#lang racket/base

(require racket/match racket/contract racket/random
         (only-in file/sha1 bytes->hex-string)
         (prefix-in @ rosette/safe)
         syntax/parse/define
         (for-syntax racket/base))

(provide
 value-of-solvable-type/c
 (contract-out
  [fresh-symbolic (-> (or/c symbol? string?)
                      @solvable?
                      @constant?)]
  [symbolic-from-id (-> symbol?
                        bytes?
                        @solvable?
                        @constant?)]
  [concrete-head? (-> any/c
                      boolean?)])
 (struct-out guid)
 check-no-asserts)

(define value-of-solvable-type/c
  (flat-named-contract
   'value-of-solvable-type?
   (lambda (v) (@solvable? (@type-of v)))))

;; instantiate a fresh symbolic that prints with the given name
;;
;; compare to code in rosette/base/form/define.rkt and rosette/base/core/term.rkt
(define (fresh-symbolic name type)
  (define sym-base
    (if (symbol? name)
        name
        (string->symbol name)))
  (define id (make-guid))
  (@constant (list sym-base id) type))

(define (symbolic-from-id name id type)
  (@constant (list name (guid id)) type))

(define id-print-width (make-parameter 3))

(define GUID-BYTES 12)

(define (make-guid)
  (guid (crypto-random-bytes GUID-BYTES)))

(define (guid-print guid port mode)
  (let* ([hex (bytes->hex-string (guid-value guid))]
         [len (string-length hex)]
         [end (min (id-print-width) len)]
         [trimmed (substring hex 0 end)])
    (write-string trimmed port)
    (when (< end len)
      (write-string ".." port))))

(struct guid (value)
  #:transparent
  #:methods gen:custom-write
  [(define write-proc guid-print)])

(define (concrete-head? expr)
  (not (or (@term? expr) (@union? expr))))

(define (check-no-asserts* expr-thunk #:assumes [assumes #t] #:discharge-asserts [discharge-asserts #f])
  (when (not (@vc-true? (@vc)))
    (error 'check-no-asserts "initial vc must be true, is ~v" (@vc)))
  (define res (@with-vc (@begin (@assume assumes) (expr-thunk))))
  (when (not (@normal? res))
    (println res)
    (error 'check-no-asserts "evaluation did not terminate normally (all paths infeasible)"))
  (define eval-vc (@result-state res))
  (cond
    [(eq? (@vc-asserts eval-vc) #t)
     (@result-value res)]
    [(not discharge-asserts)
     (error 'check-no-asserts "evaluation of expression produced asserts")]
    [else
     (if (@unsat? (@verify (@begin
                            (@assume assumes)
                            (@assert (@vc-asserts eval-vc)))))
         (@result-value res)
         (error 'check-no-asserts "unable to verify absence of assertion failures"))]))

(define-simple-macro (check-no-asserts expr (~seq k:keyword v:expr) ...)
  (check-no-asserts* (lambda () expr) (~@ k v) ...))
