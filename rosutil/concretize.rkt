#lang racket/base

(require
 "addressable-struct.rkt"
 (only-in "lens.rkt" join join? join-contents)
 yosys
 racket/list racket/contract
 (prefix-in @ rosette/safe)
 (for-syntax racket/base syntax/parse racket/syntax))

(provide
 (contract-out
  [concrete (-> any/c @solution?)]
  [concretize (->* (any/c)
                   (@boolean? #:piecewise boolean? #:error-on-failure boolean?)
                   any)]
  [all-values (->* (any/c)
                   (@boolean? #:limit (or/c boolean? natural-number/c))
                   list?)]
  [concretize-fields (->* (addressable?)
                          (@boolean?)
                          addressable?)]))

; Note: these functions are not general-purpose -- it is in general,
; NOT safe to use them in arbitrary Rosette programs. At best,
; they might _increase_ the size of terms; at worst, they may produce
; incorrect results.
;
; We use these only in conjunction with yosys, where we have a situation
; where (vc) is empty, and there is no mutation everywhere
; (it's all pure functional code), so I think this is okay.

(define (concretize view [predicate #t] #:piecewise [piecewise #f] #:error-on-failure [error-on-failure #f])
  (if (and piecewise (join? view))
      (join (map (lambda (el) (concretize el predicate #:piecewise piecewise #:error-on-failure error-on-failure)) (join-contents view)))
      (concretize-term view predicate #:error-on-failure error-on-failure)))

(define (concrete term [predicate #t])
  (define-values (_ res) (concretize-term* term predicate))
  res)

(define (concretize-term term predicate #:error-on-failure [error-on-failure #f])
  (define-values (term-concrete res) (concretize-term* term predicate))
  (if (or (@unsat? res) (not error-on-failure))
      term-concrete
      (error 'concretize-term "failed to concretize term")))

;; returns (maybe concretized term, model)
(define (concretize-term* term predicate)
  (define vars (@symbolics term))
  (cond
    [(empty? vars) (values term (@unsat))] ; don't bother checking predicate here
    [else
     (define model
       (if (eqv? predicate #t)
           (@sat) ; avoid a solver call, it'll return an empty model in this case anyways
           (@solve (@assert predicate))))
     ;; what to do if solver returns unsat?
     (unless (@sat? model)
       (error 'concretize-term* "non-sat predicate"))
     (define term-concrete (@evaluate term (@complete-solution model vars)))
     (define res
       (@verify
        (begin
          (@assume predicate)
          (@assert
           (@equal? term term-concrete)))))
     (if (@unsat? res)
         (values term-concrete res)
         (values term res))]))

(define (all-values term [predicate #t] #:limit [limit #f])
  (define vars (@symbolics term))
  (let loop ([acc '()]
             [neq-rest predicate]
             [sofar 0])
    (cond
      [(and limit (>= sofar limit)) acc]
      [else
       (define model (@solve (@assert neq-rest)))
       (cond
         [(@unsat? model) acc]
         [(@unknown? model) acc] ; give up
         [else ; sat
          (define concrete (@evaluate term (@complete-solution model vars)))
          (loop
           (cons concrete acc)
           (@&& neq-rest (@not (@equal? term concrete)))
           (add1 sofar))])])))

(define (concretize-fields val [predicate #t])
  (for/struct [(n v) val]
    (concretize-term v predicate)))
