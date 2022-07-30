#lang rosette/safe

(require
 "../semantics/syntax.rkt" "../semantics/value.rkt" "../semantics/environment.rkt" "../semantics/shared.rkt"
 "../result.rkt"
 "util.rkt"
 (prefix-in $ "../semantics/lifted.rkt")
 (only-in racket/base error)
 syntax/parse/define
 rosutil
 yosys/meta yosys/generic)

(provide
 (struct-out state)
 create-environment
 interpret
 lift
 raw)

;; Values
;;
;; value ::=
;; | void?
;; | boolean?
;; | integer?
;; | string?
;; | bv?
;; | symbol?
;; | null?
;; | cons?
;; | closure?
;; | raw?

(addressable-struct state (auxiliary oracle))

(struct raw (procedure)
  #:transparent)

(define (variable-lookup var env globals)
  (cond
    [(assoc-contains env var) (assoc-lookup env var)]
    [(assoc-contains globals var) (assoc-lookup globals var)]
    [else (error 'variable-lookup "unbound variable ~v" var)]))

(define (interpret expr st globals)
  (local-eval expr st (make-assoc) globals))

;; fully evaluates the expression, producing a value and a new state
(define (local-eval expr st env globals)
  (cond
    ;; variable reference?
    [(variable? expr)
     (result (variable-lookup expr env globals) st)]
    ;; value literal?
    [(literal? expr)
     (result (literal-value expr) st)]
    ;; quote?
    [(quote? expr)
     ;; note: skipping checking that it's actually a value in our
     ;; domain; emulator code itself will not use this, just top-level
     ;; invocations from verification code
     (result (quote-get expr) st)]
    ;; lambda?
    [(lambda? expr)
     (result (closure expr env) st)]
    ;; if-then-else?
    [(if? expr)
     (define eval-condition (local-eval (if-condition expr) st env globals))
     (define next-state (result-state eval-condition))
     (if (result-value eval-condition)
         (local-eval (if-then expr) next-state env globals)
         (local-eval (if-else expr) next-state env globals))]
    ;; and?
    [(and? expr)
     (define contents (and-contents expr))
     (cond
       [(null? contents) (result #t st)]
       [else
        (let loop ([contents contents]
                   [st st])
          (define eval-first (local-eval (car contents) st env globals))
          (cond
            [(or (null? (cdr contents)) (not (result-value eval-first))) eval-first]
            [else (loop (cdr contents) (result-state eval-first))]))])]
    ;; or?
    [(or? expr)
     (define contents (or-contents expr))
     (cond
       [(null? contents) (result #f st)]
       [else
        (let loop ([contents contents]
                   [st st])
          (define eval-first (local-eval (car contents) st env globals))
          (cond
            [(or (null? (cdr contents)) (result-value eval-first)) eval-first]
            [else (loop (cdr contents) (result-state eval-first))]))])]
    ;; let binding?
    [(let? expr)
     (define bindings (let-bindings expr))
     (let loop ([bindings bindings]
                [st st]
                [inner-env env])
       (cond
         [(null? bindings) (local-eval (let-body expr) st inner-env globals)]
         [else
          (define binding (car bindings))
          (define binding-name (car binding))
          (define binding-expr (cadr binding))
          (define eval-binding (local-eval binding-expr st env globals))
          (loop
           (cdr bindings)
           (result-state eval-binding)
           (assoc-extend inner-env binding-name (result-value eval-binding)))]))]
    ;; begin?
    [(begin? expr)
     (define contents (begin-contents expr))
     (cond
       [(null? contents) (result (void) st)]
       [else
        (let loop ([contents contents]
                   [st st])
          (define eval-first (local-eval (car contents) st env globals))
          (cond
            [(null? (cdr contents)) eval-first]
            [else (loop (cdr contents) (result-state eval-first))]))])]
    ;; function application? (this has to be last, after we're done recognizing keywords)
    [(app? expr)
     ;; evaluate function and arguments left-to-right, and then call it
     (define eval-f (local-eval (app-f expr) st env globals))
     (let loop ([args (app-args expr)]
                [st (result-state eval-f)]
                [evaled-args '()])
       (cond
         [(null? args) (local-apply (result-value eval-f) (reverse evaled-args) st globals)]
         [else
          (define eval-arg (local-eval (car args) st env globals))
          (loop (cdr args) (result-state eval-arg) (cons (result-value eval-arg) evaled-args))]))]
    [else
     (error 'local-eval "bad expression: ~v" expr)]))

(define (local-apply f args st globals)
  (cond
    [(closure? f)
     (define formals (lambda-formals (closure-expr f)))
     (define env*
       (cond
         [(symbol? formals)
          ;; var-args lambda
          (assoc-extend (closure-environment f) formals args)]
         [else
          (when (not (equal? (length args) (length formals)))
            (error 'local-apply "expected ~a arguments, got ~a" (length formals) (length args)))
          (assoc-extend*
           (closure-environment f)
           (foldl
            (lambda (var val acc) (cons (cons var val) acc))
            '() formals args))]))
     (local-eval (lambda-body (closure-expr f)) st env* globals)]
    [(raw? f)
     ((raw-procedure f) args st globals)]
    [else
     (error 'local-apply "not a function: ~v" f)]))

(define-simple-macro (pair-symbol-value v:id ...)
  (list (cons 'v v) ...))

(define simple-builtins
  (append
   (pair-symbol-value
    ;; misc
    void void?
    ;; utility
    printf print println write writeln display displayln
    ;; equality
    equal?
    ;; list
    cons car cdr caar cadr cdar cddr null? empty? first second third fourth list? list list-ref length reverse
    ;; vector (only immutable)
    vector? vector-immutable vector-length vector-ref vector-set vector->list list->immutable-vector
    ;; boolean
    not ! && || => <=>
    ;; integer
    + - * quotient modulo zero? add1 sub1 abs max min = < <= > >= expt integer?
    ;; bv
    bv bv?
    ;; comparison operators
    bveq bvslt bvult bvsle bvule bvsgt bvugt bvsge bvuge
    ;; bitwise operators
    bvnot bvand bvor bvxor bvshl bvlshr bvashr
    ;; arithmetic operators
    bvneg bvadd bvsub bvmul bvsdiv bvudiv bvsrem bvurem bvsmod
    ;; conversion operators
    concat extract sign-extend zero-extend bitvector->integer bitvector->natural integer->bitvector
    ;; additional operators
    bit lsb msb bvzero? bvadd1 bvsub1 bvsmin bvumin bvsmax bvumax bvrol bvror rotate-left rotate-right bitvector->bits bitvector->bool bool->bitvector
    ;; yosys generic
    get-field update-field update-fields)
   (list
    (cons 'bv $bv)
    (cons 'bitvector $bitvector))))

(define (builtin-apply args st globals)
  (local-apply (car args) (cadr args) st globals))

(define (builtin-get args st globals)
  (result (state-auxiliary st) st))

(define (builtin-set! args st globals)
  (result (void) (state (car args) (state-oracle st))))

(define (lift f)
  (lambda (args st globals)
    (result (apply f args) st)))

(define builtins
  (append
   (map (lambda (sv) (cons (car sv) (lift (cdr sv)))) simple-builtins)
   (list
    (cons 'apply builtin-apply)
    (cons 'get builtin-get)
    (cons 'set! builtin-set!))))

(define initial-values
  (pair-symbol-value
   null
   true
   false))

(define basic-environment
  (append
   initial-values
   (map (lambda (sv) (cons (car sv) (raw (cdr sv)))) builtins)))

;; oracle api is a list of pairs, of function name (symbol) and
;; procedure, where the procedure is a curried function, first taking the
;; arguments to the oracle, and then taking the oracle state, and returning a result
(define (oracle->environment oracle-api)
  (define (lift f)
    (lambda (args st globals)
      (define oracle-result ((apply f args) (state-oracle st)))
      (result (result-value oracle-result)
              (state (state-auxiliary st) (result-state oracle-result)))))
  (map (lambda (sv) (cons (car sv) (raw (lift (cdr sv))))) oracle-api))

(define (meta->environment metadata)
  (define (make-op name-f)
    (cons (car name-f) (raw (lift (cdr name-f)))))
  (append
   (list
    ;; constructor
    (cons 'circuit-new (raw (lift (lambda () (circuit-with-invariants metadata)))))
    (cons 'circuit-zeroed (raw (lift (meta-new-zeroed metadata))))
    ;; step
    (cons 'circuit-step (raw (lift (meta-step metadata))))
    ;; I/O
    (cons 'input (raw (lift (meta-input metadata))))
    (cons 'input* (raw (lift (meta-input* metadata))))
    (cons 'circuit-with-input (raw (lift (meta-with-input metadata))))
    (cons 'circuit-get-input (raw (lift (meta-get-input metadata))))
    (cons 'output (raw (lift (meta-output metadata))))
    (cons 'output* (raw (lift (meta-output* metadata))))
    (cons 'circuit-get-output (raw (lift (meta-get-output metadata)))))
   (map make-op (meta-input-getters metadata))
   (map make-op (meta-output-getters metadata))))

(define (create-environment oracle-api metadata global-bindings)
  (append
   basic-environment
   (oracle->environment oracle-api)
   (meta->environment metadata)
   global-bindings))

(module+ test
  (require
   rackunit
   (only-in "../../test/yosys/verilog/counter.rkt" [metadata counter:metadata]))

  (test-case "state"
    (check-equal?
     (local-eval '(begin
                    (set! (+ (get) 1))
                    (set! (+ (get) 1))
                    (set! (integer->bitvector (get) (bitvector 10)))
                    (bvadd (get) (bv 1 10)))
                 (state 0 #f)
                 (make-assoc)
                 basic-environment)
     (result (bv 3 10) (state (bv 2 10) #f))))

  (test-case "oracle"
    (struct counter (value)
      #:transparent)
    (define ((inc!) st)
      (result (void) (counter (add1 (counter-value st)))))
    (define ((incn! n) st)
      (result (void) (counter (+ (counter-value st) n))))
    (define ((rd) st)
      (result (counter-value st) st))
    (define api
      (pair-symbol-value inc! incn! rd))

    (check-equal?
     (local-eval '(begin
                    (inc!)
                    (inc!)
                    (incn! 5)
                    (inc!)
                    (incn! (rd))
                    (rd))
                 (state #f (counter 0))
                 (make-assoc)
                 (append basic-environment (oracle->environment api)))
     (result 16 (state #f (counter 16)))))

  (test-case "circuit"
    (check-equal?
     (local-eval
      '(begin
         (let ([c0 (circuit-new)])
           (let ([c1 (circuit-with-input c0 (input* 'nrst #t 'en #t))])
             (let ([c2 (circuit-step (circuit-step c1))])
               (output-count (circuit-get-output c2))))))
      (state #f #f)
      (make-assoc)
      (append basic-environment (meta->environment counter:metadata)))
     (result (bv 2 8) (state #f #f))))

  (test-case "bv" ; regression test
    (define-symbolic* b boolean?)
    (check-pred
     unsat?
     (verify
      (local-eval
       `(if ,b
            (let () (bv 0 1))
            (bv 0 1))
       (state #f #f)
       (make-assoc)
       basic-environment)))))
