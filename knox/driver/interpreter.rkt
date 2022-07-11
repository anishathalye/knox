#lang rosette/safe

(require
 "../semantics/syntax.rkt"
 "../semantics/value.rkt"
 "../semantics/environment.rkt"
 "../semantics/shared.rkt"
 (prefix-in $ "../semantics/lifted.rkt")
 (only-in racket/base error)
 (prefix-in lib: "lib.rkt")
 rosutil
 rosette/lib/destruct
 syntax/parse/define
 yosys/meta
 yosys/generic)

(provide
 basic-value? uninterpreted?
 make-interpreter step run run* show closure update-circuit
 make-assoc assoc-contains assoc-lookup assoc-remove assoc-extend assoc-extend*
 (struct-out finished)
 (struct-out state)
 (struct-out globals))

(struct builtin
  (name)
  #:transparent)

(define (uninterpreted? expr)
  (member (tag expr) '(yield hint)))

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
;; | builtin?
;; | circuit-op?
;; | input?
;; | output?

;; checks if v is a value, but doesn't include input/output (because
;; that's slightly more annoying, those structs are supplied via
;; metadata)

(struct circuit-op
  (name)
  #:transparent)

;; Built-in functions
;;
;; A built-in function has type (-> (list value) globals continuation (or value state))

;; Simple built-ins have type (-> (list value) value)

(define-simple-macro (pair-symbol-value v:id ...)
  (list (cons 'v v) ...))

(define (lift f)
  (lambda (values globals cont)
    (cont (apply f values) globals)))

(define (bitvector->bytes x)
  (define w (bitvector-size (type-of x)))
  (if (<= w 8)
      (list x)
      (cons (extract (sub1 w) (- w 8) x) (bitvector->bytes (extract (- w 9) 0 x)))))

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
    not
    ;; integer
    + - * quotient modulo zero? add1 sub1 abs max min = < <= > >= expt integer?
    ;; bv
    bv?
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
    ;; addressable generic
    get-field update-field update-fields
    ;; additional utility functions
    bitvector->bytes)
   (list
    (cons 'bv $bv)
    (cons 'bitvector $bitvector))))

(define (builtin-apply values globals cont)
  (local-apply (car values) (cadr values) globals cont))

(define builtins
  (append
   (map (lambda (sv) (cons (car sv) (lift (cdr sv)))) simple-builtins)
   (list
    (cons 'apply builtin-apply))))

(define initial-values
  (pair-symbol-value
   null
   true
   false))

(define initial-environment
  (append
   initial-values
   (map (lambda (sv) (let ([name (car sv)]) (cons name (builtin name)))) builtins)
   (map (lambda (se) (let ([name (car se)] [e (cdr se)]) (cons name (closure e (make-assoc))))) lib:global-exprs)))

;; State

(addressable-struct globals
  (environment circuit meta))

(define (update-circuit g circuit)
  (globals (globals-environment g) circuit (globals-meta g)))

(addressable-struct state
  (control environment globals continuation))

(struct finished (value circuit)
  #:transparent)

;; Continuation

(addressable-struct done
  ()
  #:property prop:procedure
  (lambda (this val globals)
    (finished val (globals-circuit globals))))

(addressable-struct eval-app
  (environment function-value argument-values argument-exprs continuation)
  #:property prop:procedure
  (lambda (this val globals)
    (destruct
     this
     [(eval-app env f args pending cont)
      (cond
        [(not f)
         ;; the hole is the function
         (cond
           [(null? pending)
            ;; no-arg function, call immediately
            (local-apply val '() globals cont)]
           [else
            ;; some args left
            (state (car pending) env globals (eval-app env val '() (cdr pending) cont))])]
        [else
         ;; the hole is an argument
         (cond
           [(null? pending)
            ;; no args left, call
            (local-apply f (reverse (cons val args)) globals cont)]
           [else
            ;; some args left
            (state (car pending) env globals (eval-app env f (cons val args) (cdr pending) cont))])])])))

(addressable-struct eval-if
  (environment then-expr else-expr continuation)
  #:property prop:procedure
  (lambda (this val globals)
    (destruct
     this
     [(eval-if env then-expr else-expr cont)
      (state (if val then-expr else-expr) env globals cont)])))

(addressable-struct eval-and
  (environment contents continuation)
  #:property prop:procedure
  (lambda (this val globals)
    (destruct
     this
     [(eval-and env contents cont)
      (if val
          (state (car contents) env globals (let ([tail (cdr contents)])
                                              (if (null? tail)
                                                  cont
                                                  (eval-and env tail cont))))
          (cont #f globals))])))

(addressable-struct eval-or
  (environment contents continuation)
  #:property prop:procedure
  (lambda (this val globals)
    (destruct
     this
     [(eval-or env contents cont)
      (if val
          (cont val globals)
          (state (car contents) env globals (let ([tail (cdr contents)])
                                              (if (null? tail)
                                                  cont
                                                  (eval-or env tail cont)))))])))

(addressable-struct eval-let
  (environment bindings current-name pending body-expr continuation)
  #:property prop:procedure
  (lambda (this val globals)
    (destruct
     this
     [(eval-let env bindings var pending body cont)
      (cond
        [(null? pending)
         ;; no bindings left
         (define env* (assoc-extend* env (cons (cons var val) bindings)))
         (state body env* globals cont)]
        [else
         ;; some bindings left
         (state (cadar pending) env globals (eval-let env (cons (cons var val) bindings) (caar pending) (cdr pending) body cont))])])))

(addressable-struct eval-seq
  (environment exprs continuation)
  #:property prop:procedure
  (lambda (this val globals)
    (destruct
     this
     [(eval-seq env exprs cont)
      (cond
        [(null? (cdr exprs))
         (state (car exprs) env globals cont)]
        [else
         (state (car exprs) env globals (eval-seq env (cdr exprs) cont))])])))

;; Interpreter

(define (local-apply f args globals cont)
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
          (assoc-extend* (closure-environment f)
                         (foldl
                          (lambda (var val acc) (cons (cons var val) acc))
                          '() formals args))]))
     (state (lambda-body (closure-expr f)) env* globals cont)]
    [(builtin? f)
     ((assoc-lookup builtins (builtin-name f)) args globals cont)]
    [(circuit-op? f)
     (define op (circuit-op-name f))
     (define circuit (globals-circuit globals))
     (define meta (globals-meta globals))
     (case op
       [(tick)
        (let ([circuit* ((meta-step meta) circuit)])
          (cont (void) (update-circuit globals circuit*)))]
       [(in)
        (let ([inp ((meta-get-output meta) circuit)])
          (cont inp globals))]
       [(out)
        ;; if args is empty, assume we are _getting_ the circuit's input
        (cond
          [(empty? args)
           (let ([out ((meta-get-input meta) circuit)])
             (cont out globals))]
          [else
           (let ([circuit* ((meta-with-input meta) circuit (first args))])
             (cont (void) (update-circuit globals circuit*)))])]
       [(input)
        (cont (apply (meta-input meta) args) globals)]
       [(input*)
        (cont (apply (meta-input* meta) args) globals)]
       [(output)
        (cont (apply (meta-output meta) args) globals)]
       [(output*)
        (cont (apply (meta-output* meta) args) globals)]
       [else
        (cond
          [(assoc-contains (meta-input-getters meta) op)
           (cont (apply (assoc-lookup (meta-input-getters meta) op) args) globals)]
          [(assoc-contains (meta-output-getters meta) op)
           (cont (apply (assoc-lookup (meta-output-getters meta) op) args) globals)]
          [else (error 'local-apply "internal error, circuit op ~v not recognized" op)])])]
    [else
     (error 'local-apply "not a procedure: ~v" f)]))

(define (variable-lookup var env globals)
  (define global-env (globals-environment globals))
  (cond
    [(assoc-contains env var) (assoc-lookup env var)]
    [(assoc-contains global-env var) (assoc-lookup global-env var)]
    [else (error 'variable-lookup "unbound variable ~v" var)]))

(define (step s)
  (define expr (state-control s))
  (define env (state-environment s))
  (define cont (state-continuation s))
  (define globals (state-globals s))
  (cond
    ;; variable reference?
    [(variable? expr)
     (let ([value (variable-lookup expr env globals)])
       (cont value globals))]
    ;; value literal?
    [(literal? expr)
     (cont (literal-value expr) globals)]
    ;; quote?
    [(quote? expr)
     (let ([val (quote-get expr)])
       (unless (basic-value? val)
         (error 'step "not a basic value: ~v" val))
       (cont val globals))]
    ;; lambda?
    [(lambda? expr)
     (cont (closure expr env) globals)]
    ;; if-then-else?
    [(if? expr)
     (state (if-condition expr) env globals (eval-if env (if-then expr) (if-else expr) cont))]
    ;; and?
    [(and? expr)
     (let ([contents (and-contents expr)])
       (cond
         [(null? contents) (cont #t globals)]
         [(null? (cdr contents)) (state (car contents) env globals cont)]
         [else (state (car contents) env globals (eval-and env (cdr contents) cont))]))]
    ;; or?
    [(or? expr)
     (let ([contents (or-contents expr)])
       (cond
         [(null? contents) (cont #f globals)]
         [(null? (cdr contents)) (state (car contents) env globals cont)]
         [else (state (car contents) env globals (eval-or env (cdr contents) cont))]))]
    ;; let binding?
    [(let? expr)
     (let ([bindings (let-bindings expr)])
       (cond
         [(null? bindings) (state (let-body expr) env globals cont)]
         [else
          (state (cadar bindings) env globals (eval-let env '() (caar bindings) (cdr bindings) (let-body expr) cont))]))]
    ;; begin?
    [(begin? expr)
     (let ([contents (begin-contents expr)])
       (cond
         [(null? contents) (cont (void) globals)]
         [(null? (cdr contents)) (state (car contents) env globals cont)]
         [else (state (car contents) env globals (eval-seq env (cdr contents) cont))]))]
    ;; uninterpreted?
    [(uninterpreted? expr)
     (cont (void) globals)]
    ;; function application? this has to be last, after we're done recognizing keywords
    [(app? expr)
     (state (app-f expr) env globals (eval-app env #f '() (app-args expr) cont))]
    [else
     (error 'step "bad expression: ~v" expr)]))

(define (show s)
  (format "(state ~v ~v ~v)" (state-control s) (state-environment s) (state-continuation s)))

(define (run sv #:trace [trace #f])
  (if (state? sv)
      (begin
        (cond
          [(equal? trace #t) (printf "~a~n" (show sv))]
          [(procedure? trace) (trace sv)])
        (run (step sv) #:trace trace))
      sv))

(define (run* sv #:trace [trace #f])
  (finished-value (run sv #:trace trace)))

(define (meta->environment metadata)
  (define (make-op name-f)
    (let ([name (car name-f)])
      (cons name (circuit-op name))))
  (append
   (list
    ;; tick
    (cons 'tick (circuit-op 'tick))
    ;; in
    (cons 'in (circuit-op 'in))
    ;; out
    (cons 'out (circuit-op 'out))
    ;; input constructor
    (cons 'input (circuit-op 'input))
    (cons 'input* (circuit-op 'input*))
    ;; output constructor
    (cons 'output (circuit-op 'output))
    (cons 'output* (circuit-op 'output*)))
   ;; input getters
   (map make-op (meta-input-getters metadata))
   ;; output getters
   (map make-op (meta-output-getters metadata))))

(define (make-interpreter expr global-bindings initial-circuit metadata)
  (state expr
         (make-assoc)
         (globals
          (assoc-extend* (assoc-extend* initial-environment global-bindings) (meta->environment metadata))
          initial-circuit
          metadata)
         (done)))
