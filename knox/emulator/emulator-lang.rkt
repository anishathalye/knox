#lang racket/base

(require
 racket/provide
 racket/stxparam
 (prefix-in @ (combine-in rosette/safe rosutil))
 (for-syntax racket/base racket/syntax syntax/parse)
 "../emulator.rkt"
 (only-in "../semantics/environment.rkt" make-assoc assoc-extend assoc-extend*)
 (only-in "../semantics/value.rkt" closure)
 (only-in "interpreter.rkt" create-environment interpret raw lift))

(provide (rename-out [$#%module-begin #%module-begin])
         #%top-interaction #%app #%datum #%datum #%top
         (rename-out [$define define] [$struct struct])
         ;; some of the simple builtins from interpreter
         void void?
         printf println
         equal?
         cons car cdr null? list? list length reverse
         not
         + - * quotient modulo zero? add1 sub1 abs max min < <= > >= expt integer?
         (filtered-out
          (lambda (name) (substring name 1))
          (combine-out
           @bv @bv?
           @bveq @bvslt @bvult @bvsle @bvule @bvsgt @bvugt @bvsge @bvuge
           @bvnot @bvand @bvor @bvxor @bvshl @bvlshr @bvashr
           @bvneg @bvadd @bvsub @bvmul @bvsdiv @bvudiv @bvsrem @bvurem @bvsmod
           @concat @extract @sign-extend @zero-extend @bitvector->integer @bitvector->natural @integer->bitvector
           @bit @lsb @msb @bvzero? @bvadd1 @bvsub1 @bvsmin @bvumin @bvsmax @bvumax @bvrol @bvror @rotate-left @rotate-right @bitvector->bits @bitvector->bool @bool->bitvector)))

(define-syntax-parameter $define
  (lambda (stx)
    (raise-syntax-error #f "use of a define outside the top-level" stx)))

(define-syntax-parameter $struct
  (lambda (stx)
    (raise-syntax-error #f "use of a struct outside the top-level" stx)))

(define-syntax (process-defines stx)
  (syntax-parse stx
    [(_ global-bindings:id)
     #'(begin global-bindings)]
    [(_ global-bindings:id ((~literal $define) value-name:id body:expr) form ...)
     #'(let* ([value-name body]
              [global-bindings (assoc-extend global-bindings 'value-name value-name)])
         (process-defines global-bindings form ...))]
    [(_ global-bindings:id ((~literal $define) (value-name:id formals:id ...) body:expr ...+) form ...)
     #'(let* ([value-name (closure '(lambda (formals ...) body ...) (make-assoc))]
              [global-bindings (assoc-extend global-bindings 'value-name value-name)])
         (process-defines global-bindings form ...))]
    [(_ global-bindings:id ((~literal $define) (value-name:id . rest-arg:id) body:expr ...+) form ...)
     #'(let* ([value-name (closure '(lambda rest-arg body ...) (make-assoc))]
              [global-bindings (assoc-extend global-bindings 'value-name value-name)])
         (process-defines global-bindings form ...))]
    ;; struct declaration
    [(_ global-bindings:id ((~literal $struct) struct-name:id (fields:id ...)) form ...)
     #:with (getter ...) (for/list ([f (syntax->list #'(fields ...))])
                           (format-id #'struct-name "~a-~a" #'struct-name f))
     #'(let ()
         (let ([global-bindings
                (assoc-extend*
                 global-bindings
                 (list
                  (cons 'struct-name (raw (lift struct-name)))
                  (cons 'getter (raw (lift getter))) ...))])
           (process-defines global-bindings form ...)))]))

(define-syntax process-structs
  (syntax-parser
    [(_ ((~literal $struct) struct-name:id (fields:id ...)) form ...)
     #'(begin
         (@addressable-struct struct-name (fields ...))
         (provide (struct-out struct-name))
         (process-structs form ...))]
    [(_ _ form ...)
     #'(process-structs form ...)]
    [(_)
     #'(begin)]))

(define-syntax ($#%module-begin stx)
  (syntax-parse stx
    [(_ form ...)
     #:with emulator (format-id stx "emulator")
     #'(#%module-begin
        (process-structs form ...)
        (define global-bindings
          (let ([global-bindings (make-assoc)])
            (process-defines global-bindings form ...)))
        (define emulator
          (make-emulator global-bindings))
        (provide emulator))]))
