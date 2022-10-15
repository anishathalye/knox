#lang racket/base

(require racket/function racket/match
         (for-syntax racket/base syntax/parse)
         (prefix-in @ rosette/safe))

(provide new-memoization-context define/memoize1)

(define context (make-parameter #f))

(define (with-new-memoization-context proc)
  (parameterize ([context (make-hasheq)])
    (proc)))

(define-syntax (new-memoization-context stx)
  (syntax-parse stx
    [(_ body ...)
     #'(with-new-memoization-context (thunk body ...))]))

(define (memoize1 proc)
  (define (memoized arg)
    (let ([current-context (context)]
          [assumes (@vc-assumes (@vc))]
          [asserts (@vc-asserts (@vc))])
      (if current-context
          (match (hash-ref current-context memoized #f)
            [(list (== assumes eq?) (== asserts eq?) (== arg eq?) value)
             value]
            [else
             (let ([value (proc arg)])
               (hash-set! current-context memoized (list assumes asserts arg value))
               value)])
          (proc arg))))
  memoized)

(define-syntax (define/memoize1 stx)
  (syntax-parse stx
    [(_ (name:id arg:id) body ...)
     #'(define name (memoize1 (lambda (arg) body ...)))]))
