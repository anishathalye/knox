#lang racket/base

(require racket/function
         (for-syntax racket/base syntax/parse))

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
    (let ([current-context (context)])
      (if current-context
          (let ([arg-value (hash-ref current-context memoized #f)])
            (if (and arg-value (eq? arg (car arg-value)))
                (cdr arg-value)
                (let ([value (proc arg)])
                  (hash-set! current-context memoized (cons arg value))
                  value)))
          (proc arg))))
  memoized)

(define-syntax (define/memoize1 stx)
  (syntax-parse stx
    [(_ (name:id arg:id) body ...)
     #'(define name (memoize1 (lambda (arg) body ...)))]))
