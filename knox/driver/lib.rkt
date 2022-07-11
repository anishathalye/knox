#lang racket/base

(require (for-syntax racket/base syntax/parse))

;; we can't use #lang knox/driver because then there will be an import cycle

(define-syntax collect
  (syntax-parser
    [(_) #''()]
    [(_ (define (fn arg ...) body ...) form ...)
     #'(cons (cons 'fn '(lambda (arg ...) body ...)) (collect form ...))]
    [(_ (define (fn . arg) body ...) form ...)
     #'(cons (cons 'fn '(lambda arg body ...)) (collect form ...))]))

(define global-exprs
  (collect
   (define (out* . args)
     (let ([current-input (out)])
       (if (empty? args)
           (void)
           (begin
             (out (update-field current-input (car args) (cadr args)))
             (apply out* (cddr args))))))

   (define (collect proc n)
     (if (zero? n)
         '()
         (cons (proc) (collect proc (sub1 n)))))

   (define (map f xs)
     (if (null? xs) '() (cons (f (car xs)) (map f (cdr xs)))))

   (define (for-each f xs)
     (if (null? xs)
         (void)
         (begin
           (f (car xs))
           (for-each f (cdr xs)))))))

(provide global-exprs)
