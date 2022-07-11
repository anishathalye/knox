#lang rosette/safe

(require (only-in racket/base error))

(provide
 make-assoc
 assoc-contains
 assoc-lookup
 assoc-remove
 assoc-extend assoc-extend*)

(define (make-assoc)
  '()) ; list of pairs of symbol, value

(define (assoc-contains env name)
  (if (null? env)
      #f
      (or (equal? name (caar env))
          (assoc-contains (cdr env) name))))

(define (assoc-lookup env name)
  (if (null? env)
      (error 'assoc-lookup "assoc does not contain ~v" name)
      (if (equal? name (caar env))
          (cdar env)
          (assoc-lookup (cdr env) name))))

(define (assoc-remove env name)
  (if (null? env)
      env
      (let ([base (assoc-remove (cdr env) name)]
            [binding (car env)])
        (if (equal? name (car binding))
            base
            (cons binding base)))))

(define (assoc-extend env name value)
  (cons (cons name value) (assoc-remove env name)))

(define (assoc-extend* env bindings)
  (if (null? bindings)
      env
      (begin
        (let* ([binding (car bindings)]
               [name (car binding)]
               [value (cdr binding)]
               [bindings (cdr bindings)])
          (assoc-extend* (assoc-extend env name value) bindings)))))
