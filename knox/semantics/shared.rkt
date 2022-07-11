#lang rosette/safe

(provide vector-set list->immutable-vector)

(define (vector-set vec pos value)
  (define copy (list->vector (vector->list vec)))
  (vector-set! copy pos value)
  (vector->immutable-vector copy))

(define (list->immutable-vector l)
  (vector->immutable-vector (list->vector l)))
