#lang racket/base

(require
 racket/contract
 racket/match
 (prefix-in @ (combine-in
               rosette/safe
               (only-in rosette/base/core/bitvector [bv? bv-constant?])
               (only-in rosette/base/core/type typed? get-type type-construct type-deconstruct)))
 "util.rkt")

(provide
 (contract-out
  [substitute (-> any/c @constant? any/c any)]
  [substitute-terms (-> any/c hash? any)]))

(define (substitute-terms val [var-term-map (hasheq)])
  (define/internally-memoizing (substitute-memo val)
    (define (rec children)
      (for/list ([child (in-list children)])
        (substitute-memo child)))
    (match val
      [(or (? boolean?) (? integer?) (? real?) (? string?) (? symbol?) (? @bv-constant?)) val]
      [(@constant id type) (hash-ref var-term-map val val)]
      [(@union contents) (apply @union (rec contents))]
      [(@expression op vs ...) (apply op (rec vs))]
      [(list vs ...) (rec vs)]
      [(cons x y) (cons (substitute-memo x) (substitute-memo y))]
      [(vector vs ...) (let ([v (list->vector (rec vs))])
                         (if (immutable? val)
                             (vector->immutable-vector v)
                             v))]
      [(box v) (box (substitute-memo v))]
      [(and (? @typed?) (app @get-type type)) (@type-construct type (rec (@type-deconstruct type val)))]
      [_ val]))
  (substitute-memo val))

(define (substitute val var term)
  (substitute-terms val (hasheq var term)))

(module+ test
  (require
   "lens.rkt"
   "addressable-struct.rkt"
   rackunit)

  (test-case "basic"
    (@struct foo (bar baz) #:transparent)
    (@define-symbolic* w x y z @integer?)
    (define v (@list (foo x 3) (@+ x y z)))
    (define t (@+ (@+ (@* w w) w) 1))
    (define v* (substitute v x t))
    (check-equal?
     v*
     (@list (foo t 3) (@+ t y z))))

  (test-case "lens"
    (addressable-struct foo (bar baz))
    (@define-symbolic* x y @integer?)
    (define v (list (foo 1 x) y))
    (define v*
      (lens-transform
       (lens (list (lens car-lens 'baz) (list-ref-lens 1)))
       v
       (lambda (view) (substitute-terms view (hasheq x 2 y 3)))))
    (check-equal? v* (list (foo 1 2) 3)))

  (test-case "mutability"
    (@define-symbolic x @integer?)
    (check-true (immutable? (substitute (vector-immutable 1 2 x) x 3)))
    (check-false (immutable? (substitute (vector 1 2 x) x 3)))))
