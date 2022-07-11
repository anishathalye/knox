#lang racket/base

(require racket/contract racket/string)

(provide array-representation-vector
         overapproximate-symbolic-store-threshold
         overapproximate-symbolic-load-threshold
         print-filter)

; array representation:
; #t for vector
; #f for uninterpreted function
(define array-representation-vector
  (make-parameter #t
                  (lambda (v)
                    (unless (boolean? v)
                      (raise-argument-error 'array-representation-vector
                                            "boolean?"
                                            v))
                    v)))

; overapproximating stores to symbolic addresses:
; #f for no overapproximation
; n for overapproximating when the array size is >= n
;
; this only has an effect when (array-representation-vector) is #t
(define overapproximate-symbolic-store-threshold
  (make-parameter #f
                  (lambda (v)
                    (unless (or (not v)
                                (natural-number/c v))
                      (raise-argument-error 'overapproximate-symbolic-store-threshold
                                            "(or/c #f natural-number/c)"
                                            v))
                    v)))

; overapproximating loads from symbolic addresses:
; #f for no overapproximation
; n for overapproximating when the array size is >= n
;
; this only has an effect when (array-representation-vector) is #t
(define overapproximate-symbolic-load-threshold
  (make-parameter #f
                  (lambda (v)
                    (unless (or (not v)
                                (natural-number/c v))
                      (raise-argument-error 'overapproximate-symbolic-load-threshold
                                            "(or/c #f natural-number/c)"
                                            v))
                    v)))

; filter what fields are included in the printed representation of a struct
(define print-filter
  (make-parameter
   #t
   (lambda (v)
     (unless (or (boolean? v)
                 (symbol? v)
                 (string? v)
                 (regexp? v)
                 ((procedure-arity-includes/c 1) v))
       (raise-argument-error 'field-filter
                             "(or/c boolean? symbol? string? regexp? (procedure-arity-includes/c 1))"
                             v))
     v)))
