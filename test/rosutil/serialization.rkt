#lang rosette/safe

(require rackunit
         rosutil
         racket/match
         (only-in racket/base open-input-string)
         (only-in racket/port with-output-to-string))

(test-case "basic"
  (define-symbolic* x integer?)
  (define-symbolic* b boolean?)
  (define obj (list x (if b x (add1 x)) b))
  (define ser (serialize obj))
  (define des (deserialize ser))
  (check-not-equal? des obj)
  (check-pred list? des)
  (check-equal? (length des) 3)
  (define x* (car des))
  (check-pred constant? x*)
  (check-pred integer? x*)
  (define b* (caddr des))
  (check-pred constant? b*)
  (check-pred boolean? b*)
  (check-equal? (cadr des) (if b* x* (add1 x*))))

(test-case "reuse vars"
  (define x (fresh-symbolic 'x integer?))
  (define b (fresh-symbolic 'b boolean?))
  (define obj (list x (if b x (add1 x)) b))
  (define obj* (deserialize (serialize obj)))
  (check-equal? obj* obj))

(test-case "custom struct"
  (struct person (name age) #:transparent)
  (define x (fresh-symbolic 'x integer?))
  (define p (person "Alice" x))
  (check-exn #rx"unsupported type" (lambda () (serialize p)))
  (define sr (make-struct-register))
  (register-struct sr person?)
  (check-exn #rx"unknown type person\\?" (lambda () (deserialize (serialize p sr))))
  (check-equal? (deserialize (serialize p sr) sr) p))

(test-case "de-dupe objects"
  (define x (fresh-symbolic 'x (bitvector 10)))
  (define (make-big-tree n)
    (cond
      [(zero? n) x]
      [else
       (define next (make-big-tree (sub1 n)))
       (cons next next)]))

  ;; we don't want the serialized representation of this thing to be huge
  (define big (make-big-tree 100))
  (check-equal? (deserialize (serialize big)) big))

(test-case "union"
  (define b (fresh-symbolic 'b boolean?))
  (define c (fresh-symbolic 'c boolean?))
  (define v (if c "c" 0))
  (define u (if b (vector v) 4))
  (define s (serialize u))
  (define d (deserialize s))
  (check-equal? d u))

(test-case "op"
  (define x (fresh-symbolic 'x (bitvector 10)))
  (define y (fresh-symbolic 'y (bitvector 10)))
  (define obj (list (bvneg x) (bvadd x y) (bvadd x (bv 1 10))))
  (check-equal? (deserialize (serialize obj)) obj))

(test-case "string"
  (struct person (name age extra) #:transparent)
  (define x (fresh-symbolic 'x integer?))
  (define p (person "Alice" x (bv 3 64)))
  (define sr (make-struct-register))
  (register-struct sr person?)
  (check-equal? (deserialize (read (open-input-string (with-output-to-string (lambda () (write (serialize p sr)))))) sr) p))

(test-case "bitvector type"
  (define x (fresh-symbolic 'x (bitvector 16)))
  (define v (zero-extend x (bitvector 32)))
  (check-equal? (deserialize (serialize v)) v))

(test-case "partial canonicalization"
  ;; rosette uses the term cache and the id (from current-index) to
  ;; impose an ordering on the children of expressions with commutative
  ;; operators, and we should make sure serialization preserves this
  (define-symbolic* x integer?)
  (define-symbolic* y integer?)
  (define t (list y x (+ y x)))
  ;; the (+ y x) will be canonicalized as (+ x y)
  ;; but without careful treatment in serialization, we'll deserialize
  ;; y first, so it'll have a smaller ID, and then future computations
  ;; doing the same thing won't canonicalize in the same order
  (define t* (deserialize (serialize t)))
  (define y* (first t*))
  (define x* (second t*))
  (define sum* (third t*))
  (define sum** (+ y* x*))
  (check-true (equal? sum* sum**)))

(test-case "partial canonicalization: deeper"
  (define-symbolic* x integer?)
  (define-symbolic* y integer?)
  (define t (list (list y) (list x) (+ y x)))
  (define t* (deserialize (serialize t)))
  (define y* (first (first t*)))
  (define x* (first (second t*)))
  (define sum* (third t*))
  (define sum** (+ y* x*))
  (check-true (equal? sum* sum**)))

(test-case "partial canonicalization: deeper, only terms"
  (define-symbolic* x integer?)
  (define-symbolic* y integer?)
  (define t (* (- y) (- x) (+ y x)))
  (define t* (deserialize (serialize t)))
  ;; grab x and y
  (define y* (match t* [(expression _ (expression _ y) _ ...) y]))
  (define x* (match t* [(expression _ _ (expression _ x) _ ...) x]))
  (define t** (* (- y*) (- x*) (+ y* x*)))
  (check-true (equal? t* t**)))
