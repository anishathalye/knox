#lang rosette/safe

(require rosutil rackunit yosys
         (prefix-in ! racket/base))

(test-case "concretize: concrete"
  (check-equal? (concretize (bv 1337 32)) (bv 1337 32)))

(test-case "concretize: basic"
  (define-symbolic* x (bitvector 8))
  (define term
    (bveq (bv -1 32) (concat (bv 0 24) x)))
  (check-false (concrete? term))
  (check-not-eq? term #f)
  (check-eq? (concretize term) #f))

(test-case "concretize: larger"
  (define-symbolic* x (bitvector 8))
  (define term
    (bveq
     (let ([y (concat (extract 4 4 x) (bv 0 1) (extract 1 0 (concat (bv 0 2) (extract 3 3 x))))])
       (extract 3 2 (bvor y (bvshl y (bv 2 4)))))
     (extract 4 3 x)))
  (check-not-eq? term #t)
  (check-eq? (concretize term) #t))

(test-case "concretize: failure"
  (define-symbolic* x (bitvector 8))
  (define term
    (concat (bv 0 6) (extract 1 0 x)))
  (check-false (concrete? term))
  (check-equal? (concretize term) term)
  (check-exn !exn:fail? (thunk (concretize term #:error-on-failure #t))))

(test-case "concretize: non-useful predicate"
  (define-symbolic* x (bitvector 8))
  (define term (bvxor (extract 6 4 x) (bv #b101 3)))
  (check-equal? (concretize term) term)
  (check-equal? (concretize term (bvult x (bv #b00100000 8))) term))

(test-case "concretize: predicate"
  (define-symbolic* x (bitvector 8))
  (define term (bvxor (extract 7 5 x) (bv #b101 3)))
  (check-equal? (concretize term) term)
  (check-equal? (concretize term (bvult x (bv #b00100000 8))) (bv #b101 3)))

(test-case "concrete"
  (define-symbolic* x (bitvector 8))
  (define t1 (concat (bv 0 6) (extract 1 0 x)))
  (check-pred sat? (concrete t1))
  (define t2 (bveq (bv 0 8) (concat (bv -1 4) (extract 3 0 x))))
  (check-pred unsat? (concrete t2)))

(addressable-struct foo (bar baz))

(test-case "concretize: fields subset"
  (define-symbolic* x (bitvector 8))
  (define f (foo (bveq (bv -1 32) (concat (bv 0 24) x))
                 (not (bveq (bv -1 32) (concat (bv 0 24) x)))))
  (define f* (lens-transform (lens 'bar) f concretize))
  (check-eq? (foo-bar f*) #f)
  (check-not-eq? (foo-baz f*) #t))

(test-case "concretize: fields all"
  (define-symbolic* x (bitvector 8))
  (define f (foo (bveq (bv -1 32) (concat (bv 0 24) x))
                 (not (bveq (bv -1 32) (concat (bv 0 24) x)))))
  (define f* (lens-transform (lens #t) f concretize))
  (check-eq? (foo-bar f*) #f)
  (check-eq? (foo-baz f*) #t))

(test-case "concretize: cooperation with lens-transform"
  (addressable-struct person (age height))
  (define-symbolic* x y z integer?)
  (define t (foo (person x (- y z)) (+ x y)))
  (check-equal? (lens-transform (lens 'bar 'height) t (lambda (view) (concretize view (equal? y z))))
                (foo (person x 0) (+ x y)))
  (check-equal? (lens-transform (lens (list (lens 'bar (list 'age 'height)) 'baz)) t
                                (lambda (view) (concretize view (and (equal? y z) (equal? x 1) (equal? z 5)))))
                (foo (person 1 0) 6)))

(test-case "all-values"
  (define-symbolic* x (bitvector 8))
  (define t (concat (extract 1 0 x) (bv 0 1)))
  (define all (all-values t))
  (check-equal? (!length all) 4)
  (check-not-false (!member (bv #b000 3) all))
  (check-not-false (!member (bv #b010 3) all))
  (check-not-false (!member (bv #b100 3) all))
  (check-not-false (!member (bv #b110 3) all)))

(test-case "all-values limit"
  (define-symbolic* x y (bitvector 8))
  (define t (bvxor x y))
  (check-equal? (!length (all-values t #:limit 10)) 10))

(test-case "all-values predicate"
  (define-symbolic* x (bitvector 8))
  (define term (bvxor (extract 6 4 x) (bv #b101 3)))
  (check-equal? (!length (all-values term)) 8)
  (define all (all-values term (bvult x (bv #b00100000 8))))
  (check-equal? (!length all) 2)
  (check-not-false (!member (bv #b101 3) all))
  (check-not-false (!member (bv #b100 3) all)))
