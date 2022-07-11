#lang rosette/safe

(require rosutil
         rackunit)

(test-case "fresh-symbolic"
  (define x (fresh-symbolic "foo" (bitvector 32)))
  (define y (fresh-symbolic "foo" (bitvector 32)))
  (check-match (format "~a" x) (regexp #rx"^foo\\$"))
  (check-match (format "~a" y) (regexp #rx"^foo\\$"))
  (check-not-false (not (eq? x y))))

(test-case "concrete-head?"
  (define-symbolic* b boolean?)
  (check-true (concrete-head? (if b (list 1 2) (list 2 1))))
  (check-false (concrete-head? (if b (list 1 2) (list 3))))
  (check-true (concrete-head? (list 1 (if b 3 4)))))
