#lang racket/base

(require yosys/memoize
         rackunit)

(test-case "no context"
  (define run-count 0)
  (define/memoize1 (f x)
    (set! run-count (+ run-count 1))
    (* x 5))
  (check-equal? (f 3) 15)
  (check-equal? run-count 1)
  (check-equal? (f 3) 15)
  (check-equal? run-count 2))

(test-case "basic context"
  (define run-count 0)
  (define/memoize1 (f x)
    (set! run-count (+ run-count 1))
    (* x 5))
  (new-memoization-context
   (check-equal? (f 3) 15)
   (check-equal? run-count 1)
   (check-equal? (f 3) 15)
   (check-equal? run-count 1)))

(test-case "multiple values"
  (define run-count 0)
  (define/memoize1 (f x)
    (set! run-count (+ run-count 1))
    (* x 5))
  (new-memoization-context
   (check-equal? (f 3) 15)
   (check-equal? run-count 1)
   (check-equal? (f 4) 20)
   (check-equal? run-count 2)
   (check-equal? (f 4) 20)
   (check-equal? run-count 2)
   (check-equal? (f 3) 15)
   (check-equal? run-count 3)))
