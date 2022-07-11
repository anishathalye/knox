#lang rosette/safe

(require rackunit
         (prefix-in counter: "verilog/counter.rkt"))

(test-case "update-name"
  (define s
    (counter:update-counter_s
     (counter:new-zeroed-counter_s)
     [count (bv 1 8)]))
  (check-equal? s (counter:counter_s #f #f (bv 1 8) #f #f)))

(test-case "make-name"
  (define s
    (counter:make-counter_s
     [count (bv 1 8)]))
  (check-equal? s (counter:counter_s #f #f (bv 1 8) #f #f)))
