#lang racket/base

(require
 "../yosys/verilog/counter.rkt"
 (prefix-in @ rosette/safe)
 rosutil
 racket/function racket/port rackunit)

(addressable-struct person (name age))

(test-case "fields"
  (check-equal? (fields (person "Alice" 23)) '(name age)))

(test-case "get-field"
  (define p (person "Bob" 33))
  (check-equal? (get-field p 'name) "Bob")
  (check-equal? (get-field p 'age) 33))

(test-case "for/struct"
  (define p (person "Charlie" 24))
  (define p*
    (for/struct [(n f) p]
      (case n
        [(name) f]
        [(age) (add1 f)])))
  (check-equal? p* (person "Charlie" 25)))

(test-case "update-field"
  (define p (person "Dan" 11))
  (check-equal?
   (update-field p 'name "Daniel")
   (person "Daniel" 11)))

(test-case "show-diff"
  (define s0 (new-zeroed-counter_s))
  (define s1 (update-field s0 'count (@bv 3 8)))
  (define res (show-diff s0 s1))
  (define expected
    #<<EOS
{
  count: - (bv #x00 8)
         + (bv #x03 8)
}
EOS
)
  (check-equal? res expected))

(test-case "assoc-addressable"
  (define x (assoc-addressable (list (cons 'a 1) (cons 'b 2))))
  (check-equal? (get-field x 'b) 2)
  (check-equal?
   (for/struct [(n f) x]
     (cons n (add1 f)))
   (assoc-addressable (list (cons 'a (cons 'a 2)) (cons 'b (cons 'b 3))))))
