#lang rosette/safe

(require rackunit
         "verilog/counter.rkt"
         (only-in "verilog/print-test.rkt" new-zeroed-print_test_s)
         rosutil
         yosys
         (only-in racket/base string-append parameterize regexp-match))

(test-case "basic verification: when enable and reset are not set, value doesn't change"
  (define s0 (new-symbolic-counter_s))
  (define s1 (counter_t s0))
  (check-pred
   unsat?
   (verify
    (begin
      (assume (equal? (|counter_n en| s0) #f))
      (assume (equal? (|counter_n nrst| s0) #t))
      (assert (equal? (|counter_n count| s0) (|counter_n count| s1)))))))

(test-case "basic verification: counter wraparound even when no reset"
  (define s0 (update-counter_s
              (new-symbolic-counter_s)
              [nrst #t]))
  (define s1 (counter_t s0))
  (define model
    (verify
     (assert ((|counter_n count| s0) . bvule . (|counter_n count| s1)))))
  (check-pred sat? model)
  (check-equal?
   (evaluate (|counter_n count| s0) model)
   (bv #b11111111 8)))

(test-case "inputs/outputs/registers"
  (check-equal? (length inputs) 2)
  (check-equal? (length outputs) 1)
  (check-equal? (first outputs) (cons 'count |counter_n count|))
  (check-equal? (length registers) 1)
  (check-equal? (first registers) (cons 'count |counter_n count|)))

(test-case "display/write"
  (define s0 (new-zeroed-print_test_s))
  (define expected
    (apply string-append
           '("#(struct:print_test_s"
             " #f"
             " #f"
             " (bv #x00 8)"
             " #((bv #x00000000 32) (bv #x00000000 32) (bv #x00000000 32) (bv #x00000000 32))"
             ")")))
  (check-equal? (format "~a" s0) expected) ; display
  (check-equal? (format "~s" s0) expected)) ; write

(test-case "print"
  (define s0 (new-zeroed-print_test_s))
  (check-equal? (format "~v" s0) #<<EOS
print_test_s {
  clk: #f
  count: (bv #x00 8)
  ram:
    0: (bv #x00000000 32)
    1: (bv #x00000000 32)
    2: (bv #x00000000 32)
    3: (bv #x00000000 32)
}
EOS
                ))

(test-case "print filter: regexp"
  (define s0 (new-zeroed-print_test_s))
  (parameterize ([print-filter #rx"^c.*$"])
    (check-equal? (format "~v" s0) #<<EOS
print_test_s {
  clk: #f
  count: (bv #x00 8)
}
EOS
                  )))

(test-case "print filter: string"
  (define s0 (new-zeroed-print_test_s))
  (parameterize ([print-filter "c"])
    (check-equal? (format "~v" s0) #<<EOS
print_test_s {
  clk: #f
  count: (bv #x00 8)
}
EOS
                  )))

(test-case "field-filter/or"
  (define s0 (new-zeroed-print_test_s))
  (parameterize ([print-filter (field-filter/or "ram" #rx"^c..$")])
    (check-equal? (format "~v" s0) #<<EOS
print_test_s {
  clk: #f
  ram:
    0: (bv #x00000000 32)
    1: (bv #x00000000 32)
    2: (bv #x00000000 32)
    3: (bv #x00000000 32)
}
EOS
                  )))

(test-case "field-filter/not"
  (define s0 (new-zeroed-print_test_s))
  (parameterize ([print-filter (field-filter/not "ram")])
    (check-equal? (format "~v" s0) #<<EOS
print_test_s {
  clk: #f
  count: (bv #x00 8)
}
EOS
                  )))

(test-case "generic"
  (define s0 (new-symbolic-counter_s))
  (define s1 (update-field s0 'nrst #f))
  (check-eq? (counter_s-nrst s1) #f)
  (check-eq? (get-field s1 'nrst) #f)
  (define zeroed
    (for/struct (v s1)
      (define t (type-of v))
      (cond
        [(eq? t boolean?) #f]
        [(bitvector? t) (bv 0 (bitvector-size t))])))
  (check-equal? zeroed (counter_s #f #f (bv 0 8) #f #f))
  (check-equal? (fields zeroed) '(counter_is clk count en nrst)))

(test-case "input*"
  (define i (input* 'nrst #t 'en #f))
  (check-equal? (input-nrst i) #t)
  (check-equal? (input-en i) #f))

(test-case "input generic"
  (define i (input* 'nrst #t 'en #f))
  (check-equal? (get-field i 'nrst) #t)
  (check-equal? (get-field i 'en) #f)
  (define i* (update-field i 'nrst #f))
  (check-equal? (input-nrst i*) #f))
