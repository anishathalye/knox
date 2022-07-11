#lang rosette/safe

(require rackunit
         yosys
         "verilog/ram.rkt"
         (only-in racket/base parameterize))

(test-case "not uninterpreted function by default"
  (define s0 (new-symbolic-ram_s))
  (check-pred vector? (|ram_m ram| s0)))

(test-case "uninterpreted function"
  (parameterize ([array-representation-vector #f])
    (define s0 (new-symbolic-ram_s))
    (check-equal? (type-of (|ram_m ram| s0)) (~> (bitvector 8) (bitvector 32)))
    ; try writing then reading same address
    (define-symbolic* addr din (bitvector 32))
    (define s0-with-inputs
      (update-ram_s
       s0
       [valid #t]
       [addr addr]
       [din din]
       [wstrb (bv #b1111 4)]))
    (define s1 (ram_t s0-with-inputs))
    (define s1-with-inputs
      (update-ram_s
       s1
       [valid #t]
       [addr addr]
       [din (bv 0 32)]
       [wstrb (bv #b0000 4)]))
    (define dout (|ram_n dout| s1-with-inputs))
    (check-pred unsat? (verify (assert (bveq dout din))))))
