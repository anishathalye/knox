#lang rosette/safe

(require rackunit
         yosys
         "verilog/counter.rkt")

(test-case "using auto-generated methods"
  (define s0 (new-zeroed-counter_s))
  (define i (new-symbolic-input))
  (define s1 (with-input s0 i))
  (define s2 (step s1))
  (define q (equal? (output-count (get-output s2))
                    (bvadd (output-count (get-output s0)) (concat (bv 0 7) (if (input-en i) (bv 1 1) (bv 0 1))))))
  (check-pred
   unsat?
   (verify
    (begin
      (assume (equal? (input-nrst i) #t))
      (assert q)))))

(test-case "packaged metadata"
  (define s0 (new-zeroed-counter_s))
  (define s1 ((meta-step metadata) s0))
  (check-equal? s1 s0))
