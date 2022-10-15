#lang racket/base

(require
 yosys/memoize
 rackunit
 rosette/safe
 rosutil
 (prefix-in mpm: "./verilog/multi_port_memory.rkt"))

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

(test-case "vc-sensitive"
  (define-symbolic* b boolean?)
  (define/memoize1 (f1 b)
    (if b 0 1))
  (define/memoize1 (f2 b)
    (if b (+ (f1 b) 10) (+ (f1 b) 20)))
  ;; if memoizing f1 is not vc-sensitive, then when f2 is evaluated,
  ;; Rosette will first explore the [b = #t] path, and under that path
  ;; condition, (f1 b) will evaluate in Rosette to just 0; then, when
  ;; exploring the second branch of the conditional in f2, we'd use the
  ;; incorrect memoized value
  (define res (new-memoization-context (f2 b)))
  ;; with buggy (non-vc-sensitive) memoization, res would be (ite b 10 20)
  (check-equal? res (if b 10 21)))

(test-case "multi-port memory (context-sensitive symbolics)"
  ;; this is a simplified version of an example that was triggering
  ;; buggy behavior in a previous version of #lang yosys
  ;;
  ;; Yosys synthesizes writes to multi-port memories with a mask,
  ;; address, and data bus, and each port updates the memory state as:
  ;;
  ;; mem_i = if (mask == 0) then
  ;;           mem_{i-1}
  ;;         else
  ;;           store(mem_{i-1}, addr, data & mask | mem_{i-1}[addr] & !mask)
  ;;
  ;; each port updates the memory in this way; with a 3-port memory, the
  ;; calculation of mem_3 calls mem_2, first with the path condition (mask == 0),
  ;; and if we memoize mem_2 in a way that's not vc-sensitive, the second call
  ;; to mem_2 (in the "else" branch) will return the wrong value
  (define-symbolic* resetn boolean?)
  (define s
    (update-field
     (mpm:new-zeroed-multi_port_memory_s)
     'resetn resetn))
  (define m (solve (assert (equal? resetn #t))))
  (check-equal?
   (get-field (evaluate (mpm:step s) m) 'data)
   (vector-immutable (bv #b01 2) (bv #b10 2))))
