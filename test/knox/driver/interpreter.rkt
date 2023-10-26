#lang racket/base

(require
 knox/driver/interpreter
 rackunit
 (prefix-in @ (combine-in rosette/safe rosutil))
 (prefix-in ckt: "../../yosys/verilog/counter.rkt"))

(test-case "basic concrete"
  (define interp (make-interpreter '(+ 1 1) '() (ckt:new-zeroed-counter_s) ckt:metadata))
  (define res (run* interp))
  (check-equal? res 2))

(test-case "basic symbolic"
  (define x (@fresh-symbolic 'x @integer?))
  (define expr `(+ (+ ,x 1) 1))
  (define interp (make-interpreter expr '() (ckt:new-zeroed-counter_s) ckt:metadata))
  (define res (run* interp))
  (check-equal? res (@+ x 2)))

;; this is not supported:
#;(test-case "symbolic branch bitvector result"
  (define b (@fresh-symbolic 'b @boolean?))
  (define expr `(if ,b ,(@bv 1 1) ,(@bv 0 1)))
  (define interp (make-interpreter expr '() (ckt:new-zeroed-counter_s) ckt:metadata))
  (define res (run* interp))
  (check-equal? res (@if b (@bv 1 1) (@bv 0 1))))

;; a workaround:
(test-case "symbolic branch bitvector result, workaround"
  (define b (@fresh-symbolic 'b @boolean?))
  (define expr `(let ([bv1 (bv 1 1)]
                      [bv0 (bv 0 1)])
                  (if ,b bv1 bv0)))
  (define interp (make-interpreter expr '() (ckt:new-zeroed-counter_s) ckt:metadata))
  (define res (run* interp))
  (check-equal? res (@if b (@bv 1 1) (@bv 0 1))))
