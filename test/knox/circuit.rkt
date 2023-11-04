#lang racket/base

(require
 rackunit yosys knox/circuit
 (prefix-in @ (combine-in rosette/safe rosutil))
 (rename-in "circuit/use_persistent_reset.rkt" [circuit use_persistent_reset]))

(test-case "crash+power-on-reset syncs persistent state before reset"
  (define c0 (@update-field ((meta-new-zeroed (circuit-meta use_persistent_reset))) 'count_persistent (@bv 42 8)))
  (define c1 ((crash+power-on-reset use_persistent_reset) c0))
  (check-pred @unsat? (@verify (@assert (@equal? (@get-field c0 'count_persistent) (@get-field c1 'count))))))
