#lang racket/base

(require
 (prefix-in @ rosette/safe)
 yosys/meta)

(provide circuit-with-invariants)

;; returns a new circuit that satisfies invariants
;; and all other state is arbitrary
;;
;; (in practice, Rosette will zero it, but that's not guaranteed by the spec of complete-solution)
(define (circuit-with-invariants metadata)
  (define ckt-sym ((meta-new-symbolic metadata)))
  (define sol (@complete-solution (@solve (@assert ((meta-invariant metadata) ckt-sym)))
                                  (@symbolics ckt-sym)))
  (@evaluate ckt-sym sol))
