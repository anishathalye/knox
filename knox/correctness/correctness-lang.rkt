#lang racket/base

(require
 (for-syntax racket/base racket/syntax syntax/parse)
 "correctness.rkt")

(provide
 (except-out
  (all-from-out racket/base)
  #%module-begin)
 (rename-out [$#%module-begin #%module-begin]))

(define-syntax ($#%module-begin stx)
  (syntax-parse stx
    [(_
      #:spec spec-module
      #:circuit circuit-module
      #:driver driver-module
      (~seq k:keyword v:expr) ...
      body ...)
     #:with spec (format-id stx "spec")
     #:with circuit (format-id stx "circuit")
     #:with driver (format-id stx "driver")
     #'(#%module-begin
        (require
         (only-in spec-module spec)
         (only-in circuit-module circuit)
         (only-in driver-module driver))
        body ...
        (verify-correctness
         spec
         circuit
         driver
         (~@ k v) ...))]))
