#lang racket/base

(require (prefix-in @ rosette/safe)
         (for-syntax racket/base syntax/parse racket/syntax racket/list)
         (only-in "yosys.rkt" yosys-top))

(provide (rename-out
          [$#%module-begin #%module-begin])
         ; from Rosette
         (rename-out
          [@#%top-interaction #%top-interaction]
          [@#%app #%app]
          [@#%datum #%datum]
          [@#%top #%top]))

(define-syntax ($#%module-begin stx)
  #`(@#%module-begin
     (module configure-runtime racket/base
       (require yosys/lang/configure-runtime)
       (configure-runtime!))
     #,@(yosys-top stx)))
