#lang racket/base

(require (except-in "../verilog.rkt")
         (only-in "../yosys.rkt" yosys-top)
         (only-in rosette/safe [#%module-begin @#%module-begin])
         racket/pretty
         (for-syntax racket/base syntax/parse))

(provide (except-out (all-from-out "../verilog.rkt") #%module-begin)
         (rename-out [yosys-debug-expand-module-begin #%module-begin]))

(define-syntax (yosys-debug-expand-module-begin stx)
  (syntax-parse (yosys-top stx)
    [(_ form ... final)
     #'(@#%module-begin
        (let ([expanded (syntax->datum (expand-syntax-once #'form))])
          (unless (equal? expanded '(begin))
            (pretty-print expanded (current-output-port) 1))) ...
        (pretty-print 'final (current-output-port) 1))]))
