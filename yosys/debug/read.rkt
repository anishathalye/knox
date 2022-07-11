#lang racket/base

(require racket/pretty
         (for-syntax racket/base syntax/parse))

(provide (except-out (all-from-out racket/base) #%module-begin)
         (rename-out [yosys-debug-read-module-begin #%module-begin]))

(define-syntax (yosys-debug-read-module-begin stx)
  (syntax-parse stx
    [(_ form ...)
     #'(#%module-begin
        (pretty-print 'form (current-output-port) 1) ...)]))
