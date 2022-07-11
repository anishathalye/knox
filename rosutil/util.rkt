#lang racket/base

(require
 (for-syntax racket/base syntax/parse))

(provide define/internally-memoizing)

; we are not reusing the yosys/memoize stuff because that has a global
; memoization context (which makes sense for the Yosys stuff, because we
; want a global context where we do inter-procedural memoization
(define-syntax (define/internally-memoizing stx)
  (syntax-parse stx
    [(_ (name:id arg:id) body ...)
     #'(define (name arg)
         (define memo-table (make-hasheq))
         (define (name arg [use-memo-table #t])
           (if use-memo-table
               (if (hash-has-key? memo-table arg)
                   (hash-ref memo-table arg)
                   (let ([value (name arg #f)])
                     (hash-set! memo-table arg value)
                     value))
               (let () body ...)))
         (name arg))]))
