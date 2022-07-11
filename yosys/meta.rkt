#lang racket/base

(require racket/function)

(provide (struct-out meta)
         dummy-metadata)

(struct meta (new-symbolic
              new-zeroed
              invariant
              step
              input
              new-symbolic-input
              input*
              input-getters
              with-input
              output
              new-symbolic-output
              output*
              output-getters
              get-input
              get-output)
  #:transparent)

(define dummy-metadata
  (meta
   (thunk #t)
   (thunk #t)
   (lambda (_) #t)
   identity
   (thunk #t)
   (thunk #t)
   (lambda args #t)
   '()
   (lambda (s i) s)
   (thunk #t)
   (thunk #t)
   (lambda args #t)
   '()
   (lambda (s) #t)
   (lambda (s) #t)))
