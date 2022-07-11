#lang rosette/safe

(provide (struct-out result))

;; ideal functionality functions are curried, and have type
;; `args ... -> state -> result`
;;
;; For example, a lockbox's store op could be defined as
;; `(define ((store value) state) ...)`, returning a result
(struct result (value state)
  #:transparent)
