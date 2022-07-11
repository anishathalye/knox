#lang racket/base

(require (prefix-in yosys: "../reader.rkt"))

(provide configure-runtime!)

(define (configure-runtime!)
  (current-read-interaction yosys:read-syntax))
