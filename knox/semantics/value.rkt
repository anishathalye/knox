#lang rosette/safe

(require (only-in "syntax.rkt" string? symbol?))

(provide
 basic-value?
 (struct-out closure))

;; basic-value ::=
;; | void?
;; | boolean?
;; | integer?
;; | string?
;; | bv?
;; | symbol?
;; | null?
;; | cons basic-value basic-value

(define (basic-value? v)
  (or (void? v)
      (boolean? v)
      (integer? v)
      (string? v)
      (bv? v)
      (symbol? v)
      (null? v)
      (and (cons? v) (basic-value? (car v)) (basic-value? (cdr v)))))

(struct closure
  (expr environment)
  #:transparent)
