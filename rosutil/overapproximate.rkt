#lang racket/base

(require
 "convenience.rkt"
 "lens.rkt"
 racket/match
 (prefix-in @ rosette/safe))

(provide overapproximate)

(define (overapproximate view)
  (if (join? view)
      (join (map overapproximate (join-contents view)))
      (overapproximate-term view)))

(define (any->datum s)
  (if (identifier? s) (syntax-e s) s))

(define (overapproximate-term term)
  ;; do our best to generate a good name
  (fresh-symbolic
   (match term
     [(@constant id type)
      (match id
        [(list name (guid idnum)) (any->datum name)]
        [(list name _) (any->datum name)]
        [name (any->datum name)])]
     [else '||]) ; give up
   (@type-of term)))
