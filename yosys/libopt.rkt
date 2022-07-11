#lang racket/base

(require
 (prefix-in @ (combine-in
               rosette/safe
               (only-in rosette/base/core/polymorphic ite)
               (only-in rosette/base/core/type typed? get-type)))
 racket/match)

(provide rewrite-if rewrite-extract)

(define rewrite-if
  (match-lambda
    [(@expression (== @ite) (@expression (== @bveq) (== (@bv 0 1)) x) (== (@bv 0 1)) (== (@bv 1 1)))
     x]
    [x x]))

(module+ test
  (require rackunit)

  (test-case "rewrite-if"
    (@define-symbolic x (@bitvector 1))
    (define y (@if (@bveq x (@bv 0 1)) (@bv 0 1) (@bv 1 1)))
    (check-equal? (rewrite-if y) x)))

;; this rewrite rule wouldn't be accepted upstream because it creates extra new terms
;;
;; this is not in use right now, but it's here as an example of how to implement something like this
(define rewrite-extract
  (match-lambda
    [(@expression (== @extract) i j (@expression (== @concat)
                                                 (and (? @typed? (app @get-type (@bitvector size-l))) l)
                                                 (and (? @typed? (app @get-type (@bitvector size-r))) r)))
     #:when (and (>= i size-r) (< j size-r))
     (@concat (@extract (- i size-r) 0 l)
              (@extract (sub1 size-r) j r))]
    [x x]))

(module+ test
  (test-case "rewrite-extract"
    (@define-symbolic* x (@bitvector 8))
    (define y (@extract 7 1 (@concat (@extract 3 3 x) (@bv 0 7))))
    (check-equal? (rewrite-extract y)
                  (@concat (@extract 3 3 x) (@bv 0 6)))))
