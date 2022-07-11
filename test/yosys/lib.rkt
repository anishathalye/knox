#lang racket/base

(require racket/list
         rackunit
         (prefix-in @ rosette/safe)
         (prefix-in $ yosys/lib))

(test-case "if"
  (@define-symbolic* a b @boolean?)
  (check-true (@vc-assumes (@vc)))
  (define t
    ($ite a ($ite b 0 ($ite (@&& a b) 1 2)) 3))
  (check-true (@vc-assumes (@vc)))
  ; a quick sanity check to make sure we didn't break symbolic evaluation
  (check-equal? (@evaluate t (@solve (@assert (@and a b)))) 0)
  (check-equal? (@evaluate t (@solve (@assert (@and a (@not b))))) 2))

(test-case "xor"
  (@define-symbolic* a b c d e f @boolean?)
  (define (xor2 x y)
    (@! (@<=> x y)))
  (define (reference-xor . args)
    (@foldl xor2 #f args))
  (check-pred @unsat? (@verify (@assert (@equal? (reference-xor a) ($xor a)))))
  (check-pred @unsat? (@verify (@assert (@equal? (reference-xor a b) ($xor a b)))))
  (check-pred @unsat? (@verify (@assert (@equal? (reference-xor a b c) ($xor a b c)))))
  (check-pred @unsat? (@verify (@assert (@equal? (reference-xor a b c d) ($xor a b c d)))))
  (check-pred @unsat? (@verify (@assert (@equal? (reference-xor a b c d e) ($xor a b c d e))))))

(test-case "select/store asserts"
  (@define-symbolic* i (@bitvector 3))
  (define v (@vector 0 1 2 3 4 5 6 7))
  ($select v i)
  (check-true (@vc-asserts (@vc)))
  ($store v i -1)
  (check-true (@vc-asserts (@vc))))
