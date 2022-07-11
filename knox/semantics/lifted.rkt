#lang rosette/safe

(provide
 (rename-out
  [$bv bv]
  [$bitvector bitvector]))

(define ($bv val size)
  (for*/all ([val val]
             [size size])
    (bv val size)))

(define ($bitvector val)
  (for/all ([val val])
    (bitvector val)))
