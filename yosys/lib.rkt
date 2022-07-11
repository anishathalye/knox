#lang rosette/safe

(require
 (only-in rosette/base/core/bool [@true? true?])
 (only-in rosette/base/core/polymorphic ite)
 (for-syntax syntax/parse racket/syntax)
 (prefix-in ! (combine-in racket/base racket/match))
 syntax/parse/define
 "parameters.rkt"
 "libopt.rkt"
 rosutil)

(provide
 = distinct _ select store bvxnor
 (rename-out [$xor xor]
             [$if ite])
 ; exports from Rosette
 true false ; constants
 (rename-out [! not] [&& and] [|| or]) ; logical
 bv ; types
 bvult bvslt bvule bvsle bvuge bvsge bvugt bvsgt ; comparison
 bvnot bvand bvor bvxor bvshl bvlshr bvashr ; bitwise
 bvneg bvadd bvsub bvmul bvudiv bvsdiv bvurem bvsrem bvsmod ; arithmetic
 concat) ; conversion

(define-simple-macro ($if test-expr then-expr else-expr)
  (if* test-expr (thunk then-expr) (thunk else-expr)))

; this is a workaround for Rosette's `if` statement producing assertions
; when it's not necessary. `if` eventually calls `eval-assuming` to evaluate
; the then and else expressions. before doing so, `eval-assuming` augments
; the verification condition with the guard; sometimes, this immediately
; results in an exception due to the path being infeasible, and so `if`
; adds an assertion that the path condition (vc-assumes (vc)) implies that
; the test must be true or false (depending on which branch failed). this assertion,
; even though it's useless, sometimes gets added to the vc,
; because `(&& a b)`, which is used when augmenting the path condition,
; sometimes results in a concrete Racket value of `#f`, but `(=> a (! b))`,
; which is used when adding an assertion, does not simplify in Racket to `#t`
; even though it is provably so.
;
; this is an example of such a program:
;     (define-symbolic* a1 a2 boolean?)
;     (if a1 (if a2 0 (if (&& a1 a2) 1 2)) 3)
;
; after running this program, the (vc) is:
;     (vc (|| (! a1$0) (|| a2$1 (&& (&& a1$0 (! a2$1)) (! (&& a1$0 a2$1))))) #t)
;
; this thin wrapper around Rosette's `if` does this test eagerly, looking
; at the combination of the verification condition's assumption along
; with the test, and if it can be determined that the other path is
; infeasible, it skips evaluating it altogether.
;
; this should be safe to use with arbitrary Rosette code (even code
; e.g. involving mutation).
(define (if* test-expr then-expr else-expr)
  (define test (true? test-expr))
  (define assumes (vc-assumes (vc)))
  (!cond
   [(!or (!eq? test #t) (!not (&& assumes (! test))))
    (then-expr)]
   [(!or (!eq? test #f) (!not (&& assumes test)))
    (else-expr)]
   [else
    (rewrite-if (if test (then-expr) (else-expr)))]))

; we could implement this with `equal?`, but that is slow. Yosys uses `=` mostly for
; bitvectors, and only in a few cases for booleans. The boolean cases are:
;
; - in the invariant function, when comparing a boolean with the literal 'true' or 'false'
; - in the transition function (this is a macro anyways, that treats the '=' specially)
(define-syntax (= stx)
  (syntax-parse stx
    [(_ x:expr (~datum true))
     #'(<=> x true)]
    [(_ x:expr (~datum false))
     #'(<=> x false)]
    [(_ x:expr y:expr)
     #'(bveq x y)]))

(define (distinct x y)
  (not (bveq x y)))

(define ((extractor i j) x)
  (extract i j x))

(define-simple-macro (_ (~datum extract) i:expr j:expr)
  (extractor i j))

(define (select a i)
  (if (array-representation-vector)
      ; vector representation
      (let ([symbolic-index (not (concrete-head? i))]
            [thresh (overapproximate-symbolic-load-threshold)])
        (if (and symbolic-index thresh (>= (vector-length a) thresh))
            ; overapproximate, return fresh symbolic value
            (fresh-symbolic 'select-overapproximated-value (type-of (vector-ref a 0)))
            ; do the indexing into the vector
            (vector-ref-bv a i)))
      ; UF representation
      (a i)))

(define (vector-update vec pos v)
  (define symbolic-index (not (concrete-head? pos)))
  (define thresh (overapproximate-symbolic-store-threshold))
  (if (and symbolic-index thresh (>= (vector-length vec) thresh))
      (let ([type (type-of (vector-ref vec 0))])
        (!build-vector (vector-length vec)
                       (lambda (_) (fresh-symbolic 'overapproximation type))))
      ; XXX this seems inefficient
      (let ([vec-copy (list->vector (vector->list vec))])
        (vector-set!-bv vec-copy pos v)
        (vector->immutable-vector vec-copy))))

(define (store a i v)
  (if (array-representation-vector)
      ; vector representation
      (vector-update a i v)
      ; UF representation
      (lambda (i*) (if (bveq i i*) v (a i*)))))

(define (<=>* . args)
  (foldl <=> #t args))

; to match SMTLIB's xor, which can take multiple arguments
(define-syntax ($xor stx)
  (syntax-parse stx
    [(_ (~seq a0 a1) ...) #'(! (<=>* (~@ a0 a1) ...))]
    [(_ a (~seq b0 b1) ...) #'(<=>* a (~@ b0 b1) ...)]))

(define (bvxnor . args)
  (bvnot (apply bvxor args)))
