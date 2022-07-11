#lang racket/base

(require
 racket/match
 racket/set
 racket/list
 racket/function
 data/union-find
 (prefix-in @
  (combine-in
   rosette/safe
   (only-in rosette/base/core/type typed? get-type type-deconstruct)
   "convenience.rkt"
   "addressable-struct.rkt")))

(provide subsumed?)

;; Take two Rosette values (potentially structs, vectors, etc.) and return a list of pairs of Rosette terms from corresponding parts of the two structs
;; as well as a list of symbolic variables that appear free in skipped terms (we need this to do a check later).
;;
;; At a high level, the goal is to get rid of equal stuff so it doesn't make its way to the solver. But we have to be careful what we get rid of,
;; because it might break soundness if we do this wrong.
;;
;; This function is conservative and bails out on some stuff that's hard to analyze (e.g. unions; we don't rely on those).
;;
;; Returns false if one can't subsume another (e.g. due to type mismatch).
;;
;; any -> any -> (values list list seteq?)
(define (mismatched v1 v2 #:keep [keep-symbolics (seteq)])
  (define (mismatched-fail) (values #f #f (seteq)))
  (let rec ([v1 v1] [v2 v2] [l1 '()] [l2 '()] [s (seteq)])
    (define (rec-lists v1 v2)
      ;; assumes that v1 and v2 are lists of equal length
      (for/fold ([l1 l1]
                 [l2 l2]
                 [s s])
                ([x1 (in-list v1)]
                 [x2 (in-list v2)])
        #:break (not l1)
        (rec x1 x2 l1 l2 s)))
    (match v1
      [(? @union?) (mismatched-fail)] ; give up
      [(or (? @expression?) (? @constant?))
       (cond
         [(equal? (@type-of v1) (@type-of v2))
          (cond
            [(equal? v1 v2)
             (let ([sym (list->seteq (@symbolics (@list v1 v2)))])
               (cond
                 ;; can we skip adding these terms? i.e. do they not contain any symbolics in keep-symbolics?
                 [(set-empty? (set-intersect sym keep-symbolics))
                  (values l1 l2 (set-union s sym))]
                 [else (values (cons v1 l1) (cons v2 l2) s)]))]
            [else (values (cons v1 l1) (cons v2 l2) s)])]
         [else (mismatched-fail)])]
      [(box x1)
       (match v2
         [(box x2) (rec x1 x2 l1 l2 s)]
         [_ (mismatched-fail)])]
      [(? list?)
       (match v2
         [(? list?)
          (cond
            [(equal? (length v1) (length v2))
             (rec-lists v1 v2)]
            [else (mismatched-fail)])]
         [_ (mismatched-fail)])]
      [(cons x1 y1)
       (match v2
         [(cons x2 y2)
          (define-values (l1* l2* s*) (rec x1 x2 l1 l2 s))
          (if l1*
              (rec y1 y2 l1* l2* s*)
              (mismatched-fail))]
         [_ (mismatched-fail)])]
      [(vector x1s ...)
       (match v2
         [(vector x2s ...)
          (cond
            [(equal? (length x1s) (length x2s))
             (rec-lists x1s x2s)]
            [else (mismatched-fail)])]
         [_ (mismatched-fail)])]
      [(and (? @typed?) (app @get-type t1))
       (match v2
         [(and (? @typed?) (app @get-type t2))
          (cond
            [(equal? t1 t2)
             (cond
               ;; we don't need to special-case other Rosette datatypes
               ;; (bool, int, real) because their constants aren't recognized by
               ;; @typed?, and their symbolic variables / expressions are recognized
               ;; above
               [(@bitvector? t1)
                (cond
                  [(equal? v1 v2)
                   ;; this check is the same as above, in the expression/constant case
                   (let ([sym (list->seteq (@symbolics (@list v1 v2)))])
                     (cond
                       ;; can we skip adding these terms? i.e. do they not contain any symbolics in keep-symbolics?
                       [(set-empty? (set-intersect sym keep-symbolics))
                        (values l1 l2 (set-union s sym))]
                       [else (values (cons v1 l1) (cons v2 l2) s)]))]
                  [else (values (cons v1 l1) (cons v2 l2) s)])]
               [else
                (rec-lists (@type-deconstruct t1 v1) (@type-deconstruct t2 v2))])]
            [else (mismatched-fail)])]
         [_ (mismatched-fail)])]
      [_
       (match v2
         [(? @union?) (mismatched-fail)] ; give up
         [(or (? @expression?) (? @constant?))
          (cond
            [(equal? (@type-of v1) (@type-of v2))
             (cond
               [(equal? v1 v2)
                (values l1 l2 (set-union s (list->seteq (@symbolics (@list v1 v2)))))]
               [else (values (cons v1 l1) (cons v2 l2) s)])]
            [else (mismatched-fail)])]
         [(box _) (mismatched-fail)] ; v1 is not a box
         [(? list?) (mismatched-fail)] ; v1 is not a list
         [(cons _ _) (mismatched-fail)] ; v1 is not a cons
         [(vector _ ...) (mismatched-fail)] ; v1 is not a vector
         [(? @typed?) (mismatched-fail)] ; v1 is not typed
         [_
          (cond
            ;; both are concrete values: do they differ?
            [(equal? v1 v2) (values l1 l2 s)]
            [else (mismatched-fail)])])])))

(module+ test
  (require rosette/safe rackunit)

  (test-case "mismatched: symbolics"
    (define-symbolic x y integer?)
    (define-values (l1 l2 s) (mismatched x y))
    (check-equal? l1 (list x))
    (check-equal? l2 (list y))
    (check-equal? s (seteq)))

  (test-case "mismatched: fully matched"
    (define-symbolic x y integer?)
    (define-values (l1 l2 s) (mismatched (list 1 2 x y) (list 1 2 x y)))
    (check-equal? l1 '())
    (check-equal? l2 '())
    (check-equal? s (seteq x y)))

  (test-case "mismatched: cons"
    (define-symbolic x y (bitvector 10))
    (define-values (l1 l2 s) (mismatched (cons x x) (cons x y)))
    (check-equal? l1 (list x))
    (check-equal? l2 (list y))
    (check-equal? s (seteq x)))

  (test-case "mismatched: length mismatch"
    (define-symbolic x y (bitvector 10))
    (define-values (l1 l2 s) (mismatched (list x y 0) (list x y)))
    (check-false l1)
    (check-false l2)
    (check-equal? s (seteq)))

  (test-case "mismatched: vector"
    (define-symbolic x y (bitvector 10))
    (define-values (l1 l2 s) (mismatched (vector x (cons y 3)) (vector x (cons x 3))))
    (check-equal? l1 (list y))
    (check-equal? l2 (list x))
    (check-equal? s (seteq x)))

  (test-case "mismatched: vector length mismatch"
    (define-symbolic x y (bitvector 10))
    (define-values (l1 l2 s) (mismatched (vector x y 0) (vector x y)))
    (check-false l1)
    (check-false l2)
    (check-equal? s (seteq)))

  (test-case "mismatched: constants"
    (define-symbolic x integer?)
    (define-values (l1 l2 s) (mismatched (list 1 x) (list x 1)))
    (check-equal? l1 (list x 1))
    (check-equal? l2 (list 1 x))
    (check-equal? s (seteq)))

  (test-case "mismatched: constants mismatched"
    (define-symbolic x integer?)
    (define-values (l1 l2 s) (mismatched (list 1 3 4 x) (list 7 3 6 8)))
    (check-false l1)
    (check-false l2)
    (check-equal? s (seteq)))

  (test-case "mismatched: type mismatch"
    (define-symbolic x boolean?)
    (define-values (l1 l2 s) (mismatched (list 1 3 4 x) (list 7 3 6 8)))
    (check-false l1)
    (check-false l2)
    (check-equal? s (seteq)))

  (test-case "mismatched: struct"
    (struct foo (a b) #:transparent)
    (define-symbolic x y integer?)
    (define-values (l1 l2 s) (mismatched (foo (cons x y) 3) (foo (cons y y) x)))
    (check-equal? l1 (list 3 x))
    (check-equal? l2 (list x y))
    (check-equal? s (seteq y)))

  (test-case "mismatched: struct type mismatch"
    (struct foo (a b) #:transparent)
    (struct bar (a b) #:transparent)
    (define-symbolic x y integer?)
    (define-values (l1 l2 s) (mismatched (foo x y) (bar x y)))
    (check-false l1)
    (check-false l2)
    (check-equal? s (seteq)))

  (test-case "mismatched: nested structs, lists, etc."
    (struct foo (a b) #:transparent)
    (struct bar (a b) #:transparent)
    (define-symbolic x y z integer?)
    (define-values (l1 l2 s) (mismatched (foo (bar x y) (foo 1 (list 3 z))) (foo (bar x x) (foo 1 (list y 5)))))
    (check-equal? l1 (list z 3 y))
    (check-equal? l2 (list 5 y x))
    (check-equal? s (seteq x)))

  (test-case "mismatched: keep-symbolics are not discarded"
    (define-symbolic x y (bitvector 8))
    (define-values (l1 l2 s) (mismatched (list x y) (list x y)))
    (check-equal? l1 '())
    (check-equal? l2 '())
    (check-equal? s (seteq x y))
    (define-values (l1* l2* s*) (mismatched (list x y) (list x y) #:keep (seteq x)))
    (check-equal? l1* (list x))
    (check-equal? l2* (list x))
    (check-equal? s* (seteq y)))

  (test-case "mismatched: keep-symbolics are not discarded, with integer type"
    (define-symbolic x y integer?)
    (define-values (l1 l2 s) (mismatched (list x y) (list x y)))
    (check-equal? l1 '())
    (check-equal? l2 '())
    (check-equal? s (seteq x y))
    (define-values (l1* l2* s*) (mismatched (list x y) (list x y) #:keep (seteq x)))
    (check-equal? l1* (list x))
    (check-equal? l2* (list x))
    (check-equal? s* (seteq y))))

(define (terms-subsumed? free-symbolics small small-cond big big-cond)
  (let* ([types (map @type-of small)]
         [temp (map (curry @fresh-symbolic '__temp) types)]
         [free-list (set->list free-symbolics)]
         [small-body (@and small-cond (@equal? small temp))]
         [small-can-match (@exists free-list small-body)]
         [big-body (@and big-cond (@equal? big temp))]
         [big-can-match (@exists free-list big-body)]
         [body (@implies small-can-match big-can-match)]
         [q (@not body)])
    (@unsat? (@solve (@assert q)))))

;; an alternative implementation that returns a useful model (the above implementation doesn't because everything is under quantifiers)
(define (terms-subsumed*? free-symbolics small small-cond big big-cond)
  (let* ([types (map @type-of small)]
         [temp (map (curry @fresh-symbolic '__temp) types)]
         [free-list (set->list free-symbolics)]
         [body (@and (@equal? big temp) big-cond)]
         ;; could also encode the "not exists" as a "forall not"; performance seems to be equivalent
         [big-cant-match (@not (@exists free-list body))]
         [q (@and (@equal? small temp) small-cond big-cant-match)])
    (@solve (@assert q))))

;; returns indices grouping together terms that have overlapping symbolics
(define (connected-components terms)
  (define symbolic->uf-set (make-hasheq))
  ;; union together the symbolics in the term and also construct
  ;; a list of a representative uf-set? (or #f if there are no symbolics)
  (define index->rep
    (for/hasheq ([term (in-list terms)]
                 [i (in-naturals)])
      (define sym (@symbolics term))
      (for ([s (in-list sym)])
        (unless (hash-has-key? symbolic->uf-set s)
          (hash-set! symbolic->uf-set s (uf-new s))))
      (unless (or (empty? sym) (empty? (rest sym)))
        (for ([s1 (in-list sym)]
              [s2 (in-list (rest sym))])
          (uf-union!
           (hash-ref symbolic->uf-set s1)
           (hash-ref symbolic->uf-set s2))))
      (values i (if (empty? sym) #f (hash-ref symbolic->uf-set (first sym))))))
  ;; two terms are in the same group if they share any symbolics; we
  ;; can look up any symbolic contained in the term
  (group-by
   (lambda (i)
     (define rep (hash-ref index->rep i))
     ;; find canonical element if there is a representative
     (if (uf-set? rep) (uf-find rep) (gensym)))
   (range (length terms))))

(module+ test
  (test-case "connected-components: basic"
    (@define-symbolic* x y z @integer?)
    (check-equal?
     (connected-components (list (@+ x y) (@- z) (@+ x 3) (@+ y 4) (@+ z 5) (@- z 6) 3 #t))
     '((0 2 3) (1 4 5) (6) (7))))

  (test-case "connected-components: transitive"
    (@define-symbolic* w x y z @integer?)
    (check-equal?
     (connected-components (list (@+ w x) (@+ x y) (@+ y z) (@+ z 3) (@+ x 5) 7))
     '((0 1 2 3 4) (5)))))

;; takes a list of lists, of indices, and returns a new grouping
;; where two elements are in the same group if they're in the same
;; grouping in either lut1 or lut2
(define (join-components groups1 groups2)
  (define idx->uf-set (make-hasheqv))
  (for* ([groups (in-list (list groups1 groups2))]
         [group (in-list groups)])
    (for ([i (in-list group)])
      (unless (hash-has-key? idx->uf-set i)
        (hash-set! idx->uf-set i (uf-new i))))
    (unless (empty? (rest group))
      (for ([i1 (in-list group)]
            [i2 (in-list (rest group))])
        (uf-union!
         (hash-ref idx->uf-set i1)
         (hash-ref idx->uf-set i2)))))
  (group-by
   (lambda (i) (uf-find (hash-ref idx->uf-set i)))
   (range (apply + (map length groups1)))))

(define (get-fields group vec)
  (for/fold ([acc '()])
            ([i (in-list group)])
    (if (zero? i)
        acc
        (cons (vector-ref vec (sub1 i)) acc))))

;; skip the fields that are equal? to each other, but not skipping
;; terms that overlap with ones that are kept
(define (skip-equal-dedupe small big [keep-symbolics (seteq)])
  (define-values (small* big* skipped-symbolics)
    (for/fold ([small* '()]
               [big* '()]
               [skipped-symbolics (seteq)])
              ([small-term small]
               [big-term big])
      #:break (not small*)
      (let ([sym-small (list->seteq (@symbolics small-term))])
        (cond
          ;; equal terms that we can skip
          [(and (equal? small-term big-term)
                (set-empty? (set-intersect sym-small keep-symbolics)))
           (values small* big* (set-union skipped-symbolics sym-small))]
          ;; definitely unequal terms, bail out early
          [(and (@concrete? small-term) (@concrete? big-term) (not (equal? small-term big-term)))
           (values #f #f #f)]
          ;; keep this term
          [else
           (values (cons small-term small*) (cons big-term big*) skipped-symbolics)]))))
  (cond
    ;; definitely not equal
    [(not small*) (values #f #f)]
    [else
     ;; check
     (define kept-symbolics (@symbolics (@cons small* big*)))
     (define overlap-symbolics (set-intersect (list->seteq kept-symbolics) skipped-symbolics))
     (if (set-empty? overlap-symbolics)
         ;; de-dupe before returning
         (let ([included (mutable-set)])
           (for/fold ([small** '()]
                      [big** '()])
                     ([small-term small*]
                      [big-term big*])
             (let ([pair (cons small-term big-term)])
               (if (set-member? included pair)
                   (values small** big**)
                   (let ()
                     (set-add! included pair)
                     (values (cons small-term small**) (cons big-term big**)))))))
         ;; give up / recurse
         (skip-equal-dedupe small big (set-union keep-symbolics overlap-symbolics)))]))

(define (subsumed? free-symbolics small small-cond big big-cond #:skip-empty-check [skip-empty-check #f])
  (define-values (small-terms big-terms) (flatten2 small big #:fail-fast #t))
  (define all-components-subsumed
    (cond
      ;; shapes don't match
      [(not small-terms) #f]
      [else
       ;; consider the conds as "terms" so we include it in the connected components, at index 0
       (define small-components (connected-components (cons small-cond small-terms)))
       (define big-components (connected-components (cons big-cond big-terms)))
       ;; now, we need to group together _across_ small and big, to know
       ;; all the field sets that need to be compared together
       (define components (join-components small-components big-components))
       ;; vectors for random addressing
       (define small-vec (list->vector small-terms))
       (define big-vec (list->vector big-terms))
       ;; iterate over groups, do subsumption check for each
       ;;
       ;; note: first group has the predicate (because of order preservation)
       ;; indices into term lists are 1-based (because of predicate)
       (for/and ([group components])
         (let*-values ([(group-small-cond) (if (zero? (first group)) small-cond #t)]
                       [(group-big-cond) (if (zero? (first group)) big-cond #t)]
                       [(no-cond) (and (eqv? group-small-cond #t) (eqv? group-big-cond #t))]
                       [(cond-symbolics) (if no-cond (seteq) (list->seteq (@symbolics (@cons group-small-cond group-big-cond))))]
                       [(group-small-fields group-big-fields) (skip-equal-dedupe (get-fields group small-vec) (get-fields group big-vec) cond-symbolics)])
           (cond
             ;; definitely not equal
             [(not group-small-fields) #f]
             ;; length 0, no cond
             [(and no-cond (empty? group-small-fields)) #t]
             ;; length 0, with cond
             [(empty? group-small-fields)
              ;; big set just needs to be non-empty
              (@sat? (@solve (@assert group-big-cond)))]
             ;; length 1, no cond, and big is a free symbolic (doesn't matter what small is, types have been checked already)
             ;; no solver query required
             [(and no-cond (empty? (rest group-big-fields))
                   (let ([b (first group-big-fields)])
                     (and (@constant? b) (or (not free-symbolics) (set-member? free-symbolics b)))))
              #t]
             ;; fallback: solver query
             [else
              (let* ([present-symbolics (@symbolics (@list group-small-fields group-small-cond group-big-fields group-big-cond))]
                     [free-symbolics (if free-symbolics (set-intersect free-symbolics (list->seteq present-symbolics)) present-symbolics)])
                (terms-subsumed? free-symbolics group-small-fields group-small-cond group-big-fields group-big-cond))])))]))
  ;; the above check covers most cases, but there's one other case
  ;; that's not covered: if small-cond is false, then the set that is
  ;; described is the empty set, and that is vacuously subsumed,
  ;; even though the component-wise check could return false
  (or all-components-subsumed
      ;; avoid a solver query if it's unnecessary... small-cond is probably not unsat
      (if (or (eqv? small-cond #t) skip-empty-check)
          #f
          (@unsat? (@solve (@assert small-cond))))))

;; free-symbolics can be a set or #f
(define (old-subsumed? free-symbolics small small-cond big big-cond #:find-model [find-model #f] #:extra-keep [extra-keep (seteq)])
  (define cond-symbolics (list->seteq (@symbolics (@list small-cond big-cond)))) ; we can't get rid of these
  (define keep-symbolics (set-union cond-symbolics extra-keep))
  (define-values (small-fields big-fields skipped-symbolics) (mismatched small big #:keep keep-symbolics))
  (cond
    ;; if they are definitely not equal, we can return false right away
    [(not small-fields)
     (define m (@solve (@assert small-cond)))
     (if find-model m (@unsat? m))]
    [else
     ;; need to check if any things we skipped are also included in the remaining fields;
     ;; if so, we could fall back to a slow path (either figure out how to re-add some of the things
     ;; we skipped, or just start over and call the "reference implementation" reference-subsumed?,
     ;; but we can also just be conservative and return false
     (let* ([remaining-symbolics (list->seteq (@symbolics (@list small-fields big-fields)))]
            [remaining-free-symbolics (if free-symbolics (set-intersect free-symbolics remaining-symbolics) remaining-symbolics)]
            [free-symbolics (or free-symbolics (set-union remaining-symbolics cond-symbolics))] ; default if free-symbolics is not given
            [incorrectly-skipped-symbolics (set-intersect remaining-free-symbolics skipped-symbolics)])
       (cond
         ;; Bail out if any captured fields share symbolics that are free
         ;; with any non-captured fields: this case is quite complicated to
         ;; handle, and we may not need to handle this if it doesn't come up.
         ;;
         ;; An example is the query {x, x+1} <=? {x, x}. We would end up with
         ;; the mismatched fields (x+1), (x). If the query were just {x+1} <= {x}
         ;; for some bitvector x with no other constraints, the result would be
         ;; true, but with this example, it is false.
         [(not (set-empty? incorrectly-skipped-symbolics))
          ;; rather than bailing out here, we can recurse, and make sure we keep these incorrectly skipped ones;
          ;; this might be slow, but it's better than bailing out
          (old-subsumed? free-symbolics small small-cond big big-cond #:find-model find-model #:extra-keep (set-union extra-keep incorrectly-skipped-symbolics))]
         [else ((if find-model terms-subsumed*? terms-subsumed?) free-symbolics small-fields small-cond big-fields big-cond)]))]))

;; we need to check if the shape of the structures matches (we can't just flatten each independently,
;; otherwise we might think e.g. (cons 1 (cons 2 3)) is the same as (cons (cons 1 2) 3).
;; but we don't have to prune equal values, the solver can handle that for us
(define (flatten2 v1 v2 [l1 '()] [l2 '()] #:fail-fast [fail-fast #f])
  (define (flatten2-fail) (values #f #f))
  (define (flatten2-lists-equal-length v1 v2)
    (for/fold ([l1 l1]
               [l2 l2])
              ([x1 (in-list v1)]
               [x2 (in-list v2)])
      #:break (not l1)
      (flatten2 x1 x2 l1 l2 #:fail-fast fail-fast)))
  (match v1
    [(? @union?) (flatten2-fail)] ; give up
    [(or (? @expression?) (? @constant?))
     (cond
       [(equal? (@type-of v1) (@type-of v2)) (values (cons v1 l1) (cons v2 l2))]
       [else (flatten2-fail)])]
    [(box x1)
     (match v2
       [(box x2) (flatten2 x1 x2 l1 l2 #:fail-fast fail-fast)]
       [_ (flatten2-fail)])]
    [(? list?)
     (match v2
       [(? list?)
        (cond
          [(equal? (length v1) (length v2))
           (flatten2-lists-equal-length v1 v2)]
          [else (flatten2-fail)])]
       [_ (flatten2-fail)])]
    [(cons x1 y1)
     (match v2
       [(cons x2 y2)
        (define-values (l1* l2*) (flatten2 x1 x2 l1 l2 #:fail-fast fail-fast))
        (if l1*
            (flatten2 y1 y2 l1* l2* #:fail-fast fail-fast)
            (flatten2-fail))]
       [_ (flatten2-fail)])]
    [(vector x1s ...)
     (match v2
       [(vector x2s ...)
        (cond
          [(equal? (length x1s) (length x2s))
           (flatten2-lists-equal-length x1s x2s)]
          [else (flatten2-fail)])]
       [_ (flatten2-fail)])]
    [(and (? @typed?) (app @get-type t1))
     (match v2
       [(and (? @typed?) (app @get-type t2))
        (cond
          [(equal? t1 t2)
           (cond
             ;; we don't need to special-case other Rosette datatypes
             ;; (bool, int, real) because their constants aren't recognized by
             ;; @typed?, and their symbolic variables / expressions are recognized
             ;; above
             [(@bitvector? t1)
              (if (and fail-fast (@concrete? v1) (@concrete? v2))
                  (if (equal? v1 v2) (values l1 l2) (flatten2-fail))
                  (values (cons v1 l1) (cons v2 l2)))]
             [else (flatten2-lists-equal-length (@type-deconstruct t1 v1) (@type-deconstruct t2 v2))])]
          [else (flatten2-fail)])]
       [_ (flatten2-fail)])]
    [_
     (match v2
       [(? @union?) (flatten2-fail)] ; give up
       [(or (? @expression?) (? @constant?))
        (cond
          [(equal? (@type-of v1) (@type-of v2)) (values (cons v1 l1) (cons v2 l2))]
          [else (flatten2-fail)])]
       [(box _) (flatten2-fail)] ; v1 is not a box
       [(? list?) (flatten2-fail)] ; v1 is not a list
       [(cons _ _) (flatten2-fail)] ; v1 is not a cons
       [(vector _ ...) (flatten2-fail)] ; v1 is not a vector
       [(? @typed?) (flatten2-fail)] ; v1 is not typed
       [_
        (if (and fail-fast (@concrete? v1) (@concrete? v2))
            (if (equal? v1 v2) (values l1 l2) (flatten2-fail))
            (values (cons v1 l1) (cons v2 l2)))])]))

(module+ test
  (test-case "flatten2: symbolics"
    (define-symbolic x y integer?)
    (define-values (l1 l2) (flatten2 x y))
    (check-equal? l1 (list x))
    (check-equal? l2 (list y)))

  (test-case "flatten2: fully matched"
    (define-symbolic x y integer?)
    (define-values (l1 l2) (flatten2 (list 1 2 x y) (list 1 2 x y)))
    (check-equal? l1 (list y x 2 1))
    (check-equal? l2 (list y x 2 1)))

  (test-case "flatten2: cons"
    (define-symbolic x y (bitvector 10))
    (define-values (l1 l2) (flatten2 (cons x x) (cons x y)))
    (check-equal? l1 (list x x))
    (check-equal? l2 (list y x)))

  (test-case "flatten2: length mismatch"
    (define-symbolic x y (bitvector 10))
    (define-values (l1 l2) (flatten2 (list x y 0) (list x y)))
    (check-false l1)
    (check-false l2))

  (test-case "flatten2: vector"
    (define-symbolic x y (bitvector 10))
    (define-values (l1 l2) (flatten2 (vector x (cons y 3)) (vector x (cons x 3))))
    (check-equal? l1 (list 3 y x))
    (check-equal? l2 (list 3 x x)))

  (test-case "flatten2: vector length mismatch"
    (define-symbolic x y (bitvector 10))
    (define-values (l1 l2) (flatten2 (vector x y 0) (vector x y)))
    (check-false l1)
    (check-false l2))

  (test-case "flatten2: constants"
    (define-symbolic x integer?)
    (define-values (l1 l2) (flatten2 (list 1 x) (list x 1)))
    (check-equal? l1 (list x 1))
    (check-equal? l2 (list 1 x)))

  (test-case "flatten2: constants mismatch"
    (define-symbolic x integer?)
    (define-values (l1 l2) (flatten2 (list 1 3 4 x) (list 7 3 6 8)))
    (check-equal? l1 (list x 4 3 1))
    (check-equal? l2 (list 8 6 3 7)))

  (test-case "flatten2: type mismatch"
    (define-symbolic x boolean?)
    (define-values (l1 l2) (flatten2 (list 1 3 4 x) (list 7 3 6 8)))
    (check-false l1)
    (check-false l2))

  (test-case "flatten2: struct"
    (struct foo (a b) #:transparent)
    (define-symbolic x y integer?)
    (define-values (l1 l2) (flatten2 (foo (cons x y) 3) (foo (cons y y) x)))
    (check-equal? l1 (list 3 y x))
    (check-equal? l2 (list x y y)))

  (test-case "flatten2: struct type mismatch"
    (struct foo (a b) #:transparent)
    (struct bar (a b) #:transparent)
    (define-symbolic x y integer?)
    (define-values (l1 l2) (flatten2 (foo x y) (bar x y)))
    (check-false l1)
    (check-false l2))

  (test-case "flatten2: nested structs, lists, etc."
    (struct foo (a b) #:transparent)
    (struct bar (a b) #:transparent)
    (define-symbolic x y z integer?)
    (define-values (l1 l2) (flatten2 (foo (bar x y) (foo 1 (list 3 z))) (foo (bar x x) (foo 1 (list y 5)))))
    (check-equal? l1 (list z 3 1 y x))
    (check-equal? l2 (list 5 y 1 x x))))

;; a "more obviously correct" implementation used to cross-check subsumed? in tests
;; (if correct impl returns false, efficient impl should return false)
;;
;; this uses flatten2 instead of mismatched, so it doesn't need to do
;; the intersection check like subsumed? does
(define (reference-subsumed? free-symbolics small small-cond big big-cond)
  (define-values (small-fields big-fields) (flatten2 small big))
  (cond
    [(not small-fields) (@unsat? (@solve (@assert small-cond)))] ; shape mismatch
    [else
     (let ([free-symbolics (or free-symbolics (list->seteq (@symbolics (@list small-fields small-cond big-fields big-cond))))])
       (terms-subsumed? free-symbolics small-fields small-cond big-fields big-cond))]))

(module+ test
  (require yosys/generic)

  (define-check (check-subsumed expected free-symbolics small small-cond big big-cond)
    (define reference-subsumed?-result (reference-subsumed? free-symbolics small small-cond big big-cond))
    (check-eqv? reference-subsumed?-result expected "reference implementation did not produce correct result")
    (define subsumed?-result (subsumed? free-symbolics small small-cond big big-cond))
    (check-eqv? subsumed?-result expected "efficient implementation did not produce correct result")
    (define old-subsumed?-result (old-subsumed? free-symbolics small small-cond big big-cond))
    (check-eqv? old-subsumed?-result expected "old implementation did not produce correct result")
    (define old-subsumed?-model (old-subsumed? free-symbolics small small-cond big big-cond #:find-model #t))
    (check-pred (if expected @unsat? @sat?) old-subsumed?-model "old model-finding implementation did not produce correct result"))

  (struct mod (a b c) #:transparent
    ;; these method implementations aren't really necessary, but they
    ;; will make this struct mirror #lang yosys output
    #:methods gen:yosys-module []
    #:methods @gen:addressable
    [(define (fields p) '(a b c))
     (define (get-field p s)
       (case s
         [(a) (mod-a p)]
         [(b) (mod-b p)]
         [(c) (mod-c p)]))
     (define (field-type p s)
       (error "not implemented"))
     (define (map-fields p f)
       (error "not implemented"))])

  (test-case "subsumed?: mismatched shapes but empty"
    (check-subsumed true #f (list 1 2) #f (list 1) #t))

  (test-case "subsumed?: input-sensitive"
    (define-symbolic* x y (bitvector 32))
    (define s1 (mod (bv 1 8) x y))
    (define s2 (mod (bv 1 8) y x))
    (check-subsumed false (seteq) s1 #t s2 #t)
    (check-subsumed false (seteq x) s1 #t s2 #t)
    (check-subsumed true (seteq x y) s1 #t s2 #t))

  (test-case "subsumed?: mismatched shapes or definitely not equal"
    (define-symbolic* x boolean?)
    (define-symbolic* y (bitvector 8))
    (check-subsumed false #f (list 3) #t 3 #t)
    (check-subsumed false #f x #t y #t))

  (test-case "subsumed?: abstract"
    (define-symbolic* x y (bitvector 32))
    (check-subsumed true (seteq x y) (mod #f #f x) #t (mod #f #f y) #t)
    (check-subsumed true (seteq y) (mod #f #f x) #t (mod #f #f y) #t)
    (check-subsumed false (seteq x) (mod #f #f x) #t (mod #f #f y) #t))

  (test-case "subsumed?: basic math"
    (define-symbolic* x (bitvector 32))
    (check-subsumed true (seteq x) (mod #f #f x) #t (mod #f #f (bvadd x (bv 1 32))) #t)
    (check-subsumed true (seteq x) (mod #f #f (bvadd x (bv 1 32))) #t (mod #f #f x) #t)
    (check-subsumed false (seteq x) (mod #f #f x) #t (mod #f #f (bvmul x (bv 2 32))) #t)
    (check-subsumed true (seteq x) (mod #f #f (bvmul x (bv 2 32))) #t (mod #f #f x) #t))

  (test-case "subsumed?: entanglement"
    (define-symbolic* x y (bitvector 32))
    (check-subsumed false (seteq x y) (mod #f x y) #t (mod #f x x) #t)
    ;; the following case works due to recursing with keep symbolics
    (check-subsumed true (seteq x y) (mod #f x x) #t (mod #f x y) #t)
    (check-subsumed false (seteq x y) (mod #f x x) #t (mod #f x (bvadd x (bv 1 32))) #t)
    (check-subsumed true #f (mod #f x x) #t (mod #f y (bvadd x (bv 1 32))) #t))

  (test-case "subsumed? can't skip conditions"
    (define-symbolic* x y integer?)
    ;; if we ignored the conditions, this would be true, but with the conditions, it's false
    (define p (equal? y 0))
    (check-subsumed false #f x p y p)
    ;; if we ignored the conditions, this would be false, but with the conditions, it's true
    (check-subsumed true #f y p 0 p))

  (test-case "subsumed?: conditions"
    (define-symbolic* x y integer?)
    (check-subsumed true #f (list x y) #t (list (+ 1 x) y) #t)
    (check-subsumed false #f (list x y) (even? x) (list (+ 1 x) y) (even? x))
    (check-subsumed true #f (list x y) #t (list x y) #t)
    (check-subsumed true #f (list x y) (even? x) (list x y) (even? x))
    ;; If we didn't have the check in mismatched? for not removing anything
    ;; in keep-symbolics, this check would fail, because we'd be comparing
    ;; '() with '(), and so it wouldn't matter that the values of x don't
    ;; match up, and we'd get "true" as a result from the efficient impl
    (check-subsumed false #f (list x y) (even? x) (list x y) (odd? x))

    (check-subsumed false #f x #t 0 #t)
    ;; "false precondition"
    (check-subsumed true #f x #f 0 #t)
    ;; this shows that we can't ignore the conditions, even when the two conditions are equal to each other
    ;; (I thought that we might be able to set the keep-symbolics to
    ;; the empty set when the conditions are equal, but turns out that this
    ;; is not okay)
    (check-subsumed false #f (list x 0) (@equal? x y) (list x y) (@equal? x y)))

  (test-case "subsumed?: conditions not overlapping with fields"
    (define-symbolic* x y integer?)
    (check-subsumed false #f (list y) (odd? x) (list y) (and (odd? x) (even? x)))
    (check-subsumed true #f (list y) (even? x) (list y) (even? x))
    (check-subsumed true #f (list y) (even? x) (list y) (odd? x))
    (check-subsumed true #f (list y) (even? x) (list y) #t))

  (test-case "subsumed?: nested structs"
    (struct system-state (ckt-state sim-state) #:transparent)
    (struct sim-state (spec-state aux-state) #:transparent)
    (struct aux-state (circuit extra-stuff) #:transparent)
    (struct ckt (a b c) #:transparent)

    (define-symbolic* secret (bitvector 8))
    (define-symbolic* pc1 pc2 (bitvector 64))
    (define-symbolic* mem1 mem2 (bitvector 32))
    (define-symbolic* spec integer?)

    (define R (equal? (bitvector->natural secret) spec))

    (define-symbolic* fresh integer?)

    (define s1
      (system-state
       (ckt secret pc1 mem1)
       (sim-state
        spec
        (aux-state
         (ckt #| secret unknown |# (bv 0 32) pc2 mem2)
         (list 1 2 fresh 4)))))

    (define s2
      (system-state
       (ckt secret (bvadd pc1 (bv 3 64)) mem1)
       (sim-state
        spec
        (aux-state
         (ckt #| secret unknown |# (bv 0 32) (bvadd pc2 (bv 4 64)) mem2)
         (list 1 2 3 4)))))

    (check-subsumed true #f s2 R s1 R)
    (check-subsumed false #f s1 R s2 R) ; because s1 has fresh
    ;; we're not actually relying on R
    (check-subsumed true #f s2 #t s1 #t)
    (check-subsumed false #f s1 #t s2 #t)
    ;; but if we have R in only the super case, it doesn't work
    (check-subsumed false #f s2 #t s1 R)

    ;; can we make use of R?

    ;; we could have used s1 above, but the secret appears in multiple
    ;; places, and in one, it's equal, so it gets thrown out and added to the
    ;; forbidden symbolics list; handlign this case is tricky, so we don't
    ;; bother. Instead, we instantiate another variable and enforce equality between them.

    (define-symbolic* secret* (bitvector 8))
    (define R* (and R (equal? secret secret*)))

    (define s3
      (system-state
       (ckt secret* pc1 mem1)
       (sim-state
        spec
        (aux-state
         (ckt (bv 0 32) pc2 mem2)
         (list 1 2 fresh 4)))))

    (define s4
      (system-state
       (ckt secret* (bvadd pc1 (bv 3 64)) mem1)
       (sim-state
        (bitvector->natural secret) ; <---------- need to use R here
        (aux-state
         (ckt (bv 0 32) (bvadd pc2 (bv 4 64)) mem2)
         (list 1 2 3 4)))))

    (check-subsumed true #f s4 R* s3 R*)
    (check-subsumed true #f s4 #t s3 #t)

    ;; path conditions / concretization

    (define s5
      (system-state
       (ckt secret* pc1 mem1)
       (sim-state
        spec
        (aux-state
         (ckt (bv 0 32) pc2 mem2)
         (list 1 2 3 4)))))

    ;; path conditions / concretization
    (define s6
      (system-state
       (ckt (bv 0 8) (bvadd pc1 (bv 3 64)) mem1)
       (sim-state
        spec
        (aux-state
         (ckt (bv 0 32) (bvadd pc2 (bv 4 64)) mem2)
         (list 1 2 3 4)))))
    ;; case split, secret* = (bv 0 8)
    (define p (and R* (equal? secret* (bv 0 8))))

    ;; spec has to equal secret in s5, but spec can be different from secret in s6
    (check-subsumed false #f s6 R* s5 R*)
    ;; but if we have p in s6, that's enough
    (check-subsumed true #f s6 p s5 R*)
    ;; s5 is not subsumed by s6 because of the secret* in s5 that becomes 0 in s6
    (check-subsumed false #f s5 R* s6 R*)
    ;; p is enough to show that s5 is subsumed by s6
    (check-subsumed true #f s5 p s6 R*))

  ;; subsumption with existing vc (pc)
  ;; does it interfere with the forall / exists?
  ;;
  ;; not supported anymore; vc should be true
  #;(test-case "subsumed?: interaction with (vc)"
    (define-symbolic* x integer?)
    #;(check-subsumed false #f x #t 0 #t)
    (define p (equal? x 0))
    #;(check-subsumed true #f x p 0 p)
    ;; should be effectively the same thing as above
    (check-pred
     normal?
     (with-vc
       (begin
         (assume p)
         (check-subsumed true #f x #t 0 #t))))

    #;(check-subsumed true #f 0 #t x #t)
    (define p2 (odd? x))
    #;(check-subsumed false #f 0 p2 x p2)
    ;; should be effectively the same thing as above
    (check-pred
     normal?
     (with-vc
       (begin
         (assume p2)
         (check-subsumed false #f 0 #t x #t)))))

  (test-case "subsumed?: case-split-merge"
    ;; consider a circuit writing to a memory based on whether x = 0 or x = 1
    ;; say it's a 8-bit bitvector, but we have a precondition that x < 2
    ;; we case-split on x, and in the case that x = 0, we end up with:
    ;;   mem[0] = a
    ;;   mem[1] = 0
    ;;   mem[2] = 0
    ;; and in case where x = 1, we end up with
    ;;   mem[0] = 0
    ;;   mem[1] = a
    ;;   mem[2] = 1
    ;; suppose we don't care about mem[2], so we can overapproximate it with a fresh symbolic
    ;; we should be able to collapse the two states back into x < 2, and:
    ;;   mem[0] = (ite (= x 0) a 0)
    ;;   mem[1] = (ite (= x 1) a 0)
    ;;   mem[2] = <fresh symbolic>
    ;; let's make sure we can prove this using subsumes: that the final state
    ;; subsumes both case splits
    (define-symbolic* a x fresh (bitvector 8))

    (define pre (bvult x (bv 2 8)))

    (define pc0 (bveq x (bv 0 8)))
    (define st0 (vector a (bv 0 8) (bv 0 8)))

    (define pc1 (bveq x (bv 1 8)))
    (define st1 (vector (bv 0 8) a (bv 1 8)))

    (define joined
      (vector (if (bveq x (bv 0 8)) a (bv 0 8))
              (if (bveq x (bv 1 8)) a (bv 0 8))
              fresh))

    ;; fresh must be a fresh (=> free) symbolic variable, otherwise this isn't true
    (check-subsumed false (seteq) st0 pc0 joined pre)
    (check-subsumed false (seteq) st1 pc1 joined pre)
    ;; once fresh is free, we can join; this is the main result described above
    (check-subsumed true (seteq fresh) st0 pc0 joined pre)
    (check-subsumed true (seteq fresh) st1 pc1 joined pre)
    ;; some extra tests; we can add "useless" stuff in joined as long as we have the right path condition
    (check-subsumed true (seteq fresh) st0 pc0 joined pc0)
    (check-subsumed true (seteq fresh) st1 pc1 joined pc1)
    ;; but if we have the wrong path condition, it's no longer true
    (check-subsumed false (seteq fresh) st0 pc0 joined pc1)
    (check-subsumed false (seteq fresh) st1 pc1 joined pc0)))
