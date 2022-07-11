#lang rosette/safe

(require "addressable-struct.rkt"
         racket/contract
         (only-in racket/base exact-nonnegative-integer? symbol? string? regexp? procedure-arity-includes? error)
         (only-in racket/list check-duplicates)
         (for-syntax syntax/parse))

(provide
 (contract-out
  [lens? (-> any/c boolean?)]
  [lens-view (-> lens? any/c any)]
  [lens-set (-> lens? any/c any/c any)]
  [lens-transform (-> lens? any/c (-> any/c any/c) any)]
  [lens-compose (->* () #:rest (listof lens?) lens?)]
  [lens-thrush (->* () #:rest (listof lens?) lens?)]
  [lens-join (->* () #:rest (listof lens?) lens?)]
  [car-lens lens?]
  [cdr-lens lens?]
  [unit-lens lens?]
  [identity-lens lens?]
  [list-ref-lens (-> exact-nonnegative-integer? lens?)]
  [vector-ref-lens (-> exact-nonnegative-integer? lens?)]
  [virtual-lens (-> list? lens?)]
  [vector-all-elements-lens lens?]
  [struct-ref-lens (-> symbol? lens?)]
  [struct-filter-lens (-> field-filter/c lens?)]
  [as-lens (-> lens-like/c lens?)]
  [rename lens* lens (->* () #:rest (listof lens-like/c) lens?)])
 (struct-out join)
 (contract-out
  [join* (->* () #:rest (listof any/c) join?)]))

(define-generics lens
  [get lens target]
  [set lens target view]
  [update lens target transformer]
  #:fallbacks
  [(define/generic gen-get get)
   (define/generic gen-set set)
   (define (update lens target transformer)
     (gen-set lens target (transformer (gen-get lens target))))])

(define lens-view get)

(define lens-set set)

(define lens-transform update)

(struct identity-lens-t ()
  #:methods gen:lens
  [(define (get lens target) target)
   (define (set lens target view) view)])

(define identity-lens (identity-lens-t))

(struct unit-lens-t ()
  #:methods gen:lens
  [(define (get lens target) null)
   (define (set lens target view) target)])

(define unit-lens (unit-lens-t))

;; lens1 should not itself be a composition lens
(struct composition-lens (lens2 lens1)
  #:methods gen:lens
  [(define (get lens target)
     (lens-view (composition-lens-lens2 lens) (lens-view (composition-lens-lens1 lens) target)))
   (define (set lens target view)
     (lens-transform (composition-lens-lens1 lens) target (lambda (target*) (lens-set (composition-lens-lens2 lens) target* view))))
   (define (update lens target transformer)
     (lens-transform (composition-lens-lens1 lens) target (lambda (target*) (lens-transform (composition-lens-lens2 lens) target* transformer))))])

;; ensures that the lens1 of the resulting composition is not itself a composition by applying commutativity
(define (lens-compose2 lens2 lens1)
  (cond
    [(composition-lens? lens1)
     ;; push composition
     (let ([lens1-1 (composition-lens-lens1 lens1)]
           [lens1-2 (composition-lens-lens2 lens1)])
       (lens-compose2 (lens-compose2 lens2 lens1-2) lens1-1))]
    [else (composition-lens lens2 lens1)]))

(define (lens-compose . lenses)
  (cond
    [(null? lenses) identity-lens]
    [(null? (cdr lenses)) (car lenses)]
    [else (foldl (lambda (l acc) (lens-compose2 acc l)) (car lenses) (cdr lenses))]))

(define (lens-thrush . lenses)
  (apply lens-compose (reverse lenses)))

(struct join (contents) #:transparent)
(define (join* . vs) (join vs))

;; generic join lens
(struct join-lens (lenses)
  #:methods gen:lens
  [(define (get lens target)
     (join (map (lambda (lens) (lens-view lens target)) (join-lens-lenses lens))))
   (define (set lens target view)
     (let loop ([obj target]
                [lenses (join-lens-lenses lens)]
                [views (join-contents view)])
       (if (null? lenses)
           obj
           (loop
            (lens-set (car lenses) obj (car views))
            (cdr lenses)
            (cdr views)))))])

;; List lenses

(struct car-lens-t ()
  #:methods gen:lens
  [(define (get lens target) (car target))
   (define (set lens target view) (cons view (cdr target)))])

(define car-lens (car-lens-t))

(struct cdr-lens-t ()
  #:methods gen:lens
  [(define (get lens target) (cdr target))
   (define (set lens target view) (cons (car target) view))])

(define cdr-lens (cdr-lens-t))

(define (list-update lst pos upd)
  (cond
    [(zero? pos) (cons (upd (car lst)) (cdr lst))]
    [else (cons (car lst) (list-update (cdr lst) (sub1 pos) upd))]))

(struct list-ref-lens (pos)
  #:methods gen:lens
  [(define (get lens target) (list-ref target (list-ref-lens-pos lens)))
   (define (set lens target view) (list-set target (list-ref-lens-pos lens) view))
   (define (update lens target transformer) (list-update target (list-ref-lens-pos lens) transformer))])

;; Vector lenses

(struct vector-ref-lens (pos)
  #:methods gen:lens
  [(define (get lens target) (vector-ref target (vector-ref-lens-pos lens)))
   (define (set lens target view)
     (define copy (list->vector (vector->list target)))
     (vector-set! copy (vector-ref-lens-pos lens) view)
     (vector->immutable-vector copy))])

(struct vector-all-elements-lens-t ()
  #:methods gen:lens
  [(define (get lens target)
     (join (vector->list target)))
   (define (set lens target view)
     (vector->immutable-vector (list->vector (join-contents view))))])

(define vector-all-elements-lens (vector-all-elements-lens-t))

;; Struct lenses

(struct struct-ref-lens (field-name)
  #:methods gen:lens
  [(define (get lens target) (get-field target (struct-ref-lens-field-name lens)))
   (define (set lens target view)
     (update-field target (struct-ref-lens-field-name lens) view))])

(struct struct-filter-lens (field-filter)
  #:methods gen:lens
  [(define (get lens target)
     (join
      (map (lambda (name) (get-field target name))
           (matching-fields (struct-filter-lens-field-filter lens) target))))
   (define (set lens target view)
     (update-fields
      target
      (map cons (matching-fields (struct-filter-lens-field-filter lens) target) (join-contents view))))])

(define (matching-fields field-filter target)
  (filter (lambda (name) (field-matches? field-filter name)) (fields target)))

;; More efficient joining

;; lenses are all either struct-ref-lens/struct-filter-lens or a composition (with the lens1 being a struct-ref-lens/struct-filter-lens)
(struct struct-ref/filter-join-lens (lenses)
  #:methods gen:lens
  [(define (get lens target)
     ;; we don't need to do anything special here, we just run all the getters
     (join (map (lambda (lens) (lens-view lens target)) (struct-ref/filter-join-lens-lenses lens))))
   (define (set lens target view)
     ;; we want to do this with a single call to update-fields, so we only make a single copy of the underlying struct
     (define updated-fields
       (apply
        append
        (map
         (lambda (lens view)
           ;; this may be a struct-ref-lens, or a composition (where the lens1 is a struct-ref-lens)
           ;;
           ;; we want to figure out the field name and the updated value
           (cond
             ;; easy case: reference to a single field (and no further decomposition)
             [(struct-ref-lens? lens) (list (cons (struct-ref-lens-field-name lens) view))]
             ;; filter lens: references to multiple fields
             [(struct-filter-lens? lens)
              (define matching-fields
                (filter (lambda (name) (field-matches? (struct-filter-lens-field-filter lens) name)) (fields target)))
              (map cons matching-fields (join-contents view))]
             [else
              ;; composition; lens1 _must_ be a struct-ref-lens, it is illegal to compose struct-filter-lens with anything else
              ;; (no lenses operate on joins)
              (define lens1 (composition-lens-lens1 lens))
              (define lens2 (composition-lens-lens2 lens))
              (list (cons (struct-ref-lens-field-name lens1) (lens-set lens2 (lens-view lens1 target) view)))]))
         (struct-ref/filter-join-lens-lenses lens)
         (join-contents view))))
     ;; error checking: if there are duplicate keys in updated-fields,
     ;; the lenses overlap in a bad way
     (define dupe (check-duplicates (map car updated-fields)))
     (when dupe
       (error 'struct-ref/filter-join-lens:set "duplicated field '~a'~n" dupe))
     (update-fields
      target
      updated-fields))])

(struct vector-ref-join-lens (lenses)
  #:methods gen:lens
  [(define (get lens target)
     ;; don't need to do anything special here
     (join (map (lambda (lens) (lens-view lens target)) (vector-ref-join-lens-lenses lens))))
   (define (set lens target view)
     (define copy (list->vector (vector->list target)))
     (for-each
      (lambda (lens view)
        (cond
          ;; easy case
          [(vector-ref-lens? lens) (vector-set! copy (vector-ref-lens-pos lens) view)]
          ;; composition case
          [else
           (define lens1 (composition-lens-lens1 lens))
           (define lens2 (composition-lens-lens2 lens))
           (vector-set! copy (vector-ref-lens-pos lens1) (lens-set lens2 (lens-view lens1 target) view))]))
      (vector-ref-join-lens-lenses lens)
      (join-contents view))
     (vector->immutable-vector copy))])

(struct virtual-lens (names-lenses)
  #:methods gen:lens
  [(define (get lens target)
     (assoc-addressable
      (map (lambda (pair) (cons (car pair) (lens-view (cdr pair) target))) (virtual-lens-names-lenses lens))))
   (define (set lens target view)
     (foldl (lambda (pair acc) (lens-set (cdr pair) acc (get-field view (car pair)))) target (virtual-lens-names-lenses lens)))])

;; works differently based on the types of lenses being joined
;; together; a generic implementation as a fallback, but more optimized
;; implementations for special cases
(define (lens-join . lenses)
  (if (null? lenses) (join-lens '())
      (let* ([lens0 (car lenses)]
             [lens0* (if (composition-lens? lens0) (composition-lens-lens1 lens0) lens0)])
        (cond
          ;; special cases for performance
          [(or (struct-ref-lens? lens0*) (struct-filter-lens? lens0*)) (struct-ref/filter-join-lens lenses)]
          [(vector-ref-lens? lens0*) (vector-ref-join-lens lenses)]
          ;; fallback implementation
          [else (join-lens lenses)]))))

;; Convenience constructors

(define lens-like/c
  (or/c
   lens?
   symbol?
   exact-nonnegative-integer?
   (listof (recursive-contract lens-like/c))
   ;; field filter
   boolean?
   string?
   regexp?
   (procedure-arity-includes/c 1)))

(define (as-lens v)
  (cond
    [(lens? v) v]
    [(symbol? v) (struct-ref-lens v)]
    [(exact-nonnegative-integer? v) (vector-ref-lens v)]
    [(list? v) (apply lens-join (map as-lens v))]
    ;; field filter
    [(or (boolean? v)
         (string? v)
         (regexp? v)
         (procedure-arity-includes? v 1))
     (struct-filter-lens v)]
    [else (error 'as-lens "cannot be coerced to a lens")]))

(define (lens* . args)
  (apply lens-thrush (map as-lens args)))
