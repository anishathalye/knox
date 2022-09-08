#lang racket/base

(require (for-syntax racket/base syntax/parse racket/syntax))

(require
 (prefix-in @ (combine-in
               rosette/safe
               (only-in rosette/base/core/term term-id)
               (only-in rosette/base/core/bitvector bv-value bv-type [bv? bv-constant?])
               (only-in rosette/base/core/polymorphic =? ite ite* [⊢ guard])
               (only-in rosette/base/core/type typed? get-type type-name type-construct type-deconstruct)))
 (only-in "convenience.rkt" guid fresh-symbolic symbolic-from-id)
 racket/match racket/set)

(provide make-struct-register register-struct! serialize deserialize)

(define (make-struct-register) (make-hasheq))

(define (register-struct! struct-register struct-type [name-override #f])
  (define name (or name-override (@type-name struct-type)))
  (hash-set! struct-register struct-type name))

(define op->description
  (hash
   ;; polymorphic
   @=? '=?
   @ite 'ite
   @ite* 'ite*
   @guard 'guard
   ;; boolean
   @! '!
   @&& '&&
   @|| '||
   @=> '=>
   @<=> '<=>
   @exists 'exists
   @forall 'forall
   @distinct? 'distinct?
   ;; real
   @= '=
   @<= '<=
   @>= '>=
   @< '<
   @> '>
   @+ '+
   @* '*
   @- '-
   @abs 'abs
   @int? 'int?
   @quotient 'quotient
   @remainder 'remainder
   @modulo 'modulo
   @/ '/
   @integer->real 'integer->real
   @real->integer 'real->integer
   ;; bitvector
   @bveq 'bveq
   @bvslt 'bvslt
   @bvsgt 'bvsgt
   @bvsle 'bvsle
   @bvsge 'bvsge
   @bvult 'bvult
   @bvugt 'bvugt
   @bvule 'bvule
   @bvuge 'bvuge
   @bvnot 'bvnot
   @bvand 'bvand
   @bvor 'bvor
   @bvxor 'bvxor
   @bvshl 'bvshl
   @bvlshr 'bvlshr
   @bvashr 'bvashr
   @bvneg 'bvneg
   @bvadd 'bvadd
   @bvsub 'bvsub
   @bvmul 'bvmul
   @bvsdiv 'bvsdiv
   @bvudiv 'bvudiv
   @bvsrem 'bvsrem
   @bvurem 'bvurem
   @bvsmod 'bvsmod
   @concat 'concat
   @extract 'extract
   @sign-extend 'sign-extend
   @zero-extend 'zero-extend
   @integer->bitvector 'integer->bitvector
   @bitvector->integer 'bitvector->integer
   @bitvector->natural 'bitvector->natural))

(define (any->datum s)
  (if (identifier? s) (syntax-e s) s))

;; setting #:hasheq results in faster operation but produces a larger
;; serialized object (and will make the deserialized version consume more
;; memory)
;;
;; only works on cycle-free objects
(define (serialize val [struct-table (make-struct-register)] #:hasheq [use-hasheq #f])
  (define obj-table (make-hasheqv)) ; num -> repr
  ;; the following could also be a hasheq, which would result in faster lookups, but no deduplication
  (define obj-numbering (if use-hasheq (make-hasheq) (make-hash))) ; object -> num
  (define next-obj-num 0)
  (define (alloc-obj-num! repr)
    (define n next-obj-num)
    (set! next-obj-num (add1 n))
    (hash-set! obj-table n repr)
    n)

  ;; we need to make sure that all the terms are allocated object
  ;; numbers in an order that corresponds with their term-id
  ;;
  ;; this is a bit tricky to do; a lazy way to do this is to traverse the entire
  ;; object twice, first identifying all the constants and terms (because
  ;; terms can only refer to constants and terms), then allocating all of them in term-id order,
  ;; and then doing a final pass for allocating the rest of the object
  ;;
  ;; this might not be the most efficient solution, but it works; if this becomes a bottleneck,
  ;; can work on performance-optimizing it
  (define constants (mutable-set)) ; all constants seen so far
  (define terms (make-hasheqv)) ; id -> term
  ;; avoid looking at the same objects more than once, even here
  (define seen (if use-hasheq (mutable-seteq) (mutable-set)))
  (let rec ([val val])
    (unless (set-member? seen val)
      (cond
        [(set-member? constants val) (void)]
        [(and (@term? val) (hash-has-key? terms (@term-id val))) (void)]
        [else
         (match val
           ;; order matters to some degree (e.g. typed? recognizes bitvector literals), but we have
           ;; some flexibility here, so we can order to increase speed
           [(or (? boolean?) (? integer?) (? real?) (? string?) (? symbol?) (? @bv-constant?))
            (set-add! constants val)]
           [(@union contents) (rec contents)]
           [(@constant id type)
            (hash-set! terms (@term-id val) val)]
           [(@expression op vs ...)
            (hash-set! terms (@term-id val) val)
            (for ([v vs]) (rec v))]
           [(vector vs ...) (for ([v vs]) (rec v))]
           [(? list?) (for ([v val]) (rec v))]
           [(cons x y) (rec x) (rec y)]
           [(box v) (rec v)]
           [(@bitvector n) (void)] ; bitvector _type_
           [(and (? @typed?) (app @get-type type))
            (for ([v (@type-deconstruct type val)]) (rec v))]
           [_ (error 'serialize "unrecognized type")])])
      (set-add! seen val)))

  (define (process-object val)
    (hash-ref!
     obj-numbering
     val
     (lambda ()
       ;; newly seen object
       (alloc-obj-num!
        (match val
          ;; order matters to some degree (e.g. typed? recognizes bitvector literals), but we have
          ;; some flexibility here, so we can order to increase speed
          [(or (? boolean?) (? integer?) (? real?) (? string?) (? symbol?)) `(k ,val)]
          [(? @bv-constant?) `(k ,(@bv-value val) ,(@bitvector-size (@bv-type val)))]
          [(@union contents) `(u ,(process-object contents))]
          [(@constant id type)
           (define-values (name idnum)
             (match id
               [(list name (guid idnum)) (values (any->datum name) idnum)]
               [(list name _) (values (any->datum name) #f)]
               [name (values (any->datum name) #f)]))
           (match type
             ;; ordering these by likelihood for our examples
             [(@bitvector size) `(s ,name ,idnum ,size)]
             [(== @boolean?) `(s ,name ,idnum b)]
             [(== @integer?) `(s ,name ,idnum i)]
             [(== @real?) `(s ,name ,idnum r)]
             [_ (error 'serialize "unreachable: constant must be boolean, integer, real, or bitvector")])]
          [(@expression op vs ...) `(e ,(hash-ref op->description op) ,@(for/list ([v vs]) (process-object v)))]
          [(vector vs ...) `(v ,@(for/list ([v vs]) (process-object v)))]
          [(? list?) `(l ,@(for/list ([v val]) (process-object v)))]
          [(cons x y) `(c ,(process-object x) ,(process-object y))]
          [(box v) `(b ,(process-object v))]
          [(@bitvector n) `(B ,n)] ; bitvector _type_
          [(and (? @typed?) (app @get-type type))
           (cond
             [(hash-has-key? struct-table type)
              `(r ,(hash-ref struct-table type) ,@(for/list ([v (@type-deconstruct type val)]) (process-object v)))]
             [else (error 'serialize "unsupported type ~a" type)])]
          [_ (error 'serialize "unrecognized type")])))))

  ;; first, process constants
  (for ([k (in-set constants)])
    (process-object k))
  ;; then, process terms, in term order
  (for ([id (sort (hash-keys terms) <)])
    (process-object (hash-ref terms id)))
  ;; now, traverse the entire object
  (process-object val)

  ;; the object we want is always the last allocated object, so we don't need to explicitly return its number
  (for/list ([i (in-range next-obj-num)]) (hash-ref obj-table i)))

(define (invert-hash h)
  (for/hash ([(k v) (in-hash h)])
    (values v k)))

(define description->op (invert-hash op->description))

(define (deserialize repr [struct-table (make-struct-register)])
  (define inverse-struct-table (invert-hash struct-table))
  ;; we can proceed left to right in the representation, because
  ;; objects never reference "later" objects
  (define objects (make-hasheqv)) ; num -> object
  (define (ids->objects ids) (for/list ([id ids]) (hash-ref objects id)))
  (for ([rep (in-list repr)]
        [i (in-naturals)])
    (define obj
      (match rep
        [`(k ,value ,size) (@bv value size)]
        [`(k ,lit) lit]
        [`(u ,id) (apply @union (hash-ref objects id))]
        [`(s ,name ,idnum ,t)
         (define type
           (match t
             ['b @boolean?]
             ['i @integer?]
             ['r @real?]
             [size (@bitvector size)]))
         (if idnum
             ;; we want to make sure the type matches if there's anything already in the term cache
             ;; (this should never fail unless we're doing something wrong)
             ;;
             ;; there's no direct way to access the term cache, and we don't want to do (terms) to get a big list
             ;; instead, we just create the new constant, and make sure its type is correct
             (let ([var (symbolic-from-id name idnum type)])
               (when (not (equal? (@type-of var) type))
                 ;; instead of erroring, we could create a fresh variable with the right type, but this is probably
                 ;; a bug, and it's better to catch early
                 (error 'deserialize "guid type mismatch"))
               var)
             (fresh-symbolic name type))]
        [`(e ,op ,ids ...) (apply @expression (hash-ref description->op op) (ids->objects ids))]
        [`(v ,ids ...) (vector->immutable-vector (list->vector (ids->objects ids)))]
        [`(l ,ids ...) (ids->objects ids)]
        [`(c ,x ,y) (cons (hash-ref objects x) (hash-ref objects y))]
        [`(b ,id) (hash-ref objects id)]
        [`(B ,n) (@bitvector n)]
        [`(r ,name ,ids ...) (@type-construct (hash-ref inverse-struct-table name (lambda () (error 'deserialize "unknown type ~a" name))) (ids->objects ids))]))
    (hash-set! objects i obj))
  (hash-ref objects (sub1 (length repr))))
