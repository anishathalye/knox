#lang rosette/safe

(require
 (for-syntax syntax/parse racket/syntax)
 syntax/parse/define
 ; we need to be careful of what we import for runtime, because
 ; whatever we use needs to be compatible with Rosette
 "memoize.rkt" "parameters.rkt" "generic.rkt" "meta.rkt"
 rosutil
 (prefix-in ! racket/base))

(provide
 declare-datatype define-fun
 yosys-smt2-stdt yosys-smt2-module yosys-smt2-topmod
 yosys-smt2-clock yosys-smt2-input yosys-smt2-output
 yosys-smt2-register yosys-smt2-memory
 (for-syntax yosys-top))

(begin-for-syntax
  (define-splicing-syntax-class yosys-type
    #:attributes (show type-descriptor ctor zero-ctor)
    (pattern (~datum Bool)
             #:with show #'show-boolean
             #:with type-descriptor #''boolean
             #:with ctor #'(lambda (name) (fresh-symbolic name boolean?))
             #:with zero-ctor #'#f)
    (pattern ((~datum _) (~datum BitVec) num:nat)
             #:with show #'show-bitvector
             #:with type-descriptor #''(bitvector num)
             #:with ctor #'(lambda (name) (fresh-symbolic name (bitvector num)))
             #:with zero-ctor #'(bv 0 num))
    (pattern ((~datum Array) ((~datum _) (~datum BitVec) depth:nat) ((~datum _) (~datum BitVec) width:nat))
             #:with show #'show-array
             #:with type-descriptor #''(array depth width)
             #:with ctor #'(lambda (name)
                             (if (array-representation-vector)
                                 ; vector representation
                                 (vector->immutable-vector
                                  (!build-vector (expt 2 depth)
                                                 (lambda (i)
                                                   (fresh-symbolic (format "~a[~a]" name i) (bitvector width)))))
                                 ; UF representation
                                 (fresh-symbolic name (~> (bitvector depth) (bitvector width)))))
             #:with zero-ctor #'(if (array-representation-vector)
                                    ; vector representation
                                    (vector->immutable-vector (!build-vector (expt 2 depth) (lambda (_) (bv 0 width))))
                                    ; UF representation
                                    (lambda (addr) (bv 0 width)))))

  (define-splicing-syntax-class yosys-member
    #:attributes (external-name name show type-descriptor ctor zero-ctor)
    (pattern (~seq (name:id type:yosys-type) external-name:id)
             #:with show #'type.show
             #:with type-descriptor #'type.type-descriptor
             #:with ctor #'(type.ctor 'external-name)
             #:with zero-ctor #'type.zero-ctor))

  (define-syntax-class yosys-initial-state
    #:attributes (name ctor zero-ctor)
    (pattern (name:id (~datum Bool))
             #:with ctor #'(fresh-symbolic 'name boolean?)
             #:with zero-ctor #'#f)))

(define-syntax (declare-datatype stx)
  (syntax-parse stx
    [(_ datatype-name:id ((_
                           init:yosys-initial-state
                           member:yosys-member ...)))
     #:with make-name (format-id stx "make-~a" #'datatype-name)
     #:with update-name (format-id stx "update-~a" #'datatype-name)
     #:with internal-copy-name (format-id stx "internal-copy-~a" #'datatype-name)
     #:with new-symbolic-name (format-id stx "new-symbolic-~a" #'datatype-name)
     #:with new-zeroed-name (format-id stx "new-zeroed-~a" #'datatype-name)
     #:with init-getter (format-id stx "~a-~a" #'datatype-name #'init.name)
     #:with (getter ...) (for/list ([external-name (syntax->list #'(member.external-name ...))])
                           (format-id stx "~a-~a" #'datatype-name external-name))
     #:with /... (quote-syntax ...)
     #'(begin
         ; struct declaration
         (addressable-struct
          datatype-name
          (init.name member.external-name ...)
          #:methods gen:custom-write
          [(define (write-proc x port mode) (show x port mode))]
          #:methods gen:yosys-module [])
         (define (show x port mode)
           (let ([print-filter (print-filter)])
             (cond
               [(boolean? mode)
                ; write or display
                (fprintf port "#(struct:~a" 'datatype-name)
                (when (field-matches? print-filter 'init.name)
                  (fprintf port " ")
                  (show-boolean (init-getter x) port mode))
                (when (field-matches? print-filter 'member.external-name)
                  (fprintf port " ")
                  (member.show (getter x) port mode)) ...
                (fprintf port ")")]
               [else
                ; print something more human-readable
                (fprintf port "~a {~n" 'datatype-name)
                (when (field-matches? print-filter 'member.external-name)
                  (fprintf port "  ~a:" 'member.external-name)
                  (member.show (getter x) port mode)
                  (fprintf port "\n")) ...
                (fprintf port "}")])))
         (provide (struct-out datatype-name))

         ; like struct-copy, but uses the internal names instead of external names
         ; for transition function
         (begin-for-syntax
           (define name-assoc
             (make-hash '((member.name . member.external-name) ...))))
         (define-syntax (internal-copy-name stx)
           (syntax-parse stx
             [(_ state [internal-name value] /...)
              #`(!struct-copy
                 datatype-name
                 state
                 #,@(for/list ([i (syntax->list #'(internal-name /...))]
                               [v (syntax->list #'(value /...))])
                      #`(#,(datum->syntax #'datatype-name (hash-ref name-assoc (syntax-e i))) #,v)))
              ]))

         ; getters
         (define init.name init-getter)
         (provide init-getter)
         (define member.name getter) ... ; for internal use only, not exported
         (define member.external-name getter) ...
         (provide getter) ...

         ; constructors
         (define (new-symbolic-name)
           (datatype-name init.ctor member.ctor ...))
         (provide new-symbolic-name)
         (define (new-zeroed-name)
           (datatype-name init.zero-ctor member.zero-ctor ...))
         (provide new-zeroed-name)
         (define-syntax update-name
           (syntax-parser
             [(_ struct-expr:expr [field:id value:expr] /...)
              #'(update-fields struct-expr (list (cons 'field value) /...))]))
         (provide update-name)
         (define-syntax make-name
           (syntax-parser
             [(_ [field:id value:expr] /...)
              #'(update-name (new-zeroed-name) [field value] /...)]))
         (provide make-name))]))

(define-syntax (define-fun stx)
  (syntax-parse stx
    ; regular case
    [(_ name:id ((input:id input-type)) return-type body:expr)
     #'(begin
         (define/memoize1 (name input)
           body)
         (provide name))]
    ; transition function: treated specially
    ; case 1: when module is purely combinational
    [(_ name:id ((state:id type:id) ((~datum next_state) next-type:id)) (~datum Bool)
        (~datum true))
     #:with internal-copy-name (format-id stx "internal-copy-~a" #'type)
     #:with step (format-id stx "step")
     #'(begin
         (define (name state)
           (new-memoization-context
            (internal-copy-name state)))
         (define (step state) (name state))
         (provide name step))]
    ; case 2: when state has a single field
    [(_ name:id ((state:id type:id) ((~datum next_state) next-type:id)) (~datum Bool)
        ((~datum =) e (field:id (~datum next_state))))
     #:with internal-copy-name (format-id stx "internal-copy-~a" #'type)
     #:with step (format-id stx "step")
     #'(begin
         (define (name state)
           (new-memoization-context
            (internal-copy-name state [field e])))
         (define (step state) (name state))
         (provide name step))]
    ; case 3: when state has multiple fields
    [(_ name:id ((state:id type:id) ((~datum next_state) next-type:id)) (~datum Bool)
        ((~datum and) ((~datum =) e (field:id (~datum next_state))) ...))
     #:with internal-copy-name (format-id stx "internal-copy-~a" #'type)
     #:with step (format-id stx "step")
     #'(begin
         (define (name state)
           (new-memoization-context
            (internal-copy-name state [field e] ...)))
         (define (step state) (name state))
         (provide name step))]))

; this appears at the top of the extraction, so we can put global
; top-level definitions here
(define-simple-macro (yosys-smt2-stdt)
  (begin))

(define-simple-macro (yosys-smt2-module name:id)
  (begin))

(define-simple-macro (yosys-smt2-topmod name:id)
  (begin))

(define-simple-macro (yosys-smt2-clock name:id 'edge:id)
  (begin))

(define-simple-macro (yosys-smt2-input name:id width:nat)
  (begin))

(define-simple-macro (yosys-smt2-output name:id width:nat)
  (begin))

(define-simple-macro (yosys-smt2-register name:id width:nat)
  (begin))

(define-simple-macro (yosys-smt2-memory name:id bits:nat width:nat read-ports:nat write-ports:nat 'sync:id)
  (begin))

(define (show-recur x port mode)
  (case mode
    [(#t) (write x port)]
    [(#f) (display x port)]
    [else (fprintf port " ") (print x port mode)]))

(define (show-boolean x port mode)
  (show-recur x port mode))

(define (show-bitvector x port mode)
  (show-recur x port mode))

(define (show-array x port mode)
  (case mode
    [(#t) (write x port)]
    [(#f) (display x port)]
    [else
     (if (array-representation-vector)
         (!for ([e x]
                [i (!in-naturals)])
               (fprintf port "~n    ~a:" i)
               (show-bitvector e port mode))
         (begin
           (fprintf port " ")
           (print x port mode)))]))

(define (make-assoc lst)
  (cond
    [(empty? lst) '()]
    [(empty? (cdr lst)) (!error 'make-assoc "odd number of elements")]
    [else (cons (cons (car lst) (cadr lst)) (make-assoc (cddr lst)))]))

(define (assoc-default v lst default)
  (define r (assoc v lst))
  (if (not r)
      default
      (cdr r)))

(begin-for-syntax
  (define (take-upto p l)
    (let rec ([l l]
              [acc '()])
      (if (empty? l)
          (reverse acc)
          (let ([h (first l)])
            (if (p h)
                (reverse (cons h acc))
                (rec (rest l) (cons h acc)))))))

  (define (filter-tagged tag-begin tag-end stx)
    (define ((tag-match? tag) form)
      (define d (syntax-e form))
      (and (pair? d) (identifier? (first d)) (free-identifier=? (first d) tag)))
    (let rec ([forms (syntax->list stx)]
              [acc '()])
      (if (empty? forms)
          (reverse acc)
          (rec (rest forms)
               (if ((tag-match? tag-begin) (first forms))
                   (cons (if tag-end (take-upto (tag-match? tag-end) forms) (first forms)) acc)
                   acc)))))

  (define (build-getters stxs)
    (for/list ([el stxs])
      (let ([name (second (syntax->list (first el)))]
            [getter (second (syntax->list (last el)))])
        #`(cons '#,name #,getter))))

  (define (gen-struct ctxt name fields-stxs)
    (define fields (map syntax->list fields-stxs))
    (define struct-name (format-id ctxt name))
    (define new-symbolic-name (format-id ctxt "new-symbolic-~a" name))
    (define getters-name (format-id ctxt "~a-getters" name))
    (define name* (format-id ctxt "~a*" name))
    #`(begin
        (addressable-struct
         #,struct-name #,(for/list ([f fields]) (second f))
         #:methods gen:custom-write
         [(define (write-proc x port mode)
            ;; similar to show for yosys module itself, but no print filter
            (cond
              [(boolean? mode)
               ; write or display
               (fprintf port "#(struct:~a" '#,struct-name)
               #,@(for/list ([f fields])
                   #`(show-recur (get-field x '#,(second f)) port mode))
               (fprintf port ")")]
              [else
               ; print something more human-readable
               (fprintf port "~a {~n" '#,struct-name)
               #,@(for/list ([f fields])
                   #`(begin
                       (fprintf port "  ~a:" '#,(second f) )
                       (show-recur (get-field x '#,(second f)) port mode)
                       (fprintf port "\n")))
               (fprintf port "}")]))])
        ;; constructor with named fields
        (define (#,name* . args)
          (define args* (make-assoc args))
          (#,struct-name #,@(for/list ([f fields]) #`(assoc-default '#,(second f) args* #,(let ([w (syntax-e (third f))])
                                                                                            (if (equal? w 1)
                                                                                                #'#f
                                                                                                #`(bv 0 #,w)))))))
        (define #,getters-name
          (list
           #,@(for/list ([f fields])
                (let ([getter-name (format-id ctxt "~a-~a" struct-name (second f))])
                  #`(cons '#,getter-name #,getter-name)))))
        (define (#,new-symbolic-name)
          (#,struct-name #,@(for/list ([f fields])
                              (let* ([name (syntax-e (second f))]
                                     [w (syntax-e (third f))]
                                     [type (if (equal? w 1) #'boolean? #`(bitvector #,w))])
                                #`(fresh-symbolic '#,name #,type)))))
        (provide (struct-out #,struct-name) #,name* #,getters-name #,new-symbolic-name)))

  (define (gen-input-setter ctxt module-name fields)
    (define struct-name (format-id ctxt "~a_s" module-name))
    (define with-input (format-id ctxt "with-input"))
    #`(begin
        (define (#,with-input state input)
          (!struct-copy
           #,struct-name
           state
           #,@(for/list ([inp fields])
                (let* ([name (syntax-e (second (syntax->list inp)))]
                       [getter (format-id ctxt "input-~a" name)])
                  #`(#,name (#,getter input))))))
        (provide #,with-input)))

  (define (yosys-top stx)
    (syntax-parse stx
      [(_ form ...)
       (define module-name (syntax-e (second (syntax->list (first (filter-tagged #'yosys-smt2-module #f stx))))))
       (define (get-name decl-stx) (syntax-e (second (syntax->list decl-stx))))
       (define clock-names (list->set (map get-name (filter-tagged #'yosys-smt2-clock #f stx))))
       (define (filter-clocks stxs)
         (filter (lambda (decl-stx) (not (set-member? clock-names (get-name (first decl-stx))))) stxs))
       (define input-stxs (filter-clocks (filter-tagged #'yosys-smt2-input #'define-fun stx)))
       (define output-stxs (filter-clocks (filter-tagged #'yosys-smt2-output #'define-fun stx)))
       (define register-stxs (filter-tagged #'yosys-smt2-register #'define-fun stx))
       (define memory-stxs (filter-tagged #'yosys-smt2-memory #'define-fun stx))
       #`(form
          ...
          (begin
            (provide inputs outputs registers memories)
            (define inputs (list #,@(build-getters input-stxs)))
            (define outputs (list #,@(build-getters output-stxs)))
            (define registers (list #,@(build-getters register-stxs)))
            (define memories (list #,@(build-getters memory-stxs)))
            #,(gen-struct stx "input" (map first (filter-clocks input-stxs)))
            #,(gen-struct stx "output" (map first (filter-clocks output-stxs)))
            #,(gen-input-setter stx module-name (map first (filter-clocks input-stxs)))
            (define (get-input state)
              (apply #,(format-id stx "input") (map (lambda (o) ((cdr o) state)) inputs)))
            (define (get-output state)
              (apply #,(format-id stx "output") (map (lambda (o) ((cdr o) state)) outputs)))
            (provide get-output)
            ;; packaging up this stuff nicely together
            (define metadata (meta
                              #,(format-id stx "new-symbolic-~a_s" module-name)
                              #,(format-id stx "new-zeroed-~a_s" module-name)
                              #,(format-id stx "~a_i" module-name)
                              #,(format-id stx "step")
                              #,(format-id stx "input")
                              #,(format-id stx "new-symbolic-input")
                              #,(format-id stx "input*")
                              #,(format-id stx "input-getters")
                              #,(format-id stx "with-input")
                              #,(format-id stx "output")
                              #,(format-id stx "new-symbolic-output")
                              #,(format-id stx "output*")
                              #,(format-id stx "output-getters")
                              get-input
                              get-output))
            (provide metadata)))])))
