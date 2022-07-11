#lang racket/base

(require
 racket/generic racket/contract racket/function racket/match racket/format racket/string racket/bool
 (for-syntax racket/base syntax/parse racket/syntax)
 (prefix-in @ rosette/safe))

(provide
 gen:addressable addressable? addressable/c
 (contract-out
  [fields (-> addressable? (listof symbol?))]
  [get-field (-> addressable? symbol? any)]
  [map-fields (-> addressable? (-> symbol? any/c any) addressable?)]
  [update-fields (-> addressable? (listof (cons/c symbol? any/c)) addressable?)]
  [update-field (-> addressable? symbol? any/c addressable?)]
  [show-diff (-> addressable? addressable? string?)])
 for/struct
 addressable-struct
 assoc-addressable
 field-filter/c
 (contract-out
  [filter-fields (-> field-filter/c (listof symbol?) (listof symbol?))]
  [field-matches? (-> field-filter/c symbol? boolean?)]
  [field-filter/not (-> field-filter/c field-filter/c)]
  [field-filter/or (->* () #:rest (listof field-filter/c) field-filter/c)]))

;; just a tag
(define-generics yosys-module)

(define-generics addressable
  [fields addressable]
  [get-field addressable field]
  [map-fields addressable fn]
  [update-fields addressable assoc]
  #:fallbacks
  [(define/generic gen-map-fields map-fields)
   (define (update-fields x assoc)
     (define h (make-immutable-hasheq assoc))
     (gen-map-fields x (lambda (name old-value) (hash-ref h name (lambda () old-value)))))])

(define-syntax for/struct
  (syntax-parser
    [(_ [v:id s] body ...)
     #'(for/struct [(_ v) s] body ...)]
    [(_ [(k:id v:id) s] body ...)
     #'(map-fields s (lambda (k v) body ...))]))

(define (update-field struct-value field-name new-value)
  (update-fields struct-value (@list (@cons field-name new-value))))

(define (show-diff self other)
  (define out-string (open-output-string))
  (parameterize ([current-output-port out-string])
    (printf "{~n")
    (for ([f (fields self)])
      (when (not (equal? (get-field self f) (get-field other f)))
        (define field-name (symbol->string f))
        (cond
          ;; recurse when applicable
          [(addressable? (get-field self f))
           (define rec-diff (show-diff (get-field self f) (get-field other f)))
           ;; fix indentation; XXX inefficient implementation
           (define lines (string-split rec-diff "\n"))
           (for ([i (in-naturals)]
                 (line (in-list lines)))
             (cond
               [(zero? i) (printf "  ~a: ~a~n" f line)]
               [(< i (sub1 (length lines))) (printf "    ~a~n" line)]
               [else (printf "  ~a // ~a~n" line f)]))]
          [(and (vector? (get-field self f))
                (vector? (get-field other f))
                (equal? (vector-length (get-field self f)) (vector-length (get-field other f))))
           (printf "  ~a:~n" field-name)
           (for ([i (in-range (vector-length (get-field self f)))])
             (define s-i (vector-ref (get-field self f) i))
             (define o-i (vector-ref (get-field other f) i))
             (when (not (equal? s-i o-i))
               (printf "    ~a: - ~v~n" i s-i)
               (printf "    ~a  + ~v~n" (~a "" #:width (string-length (~a i))) o-i)))]
          [else
           ;; diff boolean or bit vector
           (printf "  ~a: - ~v~n" field-name (get-field self f))
           (printf "  ~a  + ~v~n" (~a "" #:width (string-length field-name)) (get-field other f))])))
    (printf "}"))
  (get-output-string out-string))

(define-syntax (addressable-struct stx)
  (syntax-parse stx
    [(_ name:id (field-name:id ...) struct-option ...)
     #:with (getter ...) (for/list ([f (syntax->list #'(field-name ...))])
                           (format-id #'name "~a-~a" #'name f))
     #'(@struct name (field-name ...) struct-option ...
                #:transparent
                #:methods gen:addressable
                [(define (fields _)
                   '(field-name ...))
                 (define (get-field x f)
                   (define v (@case f [(field-name) (getter x)] ...))
                   (@if (@void? v)
                        (error 'get-field "no such field: ~a" f)
                        v))
                 (define (map-fields x f)
                   (name (f 'field-name (getter x)) ...))])]))

(struct assoc-addressable (lst)
  #:transparent
  #:methods gen:addressable
  [(define (fields this)
     (map car (assoc-addressable-lst this)))
   (define (get-field this f)
     (let loop ([lst (assoc-addressable-lst this)])
       (if (null? lst)
           (error 'get-field "no such field: ~a" f)
           (if (equal? (caar lst) f)
               (cdar lst)
               (loop (cdr lst))))))
   (define (map-fields this f)
     (assoc-addressable
      (map (lambda (pair) (cons (car pair) (f (car pair) (cdr pair)))) (assoc-addressable-lst this))))])

(define field-filter/c
   (or/c boolean? symbol? string? regexp? (-> symbol? any)))

(define (field-filter->function v)
  (cond
    [(boolean? v) (lambda (s) v)]
    [(symbol? v) (lambda (s) (symbol=? s v))]
    [(string? v) (lambda (s) (string-contains? (symbol->string s) v))]
    [(regexp? v) (lambda (s) (regexp-match? v (symbol->string s)))]
    [else v]))

(define (filter-fields field-filter field-names)
  (filter (field-filter->function field-filter) field-names))

(define (field-matches? field-filter field-name)
  ((field-filter->function field-filter) field-name))

(define (field-filter/not filter)
  (let ([fn (field-filter->function filter)])
    (lambda (s) (not (fn s)))))

(define (field-filter/or . filters)
  (let ([fns (map field-filter->function filters)])
    (lambda (s)
      (for/or ([fn (in-list fns)])
        (fn s)))))
