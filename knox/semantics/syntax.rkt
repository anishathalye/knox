#lang rosette/safe

(require
 (only-in racket [string? racket/string?] [symbol? racket/symbol?]))

(provide
 string? symbol?
 tag
 variable?
 literal? literal-value
 lambda? lambda-formals lambda-body
 if? if-condition if-then if-else
 and? and-contents
 or? or-contents
 let? let-bindings let-body
 begin? begin-contents
 app? app-f app-args
 quote? quote-get)

(define (string? v)
  (for/all ([v v])
    (racket/string? v)))

(define (symbol? v)
  (for/all ([v v])
    (racket/symbol? v)))

(define (tag expr)
  (if (not (list? expr))
      #f
      (car expr)))

(define (variable? expr)
  (symbol? expr))

(define (literal? expr)
  (or (boolean? expr) (integer? expr) (string? expr)))

(define (literal-value expr)
  expr)

(define (lambda? expr)
  (equal? (tag expr) 'lambda))

(define (lambda-formals expr)
  (cadr expr))

(define (maybe-wrap-body expr)
  (if (null? (cdr expr))
      ;; body is a single expression, return it
      (car expr)
      ;; body is a sequence, wrap it in sequence
      `(begin ,@expr)))

(define (lambda-body expr)
  (maybe-wrap-body (cddr expr)))

(define (if? expr)
  (equal? (tag expr) 'if))

(define (if-condition expr)
  (cadr expr))

(define (if-then expr)
  (caddr expr))

(define (if-else expr)
  (cadddr expr))

(define (and? expr)
  (equal? (tag expr) 'and))

(define (and-contents expr)
  (cdr expr))

(define (or? expr)
  (equal? (tag expr) 'or))

(define (or-contents expr)
  (cdr expr))

(define (let? expr)
  (equal? (tag expr) 'let))

(define (let-bindings expr)
  (cadr expr))

(define (let-body expr)
  (maybe-wrap-body (cddr expr)))

(define (begin? expr)
  (equal? (tag expr) 'begin))

(define (begin-contents expr)
  (cdr expr))

(define (app? expr)
  (list? expr))

(define (app-f expr)
  (car expr))

(define (app-args expr)
  (cdr expr))

(define (quote? expr)
  (equal? (tag expr) 'quote))

(define (quote-get expr)
  (second expr))
