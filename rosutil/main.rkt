#lang racket/base

(require syntax/parse/define)

(define-simple-macro (require+provide module-path:str ...)
  (begin
    (require module-path ...)
    (provide (all-from-out module-path) ...)))

(require+provide
 "concretize.rkt"
 "convenience.rkt"
 "dependence.rkt"
 "addressable-struct.rkt"
 "lens.rkt"
 "subsumption.rkt"
 "serialization.rkt"
 "overapproximate.rkt"
 "substitution.rkt")
