#lang racket/base

(require
 "convenience.rkt"
 "concretize.rkt"
 racket/contract racket/set racket/list
 (prefix-in @ rosette/safe))

(provide
 (rename-out [only-depends-on only-depends-on/unchecked])
 (contract-out
  [only-depends-on (->
                    value-of-solvable-type/c
                    (set/c @constant? #:cmp 'eq #:kind 'dont-care)
                    @solution?)]))

; is value fully determined by an assignment of concrete values
; to the given symbolics?
(define (only-depends-on value constants)
  (define value-symbolics (list->seteq (@symbolics value)))
  ; okay to depend on these:
  (define value-allowed-symbolics (set-intersect value-symbolics constants))
  ; not okay to depend on these:
  (define value-rest-symbolics (set-subtract value-symbolics constants))
  (cond
    [(set-empty? value-rest-symbolics)
     ; fast path
     (@unsat)]
    [(set-empty? value-allowed-symbolics)
     ; fast-ish path when we're trying to show that something
     ; is concrete (no dependence on any constants) --
     ; no exists/forall style query required
     (concrete value)]
    [else
     ; need to invoke solver
     ; try to show that value doesn't depend on other symbolics
     (@define-symbolic* fresh (@type-of value))
     (define res
       (@verify
        (@assert
         (@exists (list fresh)
                  (@forall (set->list value-rest-symbolics)
                           (@equal? value fresh))))))
     res]))
