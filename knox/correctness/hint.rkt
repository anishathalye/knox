#lang racket/base

(require
 racket/bool
 racket/match
 (prefix-in @ (combine-in rosette/safe rosutil/lens))
 (for-syntax racket/base syntax/parse)
 syntax/parse/define)

(provide
 (struct-out hint)
 done
 done?
 evaluate-to-next-hint
 (except-out (struct-out merge) merge)
 (except-out (struct-out fixpoint) fixpoint)
 (except-out (struct-out case-split) case-split)
 (struct-out debug*)
 (except-out (struct-out tactic) tactic)
 (except-out (struct-out get-state) get-state)
 (except-out (struct-out concretize) concretize)
 (except-out (struct-out overapproximate) overapproximate)
 (except-out (struct-out overapproximate-pc) overapproximate-pc)
 (except-out (struct-out replace) replace)
 (except-out (struct-out remember) remember)
 (except-out (struct-out subst) subst)
 (except-out (struct-out clear) clear)
 (rename-out
  [tactic# tactic]
  [get-state# get-state]
  [merge# merge]
  [fixpoint# fixpoint]
  [case-split# case-split]
  [concretize# concretize]
  [overapproximate# overapproximate]
  [overapproximate-pc# overapproximate-pc]
  [replace# replace]
  [remember# remember]
  [subst# subst]
  [clear# clear])
 make-hintdb
 extend-hintdb)

(struct hint ())

(define-syntax make-hintdb
  (syntax-parser
    [(_ [name:id hint:expr] ...)
     #'(make-immutable-hash (list (cons 'name hint) ...))]))

(define (hash-extend base pairs)
  (for/fold ([tbl base])
            ([pair pairs])
    (hash-set tbl (car pair) (cdr pair))))

(define-syntax extend-hintdb
  (syntax-parser
    [(_ base:expr [name:id hint:expr] ...)
     #'(hash-extend base (list (cons 'name hint) ...))]))

(define done false)
(define done? false?)

(define hint-evaluation-prompt-tag (make-continuation-prompt-tag))

(define-simple-macro (wrap (hint-struct args ...))
  (if (continuation-prompt-available? hint-evaluation-prompt-tag)
      (call-with-current-continuation
       (lambda (k)
         (abort-current-continuation hint-evaluation-prompt-tag (lambda () (hint-struct args ... k))))
       hint-evaluation-prompt-tag)
      (hint-struct args ... (lambda _ done))))

(define (evaluate-to-next-hint k arg)
  (define next (call-with-continuation-prompt (lambda () (k arg)) hint-evaluation-prompt-tag))
  (if (hint? next) ; to handle the case where k returns (void), etc.
      next
      done))

(struct tactic hint (k))

(define (tactic-constructor fn)
  (tactic fn))

(define-match-expander tactic#
  (syntax-parser [(_ args ...) #'(tactic args ...)])
  (syntax-parser
    ;; take an ignored value so we can call a tactic and a continuation in the same way,
    ;; by plugging in a value when applicable, and (void) otherwise, which will be
    ;; passed in this case
    [(_ args ...) #'(tactic-constructor (lambda (ignored) args ...))]))

(struct get-state hint (k))

(define (get-state-hint)
  (wrap (get-state)))

(define-match-expander get-state#
  (syntax-parser [(_ args ...) #'(get-state args ...)])
  (syntax-parser
    [(_ args ...) #'(get-state-hint args ...)]
    [_ #'get-state-hint]))

(struct merge hint (key k))

(define (merge-hint [key (lambda (st) #t)])
  (wrap (merge key)))

(define-match-expander merge#
  (syntax-parser [(_ args ...) #'(merge args ...)])
  (syntax-parser
    [(_ args ...) #'(merge-hint args ...)]
    [_ #'merge-hint]))

(struct fixpoint (setup-cycles auto-detect cycle-length step-concretize-lens use-pc piecewise step-overapproximate-lens k))

(define (fixpoint-constructor setup-cycles auto-detect cycle-length [step-concretize-lens #f] [step-overapproximate-lens #f] [k done] #:use-pc [use-pc #f] #:piecewise [piecewise #f])
  (fixpoint setup-cycles auto-detect cycle-length step-concretize-lens use-pc piecewise step-overapproximate-lens k))

(define-match-expander fixpoint#
  (syntax-parser [(_ args ...) #'(fixpoint args ...)])
  (syntax-parser
    [(_ args ...) #'(fixpoint-constructor args ...)]
    [_ #'fixpoint-constructor]))

(struct case-split hint (splits use-equalities k))

(define (case-split-hint splits #:use-equalities [use-equalities #f])
  (wrap (case-split splits use-equalities)))

(define-match-expander case-split#
  (syntax-parser [(_ args ...) #'(case-split args ...)])
  (syntax-parser
    [(_ args ...) #'(case-split-hint args ...)]
    [_ #'case-split-hint]))

;; for debugging merges: basically acts like a merge and calls the
;; callback with all the paths
;;
;; return value is not used (unlike other hints, which return another hint
(struct debug* hint (callback))

(struct concretize hint (lens use-pc use-equalities piecewise k))

(define (concretize-hint lens #:piecewise [piecewise #f] #:use-pc [use-pc #f] #:use-equalities [use-equalities #f])
  (wrap (concretize lens use-pc use-equalities piecewise)))

(define-match-expander concretize#
  (syntax-parser [(_ args ...) #'(concretize args ...)])
  (syntax-parser
    [(_ args ...) #'(concretize-hint args ...)]
    [_ #'concretize-hint]))

(struct overapproximate hint (lens k))

(define (overapproximate-hint lens)
  (wrap (overapproximate lens)))

(define-match-expander overapproximate#
  (syntax-parser [(_ args ...) #'(overapproximate args ...)])
  (syntax-parser
    [(_ args ...) #'(overapproximate-hint args ...)]
    [_ #'overapproximate-hint]))

(struct overapproximate-pc hint (pc use-equalities k))

(define (overapproximate-pc-hint pc #:use-equalities [use-equalities #f])
  (wrap (overapproximate-pc pc use-equalities)))

(define-match-expander overapproximate-pc#
  (syntax-parser [(_ args ...) #'(overapproximate-pc args ...)])
  (syntax-parser
    [(_ args ...) #'(overapproximate-pc-hint args ...)]
    [_ #'overapproximate-pc-hint]))

(struct replace hint (lens term use-pc use-equalities k))

(define (replace-hint lens term #:use-pc [use-pc #f] #:use-equalities [use-equalities #f])
  (wrap (replace lens term use-pc use-equalities)))

(define-match-expander replace#
  (syntax-parser [(_ args ...) #'(replace args ...)])
  (syntax-parser
    [(_ args ...) #'(replace-hint args ...)]
    [_ #'replace-hint]))

(struct remember hint (lens name k))

(define (remember-hint lens [name #f])
  (wrap (remember lens name)))

(define-match-expander remember#
  (syntax-parser [(_ args ...) #'(remember args ...)])
  (syntax-parser
    [(_ args ...) #'(remember-hint args ...)]
    [_ #'remember-hint]))

(struct subst hint (lens variable k))

(define (subst-hint lens [variable #f])
  (wrap (subst lens variable)))

(define-match-expander subst#
  (syntax-parser [(_ args ...) #'(subst args ...)])
  (syntax-parser
    [(_ args ...) #'(subst-hint args ...)]
    [_ #'subst-hint]))

(struct clear hint (variable k))

(define (clear-hint [variable #f])
  (wrap (clear variable)))

(define-match-expander clear#
  (syntax-parser [(_ args ...) #'(clear args ...)])
  (syntax-parser
    [(_ args ...) #'(clear-hint args ...)]
    [_ #'clear-hint]))
