#lang racket/base

(require
 yosys/meta
 "../driver.rkt"
 "../circuit.rkt"
 "../spec.rkt"
 "../result.rkt"
 "../driver/interpreter.rkt"
 "checker.rkt"
 "hint.rkt"
 (only-in racket/class new send)
 (prefix-in @ (combine-in rosette/safe rosutil/addressable-struct rosutil/convenience)))

(provide verify-correctness)

(define (verify-correctness
         spec
         circuit
         driver
         #:R R
         #:hints [hints (lambda (method c1 f1 f-out f2) (make-hintdb))]
         #:only [only-method #f] ; method name or 'init or 'idle
         #:override-args [override-args #f]
         #:override-f1 [override-f1 #f]
         #:override-c1 [override-c1 #f]
         #:without-crashes [without-crashes #f]
         #:without-yield [without-yield #f]
         #:verbose [verbose #f])
  (@gc-terms!)
  (define crash+por (crash+power-on-reset circuit)) ; so we can re-use it
  (when (or (not only-method) (equal? only-method 'invariant))
    (when verbose (printf "verifying invariant...\n"))
    (verify-invariant circuit verbose)
    (when verbose (printf "  done!\n")))
  (when (or (not only-method) (equal? only-method 'init))
    (when verbose (printf "verifying init...\n"))
    (verify-init spec circuit crash+por R verbose)
    (when verbose (printf "  done!\n")))
  (when (or (not only-method) (equal? only-method 'idle))
    (when verbose (printf "verifying idle...\n"))
    (verify-idle spec circuit driver R verbose)
    (when verbose (printf "  done!\n")))
  (for ([method (spec-methods spec)])
    (when (or (not only-method) (equal? only-method (method-descriptor-name method)))
      (when verbose (printf "verifying method ~a~a...\n"
                            (method-descriptor-name method)
                            (if without-crashes " (without crashes)" "")))
      (verify-method spec circuit crash+por driver R method override-args override-f1 override-c1 without-crashes without-yield hints verbose)
      (when verbose (printf "  done!\n")))))

;; yosys uses the {module}_i to denote an initializer, not an invariant,
;; but we only use the initializer to initialize ROMs, and so it's an invariant
;;
;; still, here, we double-check that it's indeed an invariant, and that the
;; user didn't accidentally have other mutable fields be initialized
(define (verify-invariant circuit verbose)
  (define m (circuit-meta circuit))
  (define c1 ((meta-new-symbolic m)))
  (define c2 ((meta-step m) c1))
  (define inv (meta-invariant m))
  (define res
    (@verify
     (@begin
      (@assume (inv c1))
      (@assert (inv c2)))))
  (cond
    [(@unsat? res) (void)] ; verified
    [(@unknown? res) (error 'verify-invariant "solver timeout")]
    [else (error 'verify-invariant "failed to prove invariant: misuse of 'initial' in Verilog?")]))

(define (verify-init spec circuit crash+por R verbose)
  (define f0 (spec-init spec))
  (define m (circuit-meta circuit))
  (define c0
    (@update-fields
     ((meta-new-symbolic m))
     (let ([c-zeroed ((meta-new-zeroed m))])
       (for/list ([field-name (circuit-init-zeroed-fields circuit)])
         (cons field-name (@get-field c-zeroed field-name))))))
  (define c-init (crash+por c0))
  (define inv (meta-invariant m))
  (define res
    (@verify
     (@begin
      (@assume (inv c0))
      (@assert (R f0 c-init)))))
  (cond
    [(@unsat? res) (void)] ; verified
    [(@unknown? res) (error 'verify-init "solver timeout")]
    [verbose
     (define sol (@complete-solution res (@symbolics (@list f0 c-init))))
     (eprintf "failed to prove init\n")
     (eprintf "c-init = ~v\n" (@evaluate c-init sol))
     (eprintf "f0 = ~v\n" (@evaluate f0 sol))
     (eprintf "(R f0 c-init) = ~v\n" (@evaluate (R f0 c-init) sol))
     ;; finally, raise an error
     (error 'verify-init "failed to prove init")]
    [else (error 'verify-init "failed to prove init")]))

(define (verify-idle spec circuit driver R verbose)
  (define f1 ((spec-new-symbolic spec)))
  (define m (circuit-meta circuit))
  (define idle-input
    (@update-field
     (@update-fields ((meta-new-symbolic-input (circuit-meta circuit)))
                     (driver-idle driver))
     (circuit-reset-input-name circuit)
     (not (circuit-reset-input-signal circuit))))
  (define c1 ((meta-new-symbolic m)))
  (define c2 ((meta-step m) ((meta-with-input m) c1 idle-input)))
  (define inv (meta-invariant m))
  (define res
    (@verify
     (@begin
      (@assume (R f1 c1))
      (@assume (inv c1))
      (@assert (R f1 c2)))))
  (cond
    [(@unsat? res) (void)] ; verified
    [(@unknown? res) (error 'verify-idle "solver timeout")]
    [verbose
     (define sol (@complete-solution res (@symbolics (@list f1 idle-input c1 c2))))
     (eprintf "failed to prove idle\n")
     (eprintf "c1 = ~v\n" (@evaluate c1 sol))
     (eprintf "f1 = ~v\n" (@evaluate f1 sol))
     (eprintf "(R f1 c1) = ~v\n" (@evaluate (R f1 c1) sol))
     (eprintf "input = ~v\n" (@evaluate idle-input sol))
     (eprintf "c2 = ~v\n" (@evaluate c2 sol))
     (eprintf "(R f1 c2) = ~v\n" (@evaluate (R f1 c2) sol))
     (error 'verify-idle "failed to prove idle")]
    [else (error 'verify-idle "failed to prove idle")]))

(define (verify-method spec circuit crash+por driver R method override-args override-f1 override-c1 without-crashes without-yield hints verbose)
  ;; set up method and arguments
  (define method-name (method-descriptor-name method))
  (define spec-fn (method-descriptor-method method))
  (define args
    (or override-args
        (for/list ([arg (method-descriptor-args method)])
          (define type (argument-type arg))
          (if (list? type)
            (for/list ([el type]
                       [i (in-naturals)])
              (@fresh-symbolic (format "~a[~a]" (symbol->string (argument-name arg)) i) el))
            (@fresh-symbolic (argument-name arg) (argument-type arg))))))
  ;; spec
  (define f1 (or override-f1 ((spec-new-symbolic spec))))
  (define f-result (@check-no-asserts ((@apply spec-fn args) f1) #:discharge-asserts #t))
  (define f-out (result-value f-result))
  (define f2 (result-state f-result))
  ;; circuit
  (define m (circuit-meta circuit))
  (define c1 (@update-field (or override-c1 ((meta-new-symbolic m)))
                            (circuit-reset-input-name circuit)
                            (not (circuit-reset-input-signal circuit))))
  ;; make sure reset line is de-asserted
  (define driver-expr (cons method-name (map (lambda (arg) (list 'quote arg)) args)))
  (define initial-interpreter-state
    (make-interpreter driver-expr (driver-bindings driver) c1 m))
  (define local-hints (hints (cons method-name args) c1 f1 f-out f2))
  (define inv (meta-invariant m))
  (define precondition (@check-no-asserts (@&& (R f1 c1) (inv c1))))
  (define exc (new checker%
                   [initial-state initial-interpreter-state]
                   [hint-db local-hints]
                   [precondition precondition]
                   [R (if without-crashes #f R)] ; a bit of a hack, to tell exc whether we want to check for crash safety
                   [without-yield without-yield]
                   [f1 f1]
                   [f2 f2]
                   [crash+power-on-reset crash+por]))
  (when verbose (send exc debug!))
  ;; run
  (define finished (send exc run!))
  (for ([f finished])
    (define pc (checker-state-pc f))
    (define c-result (checker-state-interpreter f))
    (define c-out (finished-value c-result))
    (define c2 (finished-circuit c-result))
    (define res
      (@verify
       (@begin
        (@assume precondition) ; R and hardware invariant
        (@assume pc)
        (@assert (@equal? f-out c-out))
        (@assert (R f2 c2)))))
    (cond
      [(@unsat? res) (void)] ; verified
      [(@unknown? res) (error 'verify-method "~a: solver timeout" method-name)]
      [verbose
       (define sol (@complete-solution res (@symbolics (@list args f1 f-out f2 c1 c-out c2))))
       (eprintf "failed to verify ~a\n" method-name)
       (eprintf "c1 = ~v\n" (@evaluate c1 sol))
       (eprintf "f1 = ~v\n" (@evaluate f1 sol))
       (eprintf "args = ~v\n" (@evaluate args sol))
       (eprintf "f2 = ~v\n" (@evaluate f2 sol))
       (eprintf "f-out = ~v\n" (@evaluate f-out sol))
       (eprintf "c-out = ~v\n" (@evaluate c-out sol))
       (eprintf "(R f2 c2) = ~v\n" (@evaluate (R f2 c2) sol))
       (eprintf "c2 = ~v\n" (@evaluate c2 sol))
       ;; finally, raise an error
       (error 'verify-method "failed to verify ~a" method-name)]
      [else (error 'verify-method "failed to verify ~a" method-name)])))
