#lang racket/base

(require
 (prefix-in interp: "../driver/interpreter.rkt")
 "hint.rkt"
 racket/class racket/set racket/match racket/list racket/function
 (prefix-in yosys: yosys)
 (prefix-in @ (combine-in rosutil rosette/safe))
 syntax/parse/define)

(provide checker%
         (prefix-out checker- (struct-out state)))

(@addressable-struct state
  (interpreter
   pc
   equalities))

(struct execution
  (state
   next-hint)
  #:transparent)

(define (protected-evaluate-to-next-hint k [arg (void)])
  (if k
      (@check-no-asserts (evaluate-to-next-hint k arg))
      #f))

(define (finished? st)
  (not (interp:state? (state-interpreter st))))

(define (weak-seteq->seteq s)
  (for/seteq ([e (in-weak-set s)]) e))

(define top-view
  (@virtual-lens
   (list
    (cons 'circuit (@lens 'globals 'circuit))
    (cons 'interpreter (@virtual-lens
                        (list
                         (cons 'control (@lens 'control))
                         (cons 'environment (@lens 'environment))
                         (cons 'continuation (@lens 'continuation))))))))

(define checker%
  (class object%
    (super-new)
    (init initial-state)
    (init-field hint-db)
    (init [precondition #t])
    (init-field [R #f])
    (init-field [crash+power-on-reset #f])
    (init-field [f1 #f])
    (init-field [f2 #f])
    (init-field [without-yield #f])
    (define free-variables (weak-seteq))
    (define completed '()) ; list of state
    (define working (list (execution (state initial-state precondition (hasheq)) #f))) ; list of execution
    (define waiting '()) ; list of state (not execution, because we already have the hint saved in merge-hint)
    (define debug*-hint #f)
    (define merge-hint #f)
    (define debug #f)

    ;; weak hash of [circuit -> weak set of path conditions]
    (define crash-cache (make-weak-hasheq))
    (define empty-set (weak-set))
    ;; we get a pretty big win by caching the result of the last query
    (define last-ok-query (void))
    ;; not the most performant implementation...
    (define (check-crash-condition pc c)
      (when (and R (not (set-member? (hash-ref crash-cache c empty-set) pc)))
        (define c-crash (crash+power-on-reset c))
        (define q
          (@check-no-asserts
            (@or (@implies pc (R f1 c-crash))
                 (@implies pc (R f2 c-crash)))))
        (cond
          [(or (eqv? q #t) ; query evaluates to #t in Rosette, so no need to call solver?
               (eq? q last-ok-query) ; already verified this query?
               (@unsat? (@verify (@assert q))))
           (unless (eqv? q #t) ; no point in caching #t
             (set! last-ok-query q)) ; cache the result of this query
           (set-add! (hash-ref! crash-cache c (lambda () (weak-set))) pc)] ; cache that this circuit/pc is ok
          [else (error "failed to prove crash safety")])))

    (define/public (debug!)
      (set! debug #t))

    (define (dprintf . args)
      (when debug (apply eprintf args)))

    (define (run-single! exc)
      (match-define (execution st hint) exc)
      (cond
        ;; are there any pending hints? if so run them
        [hint (run-hint! st hint)]
        ;; no pending hints; run to next hypercall, handle it
        [else
         (define st* (run-to-next-hypercall st))
         (cond
           [(finished? st*)
            ;; value
            (set! completed (cons st* completed))]
           [else
            ;; hypercall
            (handle-hypercall! st*)])]))

    (define (handle-hypercall! st)
      (match-define (state (and ist (interp:state control environment globals continuation)) pc equalities) st)
      (unless (list? control)
        (error 'handle-hypercall! "hypercall must be a concrete list, not a term (~v), try concretizing more?" control))
      (match-define (list fun hint-name) control)
      (define hint (hash-ref hint-db hint-name))
      (case fun
        [(yield)
         (cond
           [without-yield
            ;; step past
            (define st1 (@check-no-asserts (interp:step ist) #:assumes pc))
            ;; no need to check crash condition, just stepping past the yield
            (set! working (cons (execution (state st1 pc equalities) #f) working))]
           [else
            (unless (fixpoint? hint)
              (error 'handle-hypercall! "argument to yield must be a fixpoint hint"))
            (define ckt (interp:globals-circuit globals))
            (define metadata (interp:globals-meta globals))
            (define ckt-step (yosys:meta-step metadata))
            (match-define (fixpoint setup auto len step-concretize-lens use-pc piecewise step-overapproximate-lens k) hint)
            (define fp
              (compute-fixpoint
               pc
               (@&& pc (equalities->bool equalities))
               ckt-step
               ckt
               setup
               auto
               len
               step-concretize-lens
               use-pc
               piecewise
               step-overapproximate-lens))
            ;; step (interpreter) once more to advance past the call
            (define st1 (@check-no-asserts (interp:step ist) #:assumes pc))
            (check-crash-condition pc (interp:globals-circuit (interp:state-globals st1)))
            ;; make one state for every point in fp, put back on working list
            (set! working
                  (append
                   (for/list ([ckt fp])
                     (let ([st* (state (update-state-circuit st1 ckt) pc equalities)])
                       (execution st* (protected-evaluate-to-next-hint k))))
                   working))
            (dprintf "info: yielded, now have ~a threads, ~a waiting~n" (length working) (length waiting))])]
        [(hint)
         ;; don't actually do anything here, just remember that we need to apply the hint next, and
         ;; step once more to advance past the call
         (define st1 (@check-no-asserts (interp:step ist) #:assumes pc))
         (check-crash-condition pc (interp:globals-circuit (interp:state-globals st1)))
         (set! working (cons (execution (state st1 pc equalities) hint) working))]))

    (define (run-hint! st hint)
      (match-define (state ist pc equalities) st)
      (match hint
        [(? done?) (set! working (cons (execution st #f) working))]
        [(tactic k)
         (set! working (cons (execution st (protected-evaluate-to-next-hint k)) working))]
        [(get-state k)
         (set! working (cons (execution st (protected-evaluate-to-next-hint k st)) working))]
        [(concretize! lens use-pc use-equalities piecewise k)
         (define full-lens (@lens-thrush top-view lens))
         (define effective-pc (@&&
                               (if use-pc pc #t)
                               (if use-equalities (equalities->bool equalities) #t)))
         (define ist* (@lens-transform full-lens ist
                                       (lambda (view) (@concretize view effective-pc #:piecewise piecewise))))
         (define st* (state ist* pc equalities))
         (set! working (cons (execution st* (protected-evaluate-to-next-hint k)) working))]
        [(overapproximate! lens k)
         (define full-lens (@lens-thrush top-view lens))
         (define view (@lens-view full-lens ist))
         (define overapprox-view (@overapproximate view))
         (for ([var (in-list (@symbolics overapprox-view))])
           (set-add! free-variables var))
         (define ist* (@lens-set full-lens ist overapprox-view))
         (define st* (state ist* pc equalities))
         (set! working (cons (execution st* (protected-evaluate-to-next-hint k overapprox-view)) working))]
        [(overapproximate-pc! new-pc use-equalities k)
          (define effective-pc (if use-equalities
                                   (@&& pc (equalities->bool equalities))
                                   pc))
          (unless (@unsat? (@verify (@assert (@implies effective-pc new-pc))))
            (error 'run-hint! "hint overapproximate-pc: not an overapproximation"))
          (define st* (state ist new-pc equalities))
          (set! working (cons (execution st* (protected-evaluate-to-next-hint k)) working))]
        [(replace! lens view use-pc use-equalities k)
         (define full-lens (@lens-thrush top-view lens))
         (define current-view (@lens-view full-lens ist))
         (define effective-pc (@&&
                               (if use-pc pc #t)
                               (if use-equalities (equalities->bool equalities) #t)))
         (unless (@unsat? (@verify (@begin (@assume effective-pc) (@assert (@equal? current-view view)))))
           (error 'run-hint! "hint replace: failed to prove equality"))
         (define ist* (@lens-set full-lens ist view))
         (define st* (state ist* pc equalities))
         (set! working (cons (execution st* (protected-evaluate-to-next-hint k)) working))]
        [(remember! lens name k)
         (define full-lens (@lens-thrush top-view lens))
         (define current-view (@lens-view full-lens ist))
         (define current-type (@type-of current-view))
         (when (not (@solvable? current-type))
           (error 'run-hint! "hint remember: not a solvable type"))
         (define new-var (@fresh-symbolic (or name '||) current-type))
         (define ist* (@lens-set full-lens ist new-var))
         (define st* (state ist* pc (hash-set equalities new-var current-view)))
         ;; pass new variable to callback...
         (set! working (cons (execution st* (protected-evaluate-to-next-hint k new-var)) working))]
        [(subst! lens var k)
         (define full-lens (@lens-thrush top-view lens))
         (define ist* (@lens-transform full-lens ist (lambda (view)
                                                       (if var
                                                           (@substitute view var (hash-ref equalities var))
                                                           (@substitute-terms view equalities)))))
         (define st* (state ist* pc equalities))
         (set! working (cons (execution st* (protected-evaluate-to-next-hint k)) working))]
        [(clear! var k)
         (define equalities* (if var
                                 (if (list? var)
                                     (for/fold ([equalities equalities])
                                               ([v var])
                                       (hash-remove equalities var))
                                     (hash-remove equalities var))
                                 (hasheq)))
         (define st* (state ist pc equalities*))
         (set! working (cons (execution st* (protected-evaluate-to-next-hint k)) working))]
        [(case-split! splits* use-equalities k)
         (define splits (do-case-split st use-equalities splits*))
         (set! working (append (map (lambda (st) (execution st (protected-evaluate-to-next-hint k))) splits) working))]
        [(? merge!?)
         ;; put on waiting list
         (set! waiting (cons st waiting))
         (set! debug*-hint #f)
         (unless merge-hint
           (set! merge-hint hint))]
        [(? debug*?)
         (set! waiting (cons st waiting))
         (unless debug*-hint
           (set! debug*-hint hint))]
        [else (error 'run-hint! "unimplemented hint: ~a" hint)]))

    (define (do-debug*!)
      ((debug*-callback debug*-hint) waiting)
      (set! working (map (lambda (st) (execution st #f)) waiting))
      (set! waiting '())
      (set! debug*-hint #f))

    (define (do-case-split st use-equalities splits)
      ;; split interpreter N ways, augmenting path condition with splits
      ;;
      ;; check that the split is indeed an exhaustive split (given current pc)
      ;;
      ;; doesn't make use of extra info in equalities, but that's okay
      (define pc (state-pc st))
      (define effective-pc (if use-equalities
                               (@&& pc (equalities->bool (state-equalities st)))
                               pc))
      ;; prune unsat splits
      (define pruned-splits
        (filter (lambda (p) (not (@unsat? (@solve (@assert (@&& effective-pc p)))))) splits))
      ;; verify that the current pc implies that at least one of the splits must hold
      ;;
      ;; if we have splits p1, p2, ..., pn, we prove _here_ that
      ;; pc => (p1 \/ p2 \/ ... \/ pn), and we create n threads
      ;; with pcs (pc /\ p1), (pc /\ p2), ..., (pc /\ pn)
      (define any-split (apply @|| pruned-splits))
      (when (not (@unsat? (@verify (@assert (@implies effective-pc any-split)))))
        (error 'do-case-split "failed to prove exhaustiveness"))
      (dprintf "info: case split ~a ways~n" (length pruned-splits))
      (for/list ([p pruned-splits])
        (state (state-interpreter st) (@&& pc p) (state-equalities st))))

    (define (merge-states!)
      ;; first, partition by path condition (we never merge across different PCs)
      (define by-pc-eq (group-by (lambda (st) (cons (state-pc st) (state-equalities st))) waiting))
      (define free-vars-seteq (weak-seteq->seteq free-variables))
      (define merged (apply append (map (lambda (st) (merge-states-for-pc-eq st free-vars-seteq)) by-pc-eq)))
      (define k (merge!-k merge-hint))
      (set! working (map (lambda (st) (execution st (protected-evaluate-to-next-hint k))) merged))
      (dprintf "info: merged, reduced from ~v states to ~v states~n" (length waiting) (length working))
      (set! waiting '())
      (set! merge-hint #f))

    (define (merge-states-for-pc-eq sts free-vars-seteq)
      ;; right now, we only handle the case where the rest of the
      ;; interpreter state is identical between all forks; in the future, we
      ;; could partition by interpreter state and support multiple, but I don't
      ;; think this is necessary right now
      (define template-state (first sts))
      (define template-interpreter (state-interpreter template-state))
      (for ([st (rest sts)])
        (define ist (state-interpreter st))
        ;; note: we don't check globals, because we're expecting the
        ;; circuit to differ, and we're not expecting the environment or meta
        ;; to differ (it never changes)
        (unless (or (and (interp:finished? ist) (interp:finished? template-interpreter))
                    (and (equal? (interp:state-control ist) (interp:state-control template-interpreter))
                         (equal? (interp:state-environment ist) (interp:state-environment template-interpreter))
                         (equal? (interp:state-continuation ist) (interp:state-continuation template-interpreter))))
          (error 'merge-states! "interp:states differ in aspects other than circuit")))
      (define effective-pc
        (let* ([st1 (first sts)]
               [pc (state-pc st1)]
               [eq (state-equalities st1)])
          (@&& pc (equalities->bool eq))))
      (define ckts
        (shrink-by-key
         (map
          (lambda (st)
            (define s (state-interpreter st))
            (if (interp:finished? s) (interp:finished-circuit s) (interp:globals-circuit (interp:state-globals s))))
          sts)
         (merge!-key merge-hint)
         effective-pc
         free-vars-seteq))
      (for/list ([ckt ckts])
        (state (update-state-circuit template-interpreter ckt) (state-pc template-state) (state-equalities template-state))))

    (define (compute-fixpoint pc effective-pc step s0 setup-cycles auto cycle-length step-concretize-lens use-pc piecewise step-overapproximate-lens)
      (define (step* ckt)
        ;; step, but applying concretization/overapproximatino if required at every step
        (let* ([ckt (step ckt)]
               [ckt (if step-concretize-lens
                        (@lens-transform step-concretize-lens ckt (lambda (view) (@concretize view (if use-pc pc #t) #:piecewise piecewise)))
                        ckt)]
               [ckt (if step-overapproximate-lens
                        (let ([overapprox-view (@overapproximate (@lens-view step-overapproximate-lens ckt))])
                          (for ([var (in-list (@symbolics overapprox-view))])
                            (set-add! free-variables var))
                          (@lens-set step-overapproximate-lens ckt overapprox-view))
                        ckt)])
          (check-crash-condition pc ckt)
          ckt))
      (let loop ([rev-steps (rev-step-n step* s0 (+ cycle-length (or setup-cycles 0)))]) ; going to need a minimum of this many steps
        (dprintf "info: auto fixpoint finding at ~a cycles of setup~n" (- (length rev-steps) cycle-length 1))
        ;; next step
        (define next-step (step* (first rev-steps)))
        (define earlier (list-ref rev-steps cycle-length))
        ;; if subsumption check passes, we're done, otherwise append it to the list of steps and continue
        (define fv (weak-seteq->seteq free-variables))
        (cond
          [(@subsumed? fv next-step effective-pc earlier effective-pc #:skip-empty-check #t)
           (dprintf "info: fixpoint found with ~a cycle setup (and ~a cycle length)~n"
                    (- (length rev-steps) cycle-length 1) cycle-length)
           (reverse rev-steps)]
          [else
           (if auto
               (loop (cons next-step rev-steps))
               (begin
                 (dprintf "next step: ~v~n does not loop back to~nearlier: ~v~ndiff: ~a~n" next-step earlier (@show-diff next-step earlier))
                 (error 'compute-fixpoint "Did not find a fixpoint")))])))

    (define (shrink-by-key s key path-condition free-vars-seteq)
      (define groups (group-by key s))
      (dprintf "info: merging, have ~a states grouped into ~a partitions~n" (length s) (length groups))
      ;; note: we pass in the free-variables converted to a seteq to minimize allocations
      (apply append (map (curry shrink-set free-vars-seteq path-condition) groups)))

    ;; aims to be sound, can't be "complete" (what is complete?)
    (define (shrink-set free-vars-seteq path-condition s)
      (dprintf "info: merging ~a states~n" (length s))
      (let loop ([pending (reverse s)]
                 [keep '()])
        (if (empty? pending)
            (begin
              (dprintf "info: merged into ~a states~n" (length keep))
              keep)
            (let ()
              (define p (first pending))
              (define pp (rest pending))
              (define represented
                (for/or ([k keep])
                  (@subsumed? free-vars-seteq p path-condition k path-condition #:skip-empty-check #t)))
              (if represented
                  (loop pp keep)
                  ;; need to add
                  (loop pp (cons p keep)))))))

    (define (run-to-next-hypercall st)
      (if (not (finished? st))
          (if (in-hypercall? (state-interpreter st))
              st ; return as-is
              (let ()
                (define st1 (@check-no-asserts (interp:step (state-interpreter st)) #:assumes (state-pc st)))
                (if (interp:finished? st1)
                    (check-crash-condition (state-pc st) (interp:finished-circuit st1))
                    (check-crash-condition (state-pc st) (interp:globals-circuit (interp:state-globals st1))))
                (run-to-next-hypercall (state st1 (state-pc st) (state-equalities st)))))
          ;; value
          st))

    (define (in-hypercall? st)
      (interp:uninterpreted? (interp:state-control st)))

    (define/public (run!)
      (cond
        [(and (empty? working) (empty? waiting))
         ;; we are completed, return values
         completed]
        [(not (empty? working))
         ;; more "single threads" to execute
         (match-define (cons h t) working)
         (set! working t)
         (run-single! h)
         (run!)]
        [else
         ;; merge
         (if debug*-hint
             (do-debug*!)
             (merge-states!))
         (run!)]))))

(define (rev-step-n step s0 n)
  (let loop ([s s0]
             [n n])
    (if (zero? n)
        (list s)
        (let* ([ss (loop s (sub1 n))]
               [sn-1 (first ss)])
          (cons (step sn-1) ss)))))

(define (update-state-circuit st ckt)
  (if (interp:state? st)
      (interp:state
       (interp:state-control st)
       (interp:state-environment st)
       (interp:update-circuit (interp:state-globals st) ckt)
       (interp:state-continuation st))
      (interp:finished (interp:finished-value st) ckt)))

(define (equalities->bool eqt)
  (apply @&& (for/list ([(k v) (in-hash eqt)]) (@equal? k v))))
