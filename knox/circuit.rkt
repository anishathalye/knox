#lang racket/base

(require yosys/meta
         rosutil/addressable-struct)

(provide
 (except-out (struct-out circuit) circuit)
 (rename-out [circuit make-circuit])
 crash+power-on-reset)

(struct circuit
  (meta ; from #lang yosys circuit
   reset-input-name
   reset-input-signal ; #t or #f, what the signal should be set to for reset
   persistent-fields ; list of field names
   init-zeroed-fields)) ; fields that are initially zero

;; This function returns a function that produces the
;; post-crash/power-on-reset version of a circuit; the reason it's structured
;; this way is that we want to cache the underlying symbolic circuit that's used
;; as the "base" of the returned havoced circuit, for performance. This means
;; that the result from this function should *not* be re-used across multiple calls
;; to crash+power-on-reset (even after some modifications in between); for example,
;; it can't be used to reason about what happens across multiple crash+power-on-reset
;; operations, because the underlying symbolic variables will be shared rather than
;; fresh across the calls. We do not use this function in this incorrect way in the
;; framework: we either have it be the "initial" call (in verifying init for correctness),
;; or we use it as the "terminal" call (verifying the crash property in correctness
;; or security, where we don't re-use the result after checking the property).
(define (crash+power-on-reset circuit)
  (let* ([m (circuit-meta circuit)]
         [rst (circuit-reset-input-name circuit)]
         [rst-signal (circuit-reset-input-signal circuit)]
         [new-symbolic-input (meta-new-symbolic-input m)]
         [i-rst (update-field (new-symbolic-input) rst rst-signal)]
         [i-no-rst (update-field (new-symbolic-input) rst (not rst-signal))]
         [with-input (meta-with-input m)]
         [step (meta-step m)]
         [symbolic ((meta-new-symbolic m))])
    (lambda (c1)
      ;; copy over persistent state _before_ reset (rather than after reset),
      ;; because reset might depend on persistent state
      (let* ([havoced (for/fold ([c symbolic])
                                ([field (circuit-persistent-fields circuit)])
                        (update-field c field (get-field c1 field)))])
        (with-input (step (with-input havoced i-rst)) i-no-rst)))))
