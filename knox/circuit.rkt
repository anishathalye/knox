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

(define (crash+power-on-reset circuit)
  (let* ([m (circuit-meta circuit)]
         [rst (circuit-reset-input-name circuit)]
         [rst-signal (circuit-reset-input-signal circuit)]
         [new-symbolic-input (meta-new-symbolic-input m)]
         [i-rst (update-field (new-symbolic-input) rst rst-signal)]
         [i-no-rst (update-field (new-symbolic-input) rst (not rst-signal))]
         [with-input (meta-with-input m)]
         [step (meta-step m)]
         [havoced+reset (with-input (step (with-input ((meta-new-symbolic m)) i-rst)) i-no-rst)])
    (lambda (c1)
      (for/fold
          ([c havoced+reset])
          ([field (circuit-persistent-fields circuit)])
        (update-field c field (get-field c1 field))))))
