#lang racket/base

(provide
 (except-out (struct-out driver) driver)
 (rename-out [driver make-driver]))

(struct driver
  (bindings
   idle)) ; list of (cons signal-name value)
