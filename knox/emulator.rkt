#lang racket/base

(provide
 (except-out (struct-out emulator) emulator)
 (rename-out [emulator make-emulator]))

(struct emulator
  (bindings))
