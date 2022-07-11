#lang racket/base

(require racket/generic)

(provide gen:yosys-module yosys-module? yosys-module/c)

;; just a tag
(define-generics yosys-module)
