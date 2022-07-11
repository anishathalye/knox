#lang rosette/safe

(require
 (only-in rosutil/addressable-struct addressable-struct)
 "../result.rkt"
 "../spec.rkt"
 (for-syntax racket/base racket/syntax syntax/parse))

(provide
 (except-out (all-from-out rosette/safe) struct #%module-begin)
 (rename-out [addressable-struct struct]
             [$#%module-begin #%module-begin])
 (all-from-out "../result.rkt"))

(define-syntax ($#%module-begin stx)
  (syntax-parse stx
    [(_
      #:init s0
      #:symbolic-constructor new-symbolic-state
      #:methods
      (method [arg-name arg-type] ...) ...
      (~optional (~seq #:leak leak) #:defaults ([leak #'#f]))
      body ...)
     #:with spec (format-id stx "spec")
     #'(#%module-begin
        body ...
        (define spec
          (make-spec
           s0
           new-symbolic-state
           (list
            (method-descriptor method 'method (list (argument 'arg-name arg-type) ...)) ...)
           leak))
        (provide spec))]
    [(_ body ...) ; fallback, useful in e.g. submodules (like a test module)
     #'(#%module-begin body ...)]))
