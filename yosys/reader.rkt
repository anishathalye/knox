#lang racket/base

(require racket/list racket/string racket/match
         syntax/readerr)

(provide (rename-out
          [yosys-read read]
          [yosys-read-syntax read-syntax]))

(define (make-yosys-readtable)
  (make-readtable (current-readtable)
                  #\b 'dispatch-macro read-bitvector
                  #\; 'terminating-macro read-comment))

(define (make-yosys-toplevel-readtable)
  (make-readtable (make-yosys-readtable)
                  #\( 'terminating-macro (read-toplevel-paren (current-readtable))))

(define (delimiter? c)
  (cond
    [(char-whitespace? c) #t]
    [else (case c
            [(#\() #t]
            [(#\)) #t]
            [(#\[) #t]
            [(#\]) #t]
            [(#\{) #t]
            [(#\}) #t]
            [(#\") #t]
            [(#\,) #t]
            [(#\') #t]
            [(#\`) #t]
            [(#\;) #t]
            [else #f])]))

(define (read-bitvector match-ch in src init-line init-col init-pos)
  (define digits
    (let loop ([acc '()])
      (let ([c (peek-char in)])
        (cond
          [(eof-object? c) acc]
          [(delimiter? c) acc]
          [(not (or (char=? c #\0) (char=? c #\1)))
           (let-values ([(line col pos) (port-next-location in)])
             (raise-read-error (format "bad digit `~a`" c) src line col pos 1))]
          [else
           (read-char in)
           (loop (cons c acc))]))))
  (when (empty? digits)
    (raise-read-error "no digits" src init-line init-col init-pos 2))
  (define value
    (for/fold ([acc 0])
              ([i (in-list (reverse digits))])
      (+ (* acc 2) (if (char=? i #\0) 0 1))))
  (define width (length digits))
  (datum->syntax #f `(bv ,value ,width)
                 (and
                  init-line
                  (vector src init-line init-col init-pos width))))

; handling newlines the same way as Racket's line comment reader
(define (newline? c)
  (case c
    [(#\u0a) #t]
    [(#\u0d) #t]
    [(#\u85) #t]
    [(#\u2028) #t]
    [(#\u2029) #t]
    [else #f]))

(define (read-until-eol port)
  (define chars
    (let loop ([acc '()])
      (let ([c (read-char port)])
        (cond
          [(eof-object? c) acc]
          [(newline? c) acc]
          [else (loop (cons c acc))]))))
  (apply string-append (map string (reverse chars))))

; Yosys emits certain useful information as comments. We try to
; recognize all of these useful comments and preserve them, so the
; expander layer can do something useful with them.
(define (read-comment match-ch in src init-line init-col init-pos)
  (define comment (read-until-eol in))
  (define width (string-length comment))
  (define srcloc
    (and
     init-line
     (vector src init-line init-col init-pos width)))
  (define trimmed (string-trim comment))
  (match trimmed
    [(regexp #px"^yosys-smt2-stdt$")
     (datum->syntax #f '(yosys-smt2-stdt) srcloc)]
    [(regexp #px"^yosys-smt2-module (.*)$" (list _ module-name))
     (datum->syntax #f `(yosys-smt2-module ,(string->symbol module-name)) srcloc)]
    [(regexp #px"^yosys-smt2-topmod (.*)$" (list _ topmod-name))
     (datum->syntax #f `(yosys-smt2-topmod ,(string->symbol topmod-name)) srcloc)]
    [(regexp #px"^yosys-smt2-clock (.*) (.*)$" (list _ clock-name clock-edge))
     (datum->syntax #f `(yosys-smt2-clock ,(string->symbol clock-name) ',(string->symbol clock-edge)) srcloc)]
    [(regexp #px"^yosys-smt2-input (.*) (\\d+)$" (list _ input-name input-width))
     (datum->syntax #f `(yosys-smt2-input ,(string->symbol input-name) ,(string->number input-width)))]
    [(regexp #px"^yosys-smt2-output (.*) (\\d+)$" (list _ output-name output-width))
     (datum->syntax #f `(yosys-smt2-output ,(string->symbol output-name) ,(string->number output-width)))]
    [(regexp #px"^yosys-smt2-register (.*) (\\d+)$" (list _ register-name register-width))
     (datum->syntax #f `(yosys-smt2-register ,(string->symbol register-name) ,(string->number register-width)))]
    [(regexp #px"^yosys-smt2-memory (.*) (\\d+) (\\d+) (\\d+) (\\d+) (.*)$"
             (list _ memory-name memory-bits memory-width memory-read-ports memory-write-ports memory-sync))
     (datum->syntax #f `(yosys-smt2-memory ,(string->symbol memory-name) ,(string->number memory-bits) ,(string->number memory-width) ,(string->number memory-read-ports) ,(string->number memory-write-ports) ',(string->symbol memory-sync)) srcloc)]
    [else
     (make-special-comment comment)]))

(define (make-yosys-declare-datatype-readtable)
  (make-readtable (current-readtable)
                  #\; 'terminating-macro read-declare-datatype-comment))

(define (read-declare-datatype-comment match-ch in src init-line init-col init-pos)
  (define comment (read-until-eol in))
  (define width (string-length comment))
  (define srcloc
    (and
     init-line
     (vector src init-line init-col init-pos width)))
  (define trimmed (string-trim comment))
  (match trimmed
    [(regexp #px"^\\\\?(.*)$" (list _ name))
     (datum->syntax #f (string->symbol name) srcloc)]
    [else
     (raise-syntax-error)]))

(define (port-peek=? port str)
  (equal? str (peek-string (string-length str) 0 port)))

(define (read-toplevel-paren parent-readtable)
  (lambda (match-ch in src init-line init-col init-pos)
    (parameterize ([current-readtable
                    (parameterize ([current-readtable parent-readtable])
                      (make-yosys-readtable))])
      (if (port-peek=? in "declare-datatype ")
          (parameterize ([current-readtable (make-yosys-declare-datatype-readtable)])
            (read-syntax/recursive src in #\())
          (read-syntax/recursive src in #\()))))

(module+ test
  (require rackunit)

  (test-case "basic bitvector"
    (check-equal?
     (yosys-read (open-input-string "#b0101"))
     '(bv 5 4)))

  (test-case "comment unrelated"
    (check-equal?
     (yosys-read (open-input-string "; unrelated"))
     eof))

  (test-case "comment stdt"
    (check-equal?
     (yosys-read (open-input-string "; yosys-smt2-stdt"))
     '(yosys-smt2-stdt)))

  (test-case "comment module"
    (check-equal?
     (yosys-read (open-input-string "; yosys-smt2-module modname"))
     '(yosys-smt2-module modname)))

  (test-case "comment topmod"
    (check-equal?
     (yosys-read (open-input-string "; yosys-smt2-topmod modname"))
     '(yosys-smt2-topmod modname)))

  (test-case "comment clock"
    (check-equal?
     (yosys-read (open-input-string "; yosys-smt2-clock clk posedge"))
     '(yosys-smt2-clock clk 'posedge)))

  (test-case "comment input"
    (check-equal?
     (yosys-read (open-input-string "; yosys-smt2-input cpu.mem_rdata 32"))
     '(yosys-smt2-input cpu.mem_rdata 32)))

  (test-case "comment output"
    (check-equal?
     (yosys-read (open-input-string "; yosys-smt2-output cpu.mem_wdata 32"))
     '(yosys-smt2-output cpu.mem_wdata 32)))

  (test-case "comment register"
    (check-equal?
     (yosys-read (open-input-string "; yosys-smt2-register cpu.instr_ori 1"))
     '(yosys-smt2-register cpu.instr_ori 1)))

  (test-case "comment memory"
    (check-equal?
     (yosys-read (open-input-string "; yosys-smt2-memory ram.ram 6 32 1 1 sync"))
     '(yosys-smt2-memory ram.ram 6 32 1 1 'sync)))

  (test-case "datatype"
    (check-equal?
     (yosys-read (open-input-string "(declare-datatype |mod_s| ((|mod_mk| (|mod_is| Bool) (|mod#0| (_ BitVec 5)) ; \\fancy.name\n)))"))
     '(declare-datatype mod_s ((mod_mk (mod_is Bool) (mod#0 (_ BitVec 5)) fancy.name))))))

(define (yosys-read in)
  (parameterize ([current-readtable (make-yosys-toplevel-readtable)])
    (read in)))

(define (yosys-read-syntax src in)
  (parameterize ([current-readtable (make-yosys-toplevel-readtable)])
    (read-syntax src in)))
