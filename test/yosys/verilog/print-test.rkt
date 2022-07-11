#lang yosys

; a hand-written test case

; yosys-smt2-module print_test

(declare-datatype |print_test_s| ((|print_test_mk|
  (|counter_is| Bool)
  (|counter#0| Bool) ; \clk
  (|counter#1| (_ BitVec 8)) ; \count
  (|counter#4| (Array (_ BitVec 2) (_ BitVec 32))) ; \ram
)))

(define-fun |print_test_i| ((state |print_test_s|)) Bool true)

(define-fun |print_test_t| ((state |print_test_s|) (next_state |print_test_s|)) Bool true)
