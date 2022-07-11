#lang s-exp syntax/module-reader
yosys/verilog
#:read yosys:read
#:read-syntax yosys:read-syntax

(require (prefix-in yosys: "../reader.rkt"))
