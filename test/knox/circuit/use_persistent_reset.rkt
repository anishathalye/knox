#lang knox/circuit

#:circuit "../../yosys/verilog/use_persistent_reset.rkt"
#:reset nrst #f
#:persistent [count_persistent]
#:init-zeroed [count_persistent]
