# Knox [![Build Status](https://github.com/anishathalye/knox/workflows/CI/badge.svg)](https://github.com/anishathalye/knox/actions?query=workflow%3ACI)

> Knox is a new framework that enables developers to build hardware security
> modules (HSMs) with high assurance through formal verification. The goal is
> to rule out all hardware bugs, software bugs, and timing side channels.

<p align="center">
<img src="https://raw.githubusercontent.com/anishathalye/assets/master/knox/workflow.png" width="511" alt="Knox workflow">
</p>

> Knox's approach is to relate an implementation's wire-level behavior to a
> functional specification stated in terms of method calls and return values
> with a new definition called *information-preserving refinement (IPR)*. This
> definition captures the notion that the HSM implements its functional
> specification, and that it leaks no additional information through its
> wire-level behavior. The Knox framework provides support for writing
> specifications, importing HSM implementations written in Verilog and C code,
> and proving IPR using a combination of lightweight annotations and
> interactive proofs.
>
> To evaluate the IPR definition and the Knox framework, we verified three
> simple HSMs, including an RFC 6238-compliant TOTP token. The TOTP token is
> written in 2950 lines of Verilog and 360 lines of C and assembly. Its
> behavior is captured in a succinct specification: aside from the definition
> of the TOTP algorithm, the spec is only 10 lines of code. In all three case
> studies, verification covers entire hardware and software stacks and rules
> out hardware/software bugs and timing side channels.

For more details on Knox and the underlying theory, see our [OSDI'22 paper][paper].

## Organization

This repository contains the framework code. **For examples of Knox HSMs, see
the [knox-hsm](https://github.com/anishathalye/knox-hsm) repository. It
contains fully-worked examples, including a number of small explanatory
examples along with the three HSMs from the paper.**

### rosutil

This collection contains utility code built on top of [Rosette]. Be careful if
using this outside the context of Knox: some of the code in here assumes
certain preconditions (e.g. immutable arguments) that Knox obeys, but these
preconditions may not be apparent from the code.

### yosys

Lifts [Yosys] SMT2 STDT output into a symbolically-executable representation in
Rosette.

### knox

Note: for brevity, the Knox framework internally uses the names "correctness"
and "security" for functional equivalence and physical equivalence (the latter
are the terms used in the paper). "Correctness" does correspond to functional
correctness; note that "security" proofs are not meaningful on their own unless
accompanied by a functional correctness proof.

Here are some files/directories of interest, and their overall purpose:

- `circuit.rkt`: defines a wrapper for circuits; this lets users specify some
  additional metadata on top of the Yosys output (e.g. annotating which state
  is persistent)
- `circuit/`: defines `#lang knox/circuit`
- `spec.rkt`: defines specifications
- `spec/`: defines `#lang knox/spec`
- `semantics/`: contains common code used to define the semantics of the driver and emulator languages
- `driver.rkt`: defines drivers
- `driver/driver-lang.rkt`: defines `#lang knox/driver`, the DSL for writing drivers
- `driver/interpreter.rkt`: defines the semantics of the driver language as a small-step interpreter written in Rosette
- `emulator.rkt`: defines emulators
- `emulator/emulator-lang.rkt`: defines `#lang knox/emulator`, the DSL for writing emulators
- `emulator/interpreter.rkt`: defines the semantics of the emulator language as a big-step interpreter written in Rosette
- `correctness/`: defines `#lang knox/correctness` and contains tools for verifying correctness
- `security/`: defines `#lang knox/security` and contains tools for verifying security

[Rosette]: https://emina.github.io/rosette/
[Yosys]: https://github.com/YosysHQ/yosys
[paper]: https://pdos.csail.mit.edu/papers/knox:osdi22.pdf

## Citation

```
@inproceedings{knox:osdi22,
    author =    {Anish Athalye and M. Frans Kaashoek and Nickolai Zeldovich},
    title =     {Verifying Hardware Security Modules with Information-Preserving Refinement},
    month =     {jul},
    year =      {2022},
    booktitle = {Proceedings of the 16th USENIX Symposium on Operating Systems Design and Implementation~(OSDI)},
    address =   {Carlsbad, CA},
}
```
