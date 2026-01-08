This repository contains code associated to the paper *Proving and
Computing the Infinite Pigeonhole Principle and Countable Choice* by
Zena Ariola, Paul Downen and Hugo Herbelin, in *Logics and Type
Theory* (LTT 2026), a colloquium in honor of Stefano Berardi on the
occasion of his 1000000th birthday.

# Executable classical coinductive proofs of the infinite pigeonhole principle

The infinite pigeonhole principle for Boolean values expresses that
from any countable sequence of Boolean values one can extract a
homogeneous countable subsequence.

We represent sequences coinductively, i.e. by streams and reason in
the presence of computational classical logic, that is with `callcc`.

The formalization is done in [Rocq](https://rocq-prover.org), running
the program either in [Racket](https://racket-lang.org) (formerly PLT
Scheme) or in [OCaml](https://ocaml.org) extended with
[Delimcc](https://github.com/zinid/delimcc).

We give two classical proofs and their extracted `callcc`-based programs:

- `IPP_Escardo_proof.v`: A direct-style proof derived from Escardó and
  Oliva's proof in Agda of the double-negated statement of the
  infinite pigeonhole principle; this proof is asymmetric in the role
  of the value `true` and `false`.

- `IPP_Escardo_proof.ml`: The corresponding extracted code in OCaml.

- `IPP_Escardo_proof.scm`: The corresponding extracted code in Racket.

- `IPP_Escardo_program.v`: A direct-style (`callcc`-based) program from
  Escardó and Oliva's proof in Agda of the double-negated statement of
  the infinite pigeonhole principle; the program is manually derived
  but it can be checked that, when extracted to either OCaml (below)
  or Scheme, the Rocq program and the Rocq proof extract both to the
  same programs (see the instruction to extract in OCaml or Scheme at
  the end of the files).

- `IPP_Escardo_program.ml`: The corresponding extracted code in OCaml.

- `IPP_Escardo_program.scm`: The corresponding extracted code in Racket.

- `IPP_proof.v`: A direct-style proof of our own of the infinite
  pigeonhole; this proof is symmetric in the role of the value `true`
  and `false`.

- `IPP_proof.ml`: The corresponding extracted code in OCaml.

- `IPP_proof.scm`: The corresponding extracted code in Racket.

- `IPP_program.v`: The corresponding direct-style (`callcc`-based)
  program; again when extracted to either OCaml (below) or Scheme, the
  Rocq program and the Rocq proof extract both to the same code.

- `IPP_program.ml`: The corresponding extracted code in OCaml.

- `IPP_program.scm`: The corresponding extracted code in Racket.

# Executable classical coinductive proof of the axiom of countable choice

- `ac_coinductive.v`: A direct-style (`callcc`-based) coinductive proof of
  the axiom of countable choice.

# Instructions to re-extract the code

## Extracting the Scheme and OCaml programs

With Coq up to version 8.20
```rocq
coqc IPP_proof.v
coqc IPP_program.v
coqc IPP_Escardo_proof.v
coqc IPP_Escardo_program.v
```

With Rocq, you first need to insert `From Stdlib` in front of each `Require`.

## Running the Scheme programs, e.g. in Racket

For each program, run it using:
```
racket
(load "program_name.scm")
; inspect the tests, e.g.:
test1
```

## Running the OCaml programs

For each program, add this just before the declaration `type 'a cont = 'a -> empty_set`:
```ocaml
open Delimcc
let p = (new_prompt () : _ prompt)
```

For each program, run it using:
```
ocaml -I path-to-delimcc-install-dir delimcc.cma
#use"program_name.ml";;
```

