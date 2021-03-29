# `coq-comparse`

`coq-comparse` is your companion toolkit to write parsers with general
purpose combinators in Coq. Because parsers are regular Gallina
functions, if a parser type-checks, it means it
terminates. Incidentally, Coq is able to find the termination proofs
by itself most of the time. As a consequence, `coq-comparse` allows
for writing idiomatic parsers, while benefiting from Coq unique
features.

## Getting Started

```
opam switch create . ocaml-base-compiler.4.12.0 --repositories default,coq-released
```
