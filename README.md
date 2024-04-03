# Termination property for System F
This repository contains a Coq mechanization of the termination proof described in <https://www.cs.cmu.edu/~rwh/courses/chtt/pdfs/girard.pdf>. It is intended as a minimal example that leverages impredicativity of Coq's `Prop` to carry out a logical relational proof.

Some differences from the notes:
- Instead of boolean, the unit type is used as the base type for stating the termination property.
- Binders are represented using well-scoped DeBruijn representation through [Autosubst 2](https://github.com/uds-psl/autosubst2).
- Renaming and substitution properties for both syntactic and semantic typing are formulated in the general form of simultaneous substitution/renaming.
- The definition of a candidate (`candidate`) is independent of the choice of types or the type assignment ($\delta$). The type assignment is only used to close over an open term to define semantic typing.

I also added a proof irrelevant model in [proofirrel.v](proofirrel.v),
where types are interpreted as Coq propositions rather than sets of
terms encoded as Coq predicates. With the current minimal set up of
the system, the proof irrelevant model is not very useful. However, it
allows you to treat System F purely as a logic and add axioms such as
law-of-excluded middle, which would then break the proof relevant
model because you can get stuck from the usages of the axiom.


## Dependencies
To build the project, you need to have the following opam packages installed:
- `coq-mathcomp-ssreflect` 1.17.0
- `coq` 8.16.1
- `coq-hammer-tactics` 1.3.2+8.16

Additionally, you need to have [Autosubst 2](https://github.com/uds-psl/autosubst2) installed and the executable `as2-exe` available in your `PATH` environment variable.

## Build the project
Run the following command:
```sh
make
```
Optionally, run `make -j[n]` where `[n]` is replaced by the number of jobs you want `make` to run in parallel. Shouldn't make a big difference because all of the proofs are in the file [typing.v](typing.v).
