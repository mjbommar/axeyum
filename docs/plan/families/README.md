# Families and divisions

One file per family, one per division. **This tree is the per-division source
of truth for state, cause, lever and exit criterion.** It does not restate
numbers that live elsewhere: the [ledger](../../../bench-results/PARITY.md) owns
measurements and the [parity plan](../smt-parity-plan-2026-09-05.md) owns the
S1-S12 slice history.

## The families

| Family | Divisions | State |
|---|---|---|
| [SMT, quantifier-free](smt-quantifier-free/README.md) | 10 on the board, 3 targets | the measured work |
| [SMT, quantified](smt-quantified/README.md) | 1 on the board | weakest cause knowledge |
| [The certificate chain](evidence/README.md) | none — no board row by construction | one open hole, one contract without a producer |
| [Propositional SAT](sat/README.md) | not entered | three small slices away |
| [SMT-COMP's other tracks](smt-comp-tracks/README.md) | not entered | model validation is cheap |
| [Hardware model checking](model-checking/README.md) | not entered | best architectural fit |
| [Boolean optimization and counting](boolean-optimization/README.md) | not entered | no formats implemented |

## How to read a division file

Each carries the same seven headings, and two conventions matter:

- **Numbers are stamped copies.** A division file names the solver commit its
  row came from. Re-read the ledger; do not quote the file.
- **"Cause established?" is a real question with a real "no".** Three divisions
  have no established cause (QF_UF's remaining four, UF's thirty-two, QF_RDL's
  fourteen since the last re-census) and two of those had a cause that was
  *refuted*. A division without a cause gets a census, not a slice.

## The rule this tree exists to enforce

A slice needs a scoring population and an exit criterion before it is
dispatched. Every file here has both fields, and an empty one is the signal
that the work is a census rather than a fix.

## Where the wider landscape lives

Roughly 77 further SMT-LIB logics and every arena outside SMT are catalogued,
with sources and provenance tags, in
[the competition landscape survey](../../research/02-ecosystems/competition-landscape-2026-09/README.md).
