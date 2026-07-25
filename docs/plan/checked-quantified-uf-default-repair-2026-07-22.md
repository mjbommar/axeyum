# Checked quantified-UF default repair

Status: complete; ADR-0359 accepted
Date: 2026-07-22
Decision: [ADR-0359](../research/09-decisions/adr-0359-preregister-checked-quantified-uf-default-repair.md)
Implementation: `79a8dd21`

## Bounded result

Axeyum can now repair only the total defaults of up to eight relevant
`Int`/`Real`-result uninterpreted functions for an already admitted
ADR-0357/0358 universal shape. Existing scalar assignments, signatures, and
explicit table entries are immutable. Missing interpretations may be completed
as constant total functions. Candidate values come deterministically from zero,
same-sort scalar assignments, UF defaults and entry results, and checked
predecessor/successor neighbors. Each pool is capped at 32 values and the full
Cartesian search at 256 candidates.

The search is not evidence. A candidate returns SAT only after the independent
finite-profile checker accepts every exact source universal and canonical
original-query model replay succeeds. Failure, unsupported result sorts,
malformed function storage, pool/product/function cap excess, and neighbor
overflow all decline without changing the UNSAT route.

## Measured effect

The preregistered 256-case direct-Z3 differential improved from 111 to 178
checked SAT results while retaining zero disagreements and replaying every SAT
model. Jointly decided cases increased from 131 to 197. Among Axeyum Unknowns,
the ordinary-incomplete/Z3-SAT class fell from 96 to 39 and the MBQI-resource/
Z3-SAT class from nine to zero.

The remaining 54 Unknowns contain 39 Z3-SAT, 11 Z3-UNSAT, and four Z3-Unknown
cases. They are separate work: default-only repair neither completes missing
free scalar assignments nor modifies explicit table points, and it does not
claim a complete quantifier procedure.

## Focused evidence

- 21 MBQI integration cases pass, including two missing functions, strict
  integer/real defaults, explicit-point preservation, and multi-binder replay.
- Four internal boundary tests cover the function, pool, and Cartesian caps,
  unsupported result sorts, and overflow-safe neighbor generation.
- The 256-case differential records 197/197 joint agreements, 178/178 SAT
  replays, and zero Axeyum errors.
- Solver all-target/all-feature Clippy is warning-free.

## Final gates

The containing branch passed:

- 898 solver library tests, 69 evidence tests, 15 instantiation tests, and 21
  MBQI integration tests;
- the 256-case direct-Z3 repair differential in 77.16 seconds and the broader
  UFLIA differential in 420.71 seconds, both with zero disagreements;
- workspace tests and doctests with the two separately registered CAS moment-
  family stress tests excluded from this solver acceptance run;
- workspace all-target/all-feature Clippy with warnings denied and strict
  workspace rustdoc;
- 137 foundational concept rows and 174 example packs;
- parity documentation with 680 compared decisions and zero disagreements,
  links, and whitespace;
- the QF_BV profile; and
- 52 SMT-COMP recovery tests with one environment-dependent skip, plus the
  scoring, selection-authority, and resume-contract gates.

Workspace tests rewrote five timing-sensitive frontier JSON files. Inspection
showed only fresh timing/frontier sampling from the test run; those generated
measurements were restored to the committed baseline and are not part of this
functionality result. ADR-0359 is accepted for only the bounded default-repair
surface described above.

## 2026-07-25 guarded declared-sort extension

The accepted search/check boundary now also covers a unary `Int -> U` function
guarding a top-level implication. A candidate constant default distinct from the
guard's binder-free carrier value proves the antecedent false for every binder;
the checker requires an empty override table and re-evaluates the exact source
guard. Independent ground theory components may seed the candidate only when
their merged model replays the complete ground conjunction. This moves the
public Z3-SAT `TwoSquares/smtlib.598292.smt2` row from `unknown` to certified
`sat` in 0.01 seconds. A forced `f(0) = c` mutation returns `unsat`; the fresh
1,412-file UFLIA measurement reports one SAT and zero wrong verdicts.
