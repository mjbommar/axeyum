# Checked quantified-UF default repair

Status: implementation complete; final branch-wide acceptance pending
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

ADR acceptance remains withheld until solver/workspace tests, strict rustdoc,
foundational resources, parity, links, SMT-COMP recovery, and the QF_BV profile
complete on the containing branch.
