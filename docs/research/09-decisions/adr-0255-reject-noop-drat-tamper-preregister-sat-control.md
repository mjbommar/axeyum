# ADR-0255: Reject the no-op DRAT tamper and preregister a SAT control

Status: accepted
Date: 2026-07-19

Result state: ADR-0254 observed and rejected; corrected teeth control
preregistered but not run

## Context

ADR-0254's positive external-consumption route succeeds. From clean detached
Axeyum `ba9ff7c6`, the fixed real query exports a self-rechecked 558-variable,
2,166-clause DIMACS file plus DRAT and LRAT. Pinned upstream `drat-trim` exits
zero and prints `s VERIFIED`.

The preregistered negative control fails its purpose. The CNF is already UNSAT
by unit propagation over seven input clauses, so the DRAT is only the textual
empty clause `0\n`. Deleting that line yields an empty proof, but `drat-trim`
still proves the input UNSAT and prints `s VERIFIED`. The complete ADR-0254 cell
therefore rejects: the positive checker result is real, but the proposed
mutation did not create an invalid proof problem.

## Decision

Preserve ADR-0254 as a rejected teeth experiment with a successful positive
interoperability observation. Do not relabel the verified empty proof as a
failed checker or hide the negative-control mistake.

Preregister one corrected sanity control before running it. Keep the exact
two-byte real proof unchanged, replace only the checker input with the exact
satisfiable DIMACS text:

```text
p cnf 1 0
```

Its SHA-256 is
`946afef7ecdb9105cb716a27cc0fce5d64ad13885ba0fa0108d4873be031790c`.
Run the same pinned checker and require that stdout does not contain
`s VERIFIED`. Also rerun the unchanged positive command and require its prior
`s VERIFIED` result. Preserve exact streams, exit codes, and hashes regardless
of outcome.

This control is deliberately a checker sanity/binding test, not a claim that a
single-byte mutation of the source query was rejected. It is selected after
observing why the original control was semantically inert, and is reported as
such.

## Evidence

The rejected attempt is preserved under
`bench-results/glaurung-external-drat-20260719/`. Exact observed identities are:

- real source SHA-256 `0015f5bd...` and 6,543 bytes;
- exporter binary SHA-256 `6a1e4d36...`;
- DIMACS SHA-256 `40154e42...` and 29,135 bytes;
- DRAT SHA-256 `9a271f2a...` and 2 bytes;
- LRAT SHA-256 `f5eefbff...` and 50 bytes;
- positive checker stdout SHA-256 `25ec40ff...`, containing `s VERIFIED`;
- deleted-final-step stdout SHA-256 `7f7958e2...`, also containing
  `s VERIFIED`.

Access-controlled source and derived proof bytes remain outside Git. The
result record contains normalized diagnostic lines plus exact stream hashes.

## Consequences

The publication record gains an honest negative-control correction without
discarding the failed design. If the v2 sanity control passes, the bounded claim
is one real standard-format proof accepted by an external checker whose binding
behavior is separately exercised on a fixed satisfiable CNF. This remains
interoperability evidence, not proof-coverage, source-lowering, or performance
evidence.
