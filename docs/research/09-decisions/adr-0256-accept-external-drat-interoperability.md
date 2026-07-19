# ADR-0256: Accept bounded external DRAT interoperability

Status: accepted
Date: 2026-07-19

## Context

ADR-0254's fixed real-query positive result succeeded, but its final-line
deletion control did not. The selected 558-variable, 2,166-clause CNF is
already UNSAT by input unit propagation, so Axeyum's complete DRAT text is only
the empty-clause line `0\n`; pinned upstream `drat-trim` verifies the CNF even
when that line is removed. ADR-0255 retained this rejected control and fixed a
separate checker sanity test before observing it.

The corrected test keeps the exact real proof unchanged and supplies the fixed
satisfiable DIMACS input `p cnf 1 0\n`. The input has SHA-256
`946afef7ecdb9105cb716a27cc0fce5d64ad13885ba0fa0108d4873be031790c`.

## Decision

Accept one bounded external-interoperability result and its separate checker
sanity/binding control:

- the unchanged real DIMACS/DRAT pair makes the pinned `drat-trim` binary exit
  0 and print `s VERIFIED`;
- the exact same two-byte proof against the preregistered satisfiable CNF makes
  the checker exit 1, report `no conflict`, and print `s NOT VERIFIED`.

Keep ADR-0254's rejected final-line mutation in the evidence trail. Describe
the accepted real proof as a trivial empty-clause proof over an input-unit-
refutable CNF, not as a nontrivial learned-clause trace.

## Evidence

The committed result is under
`bench-results/glaurung-external-drat-20260719/accepted-v2-satisfiable-cnf-control/`.
Its exact identities include:

- real source SHA-256 `0015f5bd...`;
- real DIMACS SHA-256 `40154e42...`;
- real DRAT SHA-256 `9a271f2a...`, 2 bytes;
- pinned checker binary SHA-256 `c0b9bd6a...`;
- accepted positive stdout SHA-256 `c3d94242...`, with exit 0 and
  `s VERIFIED`;
- rejected satisfiable-control stdout SHA-256 `c1924d7b...`, with exit 1 and
  `s NOT VERIFIED`;
- result-record SHA-256 `a81a6947...`.

The source query and derived CNF/proof bytes remain access-controlled and are
not committed. The result record preserves normalized streams, exact hashes,
sizes, and exit codes.

## Consequences

Axeyum now has one concrete standard DIMACS/DRAT export consumed by an
independent checker, with the checker's binding behavior exercised separately.
This closes the narrow external-consumer checkbox for that real cell.

It does not establish proof coverage, validate source-to-CNF lowering, exercise
a long learned-clause trace, or provide performance evidence. A nontrivial
external-proof claim requires a separately preregistered deterministic
selection protocol that retains every attempted row and requires the input
alone to fail verification.
