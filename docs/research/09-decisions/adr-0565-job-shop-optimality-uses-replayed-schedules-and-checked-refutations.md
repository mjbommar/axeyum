# ADR-0565: Job-shop optimality uses replayed schedules and checked refutations

Status: accepted
Date: 2026-08-26
Index-summary: Certify classical job-shop optima with independently replayed schedules and DRAT-checked bounded-makespan refutations

## Context

The certification lane identified classical job-shop optima whose public tables name a value
but no machine-checkable lower-bound artifact. Axeyum had generic integer and SAT machinery,
but no stable job-shop instance parser, semantic schedule artifact, bounded-makespan encoding,
or model-lifting route. A feasible schedule certifies only an upper bound; a solver status at
the preceding makespan is not a lower-bound certificate.

## Decision

Add a strict parser for the common OR-Library/JSPLIB format and an independent schedule
checker. The checker recomputes every operation end, job precedence, pairwise machine
non-overlap, and makespan. Add a complete time-indexed SAT encoding for makespan at most `H`:

- every operation chooses exactly one integer start through a sequential at-most-one encoding;
- prefix variables encode “started by time t” and enforce job precedence;
- one Boolean order per pair of operations sharing a machine selects either direction, with
  conditional prefix clauses enforcing the corresponding non-overlap.

All sizes have explicit ceilings. SAT assignments gain authority only after lifting to a
portable schedule and independent replay. External competition-format models are treated as
untrusted input and must completely assign and satisfy the generated formula before lifting.
UNSAT gains authority only after a textual DRAT proof is checked against the exact formula by
Axeyum's backward checker.

## Evidence

- A two-job/two-machine optimum-three unit instance has a replayed SAT schedule at three and a
  backward-checked refutation at two; machine-overlap and precedence mutations fail.
- JSPLIB `ft06` at commit `eea2b60...61812eb7` has source SHA-256 `fee21236...721a1c`.
  Axeyum's makespan-55 formula has 3,692 variables / 15,958 clauses; its model lifts to a
  36-operation schedule and replays at exactly 55. A one-start precedence mutation exits 101.
- The makespan-54 formula has 3,620 variables / 15,640 clauses. CaDiCaL 3.0.1 returned UNSAT
  and emitted a 375,015-byte, 11,614-step textual DRAT proof; Axeyum's file-backed backward
  checker accepted it. Together the two artifacts independently reproduce optimum 55.
- The `abz7` makespan-655 formula fits but is much larger: 381,418 variables, 4,343,486
  clauses, and 102,215,416 DIMACS bytes. CaDiCaL reached 300 seconds / 940,152 KiB without a
  proof. Its makespan-656 counterpart likewise timed out without a model. Both verdicts are
  `interrupted`, so optimum 656 is not certified by this increment.

## Consequences

- Axeyum now has a domain-specific end-to-end certificate route for any classical permutation
  job-shop instance in the admitted envelope.
- `ft06 = 55` is a calibration/reproduction. Current Scholar, arXiv, web, and repository
  searches found no prior portable proof artifact, but this negative search is not sufficient
  to advertise the artifact as the first in the field.
- Scaling to `abz7` requires scheduling propagation, symmetry/decomposition, or imported
  branch proofs whose coverage can be independently composed. A timeout cannot establish a
  lower bound.
