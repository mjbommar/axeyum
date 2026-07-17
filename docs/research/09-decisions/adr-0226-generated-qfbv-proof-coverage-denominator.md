# ADR-0226: Generated QF_BV proof-coverage denominator

Status: accepted
Date: 2026-07-17

## Context

The publication review asks how often QF_BV UNSAT results receive only a CNF
DRAT proof versus the stronger end-to-end certificate that also checks
term-to-bitblast faithfulness. Capability tables establish that both routes
exist, but existence is not a coverage denominator. ADR-0225 supplies a fixed
4,000-formula population with 2,513 jointly-UNSAT rows.

Running the end-to-end route over an undeclared or unbounded subset would make
the resulting percentage uninterpretable. The current certificate API also has
no cooperative per-instance deadline, so a complete sweep can block inside one
faithfulness miter.

## Decision

Add an opt-in proof sample to the standing generator. Select a formula only
after Axeyum and direct Z3 agree UNSAT, and only when its instance width is at
most 8 and its seed is divisible by the positive configured stride. For every
selected row:

1. export the CNF DRAT proof and independently recheck it;
2. request the end-to-end faithfulness-plus-DRAT certificate and independently
   recheck both stored proof components;
3. count proved, inconclusive/not-certified, and selected totals separately.

Accept stride four as the first denominator. Do not widen to the complete
width-at-most-8 cohort until the proof route has cooperative deadlines or the
harness isolates each proof in a killable process. A process timeout is an
unmeasured row, not a failed certificate and not an UNSAT result.

## Evidence

At Axeyum `7866b921`, the 4,000-formula population contains 1,487 SAT and 2,513
UNSAT rows. The declared stride-four/width-at-most-8 subset contains 169 UNSAT
formulas (6.725030% of all generated UNSAT):

- CNF DRAT: 169 attempted, 169 proved, 169 rechecked, 0 inconclusive;
- end to end: 169 attempted, 169 certified, 169 rechecked, 0 not-certified;
- 2,344 UNSAT rows remain unmeasured by this denominator.

A wider diagnostic isolates seed 83. Its CNF DRAT proof completes and rechecks,
but the end-to-end faithfulness route does not complete within a 15-second
process timeout. The exact formula and full counters are committed under
[`bench-results/qfbv-proof-coverage-20260717/`](../../../bench-results/qfbv-proof-coverage-20260717/README.md).

## Consequences

The paper may report 100% CNF and end-to-end proof coverage over the exact
169-row selected denominator, alongside the 6.725030% population fraction. It
must not report 100% coverage of all generated UNSAT or of the 9,526 real
Glaurung checks. The measured result also shows no CNF-only gap inside the
selected subset.

Seed 83 creates a concrete engineering target: deadline-aware or isolated
faithfulness certification. Broader proof coverage remains open until that
resource contract exists and the denominator is expanded explicitly.

## Alternatives

- Divide 169 certificates by only the rows that happened to finish: rejected;
  selection precedes proof execution.
- Count unattempted rows as not-certified: rejected because that conflates
  policy with capability.
- Let the complete sweep run without a bound: rejected as irreproducible and
  unsuitable for a publication artifact.
- Report CNF DRAT alone as end-to-end proof: rejected because it does not close
  the term-to-CNF faithfulness gap.
