# ADR-0225: Exhaustive neutral QF_BV fuzz coverage

Status: accepted
Date: 2026-07-17

## Context

ADR-0224 establishes the first standing Axeyum/Z3/cvc5 QF_BV fuzz gate, but
routine cost limits cvc5 to a deterministic 1-in-16 sample and the operator
coverage claim is documented rather than asserted. That is a useful CI gate,
not yet the strongest publication response to the request for systematic
multi-oracle differential evidence.

## Decision

Keep the default cvc5 stride at 16, but allow a positive
`AXEYUM_CVC5_SAMPLE_STRIDE` override. A publication run sets the stride to one,
requires a working cvc5 binary, and requires every submitted neutral row to
decide. Continue to fail closed on cvc5 process, parser, status, or output
failure and to replay every Axeyum SAT model on the original IR.

Add an executable coverage inventory to the deterministic generator. The test
must hit all declared widths and every required variable/constant, Boolean,
comparison, bit-vector arithmetic, division/remainder, bitwise, shift, concat,
extract, and extension class. A missing class fails the gate rather than
surviving as a prose coverage claim.

## Evidence

At Axeyum `cf37d269`, all 4,000 fixed-seed instances decide in Axeyum, direct
Z3, and cvc5 1.3.4 and all 4,000 agree. The run records:

- 1,487 Axeyum SAT models replayed on every original assertion;
- zero Unknown, timeout, crash, replay gap, cvc5 process/parser failure, or
  disagreement;
- all widths 1/4/8/16/32 and all 35 required generator classes covered;
- the separate strict/named Glaurung control tests still passing.

The complete required-neutral run takes 92.39 seconds on the recorded host.
Exact provenance, limits, coverage inventory, and counters are committed under
[`bench-results/qfbv-multi-oracle-fuzz-full-cvc5-20260717/`](../../../bench-results/qfbv-multi-oracle-fuzz-full-cvc5-20260717/README.md).

## Consequences

The paper may state that the accepted generated QF_BV round has complete
three-way verdict coverage over its 4,000 deterministic formulas and an
executable operator/width inventory. It may not generalize that bounded result
to proof of correctness, to malformed consumer states, to widths generated
only by named controls, or to end-to-end finding parity.

Routine CI retains the cheaper 250-row neutral sample. Further correctness work
should add independent seed rounds, shape-frequency/edge-case accounting,
another neutral implementation, and a measured proof-coverage denominator;
repeating the same seeds is not additional coverage.

## Alternatives

- Make all 4,000 cvc5 processes the default test: rejected because it roughly
  doubles this already-heavy integration test's routine wall time.
- Report inferred operator coverage: rejected because deterministic generator
  drift could silently remove a class.
- Count cvc5 Unknown as agreement: rejected; it remains a named nondecision and
  the accepted publication run requires none.
