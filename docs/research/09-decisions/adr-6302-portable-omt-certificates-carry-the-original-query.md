# ADR-6302: Portable OMT certificates carry the original query

Status: accepted; audited OMT contract adopted, final integration gates remain open
Date: 2026-10-11

## Decision

Version 1 carries the exact source script, mode, selected objective index and
all required earlier lexicographic rows. Each row binds its objective direction
and exact integer value, named model assignments, and Farkas atoms, origins,
multipliers and named variable columns with explicit user/internal namespace tags.
The checker resolves each column in its declared namespace; helper names never
fall back to user symbols. Box certificates carry only the selected
row. Export requires the existing model-plus-refutation checks; missing evidence
is an explicit decline. Parsing data never establishes acceptance.

The byte checker must compare a caller-supplied original subject, reconstruct
active objectives and scoped assertions, rebuild earlier pins, check models and
strict-better refutations, and return counted acceptance. It must never invoke
optimization search. Stable names replace ephemeral arena IDs in transport.
Original source, objective direction/order, model, coefficient, origin and column
corruptions must fail; deleting each checker guard must kill one intended test.

Use strict serde envelopes, canonical decimal integer/rational strings, and
explicit byte/node/depth/row/atom/work limits. Source-bearing transport does not
remove the need to verify original Int-to-Real lowering; reuse ADR-6301's binding.
Real-relaxation-infeasible integer results are the first producer. Missing
integer-only cuts, Boolean composition and BV evidence remain explicit until
those producers land; kernel admission remains a separate trust-anchor step.

## Validation

Round-trip exported bytes in Rust/Python and a separate process, with a positive
nonzero checked-obligation count and altered-subject controls. Run affected
solver/workspace/front-door/differential gates, stubs, formatting and lint. Bounds
and canonical carriers are checked before granting any evidence credit.

## Adoption and later composition

The implemented bounded contract is adopted. Later ADR-6301/6302 bind finite
integer optimality evidence to the original query; ADR-7000/7100 carry shared
cooperative deadlines through intake and model replay. Earlier follow-up lists
above record the original increment and are superseded where these later
contracts supply the implementation. See the
[current validation receipts](../../plan/notes/28-wide-real-smtlib-writer.md)
and [completion audit](../../plan/user-feedback-completion-audit-2026-10-11.md).
Current fresh-native OMT suites and full-feature solver regressions cover
feasible/optimal/unknown/unsupported outcomes and changed evidence. A checked
affine recession witness, not search exhaustion, justifies unboundedness.
Gold remains false when strict-better evidence is absent; integer-cut, BV and
other unsupported certificate producers retain explicit declines. Shared
linearization/checking is not advertised as independent implementation or
kernel admission. Final workspace/all-target verification and main integration
remain open.
