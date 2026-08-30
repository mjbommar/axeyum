# 362 — IVT/EVT ledger hygiene

<!-- plan-section: lane-status -->

**Status: DONE.** Follow-up to lane 359's audit
(`docs/formalized-math-2026-08/08-ivt-and-evt-measured-against-mathlib.md`,
ADR-0675), which found three ledger-quality problems and deliberately left
them unfixed. This lane fixed them.

## 1. Nine (measured: ten) generated-unreviewed CReal IVT/EVT facts, curated

The audit and its own brief both said "9 of 11". Recounted directly from
`provenance.curation`: **10 of the 11 CReal IVT/EVT facts were
`generated-unreviewed`**, not 9 — the audit's "9 constructive + 2 row-2" split
is right, but only one of the two row-2 facts
(`F:creal-ivt-exact-root-decides-sign`) was curated; the other
(`F:creal-evt-attained-max-decides-sign`) was still generated-unreviewed too.
All ten are now curated, reading from the rendered kernel type plus the module
documentation in `creal/ivt.rs`, `creal/ivt_boundary.rs`, `creal/extreme_value.rs`
and the field docs in `creal.rs`:

| fact | before | after (one line) |
| --- | --- | --- |
| `F:creal-ivt-approx` | boilerplate, no characterisation | ADR-0603 row 1, the real general form: arbitrary `F`/`a`/`b`, `∀n` accuracy — but fixed target 0, fixed orientation, uniform (not pointwise) continuity |
| `F:creal-ivt-step` | boilerplate | one bisection step; weak epsilon-slack invariant, never decides an exact sign |
| `F:creal-ivt-iter` | boilerplate | `n`-fold bisection, width shrinks geometrically; still pure machinery |
| `F:creal-ivt-bisect-invariant` | boilerplate | the computable (data) bracket satisfies the same 6-part invariant as the existential one — what makes a sequence possible at all |
| `F:creal-ivt-bisect-approx` | boilerplate | `ivt_approx`'s bound restated at a named point instead of an existential witness |
| `F:creal-ivt-bisect-cauchy-bound` | boilerplate | real-valued Cauchy estimate between two accuracies, needs the stronger derivative hypothesis |
| `F:creal-ivt-bisect-cauchy` | boilerplate | the named-point sequence is a genuine `CReal.Cauchy` sequence |
| `F:creal-ivt-exact-root` | boilerplate | EXACT root, priced at a uniformly positive derivative on the whole interval — strictly stronger than Mathlib's `ContinuousOn`, and row 2 shows nothing weaker will do |
| `F:creal-ivt-exact-root-at` | boilerplate | same exact-root theorem generalized to an arbitrary target `y`, same strong hypothesis |
| `F:creal-evt-attained-max-decides-sign` | boilerplate | EVT's row 2: an attained maximiser for a linear family decides the sign of an arbitrary real — and, stated explicitly for the first time in this fact, EVT has **no** positive constructive form behind it anywhere in the ledger (unlike IVT) |

Detail moved to [`../notes/362-ivt-evt-ledger-hygiene.md`](../notes/362-ivt-evt-ledger-hygiene.md).

