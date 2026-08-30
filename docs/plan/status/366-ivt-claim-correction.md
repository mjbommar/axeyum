# Lane 366 — `ivt-claim-correction`

<!-- plan-section: lane-status -->

## Status

**Done.** Adjudicated the adversarial audit's charge
([`2026-08-30-session-audit.md`](../../research/11-design-review/2026-08-30-session-audit.md)
§Part 1 item 3) that
[`08-ivt-and-evt-measured-against-mathlib.md`](../../formalized-math-2026-08/08-ivt-and-evt-measured-against-mathlib.md)
graded IVT and EVT on inconsistent criteria.

**The charge holds against the presentation, not against the verdict.** No
test was written down before §4's axis tables were built, so the "Net" lines
read as an unweighted vote over an ad hoc axis list — three Mathlib-wins
excused for IVT, one comparable Mathlib-win sinking EVT, with no stated rule
for the difference. But `07-the-cost-model-and-pareto-position.md` §1
already states the real test, narrower than the seven-axis table: dominance
is decided by exactly two axes — **trusted base** (axiom footprint) and
**computational content** (constructive-with-a-program vs
classical-existence) — on a statement we ship that is comparable to
Mathlib's; breadth (generality of statement, of structure, which continuity
notion is assumed) is **explicitly conceded**, per that same section, never
scored toward or against the verdict. That test was simply never carried
into the comparison document.

Applied uniformly:

Detail moved to [`../notes/366-ivt-claim-correction.md`](../notes/366-ivt-claim-correction.md).

