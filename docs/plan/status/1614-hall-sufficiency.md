# Lane: hall-sufficiency — the two-dimensional search primitive Hall's sufficiency needs

<!-- plan-section: lane-status -->

**Your lane's block (`WIP`, hall-sufficiency, 2026-09-04).** ADR-1608 stopped
Hall's marriage theorem at *necessity* and named the obstruction: the
sufficiency direction needs the **critical subfamily** `t ⊆ s` with
`card t = card (unionOver nb t)`, and with no classical choice it must be
COMPUTED — a bounded search over the `2^(bound s)` subsets of a `Nat.Finset`
with a reflection lemma reading the verdict back into the kernel.
`Nat.Finset.allBelow_false_witness` is the one-dimensional model (search over
indices); the two-dimensional version (search over *subsets*) does not exist.
This lane builds it, plus the `Nat.strongInduction` wrapper ADR-1608 measured
absent, and then attempts sufficiency.

<!-- plan-section: landed-changes -->

| 2026-09-04 | hall-sufficiency | lane opened: subset-search primitive + strong induction toward Hall sufficiency |
