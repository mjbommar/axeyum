# Notes: 62-creal-reconstruct

Detail moved out of [`../status/62-creal-reconstruct.md`](../status/62-creal-reconstruct.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

on all five fixtures (`baby-farkas`, `farkas-sum`, `farkas-three`,
`strict-cycle`, `sos-square`), with 39 ring binders, an empty generalized
footprint, and zero kernel-`Eq` constants left in the proof term. The remaining
2–7 are the query's own variable and hypothesis axioms and nothing else. "Carrier
axioms" is the intersection of the measured `Kernel::axiom_footprint` with the
telescope the generalization actually abstracted, so it cannot drift with a
naming convention, and the non-empty `Real` column in the same output is the
control that keeps the zero from being vacuous.

**The `Real` package is this repository's entire remaining trusted surface
(`real: axiom=30`), and this is the first route that produces a kernel-checked
`False` about the reals without it.** What it does *not* yet do is retire the
package: `LraReconstructCtx::new` still builds `Real`, and every shipped
front-door LRA/SOS route goes through it. Making `CReal` the default carrier is
the next slice, and its cost is `build_creal_prelude` — ~40 s in a debug build,
against ~1 s for `build_arith_prelude`, which is why both the example and the
test fixture clone a process-wide template rather than rebuilding it.

**Five guards, five mutation kills, one test each.** The adoption seam refuses a
signature whose equality is the kernel's `Eq` (nothing to adopt), a slot naming a
relation the ring laws are not stated over, an undeclared member, a member of the
wrong *shape* (swapping `le_congr` and `lt_congr` leaves both present, declared
and true — a name-only check waves it through), and a second slot in a context
that already has one. Every member's declared type is `def_eq`-compared against a
statement built by the **same** builder `declare_setoid_equality` axiomatizes, so
the declared slot and the adopted one cannot drift apart.
