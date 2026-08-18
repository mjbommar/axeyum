# Lane: agent-creal-reconstruct — Farkas refutations over the CONSTRUCTED reals

<!-- plan-section: lane-status -->

**ADR-0468 phase R4 reaches the reconstruction route: a Farkas/SOS refutation
now reconstructs over `CReal`, and the closed `False` rests on ZERO carrier
axioms (`WIP`, agent-creal-reconstruct, 2026-08-18).** R3 made equality a
parameter of the ring telescope; R4 modelled the `Real` package by `CReal`. The
gap between them was the *proof-term* route: the only way to fill the equality
slot was `enable_setoid_equality`, which **declares eighteen axioms** — nine
slot members plus the nine `Eq`-stated laws restated through them — because the
`Real` package cannot prove any of it. `LraReconstructCtx::adopt_setoid_equality`
is the other half: it takes the nine members from `CRealPrelude`, which proves
every one of them footprint-free, and reads the nine ring laws off the
signature, which under `RingEquality::Defined` already states them over
`CReal.Equiv`.

**Measured, `cargo run -q -p axeyum-solver --features full --example
ordered_ring_refutation -- --require-empty --constructed-reals`:**

| | equality slot | closed `False` footprint | of which CARRIER axioms |
|---|---|---|---|
| over `Real` | **18 axioms declared** | 32–37 | **30** |
| over `CReal` | **0 declarations added** | 2–7 | **0** |

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

<!-- plan-section: landed-changes -->

| 2026-08-18 | (pending) | **ADR-0468 phase R4 reaches reconstruction: `LraReconstructCtx::adopt_setoid_equality` fills the ring interface's equality slot from `CRealPrelude`'s own theorems, and a Farkas/SOS refutation over the CONSTRUCTED reals rests on zero carrier axioms.** Measured on all five `ordered_ring_refutation` fixtures: 30 carrier axioms over `Real` against **0** over `CReal`, and the slot costs **0** declarations against 18 for the `Real` route — both read out of `Environment::len` and `Kernel::axiom_footprint`, with the `Real` column as the in-output control. Four adoption guards plus the ctx's one-slot rule, each killed by exactly one test under mutation. The nine slot-member types come from one builder shared with `declare_setoid_equality`, so an interface change cannot move only one of them. `--require-empty` output is byte-identical to before. |
