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

Detail moved to [`../notes/62-creal-reconstruct.md`](../notes/62-creal-reconstruct.md).

<!-- plan-section: landed-changes -->

| 2026-08-18 | (pending) | **ADR-0468 phase R4 reaches reconstruction: `LraReconstructCtx::adopt_setoid_equality` fills the ring interface's equality slot from `CRealPrelude`'s own theorems, and a Farkas/SOS refutation over the CONSTRUCTED reals rests on zero carrier axioms.** Measured on all five `ordered_ring_refutation` fixtures: 30 carrier axioms over `Real` against **0** over `CReal`, and the slot costs **0** declarations against 18 for the `Real` route — both read out of `Environment::len` and `Kernel::axiom_footprint`, with the `Real` column as the in-output control. Four adoption guards plus the ctx's one-slot rule, each killed by exactly one test under mutation. The nine slot-member types come from one builder shared with `declare_setoid_equality`, so an interface change cannot move only one of them. `--require-empty` output is byte-identical to before. |
