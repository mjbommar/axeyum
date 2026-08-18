# Notes: 56-r3-telescope

Detail moved out of [`../status/56-r3-telescope.md`](../status/56-r3-telescope.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

**The round trip is checked in two places because one of them is nearly
vacuous.** `specialize_setoid_to_eq` re-opens the `Eq`-shaped statement's own 30
binders and applies the 39-binder theorem inside them, filling the slot with
`Eq R` (a *partial application*, never `fun a b => Eq R a b`) and five generic
`Eq`-is-a-setoid lemmas proved from `Eq.rec`. Comparing the inferred conclusion
is weak — the 30 binder types are copied from the reference, so only the
variables/constraints tail is really compared. The load-bearing half is the
**binder-type** comparison: walk both telescopes in step and require the 30
non-slot domains to be the same interned expressions. Verified by mutation:
supplying an η-expanded `fun a b => Eq R a b` leaves the conclusion identical,
admits, stays axiom-free — and drops the binder count to **21 of 30**, the nine
mismatches being exactly the nine `Eq`-stated laws, which independently
re-derives ADR-0468's Measurement 2.

**A third guard exists because the other two cannot see the failure that
matters.** `Eq`, `Eq.refl` and `Eq.rec` are an inductive, a constructor and a
recursor — **not axioms**. A proof step that quietly kept using `Eq.rec` still
generalizes to an axiom-free theorem with 39 binders that still specializes back
at `Eq`; every number reads as success while the theorem has become
uninstantiable at a carrier whose equality is a defined relation, which is the
entire purpose. `residual_eq_constants` scans the proof term for those three and
the example's exit status depends on it, with the `Eq`-mode proof of the same
query as the in-test positive control.

**Three mutations, three kills, no survivors.** Deleting one helper's slot
branch (`add_comm_eq`) → the kernel refuses the setoid proof outright
(`TypeMismatch`). Supplying `congr₂ R mul` where `add_congr` belongs → the
specialization does not infer. η-expanding the equality argument → 9 binder-type
mismatches and **exactly one** unit test dies.

**Next.** R4 is the instantiation: supply `CReal` to this telescope with an
`arith_model`-shaped witness module and a `creal_model_witness` example whose
exit status depends on all 22 witnesses having empty footprints. R3's telescope
is the thing it plugs into, and the 9 laws it must supply in `Equiv` form are
exactly the 9 the binder-type mutation just isolated. Not blocked on anything in
this lane.
