# Lane: agent-r3-telescope — the ordered-ring interface's equality slot

<!-- plan-section: lane-status -->

**ADR-0468 phase R3 has landed: the ring interface takes equality as a
parameter, 30 → 39, and instantiating it back at `Eq` reproduces today's
statement node for node (`WIP`, agent-r3-telescope, 2026-08-18).**
`LraReconstructCtx::enable_setoid_equality` declares nine equality-interface
axioms (`eq`, `eq_refl`/`eq_symm`/`eq_trans`, and `add`/`mul`/`neg`/`le`/`lt`
congruence) plus the nine `Eq`-stated `Real` laws **restated through them** —
whose types are computed from the environment by rewriting the partial
application `Eq Real` to `eq`, never written out, so a changed law changes its
restatement rather than silently disagreeing with it. Every equality step in the
LRA/SOS reconstruction then routes through the slot, and
`RingTelescope::SetoidInterface` binds 39. All five fixtures of
`cargo run -q -p axeyum-solver --features full --example ordered_ring_refutation
-- --require-empty`: **39 binders, footprint 0, zero kernel-`Eq` constants left
in the proof term, 30 of 30 non-slot binder types reproduced exactly.**
`farkas_over_the_integers` (9 tests) is untouched — the `Eq` route is the
default and is unchanged.

**Why the five congruences are exactly five is a measurement, not a taste.**
Every `Eq.rec` in the whole arithmetic reconstruction sits inside one of eleven
helpers, and those eleven collapse onto symmetry, transitivity, `add`- and
`mul`-congruence (each left and right), `neg`-congruence, and the `le`/`lt`
casts (each left and right). One-sided congruence is the two-sided law with
`eq_refl` on the argument that does not move, so the two-sided form is what gets
bound. Nothing else in the LRA or SOS routes touches `Eq` at the carrier.

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

<!-- plan-section: landed-changes -->

| 2026-08-18 | (pending) | ADR-0468 phase R3: the ordered-ring telescope gains an equality slot (30 → 39 binders) and `specialize_setoid_to_eq` proves it specializes back to today's statement — conclusion **and** all 30 non-slot binder types, node for node. Three mutation kills recorded; `residual_eq_constants` guards the one failure the footprint cannot see. |
