# Lane: agent-r4-model — the constructed reals as a model of the `Real` package

<!-- plan-section: lane-status -->

**ADR-0468 phase R4 has landed: the `Real` axiom package is modelled by the
CONSTRUCTED reals, and ADR-0456's "`Int` is not ℝ" caveat is discharged
(`WIP`, agent-r4-model, 2026-08-18).** `build_creal_model_of_arith` admits one
theorem per law,

```text
Real.CRealModel.<law> : ⟦ type of Real.<law> ⟧ := CReal.<law>
```

with `⟦·⟧` **computed from the axiom as it stands in the environment** —
`arith_model`'s discipline — so an axiom whose statement changes changes the
obligation and an axiom `CReal` does not satisfy makes the build fail rather
than dropping a row. `cargo run -q -p axeyum-lean-kernel --example
creal_model_witness`: **22/22 witnesses footprint-empty, 22/22 syntactically
the `CReal` law up to binder names, 9/22 restated over `CReal.Equiv`, 7/7
discrimination witnesses**, exit 0.

**The interpretation is not a constant renaming, and that is the whole content
of R4.** `Eq` is polymorphic and `CReal.Equiv` is not, so no map from `Eq`
alone is type-correct; what gets replaced is the *partial application*
`Eq Real`, which is exactly R3's `rewrite_eq_at_real` applied to the axioms
instead of to the telescope. The rewrite is **self-guarding**: fail to fire and
the obligation still reads `Eq CReal …` while the proof proves
`CReal.Equiv …`, so the kernel refuses it. Verified — disabling the match makes
`build_creal_model_of_arith` return `DeclarationValueMismatch` and the example
exit 101.

**9 of 22 is now measured three independent ways.** ADR-0468 Measurement 2
counted `Eq` in the axiom types; R3's η-expansion mutation isolated the same
nine as binder-type mismatches; this model reports `restated_over_equiv` from
whether the rewrite fired, and the nine names agree exactly.

**Four mutations, four kills.** Disabling the `Eq Real` rewrite → the kernel
refuses the model. Dropping one law → the coverage check fails (population is
read from the environment, not from the table). Pointing one vacuity guard at
an interned-but-**undeclared** name → exit 1, which is the trap that made an
earlier presence test pass with its witness deleted: `axiom_footprint` of an
undeclared name is the empty vector, so presence is asserted first, everywhere.
Falsifying `restated_over_equiv` while leaving the rewrite in place → **exactly
one** unit test dies. That last one also exposed a real defect in the example's
own summary line, which printed `7/7` guards while failing on eight; it now
reports out of the list length.

**A fifth mutation found a guard that is not load-bearing, and it is recorded
as such rather than dressed up.** `the_pairing_is_by_leaf_name` was written on
the theory that zipping two hand-ordered 22-element arrays can drift silently.
It cannot, here: swapping an entry is a `TypeMismatch` at admission, and
duplicating one consistently in *both* lists — the shape a type check
structurally cannot see, since all 22 types still match — is refused as a
repeated declaration name. Both kill all seven tests at
`build_creal_model_of_arith`, none at the assertion. The test is kept, with its
doc corrected to say it is documentation with an exit status; it would still be
the one to fire if two of the 22 law types ever coincided.

**What this does NOT give, stated because it is the temptation.** `Eq CReal` is
not real-number equality — `CReal.Equiv` is — and nine of the 22 obligations say
so in their own statement. Anyone who wants Leibniz equality on reals pays
`Quot.sound`.

**Next.** Not the deletion. `build_arith_prelude` is still load-bearing: every
LRA refutation is stated over the axiomatized `Real`, and `LraReconstructCtx`'s
own doc says "the trusted base is `build_arith_prelude`'s axioms" — including on
the setoid path, whose nine restated laws are computed from the `Real` axioms in
the environment. Retiring the 30 is a separate lane and it needs the consumers
moved onto `CReal` (or onto the R3 telescope with `CReal` supplied), not a
`git rm`.

<!-- plan-section: landed-changes -->

| 2026-08-18 | (pending) | ADR-0468 phase R4: `build_creal_model_of_arith` — the `Real` axiom package modelled by the **constructed** reals. 22/22 witnesses axiom-free, 9/22 restated over `CReal.Equiv`, 7/7 discrimination witnesses, exit status depending on all of it (`creal_model_witness`). Four mutation kills; ADR-0456's "`Int` is not ℝ" caveat discharged. |
