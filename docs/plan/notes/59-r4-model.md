# Notes: 59-r4-model

Detail moved out of [`../status/59-r4-model.md`](../status/59-r4-model.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

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
