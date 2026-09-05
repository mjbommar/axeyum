# Lane: complex-estimates — the ℂ estimates landed, Leibniz with them, and the index arithmetic turned out to be shared

<!-- plan-section: lane-status -->

**The product-rule blocker ADR-1642 named is closed** (`WIP`,
complex-estimates, 2026-09-05, ADR-1646). `Complex.BoundedOn` and
`Complex.UniformlyContinuousOn` did not exist; both now do, in the real
shelf's shape with the interval's two range hypotheses collapsed to one
`Complex.InDisc` and the modulus still carried as `Nat → Nat` DATA. With them
came `Complex.abs_sub_le`, `Complex.abs_mul_le_of_bounds`,
`Complex.bounded_on_unfold`, the two non-vacuity witnesses
(`uniformlyContinuous_const`/`_id`), and
`Complex.uniformlyContinuous_of_hasDerivative`.

**The measured finding is that the index arithmetic is not a ℂ problem at
all.** Every bound in this development is a `CReal` or a `Nat`: the magnitude
bound `(k+1)/1`, the accuracy `1/(e+1)`, the rescaled index `(k+1)·m + k`, the
three-way equal split. Nothing in that arithmetic can observe which carrier
produced the quantity being bounded. So `creal/derivative.rs`'s
`rescale_index`, `mag_bound`, `fold_index0_first`, `fold_index0_second`,
`mul_modulus_components`, `weaken_to_addend` and `fuse_three_equal_bounds` were
made `pub(crate)` and CALLED rather than copied — a seven-line visibility diff
instead of ~350 lines of transcription that would have diverged on the first
correction to either side.

**Two corrections to the brief, both from the real shelf's own record rather
than re-derivation.** ADR-1642 says the product rule needs "a uniform bound on
`|G|`, one on `|F'|`, one on `|F|`" and "a modulus of continuity for `G`".
Both halves are off: the continuity requirement is on **`F`**, and the three
bounds are on `F`, `G` and **`G'`** (`F'` never needs one — it appears only
inside `F`'s own error term, which `HasDerivativeOn.spec` already bounds).
`creal/derivative.rs`'s module documentation records that its own prose carried
the mislabeled version until it was re-verified numerically. Transcribing
ADR-1642's sentence literally would have produced a theorem that still
type-checks with the hypotheses on the wrong functions.

**Leibniz landed.** `Complex.hasDerivative_mul` is kernel-checked and
axiom-free, with the four hypotheses the real one carries. Its
five-hundred-line six-leaf algebraic shuffle — `expand_bound_term` twice,
`expand_term3`, `cancel_middle`, and steps 8a–8f bringing `−F(y)G(x)` and
`+G(x)F(y)` adjacent so they cancel — is ONE `ring_law_proof` call here.

**`Complex.hasDerivative_polyEval` did NOT land, and the obstruction has
moved.** It is no longer the product rule. An induction over the degree applies
`hasDerivative_mul` at every step, and every step needs three fresh
`BoundedOn` facts plus uniform continuity of the accumulator — i.e. closure of
`BoundedOn` and `UniformlyContinuousOn` under `mul` and `add` on a disc, which
is the same wall `CReal.hasDerivative_pow` at general `n` hit. Two of the four
are now landed as well (`Complex.bounded_on_add`, `Complex.bounded_on_mul`),
both short because `Complex.abs_mul_le_of_bounds` does the ℂ half and
`fold_mag_bound_sum`/`fold_mag_bound_product` the `Nat` half. What remains is
`Complex.uniformlyContinuous_mul` — whose real analogue is
`creal/uniform_continuity.rs`'s separate second entry point, a slice on the
order of this lane's own — and the induction, which must also carry
`Complex.pow`'s derivative. Cauchy–Riemann was not reached and is independent
of all of this: it needs `Complex.abs_ofReal`, `abs_re_le`, `abs_im_le`
(the first via `CReal.sqrt_sq`, which exists), and a bridge from
`Complex.HasDerivativeOn` on a disc to `CReal.HasDerivativeOn` on the interval
a segment through the centre traces.

**A negative control of this lane's own was VACUOUS on its first run, and only
the positive half failing exposed it.** The halved-modulus pair left
`F, F', c, r, hf, k, n` free, so `Kernel::add_declaration` returned
`UnboundFVar` for BOTH halves: the control asserted a refusal and got one, for
a reason that had nothing to do with the halving. Had the vacuous half been the
control's twin instead, the pair would have looked green. The repair runs both
under binders. The rule this instance adds to the two known ways a negative
control fails: when a positive/negative pair SHARES a construction, a
construction error refuses both, and the control cannot tell that apart from
success — so a control is only evidence while its positive twin is admitted.

Detail in
[ADR-1646](../../research/09-decisions/adr-1646-the-complex-estimates-are-a-carrier-change-and-the-index-arithmetic-is-not.md).

<!-- plan-section: landed-changes -->

| 2026-09-05 | `8390bf4cf` | `Complex.abs_sub_le`, `Complex.abs_mul_le_of_bounds`, `Complex.BoundedOn` + `bounded_on_unfold`, `Complex.UniformlyContinuousOn` (+ `.mk`/`.rec`/`.modulus`/`.spec`), `uniformlyContinuous_const`/`_id`, and `uniformlyContinuous_of_hasDerivative` — 12 declarations in a new `complex/estimates.rs`, all axiom-free. `abs_mul_le_of_bounds` is four monotonicity steps here where `CReal.abs_mul_le_of_bounds` needed two nonneg-product identities, because `Complex.abs_mul` is an exact `Equiv`. Seven tests, each positive paired with a negative control that must be REFUSED. |
| 2026-09-05 | `8b92a520e` | `Complex.hasDerivative_mul` — the product rule — plus `Complex.bounded_on_add` and `Complex.bounded_on_mul`. Corrects two things ADR-1642's prose got wrong about the hypotheses (continuity is on `F`, the third bound on `G'`). Repairs the vacuous halved-modulus control from `8390bf4cf`. Registers a `complex-estimates` mutation suite with the two mutants the brief named, both on live subjects. |
