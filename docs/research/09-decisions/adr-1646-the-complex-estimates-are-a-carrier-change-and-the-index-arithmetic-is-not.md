# ADR-1646: the ℂ estimates are a carrier change; the index arithmetic underneath them is not, and is reused rather than re-derived

Status: proposed
Date: 2026-09-05
Lane: `complex-estimates`
Roadmap: W3-5 (complex differentiability, holomorphy, Cauchy's theorem), second slice

Index-summary: ADR-1642 left Leibniz on ℂ blocked, and named the blocker
correctly: not the algebra, but three missing ℂ-side estimates plus a modulus
of continuity, because neither `Complex.BoundedOn` nor
`Complex.UniformlyContinuousOn` existed. This lane declared both, position for
position with the real shelf (the interval's two range hypotheses collapse to
one `Complex.InDisc`, the modulus stays DATA), plus
`Complex.abs_mul_le_of_bounds`, `Complex.abs_sub_le`, two non-vacuity
witnesses, `Complex.uniformlyContinuous_of_hasDerivative`, and then
`Complex.hasDerivative_mul` itself. The decision this ADR records is about the
LAYER BOUNDARY: a bound on a complex quantity is a `CReal`, so the accuracy
budget, the rescale-by-a-magnitude-bound fold and the equal-share fuse are
statements about `Rat.natDivSucc` and `Nat` with no complex number anywhere in
them. `creal/derivative.rs`'s `rescale_index`, `mag_bound`,
`fold_index0_first`, `fold_index0_second`, `mul_modulus_components`,
`weaken_to_addend` and `fuse_three_equal_bounds` were therefore made
`pub(crate)` and CALLED, not copied — the alternative was ~350 lines of
transcription and is exactly the "helper duplication lanes rediscover every
time" the 2026-08-27 architecture review names as a measured root cause. The
lane's other finding confirms ADR-1642's asymmetry claim from the other side:
the five-hundred-line six-leaf shuffle `CReal.hasDerivative_mul` performs by
hand (`expand_bound_term` twice, `expand_term3`, `cancel_middle`, steps 8a–8f)
is ONE `ring_law_proof` call here, while the analytic half is byte-for-byte the
real one.

Index-status: proposed

## Context

ADR-1642 landed `Complex.HasDerivativeOn` on a closed disc with the
const/id/neg/add witnesses and `Complex.HolomorphicOn` as a `Sigma`, and
recorded that the product rule was blocked. Its statement of the blocker is
worth repeating verbatim, because this lane's first job was to check it and it
held:

> The product rule. Its error identity is one `ring_law_proof` call like every
> other; what is missing is three ℂ-side ESTIMATES (a uniform bound on `|G|`,
> one on `|F'|`, one on `|F|`) and a modulus of continuity for `G`.

Two corrections the lane found while building, both from the real shelf's own
record rather than from re-derivation:

1. The continuity requirement is on **`F`**, not `G`. `creal/derivative.rs`'s
   module documentation says its own prose carried the mislabeled version for a
   while and had to be re-verified numerically; the corrected decomposition
   puts `F(y) − F(x)` in the third term. Transcribing ADR-1642's sentence
   literally would have produced a theorem with the hypotheses on the wrong
   functions — a shape that still type-checks, which is why it is worth naming.
2. The three bounds are on `F`, `G` and `G'` (not `F'`). `F'` never needs a
   magnitude bound: it appears only inside `F`'s own error term, which
   `HasDerivativeOn.spec` already bounds.

## Decision

**1. Both estimate predicates are the real shelf's shape, one carrier up.**

`Complex.BoundedOn F c r k` is a transparent `Definition` naming
`∀ z, InDisc c r z → CReal.le (Complex.abs (F z)) (ofRat (natDivSucc (k+1) 0))`
verbatim, with `Complex.bounded_on_unfold` as the isolated confirmation of
defeq — `CReal.BoundedOn`'s arrangement exactly.

`Complex.UniformlyContinuousOn F c r` is a one-constructor inductive in
`Type 0` with a `modulus : Nat → Nat` DATA field and a dependent `Prop` spec,
`CReal.UniformlyContinuousOn`'s arrangement exactly. The modulus is data for
the reason `creal/uniform_continuity.rs` gives at length, and the reason is
sharper here than there: `Complex.HasDerivativeOn` is ALREADY in `Type 0`, so a
`Prop`-valued continuity predicate could not be consumed by any witness in
`complex/deriv.rs` at all.

**2. The index arithmetic is a shared layer and is reused, not transcribed.**

This is the load-bearing decision. Every bound in this development — the
magnitude bound `(k+1)/1`, the accuracy `1/(e+1)`, the rescaled index
`(k+1)·m + k`, the three-way equal split — is a `CReal` or a `Nat`. Nothing in
that arithmetic can observe which carrier produced the quantity being bounded.
Nine helpers in `creal/derivative.rs` were made `pub(crate)`
(`mod derivative` in `creal.rs` likewise) and are called directly from
`complex/estimates.rs` and `complex/leibniz.rs`: `rescale_index`,
`mag_bound`, `fold_index0_first`, `fold_index0_second`,
`mul_modulus_components`, `weaken_to_addend`, `fuse_three_equal_bounds`,
`fold_mag_bound_product` and `fold_mag_bound_sum`.

The alternative considered and rejected was copying them. It is ~350 lines of
mechanical transcription with no mathematical content, it would diverge the
moment either side is corrected, and the architecture review's §1 names helper
duplication as one of two measured root causes of recurring defects in this
area. The cost of the chosen route is a ten-line visibility diff in two files
the `creal` lanes also touch (nine `fn` lines plus one `mod` line, each a
single token); that is a smaller and more legible conflict surface than a
parallel copy.

**3. `uniformlyContinuous_of_hasDerivative` takes the derivative bound as a
hypothesis.**

"Differentiable on a closed disc implies uniformly continuous there" is FALSE
in this development without a bound on `F'`, and the bound is not derivable:
`Complex.InDisc` is a closed disc, but there is no compactness argument in this
kernel that turns continuity on it into a magnitude bound. The real shelf's
`hasDerivative_mul` carries its `BoundedOn` hypotheses explicitly for the same
reason. So the statement is

```text
HasDerivativeOn F F' c r → ∀ k, BoundedOn F' c r k → UniformlyContinuousOn F c r
```

and the estimate spends `1/(n+1)` as two equal halves at `n₂ := 2n+1`:
`|F x − F y| ≤ |(F x − F y) − F'(y)(x−y)| + |F'(y)(x−y)|`, the first summand
read at accuracy `rescale_index(0, n₂)` against `|x−y| ≤ 1`, the second at
`rescale_index(k, n₂)` against `|F'(y)| ≤ k+1`. The halving is pinned by a test
that admits the modulus equation UNDER BINDERS for `F, F', c, r, hf, k, n`,
with a negative control that the un-halved modulus is REFUSED — not by a
comment.

**4. The four hypotheses of `hasDerivative_mul` stay explicit.**

`Complex.hasDerivative_mul` takes `UniformlyContinuousOn F c r` and three
`BoundedOn` facts, in the inline (defeq) shape, mirroring
`CReal.hasDerivative_mul` argument for argument. Folding the three `Nat`
bounds into one would need a rational identity
`natDivSucc(m,0) · natDivSucc(n,0) = natDivSucc(m·n,0)` that this prelude does
not establish — the same gap `CReal.hasDerivative_cube` declined to close.

## Consequences

- Leibniz on ℂ is landed and axiom-free. The product-rule blocker ADR-1642
  named is closed.
- `Complex.hasDerivative_polyEval` is still not landed, and the obstruction has
  MOVED: it is no longer the product rule, it is closure of `BoundedOn` and
  `UniformlyContinuousOn` under `mul` and `add` on a disc, which an induction
  over the degree needs at every step. This is the same wall
  `CReal.hasDerivative_pow` at general `n` hit. Two of the four closure lemmas
  landed with this slice — `Complex.bounded_on_add` and
  `Complex.bounded_on_mul`, both short because
  `Complex.abs_mul_le_of_bounds` does the ℂ half and
  `fold_mag_bound_sum`/`fold_mag_bound_product` (again reused, by decision 2)
  the `Nat` half. What remains is `Complex.uniformlyContinuous_mul`, whose real
  analogue is `creal/uniform_continuity.rs`'s separate SECOND entry point and a
  slice on the order of this one, and then the induction itself, which must
  also carry `Complex.pow`'s own derivative.
- Cauchy–Riemann in one direction is independent of all of the above, and its
  three prerequisites landed with this slice: `Complex.abs_ofReal`
  (the embedding ℝ ↪ ℂ is an isometry), `Complex.abs_re_le` and
  `Complex.abs_im_le`, in `complex/components.rs`. All three route through
  `CReal.sqrt_sq`, whose hypothesis is that its argument is NONNEGATIVE, so the
  square cancelled is `|t|·|t|` and never `t·t` — which is why `abs_ofReal`'s
  right-hand side is `CReal.abs t` and not `t`, and why the bare-`t` form is
  pinned as a REFUSED negative control rather than left to a comment.

  What is still missing is the BRIDGE, and it is a construction rather than a
  lemma: producing `CReal.HasDerivativeOn (fun t => re (F (c + ofReal t))) …
  a b` from `Complex.HasDerivativeOn F F' c r`. Its three parts are (1) disc
  membership from `|t| ≤ r`, which `abs_ofReal` plus one ring step gives;
  (2) the FOUR interval hypotheses of `CReal.HasDerivativeOn` rebuilt from TWO
  disc memberships — ADR-1642's collapse run backwards, and where the work is;
  and (3) the error bound transported by `abs_re_le`, cheap. Not attempted
  here.
- **A negative control of this lane's own was vacuous on its first run**, and
  the way it was caught is worth recording because the usual advice does not
  cover it. The halved-modulus pair was first written with `F, F', c, r, hf, k,
  n` FREE, so `Kernel::add_declaration` returned `UnboundFVar` for both halves:
  the control asserted a refusal and got one, for a reason that had nothing to
  do with the halving. The known two ways a negative control fails are vacuous
  (cannot fail) and inverted (the "false" case was true). This is a third and
  it is specific to a SHARED construction: a construction error refuses both
  halves, and the control cannot distinguish that from success. Only the
  positive half failing exposed it. The rule: **a negative control is evidence
  only while its positive twin is ADMITTED**, and a pair built by one shared
  function must be asserted in both directions or not at all.
- Anything that later corrects one of the nine shared index helpers now
  corrects both carriers at once. That is the point, and it is also the risk:
  a `creal` lane changing one of them changes ℂ silently. The
  `complex_prelude_builds` test is the guard, and it is in the same suite.
