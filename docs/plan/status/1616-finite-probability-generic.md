# Lane: finite-probability-generic — generalize finite probability over `AlgS.OrderedRing`

<!-- plan-section: lane-status -->

**Your lane's block (`COMPLETE`, finite-probability-generic, 2026-09-04).**
All three pieces landed: roadmap **W1-10** (the finite probability layer
stated once over `(R : AlgS.OrderedRing)`), **W2-15** (independence as a
definition, with independence ⇒ uncorrelated), and the ℚ↔ℝ step
**ADR-1612** named. Decision record:
[ADR-1616](../../research/09-decisions/adr-1616-finite-probability-over-algs-orderedring-independence-and-the-integral-bridge.md).

**The deciding number W1-10 asked for is 9 + 2 of 11 attempted, measured by
the kernel and not by inspection.** Nine `Rat.*` theorems are instances of a
generic statement outright (`sumRange_congr_lt`, `sumRange_add`,
`sumRange_le`, `sumRange_nonneg`, `expectation_add`, `expectation_smul`,
`expectation_const`, `expectation_nonneg`, `expectation_le`); two more are
instances with a stated adjustment — `Rat.markov_inequality` after DROPPING
two hypotheses its own proof never uses, and `Rat.variance_nonneg` once
`Rat.sq_nonneg` is supplied for a trichotomy consequence the record cannot
yield. The five definitions (`sumRange`, `IsDistribution`, `expectation`,
`variance`, `covariance`) are DEFINITIONALLY the `ℚ` constants, checked as
`def_eq` of the closed terms rather than of their types. Two `ℚ` theorems
are NOT instances and would need reproof, both for statement-shape reasons
rather than proof difficulty: `Rat.sumRange_congr` states its hypothesis
unbounded, and `Rat.mul_sumRange` is stated in the opposite direction.
**The remaining ~19 `Rat.*` probability theorems were not attempted and are
not claimed** — see the next-lane note below.

**Expectation's linearity is a CONSEQUENCE, not an axiom.** ADR-1612's
warning ("a record whose axioms come from what a development proves cannot
re-derive what it took") was checked here rather than quoted, and it does
not bite, for the reason that ADR itself names: `AlgS.OrderedRing`'s fields
were drawn from `linarith`'s needs (ADR-1584/1585/1592), not probability's,
so probability's theorems are derivable. Where it DOES bite is
`mul_le_mul_of_nonneg_right` — the workhorse under every expectation bound
and a PRIMITIVE on the `ℚ` side. The record's only multiplicative order law
is `mul_nonneg`, so recovering it cost three new generic ring lemmas
(`zero_mul`, `neg_mul`, `sub_nonneg_of_le`) and two forgetful projections
ADR-1592 never declared (`AlgS.OrderedRing.toRingS`, `toGroupS`).
`AlgS.add_add_add_comm` stays out of reach entirely — it is stated over
`AlgS.CommRing`, and a Ring-based `AlgS.OrderedRing` has no projection to
one — so the middle-four exchange is rebuilt inline.

**W2-15 needed no commutativity, and the reason is worth carrying
forward:** `Rat.covariance` is already the computational form
`E[XY] − E[X]E[Y]` while `Rat.variance` is centred. That asymmetry in the
`ℚ` development is load-bearing. Relating the two forms needs
`E[fun k => X k * c] ≃ E[X] * c`, which pulls a constant past the weight
`p k` and therefore needs `mulComm` — which ADR-1592 §2 could not give the
record. Had `Rat.covariance` been centred, W2-15 would have required
commutativity as an explicit hypothesis and a full expansion.

**The bridge ADR-1612 named cannot be stated, and that is the finding.**
`IntSpace` is generic over the FUNCTION space and hard-wired in the VALUE
type: `carrier` is a field, but `integral : (f : carrier) → Integrable f →
CReal` returns a `CReal` and `total : CReal` is a `CReal`. There is no
ℚ-valued `IntSpace` and there cannot be one without a second carrier field,
while `Rat.expectation` is ℚ-valued. Landed instead:
`IntSpace.crealFinite_expectation` — the ℝ-valued finite expectation IS the
`crealFinite` integral, definitionally, in one application — and
`IntSpace.ratExpectation_integral`, the rational one across `CReal.ofRat`,
from the new generic transfer `AlgS.OrderedRing.expectation_map` plus the
already-proved `ofRat_add`/`ofRat_mul`. **Nothing new was needed on the
reals.**

**What the next lane should know.**

- **Extending the instance count is cheap and the failures are informative.**
  Add a row to `instance_rows` in
  `crates/axeyum-lean-kernel/src/rat_prelude/probability_s_tests.rs` and run
  it; both non-instances found here were direction or hypothesis-strength
  mismatches and the kernel reported them in seconds. The untried families
  are `variance_eq`, `variance_smul`, `variance_add_eq`, the `covariance_*`
  bilinearity family, `sumVars`, the indicator family, Chebyshev, the
  sample-mean bound and the weak law.
- **Two obstructions are already known for parts of that remainder.** The
  indicator family needs a DECIDABLE order (`Rat.ble`), which is not a
  record field; and anything relating the centred and computational forms
  needs `mulComm`, so it must take commutativity as an explicit hypothesis
  (the pattern `variance_nonneg` already uses for `∀ a, le zero (a*a)`).
- **Four names belong in the spine, not in this lane's file.**
  `AlgS.OrderedRing.{zero_mul, neg_mul, sub_nonneg_of_le,
  mul_le_mul_of_nonneg_right}` are general ordered-ring facts, here only
  because this was the first lane to need them. Whoever consolidates
  `nat_prelude/structures_setoid.rs` should move them.
- **A `def_eq` between a `ℚ` constant and its generic twin under a symbolic
  bound can fail to terminate usably.** One test was written and WITHDRAWN
  for this, with the reason recorded in the file rather than deleted:
  `Rat.expectation` has delta height 36 and the generic `expectation` has
  height 4, which drives the unfolder the wrong way round. Route around it
  the way `independence_discharges_the_uncorrelated_hypothesis_of_the_rat_theorem`
  does — build the composite the consumer needs and let the kernel infer it.
- **`IntSpace` will need a second carrier field** if a non-`CReal`-valued
  integral is ever wanted. That is a record change, not a proof.

Landed from `a1e6c17ad`; commits `d77ede9db`, `663e925c0`, `f755a5c8c`,
`194f52c03`.

<!-- plan-section: landed-changes -->

| 2026-09-04 | finite-probability-generic | W1-10: the finite probability layer stated once over `AlgS.OrderedRing` — 29 declarations, footprint 0, **9 + 2 `Rat.*` theorems measured as instances**; `mul_le_mul_of_nonneg_right` costs three new ring lemmas and two projections ADR-1592 never declared |
| 2026-09-04 | finite-probability-generic | W2-15: `AlgS.OrderedRing.Independent` and `uncorrelated_of_independent` — the conclusion IS the hypothesis `Rat.variance_add_of_uncorrelated` carries, checked by composing the two terms; needs no `mulComm` only because `Rat.covariance` is already the computational form |
| 2026-09-04 | finite-probability-generic | the ℚ↔ℝ step ADR-1612 named: **it cannot be stated** (`IntSpace`'s integral is `CReal`-valued, so no ℚ-valued instance exists); landed `IntSpace.crealFinite_expectation` and `IntSpace.ratExpectation_integral` across `CReal.ofRat` instead, with nothing new proved about the reals |
