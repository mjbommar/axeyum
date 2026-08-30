# Notes: 125-flywheel-mathematics

Detail moved out of [`../status/125-flywheel-mathematics.md`](../status/125-flywheel-mathematics.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

1. **`CReal.sqrt` blocks three unrelated results.** The unsquared triangle
   inequality (why `CPoint.distSq_triangle_sq_bound` is stated squared), the
   metric form of Ptolemy, and `CPoint.incentre` — which needs side *lengths*,
   not their squares. Three lanes on different targets converged on one missing
   definition. Step A of its regularity proof landed, and the constant `c = 3`
   survived a genuine refutation attempt (exact rational arithmetic at
   `dm = dn`, `dm = 1`, `dm ≫ dn`, `dn ≫ dm`; margin `4/(dm·dn) + 1/dn²`,
   strictly positive throughout).

2. **The predicate-scoped fold, recorded WRONGLY TWICE before it was right.**
   Seven lanes reported "no product over a predicate-defined subset". I then
   recorded that it existed one carrier away (`Int.prodRange_permute`) and
   redirected a lane — **matching on a name without reading its hypotheses**,
   the same failure that produced four duplicate lanes the same day. It is
   `MapsInto σ n`: a self-map of the *whole* range. Wilson's theorem does not
   need the scoped version because its modulus is **prime**, so every residue is
   a unit and the subset *is* the contiguous range. Euler's modulus is
   composite. Both corrections are kept in
   [`../../mathematics-2026-08/diary-predicate-subset-product.md`](../../mathematics-2026-08/diary-predicate-subset-product.md)
   rather than edited away.

3. **The blind-evaluation held-out partition was being spent by ordinary library
   work.** 5 of 57 nursery propositions were already proved in the kernel by hand
   development unrelated to autogenesis. `check-autogenesis-holdout-isolation.py`
   could not see any of them: it reads `epistemic_status` and scans for textual
   references, and reported `held_out=57|settled=0|verdict=PASS` throughout. Not
   the vacuous-checker shape — it discriminates correctly on its own predicate;
   the predicate was the wrong one. Repaired per ADR-0542 by an amendment moving
   `natural-binomial` to `development` as a whole family (held-out re-froze at
   **37**), and `scripts/check-autogenesis-holdout-contamination.py` now reports
   contamination without failing the build — failing it would only pressure a
   lane into not proving a theorem it needs.

**The mechanism worth keeping**: every brief said to report precisely what
blocked the lane, and treated a refutation as a complete result. Four targets
this coordinator named were refuted or redirected by lanes doing exactly that,
including one that corrected a design note and redirected a whole line of work.
A wrong brief with an escape hatch is recoverable; one that demands success is
not.
