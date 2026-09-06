# Lane: fourth-moment — the first Hoeffding-class rate the carrier can state

<!-- plan-section: lane-status -->

**Four-wise uncorrelatedness, the fourth central moment of a sum, and the `1/m²`
tail that follows, all at ℚ and all axiom-free** (`DONE`, fourth-moment,
2026-09-06, ADR-1653).

## What this slice is

ADR-1631 closed the binomial slice with a sized obstruction rather than a gap in
effort: Hoeffding needs `E[∏_j f(X_j)] = ∏_j E[f(X_j)]`, which is about a JOINT
law over a product space, and this development has one weight function over one
index range; and Hoeffding's lemma needs `expFn_add`, which exists on no carrier
here. It named the next rate that IS statable, and this lane is that rate.

The shelf now carries, at ℚ:

* Chebyshev on a sample mean — tail `1/m`;
* **the fourth-moment tail — `1/m²`.**

That gap is the whole return on paying for the fourth moment, and it is the
first Hoeffding-class rate this carrier reaches.

## Partition check

Run before proving anything. `artifacts/structural-index/held-out-exclusion-
manifest.json` holds 136 held-out fact ids, every one of them `F:ml430-int-*`;
`artifacts/autogenesis/nursery-v2-extension.json` names 54 families, all
integer/natural arithmetic and none rational, probabilistic, or
moment-shaped. Coverage confirmed positively (`partition` occurs 579 times in
the nursery file; the family list was read out in full), so the empty result is
a real negative and not a grep that never pointed at its subject. **No target
of this lane is in a blind evaluation population.**

## What landed

Six declarations in one new file, `crates/axeyum-lean-kernel/src/rat_prelude/fourth_moment.rs`:

| name | what it says |
| --- | --- |
| `Rat.expectation_sumVars_mul` | `E[(Σ_{i<m} Y_i)·W] = Σ_{i<m} E[Y_i·W]`, for ARBITRARY `W` and with no hypothesis at all |
| `Rat.expectation_sumVars_mul_eq_zero` | the same with every per-index term known to vanish |
| `Rat.FourwiseUncorrelated` | the `Definition`: lone-index mixed moments vanish, and squares are uncorrelated |
| `Rat.expectation_sq_sumVars_mul_sq` | `E[(Σ_{i<m} Y_i)²·z²] = Σ_{i<m} E[Y_i²·z²]` — the one cross term the fourth power does not kill |
| `Rat.fourth_moment_sumVars_le` | `E[(Σ_{i<m} Y_i)⁴] ≤ Σ_{i<m} M₄ + 3(Σ_{i<m} σ²)²` |
| `Rat.fourth_moment_tailSumVars` | `a⁴·E[𝟙[(Σ − EΣ)⁴ ≥ a⁴]] ≤ Σ_{i<m} M₄ + 3(Σ_{i<m} σ²)²` |

## The four calls worth reading (ADR-1653)

1. **The lone-index condition is ONE universal, not three.** "Some index occurs
   exactly once" is, after a commutative reordering, "the last slot differs from
   the other three", and that single condition covers all three unpaired
   multinomial shapes.
2. **One hypothesis-free peeling lemma carries the whole proof.** `W` being
   arbitrary is load-bearing: in every use it MENTIONS the sum being peeled.
3. **`Rat.sumRange_delta` is unusable here** — its hypothesis is unrestricted
   (`∀ t, t ≠ i → …`) and four-wise uncorrelatedness supplies zeros only below
   the bound. A bounded `sumRange_delta_lt` would be a real addition to
   `rat_prelude/sum.rs`; it was not needed once the diagonal lemma had its own
   induction.
4. **The bound is `sumRange`-shaped and the induction closes with `3σ⁴` of
   slack**, not on the nose. `sumRange f (succ b) ≡ sumRange f b + f b` is
   `Eq.refl` here; `natDivSucc (succ b) 0 = natDivSucc b 0 + 1` is not a fact
   this prelude has.

## Hoeffding is still blocked, and for the same two reasons

Re-checked, not inherited: no product space (so no joint law to state
`E[∏ f(X_j)] = ∏ E[f(X_j)]` over), and no `expFn_add` on any carrier here.
Nothing in this slice moves either.
