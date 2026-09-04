# Lane: rn-carrier — ℝⁿ as a carrier (W2-4, convergence point C7)

<!-- plan-section: lane-status -->

**Your lane's block (`landed`, rn-carrier, 2026-09-04).** ℝⁿ landed as
`crates/axeyum-lean-kernel/src/rn.rs`: **58 declarations in a new `RN`
namespace, every one with an empty `Kernel::axiom_footprint`**, 24 tests green
in ~75 s (release, `--test-threads=2`).

**The design (ADR-1606).** A vector is a coefficient function `Nat → CReal`
plus an explicit bound, and **the dimension lives in the equivalence relation,
not in the type**: `RN.EqOn n u v := ∀ i, Nat.lt i n → CReal.Equiv (u i) (v i)`.
So ℝⁿ is one setoid per `n` over one carrier and `RN.metric : Nat → Metric` is
one metric space per dimension. `Fin` does not exist in this kernel and cannot
be carved out (there is no `Subtype` and no `Sigma`); a length-indexed vector
would fight `CReal.sumRange`, which is already `Nat.rec` on a BOUND. This is
the shape `Rat.dotN` already uses for ℚ.

**The headline result.** `RN.cauchy_schwarz : ∀ u v n, ⟨u,v⟩ₙ ≤ ‖u‖ₙ·‖v‖ₙ` —
**unsquared, at symbolic dimension**. `Rat.dotN_cauchy_schwarz` and
`CPoint.cauchy_schwarz` are both squared; `Metric.CPoint.dotLeSqrtMul` is
unsquared but only on the plane. The proof *generalizes* the plane lemma
rather than rebuilding it: the induction step at dimension `n+1` is one
application of `dotLeSqrtMul` at the points `(‖u‖ₙ, uₙ)` and `(‖v‖ₙ, vₙ)`. No
discriminant, no case split on whether `⟨u,u⟩` vanishes — over `CReal` that
split is not available (no `le_total`), which is why the plane lemma had to be
the engine.

**Also landed.** Minkowski (`RN.norm_add_le`) and hence the `Metric` instance,
so `Metric.dist_self`, `Metric.dist_quadrilateral`, `Metric.Cauchy`,
`Metric.TendsTo` and `Metric.Complete` all read on ℝⁿ unchanged. The bridge to
the plane: `RN.ofCPoint` with agreement on `dot`, `distSq` and
`Metric.CPoint.dist`, and the equivalence transported in **both** directions,
so `CPoint` is a provable instance of the n = 2 case.

**What did NOT land, sized.** (1) Cauchy–Schwarz in *squared* form — it needs
the bound at `−v`, hence `CReal.neg_add` and `CReal.mul_neg`, both of which
exist only as unnamed inline steps inside `creal.rs`; naming them is a
`creal.rs` edit this lane does not own, ~60 lines once they exist.
(2) Completeness of ℝⁿ — coordinatewise from `CReal.converges_of_cauchy`,
needing the undeclared bound `|uᵢ − vᵢ| ≤ d(u,v)`. (3) The inverse of
`ofCPoint`, and hence a genuine isomorphism rather than the agreement lemmas.
(4) `smul`'s vector-space laws beyond congruence — nothing consumed them.

**Two notes for the next lane.** `RN.CReal.sumRangeCongrLt` (a
**bound-restricted** finite-sum congruence) is what every `RN` congruence
consumes: `CReal.sumRange_congr` demands agreement at every index, which an
`EqOn n` setoid cannot supply. `Nat`, `Rat` and `Complex` all had one; `CReal`
did not, and it costs two `sumRange_le`s closed by `equiv_of_le_le`. And
`build_rn_prelude` runs its steps through a `declare_each!` macro that NAMES
the refused declaration and renders both types — `DeclarationValueMismatch`
carries two bare `ExprId`s and nothing else, so without it one rejection is a
bisect over 55 steps at ~4 minutes a release build. It found all four defects
in this lane directly.

<!-- plan-section: landed-changes -->

| 2026-09-04 | rn-carrier | `RN.*`: ℝⁿ as a setoid over `Nat → CReal` with the dimension in the relation — 58 declarations, axiom-free, unsquared Cauchy–Schwarz at symbolic dimension, Minkowski, a `Metric` instance per dimension, and the `CPoint` bridge (`b37c3e5ef`) |
| 2026-09-04 | rn-carrier | `shape_search` and `kernel_declaration_projection` taught the `rn` group; the projection's `rn` block adds exactly 58 names to `metric`'s, all under `RN.`, and removes none |
| 2026-09-04 | rn-carrier | ADR-1606 records the carrier design, the three rejected alternatives, what the `CPoint` agreement cost, and the mutation finding that a producer mutation here poisons the shared build rather than killing one test |
