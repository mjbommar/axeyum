# ADR-0516: the real inverse is well-defined by uniqueness of inverses, and its congruence must range over the modulus

Status: accepted
Date: 2026-08-18
Index-summary: `CReal.inv : (x : CReal) → (k : Nat) → PosBound x k → CReal` is **built** — the modulus is an explicit `Nat`, the proof only discharges `CReal.mk`'s `Prop` field, and the sampling index `(C+1)n + C` with `C+1 = (4k+4)(k+2)` reads back **two** ways so `Rat.natDivSucc` still never needs to be antitone in its index. Well-definedness is `mul_inv_cancel` plus **uniqueness of inverses in a commutative monoid**, not a second estimate — and because the modulus is *data*, the congruence must quantify over `k₁` and `k₂` independently, which `CReal.inv_index_irrelevant` records

## Context

[ADR-0510](adr-0510-the-real-inverse-is-partial-and-its-modulus-is-data.md)
settled *what shape* the real inverse has: `Apart x zero` is an `Or`, so
`inv : (x : CReal) → Apart x zero → CReal` is undefinable, while
`inv : (x : CReal) → (k : Nat) → PosBound x k → CReal` is definable, because a
function may **take** a `Prop` and return a `Type` — it may only not *branch* on
one. It did not build it. Two things were left open and are decided here.

**First, well-definedness is a bigger obligation than usual.** The five
congruences `CReal` already carries (`neg_congr`, `add_congr`, `mul_congr`,
`le_congr`, `lt_congr`) each say one thing: replacing an argument by an
`Equiv`-equal one does not change the result. `inv` has a second argument that
is **not** a real number and is not related to anything by `Equiv` — the
modulus. Two callers holding different separating moduli for the *same* `x`
build genuinely different sequences: `k = 0` samples at `7n+7`, `k = 1` at
`32n+31`. Nothing in `inv`'s type says the results agree, and if they do not,
`x⁻¹` is not a function on ℝ but a function on (real, modulus) pairs — which
would make every downstream field law carry a modulus it has no business
carrying.

**Second, an estimate for that congruence would be expensive and is avoidable.**
The direct route bounds `(x_{j₁(n)})⁻¹ − (y_{j₂(n)})⁻¹` by telescoping through
`y_{j₁(n)}`, needing the regularity of `y`, the hypothesis `Equiv x y`, and the
reciprocal bound at two different moduli — roughly the size of `CReal.inv`'s own
regularity proof, again.

## Decision

**1. `CReal.inv` samples at `j(n) := (C+1)·n + C` with
`C := (4k+4)·(k+1) + (4k+3)`, so that `C + 1` is `(4k+4)·(k+2)`
definitionally.** `CReal.invShift k` is that `C`, written in the shape
`(A+1)·b + A` rather than as the polynomial `4k²+12k+7`, so that
`Rat.nat_index_compose` applies to it verbatim and no ℕ-subtraction appears
anywhere.

The index is chosen so it reads back **two** ways through the *existing*
`Rat.natDivSucc_le_scaled`, and this is what keeps antitonicity of
`Rat.natDivSucc` in its index off the critical path for the fifth time:

- *A constant lower bound.* `nat_index_compose` rewrites `j(n)` as `(A+1)·e + A`
  with `e = (k+2)n + (k+1)`, and the **new** `Rat.nat_index_symm` rewrites that
  as `(e+1)·A + e` — a sampling index whose shrinking argument is `A`, not `n`.
  So `2/(j(n)+1) ≤ 2/(A+1) = 1/(2k+2)` at every `n`, and with `PosBound` that
  gives `1/(2k+2) ≤ x_{j(n)}` with no dependence on `n` at all.
- *A shrinking bound.* `j(n) = (C+1)n + C` directly, so `K/(j(n)+1) ≤ 1/(n+1)`
  for any `K ≤ C+1` by `natDivSucc_le_add_left` then `natDivSucc_scale`. The `K`
  the regularity estimate produces is `(2k+2)²`, and `C + 1 = (2k+2)² + (4k+4)`
  exactly — which is why the factor `(k+2)` is in `C`.

**2. Well-definedness is proved by uniqueness of inverses, not by an estimate.**
`CReal.inv_congr : ∀ x y k₁ k₂ h₁ h₂, Equiv x y → Equiv (inv x k₁ h₁) (inv y k₂ h₂)`
closes on `mul_inv_cancel` at both ends:

```text
u ≈ u·1 ≈ u·(y·v) ≈ (u·y)·v ≈ (u·x)·v ≈ (x·u)·v ≈ 1·v ≈ v·1 ≈ v
```

using only `mul_congr`, `mul_assoc`, `mul_comm`, `mul_one` and `Equiv.trans`. No
index arithmetic appears, and none can: the two sequences are compared *only*
through the operation they invert.

**3. The congruence quantifies over `k₁` and `k₂` independently, and the
modulus-only case is stated separately.**
`CReal.inv_index_irrelevant : ∀ x k₁ k₂ h₁ h₂, Equiv (inv x k₁ h₁) (inv x k₂ h₂)`
is `inv_congr` at `y := x` with `Equiv.refl`. It is a separate declaration
because it is the half a reader does *not* expect to need, and because a
congruence stated only over `Equiv x y` at a *fixed* `k` would look complete
while leaving `x⁻¹` a function of the modulus.

**4. `mul_inv_cancel` closes through `Equiv.of_bounded`, not by an exact
estimate.** `CReal.mul`'s sampling shift is built from `CReal.bound` of its two
factors — opaque `Int.natAbs` projections — and `CReal.invShift` from `k`.
Nothing relates them, and nothing has to: `Rat.mul_inv_sub_one` makes the
residue a regularity gap times a constant, and `Equiv.of_bounded` accepts any
`O(1/n)` bound. The constant that comes out is `4k+4`.

## Consequences

- ℝ has a multiplicative inverse on `{x | PosBound x k}` with **zero** trusted
  declarations: `nat_axiom_inventory --include-constructed` reports
  `creal: axiom=0 opaque=0 quotient=0 total_trusted=0`, unchanged.
- Two ℚ lemmas were needed one level down and are new:
  `Rat.inv_natDivSucc : (1/(m+1))⁻¹ = (m+1)/1` — the only place in this
  development where the *value* of an inverse is computed rather than a property
  of it derived, and necessary because every bound in ℝ is a single
  `Rat.natDivSucc` whose numerator is a `Nat` — and `Rat.nat_index_symm`.
- **The negative branch is still not built.** `Rat.mul_inv_cancel`'s hypothesis
  is `0 < q`; the general `x # 0` case cannot be reduced to the positive one by
  branching on the disjunction, so it needs `inv (neg x)` under a separate
  hypothesis or a caller who picks the sign. `CReal.no_total_inverse` remains
  the proved statement that no total inverse can exist.
- No Markov's principle in any disguise: `¬(x ≈ 0) → x # 0` is not proved, not
  assumed, and not used.

## Alternatives considered

- **An estimate for `inv_congr`.** Rejected: same size as `CReal.inv`'s own
  regularity proof, and it would have to be redone for every later operation
  whose congruence follows from an algebraic law.
- **Hiding the modulus behind `Exists`.** Impossible, and that impossibility is
  ADR-0510's `pos_bound_of_lt`: `Exists` is a `Prop`, so `Exists.rec` eliminates
  only into `Prop` and the `k` can never reach a `CReal`.
- **Making `Rat.natDivSucc` antitone in its index** and picking a simpler
  sampling index. Rejected for the fifth time: that lemma is ~250 lines and
  every use so far has had a cheaper reading available. `nat_index_symm` is
  fifteen.
- **A single `inv_congr` at a fixed `k`.** Rejected: it looks like
  well-definedness and is not, for exactly the reason in Context.
