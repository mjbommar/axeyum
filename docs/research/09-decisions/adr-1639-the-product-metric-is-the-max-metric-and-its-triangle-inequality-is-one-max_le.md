# ADR-1639: the product metric is the max metric, and its triangle inequality is one `max_le`

Status: accepted
Date: 2026-09-05
Lane: `metric-products`

Index-summary: `Metric.prod M N` (roadmap W2-10) carries the MAX metric,
`dist (x,y) := CReal.max (M.dist (fst x) (fst y)) (N.dist (snd x) (snd y))`,
not the sum metric — its triangle inequality is one `CReal.max_le` against a
target that is already the max metric's own RHS, versus two `add_le_add`s
plus a rearrangement for the sum metric. Projections are 1-Lipschitz
(`le_max_left`/`le_max_right`, no rate change); completeness transfers with
the combined modulus `K1 + K2` (additive stand-in for "max of the two
moduli", via `Rat.natDivSucc`'s numerator monotonicity); `Metric.cpoint` and
`Metric.prod Metric.creal Metric.creal` are shown carrier-equivalent (a
setoid isomorphism), not isometric — their distances are genuinely different
formulas (Euclidean vs max).

## Context

`docs/research/08-planning/roadmap.md` W2-10 records the product of two
metric spaces as open, with the subspace half already closed by
`metric/subspace.rs` (ADR-1613). `Metric` is a 12-field record over an
explicit `CReal`-valued distance (`metric.rs`); building a product needs a
CARRIER (this kernel's `Sigma.{0,0}`, ADR-1613) and a DISTANCE formula, and
the distance formula is a genuine choice with different proof costs on
`CReal`.

## Decision

**The carrier** is `Sigma.{0,0} M.carrier (fun _ => N.carrier)` — the
non-dependent specialization of the SAME dependent-pair inductive
`metric/subspace.rs` uses for `Subtype`. `M.carrier : Sort 1` (`Type 0`), so
the level arguments are `[0, 0]` and the result sort is `Type (max 0 0) =
Sort 1`, matching `Metric`'s own carrier field exactly.

**The distance is the max metric, not the sum metric.** Both are valid
metrics; the choice is about proof cost on `CReal`. The max metric's
triangle inequality needs exactly `CReal.max_le` once, against the target
`add (dist x y) (dist y z)` — which is ALREADY that target, because
`max_le`'s two premises (`le dM(x,z) target` and `le dN(x,z) target`) are
each one `le_max_left`/`le_max_right` (bounding a component by its own
`dist`) composed with one `add_le_add` (summing two such bounds) composed
with one `le_trans` through the ambient triangle inequality (`M.distTriangle`
/ `N.distTriangle`). No case split, and no lemma about `max` distributing
over `add` is needed. The sum metric's triangle inequality needs the SAME
`add_le_add`-through-`distTriangle` step twice, plus a rearrangement
(`(a+b)+(c+d) ~ (a+c)+(b+d)`) the max metric's proof never touches. Every
other field (`distSelf`, `distEquiv`, `distComm`, `distNonneg`, `distCongr`)
is `CReal.max_congr`/`equiv_of_le_le`/`le_of_equiv` composed with the
corresponding fact about each component — no case split anywhere in the
12-field record.

**Projections are 1-Lipschitz.** `Metric.prod_fst`/`Metric.prod_snd`'s
`UniformlyContinuous` proof uses the IDENTITY modulus (`fun n => n`): the
hypothesis bound and the conclusion bound are the SAME rational
(`ofRat (natDivSucc 1 n)`), because `M.dist (fst x)(fst y) ≤ dist_prod x y`
(`le_max_left`) needs no rate change at all. The same one-step bound
composes: a map `G` into the product that is `Metric.Continuous` stays
continuous after composing with either projection, AT THE SAME MODULUS
(`Metric.prod_fst_continuous_of_continuous` / `..._snd_...`) — the `→`
direction of "continuous into the product iff continuous in both
components". The `←` direction (needing `CReal.max_le` to COMBINE two
component moduli into one, nested inside a modulus-producing existential)
and compactness transfer (the net-cover route in `metric/compactness.rs`)
are NOT attempted this round; see the module doc in `metric_prod.rs` for the
precise obstruction each would need to close.

**Completeness transfers, and the combined modulus is additive, not
`Nat.max`.** `Rat.natDivSucc`'s FIRST argument is the numerator
(`Rat.natDivSucc k j = k/(j+1)`), so — unlike `ContinuousAtWith`'s modulus,
which supplies the DENOMINATOR argument — `TendsToAt`/`CauchyAt`'s `K` is
monotone INCREASING: a bigger `K` gives a LOOSER (bigger) bound. Given
`TendsToAt M f1 L1 K1` and `TendsToAt N f2 L2 K2` (from `Complete M`/
`Complete N` applied to the two projected sequences), `K1 + K2` dominates
BOTH `K1` and `K2`'s own rate via `Rat.natDivSucc_le_add_left` (`natDivSucc a
j ≤ natDivSucc (a+e) j`) — the M-side bound needs it directly (`a := K1, e :=
K2`); the N-side bound needs it at `a := K2, e := K1` PLUS one
`Nat.add_comm`-rewrite (`K2+K1 = K1+K2`) to land on the SAME combined
modulus. `K1 + K2` is the additive stand-in for "the max of the two
moduli" here — no `Nat.max` primitive is threaded through
`Rat.natDivSucc`'s own lemmas, and the sum dominates both summands exactly
the way a max would, which is the only property this proof needs. Forgetting
this step (reusing `K1` alone as the combined modulus, dropping the `N`
projection's own rate entirely) is exactly the adversarial mutant recorded
below: the kernel REFUSES the resulting declaration, because
`TendsToAt N f2 L2 K2`'s own witness does not have type `le .. (rate K1 n)`
in general.

The CAUCHY direction (`Cauchy (Metric.prod M N) f → Cauchy M f1 ∧ Cauchy N
f2`) needs no combination at all: `CauchyAt (prod M N) f K`'s own witness `K`
already bounds EACH projected component (`le_max_left`/`le_max_right`
through the SAME `K`), so `f1`, `f2` are Cauchy at that SAME `K` — the
asymmetry between the two directions (one needs combining, one does not) is
itself worth recording: going DOWN into the product's factors costs nothing
extra; coming BACK UP from the factors' own (independently witnessed) limits
is where the two moduli must be reconciled.

**`Metric.cpoint` and `Metric.prod Metric.creal Metric.creal` are related as
CARRIERS, not as metric spaces.** `Metric.cpoint`'s distance is Euclidean
(`CReal.sqrt (CPoint.distSq P Q)`, `metric.rs`); `Metric.prod`'s is the max
metric built here. The two are bi-Lipschitz equivalent
(`max(|dx|,|dy|) ≤ sqrt(dx²+dy²) ≤ max(|dx|,|dy|)·sqrt 2`) but not EQUAL, so
no isometry statement is attempted. What IS proved: `Metric.cpoint_of_prod`
/ `Metric.prod_of_cpoint`, the two carrier maps, and BOTH round trips up to
each side's own equivalence relation. The first round trip
(`Metric.prod_of_cpoint_of_prod`) is definitional — `CPoint.x`/`.y` and
`Sigma.fst`/`.snd` both ι-reduce on a LITERAL constructor, so two
`CReal.equiv_refl`s close it. The second (`Metric.cpoint_of_prod_of_cpoint`)
is NOT definitional for an arbitrary bound `P` (`CPoint.x P` is stuck on a
variable) and needs `CPoint.rec`: case-eliminate `P` into the literal-`mk`
case, where `CPoint.mk (CPoint.x P)(CPoint.y P)` — now `CPoint.mk a b` for
literal `a`, `b` — becomes `CPoint.Equiv (CPoint.mk a b) (CPoint.mk a b)`,
closed by `Metric.cpoint_equiv_refl`.

## Mutation evidence

Two mutants were RUN (not predicted) against the built proof terms, both in
the shared worktree per the standing brief (this lane made no other
concurrent writes), each applied/tested/restored one at a time:

1. **Wrong component in the triangle inequality**: `build_dist_triangle`'s
   `t2a` (meant to bound `M`'s distance by `le_max_left`) changed to
   `le_max_right`. RUN: kernel REFUSED the declaration outright — 7 of 7
   `metric_prod::` tests failed, with the explained `TypeMismatch` naming
   exactly the swapped selector (`Sigma.fst` expected, `Sigma.snd` got).
   Restored byte-for-byte; `git diff` empty afterward.
2. **Completeness forgetting to combine the two moduli**: `kc := k1 + k2`
   changed to `kc := k1` (the N-projection's own rate dropped entirely). RUN
   (`--release`, since debug-build kernel checking is up to 32x slower on
   proof terms this size): kernel REFUSED the declaration outright — 7 of 7
   `metric_prod::` tests failed, with the explained `TypeMismatch` naming a
   `Rat.natDivSucc` term whose numerator no longer matched the one the
   N-side bound actually established. Restored byte-for-byte; `git diff`
   empty afterward.

## Two real defects the kernel caught, not inspection

Running the suite (not reading the proof terms) found two genuine bugs
before any mutant was applied:

- `Metric.ContinuousAtWith`'s modulus `k` is `Nat -> Nat` (it supplies the
  DENOMINATOR argument `k n`), unlike `Metric.CauchyAt`/`TendsToAt`'s plain
  `Nat` numerator `K` — two different "modulus" shapes in the same
  vocabulary. The continuity-composition proof existentially quantified
  over plain `Nat` instead of `Nat -> Nat`; the kernel refused with a
  `TypeMismatch` naming a bare `AxNat` where a `(x0:AxNat)->AxNat` function
  was expected.
- The N-side modulus-combination rewrite (`K2+K1 = K1+K2`, via
  `Nat.add_comm`) needs an `Eq.rec` motive over `Rat.le`, since both sides
  are still `Rat.natDivSucc` values at that point (before
  `CReal.ofRat_le` lifts them) — the motive was built with `CReal.le`
  instead, and the kernel refused with a `TypeMismatch` naming `Rat` where
  `CReal` was expected.

Neither would have been caught by `cargo check`: both are kernel-level
(runtime) type errors inside `Kernel::add_declaration`, invisible to the
Rust compiler, which sees only `ExprId`s. Both commits (7068500cf,
02384e4c4) are separate from the scaffold commit that compiled clean but
had not yet been run.

## Consequences

- `Metric.prod` is available as a first-class `Metric` for any two spaces
  already in the library (`Metric.creal`, `Metric.cpoint`,
  `Metric.crealIntervalSpace`, a `Metric.subspace`, …), and composes with
  `Metric.subspace`/`Metric.crealIntervalSpace` without further work (a
  product of subspaces is a subspace of the product's carrier restricted by
  the obvious conjunction predicate — not built this round, but expressible).
- The `←` continuity direction and compactness transfer are the two
  concrete next tasks this ADR leaves open for W2-10; both need `CReal.max_le`
  to COMBINE two moduli/covers rather than propagate one, the same shape
  the completeness proof already used once.
- No isometry between `Metric.cpoint` and the max-metric product is claimed
  or implied by the carrier-equivalence proved here; a future ADR closing
  that gap needs `CReal.sqrt` monotonicity against both `max` and `add`
  bounds, which this round did not derive.
