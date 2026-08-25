# The constructive square root: the route, and what is actually left

Status as of 2026-08-25: **`CReal.sqrt` is not declared.** `creal/sqrt.rs`
declares `CReal.natSqrt` (with a two-sided spec) and the rational approximant
`CReal.sqrtApprox`, and the module's own doc names the open obligation: no
`Regular` proof exists for `sqrtApprox`, so it cannot be sealed into a `CReal`.

This note records a route to that proof, worked out 2026-08-25. It is written
down because the interesting part is a *number* that took a derivation to find,
and a transcript is not a durable place for it.

## What is verified, and what is not

Verified by measurement: every lemma the route cites exists in the tree —
`p.rat_sq_le`, `regular_of_kregular`, `Rat.sub_max_le`, `natSqrtLe`/`natSqrtLt`,
`Nat.div_mod_exec`, `Nat.div_mod_bounds`, `of_nat_nat_abs_of_nonneg`,
`Rat.nat_div_succ_add`. A deliberate nonsense name in the same query returns
zero, so the query discriminates.

**Not verified: the derivation itself.** No proof term has been built and the
kernel has not checked a line of it. Two numeric spot-checks were done by hand
(`x = 2`: the gap between indices 2 and 4 is ~0.067 against a bound of ~2.13;
`x = 4`: `sqrtApprox` is exactly `2` at every index), which check the direction
and sign of the steps and nothing more. Treat the constant below as a claim to
be discharged, not as a result.

## The claim

`sqrtApprox x` is **`KRegular` with the fixed constant `c = 3`** (so `K = 4`),
**uniformly in `x`** — the constant does not depend on `x`'s magnitude.

That uniformity is the whole point. `regular_of_kregular` in `creal/speedup.rs`
then converts it to a genuine `Regular` sequence with no slack, so

    CReal.sqrt x := CReal.mk (speedup (sqrtApprox x) 3) (regular_of_kregular …)

is a **total function of `x` alone**. No sign hypothesis, no `PosBound`, no case
split on whether `x ≥ 0` — which matters, because in a constructive setting
`0 ≤ x` is undecidable and cannot be case-split on.

This is the point where `sqrt` and `inv` part company, and it is worth being
precise about why, because `CReal.inv` is the obvious precedent to copy and
copying it here would be wrong. `inv` takes `PosBound x k` as *data* because it
must know how far `x` is from zero in order to choose a sampling depth: near
zero the answer is enormous and the schedule has to react. `sqrt` has no such
need. The `max(·,0)` clamp inside `sqrtApprox` handles negative samples without
a decision, and the schedule's index `j = (n+1)²` is fixed in advance. So
nonnegativity is not needed to *build* `sqrt x`; it is needed only to state the
theorem that `sqrt x · sqrt x ~ x`, where it belongs as an ordinary `Prop`
hypothesis.

## The derivation

Write `dm := m+1`, `rm := sqrtApprox x m`, `qm` for the clamped sample.

- **A. Floor bracket.** `Nat.div_mod_bounds` (through `Nat.div_mod_exec`, which
  reconstructs the executable `Nat.div` as a `divMod` witness) with
  `natSqrtLe`/`natSqrtLt` gives, at each index, `rᵢ² ≤ qᵢ < (rᵢ + 1/dᵢ)² + 1/dᵢ²`.
- **B. The two samples are close.** `p.regular` applied at the *exact* indices
  `(jm, jn)` — not read back through a shared index — gives
  `|qm − qn| ≤ 1/(jm+1) + 1/(jn+1)`. `Rat.sub_max_le` carries this through the
  clamp. Since `jᵢ = dᵢ²` exactly, this is `≤ 1/dm² + 1/dn²`.
- **C. Combine, then take the square root once.** With `δ := 1/dm + 2/dn`,
  steps A and B give `rm² < (rn + 1/dn + δ)²`. The right factor is nonnegative,
  so **one** application of `CReal.ratSqLe` (`u·u ≤ s·s → 0 ≤ s → u ≤ s`)
  discharges the square: `rm ≤ rn + 1/dm + 3/dn`. Mirror in `m`/`n`, weaken
  `1/dm ≤ 4/dm`, and the two one-sided facts fuse to `KRegular`'s shape at
  `c = 3`.

`ratSqLe` is the load-bearing step and the reason this route exists at all: it is
what lets a bound on squares become a bound on the values without a case split.
It cost a four-lane chain (`creal/mul_self_zero.rs`, 982 lines) for a strictly
simpler statement than this one.

## What is left

Two bridging pieces, then the chain:

1. **`1 ≤ n → n = succ (pred n)`**, to turn `Rat.den_pos` into the `succ`-shaped
   divisor `Nat.div_mod_exec` wants. This is proved **three times already** as a
   private helper — `nat_prelude/finite.rs` (`pub(super)`), `fermat.rs`,
   `totient.rs` — and is reachable from none of them outside `nat_prelude`. A
   fourth copy is the path of least resistance; **promoting it to a declared
   `Nat` theorem is the right fix**, and would delete three duplications.
2. The num/den reconstruction connecting the clamped rational sample back to the
   `Nat` operands of the floor division. `of_nat_nat_abs_of_nonneg` covers the
   numerator; the denominator half goes through `Rat.le`'s cross-multiplication
   definition and has not been chained to a single reusable lemma.

Then `declare_kregular_sqrt_approx` (steps A–C), and `CReal.sqrt` is short
wiring. Size estimate: 800–1500 lines of term construction, comparable to
`mul_self_zero.rs`.

## Why this unblocks more than itself

Geometry is waiting on it. `CPoint.distSq_triangle_sq_bound` (Euclid I.20 in
squared form) landed 2026-08-24 in squared form *because* there is no `sqrt` —
the unsquared triangle inequality, actual Euclidean distance, and Heron's
formula all need it. It is the single highest-fanout missing definition in the
constructive-reals development.

---

# Addendum, 2026-08-25: what "nothing is missing" is worth

Unrelated to `sqrt`, but the same lesson and it belongs somewhere durable.

A lane building `monotone_of_nonneg_deriv` handed off a plan ending *"none of
these needs anything absent from the codebase — it's a genuinely substantial
further slice, not a blocked one."* The next lane checked and **the claim did
not survive contact.**

The gap neither of the first two lanes named: the subdivision picks a piece
count `K` so the last interpolation point lands on `y`. But `ofNat K · step ~
(y − x)` is a **proved identity, not a reduction** — so `x_K` is only ever
`Equiv` to `y`, never syntactically equal. Closing the telescoped bound to
`F x ≤ F y` therefore needs `F` to respect that `Equiv`, and **that is not free
for an arbitrary `F : CReal → CReal`.** Only proved congruences (`mul_congr`,
`neg_congr`, …) carry across `Equiv`, and `HasDerivativeOn`'s hypothesis is
stated for the caller's specific `x, y`, not up to `Equiv` on them.

The lane then closed it: `CReal.hasDerivative_closeOfEquiv` derives exactly that
congruence from `HasDerivativeOn`'s own spec, instantiated at a **fixed**
accuracy `e := 0` — because `u ~ v` makes the piece width `Equiv` to `zero`
outright rather than merely small, so no Archimedean closing is needed for this
lemma specifically. Landed, axiom-free.

**The transferable point:** a plan's "nothing is missing" is a *prediction*, and
this one was made by the lane that had just spent a full attempt on the problem
and was in the best position to know. It was still wrong, in a way visible only
to someone who tried to write the terms. Treat a handoff's confidence about the
remaining work the way this repository treats a checker that has never been seen
to fail — it may be right, but nothing yet distinguishes it from wishful.

Two setoid facts worth carrying forward on their own:

- **Endpoint exactness is not free in a setoid.** Any construction that "picks
  `K` so the endpoints match" gets `Equiv`, not `Eq`, and every function applied
  to that endpoint then needs a congruence.
- **A congruence for a function given only by a spec can often be *derived* from
  that spec at a degenerate accuracy.** That is what made this one cheap, and it
  is likely to recur for `integral`, `exp`, and anything else defined by a
  modulus.
