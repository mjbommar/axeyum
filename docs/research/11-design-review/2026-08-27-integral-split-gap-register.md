# The `integral_split` gap register — two prerequisites four sizings missed

Status: **both gaps CLOSED** 2026-08-27. Kept as the record of how they
were found, what was wrong about the first characterisation, and what remains.

## Why this file exists

The active goal is: *any time there is a deficiency or gap, log it and launch an
Opus lane against it.* This is that log. It is deliberately a **register** rather
than a one-off note — `CReal.integral_split` has now absorbed fifteen lanes, and
the pattern that keeps repeating is that a gap gets found, gets fixed by
reslicing, and the *next* gap underneath it was never written down. Append here.

## What is actually landed

Reslicing `integral_split` into individually-verified pieces worked. These are in
the kernel and checked:

`mesh_count_align`, `bnd_leg_plus_share_le_at`, `riemannSum_split_exact`,
`riemannSum_split_exact_of_uc`, `riemannSum_split_scale_invariant`,
`close_within_of_within_indexed`, `riemannSum_sharedAccuracyClose_at`,
`uniformlyContinuousOn_restrict`.

The fifteenth lane then declined to assemble `integral_split` from them, on the
grounds that two prerequisites do not exist. **That refusal was correct** and is
the reason the gaps are known at all — eleven earlier lanes attacked the whole
theorem and produced no characterisation of why it failed.

## Gap A — CLOSED. The alignment was midpoint-only, and worse than described

`mesh_count_align` pads with `depth_ac := depth_cb := deep_ab + big_n`, which is
**additive**. The fifteenth lane measured the resulting split ratio drifting to
1:1 and concluded the stratum was bisection-only.

**Its ratio formula was off by one, and correcting it makes the finding
stronger.** `delta_of a b m` is `(b−a)/(m+1)`, so the split fraction is
`succ(m_ac)/(combined+1) = n_ac/(n_ac+n_cb)`, not `succ(m_ac)/combined`.
Corrected, with `deep_ac = deep_cb` the ratio is **exactly 0.5 at every `big_n`,
including 0** — not a sequence converging to it. Asymmetric deeps drift toward
it (0.2857 → 0.4118 → 0.4860 → 0.49985 → 0.4999985).

And the decisive fact is structural, not numeric: **`mesh_count_align` takes no
ratio argument at all** — its parameters are three uniform-continuity moduli plus
`big_n` — so no choice of arguments reaches a non-midpoint split.

### The fix, and what it says about the retraction below

`mesh_count_align_mul` (commit `40eb61c1c`) scales both counts through
`succ_mul_succ` at a common `succ k`, which cancels out of the ratio
identically, giving
`succ(m_ac)/(combined+1) = succ(m_ac0)/(succ(m_ac0)+succ(m_cb0))` for every `k`.
Verified numerically first — 40 of 40 (base ratio, k) pairs exactly equal for k
up to 1e6 — then kernel-verified four ways, including **both child thresholds**
(which `mesh_count_align` never had to prove) and a **negative control asserting
the additive counts FAIL that identity at 1:5**. The threshold inequality had
0 counterexamples in 200,000 draws, against 1,435 in 20,000 for a deliberately
weakened `k`, so the check is not vacuous.

Uses no `Nat.sub`. Two sub-helpers were needed: `nat_le_add_left` (the prelude
carries `le_add_right` only) and `le_dest_elim`.

### Correction to the correction

An earlier revision of this file recorded that the coordinator's claim of
*"every rational proportion"* was **wrong**. That retraction went too far in the
other direction, and the record should be precise:

- **Wrong about the lemma.** `mesh_count_align` as landed is midpoint-only and
  cannot be argued into anything else.
- **Right about the goal.** Every rational proportion *is* reachable — through
  multiplicative scaling, which is what `mesh_count_align_mul` now provides.

**Bisection-only is NOT the honest stratum.** The only in-tree overstatement was
`creal/integral.rs`'s own module doc, corrected in place by the closing lane.

## Gap B — CLOSED, and the impossibility argument was false

Gap B is **load-bearing**: it is not avoidable by sharing one `ExprId`, for a
reason the coordinator's suggested shortcut could not have anticipated. The split
point `c_k` is *derived from* `m_ac`/`m_cb` — the very counts that must grow
without bound — so it is a fresh `Nat` arithmetic expression at every accuracy
and there is nowhere to put a shared literal.

**But it was the wrong lemma.** Naming the three legs shows the two *integrals*
are never compared at all: `riemann_sum_integral_close` already relates the
caller's `c`-integrals to `c`-Riemann **sums**, and the only mismatch is
`riemannSum F a c_k m_ac` against `riemannSum F a c m_ac`. That is a
`riemannSum` fact, not the `integral_congr_endpoint` that was sized.

The fifteenth lane's argument that this was impossible in principle — because
`sample x n` is rational while `Equiv` reals agree only in the limit — rules out
proving it **sample by sample**, which nothing requires. `riemannSum` is
`sumRange` of `mul (F (add x (mul (ofNat i) Δ))) Δ`, so the congruence follows
from the setoid's own lemmas with `sample` appearing nowhere.

`riemann_sum_congr_endpoints` (commit `e18799228`) is that proof, kernel-accepted
on the first attempt:

    ∀ F aa bb, UniformlyContinuousOn F aa bb → ∀ x y x2 y2 m,
      le x y → le x2 y2 → le aa x → le y bb → le aa x2 → le y2 bb →
      Equiv x x2 → Equiv y y2 →
      Equiv (riemannSum F x y m) (riemannSum F x2 y2 m)

Every step names an existing lemma. **Gap A is a prerequisite for Gap B**:
`riemann_sum_split_scale_invariant` gives `Equiv c_k c_0` only for the
`succ_mul_succ` family. `split_identity_at_equiv_point` (commit `8a6bacfb2`)
builds the join rather than asserting it.

### The one kernel rejection, and what it teaches

`riemann_sum_congr_endpoints` takes the **outer interval its witness is about**
separately from the endpoints being moved. The `[c_k,b]` leg was given
`(c_k,b)` as the outer interval, but `u` witnesses continuity on `[a,b]` and
nothing else — **both legs take `(a,b)`**. The message was a bare `TypeMismatch`
between two `ExprId`s naming neither `u` nor `c_k`, indistinguishable from a
transposed endpoint pair. The `[a,c_k]` leg was correct from the start, which is
exactly why a both-endpoints helper needs a caller test exercising **both**
directions — a one-directional test would have stayed green.

## What remains: `integral_split` did NOT close

No further gap appeared. What is left is exactly the twelfth lane's estimated
volume, and **both named prerequisites are now landed and kernel-checked**:
three `riemann_sum_integral_close` legs, `close_within_of_within_indexed` and
`bnd_leg_plus_share_le_at` per leg, `abs_add_le` twice, `equiv_zero_of_small` to
close, with `big_n` and `e_inner` as functions of `e`.

Prelude build: 31.58 s at merge → 32.66 s isolated final, band 29–39 s, no
movement. (A 35.93 s reading came from a batched run; the isolated
re-measurement is the one to quote — a lesson worth keeping, since a contended
reading looks exactly like a regression.)

## Standing note on the dead-code warnings

Dead-code warnings went from **2 to 7**, and the closing lane added no
`#[allow]`: `mesh_count_align`, `bnd_leg_plus_share_le_at`,
`mesh_count_align_mul`, `riemann_sum_congr_endpoints`,
`split_identity_at_equiv_point`, `nat_le_add_left`, `le_dest_elim`,
`MeshAlignMul`. They carry dead-code warnings because nothing consumes them. **That is the honest signal and must not
be silenced with `#[allow]`.** The fifteenth lane deliberately declined to wire
them into an unverified assembly, on the grounds that doing so would ship a
checker that cannot fail. Wiring them into a *verified* declaration is the only
acceptable fix.
