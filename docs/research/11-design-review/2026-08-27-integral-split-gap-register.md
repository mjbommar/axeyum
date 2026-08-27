# The `integral_split` gap register — two prerequisites four sizings missed

Status: **open**, one Opus lane dispatched 2026-08-27.

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

## Gap A — the alignment drifts to the midpoint

`mesh_count_align` pads with `depth_ac := depth_cb := deep_ab + big_n`. That
padding is **additive**, and additive padding drives any split ratio toward 1:1
as `big_n` grows. Measured by the lane, for an intended 20% split
(`m_ac0 = 0`, `m_cb0 = 3`):

| `big_n` | actual ratio |
| ------: | -----------: |
|      10 |       0.5185 |
|     10³ |       0.5024 |
|     10⁵ |      0.50002 |
|     10⁶ |     0.500000 |

The outer Archimedean squeeze needs mesh counts unbounded in accuracy, so the
ratio is driven to ½ exactly in the regime the proof depends on. **As landed,
`mesh_count_align` supports bisection only.**

### Correction to the record

The coordinator repeatedly described this stratum as covering *"every rational
proportion"*, in lane briefs and in conversation. **That was wrong**, and it was
wrong in the coordinator's own words, not a lane's — no lane ever claimed it.
It never reached a committed doc or module (checked by `git grep` with a positive
control), so the correction is confined to this entry and to the briefs it
polluted.

### Untested hypothesis handed to the Opus lane

`riemannSum_split_scale_invariant` proves that scaling both counts by `succ k`
leaves the split point `c` **exactly** unchanged, and `succ_mul_succ` /
`mesh_reciprocal_mul` are this file's multiplicative refinement machinery. So a
**multiplicative** alignment may preserve an arbitrary rational ratio where
additive padding destroys it.

This is a hypothesis to test numerically **before** anything is built, not a
design. It is recorded as untested precisely because the coordinator's last
confident claim about this stratum is the one being corrected above.

## Gap B — no endpoint-congruence for the integral

Nothing relates `CReal.integral` at one endpoint to the same integral at an
endpoint that is `Equiv` but not equal. `integral_witness_independent` is the
nearest lemma and does not cover it: its endpoints are the same `b`, varying only
the witness.

The lane established this **cannot** be patched at the `riemannSum` level.
`sample x n` is rational, while `Equiv` reals agree only in the limit — never
sample-by-sample. So a congruence would have to be proved at the limit, not
lifted from the sums.

**Open question, and the lane was asked to answer it before building:** whether
Gap B is load-bearing at all. The split point `c` is *constructed*
(`a + (ofNat (succ m_ac))·Δ`), so if every consumer shares one `ExprId` for it,
congruence may never be needed. Twelve times this session the needed piece either
already existed or was unnecessary; that prior applies here.

## The honest stratum, pending Gap A

If ratio preservation turns out to be impossible with unbounded counts, then
**bisection-only is the true stratum** and must be stated as such in
`creal/integral.rs`'s module doc — not quietly left as an unstated limit of a
lemma whose name suggests generality.

## Standing note on the dead-code warnings

`mesh_count_align` and `bnd_leg_plus_share_le_at` currently carry dead-code
warnings because nothing consumes them. **That is the honest signal and must not
be silenced with `#[allow]`.** The fifteenth lane deliberately declined to wire
them into an unverified assembly, on the grounds that doing so would ship a
checker that cannot fail. Wiring them into a *verified* declaration is the only
acceptable fix.
