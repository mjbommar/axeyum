# Architecture review, 2026-08-27

Measured, not impressionistic. Companion to ADR-0601..0604 and
`docs/formalized-math-2026-08/07-the-cost-model-and-pareto-position.md`.

## 1. The software root cause: `creal.rs` fuses four concerns

Measured this day:

| Signal | Value |
|---|---|
| `CRealPrelude` fields | 441 |
| `creal.rs` (struct + dispatch hub) | 9,284 lines |
| `declare_*` calls in one linear sequence | 364 |
| private `fn` : `pub(super) fn` in `creal/` | 1,275 : 178 |
| verbatim helper copies | `zero_le_of_nat` x3; `mul_deshift`, `telescope_cauchy_pad2`, `exp_dominant_cauchy_body_concrete` x2 |
| suite wall-clock | `creal::` 313 s, `complex::` 361 s |

`creal.rs` is simultaneously the **name registry**, the **field struct**, the
**build order**, and the **dispatch**. Every recurring failure follows:

1. **Phase-order bugs.** Four lanes in one day hit `UnknownConst` on a name
   plainly visible in source, each fixing it with a "second dispatch entry
   point". That is a hand-maintained linearization of a dependency graph, and
   its failure mode is SILENT in the worst way: indistinguishable from the
   declaration not existing.
2. **The inventory sharding fixed only the mirror.** Sharding
   `creal_tests.rs` into 33 per-module inventory files removed the test-side
   collision (8+ pin incidents in one day, now zero). But two lanes adding
   declarations to different modules STILL both edit `creal.rs`'s 441-field
   struct and its dispatch list. Same bottleneck, production side.
3. **Duplication is structural, not sloppy.** With a 7:1 private-to-exposed
   ratio and per-lane file ownership, exposing a helper means editing a file
   another lane owns; copying does not. Lanes rationally copy. `zero_le_of_nat`
   exists three times for this reason, and one lane copied six helpers verbatim
   in a single session.

**Proposed fix (one refactor, deliberately deferred):** each `declare_*`
announces the declarations it depends on; the builder topologically sorts them.
That eliminates the phase-order class permanently rather than documenting it.
Split the god-struct into per-module registries behind a facade, and the
production-side collision goes away too. This is
[05-throughput.md](../../formalized-math-2026-08/05-throughput.md)'s C1
("shard the library so lanes compose instead of collide") applied to the half
that still hurts.

**Sequencing constraint:** this refactor touches every file every live lane
owns. It must run against an EMPTY board, and its own verification is the
environment-derived union check plus the full `creal::` sweep.

## 2. The mathematical root cause: the integral's mesh is INTERVAL-RELATIVE

`Delta_ab := (b-a)/(m+1)`. The mesh is defined BY the interval, so `[a,c]` and
`[c,b]` meshes are incommensurate with `[a,b]`'s for an arbitrary `c`. The
entire crossing-index / clamping / uniform-continuity apparatus
(`crossingIndex`, `crossingCloseClamped`, `meshScaledLeOfGe`,
`riemannSampleCrossingClose`, ~13 lanes) exists to bridge exactly that gap.

**The decisive evidence that this is definitional, not analytic**:
`CReal.riemannSum_split_exact` proves additivity **exactly, with no estimate,
no crossing index, no uniform continuity** — precisely when the split point IS
a mesh point (`n_ab = succ m_ac + m_cb`). The old "false counterexample"
(`m := 0` on all three intervals, `0` vs `2`) violates that identity and
nothing else.

**The alternative not taken**: anchor the mesh to a FIXED GLOBAL GRID (spacing
`2^-k` over the reals) and integrate over grid points inside `[a,b]`. Adjacent
intervals then align BY CONSTRUCTION, additivity becomes near-structural, and
the cost moves to boundary handling (endpoints are no longer mesh points).
This is the discrete shadow of what a measure-theoretic integral gets from
countable additivity on disjoint sets — cf. Mathlib's
`integral_add_adjacent_intervals`, which is `setIntegral_union` plus set
algebra and never mentions a mesh.

**This note does not propose rebuilding the integral.**
`riemannSum_split_exact` plus the mesh-point stratum may well carry FTC-1. The
point is that the DIFFICULTY IS RECORDED AS A CONSEQUENCE OF A DEFINITIONAL
CHOICE, so the next person does not re-derive it as an inherent obstacle — and
so that a future carrier (a Lebesgue-style or L1-completion integral) starts
from a stated comparison rather than from scratch.

## 3. Two design patterns lanes rediscover every time

### 3a. "Computed, not extracted"

`Exists.rec` is `Prop`-only: it cannot produce a term whose type mentions the
extracted witness, so **anything needed as DATA must be computed**. This shaped
roughly a dozen designs in one session. Three canonical shapes:

- **Computed witness.** `ivt_bisect`'s bisection depth; Chapter 7 boundedness's
  `K = succ(succ(bound(F a)) + ...)`; `Nat.even_or_odd`'s `k := div n 2`;
  `Complex.factorQuotient`'s synthetic division. Never `exists K, ...`.
- **Generic over a bound, substitute last.** `declare_converges_of_cauchy` /
  `declare_e_converges` / `declare_cos_one_converges`: build over a BOUND
  `(k, h)` and substitute the concrete pair only in the final Pi-application.
  Doing otherwise let a concrete `Nat.mul` partially fire against a symbolic
  index and turned a 14.8 s build into a 1 GiB release-mode stack overflow.
- **`Type`, not `Prop`, for data-carrying structures.**
  `CReal.UniformConvergesOn` is a one-constructor `Type` because
  `uniform_limit_uniformly_continuous` must CONSTRUCT a `UniformlyContinuousOn`
  whose `modulus` needs the rate as literal `Nat`-building data.

**Sound in the other direction**: `Exists.rec` IS available for proving a
PROPOSITION about a construction — `Nat.le_dest` + `Exists.rec` proved a
`polyDegreeLt` precisely because the target `Equiv (f i) zero` is a `Prop`.

### 3b. Two congruence regimes — an undocumented API fork

- **Unrestricted**: `CRealPrelude::sum_range_congr` demands
  `forall i, Equiv (f i) (g i)` with no domain condition.
- **Bounded**: `integral.rs`'s file-local `sum_range_congr_lt_proof` /
  `bounded_equiv_pointwise`, congruence only below an index bound.

`riemannSum_split_exact_of_uc` HAD to route through the bounded analogue,
because a `UniformlyContinuousOn` witness says nothing outside `[a,b]` — so the
global congruence the public lemma wants is not merely unavailable, it is FALSE
for an arbitrary witness. That is not a gap; it is the correct statement of the
situation, and `CReal.congrOfUniformlyContinuous` is deliberately
domain-restricted for the same reason.

**Rule**: reach for the bounded regime whenever the congruence source is a
domain-scoped witness (uniform continuity, integrability); reach for the
unrestricted one only when `f` and `g` are congruent everywhere by
construction. The congruence deriver (`creal/congruence.rs`, 7.62 ms per
composite) mechanizes the REGISTERED-op composites in the unrestricted regime;
it does not cover an opaque `F`.

## 4. Smaller decisions worth making explicitly

- **`axreal`** carries 30 axioms with `originated = 0`: declared, never
  reached. Decide it as either the deliberate negative control that
  axiom-freedom measurements are read against (ADR-0515's role) or as dead
  weight to delete. Right now it is neither, by default.
- **ADR-0603's graded statement family** covers IVT and EVT. **MVT, LUB /
  completeness, Taylor remainder, and FTA each deserve their four rows stated
  explicitly** — general constructive form, boundary refutation, exact
  decidable-fragment form, labeled import.
- **Suite wall-clock** (`creal::` 313 s, `complex::` 361 s, one concrete
  degree-2 kernel check 356 s) is trending toward a publication gate. Not
  urgent this week; will be.
