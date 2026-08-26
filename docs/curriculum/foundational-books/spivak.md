# Spivak, *Calculus* — the spine, and three routes through it

> **2026-08-25 amendment.** This note originally covered Chapter 1 only, split
> two ways: *solver-decidable* versus *Lean-horizon*. That split is now
> misleading, because most of the analysis has arrived by a **third route** the
> note did not name — the constructive kernel (`CReal`, a Bishop setoid,
> trusted surface 0). The full-spine map is at the bottom; the original
> Chapter-1 material below is unchanged and still accurate.
>
> The important correction: **"Lean-horizon" reads as "not yet", and for
> Chapter 7 it is closer to "not ever, in this logic."** See the spine table.

# Spivak, *Calculus* — Chapter 1 through the Decidability Lens

Spivak's Chapter 1, "Basic Properties of Numbers," founds the whole book on the
**ordered-field axioms P1–P12** and a few **foundational inequalities**. This is
the part of Spivak axeyum can actually *check* — the order axioms are linear
(LRA) and the inequalities are fixed-degree polynomial (NRA / real-closed
fields). Chapters 2+ (limits, continuity, derivatives, integrals, series) are
ε-δ and **Lean-horizon**. Worked as
`crates/axeyum-solver/tests/spivak_inequalities.rs`.

## The ordered-field axioms (P1–P12)

| Axiom | Statement | Class |
|---|---|---|
| P1 | `a + (b + c) = (a + b) + c` | LRA (equational) |
| P2 | `a + 0 = a` | LRA |
| P3 | `a + (−a) = 0` | LRA |
| P4 | `a + b = b + a` | LRA |
| P5 | `a · (b · c) = (a · b) · c` | NRA (products) |
| P6 | `a · 1 = a` (`1 ≠ 0`) | LRA |
| P7 | `a ≠ 0 ⇒ a · a⁻¹ = 1` | NRA |
| P8 | `a · b = b · a` | NRA |
| P9 | `a · (b + c) = a·b + a·c` (distributivity) | NRA |
| P10 | trichotomy: exactly one of `a∈P`, `a=0`, `−a∈P` | LRA |
| P11 | `a,b ∈ P ⇒ a + b ∈ P` | LRA |
| P12 | `a,b ∈ P ⇒ a · b ∈ P` | NRA |

The order axioms (P10–P12) and their linear consequences — e.g. transitivity
`a < b ∧ b < c ⇒ a < c` — are proved with a **re-checked Farkas certificate** via
the `prove` front door.

## The Chapter-1 inequalities

Measured against `crates/axeyum-solver/tests/spivak_inequalities.rs` and the
focused SOS evidence/reconstruction suites:

| Inequality | Statement | Class | axeyum verdict (measured) |
|---|---|---|---|
| Order transitivity | `a<b ∧ b<c ⇒ a<c` | LRA | **Proved** (Farkas, re-checked) ✓ active test |
| Monotonicity (threshold-1) | `x≥1 ∧ y≥1 ⇒ x·y≥1` | NRA | **Proved** by NRA ✓ active test |
| Triangle inequality | `\|a+b\| ≤ \|a\|+\|b\|` | LRA + abs case split | not pinned by the focused Spivak regression; do not infer a proof claim from other LRA coverage |
| Square nonnegativity | `a² + b² ≥ 2ab` (`(a−b)²≥0`) | NRA (degree 2) | **Proved**; active NRA regression, checked SOS/PSD evidence, and kernel-reconstructed supported form |
| AM–GM, n=2 (sqrt-free) | `(a+b)² ≥ 4ab` | NRA (degree 2) | covered by the degree-2 SOS/PSD route; focused evidence and reconstruction tests include the two-variable sum form |
| Bernoulli, fixed n=2 | `(1+x)² ≥ 1+2x` (`x²≥0`) | NRA (degree 2) | algebraically in the SOS class, but not a named Spivak regression cell; keep the claim at route level |
| Cauchy–Schwarz, n=2 | `(a₁b₁+a₂b₂)² ≤ (a₁²+a₂²)(b₁²+b₂²)` | NRA (degree 4) | outside the degree-2 SOS certificate; no Spivak-specific checked-proof claim |
| Bernoulli, ∀n | `(1+x)ⁿ ≥ 1+nx` | induction | **Lean-horizon** |
| AM–GM, general n | `(Σaᵢ)/n ≥ (Πaᵢ)^{1/n}` | induction + roots | **Lean-horizon** |

## Findings, and what was fixed (measured, not assumed)

1. **LRA→NRA dispatch — FIXED (#14).** The `prove`/`produce_evidence` front door
   used to reject a nonlinear real goal as `Unsupported`; it now falls back to
   the NRA engine (`produce_nra_evidence`) when the linear route hits a nonlinear
   product. Pinned by `prove_dispatches_nonlinear_real_to_nra`; the soundness
   probe `nra_must_not_claim_x_squared_negative_is_sat` confirms NRA doesn't
   return a spurious model on the way.
2. **NRA wall-clock timeout — FIXED (#15).** NRA's spatial branch-and-bound had
   no deadline (only a magnitude bound), so it could run far past the configured
   budget (the `a²+b²≥2ab` / AM–GM cases hung 60s+). A `deadline` is now threaded
   through `branch_and_bound` and the per-box refinement loop, so the engine bails
   to `Unknown` promptly. The frontier test `square_nonnegativity_is_the_nra_frontier`
   is now active (returns `Unknown` in ~5s instead of hanging).
3. **The degree-2 SOS frontier moved.** Axeyum now extracts a quadratic form,
   checks an exact rational LDL-transpose/PSD certificate, and reconstructs
   selected two- and three-variable AM–GM forms through the Lean-core checker.
   The remaining frontier is broader: higher-degree Positivstellensatz-style
   evidence, general CAD proof production, and source-bound reconstruction for
   polynomial shapes outside the admitted SOS slice.

## Why this matters for axeyum

Spivak Chapter 1 is, quite literally, a curriculum of ordered-field and
fixed-degree-polynomial reasoning — i.e. a hand-curated **LRA + NRA benchmark**
of foundational, human-meaningful theorems. It exercises exactly the arithmetic
the proof track cares about, and it cleanly separates checked LRA/SOS evidence,
decision-only or incomplete NRA routes, and the Lean horizon.


---

# The spine, end to end (measured 2026-08-25)

Three routes, not two:

- **S — solver-decidable.** LRA/NRA/SOS with a re-checked certificate. This is
  what the Chapter-1 material above covers.
- **K — constructive kernel.** Proved in `axeyum-lean-kernel` over `CReal`,
  axiom-free. Most of the analysis lives here.
- **X — unavailable in this logic.** Not a gap in effort; the classical
  statement is not constructively provable, and the entry names its
  constructive substitute.

Counts are `CReal.*` declarations matching the topic, from
`prelude_theorem_inventory --release --include-constructed`.

| Spivak | Topic | Route | State |
|---|---|---|---|
| 1 | Ordered-field axioms P1–P12, inequalities | **S** | table above; `spivak_inequalities.rs` |
| 2 | Induction, binomial theorem | **K** | `Nat.add_pow`, `Complex.add_pow` |
| 3–4 | Functions, graphs | — | no carrier needed |
| 5 | Limits | **K** | 11 `converges_*`, incl. `converges_of_cauchy`, `converges_unique`, `converges_squeeze` |
| 6 | Continuous functions | **K** | 9 `continuous_*` / `uniformly_continuous_*` |
| **7** | **"Three Hard Theorems"** — IVT, EVT, boundedness | **X → K** | **IVT: closed.** `ivt_approx` proved; `ivt_bisect` is data-valued (one `Nat.rec` into `Bool → CReal`) with a proven invariant. An **exact** root is refuted, not merely unbuilt — two kernel-computed counterexamples: a stationary endpoint freezes its slack, and `F := id` on `[−1,2]` converges to `1/2` where the root is `0`. **EVT: unavailable** (an attained maximum is not constructive). **Boundedness: in flight** — `bucketIndexFloorLower`/`Upper` landed, sandwiching the clamped sample between grid points **with no sign hypothesis** (`q ≥ 0` holds unconditionally via `Rat.le_max_right`) |
| 8 | Least upper bounds | **X → K** | classical LUB unavailable; **Bishop completeness** proved instead (`creal/completeness.rs`): every regular sequence of reals has a limit, *constructed* |
| 9–10 | Derivatives, differentiation rules | **K** | 17 `hasDerivative_*` incl. `_chain`, `_mul`, `_pow`, and **`_unique`** — which needs `lt a b`: without it the naive statement is FALSE (at `a = b` the spec is vacuous, so `const zero` and `const one` are both derivatives of `id`) |
| **11** | Significance of the derivative (MVT) | **X → K** | MVT unavailable (rests on EVT); **`monotone_of_nonneg_deriv` proved without it**, by direct subdivision. Also `constant_of_zero_deriv`, `antitone_of_nonpos_deriv`, **`strict_mono_of_pos_deriv`**, `strict_injective_of_pos_deriv`, `strict_antitone_of_neg_deriv`, `strict_mono_comp`, and the **rate**: `strict_mono_magnitude` + `scale_cancel_le` → `diff_le_of_strict_mono_magnitude` (`|x−y| ≤ 2(k+1)(|Fx|+|Fy|)`). `scale_cancel_le` deliberately avoids `le_of_mul_le_mul_left`'s `PosBound`/`inv` machinery by exploiting that `ofNat n` is **defeq** to `ofRat (natDivSucc n 0)` |
| 12 | Inverse functions | **K / X** | `order_reflect_of_pos_deriv` ✓ (needs `Apart` as data). **Order PRESERVATION is reachable; order REFLECTION is exactly as hard as an exact IVT preimage** — both convert a codomain fact into domain position information |
| 13 | Integrals | **K** | **4 of 5 steps done**, each easier than the last. (1) `samplePoint_reblock` — the sample-point bridge, **unconditional**, no index bound needed. (2) `Nat.mul_succ_add_lt_of_le_of_lt` — row-major index flattening, no induction. (3) `reblockBlock_eq_fineBlockSum` — the per-block fold, an **exact `Equiv`**, no error term, so nothing accumulates from below. (4) `riemannSum_reblock_close` — the outer fold, carrying only `fineBlockSum_close`'s own `±eps`. (5) open: the Archimedean instantiation discharging `Nat.le deep m`, then `within_of_two_sided_le`. The obstruction that shaped all of it: `CReal → CReal` functions are **not automatically `Equiv`-respecting** in this setoid (ADR-0512) |
| 14 | Fundamental Theorem of Calculus | — | open, downstream of 13 |
| 15–17 | Trig, π irrational, planetary motion | — | open; no transcendental functions exist |
| 18 | Log and exp | **K** | partial — `expTerm`, `expSeriesPartial`, `expTerm_le_geom`, and the domination chain ending at `exp_term_abs_le_dominant`, the exact `abs`-shaped form `sumRange_cauchy_of_dominated` consumes. `Rat.pow_natDivSucc_two` (in `rat_prelude/pow_bridge.rs`) closed the representation gap. **The whole bridge is `inv`-free** — `geom_pair_within`'s `inv`-based machinery is not involved, sidestepping the decided-apartness problem. Note the numerators genuinely differ (`normalize 2 (2ⁿ)` vs `normalize 1 (2ⁿ)`): the factor of 2 is real work via `normalize_mul_normalize`, not a free identification. `e` itself open — one declaration broke the prelude build and was reverted with a precise bisection target |
| 20 | Taylor polynomials | — | open |
| 21 | `e` is irrational | — | open (√2's irrationality **is** proved, `Nat.no_rational_sqrt_two`) |
| 22–23 | Sequences and series | **K** | comparison test, dominated convergence, telescoping, geometric tail bounds |
| 24 | Uniform convergence, power series | — | open |
| 25–27 | Complex numbers and functions | **K** | ~1,000 `Complex.*` declarations; field, `conj`, `normSq`, roots of unity, Ptolemy, `add_pow`, `mul_sub_one_geom`; conjugation now closed over the ring and division: `conj_zero`, `conj_one`, `conj_pow`, `conj_div`, `div_congr`. `Complex.exp`/`abs`/`arg` absent — all gated on a general `CReal.sqrt`, itself an open climb. **FTA needs polynomial infrastructure that does not exist at all** |
| 28 | Fields | **K** | `Rat`, `CReal`, `Complex` field laws |
| **29** | **Construction of the real numbers** | **K** | **`CReal` *is* this** — Bishop setoid over constructed rationals, trusted surface 0 (ADR-0512) |
| 30 | Uniqueness of the reals | — | open (needs LUB, so likely **X**) |

## Chapter 7 is the constructive fault line, and that is not a coincidence

Spivak titles Chapter 7 "Three Hard Theorems" for pedagogical reasons — they are
the first results in the book that genuinely need completeness. They are also,
almost exactly, the theorems that **fail constructively**:

- **IVT** asserts a root. No algorithm produces one in general: the root's
  location can be made to depend on an undecidable comparison. The constructive
  replacement is the **approximate IVT** (`∀ε ∃x, |f x| ≤ ε`), proved by
  trisection with an overlap using **`CReal.lt_cotrans`** — Bishop's replacement
  for trichotomy, which exists here precisely because `lt_total` does not.
- **EVT** asserts an *attained* maximum. Constructively one gets a supremum only
  under extra hypotheses, and attainment is exactly what is lost.
- **Boundedness** on `[a,b]` is available for **uniformly** continuous
  functions — which is why `UniformlyContinuousOn`, not pointwise continuity, is
  the hypothesis Chapters 13 and 14 run on here.

**MVT (Ch 11) inherits the problem** — it is proved classically via EVT. That is
why `monotone_of_nonneg_deriv` was proved by direct subdivision instead, and why
a brief attempting it must say *do not try to prove MVT first*.

So the `X` rows are the interesting ones. A reader who sees "0" there and infers
missing effort has it backwards: those zeros are where the logic is speaking.


## Postscript: the one lemma that gated six chapters

Measured across this session, Chapters **7, 12, 18, 21, 22 and 23** were all
blocked on a single estimate — `pow half n ≤ 1/(n+1)`, geometric decay
dominating harmonic rate. Its *rational* form already existed
(`Rat.bernoulli_harmonic_bound`, a **Chapter 2** result); only the transport to
`CReal` was missing.

Two things about how that was found are worth keeping.

**No single lane could see it.** Each arrived independently — the IVT lane
needed it to turn "`N` halvings" into "width small enough"; the `e` lane needed
a decay rate for its `1/n! ≤ 2·(1/2)ⁿ` domination; the geometric lane needed it
for `geom_pair_within`'s undischarged leaf. Three reports of *where a lane
stopped*, converging on one cause.

**The obvious route was refuted before it was attempted.** A lane established
that there is no samples-level bridge from `seq (CReal.pow x a) b` to `Rat.pow`
of a sample of `x`: `CReal.mul`'s shift is `bound x + bound y + 1`, so unrolling
`pow` nests `bound(pow x j)` **recursively**, and no closed-form index exists.
The route that works stays entirely at the `CReal` level —
`pow (ofRat q) n ~ ofRat (Rat.pow q n)` by induction — because `Equiv` is a
statement about the reals, not about their representatives. That distinction is
the general lesson: **an argument phrased about representatives inherits the
sampling schedule; one phrased about the setoid does not.**

## Postscript II: a cited blocker is often older than the code that removed it

Three times in one session a lane found that the obstacle its brief or a module
doc named had already been dissolved by unrelated work, by someone who never
knew what they were unblocking.

- `exponential.rs`'s module doc gave two routes to `Cauchy (sumRange expTerm)`
  and stated **"neither is built."** By then a later lane had landed
  `CReal.ofRat_pow` and `pow_half_le_natDivSucc` in `geometric.rs`, which is
  most of route (a). The doc had stopped the work it described for weeks.
- `Complex.conj_div`'s `PosBound` transport was briefed as "the whole
  difficulty" on the previous lane's own analysis. `Complex.pos_bound_conj`
  already existed and transported at the **same `k`**, collapsing it to one
  call.
- Chapter 7's boundedness was expected to need a sign hypothesis on `w`. It does
  not: `q ≥ 0` holds unconditionally via `Rat.le_max_right`, which is exactly
  what makes `natAbs (num q)` an *exact* read rather than a bounding one.

The pattern is structural, not careless. A doc records the frontier **at the
moment it was written**, and in a repository with several lanes running it goes
stale in hours — while reading exactly like a current statement of fact. The
cost is asymmetric: a stale "this is impossible" note suppresses attempts
silently and forever, whereas a stale "this is easy" note is corrected by the
first lane that tries.

So: **before building machinery to get around a documented blocker, check
whether it is still there** — read the inventory, not the prose. And when a lane
finds a doc wrong, correcting the doc is part of the deliverable, not a
courtesy. Two of the three above were corrected in the same commit that used
the finding; the third is this note.
