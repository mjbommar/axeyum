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

**FOUR routes, not three. Corrected 2026-08-31 — this legend said "Three
routes, not two" and omitted the CAS, and that omission produced a wrong
answer.** Asked how much of Spivak is done, I read this table's route column
and reported the `X` rows as terminal. They are not: `X` is **row 1's**
verdict under ADR-0603, and the CAS supplies **row 3** — the exact CLASSICAL
statement on the decidable fragment. `crates/axeyum-cas` is **72,008 lines,
363 public functions across 53 modules**, and before this correction the
string `axeyum-cas` appeared in this file exactly ONCE (the MVT row) against
28 mentions of `CReal`.

- **S — solver-decidable.** LRA/NRA/SOS with a re-checked certificate. This is
  what the Chapter-1 material above covers.
- **K — constructive kernel.** Proved in `axeyum-lean-kernel` over `CReal`,
  axiom-free. Most of the analysis lives here.
- **C — CAS, decidable fragment (ADR-0603 row 3).** The exact classical
  statement, decided where it is decidable, with a re-checkable certificate.
  `polynomial_mvt` + `verify_mvt_certificate` (`axeyum-cas/src/mvt.rs`) is the
  full classical MVT with `c` named as a `RealAlgebraic`; the ledger carries
  **46 `cas-certificate` facts**. A `C` entry is NOT a weaker consolation for
  a failed `K` — it decides the classical statement that `K` cannot, on a
  fragment where the question is decidable, and ADR-0603's whole argument is
  that row 1 is optimal *because* row 2 refutes the general form while row 3
  still settles the decidable one.
- **X — unavailable in this logic.** Not a gap in effort; the classical
  statement is not constructively provable, and the entry names its
  constructive substitute. **`X` describes row 1 only.** Read the `C` column
  and [`graded-statement-families.md`](../graded-statement-families.md) before
  concluding a chapter is out of reach.

**The route column below is being audited chapter by chapter against the CAS's
363 public functions; until that lands, a blank `C` means UNAUDITED, not
absent.**

Counts are `CReal.*` declarations matching the topic, from
`prelude_theorem_inventory --release --include-constructed`.

| Spivak | Topic | Route | State |
|---|---|---|---|
| 1 | Ordered-field axioms P1–P12, inequalities | **S** | table above; `spivak_inequalities.rs` |
| 2 | Induction, binomial theorem | **K** | `Nat.add_pow`, `Complex.add_pow` |
| 3–4 | Functions, graphs | — | no carrier needed |
| 5 | Limits | **K** | 11 `converges_*`, incl. `converges_of_cauchy`, `converges_unique`, `converges_squeeze` |
| 6 | Continuous functions | **K** | 9 `continuous_*` / `uniformly_continuous_*` |
| **7** | **"Three Hard Theorems"** — IVT, EVT, boundedness | **X → K** | **Two of three closed, and the third is refuted rather than open.** **IVT: closed** — `ivt_approx` proved, `ivt_bisect` data-valued with a proven invariant. An *exact* root is **refuted**, not merely unbuilt: two kernel-computed counterexamples (a stationary endpoint freezes its slack; `F := id` on `[−1,2]` converges to `1/2` where the root is `0`). **Boundedness: proved** — `bounded_of_uniformly_continuous` with a **computed** `K = succ(succ(bound(F a)) + (succ(bound(b−a))+2)·succ(k))`, `k := rescale_index(3, modulus 0)`, never `∃ K`. Six lanes; **four landed no theorem** and were as load-bearing as the two that did — one found the boundary-overshoot blocker three predecessors had planned past. **EVT: unavailable** — an attained maximum is not constructive |
| 8 | Least upper bounds | **X → K** | classical LUB unavailable; **Bishop completeness** proved instead (`creal/completeness.rs`): every regular sequence of reals has a limit, *constructed*. **Graded family stated**: [`graded-statement-families.md`](../graded-statement-families.md) §2 — row 2 is **landed** as of 2026-08-31 (`CReal.lub_decides_em`, ADR-1010, `F:creal-lub-decides-em`): a Bishop supremum for `CReal.lubSet A := fun x => Or (le x zero) (And A (le x one))` yields `Or A (Not A)` for an arbitrary `Prop`, i.e. UNRESTRICTED excluded middle — a strictly stronger boundary than the analytic LLPO IVT's and EVT's rows reach. (This row previously read "the unavailability is asserted, not proved"; that was accurate until row 2 landed.) Row 1 also gained `CReal.supOn` + `supOn_ub` + `supOn_approx_lub` on 2026-08-30; `extremum::polynomial_extremum` gives row 3 for the polynomial-range special case |
| 9–10 | Derivatives, differentiation rules | **K** | 17 `hasDerivative_*` incl. `_chain`, `_mul`, `_pow`, and **`_unique`** — which needs `lt a b`: without it the naive statement is FALSE (at `a = b` the spec is vacuous, so `const zero` and `const one` are both derivatives of `id`) |
| **11** | Significance of the derivative (MVT) | **X → K** | MVT unavailable (rests on EVT); **`monotone_of_nonneg_deriv` proved without it**, by direct subdivision. Also `constant_of_zero_deriv`, `antitone_of_nonpos_deriv`, **`strict_mono_of_pos_deriv`**, `strict_injective_of_pos_deriv`, `strict_antitone_of_neg_deriv`, `strict_mono_comp`, and the **rate**: `strict_mono_magnitude` + `scale_cancel_le` → `diff_le_of_strict_mono_magnitude` (`|x−y| ≤ 2(k+1)(|Fx|+|Fy|)`). `scale_cancel_le` deliberately avoids `le_of_mul_le_mul_left`'s `PosBound`/`inv` machinery by exploiting that `ofNat n` is **defeq** to `ofRat (natDivSucc n 0)`. **Graded family stated**: [`graded-statement-families.md`](../graded-statement-families.md) §1 — row 2's "MVT rests on EVT" is an inherited, not a dedicated, refutation, and EVT's own row 2 is itself only "in progress" (a separate lane is building that refutation in `creal/extreme_value.rs`, not yet landed); **row 3 (`polynomial_mvt`/`verify_mvt_certificate`, `crates/axeyum-cas/src/mvt.rs`) landed 2026-08-27** — the full classical MVT on the decidable fragment, `c` named as a `RealAlgebraic`, CAS-internal only pending kernel reconstruction |
| 12 | Inverse functions | **K / X** | Order PRESERVATION (`strict_mono_of_pos_deriv`, Ch11) and CONDITIONAL order-reflection (`order_reflect_of_pos_deriv` ✓, needs `Apart` as data) were already landed. **Landed this session: `inverse_lipschitz_of_pos_deriv`** ✓ — the CONTINUITY-of-the-inverse statement, `Apart x y → abs(x−y) ≤ (2k+2)·abs(F x − F y)`, composing `strict_mono_magnitude`+`scale_cancel_le` (Ch11) with `abs_le`. Unlike `order_reflect_of_pos_deriv` it needs NO codomain hypothesis at all — it bounds the domain gap in BOTH directions from `Apart` alone, which is what makes it continuity rather than a restatement of order-reflection. **What remains is genuinely gated on an exact IVT preimage**: an actual inverse FUNCTION (not just a bound relating gaps) needs producing, for a given `F x0`, an actual point `x0` back out of the codomain value — exactly the exact-root construction `creal/ivt.rs` refutes rather than leaves open (two kernel-computed counterexamples). So Ch12's "the inverse function is continuous" is now fully covered constructively; "the inverse function is [differentiable / exists as a `CReal → CReal`]" is not reachable without solving that already-refuted problem |
| **13** | **Integrals** | **K** | **CLOSED, and `CReal.integral` now EXISTS.** `CReal.riemannSum_cauchy` → the representative-index bridge (`sharedIndexToCanonical`) → the common-refinement construction → **`CReal.integral`**, built on the `deep`-reindexed sequence (`e := n` directly, never inverting a general modulus). Both concerns this row previously named are resolved. It is proved **witness-independent** (`integral_witness_independent`) — the value does not depend on which convergence witness is supplied — and carries its algebra: `integral_const`, `integral_add`, `integral_le`, `integral_scale`, `integral_converges`, and **`riemannSum_integral_close`** (a Riemann sum at sufficient depth sits within an explicit `e`-derived distance of the integral). Thirteen lanes; the estimate's first version cost **74 s on every prelude build** by forcing a full `Definition` unfold, caught pre-publication by bisecting the declaration by legs. Registered in the fact ledger as `F:creal-integral` and nine siblings |
| **14** | **Fundamental Theorem of Calculus** | **K (partial)** | The integral's **algebra is complete** (row 13). What remains is **`CReal.integral_split`** — additivity over an interval split — and it is blocked on exactly **two** named facts, not on effort. **The `riemannSum` version is FALSE at fixed mesh count**, with a kernel-computed counterexample (`m := 0`, `f := id`, `a,c,b := 0,1,3`: the whole is `0`, the halves give `0 + 2 = 2`); only the LIMIT is additive. Every existing 'combine several riemannSums' construction is `Nat`-refinement algebra over **one fixed interval** and cannot be rearranged, because that relation does not exist algebraically for a general `c`. **(1) An Archimedean crossing index — LANDED** (`CReal.crossingIndex`/`crossingUpper`/`crossingLower`, a *slack* variant; the tight bracket is not constructible, since deciding which side of an exact crossing `c` falls on IS the undecidable comparison). **(2) A cross-width term-by-term Riemann comparison via uniform continuity** — in progress. A doc objection that `converges_unique` needs both facts to name the syntactically same sequence was **dissolved**: `le_of_forall_le_add_small` / `equiv_zero_of_small` prove an `Equiv` from an arbitrary-accuracy rational bound with no shared sequence at all |
| **15–17** | **Trig, π irrational, planetary motion** | **K (opened)** | **This row's previous claim — "no transcendental functions exist" — is no longer true.** **`CReal.cosOne` is constructed**: `cos 1 = Σ(-1)^k/(2k)!`, built via `CReal.mk` on an explicit regular sequence, never `Exists`-elimination, mirroring `e`. Its index is doubled as `Nat.add k k` (**not** `Nat.mul 2 k`) so `CReal.pow_add` applies with zero reduction bookkeeping, and its domination series is *literally* `expDominant` — the same one `e` uses — so no new domination argument was needed. Two claims I briefed were wrong and the lane checked both: the absolute-convergence bridge is unnecessary (`sumRange_cauchy_of_dominated` never required nonnegativity, only a bound on `abs (f k)`, so it already covers a SIGNED series), and no parity case split is needed (`abs (pow (neg one) k) ≤ one` goes by induction). **Still out of reach: general `sin`/`cos : CReal → CReal`** (needs a bound depending on `\|x\|`, i.e. power series — see row 24) and **π**, which is downstream of a root of `cos` and therefore of the exact-root construction `creal/ivt.rs` **refutes** |
| **18** | **Log and exp** | **K** | **`CReal.e` is constructed** — via `CReal.mk` on an explicit regular sequence, never `Exists`-elimination. Five lanes: `expTerm`/`expSeriesPartial` → `expTerm_le_geom` → `Rat.pow_natDivSucc_two` (the representation bridge) → the closed form, after a bisect found **one stray `equiv_symm`** reversing a chain link → `cauchyOfPointwiseEquiv` → `expDominantCauchy` → **`e`**. The whole domination bridge is **`inv`-free**. **`2 ≤ e ≤ 3` is now PROVED** (`CReal.two_le_e`, `CReal.e_le_three`, plus the looser but uniform-in-`n` `CReal.e_le_four`), once `CReal.sumRange_mono_outer` supplied the missing outer-index monotonicity this row previously called for. `two_le_e` needs an EVENTUAL argument (`converges_lower_bound_shift`, since `expSeriesPartial 0 = 0 < 2`); `e_le_three` needs a genuine `{0, 1, k+2}` case split — the index-2 kink is mathematical, not an artifact — while `e_le_four` is one uniform bound at every `n` |
| 20 | Taylor polynomials | — | open. **Graded family stated**: [`graded-statement-families.md`](../graded-statement-families.md) §3 — row 1 (integral-form remainder) is sized but not started, blocked on an n-fold `hasDerivative` package that does not exist; row 2 is not merely absent, it is undecided which statement would need refuting; the CAS `series` route (row-3-shaped) answers a weaker question (truncation identity, no error bound) |
| 21 | `e` is irrational | — | open — but **`CReal.e` now exists** (see Ch 18), so this is downstream of a constructed object rather than of nothing. √2's irrationality **is** proved (`Nat.no_rational_sqrt_two`) |
| **22–23** | **Sequences and series** | **K** | comparison test (nonnegative series, `0 ≤ a k ≤ b k`), dominated convergence, telescoping, geometric tail bounds, **`geomCauchy`** — `Cauchy (sumRange (pow half ·))` — and **`sumRange_cauchy_of_abs_cauchy`/`sumRange_converges_of_abs_converges`** (absolute convergence implies convergence, landed this session), which is what makes the comparison test usable on a SIGNED series. **The "exactly two declarations" `inv`-containment claim this row previously made was undercounted, corrected here: `CReal.inv` is directly built by SIX declarations along `geomCauchy`'s own dependency chain** — four in `geometric.rs` (`geom_tail_bounded_div`, `geom_tail_within`, `geom_tail_within_le`, `geom_pair_within`, all pre-existing infrastructure for the quotient-form tail bound `tail ≤ xᵐ/(1−x)`) plus the two in `exponential.rs` this row already named (`geomHalfInvLeafBound`, `geomCauchyOrderedHalf`) that consume `geom_pair_within` at the concrete base `1/2`. `geomCauchy` itself constructs no `inv` term directly. **Ratio test and `e` irrational (Ch21): assessed, not built** — see below . **Landed since: the RATIO TEST.** `CReal.geomCauchyOfLt` generalizes geometric convergence from the literal base ½ to any `0 ≤ x < 1` — the half-case's literal coincidence `3+4=7` cannot survive a symbolic bound, so both sides pad to a common target through `Rat.natDivSucc_le_add_left` and `Rat.natDivSucc_add` rather than by defeq reduction. Then `CReal.geomScaledCauchyOfLt` and **`CReal.sumRangeRatioTest`**. The general route was cross-checked against the base-½ one at `x := half`, **against `geomCauchy`'s own stored type fetched from the kernel** rather than a hand-reconstruction, with a negative control confirming the agreement is not vacuous — it passed first try. Composition proved simpler than sized: **no absolute-convergence bridge is needed**, because `sumRange_cauchy_of_dominated`'s hypothesis is already stated on `abs (f k)`, so it covers a signed series directly. Two lanes discovered that independently, against my brief |
| 24 | Uniform convergence, power series | — | open |
| 25–27 | Complex numbers and functions | **K** | ~1,000 `Complex.*` declarations; field, `conj`, `normSq`, roots of unity, Ptolemy, `add_pow`, `mul_sub_one_geom`; conjugation now closed over the ring and division: `conj_zero`, `conj_one`, `conj_pow`, `conj_div`, `div_congr`. **Corrected 2026-08-27, kernel-measured stale within 48h of writing**: `CReal.sqrt` now EXISTS (landed 2026-08-23, total, axiom-free) and `Complex.abs` is built on top of it — `abs_nonneg`, `abs_congr`, `abs_one`, `abs_mul`, and (landed 2026-08-26) **`abs_add_le`, the modulus triangle inequality**, are all proved. Only `Complex.exp`/`arg` remain absent. <!-- absent: Complex.exp, Complex.arg --> **FTA needs polynomial infrastructure that does not exist at all** . **The 'polynomial infrastructure that does not exist at all' now exists**: `Complex.polyEval`, `polyAdd`, `polyScale`, `polyDegreeLt` and the two **evaluation homomorphisms** (`polyEval_polyAdd`, `polyEval_polyScale`), proved symbolically. Representation is a coefficient function `Nat → Complex` plus an explicit bound — this kernel has no `List`, so it mirrors `Rat.polyEval` — and the bound is deliberately **not** a computed degree, because `Complex.Equiv` is undecidable so no coefficient can be tested for zero. `polyEval` is sum-of-monomials, not Horner: Horner needs highest-coefficient-first processing, i.e. a countdown `Nat.sub` inside a recursion, which is this kernel's documented concrete-witness trap. **`polyMul` was blocked as of the previous measurement; it is not anymore (corrected 2026-08-27, landed same day)**: the naive convolution is the correct truncated coefficient only if both factors vanish beyond their bound, and `Complex.sumRange_mul_eq_diag_add_corner`'s own doc still correctly records that the identity WITHOUT its corner term is **false**, refuted at n=2 — but the hypothesis-carrying version, `Complex.polyMul` plus `polyDegreeLt_polyMul` and `polyEval_polyMul` (the padded evaluation homomorphism), is now proved. FTA itself is still not built — see [`graded-statement-families.md`](../graded-statement-families.md) for the full four-row account, including why row 3 (root isolation over ℂ) is a genuinely missing algorithm, not an assembly gap |
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

## Postscript III: absolute convergence landed; the ratio test and `e`
irrational, precisely sized

Chapters 22–23's comparison test (`CReal.sumRange_comparisonTest`) only ever
took a NONNEGATIVE series, `0 ≤ a k ≤ b k` — it cannot be applied to a series
that changes sign. **`CReal.sumRange_cauchy_of_abs_cauchy` /
`CReal.sumRange_converges_of_abs_converges`** close that gap: `Cauchy (sumRange
(fun k => abs (f k))) → Cauchy (sumRange f)`, and the `Converges`/`Exists` form
that composes directly with `sumRange_comparisonTest`'s own output (apply it at
`fun k => abs (a k)` against a dominating `b`, then feed the result through
this theorem to reach `Converges (sumRange a)` for a signed `a`). Both are pure
corollaries of the already-proved `sumRange_cauchy_of_dominated`, taken at
`g := abs ∘ f` — the pointwise hypothesis is `le_refl (abs (f k))` after one
beta reduction, so this needed no new real-analysis content, and neither
declaration touches `CReal.inv`.

Two candidate targets were assessed and NOT built, for reasons specific enough
to act on:

- **The ratio test.** `CReal.le` is not decidable and `CReal.inv` needs a
  *witnessed* `PosBound` (a rational modulus `k` plus a proof every sample from
  `k` on is `≥ 1/(k+1)`), so the classical `f(n+1)/f(n) ≤ r < 1` statement is
  not directly expressible without first manufacturing that witness for every
  `n` — exactly the obstacle `geometric.rs`'s own module documentation already
  names for the quotient-form tail bound (`0 ≤ x` says nothing about how close
  `x` is to `1`; a `PosBound` has to be carried as data, not derived). The
  reachable statement is almost certainly the **multiplicative** form this row
  previously flagged — `(∀n, le (mul r (f n)) (f (succ n))) → …`, `r` a fixed
  rational with `0 ≤ r < 1`, avoiding `inv` entirely by never dividing — proved
  by comparison against a geometric series built by `r`-scaled induction on
  `f 0`, the same shape `geom_sum_bounded`/`geom_tail_bounded` already use.
  This is a genuinely new construction (not a corollary of anything landed this
  session) and was not attempted here; it is sized enough to be a direct next
  task.
- **`e` is irrational (Ch 21).** `CReal.e` now exists with proved bounds
  (`2 ≤ e ≤ 3`, this session — see Ch 18's corrected row). The classical proof
  multiplies by `n!` and argues the tail becomes an integer plus a strictly
  fractional remainder in `(0, 1)` for every `n` past some point — an
  INTEGRALITY argument with no analogue anywhere in this development. Nothing
  here connects a `CReal` built from a `sumRange` of rationals back to `Nat`/
  `Int` divisibility facts about the partial sums' denominators; `int_prelude`
  has no theory of `n!·e`'s fractional part, and building one is a genuinely
  new piece of arithmetic, not an assembly of existing `CReal` lemmas the way
  this session's addition was. **Assessed as out of reach without new
  machinery, not attempted as a corollary.**
