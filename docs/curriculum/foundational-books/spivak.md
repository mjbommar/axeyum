# Spivak, *Calculus* — the spine, and four routes through it

> **2026-08-31 amendment (title).** This heading said "three routes" and the
> spine table had no `C` column. Both are fixed below; the `C` column is now
> audited chapter by chapter, and a blank one would be a defect rather than a
> claim.

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

**That audit LANDED 2026-08-31 (lane `cas-coverage-audit`).** Every row below
carries a `C` cell that is either a named module and function or the literal
marker **audited — none** with its reason, so **a blank `C` cell is now a
defect, not a claim** — `scripts/check-spivak-cas-column.py` fails on one. What
changed, with the refuted text quoted, is directly under the table.

Counts are `CReal.*` declarations matching the topic, from
`prelude_theorem_inventory --release --include-constructed`.

| Spivak | Topic | Route | C — CAS, decidable fragment (ADR-0603 row 3) | State |
|---|---|---|---|---|
| 1 | Ordered-field axioms P1–P12, inequalities | **S** | `sos::check` re-derives an exact rational SOS certificate artifact independently; `lib.rs::solve_polynomial_inequality` DECIDES a univariate polynomial inequality `p ⋈ 0` by sign chart over isolated real roots, returning the solution set as disjoint exact intervals (it declines when a root is irrational, so endpoints stay exactly representable); `interval_arith::evaluate_polynomial` gives rigorous enclosures. Ledger: `F:cas-difference-of-squares-free-x-kernel-checked` (**kernel-reconstructed**) — the CAS decides `(x+1)(x−1) = x²−1` in its `MultiPoly` normal form AND refutes the `x²+1` variant, both re-decided through `Kernel::add_declaration`. **Not audited:** whether the degree-4 Ch-1 forms (Cauchy–Schwarz n=2) have an SOS artifact — a separate measurement, and this row does not claim it | table above; `spivak_inequalities.rs` |
| 2 | Induction, binomial theorem | **K** | `telescoping::zeilberger` plus the independent `telescoping_check::check_certificate` (creative telescoping; the certificate is checkable by polynomial algebra alone), `gosper::gosper_sum`, `lib.rs::{prove_wz_sum, definite_sum, sum_polynomial}`, and `combinatorics.rs` (Bernoulli, Euler, both Stirling kinds, Bell, partitions, Catalan — each overflow-safe, returning `None` rather than a wrong value). **Nine ledger facts, all `cas-internal`**: `F:binomial-row-sum-two-power`, `F:alternating-binomial-row-sum-zero`, `F:squared-binomial-row-sum-central`, `F:weighted-binomial-row-sum`, `F:cross-binomial-row-sum`, `F:chu-vandermonde-convolution` and `…-recurrence`, `F:apery-numbers-recurrence`, `F:franel-numbers-recurrence` | `Nat.add_pow`, `Complex.add_pow` |
| 3–4 | Functions, graphs | — | `lib.rs::function_parity` decides even/odd/neither by the sound zero-test, and answers `Neither` honestly when it cannot decide; `solve_polynomial_inequality` returns a graph's sign regions as exact intervals; `sets.rs` is real sets as normalized unions of disjoint rational intervals; `geometry.rs` is analytic geometry at exact rational coordinates. No ledger fact | no carrier needed |
| 5 | Limits | **K** | `lib.rs::limit` — **exact limits of univariate rational functions**: continuous evaluation, `0/0` by cancelling common `(x−a)` factors, and `±∞` by degree comparison; it declines (`None`) on a pole, a non-rational or multivariate expression, or overflow. `laurent_series` supplies the principal part and the residue at a pole. That decides Spivak's whole worked-limit class on the rational fragment. No ledger fact — **unregistered capability** | 11 `converges_*`, incl. `converges_of_cauchy`, `converges_unique`, `converges_squeeze` |
| 6 | Continuous functions | **K** | **audited — none.** Measured 2026-08-31: **zero** non-comment lines in `crates/axeyum-cas/src/**/*.rs` mention continuity or uniform continuity (positive control, same comment masking: 548 lines mention `polynomial`). Continuity is definitional on this fragment — the objects are polynomials and rational functions — so nothing here *states* a continuity proposition. `interval_arith` gives rigorous enclosures, which is a different claim | 9 `continuous_*` / `uniformly_continuous_*` |
| **7** | **"Three Hard Theorems"** — IVT, EVT, boundedness | **X → K** | **Both theorems this chapter calls unavailable have an exact CAS route.** `real_algebraic::polynomial_ivt` + `verify_ivt_certificate` — the root is *named* as a `RealAlgebraic` (minimal polynomial irreducible over ℚ plus a Sturm-certified isolating interval), not approximated. `extremum::polynomial_extremum` + `verify_extremum_certificate` — the EVT, with the maximizer an exact algebraic point; the checker **re-isolates `p'`'s roots from scratch and rejects a candidate list of the wrong size**, so completeness is falsifiable rather than asserted. Boundedness follows from the attained max. Ledger, six facts: `F:cas-ivt-cbrt2-in-1-2` and `F:cas-extremum-irrational-argmax` (`cas-internal`); `F:cas-ivt-sign-bracket-cbrt2-kernel-checked`, `F:cas-ivt-degree4-sign-bracket-kernel-checked-cost-curve`, `F:cas-extremum-deriv-sign-bracket-kernel-checked`, `F:cas-evt-endpoint-exclusion-cubic-kernel-checked` (**kernel-reconstructed**). Read [`08-ivt-and-evt-measured-against-mathlib.md`](../../formalized-math-2026-08/08-ivt-and-evt-measured-against-mathlib.md) §'Row 3 — the CAS rows state less than their names suggest' before quoting these: it already records that the *substantive* half is `cas-internal` | **Two of three closed, and the third is refuted rather than open.** **IVT: closed** — `ivt_approx` proved, `ivt_bisect` data-valued with a proven invariant. An *exact* root is **refuted**, not merely unbuilt: two kernel-computed counterexamples (a stationary endpoint freezes its slack; `F := id` on `[−1,2]` converges to `1/2` where the root is `0`). **Boundedness: proved** — `bounded_of_uniformly_continuous` with a **computed** `K = succ(succ(bound(F a)) + (succ(bound(b−a))+2)·succ(k))`, `k := rescale_index(3, modulus 0)`, never `∃ K`. Six lanes; **four landed no theorem** and were as load-bearing as the two that did — one found the boundary-overshoot blocker three predecessors had planned past. **EVT: unavailable** — an attained maximum is not constructive |
| 8 | Least upper bounds | **X → K** | `extremum::polynomial_extremum` returns the **attained** maximum of a polynomial on a closed rational interval, exactly — the least upper bound of that range, reached, on the decidable fragment. `sets.rs`'s normalized disjoint-interval unions carry exact endpoints. **Boundary:** this is the sup of a polynomial's range on `[a,b]`, not the sup of an arbitrary bounded set, so nothing here reaches the general LUB that row 2 refutes | classical LUB unavailable; **Bishop completeness** proved instead (`creal/completeness.rs`): every regular sequence of reals has a limit, *constructed*. **Graded family stated**: [`graded-statement-families.md`](../graded-statement-families.md) §2 — row 2 is **landed** as of 2026-08-31 (`CReal.lub_decides_em`, ADR-1010, `F:creal-lub-decides-em`): a Bishop supremum for `CReal.lubSet A := fun x => Or (le x zero) (And A (le x one))` yields `Or A (Not A)` for an arbitrary `Prop`, i.e. UNRESTRICTED excluded middle — a strictly stronger boundary than the analytic LLPO IVT's and EVT's rows reach. (This row previously read "the unavailability is asserted, not proved"; that was accurate until row 2 landed.) Row 1 also gained `CReal.supOn` + `supOn_ub` + `supOn_approx_lub` on 2026-08-30; `extremum::polynomial_extremum` gives row 3 for the polynomial-range special case |
| 9–10 | Derivatives, differentiation rules | **K** | `CasExpr::differentiate` plus `lib.rs::prove_derivative`, which is a *proof* on this fragment: differentiate, then decide the claimed derivative by the certified zero-test. Vector calculus is present and exact — `gradient`, `jacobian`, `hessian`, `divergence`, `curl`, `laplacian`, `wronskian` — with `forward_difference`/`backward_difference`, `resultant` and `discriminant`. No ledger fact for the differentiation rules themselves | 17 `hasDerivative_*` incl. `_chain`, `_mul`, `_pow`, and **`_unique`** — which needs `lt a b`: without it the naive statement is FALSE (at `a = b` the spec is vacuous, so `const zero` and `const one` are both derivatives of `id`) |
| **11** | Significance of the derivative (MVT) | **X → K** | `mvt::polynomial_mvt` + `verify_mvt_certificate` — the **full classical MVT**, with `c` named as a `RealAlgebraic`. Ledger: `F:cas-mvt-cubic-witness-sqrt3` (`cas-internal`) and `F:cas-mvt-secant-endpoints-kernel-checked` (**kernel-reconstructed**). Note also that `solve_polynomial_inequality` decides `p' ⋈ 0` exactly, so the monotonicity intervals the `K` route reaches by direct subdivision are *computed* here, and `extremum` supplies the Fermat interior-extremum step the classical MVT proof runs on | MVT unavailable (rests on EVT); **`monotone_of_nonneg_deriv` proved without it**, by direct subdivision. Also `constant_of_zero_deriv`, `antitone_of_nonpos_deriv`, **`strict_mono_of_pos_deriv`**, `strict_injective_of_pos_deriv`, `strict_antitone_of_neg_deriv`, `strict_mono_comp`, and the **rate**: `strict_mono_magnitude` + `scale_cancel_le` → `diff_le_of_strict_mono_magnitude` (`|x−y| ≤ 2(k+1)(|Fx|+|Fy|)`). `scale_cancel_le` deliberately avoids `le_of_mul_le_mul_left`'s `PosBound`/`inv` machinery by exploiting that `ofNat n` is **defeq** to `ofRat (natDivSucc n 0)`. **Graded family stated**: [`graded-statement-families.md`](../graded-statement-families.md) §1 — row 2's "MVT rests on EVT" is an inherited, not a dedicated, refutation, and EVT's own row 2 is itself only "in progress" (a separate lane is building that refutation in `creal/extreme_value.rs`, not yet landed); **row 3 (`polynomial_mvt`/`verify_mvt_certificate`, `crates/axeyum-cas/src/mvt.rs`) landed 2026-08-27** — the full classical MVT on the decidable fragment, `c` named as a `RealAlgebraic`, CAS-internal only pending kernel reconstruction |
| 12 | Inverse functions | **K / X** | **The blocker this row names is exactly what the CAS supplies.** `lib.rs::series_reversion` is the compositional inverse of a power series (`f(0) = 0`, `f'(0) ≠ 0` ⇒ `g` with `f(g(x)) = x`) — the inverse-function theorem in power-series form, an actual inverse FUNCTION rather than a bound relating gaps. And `real_algebraic::polynomial_ivt` produces the **exact preimage point** for `p(x) = y` as a named algebraic number, which is the 'exact IVT preimage' this row calls the gate. Both live on the polynomial / power-series fragment. No ledger fact for either — **unregistered capability** | Order PRESERVATION (`strict_mono_of_pos_deriv`, Ch11) and CONDITIONAL order-reflection (`order_reflect_of_pos_deriv` ✓, needs `Apart` as data) were already landed. **Landed this session: `inverse_lipschitz_of_pos_deriv`** ✓ — the CONTINUITY-of-the-inverse statement, `Apart x y → abs(x−y) ≤ (2k+2)·abs(F x − F y)`, composing `strict_mono_magnitude`+`scale_cancel_le` (Ch11) with `abs_le`. Unlike `order_reflect_of_pos_deriv` it needs NO codomain hypothesis at all — it bounds the domain gap in BOTH directions from `Apart` alone, which is what makes it continuity rather than a restatement of order-reflection. **What remains is genuinely gated on an exact IVT preimage**: an actual inverse FUNCTION (not just a bound relating gaps) needs producing, for a given `F x0`, an actual point `x0` back out of the codomain value — exactly the exact-root construction `creal/ivt.rs` refutes rather than leaves open (two kernel-computed counterexamples). So Ch12's "the inverse function is continuous" is now fully covered constructively; "the inverse function is [differentiable / exists as a `CReal → CReal`]" is not reachable without solving that already-refuted problem |
| **13** | **Integrals** | **K** | `lib.rs::integrate` returns an antiderivative **with a proof**: it differentiates its own answer and zero-tests it against the integrand (`CertifiedIntegral`), so a returned integral carries a re-checkable proof of its own correctness. `ratint.rs` is Horowitz–Ostrogradsky, splitting `∫A/D` into a rational part found by one exact linear system and a residual logarithmic part with no factorization and no root-finding; `ratint::` is consumed at 38 sites in `lib.rs`. Also `definite_integrate`, `numeric_integrate`, `iterated_integral`, `improper_integrate` (bounds at `±∞` through `limit`; Gaussian moments and integer-order Bessel-J closed forms), `average_value`, `root_mean_square`. No ledger fact — **unregistered capability** | **CLOSED, and `CReal.integral` now EXISTS.** `CReal.riemannSum_cauchy` → the representative-index bridge (`sharedIndexToCanonical`) → the common-refinement construction → **`CReal.integral`**, built on the `deep`-reindexed sequence (`e := n` directly, never inverting a general modulus). Both concerns this row previously named are resolved. It is proved **witness-independent** (`integral_witness_independent`) — the value does not depend on which convergence witness is supplied — and carries its algebra: `integral_const`, `integral_add`, `integral_le`, `integral_scale`, `integral_converges`, and **`riemannSum_integral_close`** (a Riemann sum at sufficient depth sits within an explicit `e`-derived distance of the integral). Thirteen lanes; the estimate's first version cost **74 s on every prelude build** by forcing a full `Definition` unfold, caught pre-publication by bisecting the declaration by legs. Registered in the fact ledger as `F:creal-integral` and nine siblings |
| **14** | **Fundamental Theorem of Calculus** | **K (partial)** | `lib.rs::definite_integrate` **is** the FTC on this fragment, by construction: find a certified antiderivative `F` with `integrate`, return `F(upper) − F(lower)`; `prove_derivative` certifies the other direction. **Interval additivity — the exact obstacle the `K` route is blocked on — is free here**: `(F(c)−F(a)) + (F(b)−F(c)) = F(b)−F(a)` is an identity in the certified antiderivative and never mentions a mesh, which is why the constructive difficulty (an interval-relative mesh) has no analogue on the decidable fragment. No ledger fact — **unregistered capability** | The integral's **algebra is complete** (row 13). What remains is **`CReal.integral_split`** — additivity over an interval split — and it is blocked on exactly **two** named facts, not on effort. **The `riemannSum` version is FALSE at fixed mesh count**, with a kernel-computed counterexample (`m := 0`, `f := id`, `a,c,b := 0,1,3`: the whole is `0`, the halves give `0 + 2 = 2`); only the LIMIT is additive. Every existing 'combine several riemannSums' construction is `Nat`-refinement algebra over **one fixed interval** and cannot be rearranged, because that relation does not exist algebraically for a general `c`. **(1) An Archimedean crossing index — LANDED** (`CReal.crossingIndex`/`crossingUpper`/`crossingLower`, a *slack* variant; the tight bracket is not constructible, since deciding which side of an exact crossing `c` falls on IS the undecidable comparison). **(2) A cross-width term-by-term Riemann comparison via uniform continuity** — in progress. A doc objection that `converges_unique` needs both facts to name the syntactically same sequence was **dissolved**: `le_of_forall_le_add_small` / `equiv_zero_of_small` prove an `Equiv` from an arbitrary-accuracy rational bound with no shared sequence at all |
| **15–17** | **Trig, π irrational, planetary motion** | **K (opened)** | Trig and its relatives are present as exact symbolic machinery: `lib.rs::{evaluate_trig, expand_trig, trigsimp, rewrite_exp, roots_of_unity, argument, modulus}`, `orthopoly::{chebyshev_t, chebyshev_u}` (the trig polynomials, exact rational), `hyperbolic.rs` (nine functions from exp/ln/sqrt), `special::{gamma, beta, zeta, dirichlet_eta, dirichlet_lambda, polygamma_at_one}` (closed forms at rational arguments), and `fourier_series` (Euler coefficients by exact `definite_integrate`). **π itself: audited — none.** π is not in the exact-rational fragment, so the CAS carries it as a symbol and decides nothing about its irrationality. No ledger fact | **This row's previous claim — "no transcendental functions exist" — is no longer true.** **`CReal.cosOne` is constructed**: `cos 1 = Σ(-1)^k/(2k)!`, built via `CReal.mk` on an explicit regular sequence, never `Exists`-elimination, mirroring `e`. Its index is doubled as `Nat.add k k` (**not** `Nat.mul 2 k`) so `CReal.pow_add` applies with zero reduction bookkeeping, and its domination series is *literally* `expDominant` — the same one `e` uses — so no new domination argument was needed. Two claims I briefed were wrong and the lane checked both: the absolute-convergence bridge is unnecessary (`sumRange_cauchy_of_dominated` never required nonnegativity, only a bound on `abs (f k)`, so it already covers a SIGNED series), and no parity case split is needed (`abs (pow (neg one) k) ≤ one` goes by induction). **Still out of reach: general `sin`/`cos : CReal → CReal`** (needs a bound depending on `\|x\|`, i.e. power series — see row 24) and **π** -- **RETRACTED 2026-08-31, and the retraction is the point.** This clause read: *"and π, which is downstream of a root of `cos` and therefore of the exact-root construction `creal/ivt.rs` refutes."* That was a statement about ONE DEFINITION of π presented as a statement about π. **`CReal.pi` is now constructed** (`creal/pi.rs`), by `CReal.mk` on an explicit regular sequence exactly as `CReal.e` and `CReal.cosOne` are, from **Euler's transform of Leibniz** (`π/2 = Σ 2^k (k!)^2/(2k+1)!`), with `3 <= π <= 4` proved and an empty axiom footprint. No root, no IVT. What survives of the old clause: IDENTIFYING this π with a root of `cos` still needs the refuted construction. The NUMBER never did. Compare Mathlib, whose `Real.pi := 2 * Classical.choose exists_cos_eq_zero` is exactly the refuted route -- IVT plus choice -- and is `noncomputable` |
| **18** | **Log and exp** | **K** | `lib.rs::{expand_log, logcombine, rewrite_exp, nsimplify, evalf}`, `matrix_exp`, `laplace_transform`/`inverse_laplace`, and `hyperbolic.rs` (built from exp/ln/sqrt). **Bounds on `e`: audited — none.** `e` is a symbol on this fragment, not a constructed object, so nothing here proves `2 ≤ e ≤ 3`; that result is the `K` route's and stays there. No ledger fact | **`CReal.e` is constructed** — via `CReal.mk` on an explicit regular sequence, never `Exists`-elimination. Five lanes: `expTerm`/`expSeriesPartial` → `expTerm_le_geom` → `Rat.pow_natDivSucc_two` (the representation bridge) → the closed form, after a bisect found **one stray `equiv_symm`** reversing a chain link → `cauchyOfPointwiseEquiv` → `expDominantCauchy` → **`e`**. The whole domination bridge is **`inv`-free**. **`2 ≤ e ≤ 3` is now PROVED** (`CReal.two_le_e`, `CReal.e_le_three`, plus the looser but uniform-in-`n` `CReal.e_le_four`), once `CReal.sumRange_mono_outer` supplied the missing outer-index monotonicity this row previously called for. `two_le_e` needs an EVENTUAL argument (`converges_lower_bound_shift`, since `expSeriesPartial 0 = 0 < 2`); `e_le_three` needs a genuine `{0, 1, k+2}` case split — the index-2 kink is mathematical, not an artifact — while `e_le_four` is one uniform bound at every `n` |
| **19** | **Integration in elementary terms** | **C** | **This chapter had NO ROW in this table until 2026-08-31, and it is one of the CAS's strongest.** `partial_fractions::{partial_fractions, verify_partial_fraction_certificate}` — certified partial-fraction decomposition, whose module doc names **Spivak ch. 19** explicitly; `ratint.rs` is Horowitz–Ostrogradsky (Bronstein, *Symbolic Integration I*, ch. 2), splitting `∫A/D` into a rational part found by one exact linear system and a logarithmic residue, with no factorization and no root-finding; `lib.rs::{apart, residue, integrate}`. Ledger: `F:cas-partial-fractions-mixed-general-case` (`cas-internal`) and `F:cas-partial-fractions-mixed-general-case-kernel-checked` (**kernel-reconstructed**) | **No `K` route exists or is planned**, and that is not a gap — elementary integration is an algorithm question rather than a constructive-analysis one, so `C` is not a fallback here but the only route the statement has. The purely-rational case is fully certified by differentiate-and-zero-test; a genuine logarithmic part is a later slice |
| 20 | Taylor polynomials | — | **`taylor::polynomial_taylor` + `verify_taylor_certificate` — Taylor's theorem WITH THE LAGRANGE REMAINDER**, exactly, on the polynomial fragment. Its module doc names ADR-0603 row 3 and *Spivak ch. 20* by name. Around it: `series::{series, series_at}`, `approx::{lagrange_interpolation, newton_divided_differences, pade, pade_fraction}`, `lib.rs::least_squares_polynomial`, and eight `orthopoly` families. Ledger: `F:cas-taylor-quartic-lagrange-witness` (`cas-internal`) and `F:cas-taylor-remainder-lhs-kernel-checked` (**kernel-reconstructed**) | open. **Graded family stated**: [`graded-statement-families.md`](../graded-statement-families.md) §3 — row 1 (integral-form remainder) is sized but not started, blocked on an n-fold `hasDerivative` package that does not exist; row 2 is not merely absent, it is undecided which statement would need refuting; the CAS `series` route (row-3-shaped) answers a weaker question (truncation identity, no error bound) |
| 21 | `e` is irrational | — | **audited — none, and this is a genuine boundary rather than a gap.** `factor_int::factor_univariate_over_q` decides irreducibility over ℚ and `algebraic::real_roots` names any real algebraic number exactly, so *algebraicity of a given algebraic number* is decidable here — but transcendence asserts the absence of ANY rational polynomial relation, which is not expressible in a fragment whose objects are individual rational polynomials. Nothing in the crate attempts it | open — but **`CReal.e` now exists** (see Ch 18), so this is downstream of a constructed object rather than of nothing. √2's irrationality **is** proved (`Nat.no_rational_sqrt_two`) |
| **22–23** | **Sequences and series** | **K** | `gosper::gosper_sum` — **Gosper's algorithm decides** whether a hypergeometric term has a hypergeometric antidifference, proof-carrying; `telescoping::zeilberger` plus `telescoping_check` handle the definite case. `lib.rs::infinite_sum` is a real convergence decision on its fragment: the value is `lim S(k) − S(lower)` for a certified antidifference, and it declines exactly when that limit is infinite (`∑2⁻ᵏ = 2` and `∑k·3⁻ᵏ = 3/4` return; a polynomial or `|ratio| ≥ 1` summand returns `None`). Plus `definite_sum`, `finite_product`, `sum_polynomial`, and `solve_recurrence` (closed form for a constant-coefficient linear recurrence, certified by substitution). Ledger: the nine facts listed at Ch 2, all `cas-internal` | comparison test (nonnegative series, `0 ≤ a k ≤ b k`), dominated convergence, telescoping, geometric tail bounds, **`geomCauchy`** — `Cauchy (sumRange (pow half ·))` — and **`sumRange_cauchy_of_abs_cauchy`/`sumRange_converges_of_abs_converges`** (absolute convergence implies convergence, landed this session), which is what makes the comparison test usable on a SIGNED series. **The "exactly two declarations" `inv`-containment claim this row previously made was undercounted, corrected here: `CReal.inv` is directly built by SIX declarations along `geomCauchy`'s own dependency chain** — four in `geometric.rs` (`geom_tail_bounded_div`, `geom_tail_within`, `geom_tail_within_le`, `geom_pair_within`, all pre-existing infrastructure for the quotient-form tail bound `tail ≤ xᵐ/(1−x)`) plus the two in `exponential.rs` this row already named (`geomHalfInvLeafBound`, `geomCauchyOrderedHalf`) that consume `geom_pair_within` at the concrete base `1/2`. `geomCauchy` itself constructs no `inv` term directly. **Ratio test and `e` irrational (Ch21): assessed, not built** — see below . **Landed since: the RATIO TEST.** `CReal.geomCauchyOfLt` generalizes geometric convergence from the literal base ½ to any `0 ≤ x < 1` — the half-case's literal coincidence `3+4=7` cannot survive a symbolic bound, so both sides pad to a common target through `Rat.natDivSucc_le_add_left` and `Rat.natDivSucc_add` rather than by defeq reduction. Then `CReal.geomScaledCauchyOfLt` and **`CReal.sumRangeRatioTest`**. The general route was cross-checked against the base-½ one at `x := half`, **against `geomCauchy`'s own stored type fetched from the kernel** rather than a hand-reconstruction, with a negative control confirming the agreement is not vacuous — it passed first try. Composition proved simpler than sized: **no absolute-convergence bridge is needed**, because `sumRange_cauchy_of_dominated`'s hypothesis is already stated on `abs (f k)`, so it covers a signed series directly. Two lanes discovered that independently, against my brief |
| 24 | Uniform convergence, power series | — | Power series are present and exact — `series::{series, series_at}`, `laurent_series` (including a finite principal part), `series_reversion`, `approx::pade` (Padé approximants matching a Maclaurin series through order `m+n`), `fourier_series`, `z_transform`/`inverse_z_transform`. Error control on the polynomial fragment is `taylor::polynomial_taylor`'s Lagrange remainder, and `interval_arith` gives rigorous enclosures. **Uniform convergence as a statement: audited — none** — nothing in the crate states or certifies it, and `series` alone answers a truncation-identity question with no error bound, exactly as [`graded-statement-families.md`](../graded-statement-families.md) §3 already says. No ledger fact | open |
| 25–27 | Complex numbers and functions | **K** | `lib.rs::{conjugate, real_part, imaginary_part, modulus, argument, roots_of_unity, cyclotomic_polynomial, eigenvalues, characteristic_polynomial, minimal_polynomial, jordan_form, diagonalize}`; `factor_int::factor_univariate_over_q` gives **complete** factorization over ℚ into irreducibles (Berlekamp–Zassenhaus, with the answer cheaply certified by multiplying the factors back and zero-testing) — the ℚ half of the FTA question; `gfp::{factor_berlekamp, roots, is_irreducible}` over 𝔽ₚ. **FTA over ℂ: audited — none, and this CONFIRMS the `K` row rather than contradicting it** — `sturm.rs` and `algebraic.rs` isolate REAL roots only, so complex root isolation is a genuinely missing algorithm on the CAS side too, exactly as `graded-statement-families.md` says of row 3. No ledger fact | ~1,000 `Complex.*` declarations; field, `conj`, `normSq`, roots of unity, Ptolemy, `add_pow`, `mul_sub_one_geom`; conjugation now closed over the ring and division: `conj_zero`, `conj_one`, `conj_pow`, `conj_div`, `div_congr`. **Corrected 2026-08-27, kernel-measured stale within 48h of writing**: `CReal.sqrt` now EXISTS (landed 2026-08-23, total, axiom-free) and `Complex.abs` is built on top of it — `abs_nonneg`, `abs_congr`, `abs_one`, `abs_mul`, and (landed 2026-08-26) **`abs_add_le`, the modulus triangle inequality**, are all proved. Only `Complex.exp`/`arg` remain absent. <!-- absent: Complex.exp, Complex.arg --> **FTA needs polynomial infrastructure that does not exist at all** . **The 'polynomial infrastructure that does not exist at all' now exists**: `Complex.polyEval`, `polyAdd`, `polyScale`, `polyDegreeLt` and the two **evaluation homomorphisms** (`polyEval_polyAdd`, `polyEval_polyScale`), proved symbolically. Representation is a coefficient function `Nat → Complex` plus an explicit bound — this kernel has no `List` **today** -- an INVENTORY, not a law ([ADR-1310](../../research/09-decisions/adr-1310-the-aggregate-absence-is-an-inventory-and-a-fold-is-not-a-type.md), 2026-08-31: `Nat.Pair` and `Nat.Primrec` both landed this week, an inductive costs ZERO axioms in the ledger accounting, and the reason not to add one is that `Nat.Fin` already exists with zero non-test consumers. A finite sum needs a FOLD over its index set, and a fold is a function -- `Int.sumMaps` folds over every `g : [0,m) -> [0,n)` and `Int.prodRange_sumRange_expand` is the Cauchy-Binet expansion step ADR-1135 called inexpressible), so it mirrors `Rat.polyEval` — and the bound is deliberately **not** a computed degree, because `Complex.Equiv` is undecidable so no coefficient can be tested for zero. `polyEval` is sum-of-monomials, not Horner: Horner needs highest-coefficient-first processing, i.e. a countdown `Nat.sub` inside a recursion, which is this kernel's documented concrete-witness trap. **`polyMul` was blocked as of the previous measurement; it is not anymore (corrected 2026-08-27, landed same day)**: the naive convolution is the correct truncated coefficient only if both factors vanish beyond their bound, and `Complex.sumRange_mul_eq_diag_add_corner`'s own doc still correctly records that the identity WITHOUT its corner term is **false**, refuted at n=2 — but the hypothesis-carrying version, `Complex.polyMul` plus `polyDegreeLt_polyMul` and `polyEval_polyMul` (the padded evaluation homomorphism), is now proved. FTA itself is still not built — see [`graded-statement-families.md`](../graded-statement-families.md) for the full four-row account, including why row 3 (root isolation over ℂ) is a genuinely missing algorithm, not an assembly gap |
| 28 | Fields | **K** | **One of the CAS's strongest chapters, and this row said nothing about it.** `gfp.rs` — full univariate arithmetic over 𝔽ₚ with Berlekamp factorization, `is_irreducible`, `roots`. `gf2.rs` + `gf2_extension.rs` — GF(2) and binary extension fields with irreducibility certificates, re-checked by a **deliberately separate** implementation in `gf2_independent.rs`. `algebraic.rs` — number fields as ℚ[x]/(minimal polynomial), with exact arithmetic and an exact ORDER (`real_algebraic::{inv, div, algebraic_cmp}`). `normalforms.rs` — Hermite and Smith normal forms over ℤ. Ledger, four facts, all `cas-internal`: `F:gf2-composition-shape-classification`, `F:gf2-general-monomial-composition-criterion`, `F:gf2-witt-shifted-degree-seven-closed-form`, and `F:gf2-degree-eight-octuple-two-step-chain` (**`refuted`** — a recorded negative result, not a gap) | `Rat`, `CReal`, `Complex` field laws |
| **29** | **Construction of the real numbers** | **K** | `algebraic::AlgebraicReal` + `real_algebraic` — the **real algebraic numbers**: an exactly representable, exactly *comparable*, arbitrarily refinable ordered subfield of ℝ. The contrast with the `K` route is the interesting part: `algebraic_cmp` is a genuine DECISION where `CReal.lt` deliberately has no `lt_total`. This is not a construction of ℝ — it is the decidable subfield, which is the whole ADR-0603 row-3 bargain in one object | **`CReal` *is* this** — Bishop setoid over constructed rationals, trusted surface 0 (ADR-0512) |
| 30 | Uniqueness of the reals | — | **audited — none.** Uniqueness of ℝ is a second-order statement about complete ordered fields; the CAS fragment has no way to state it, and nothing in the crate attempts it | open (needs LUB, so likely **X**) |

### What the 2026-08-31 audit changed, with the refuted text quoted

Lane `cas-coverage-audit`. Every `C` cell above is either a named module and
function, or the literal marker **audited — none** with the reason. A blank `C`
cell now means the row was never audited, and there are none left. Six cells
contradicted what the `Route`/`State` columns said:

- **Chapter 19 had no row at all.** It was absent from a 22-row table that ran
  1 → 30, and `partial_fractions.rs`'s module doc names *Spivak ch. 19* in its
  first sentence. Added.
- **Chapter 20 read, in full:** *"20 | Taylor polynomials | — | open."* The
  route column was a dash. `crates/axeyum-cas/src/taylor.rs` is *"Exact
  polynomial TAYLOR'S THEOREM with Lagrange remainder (ADR-0603 row 3, Spivak
  ch. 20)"*, with two ledger facts, one of them kernel-reconstructed. That cell
  was the worst in the file: not stale, simply never looked.
- **Chapter 24 read:** *"24 | Uniform convergence, power series | — | open."*
  Power series, Laurent series, series reversion, Padé approximants, Fourier
  series and the z-transform all ship. What is genuinely absent is *uniform
  convergence as a statement*, and the cell now says exactly that instead of
  "open".
- **Chapter 12's** *"What remains is genuinely gated on an exact IVT
  preimage… exactly the exact-root construction `creal/ivt.rs` refutes"* is
  true of the `K` route and reads as a statement about the chapter.
  `real_algebraic::polynomial_ivt` produces that exact preimage on the
  decidable fragment, and `series_reversion` produces an actual inverse
  function. The `K` cell is unchanged and still correct about `K`.
- **Chapter 14's** blocker — additivity over an interval split — is free in the
  `C` column, because a certified antiderivative never mentions a mesh. The two
  routes' difficulties do not correspond, which is the useful thing to know
  before briefing a lane against either.
- **Chapter 28** said only *"`Rat`, `CReal`, `Complex` field laws"*. 𝔽ₚ,
  GF(2), binary extension fields and number fields are all here, with an
  independent second checker for the GF(2) certificates.

Two cells were **corrected in the other direction**, and they matter as much:
`FTA over ℂ` (25–27) and `uniform convergence` (24) are audited-none on the CAS
side too, so the `K` rows' pessimism about them is *confirmed by an independent
route* rather than contradicted. An audit that only ever adds capability is not
an audit.

**One number in the corrected legend above is off, measured here.** It says
`crates/axeyum-cas` is "72,008 lines, 363 public functions across 53 modules".
`72,008` and `363` are `src/*.rs` with `pub fn` at column 0 — they exclude the
`mvpoly/`, `ntheory_certify/`, `sos/` and `bin/` subdirectories and every `impl`
method. Counting all 68 `.rs` files under `src/`: **77,590 lines**, and **685
`pub fn`** at any indentation (669 in `src/*.rs` alone). The 53 modules figure is
right. The direction of the error is the one this whole note is about — the
smaller number was the one quoted.

**Where the 46 `cas-certificate` facts actually sit**, since only 26 of them are
Spivak-shaped: 16 are Euclidean geometry (`geometry_certify` + the independent
`geometry_check`), 9 are binomial/telescoping identities (Ch 2 and 22–23), 6 are
IVT/EVT/extremum (Ch 7), 4 are number theory, 4 are GF(2), 2 are MVT (Ch 11), 2
are Taylor (Ch 20), 2 are partial fractions (Ch 19), and 1 is the
difference-of-squares polynomial identity (Ch 1). Split by ADR-0601 §2:
**32 `cas-internal`, 14 `kernel-reconstructed`** — read from
`scripts/validate-facts.py`'s own `classify_cas_certificate_fact`, not from a
label.

**And the audit found capability with no ledger fact at all.** Chapters 5, 12,
13, 14 have a real, exact, certificate-carrying `C` route and **zero**
registered facts — marked *unregistered capability* in the cells above. That is
the flywheel's own next task: `lib.rs::integrate` returns a proof of its own
correctness on every call and nothing in `artifacts/facts/` records it.


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
