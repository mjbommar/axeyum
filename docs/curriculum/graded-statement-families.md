# Graded statement families: MVT, LUB, Taylor remainder, FTA

Status: measurement note (2026-08-27), §2 AMENDED 2026-08-31 (LUB's row 2 is
landed — `CReal.lub_decides_em`, ADR-1010; the superseded absence assessment is
quoted in place rather than deleted)

[ADR-0603](../research/09-decisions/adr-0603-classical-theorems-land-as-graded-statement-families.md)
decided that a classical theorem lands as a four-row family — constructive
general form, boundary refutation, exact form on the decidable fragment,
labeled import. IVT and EVT have that family stated (`creal/ivt.rs`,
`docs/research/10-cas/decidability-map.md`); the
[2026-08-27 architecture review](../research/11-design-review/2026-08-27-architecture-review.md)
§4 named four more that deserve it: **MVT, LUB/completeness, Taylor
remainder, FTA**. This note states all four rows for each, as **measured
status**, not aspiration.

## Method

Every claim below traces to one of:

- a kernel declaration, checked with `kernel_declaration_projection
  --require-declaration <name>` (built `--release`;
  `target/release/examples/prelude_theorem_inventory` and
  `kernel_declaration_projection` were rebuilt fresh for this note —
  `scripts/cargo-serialized.sh build --release -p axeyum-lean-kernel --example
  prelude_theorem_inventory --example kernel_declaration_projection`,
  33s, clean) — or `prelude_theorem_inventory --release --include-constructed`
  for theorem-kind rows (it lists **theorems only**; definitions need the
  projection tool, which exits non-zero on absence);
- a fact in `artifacts/facts/` (806 facts; `python3 scripts/validate-facts.py`:
  626 proved, 4 refuted, 171 open; of 25 `cas-certificate` facts, only **1** is
  kernel-reconstructed and 24 are cas-internal-only);
- an explicit gap, with its blocker named and a positive/negative control
  pair recorded.

Every negative was paired with a positive control of the same declaration
kind before being trusted (`Complex.factorQuotient`, `CReal.weierstrassMTest`,
`CReal.monotone_of_nonneg_deriv` etc. all `found`, confirming the binaries are
fresh and not the stale-target trap this session has hit before).

**This measurement corrected two stale claims in `spivak.md`** (see
"Corrections" at the end) — both landed in the 48 hours before this note and
were simply never propagated.

---

## 1. Mean Value Theorem (Spivak ch. 11)

| Row | Status |
|---|---|
| **1. Constructive general form** | Not MVT — MVT is unavailable (see row 2). What IS proved, axiom-free, over `CReal`, without invoking MVT: `CReal.monotone_of_nonneg_deriv`, `CReal.antitone_of_nonpos_deriv`, `CReal.constant_of_zero_deriv`, `CReal.strict_mono_of_pos_deriv`, `CReal.strict_injective_of_pos_deriv`, `CReal.strict_antitone_of_neg_deriv`, `CReal.strict_mono_comp` — all confirmed present (`kernel_declaration_projection --require-declaration`, `found … theorem … 0` axiom footprint). The **rate** chain — `CReal.strict_mono_magnitude` → `CReal.scale_cancel_le` → `CReal.diff_le_of_strict_mono_magnitude` (`\|x−y\| ≤ 2(k+1)(\|Fx\|+\|Fy\|)`) — is likewise present. None of these seven are registered in `artifacts/facts/` (`ls artifacts/facts | grep -i` finds no `monotone-of-nonneg-deriv`/`strict-mono`/etc. entry); they exist only as kernel declarations. |
| **2. Boundary refutation** | **Absence, not refutation.** `crates/axeyum-lean-kernel/src/creal/monotone.rs:5029-5032`'s own module doc states MVT is "unavailable here — it rests on the extreme value theorem, not constructively provable" — an *inherited* unavailability argument (MVT needs EVT; EVT is unavailable), never a **dedicated MVT counterexample**. No declaration, test, or fact constructs a function `F` for which the MVT conclusion (`∃c ∈ (a,b), F'(c) = (F(b)−F(a))/(b−a)`) is false — contrast with IVT's row 2, which has a **kernel-computed** reduction test (`ivt_bisect_diag_reduces_on_the_identity_bracket_neg_one_two`, `creal_tests.rs:6026`) exhibiting a concrete bracket converging to the *wrong* value. And EVT's own row 2 — the theorem MVT is said to inherit its unavailability from — is itself marked **"in progress"** in `crates/axeyum-cas/src/extremum.rs:11` ("Row 2 (kernel side, in progress): attainment is refuted as constructively unavailable…"), not landed. So MVT's row 2 rests on an argument whose own foundation is not yet built. This is a genuine gap in the family, not a documentation gap: building it needs either (a) a direct MVT counterexample (a function with a bounded derivative-difference structure but no interior point matching the secant slope — the standard classical counterexamples all secretly use EVT/attainment, so a genuinely *independent* MVT counterexample is not obviously easier than finishing EVT's own row 2), or (b) finishing EVT's row 2 first and then formally deriving MVT's unavailability from it. |
| **3. Exact form on the decidable fragment** | **Landed, same day as this row was last marked "reachable, not built."** `crates/axeyum-cas/src/mvt.rs`: `polynomial_mvt`/`verify_mvt_certificate`, confirmed present this session (`cargo test -p axeyum-cas --lib mvt::` — **18 passed, 0 failed**, re-run fresh, not read from the lane's own report). For a polynomial `p` with rational coefficients on `[a,b]`, it forms the Rolle reduction `g(x) := p(x) − p(a) − m(x−a)` (`m` the exact secant slope), reuses `extremum::polynomial_extremum` on `g` (and `−g` on a tie) to locate an interior critical point when `deg(p) ≥ 2`, and handles `deg(p) ≤ 1` as its own degenerate branch (`g' ≡ 0` identically, every interior point a witness) — `c` is produced as a **named** `AlgebraicReal`, not merely asserted. `verify_mvt_certificate` independently re-derives the slope, `g`/`g'`, the bracket's Sturm recount, strict interiority, and the conclusion `p'(c) = m`, all from `poly`/`a`/`b` alone. The adversarial case worth naming: `p = x³ − 4x²` on `[0,4]` has `m = 0` and `p'(x) = x(3x−8)`, whose roots are `x = 0` (the **left endpoint itself**) and `x = 8/3` (genuinely interior) — both satisfy the slope equation, so a checker that skipped the strict-interiority re-check would wrongly accept the endpoint (`verify_rejects_an_endpoint_witness` confirms this). **Cost is not simply inherited from `extremum.rs`**: reusing EVT's cheap all-rational degree-5 case (`3x⁵−5x³` on `[−2,2]`) gives a nonzero secant slope, which destroys the factorization that made the *original* derivative cheap to isolate — `g'` becomes an irreducible quartic that declines soundly at ~2–4s instead of resolving cleanly. Measured cost curve (debug build): degree 2 ~2ms, degree 3 (√3 witness) ~5ms, degree 5 (degree-4 algebraic witness) ~27ms. Kernel reconstruction (ADR-0601 §2) is not attempted — this is a CAS-internal-only row 3 until that lands. |
| **4. Labeled import** | Not attempted. `AxReal`'s 30-axiom package (`crates/axeyum-lean-kernel/src/arith_model.rs:1-13`) axiomatizes only "a commutative ring with 1, compatibly ordered" — no `inv`, no `div`, no completeness/supremum axiom, no Archimedean axiom, no MVT. There is no axiomatized carrier in this repository a classical MVT import would even attach to; building row 4 means adding new axioms first. |

**Verdict (updated 2026-08-28: EVT row 2 has since landed — see the
recommendations below, which now supersede this row's "unfinished EVT"
reasoning)**:
MVT's family is 1 real row (constructive substitutes, unregistered as facts),
1 half-row (row 2 is an inherited assertion — not a dedicated refutation),
**1 landed row (row 3,
`polynomial_mvt`/`verify_mvt_certificate`, CAS-internal only pending kernel
reconstruction)**, 1 not-applicable-yet row (row 4, no axiomatized target
exists).

---

## 2. Least upper bound / completeness (Spivak ch. 8)

| Row | Status |
|---|---|
| **1. Constructive general form** | **Bishop completeness**, `crates/axeyum-lean-kernel/src/creal/completeness.rs` (488 lines): every `RegularSeq` has a constructed limit — `CReal.limitSeq` (the diagonal `seq (X (2n+1)) (2n+1)`), `CReal.limitSeq_regular`, `CReal.limit`, `CReal.limit_dist`. All confirmed present via `prelude_theorem_inventory`/source read; the module doc states this is "constructed rather than merely asserted." **Updated 2026-08-31**: `CReal.supOn` landed 2026-08-30, after this note was written, together with `CReal.supOn_ub` (upper bound) and `CReal.supOn_approx_lub` (the approximation property) in `creal/sup_laws.rs`. So row 1 now has two constructions, not one: the limit of a **regular sequence** (which carries its own rate) and the supremum of a **uniformly continuous function on a compact interval** (where the modulus supplies the locatedness). Row 2 below is exactly the statement that generalises past both. |
| **2. Boundary refutation** | **CLOSED 2026-08-31 — this row was the one clean absence in this note and it is now a kernel-checked theorem, `CReal.lub_decides_em` (`crates/axeyum-lean-kernel/src/creal/lub_boundary.rs`, ADR-1010).** The counterexample family is a set carved out by an arbitrary proposition, which is what Spivak's P13 actually quantifies over: `CReal.lubSet A := fun x => Or (le x zero) (And A (le x one))`, i.e. `(−∞, 0] ∪ ((−∞, 1] if A)`. Both of classical LUB's hypotheses about it are **proved, not asserted** — `CReal.lubSet_inhabited` (`∀ A, lubSet A zero`, an exhibited witness rather than an `∃`) and `CReal.lubSet_bounded` (`∀ A x, lubSet A x → le x one`, an explicit bound rather than an `∃`) — so the family is machine-checked to lie inside LUB's hypothesis class. Given a supremum in **Bishop's** sense (an upper bound plus the approximation property, which is the clause `supOn_approx_lub` proves for the located case; the classical leastness clause is deliberately NOT assumed, because it yields only `¬¬A` and the reduction through it would be circular), one `lt_cotrans` call on `zero < one` at `z := s` gives `Or A (Not A)` for an **arbitrary `Prop`**. Statement read from `kernel_declaration_projection`'s `render_lean` column, not from prose: `(x0 : Prop) → (x1 : CReal) → ((x2 : CReal) → CReal.lubSet x0 x2 → CReal.le x2 x1) → ((x3 : CReal) → CReal.lt x3 x1 → Exists.{1} CReal (fun x5 => And (CReal.lubSet x0 x5) (CReal.lt x3 x5))) → Or x0 (Not x0)`; all four declarations carry footprint **0**. **The principle is UNRESTRICTED EXCLUDED MIDDLE, which is strictly stronger than the analytic LLPO IVT's and EVT's rows land on** — LLPO is consistent with Bishop's constructive mathematics and `em` is not, and this kernel contains only `Decidable.em` (which takes a `Decidable` instance) plus the four conditional bridges `em_of_dne`/`dne_of_em`/`em_of_peirce`/`peirce_of_em`, which take unrestricted `em` as a hypothesis and never assert it (ADR-0716 §2 measures that absence with controls). Non-vacuity is discharged as ADR-0603 Amendment 2 requires: at `A := True` BOTH hypotheses are built and `Kernel::infer` accepts the instance (`creal/lub_boundary_tests.rs`), with the conclusion pinned verbatim against an independently built `Or True (Not True)` and a negative control differing in one small term. Honest scope, unchanged from the sibling rows: this does not prove `em` FALSE — `em` is consistent here, so the classical conclusion is *unprovable* rather than refutable, and it is falsifiable in Amendment 2's sense (land an unrestricted `em` and this becomes a route to LUB rather than a boundary). Registered as `F:creal-lub-decides-em`. |
| **3. Exact form on the decidable fragment** | **`extremum::polynomial_extremum` computes exactly this for a polynomial on a closed interval.** For rational `p` on `[a,b]`, the supremum of `p`'s range *is* the maximum, and it is attained at a nameable algebraic point — decidable, exact, with an independent re-derivation checker (`verify_extremum_certificate`). This is the same file EVT's row 3 uses (ADR-0603 already labels it EVT row 3); it doubles as LUB's row 3 for the polynomial-range special case (attained sup ⇒ sup exists and is nameable). It does **not** generalize to an arbitrary bounded set of algebraic numbers (only ranges of a single polynomial over an interval), so it is a genuine but narrow row 3, not "LUB solved for the algebraic fragment" in full generality. |
| **4. Labeled import** | **Does not exist, and cannot attach to anything yet.** Confirmed via `arith_model.rs`, `docs/mathematics-2026-08/diary-real-keystone.md:26-30`, and ADR-0512 §(consequences): `AxReal` declares **no completeness/supremum axiom at all** — "There is no completeness (supremum) axiom, no Archimedean axiom, no density axiom — so nothing in it distinguishes ℝ from ℚ." A classical-LUB labeled import would need a *new* axiom added to (or a new package alongside) `AxReal` first; there is currently nothing to label. |

**Verdict (rewritten 2026-08-31; the original is quoted below because the gap
it named is what this row now closes)**: row 1 is solid and has grown a second
construction (Bishop completeness, plus `CReal.supOn` and its two
characterisation laws, landed 2026-08-30). **Row 2 is landed and is the
strongest boundary in this note**: `CReal.lub_decides_em` extracts unrestricted
excluded middle, where the IVT and EVT rows extract analytic LLPO — a
difference that matters, since LLPO is consistent with BISH and `em` is not.
Row 3 exists but only for the polynomial-range special case, reusing EVT's own
row 3 file, and is CAS-internal (no kernel reconstruction). Row 4 still has no
target axiom to import against.

> **Superseded, 2026-08-27**: "Row 2 is a **clean absence** — this is the
> single clearest case in this note of an unavailability that is asserted in
> prose but never proved with a counterexample, exactly the 'hole in the Pareto
> argument' the task asked to surface."

That assessment was accurate when written and is what the work recorded here
was aimed at. It is kept rather than deleted for the reason ADR-0603
Amendment 4 exists: an absence claim that quietly disappears once it is closed
leaves no way to check that it was ever true, and this repository's own
retrospectives record stale obstacle text costing more than the obstacles.
One thing the original got wrong is worth naming, because it shaped the sizing:
it looked for "a bounded, inhabited, **located** set with no computable least
upper bound". A located set is the wrong target — locatedness is exactly the
data that makes `supOn` work — and the reduction went through in four
declarations, using no primitive that was not already present, once the family
was allowed to be un-located.

---

## 3. Taylor remainder (Spivak ch. 20)

| Row | Status |
|---|---|
| **1. Constructive general form** | **Not built; explicitly sized and deferred.** `crates/axeyum-lean-kernel/src/creal/polynomial.rs:102-108`'s own module doc: "The Taylor polynomial as an object, and the integral-form remainder. Sized and reported separately (session report), not attempted in this file." The named next step, `taylorPoly a coeffs n := fun x => polyEval (fun i => scale (coeffs i) (invFactorial i)) n (add x (neg a))`, needs a `1/i!` scalar in `CReal` that does not exist yet. What DOES exist and is confirmed present: `CReal.polyEval`, `CReal.polyAdd`, `CReal.polyScale`, `CReal.polyDegreeLt` and their two evaluation homomorphisms (`polyEval_polyAdd`, `polyEval_polyScale`) — the algebra layer, not the remainder. The remainder itself needs an **n-fold iterated `hasDerivative` package**: confirmed by source (`crates/axeyum-lean-kernel/src/creal.rs`) that only **pairwise** combinators exist — `hasDerivative_const`, `_id`, `_neg`, `_add`, `_sub`, `_smul`, `_mul`, `_chain`, `_pow` (fixed low powers: `_pow_two`, `_cube`, general `_pow` still bound-hypothesis-gated) — no `n`-th derivative operator or Leibniz-for-`n` package exists. |
| **2. Boundary refutation** | **Not established — and it is not obvious a boundary even exists here the way it does for IVT/EVT/MVT/LUB.** The classical Lagrange-form Taylor remainder is normally proved via MVT (which is unavailable, see family 1), but an **integral-form** remainder (`R_n = ∫ₐˣ (x−t)ⁿ/n! · f^(n+1)(t) dt`) avoids MVT entirely and, per the brief's own framing (an earlier lane's assessment), may be constructively available once `CReal.integral` (landed, Spivak ch. 13) is composed with the missing n-fold derivative package. No refutation of any Taylor-remainder form has been attempted or found in this codebase (`grep -rliE taylor` across `docs/mathematics-2026-08/`, `docs/research/`, and kernel source turns up only the polynomial.rs module doc above and CAS planning docs — no counterexample). This row is genuinely open, not merely unfilled: whether a boundary refutation is even needed depends on which remainder form is targeted, and that has not been decided. |
| **3. Exact form on the decidable fragment** | **Not built at the kernel level; a weaker, non-equivalent thing exists in the CAS.** `axeyum-cas`'s `series`/`series_coefficients` (`crates/axeyum-cas/src/lib.rs:13162`) computes a finite-order Taylor/Maclaurin expansion with a **certified truncation identity** (per `docs/research/10-cas/curriculum-gaps.md` item 5, "Tier A — shipped, certified, TDD'd": arbitrary-center Taylor). This is NOT the Spivak ch. 20 remainder theorem: a truncation identity says the finite series equals itself when re-expanded to that order; it carries no **error bound** relating the truncated polynomial to the original function's value away from the center, which is what Ch. 20 actually asks for. So: a CAS-level finite Taylor expansion exists and is certified in its own (weaker) sense; a certified *remainder bound* for the polynomial fragment does not exist and would need combining `poly::rat_derivative` (for `f^(n+1)`) with an exact bound on `f^(n+1)` over the interval — itself close to another `extremum`-shaped construction, unbuilt. |
| **4. Labeled import** | Not attempted; no import infrastructure targets Taylor's theorem specifically. Same "no target axiom package" situation as MVT/LUB row 4. |

**Verdict**: this is the least-developed of the four families. Row 1 is
explicitly sized but not started (blocked on the n-fold derivative package,
which is itself blocked on nothing but effort). Row 2 is not merely absent —
it is **undecided which statement would even need refuting**. Row 3 has a
CAS-level cousin that is certified but answers a different (weaker) question
than the remainder theorem. Row 4 has no target.

---

## 4. Fundamental Theorem of Algebra (Spivak ch. 25–27)

| Row | Status |
|---|---|
| **1. Constructive general form** | **Not built.** No FTA-shaped declaration exists under any name tried (`Complex.fundamentalTheoremOfAlgebra` confirmed absent via `kernel_declaration_projection`, non-zero exit). What HAS landed and is directly load-bearing, all confirmed present via `kernel_declaration_projection`: `Complex.polyEval`, `Complex.polyAdd`, `Complex.polyScale`, `Complex.polyDegreeLt`, `Complex.polyMul` (**with its two correctness theorems, `Complex.polyDegreeLt_polyMul` and `Complex.polyEval_polyMul`, both confirmed present** — landed 2026-08-27, same day as this note), `Complex.hornerFromTop` (+ its three reduction lemmas), and `Complex.factorQuotient` (+ `Complex.factorQuotient_degreeLt`). **`CReal.sqrt` now exists** (landed 2026-08-23, `crates/axeyum-lean-kernel/src/creal/sqrt.rs`, total, no `0 ≤ x` hypothesis) and **`Complex.abs` now exists on top of it**, confirmed present, with `Complex.abs_nonneg`, `Complex.abs_congr`, `Complex.abs_one`, `Complex.abs_mul`, and — landed 2026-08-26 — **`Complex.abs_add_le`, the triangle inequality for the modulus**. `Complex.exp` and `Complex.arg` remain confirmed absent. <!-- absent: Complex.fundamentalTheoremOfAlgebra, Complex.exp, Complex.arg --> None of this assembles into FTA itself: a general constructive FTA needs a minimum-modulus / compactness argument over ℂ that this repository has not attempted (no holomorphic-function theory, no argument principle, no min-modulus machinery beyond the single-polynomial `extremum.rs` construction, which is real-valued and interval-bounded, not a 2-D compactness argument). |
| **2. Boundary refutation** | **Not established, and unlike MVT/LUB/IVT/EVT it is not clear one is even true.** No refutation of a constructive FTA exists in this codebase (`grep -rliE "\bfta\b\|fundamental theorem of algebra"` across `docs/` finds only "Lean-horizon"/scope-boundary notes, e.g. `docs/curriculum/02-structures/polynomials.md:46`, `docs/learn/math/complex-analysis-theorem-boundary.md:48`, never a counterexample). More importantly: FTA is **not obviously in the same constructive-failure class as IVT/EVT/MVT/LUB**. Those all fail because they assert something is *found* via an undecidable comparison over an unbounded domain. FTA is stated over a *compact* set (any disk large enough to contain all roots by the standard bound), and Bishop-style constructive analysis is known to have approximate constructive proofs of FTA using an infimum-of-modulus argument that does not require deciding real equality anywhere — this project has neither built that route nor refuted it. This row should read **"unassessed"**, not "unavailable": the honest gap is that nobody has yet determined whether FTA belongs with IVT/EVT (genuinely refuted) or with the ch. 9–10 derivative rules (constructively fine, just not yet built). |
| **3. Exact form on the decidable fragment** | **Not reachable today — this is the real gap, and it is an infrastructure gap, not a proof-difficulty one.** For rational-coefficient polynomials, an "FTA on the decidable fragment" would mean: isolate and name every complex root exactly (real root isolation's 2-D analogue). Searched for any such route (`weyl`, `durand.kerner`, `argument principle`, `complex.*isolat` across `crates/axeyum-cas/src/`) and found **none**. `axeyum-cas`'s `solve()` handles complex roots only for degree ≤ 2 in closed radical form and declines irreducible cubic-or-higher factors by design (same restriction `real_algebraic::real_roots` was built to lift for the *real* line only). `real_algebraic.rs`/`sturm.rs` isolate REAL roots of a real polynomial; there is no companion that isolates complex roots of a general (possibly complex-coefficient) polynomial via, e.g., a certified 2-D bisection or a resultant-based real/imaginary decomposition. `docs/research/10-cas/gap-analysis.md` G17 labels "roots/factorization over ℂ" as `certified (arithmetic/algebraic); complex analysis → heuristic`. **Re-checked this session, and the parenthetical needs to be more precise than "radical-form quadratics/cubics"**: `solve()`'s own source (`crates/axeyum-cas/src/lib.rs`) shows only degree ≤ 2 gets a closed radical form (real or complex, via `quadratic_roots`); an irreducible cubic-or-higher factor is dropped from `solve()`'s output entirely — `_ => {}`, no root at all, real or complex — and no Cardano/Ferrari radical solver exists anywhere in the crate (`grep -rniE "fn.*cubic|cubic_roots|solve_cubic"` finds only test names and an unrelated `gf2.rs` criterion). What G17's "certified (arithmetic/algebraic)" actually covers for degree ≥ 3 is `real_algebraic.rs`/`sturm.rs`'s Sturm-isolated **real** roots as algebraic-number witnesses — never a radical form, and never a complex root. So the gap is not "cubics need a slightly bigger radical formula"; it is "no complex root of any irreducible cubic-or-higher polynomial is named at all, in any representation." Building the FTA-row-3 route would need a genuinely new algorithm, not an assembly of existing pieces the way MVT's row 3 is. |
| **4. Labeled import** | Not attempted; same "no target axiom package" situation. |

**Re-assessment, 2026-08-27 (`fta-assess` lane, independent re-verification, no
declarations built):**

1. **Does `CReal.sqrt`/`Complex.abs` still gate an approximate FTA?** No —
   re-confirmed with fresh positive controls this session
   (`kernel_declaration_projection --require-declaration`, all `found`,
   exit 0): `CReal.sqrt`, `Complex.abs`, `Complex.abs_add_le`,
   `Complex.polyMul`, `Complex.polyDegreeLt_polyMul`,
   `Complex.polyEval_polyMul`, `Complex.factorQuotient`. Negative controls of
   the same declaration kind (`Complex.exp`, `Complex.arg`,
   `Complex.fundamentalTheoremOfAlgebra`) all correctly absent (non-zero
   exit). <!-- absent: Complex.exp, Complex.arg, Complex.fundamentalTheoremOfAlgebra --> So the modulus/triangle-inequality machinery an infimum-of-modulus
   argument would need is present; what is **not** present is the
   compactness/infimum-attainment argument itself (row 1) — nobody has
   attempted the Bishop-style construction (a decreasing sequence of shrinking
   disks + an infimum-of-modulus witness at every accuracy `e`, mirroring
   `ivt_approx`'s "root within `e`" rather than an exact root). Sizing that
   attempt is future work, not part of this assessment.
2. **Does complex root isolation genuinely not exist?** Confirmed, with a
   methodology note: the naive grep for
   `weyl|durand.kerner|argument principle|complex.*isolat` "matches"
   `extremum.rs`, but the hit is `complex**ity**...**isolat**ion` in one
   sentence — a false positive from the wildcard, not a real hit (verified by
   reading the matched line). The real evidence is code-level: `solve()`
   (`crates/axeyum-cas/src/lib.rs`) gives a closed radical form only for
   degree ≤ 2 factors and **drops** any irreducible cubic-or-higher factor
   entirely (`_ => {}`, no root at all, real or complex) — confirmed by
   reading the match arm directly, not inferred from a doc. No
   Cardano/Ferrari radical solver exists anywhere in the crate. `real_algebraic.rs`/`sturm.rs` isolate real roots of a real polynomial only.
3. **Cheapest sound route to FTA row 3, sized.** Pieces that already exist and
   would compose into it: a general multivariate Gröbner basis
   (`groebner_basis` in `groebner.rs`, with `lex_cmp` — i.e. elimination
   order is already available), a resultant (`resultant()` in `lib.rs`, but
   **only for two genuinely univariate polynomials with rational
   coefficients** — it calls `to_univariate`, so it cannot eliminate a
   variable from two *bivariate* polynomials treating the other as a
   parameter; that generalization does not exist), and real root isolation
   (`sturm.rs`/`real_algebraic.rs`). The standard route this composes toward
   is a **Rational Univariate Representation (RUR)**: write a complex root
   `x+iy` of `p` as the real solution pair of `A(x,y)=0, B(x,y)=0` (the real
   and imaginary parts of `p(x+iy)`), pick a generic primitive element
   `t = x + c·y`, compute its minimal polynomial via the lex Gröbner basis of
   `(A,B)`, isolate `t`'s real roots with the existing Sturm machinery, and
   express `x`, `y` as polynomial images of `t` (each root pair becomes a
   *derived* real algebraic number from a shared witness `t₀`, not two
   independently-isolated ones). Searched for this by name and found nothing
   (`primitive element`, `rational univariate`, `RUR` — the one grep hit is
   "rational univariate **series**" in `series.rs`, unrelated). **This is a
   genuinely new algorithm, not an assembly**: none of the missing pieces
   (bivariate real/imaginary decomposition of a `Complex` polynomial, a
   generic-primitive-element genericity check, RUR extraction from a
   Gröbner basis, and a certificate/checker for a *derived* algebraic number
   rather than `real_algebraic.rs`'s single-minimal-polynomial
   `AlgebraicReal`) exists today, even though the underlying Gröbner-basis
   and Sturm primitives do. Scope estimate: comparable to building
   `sturm.rs` + `real_algebraic.rs` again, plus a new certificate shape — a
   multi-file, multi-day effort, not the same-day, single-new-file shape
   `mvt.rs` had (which reused `extremum.rs`'s existing scalar witness type
   unchanged).
4. **Does FTA need row 2 at all?** **No — and this is the interesting
   finding.** IVT/EVT/MVT/LUB all fail the SAME way: the classical statement
   asserts existence of a point found by deciding an undecidable real
   comparison over an *unbounded* or *open* search (`CReal.lt` has no
   `lt_total`), so row 2 exhibits a concrete function for which that search
   provably cannot terminate on the right answer. FTA has no analogous
   step to refute: the classical proof (minimize `|p(z)|` over a
   sufficiently large closed disk, show the minimum is 0) is a compactness
   argument over a **bounded, closed** domain, and Bishop-style constructive
   analysis is documented to prove exactly this — an infimum of a uniformly
   continuous function over a compact set is always constructively
   computable to any accuracy, unlike an *attained* maximum/root search over
   an unbounded or open domain. So an "FTA-approx" (row 1, `ivt_approx`-shaped: for every accuracy `e`,
   produce `z` with `|p(z)| ≤ 1/(e+1)`) is plausibly provable **without ever
   needing a boundary refutation**, because there is no boundary — the
   general constructive form is not "weaker than classical, and provably so"
   the way IVT's general form is; it may simply equal the classical
   existence statement's *computational content* directly. If that holds up
   once row 1 is attempted, **FTA is a three-row theorem (1, 3, 4) with no
   row 2**, not a four-row family missing one row. This is a claim about
   ADR-0603's own row-count assumption, not a gap in this theorem: the
   framework should read "up to four rows," and a theorem needing only three
   is a finding about which class the theorem belongs to, not unfinished
   work on row 2. (This is *not* fully certain — nobody has attempted the
   row-1 construction yet to confirm no undecidable step sneaks in, e.g. in
   distinguishing "the infimum is exactly 0" from "the infimum is positive
   but arbitrarily small," which is itself the FTA-specific analogue of the
   comparison IVT/EVT get stuck on. So the honest claim is: **the failure
   mode that produces row 2 for the other four does not obviously apply to
   FTA**, not "row 2 is proved impossible.")

**Verdict**: the polynomial infrastructure (evaluation, multiplication with
its correctness theorems, synthetic division/factor-quotient, `sqrt`, `abs`
with the triangle inequality) is much further along than `spivak.md` says —
see corrections below, and it fully covers what an approximate-FTA row 1
attempt would need on the `Complex.abs` side. But this infrastructure does
not compose toward any FTA row without genuinely new mathematics: row 1
needs a compactness argument this repository has never attempted (though
unlike IVT/EVT/MVT/LUB, nothing here suggests it is constructively
unavailable — see point 4 above), row 2 may not exist as a distinct row for
this theorem at all, and row 3 needs a complex root-isolation algorithm
(sized above as RUR, not an assembly of existing pieces) that does not exist
in any form here.

---

## Corrections to `spivak.md`

Both corrections below were verified stale by direct kernel/source
measurement, not by re-reading the prose more carefully — the declarations
in question landed in the 24–96 hours before this note (`git log -S`
confirms 2026-08-23 for `CReal.sqrt`, 2026-08-26 for `Complex.abs_add_le`,
2026-08-27 for `Complex.polyMul`'s correctness theorems), which is inside
`spivak.md`'s own "measured 2026-08-25" window for the sqrt case and simply
after it for the other two.

1. **Ch 25–27 row, `Complex.abs`/`CReal.sqrt`**: the row read "`Complex.exp`/
   `abs`/`arg` absent — all gated on a general `CReal.sqrt`, itself an open
   climb." **`CReal.sqrt` exists** (total, axiom-free) and **`Complex.abs`
   exists on top of it**, with `abs_nonneg`, `abs_congr`, `abs_one`,
   `abs_mul`, and `abs_add_le` (the triangle inequality) all proved. Only
   `Complex.exp` and `Complex.arg` remain absent. Fixed in place.
2. **Ch 25–27 row, `Complex.polyMul`**: the row read "`polyMul` is genuinely
   blocked, not merely unbuilt: … refuted at n=2" (referring to the naive
   convolution without a vanishing/degree hypothesis, which is correctly
   refuted). **The hypothesis-carrying version has since landed**:
   `Complex.polyMul` plus `Complex.polyDegreeLt_polyMul` and
   `Complex.polyEval_polyMul` (the evaluation homomorphism, padded to
   `Nat.add m n`) are all proved, using the same
   `sumRange_mul_eq_diag_add_corner` decomposition whose *unconditional*
   form is still correctly refuted. Fixed in place: the naive form stays
   refuted, the hypothesis-carrying form is now proved.

No other row in `spivak.md`'s spine table was found to disagree with a
kernel measurement this session (Ch. 7, 8, 9–10, 11, 13 rows were spot-
checked against the declarations they name and matched).

## What this changes for the next lane

- MVT and LUB row 2 are the two clearest cases of an asserted-not-proved
  unavailability in the whole ladder. If a future lane wants the strongest
  version of the Pareto argument (row 1 optimal *because* row 2 is refuted,
  per ADR-0603's own stated purpose for row 2), these two are the ones that
  need a genuine counterexample construction, not documentation.
- **EVT's row 2 LANDED 2026-08-27** (`cf77a1912`,
  `crates/axeyum-lean-kernel/src/creal/extreme_value.rs`) as `CReal.evt_attained_max_decides_sign`,
  kernel-checked, registered and axiom-free: an attained maximum of
  `t ↦ t·v` on `[0, 1]` yields `∀ v, v ≤ 0 ∨ 0 ≤ v` — analytic LLPO, the
  comparison `CReal` deliberately lacks.

  **This does NOT unblock MVT row 2, and an earlier revision of this bullet
  wrongly said it did.** Route (b) above was "finish EVT's row 2, then derive
  MVT's unavailability from it"; EVT's row 2 is the prerequisite, and it is
  done, but the *derivation* is the hard half and it is an open problem, not a
  formality. Both `creal/rolle.rs` and `creal/mvt.rs` record in their module
  docs that the unrestricted existential form does not reduce to
  `creal/extreme_value.rs`'s obstruction by any short route either file could
  find, and they name the reason: **scaling by `v` never moves the
  derivative's zero location**, so `evtLinear`-shaped families transport
  through the chord subtraction without separating anything. Three auxiliary
  functions were tried and all three fail identically. Per ADR-0603's
  vocabulary, MVT row 2 is **unassessed** — "several short reductions provably
  fail to separate" — not "asserted unavailable" and not "one derivation
  away".
  **Its one labeled gap is now CLOSED too (2026-08-28).** EVT row 2 had
  carried a single assertion — that `evtLinear v` is uniformly continuous,
  i.e. that the counterexample family is inside classical EVT's hypothesis
  class — which the file marked "ASSERTED here, not proved" rather than
  hiding. It is now `CReal.evtLinear_uniformly_continuous`, kernel-checked and
  axiom-free, assembled from `uniformly_continuous_mul` at `id` and a
  constant. Two supporting declarations landed with it and are reusable well
  beyond EVT: `CReal.abs_bound_of_self` (promoted from a private `fn` in
  `creal/uniform_continuity.rs`, which makes `BoundedOn` trivial for EVERY
  constant function on EVERY interval) and `CReal.bounded_on_id_zero_one`.
  **So EVT's row 2 now rests on nothing asserted.**

  **The standing caveat**: inheriting a refutation is a proof obligation, not
  a citation. Since Rolle and MVT are equivalent up to a chord subtraction, a
  genuine row-2 construction for either is probably adaptable to the other —
  so the open question is one problem, not two.
- **MVT row 3 landed 2026-08-27, same day it was named the cheapest win**:
  `crates/axeyum-cas/src/mvt.rs`, `polynomial_mvt`/`verify_mvt_certificate`,
  18 tests. Kernel reconstruction (ADR-0601 §2) is the remaining step, not
  attempted here.
- FTA is the one family where the right question is still open ("does a
  constructive counterexample exist at all?"), not just unbuilt — see the
  re-assessment below, which confirms this and sharpens it: FTA's row 2 may
  not exist at all as a *distinct* row (see the FTA verdict).
