# Graded statement families: MVT, LUB, Taylor remainder, FTA

Status: measurement note (2026-08-27)

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
| **3. Exact form on the decidable fragment** | **Reachable, not built.** For a polynomial `p` with rational coefficients on `[a,b]`, MVT's conclusion becomes: does `q(x) := p'(x) − (p(b)−p(a))/(b−a)` have a root in the *open* interval `(a,b)`? Every ingredient already ships: `poly::rat_derivative` (exact differentiation), `real_algebraic::polynomial_ivt`/`verify_ivt_certificate` (exact sign-change root existence, the same machinery IVT's row 3 uses), and `extremum::polynomial_extremum` (differentiate + Sturm-isolate + exact compare) as the nearest existing analog — its 20 in-file unit tests (`cargo test -p axeyum-cas --lib extremum::`, confirmed 20 passed / 1 ignored / 0 failed this session) include a family of adversarial `verify_rejects_*` fixtures, which is the right shape for a re-derivation checker. Nothing in `axeyum-cas` currently assembles these into a `polynomial_mvt`/`verify_mvt_certificate` pair (`grep -rliE "mean_value\|mvt" crates/axeyum-cas/src/` is empty) — it is unbuilt, not blocked, and it is the **same shape** as `extremum.rs`, sized as a same-day task once someone picks it up. |
| **4. Labeled import** | Not attempted. `AxReal`'s 30-axiom package (`crates/axeyum-lean-kernel/src/arith_model.rs:1-13`) axiomatizes only "a commutative ring with 1, compatibly ordered" — no `inv`, no `div`, no completeness/supremum axiom, no Archimedean axiom, no MVT. There is no axiomatized carrier in this repository a classical MVT import would even attach to; building row 4 means adding new axioms first. |

**Verdict**: MVT's family is 1 real row (constructive substitutes, unregistered
as facts), 1 half-row (row 2 is an inherited assertion resting on an
unfinished EVT row 2, not a dedicated refutation), 1 reachable-but-unbuilt row
(row 3), 1 not-applicable-yet row (row 4, no axiomatized target exists).

---

## 2. Least upper bound / completeness (Spivak ch. 8)

| Row | Status |
|---|---|
| **1. Constructive general form** | **Bishop completeness**, `crates/axeyum-lean-kernel/src/creal/completeness.rs` (488 lines): every `RegularSeq` has a constructed limit — `CReal.limitSeq` (the diagonal `seq (X (2n+1)) (2n+1)`), `CReal.limitSeq_regular`, `CReal.limit`, `CReal.limit_dist`. All confirmed present via `prelude_theorem_inventory`/source read; the module doc states this is "constructed rather than merely asserted." |
| **2. Boundary refutation** | **Pure absence — no refutation exists anywhere in the repository.** `grep -rliE "least.upper.bound\|\blub\b\|supremum" crates/axeyum-lean-kernel/src/` matches only `arith_model.rs` and its test file, and both mentions are about `AxReal` **not carrying** a completeness axiom (a *design* fact, not a counterexample). No function is exhibited whose classical supremum is not constructively computable (the standard Brouwerian move — a bounded set built from an undecidable predicate whose sup would decide it — is not in this codebase under any name I could find: `specker`, `no.computable.supremum`, `LPO` all miss). `spivak.md`'s existing Ch. 8 row ("classical LUB unavailable") does not overclaim — it never says "refuted" — but this note makes explicit what was implicit: **the unavailability is asserted, not proved.** Building row 2 would need an actual constructive counterexample (e.g. a bounded, inhabited, located set with no computable least upper bound), which is standard Bishop-style material but is not built here. |
| **3. Exact form on the decidable fragment** | **`extremum::polynomial_extremum` computes exactly this for a polynomial on a closed interval.** For rational `p` on `[a,b]`, the supremum of `p`'s range *is* the maximum, and it is attained at a nameable algebraic point — decidable, exact, with an independent re-derivation checker (`verify_extremum_certificate`). This is the same file EVT's row 3 uses (ADR-0603 already labels it EVT row 3); it doubles as LUB's row 3 for the polynomial-range special case (attained sup ⇒ sup exists and is nameable). It does **not** generalize to an arbitrary bounded set of algebraic numbers (only ranges of a single polynomial over an interval), so it is a genuine but narrow row 3, not "LUB solved for the algebraic fragment" in full generality. |
| **4. Labeled import** | **Does not exist, and cannot attach to anything yet.** Confirmed via `arith_model.rs`, `docs/mathematics-2026-08/diary-real-keystone.md:26-30`, and ADR-0512 §(consequences): `AxReal` declares **no completeness/supremum axiom at all** — "There is no completeness (supremum) axiom, no Archimedean axiom, no density axiom — so nothing in it distinguishes ℝ from ℚ." A classical-LUB labeled import would need a *new* axiom added to (or a new package alongside) `AxReal` first; there is currently nothing to label. |

**Verdict**: row 1 is solid and well-documented (Bishop completeness). Row 2
is a **clean absence** — this is the single clearest case in this note of an
unavailability that is asserted in prose but never proved with a
counterexample, exactly the "hole in the Pareto argument" the task asked to
surface. Row 3 exists but only for the polynomial-range special case, reusing
EVT's own row 3 file. Row 4 has no target axiom to import against.

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
| **1. Constructive general form** | **Not built.** No FTA-shaped declaration exists under any name tried (`Complex.fundamentalTheoremOfAlgebra` confirmed absent via `kernel_declaration_projection`, non-zero exit). What HAS landed and is directly load-bearing, all confirmed present via `kernel_declaration_projection`: `Complex.polyEval`, `Complex.polyAdd`, `Complex.polyScale`, `Complex.polyDegreeLt`, `Complex.polyMul` (**with its two correctness theorems, `Complex.polyDegreeLt_polyMul` and `Complex.polyEval_polyMul`, both confirmed present** — landed 2026-08-27, same day as this note), `Complex.hornerFromTop` (+ its three reduction lemmas), and `Complex.factorQuotient` (+ `Complex.factorQuotient_degreeLt`). **`CReal.sqrt` now exists** (landed 2026-08-23, `crates/axeyum-lean-kernel/src/creal/sqrt.rs`, total, no `0 ≤ x` hypothesis) and **`Complex.abs` now exists on top of it**, confirmed present, with `Complex.abs_nonneg`, `Complex.abs_congr`, `Complex.abs_one`, `Complex.abs_mul`, and — landed 2026-08-26 — **`Complex.abs_add_le`, the triangle inequality for the modulus**. `Complex.exp` and `Complex.arg` remain confirmed absent. None of this assembles into FTA itself: a general constructive FTA needs a minimum-modulus / compactness argument over ℂ that this repository has not attempted (no holomorphic-function theory, no argument principle, no min-modulus machinery beyond the single-polynomial `extremum.rs` construction, which is real-valued and interval-bounded, not a 2-D compactness argument). |
| **2. Boundary refutation** | **Not established, and unlike MVT/LUB/IVT/EVT it is not clear one is even true.** No refutation of a constructive FTA exists in this codebase (`grep -rliE "\bfta\b\|fundamental theorem of algebra"` across `docs/` finds only "Lean-horizon"/scope-boundary notes, e.g. `docs/curriculum/02-structures/polynomials.md:46`, `docs/learn/math/complex-analysis-theorem-boundary.md:48`, never a counterexample). More importantly: FTA is **not obviously in the same constructive-failure class as IVT/EVT/MVT/LUB**. Those all fail because they assert something is *found* via an undecidable comparison over an unbounded domain. FTA is stated over a *compact* set (any disk large enough to contain all roots by the standard bound), and Bishop-style constructive analysis is known to have approximate constructive proofs of FTA using an infimum-of-modulus argument that does not require deciding real equality anywhere — this project has neither built that route nor refuted it. This row should read **"unassessed"**, not "unavailable": the honest gap is that nobody has yet determined whether FTA belongs with IVT/EVT (genuinely refuted) or with the ch. 9–10 derivative rules (constructively fine, just not yet built). |
| **3. Exact form on the decidable fragment** | **Not reachable today — this is the real gap, and it is an infrastructure gap, not a proof-difficulty one.** For rational-coefficient polynomials, an "FTA on the decidable fragment" would mean: isolate and name every complex root exactly (real root isolation's 2-D analogue). Searched for any such route (`weyl`, `durand.kerner`, `argument principle`, `complex.*isolat` across `crates/axeyum-cas/src/`) and found **none**. `axeyum-cas`'s `solve()` handles complex roots only for degree ≤ 2 in closed radical form and declines irreducible cubic-or-higher factors by design (same restriction `real_algebraic::real_roots` was built to lift for the *real* line only). `real_algebraic.rs`/`sturm.rs` isolate REAL roots of a real polynomial; there is no companion that isolates complex roots of a general (possibly complex-coefficient) polynomial via, e.g., a certified 2-D bisection or a resultant-based real/imaginary decomposition. `docs/research/10-cas/gap-analysis.md` G17 labels "roots/factorization over ℂ" as `certified (arithmetic/algebraic); complex analysis → heuristic` for the parts that exist (ℚ(i) arithmetic, radical-form quadratics/cubics), which is a much narrower claim than "isolate all roots of a degree-n polynomial." Building this would need a genuinely new algorithm, not an assembly of existing pieces the way MVT's row 3 is. |
| **4. Labeled import** | Not attempted; same "no target axiom package" situation. |

**Verdict**: the polynomial infrastructure (evaluation, multiplication with
its correctness theorems, synthetic division/factor-quotient, `sqrt`, `abs`
with the triangle inequality) is much further along than `spivak.md` says —
see corrections below. But this infrastructure does not compose toward any
FTA row without genuinely new mathematics: row 1 needs a compactness
argument this repository has never attempted, row 2's very applicability is
unassessed, and row 3 needs a complex root-isolation algorithm that does not
exist in any form here.

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
- EVT's own row 2 (`extremum.rs`'s "in progress" note) should be finished
  before leaning on it to justify MVT's inherited unavailability.
- MVT row 3 (`polynomial_mvt`) is the single cheapest win named in this
  note: every ingredient it needs already ships and is unit-tested.
- FTA is the one family where the right question is still open ("does a
  constructive counterexample exist at all?"), not just unbuilt.
