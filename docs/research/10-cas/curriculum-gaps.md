# Curriculum coverage gaps — union of the per-branch reviews

Status: roadmap synthesis (2026-07-20)
Last updated: 2026-07-20

Seven sub-agents each reviewed one branch of [`docs/curriculum/`](../../curriculum/)
against the CAS roadmap (`gap-analysis.md`, `build-plan.md`, `curriculum-coverage.md`,
`decidability-map.md`, `README.md`) **and against the actual `crates/axeyum-cas`
code**. This note is the union of what they found MISSING — the answer to "does
our roadmap include everything necessary?" It complements
[next-wave-roadmap.md](next-wave-roadmap.md) (the SymPy/Mathematica capability
survey); where they overlap, an item is doubly-confirmed and prioritized up.

**Method note:** every gap below was verified against source, not just docs. The
reviews also surfaced *documentation* defects (over-claims in the roadmap) that
are corrected in §5.

## 1. Branch-by-branch verdict (one line each)

| Branch | Verdict |
|---|---|
| **00-foundations** | Essentially covered — the finite/Boolean content correctly routes to the SAT/EUF/BV solver; induction's polynomial-sum need is *shipped* (`sum_polynomial`). One doc-attribution nit (propositional-logic credited to CAS `simplify`; it's SAT). |
| **01-number-systems** | Naturals/integers/rationals solid. **Reals is the weak point**: `RealAlgebraic` exists in `axeyum-ir` but is *never wired into `axeyum-cas`*, has no `inv`/`div`, and `solve` silently declines degree ≥ 3. Radical simplification, `evalf`, continued fractions absent. Complex = `I`-symbol identity-checking only (not a ℚ(i) type). |
| **02-structures** | Divisibility/modular/polynomial-arithmetic solid. **Finite groups/rings, 𝔽_{pⁿ} extension fields, multivariate factorization, public resultant/discriminant, cyclotomics, permutation-as-object, linear-recurrence closed forms** are all unroadmapped. |
| **03-destinations** | Calculus analytic core good. **Eigenvectors, minimal polynomial, vector calculus (grad/div/curl)/Jacobian, LU/QR/Cholesky/Gram–Schmidt, Legendre/Jacobi/primitive-roots/CF/Pell, discrete log, Taylor-about-a-point, improper/multiple integrals, Jordan form, Laurent/Puiseux** absent or only label-deep. |
| **foundational-books** | Confirms 03 + adds **definite/Riemann integration** (cheapest win — `integrate`+`substitute`+`equal` already exist), **Taylor remainder bound**, sup/inf & IVT/EVT shadows, series-convergence tests, continuity/curve-sketching predicates, SOS/Positivstellensatz (the named NRA frontier), inner-product/norm layer. |
| **k12** | Elementary layer under-served: **radical simplification, inequality solving, exact trig values, statistics (mean/median/var), absolute value, rationalizing denominators, log rules, nPr + probability, coordinate geometry, functions/graphing, percent/ratio, decimal display**. Also: no K-12 *math* coverage doc exists (the `k12/` dir is a SAT/SMT logic curriculum). |
| **reconstruction-targets** | The decidability *line* is sound but the **CAS-witness → Alethe/Lean bridge is undesigned and unscheduled**; `decidability-map.md`'s certificate-route column overstates what ships (`equal` is a self-contained `MultiPoly` normal form, never lowers to the solver); `is_prime` tag (ECPP/Pratt) mismatches the deterministic-Miller–Rabin code; only Peano `add` is frozen as a target (cardinality/complex/limits/calculus/Bernoulli stubs promised, absent). |

## 2. Consolidated MISSING list, ranked by (value × certifiability × buildability-now)

**Tier A — cheap, certifiable, buildable on existing machinery (do first):**

1. **Eigenvectors** — nullspace of `A−λI` per eigenvalue. Cert: `(A−λI)v ≡ 0`. *(03, foundational-books)*
2. **Nullspace + explicit rank basis** — RREF free-columns. Cert: `A·nᵢ ≡ 0`. *(03)*
3. **Minimal polynomial** — factor char-poly, least annihilator. Cert: `m(A) ≡ 0`. *(03)*
4. **Definite integration** — evaluate the *certified* antiderivative at bounds (FTC). Cert: inherited from `integrate`. *(foundational-books #1 — "cheapest missing item")*
5. **Taylor/series about an arbitrary center `a`** — `series(f, x, a)` via `x→x+a`. Cert: truncation identity. Also **fixes** the README over-claim (current `series` is Maclaurin-only). *(01, 03, foundational-books)*
6. **Radical simplification** — `sqrt(n)→k·sqrt(m)` (extract square factors), rationalize denominators. Cert: square-back `equal`. *(k12 #1, 01 #3)*
7. **Number-theory bundle** — Legendre/Jacobi, quadratic residues, primitive roots, `multiplicative_order`, discrete log (BSGS), continued fractions, Pell, `nPr`. Cert: direct re-check. *(02, 03, foundational-books, k12 — building now)*
8. **Basic statistics** — mean/median/mode/variance/stddev over exact rationals. Cert: exact arithmetic. *(k12 #4)*
9. **Vector calculus + Jacobian** — grad/div/curl/`jacobian` via multivariate `differentiate` → `Matrix`. Cert: each entry a certified partial. *(03 #4)*
10. **Univariate factorization over ℤ/ℚ** (Berlekamp–Zassenhaus). Cert: re-multiply `equal`. *(02, 03, polynomials — building now)*

**Tier B — moderate, still certifiable:**

11. **Linear-recurrence closed forms** (Fibonacci-style, char-poly of the recurrence) — the difference-equation analogue of `dsolve_homogeneous`. Cert: substitute into recurrence. *(02 #8)*
12. **First-order ODE methods** (separable/exact/integrating-factor/Bernoulli). Cert: substitute-back. *(next-wave #4)*
13. **Absolute value head `Abs`** + `sqrt(x²)→|x|` (assumptions-gated). *(k12 #5)*
14. **Public `resultant`/`discriminant`** — expose the existing Sylvester machinery. Cert: cofactor. *(02 #5)*
15. **Cubic/quartic solve** (Cardano/Ferrari) or documented RootOf routing for degree ≥ 3. Cert: substitute-back. *(01 #6)*
16. **`evalf`** — n-digit / interval numeric evaluation (rationals exact; `RealAlgebraic::approx_midpoint`; transcendental heads via bounded series). *(01 #4)*
17. **Wire `RealAlgebraic` into `axeyum-cas`** + add `RealAlgebraic::inv`/`div` — lets `solve`/`equal` return/certify degree ≥ 3 real roots. *(01 #1–2 — the biggest single 01 gap)*
18. **Inequality solving** (linear/quadratic → interval, via sign analysis / real-root isolation). *(k12 #2)*
19. **Exact trig values at special angles** (`sin(π/6)=1/2` table) + basic trig-equation solving. *(k12 #3)*
20. **Log-rule simplifier** (product/quotient/power/change-of-base), assumptions-gated. *(k12 #7, foundational-books)*
21. **Finite-field extensions 𝔽_{pⁿ}** (irreducible-poly modulus arithmetic). Cert: substitute-and-check. *(02 #4)*
22. **Finite group/ring computation** (Cayley tables from generators, axiom checks, order, subgroup/zero-divisor search). Cert: finite enumeration. *(02 #1–2)*
23. **Permutations as objects** (cycle notation, composition) — feeds symmetric/dihedral groups. *(02 #7)*
24. **Curve-sketching classification** (2nd-derivative test / sign of `f'` on intervals). *(foundational-books #6)*
25. **Gram–Schmidt / QR / LU / Cholesky (exact)** + inner-product/norm layer. Cert: orthogonality zero-test / `L·U≡A` residual. *(03 #5, foundational-books #9)*

**Tier C — harder or weaker-certificate (sequence later, several already in next-wave):**

26. Gosper / Zeilberger summation *(next-wave #1, #14)*; 27. Laurent/Puiseux series + residues *(next-wave #10)*; 28. Improper & multiple integrals *(03)*; 29. Jordan / rational canonical form *(03)*; 30. Multivariate factorization *(02)*; 31. Cyclotomic polynomials *(02)*; 32. Special functions (Γ, erf, Bessel…) *(next-wave #11)*; 33. trigsimp via Euler *(next-wave #12)*; 34. Assumptions engine *(next-wave #13)*; 35. SOS/Positivstellensatz for the NRA-inequality frontier *(foundational-books #3, Spivak Ch.1)*; 36. Series-convergence tests, sup/inf & IVT/EVT decidable shadows *(foundational-books #4–5)*; 37. ℚ(i) as a first-class type + FTA/ℂ-factorization *(01 #7, G17)*; 38. Functions-as-objects, domain/range, coordinate geometry, percent/decimal-display *(k12 — pedagogy-facing)*.

**Tier D — cross-cutting infrastructure:**

39. **CAS-witness → Alethe/Lean bridge** — lower a `ZeroTest::Certified{witness}` (or Gosper/Bareiss/ODE residual) into a Lean-kernel term / Alethe step, reusing `axeyum-lean-kernel::arith_prelude` (ADR-0040 ring axioms). Currently undesigned; the only real "proof-carrying beyond the crate" story. *(reconstruction-targets #1)*

## 3. Doc-hygiene fixes the reviews demand (independent of new capability)

- **`series` is Maclaurin-only (`x=0`)** but README/build-plan say "Maclaurin/**Taylor**" → fixed by item 5, and the README wording corrected meanwhile.
- **`decidability-map.md` certificate-route column overstates the shipped code**: `equal` is a self-contained `MultiPoly` normal form and never lowers to the solver / DRAT / Lean; several rows imply a bridge that doesn't exist. Add a "route: self-contained normal form (sound, not solver-lowered)" note and reserve the QF_NRA/DRAT/Lean claims for the (unbuilt) item 39.
- **`is_prime` tag** should read "deterministic Miller–Rabin, sound for n < 2⁶⁴" not "ECPP/Pratt/AKS certificate".
- **`curriculum-coverage.md` propositional-logic row** credits CAS `simplify`; it's the SAT engine — reword to match the honest `sets` row.
- **`build-plan.md` progress snapshot is stale** (lists shipped G4/G6/complex/ODEs as "Next"); reconcile with `gap-analysis.md`/`README.md`.
- **`is_prime`/number-theory** are not marked certified in the README table — correct once the re-check certificates land.

## 4. What is correctly out of scope (not gaps)

ε-δ/ε-N analysis, metric-space topology, measure theory, Cantor cardinality,
general Diophantine (MRDP), the induction/quantifier *schemas* themselves, and
complex analysis (residues/branch cuts) are **Lean-horizon by design** — the CAS
computes their decidable shadow and labels the rest. The reviews confirmed the
roadmap is honest about these; adding them as "compute targets" would violate the
no-false-certification rule. They belong to the P3.6/P3.7 Lean track (via item 39).

## 4b. Build status (2026-07-21) — 192 tests

**Tier A — all shipped, certified, TDD'd:** eigenvectors (1), null space (2),
minimal polynomial (3), definite integration (4), arbitrary-center Taylor (5),
radical simplification (6), the number-theory bundle (7 — `ntheory_advanced`),
statistics + `standard_deviation` (8), gradient/jacobian/divergence/curl (9),
univariate factorization over ℤ/ℚ (10 — `factor_int`, Berlekamp–Zassenhaus).

**Tier B/C — largely shipped:** `resultant`/`discriminant` (14); `solve` factors
degree-≥3 over ℚ; the sound `sqrt(c)²→c` zero-test fold (radical arithmetic +
irrational roots); `evalf` (16); **inhomogeneous linear ODEs** with polynomial
forcing (undetermined coefficients — the exp-free part of 12); **cyclotomic
polynomials**; **exact trig values** at multiples of π/12 (19); **LU** decomposition;
`expand_log` (20); the **`Abs` head** (13) + `√(x²)→|x|`; **vector** dot/cross/norm;
**Gosper** indefinite hypergeometric summation (next-wave #1); **Sturm real-root
isolation** + numeric approximation (next-wave #8); **polynomial inequality solving**
(18). Hermite/Smith normal form (9) is delegated (in flight).

**Still open:** first-order ODEs (12) and linear recurrences (11) — both blocked on
the [exp-tower substrate](exp-tower.md); full `RealAlgebraic`/RootOf wiring (17);
Zeilberger (needs the exp tower for the geometric fragment); Lazard–Rioboo–Trager
(needs RootOf, now unblocked by Sturm); assumptions engine (34); special functions.

**Newly identified substrate blocker.** First-order linear ODEs (12) and linear
recurrences (11) both need the zero-test to know `e^A·e^B = e^{A+B}`. The
opaque-atom representation keys `exp` by the render of its argument, so combining
requires summing argument *expressions* — an atom-representation refactor (carry
the argument `CasExpr`, add `fold_exponential`, mirroring the just-added
`fold_radical`). This is now the **next substrate step**: it unlocks first-order
ODEs, recurrences, and general `exp`/`log` simplification together. Sequenced
ahead of the assumptions engine (34).

## 5. Sequenced build plan for this wave

Tier A (items 1–10) first — all certifiable on today's machinery — then Tier B as
capacity allows, delegating self-contained modules (number theory, factorization,
special functions, finite fields) to sub-agents and building the linear-algebra /
calculus / statistics items in-crate. Each capability lands TDD'd with its
certificate and a real fixture, committed and pushed individually. Tier C/D items
graduate into [next-wave-roadmap.md](next-wave-roadmap.md)'s sequence. Doc-hygiene
fixes (§3) are applied opportunistically alongside the capabilities they touch.
