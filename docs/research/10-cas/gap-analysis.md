# Gap analysis — from substrate to CAS

Status: design note (2026-07-20)
Last updated: 2026-07-20

> **Implementation status (2026-07-20):** the build units below are essentially
> all implemented — **G0–G18 shipped** in `crates/axeyum-cas` (differentiation,
> integration, expand/cancel/factor/solve/apart/simplify, limit, series,
> summation, ODEs, linear algebra incl. eigenvalues, number theory, multivariate
> polynomials + GCD, **Gröbner bases**, complex numbers with certified `I²=−1`,
> and the Pythagorean identity in the zero-test). See the
> [README capability table](README.md#implemented) and [diary.md](diary.md) for
> the current surface (130+ tests). This document is retained as the original
> gap map; the *next wave* beyond G18 is tracked in
> [next-wave-roadmap.md](next-wave-roadmap.md) (SymPy/Mathematica capability
> survey — Risch integration, factorization over ℚ, assumptions, Smith/Hermite,
> Gosper/Zeilberger, special functions, more ODE classes) and
> [curriculum-gaps.md](curriculum-gaps.md) (the union of the seven per-branch
> curriculum reviews, Tier A–D). **Coverage target: ≥ SymPy, → Mathematica**, as
> enumerated by the 23-node curriculum + K-12 layer.

What must be built, given [substrate-map.md](substrate-map.md) (what exists) and
[cas-architecture-survey.md](cas-architecture-survey.md) /
[decidability-map.md](decidability-map.md) (the target). Ordered into build units
by **leverage × decidability × substrate-reuse** — decidable, high-reuse,
foundational units first.

## The foundational gap (blocks everything else)

**G0 — the `axeyum-cas` expression layer + reduce-to-decide certifier.**
Nothing certifiable ships without: (a) a CAS expression representation (reuse the
IR `TermArena` for the decidable fragment; a thin `CasExpr` for broader heads),
(b) a **substitution / match-and-rewrite API** (missing today — only structural
`replace_subterms`), and (c) the **lowering-to-decide** bridge that turns a
correctness obligation into an IR term and calls a decision procedure, returning
the witness + trust tag. This is the spine of the whole initiative.

## Build units (each: gap · nearest asset · certificate route · decidability)

| # | Build unit | Nearest existing asset | Certificate route | Class |
|---|---|---|---|---|
| **G1** | **Rational-function differentiation over terms** (`d/dx`, sum/product/quotient/power rules) | `poly.rs::rat_derivative` (numeric univariate) | exact `poly.rs` match + QF_NRA identity | **certified**, decidable |
| **G2** | **Polynomial canonical form + decidable `equal?`/zero-test on terms** | `poly.rs` normal form; `COMMUTATIVE_ORDER` canonicalizer | `poly.rs` normal form is the witness; QF_NRA fallback | **certified**, decidable |
| **G3** | **Multivariate polynomial representation** (sparse, domain tower ℚ/ℤ/𝔽ₚ) | univariate `RatVec` only | structural; feeds G4–G6 | infra |
| **G4** | **Multivariate GCD (subresultant PRS) + square-free** | `rat_gcd`, `squarefree_part` (univariate) | cofactor/Bézout re-multiply | **certified** |
| **G5** | **Univariate factorization over 𝔽ₚ/ℤ/ℚ** (Berlekamp–Zassenhaus + Hensel + LLL) | `squarefree_part`, resultants | re-multiply factors ≡ input | **certified** |
| **G6** | **Gröbner bases (Buchberger → F4) + ideal membership** | resultants (`sylvester_*`) | reduction-to-zero cofactor certificate | **certified** |
| **G7** | **Expand / collect / directed `simplify` (partial, per-substep certified)** | canonicalizer (~60 fixed rules), e-graph (matches, no apply) | each substep lowers to a decidable zero-test; frontier labeled | mixed |
| **G8** | **General rewrite / equality-saturation engine** (apply + cost-extract on the e-graph) | `axeyum-egraph` (matches only; no saturation/extract) | rewrites are manifested denotation-preserving rules | infra |
| **G9** | **Exact symbolic linear algebra** (matrix type; Bareiss solve/det/rank; Hermite/Smith; char. poly) | internal `Vec<Vec<RatVec>>` for resultants | residual `A·x−b≡0`; unimodular `U·A·V=S` | **certified** |
| **G10** | **Transcendental heads** (exp/log/sin/cos/sqrt as CAS ops) + differentiation rules for them | none (IR has no such heads) | per-rule denotation (Lean-liftable); values via `real_algebraic` where algebraic | decidable-uncertified |
| **G11** | **Integration** — rational functions (partial fractions, exact), then elementary (Risch–Norman/heurisch), self-certified by differentiate-and-check | `poly.rs` (partial fractions buildable from GCD/factor) | **differentiate answer + zero-test vs integrand** | **certified** (when returned) |
| **G12** | **Series** (Taylor/Laurent to finite order) + **limits** (Gruntz) | `eval`, `poly.rs` | truncation identity; limit value (cert route open) | certified / decidable-uncertified |
| **G13** | **Summation** — Gosper (indefinite), Zeilberger (definite, holonomic) | — | telescoping/recurrence certificate, zero-tested | **certified** |
| **G14** | **Equation solving** — linear/polynomial (Gröbner/resultants), then transcendental (heuristic) | `solve_eqs`, resultants | substitute-back + zero-test; completeness only on the decidable fragment | mixed |
| **G15** | **Assumptions engine** (3-valued predicates; derive over composites) | none | gates domain-sensitive certified rewrites (`sqrt(x²)→|x|`, branch cuts) | infra (mid-phase) |
| **G16** | **Number theory compute surface** (primality certs, integer factorization) | BV/LIA scenarios (verification-shaped) | ECPP/AKS cert; re-multiply factors | **certified** |
| **G17** | **Complex numbers** (ℚ(i) + complex-algebraic arithmetic; roots/factorization over ℂ) — the `complex` curriculum node | `real_algebraic.rs`, `poly_big.rs` | substitute-back zero-test; algebraic-number witness | **certified** (arithmetic/algebraic); complex analysis → heuristic |
| **G18** | **Differential equations** (symbolic ODE solving) | G11 (integration), G5 (factorization) | **substitute solution into ODE + zero-test residual** (differentiate-and-check) | **certified** when returned (linear const-coeff decidable); general → heuristic |

See [curriculum-coverage.md](curriculum-coverage.md) for the full node-by-node
map. Geometry is **not** a build unit — it is a scenario/example suite over the
RCF/CAD core (G6/NRA), per suite B of
[foundational-example-suites.md](../08-planning/foundational-example-suites.md).

## Ordering rationale

- **G0 → G1 → G2 first**: the thin vertical slice. It exercises the whole spine
  (CAS expr → transform → lower-to-decide → witness + tag) on the smallest fully
  decidable, high-value capability, and directly answers the user's exemplar
  `D[x²+c] = 2x`. Everything downstream reuses G0's substitution/lowering API.
- **G3 → G4 → G5 → G6**: the polynomial tower — the certified heart of any CAS
  and axeyum's strongest turf. High reuse of exact arithmetic; all `certified`.
- **G8 (rewrite engine)** is deferred until after the polynomial normal forms,
  because on the decidable fragment a *normal form* beats a rule-search, and G8's
  main early use (G7 directed simplify) needs the polynomial core first.
- **G10 (transcendental heads)** is where the trust ceiling first drops below
  `certified`; sequence it after the polynomial/linear-algebra certified core so
  the certified surface is broad before the heuristic frontier opens.
- **G11 (integration)** is the flagship proof-carrying demo (differentiate-and-
  check), but it depends on G1 (differentiation), G4/G5 (partial fractions), and
  G10 (elementary heads) — so it is a mid/late milestone, sequenced deliberately.
- **G15 (assumptions)** lands when the first domain-sensitive certified rewrite
  needs it (around G7/G10), not before.

Full phasing with exit gates: [build-plan.md](build-plan.md).
