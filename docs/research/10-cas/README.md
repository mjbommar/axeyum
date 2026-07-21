# Computer Algebra System (CAS) — proof-carrying symbolic mathematics

Status: **implemented core + active expansion** (kickoff 2026-07-20)
Last updated: 2026-07-21

## Implemented (`crates/axeyum-cas` — pure Rust, WASM-safe, 421 tests, clippy-clean)

A working proof-carrying CAS. Results are exact; those marked below as *certified*
carry a machine-checked proof (a decidable zero-test / differentiate-and-check),
which also acts as a correctness backstop (out-of-fragment cases decline, never
return a wrong answer). Runnable demos: `examples/certified_calculus.rs`,
`examples/cas_tour.rs`.

| Area | Functions | Certified |
|---|---|---|
| Core | `differentiate`/`differentiate_n`, `substitute`, `expand`, `simplify`, `trigsimp`, `normalize`, `equal` (zero-test w/ witness, **Euler-sound for related trig atoms**) | equal ✓ |
| Rational | `cancel` (uni+multivariate), `apart`, `factor`, `factor_univariate_over_q`/`factor_expr` (full ℤ/ℚ, Berlekamp–Zassenhaus), `poly_gcd`, `poly_div`, `resultant`, `discriminant`, `cyclotomic_polynomial`, `degree`/`coeff`/`leading_coeff` | factor/apart/factor_expr ✓ |
| Equations | `solve` (rational, quadratic w/ simplified surds, **complex**, degree-≥3 factoring over ℚ, **elementary transcendental** `eˣ−5⇒ln5`); `solve_polynomial_system` (bivariate, Sylvester resultant); `real_roots` → `AlgebraicReal` (RootOf, any degree), `real_root_intervals`/`count_real_roots` (Sturm), `approximate_real_roots`; `solve_polynomial_inequality` | rational + radical + system ✓; Sturm-certified |
| Summation | `sum_polynomial` (telescoping), `gosper_sum` (indefinite hypergeometric) | ✓ |
| Summation (definite) | `definite_sum` (Σ over bounds), `gosper_sum` | ✓ |
| Complex analysis | `residue` (at a pole), `laurent_series` (principal part), `modulus`, `roots_of_unity` | exact |
| Approximation | `approx`: Padé, Lagrange/Newton interpolation; `least_squares_polynomial`, `rationalize` (f64→ℚ), `series_reversion` (compositional inverse) | exact |
| Integration | `integrate` → `CertifiedIntegral`: polynomials, full rational (Horowitz + Rothstein–Trager logs + `atan`), `∫k·f(ax+b)`, `∫p·eˣ`, `∫p·sin\|cos`, `∫p·eˣ·sin\|cos` (exp×trig), `∫sinᵐ·cosⁿ` (odd + even powers), `∫f+g` (linearity), `∫ln x/x`, `∫1/(x ln x)`, `∫tan`, `∫atan`, `∫p·ln`; **substitution/power-rule family**: `∫k·g′·gⁿ = k·gⁿ⁺¹/(n+1)` (reverse power rule — `∫(ln x)²/x`, `∫eˣ(eˣ+1)²`, `∫sin·cos³`), `∫k·f′/√f = 2k√f`, half-integer power rule `∫√(ax+b)`/`∫xᵐ√x`, `u=x²` for `∫x·S(x²)·{eˣ²,sin,cos}`; `definite_integrate` (FTC, folds exact constants), `improper_integrate` (±∞ bounds — `∫₀^∞ e^{−x}=1`, divergence declined) | ✓ (differentiate-and-check / FTC) |
| Analysis | `limit` (rational; transcendental `0/0` via series — `sin x/x=1`, `tan x/x=1`; **exponential dominance** at ±∞ — `x²/eˣ=0`), `series`/`series_at`/`laurent_series` (incl. `tan`), `sum_polynomial`, `evalf` (f64), finite calculus | limit/sum ✓ |
| Transforms | `laplace_transform` + `inverse_laplace`, `z_transform` + `inverse_z_transform` (discrete; simple poles, round-trip-certified) | ✓ |
| ODEs / recurrences | `dsolve_homogeneous`, `dsolve_inhomogeneous` (polynomial forcing), `dsolve_first_order_linear` (integrating factor), `dsolve_separable`, `dsolve_exact`, `dsolve_bernoulli`, `solve_recurrence` (rational **and** quadratic-irrational roots — incl. **Fibonacci**/Binet); `wronskian` | ✓ (substitute-and-check) |
| Trig | `evaluate_trig` (exact values at π/12 multiples), `rewrite_exp` (Euler) → **all polynomial trig identities decidable**; trig-equation solving via `solve` (`2sin x−1⇒π/6,5π/6`, principal in [0,2π)) | values compute; identities ✓ |
| Complex | `imaginary_unit` (`I²=−1`), `conjugate`, `real_part`, `imaginary_part`, `modulus`, `roots_of_unity` | ✓ |
| Linear algebra | `Matrix`: +/−/×, determinant (+ Bareiss), RREF, solve, inverse, `adjugate`/`cofactor`, `pow`, `hadamard`/`kronecker`, `null_space`, `lu`, `rank`, `trace`, char-poly, `eigenvalues`/`eigenvectors`, `minimal_polynomial`, `diagonalize` (P·D·P⁻¹), `jordan_form` (P·J·P⁻¹, **defective** via generalized eigenvectors), `matrix_exp` (e^{At}, rational spectrum incl. defective), `linear_ode_system` (x′=Ax), Hermite/Smith, `gram_schmidt`; `companion_matrix`, `solve_linear_system`, `least_squares_polynomial` | det/solve/eigvec/diag/jordan/matexp/ODE/companion ✓; A·P=P·J ✓ |
| Logic / sets | `boolean::BoolExpr` (truth tables, tautology/SAT, DNF/CNF, Quine–McCluskey); `sets::RealSet` (interval unions, set algebra, measure); `interval_arith::Interval` (rigorous enclosures) | truth-table / exact ✓ |
| Special functions | `special`: `gamma`/`beta`, `zeta`/`dirichlet_eta`/`dirichlet_lambda`, `polygamma_at_one`, `gamma` at negative half-integers; **integral-defined heads** `erf`, `Si`/`Ci`/`Ei`, `li`, `Shi`/`Chi`, Fresnel `S`/`C`, `BesselJ0`/`J1`, `asin`/`acos`/`asinh`/`acosh` — with **certified defining integrals** (∫e^{−x²}=(√π/2)erf incl. completing-the-square, ∫sin x/x=Si, ∫eˣ/x=Ei, ∫1/ln x=li, ∫sinh x/x=Shi, ∫sin(πx²/2)=S, ∫1/√(1−x²)=asin, ∫1/√(x²+1)=asinh) + numeric `evalf`; `hyperbolic`: sinh/cosh/…/atanh (via exp tower) | ✓ (deriv-check / identities / Bernoulli) |
| Finite fields | `gfp`: 𝔽ₚ[x] ring ops, gcd, `is_irreducible`, `factor_berlekamp`, `roots` | re-multiply ✓ |
| Groups | `Permutation`: compose, inverse, cycles, order, sign (symmetric groups) | group laws ✓ |
| Boolean algebra | `boolean::BoolExpr`: truth tables, tautology/SAT, DNF/CNF, `equivalent`, Quine–McCluskey minimization | truth-table ✓ |
| Geometry | `geometry`: `Point`/`Line`/`Circle` — distance, midpoint, slope, collinear, triangle area, line ops, circumcircle | exact |
| Vector calculus | `gradient`, `jacobian`, `divergence`, `curl`, `hessian`, `laplacian` (certified partials); `dot`, `cross`, `norm` | ✓ |
| Special polys | `orthopoly`: `chebyshev_t`/`chebyshev_u`/`legendre`/`hermite`/`laguerre` (three-term recurrences) | ✓ (vs closed forms) |
| Combinatorics | `combinatorics`: `bernoulli`, `euler_number`, `stirling_first`/`second`, `bell`, `partition_count`, `catalan`, `fibonacci`/`lucas`, `harmonic`/`generalized_harmonic`, `derangements`, `double_factorial`, `multinomial`, `pell`/`jacobsthal`/`tribonacci`/`motzkin`, `eulerian`/`narayana`/`lah` (triangles); `bernoulli_polynomial`/`euler_polynomial`; `finite_product` (∏) | exact |
| Logs / abs | `expand_log`, `logcombine` (product/quotient/power rules), `Abs` head (`|·|`, `√(x²)→|x|`) | compute / exact |
| Statistics | `stats`: mean/median/mode/variance/covariance; `standard_deviation`, `correlation` (surd-simplified) | exact |
| Radicals | `simplify_radicals` (`√12→2√3`, rationalize denominators) | exact (`k²·m=c`) |
| Number theory | `ntheory` (gcd, mod-pow/inverse, `is_prime`, `factorize`, φ, CRT, binomial); `ntheory_advanced` (nPr, Legendre/Jacobi, quadratic residues, `sqrt_mod` (Tonelli–Shanks), `kronecker_symbol`, `solve_linear_congruence`, order, primitive root, discrete log, continued fractions, Pell); `ntheory_more` (Möbius, Mertens, σ_k, perfect/squarefree, radical, `perfect_power`, `integer_nth_root`, `aliquot_sum`/`are_amicable`, `primitive_pythagorean_triples`, Carmichael λ, primorial, next/prev prime, π(n), nth prime, Carmichael numbers) | re-check ✓ |
| Multivariate | `mvpoly::MvPoly`: ring ops, division, **GCD** (primitive PRS), square-free | — |

Heads: `exp, sin, cos, tan, ln, atan, sqrt, abs`, the inverse pair
`asin/acos/asinh/acosh`, and the special functions `erf, Si, Ci, Ei, li, Shi, Chi,
FresnelS, FresnelC, BesselJ0, BesselJ1` (extensible `Unary` — each adds a `name`,
derivative, `series` rule, and `evalf` kernel; everything else is catch-all). The zero-test
carries sound folds — `I²=−1`, Pythagorean `sin²+cos²=1`, the **symbolic radical
fold** `(√u)²=u` for any `u` (not just constants — so `x/√x=√x` certifies), and the
**exp tower** (`exp(A+B)=exp(A)exp(B)`, `exp(2x)=exp(x)²`, `exp(k·ln v)=vᵏ`) — which
is what makes complex arithmetic, radical arithmetic, first-order ODEs, and
recurrences certify. Progress log: [diary.md](diary.md).

**Coverage target.** At least SymPy's compute surface, aiming at Mathematica's —
the yardstick is the 23-node [curriculum](../../curriculum/) plus its K-12 layer.
The prioritized continuation lives in [next-wave-roadmap.md](next-wave-roadmap.md)
(capability survey) and [curriculum-gaps.md](curriculum-gaps.md) (the union of the
seven per-branch curriculum reviews, Tier A–D). Active build wave (Tier A):
eigenvectors, definite integration, arbitrary-center Taylor, radical
simplification, the number-theory bundle (Legendre/Jacobi, primitive roots,
discrete log, continued fractions, Pell, `nPr`), statistics, vector
calculus/Jacobian, integer factorization. Longer tail: Gosper/Zeilberger,
assumptions, trig/log identity simplification, special functions, Risch, more
ODE/integration classes.

---

> This section plans a new major capability: **a computer algebra system in
> axeyum with the compute-side functionality of SymPy / Mathematica** —
> differentiate, simplify, factor, expand, solve, integrate, series, limits,
> summation, and symbolic linear algebra — built the axeyum way. It is
> research-and-design first: nothing lands without semantics, a checker, and a
> self-checking test, exactly as the [foundational
> DAG](../08-planning/foundational-dag.md) and
> [ADR-0008](../09-decisions/adr-0008-consumer-scenario-models.md) require.

## The one-sentence thesis

Every mainstream CAS *computes* a transformed expression and asks you to trust
it; axeyum already *decides and certifies* mathematical facts. A CAS built on
axeyum is therefore the first **proof-carrying CAS**: it returns
`transform(expr)` **and** — wherever the fragment is decidable — a checkable
witness that `transform(expr)` is equal to (or a sound normalization of) `expr`,
with `unknown`/`uncertified` as a first-class, honestly-labeled outcome
everywhere else.

This is axeyum's "untrusted search / trusted checking" identity
([north star](../00-orientation/north-star.md)) applied to algebra. It is not a
reimplementation of Mathematica; it is the thing Mathematica cannot be — a CAS
that tells you exactly which of its answers carry a machine-checked proof.

## Why this is tractable now (not a decade-scale moonshot)

The reason a *correct* CAS is historically a decades-long problem is not writing
`diff` — it is *knowing the transforms are right across mathematics*. axeyum has
already built the hard half:

1. **The expression substrate exists.** The hash-consed `axeyum-ir` `TermArena`
   is exactly Mathematica's `head[args...]` DAG. `axeyum-rewrite` is a
   denotation-preserving rewrite engine with a `RewriteManifest`; `axeyum-egraph`
   is congruence closure / equality saturation; `axeyum-ir::poly` is exact
   rational polynomial algebra (`rat_derivative`, `rat_gcd`, `squarefree_part`,
   …). (Exact inventory: [substrate-map.md](substrate-map.md).)
2. **The correctness oracle exists.** The self-checking scenario corpus
   (`axeyum-scenarios`), the [curriculum knowledge graph](../../curriculum/), and
   the [formal-mathematics tour](../08-planning/formal-mathematics-tour.md) are a
   curriculum-organized, **self-grounded** (oracle-free at small width; see
   [ADR-0008](../09-decisions/adr-0008-consumer-scenario-models.md)) corpus of
   machine-checkable mathematical identities — i.e. a **test harness for a CAS**.
3. **The decision procedures are the checker.** The [capability
   matrix](../08-planning/capability-matrix.md) shows certified procedures across
   QF_BV/UF/LIA/LRA/NRA/NIA/FP/arrays/datatypes/quantifiers, with DRAT / Alethe /
   Lean-kernel certificates. Polynomial zero-testing, RCF decision, exact linear
   algebra, and bounded number theory — the certifiable core of a CAS — are
   already decided here.

The remaining work is the **compute side** (the transformation functions), which
is comparatively mechanical *when every output can be checked against an existing
oracle*. That is the whole bet.

## The decidability spine (the load-bearing distinction)

The [decidability lens](../08-planning/foundational-example-suites.md) governs
everything. CAS operations split cleanly:

- **Certifiable core** (axeyum returns a checked witness): polynomial arithmetic,
  GCD, square-free/factor over ℚ and 𝔽ₚ, **differentiation of rational
  functions** (purely algebraic), polynomial/rational **canonical form and
  zero-testing**, exact linear algebra (Bareiss, Smith/Hermite), linear &
  polynomial equation solving, bounded/modular number theory, RCF-decidable
  inequalities.
- **Heuristic / undecidable frontier** (axeyum computes, labels `uncertified`,
  and certifies *only what it can decide*): general simplification of elementary
  expressions (**Richardson's theorem** — zero-testing is undecidable),
  transcendental integration (Risch — decidable for elementary functions with
  real caveats), transcendental equation solving, general limits & summation.

The differentiator is the boundary itself: axeyum is the CAS whose every result
is tagged `checked` / `validated` / `computed-uncertified`, and which uses its
own SMT/RCF engine as the zero-tester wherever zero-testing is decidable, instead
of SymPy's heuristic `simplify`.

## Relationship to existing plans

This initiative **extends**, and must not starve, the solver + Lean-parity
mission ([PLAN.md](../../../PLAN.md), [STATUS.md](../../../STATUS.md)). It is the
compute-side realization of destinations the research tree already names:

- [north-star.md](../00-orientation/north-star.md) — general reasoning/proving.
- [formal-mathematics-tour.md](../08-planning/formal-mathematics-tour.md) — the
  backward-derived math DAG and its per-node decidable fragment. **The CAS is the
  engine that makes those nodes *computational*, not just checkable.**
- [foundational-example-suites.md](../08-planning/foundational-example-suites.md)
  — double-duty artifacts; the oracle-free ground-truth contract.
- [capability-matrix.md](../08-planning/capability-matrix.md) — the certified
  decision procedures the CAS uses as its checker.

## Documents in this section

| File | Purpose | State |
|---|---|---|
| [diary.md](diary.md) | Running research + design + prototyping log with references | live |
| [vision.md](vision.md) | The full vision, thesis, and non-goals | done |
| [substrate-map.md](substrate-map.md) | Exact inventory of existing CAS-relevant code (file:line) | done |
| [cas-architecture-survey.md](cas-architecture-survey.md) | How SymPy / Mathematica / Symbolica are built; capability taxonomy | done |
| [decidability-map.md](decidability-map.md) | Per-capability decidable? / complete? / certificate route | done |
| [curriculum-coverage.md](curriculum-coverage.md) | Node-by-node map of the CAS onto the full 23-node curriculum (+ complex, ODEs, geometry) | done |
| [oracle-as-test-harness.md](oracle-as-test-harness.md) | Why the existing corpus is a non-circular CAS test harness | done |
| [gap-analysis.md](gap-analysis.md) | Substrate vs. target; 16 build units (G0–G18, all shipped) | done |
| [build-plan.md](build-plan.md) | Phased (C0–C7), decidable-first, TDD sequence with exit gates | done |
| [rational-integration.md](rational-integration.md) | `∫ P/Q dx` algorithm (Horowitz) + certification + log-part roadmap | done |
| [next-wave-roadmap.md](next-wave-roadmap.md) | Post-G18 SymPy/Mathematica capability survey; prioritized top-15 | live |
| [curriculum-gaps.md](curriculum-gaps.md) | Union of the 7 per-branch curriculum reviews; Tier A–D ranked gaps | live |

**Decisions:** [ADR-0301](../09-decisions/adr-0301-cas-layer-reduce-to-decide.md)
(the `axeyum-cas` layer + reduce-to-decide certifier).

**Code:** `crates/axeyum-cas` — Phase C0 certified polynomial kernel
(`differentiate` / `normalize` / decidable `equal`), 11 tests + doctest passing,
clippy-clean, WASM-green. See [diary.md](diary.md) entry 2.

## Standing rules for this initiative (inherited, non-negotiable)

- **Decidable-first, thin vertical slice first** ([ADR-0001](../09-decisions/adr-0001-vertical-slice-first.md)):
  the first slice is the certified polynomial kernel (canonicalize + differentiate
  + decidable equality), end to end, before any transcendental breadth.
- **Every transform ships with its checker and a self-checking scenario.** No
  compute function is public until its output is either denotation-preserving by
  a manifested rewrite rule or checked by a decision procedure, with a test.
- **`unknown`/`uncertified` is first-class.** Never present a heuristic result as
  certified; label the trust route per result (cf. the [trust
  ledger](../08-planning/trust-ledger.md)).
- **No oracle laundering.** SymPy/Mathematica/Z3 may be *differential oracles* in
  tests, never the ground truth of a shipped answer.
- **WASM-safe by default.** Pure Rust; the CAS runs where the solver runs.
