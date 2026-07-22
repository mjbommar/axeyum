# Computer Algebra System (CAS) — proof-carrying symbolic mathematics

Status: **implemented core + active expansion** (kickoff 2026-07-20)
Last updated: 2026-07-22

## Implemented (`crates/axeyum-cas` — pure Rust, WASM-safe, 512 unit + 147 doctests, clippy-clean)

> **Data-model frontier now built** (special functions & fractional powers, none needing a `Pow`
> representation change): the **gamma family** `Γ`, arbitrary-order **polygamma** `ψ⁽ⁿ⁾` (via
> `UnaryFunc::PolyGamma(u32)` — the index carried in the variant, so the derivative tower
> `ψ⁽ⁿ⁾′=ψ⁽ⁿ⁺¹⁾` stays closed), symbolic **factorial** `Γ(n+1)`, **Beta** `B(a,b)`, **binomial**
> `C(n,k)`; arbitrary-order **Bessel** `Jₙ`; **Airy** `Ai/Bi` (closing tower `Ai″=x·Ai`); **Lambert W**
> (+ `solve` for `x·eˣ=c`); the **nth-root** head `x^{1/q}` with `∫x^{p/q}` and the `root_q(u)^q=u`
> zero-test fold; **Puiseux series** `sin√x=√x−(√x)³/6+…`; and **Euler–Cauchy ODEs** `a₂x²y″+a₁xy′+a₀y=0`
> (`xʳ=exp(r·ln x)`). Techniques: parameterize the `UnaryFunc` variant, `x^r=exp(r·ln x)`, closing towers.

A working proof-carrying CAS. Results are exact; those marked below as *certified*
carry a machine-checked proof (a decidable zero-test / differentiate-and-check),
which also acts as a correctness backstop (out-of-fragment cases decline, never
return a wrong answer). Runnable demos: `examples/certified_calculus.rs`,
`examples/cas_tour.rs`.

| Area | Functions | Certified |
|---|---|---|
| Core | `differentiate`/`differentiate_n`, `substitute`, `expand`, `collect` (group by powers), `simplify`, `trigsimp`, `normalize`, `equal` (zero-test w/ witness, **Euler-sound for related trig atoms**, **log arithmetic** `2ln2−ln3=ln(4/3)` via prime-basis expansion) | equal ✓ |
| Rational | `cancel` (uni+multivariate), `apart`, `factor` (**full ℚ irreducible factorization** — peels rational roots then splits the degree-≥2 residual via Berlekamp–Zassenhaus, `x⁴+x²+1=(x²+x+1)(x²−x+1)`), `factor_univariate_over_q`/`factor_expr` (full ℤ/ℚ, Berlekamp–Zassenhaus); **bivariate** quadratics `x²−y²` and sum/difference of like powers `x³−y³=(x−y)(x²+xy+y²)`, `x⁵+y⁵`, `poly_gcd`, `poly_div`, `resultant`, `discriminant`, `cyclotomic_polynomial`, `degree`/`coeff`/`leading_coeff` | factor/apart/factor_expr ✓ |
| Equations | `solve` (rational, quadratic w/ simplified surds, **complex**, degree-≥3 factoring over ℚ; **elementary transcendental** `eˣ−5⇒ln5`, `ln x−2⇒e²`, `√x−3⇒9`; **polynomial in eˣ** `e^{2x}−3e^x+2⇒{0,ln2}`); `solve_polynomial_system` (bivariate, Sylvester resultant); `real_roots` → `AlgebraicReal` (RootOf, any degree), `real_root_intervals`/`count_real_roots` (Sturm), `approximate_real_roots`; `solve_polynomial_inequality` | rational + radical + transcendental + system ✓; Sturm-certified |
| Summation | `sum_polynomial` (telescoping), `gosper_sum` (indefinite hypergeometric), `infinite_sum` (**convergent** Σ_{k}^∞ — geometric `Σr^k=1/(1−r)`, p-series `Σ1/k²=π²/6` via ζ) | ✓ |
| Summation (definite) | `definite_sum` (Σ over bounds — polynomial via telescoping, **geometric/hypergeometric via Gosper**: `Σ 2^k = 2^{n+1}−1`, `Σ k·2^k`; geometric base recovered from any exponent spelling — `2^{−k}`, `(½)^k`, `Σ_{k≥0}2^{−k}=2`); `prove_wz_sum` (symbolically checked Wilf–Zeilberger certificates for binomial moments, **Vandermonde** `ΣC(n,k)²=C(2n,n)`, fixed-shift convolutions `ΣC(n,k)C(n,k+r)=C(2n,n−r)` for `r=1,2`, and the first three squared-binomial moments through `Σk³C(n,k)²=n³(n+1)C(2n,n)/(4(2n−1))`) | ✓ |
| Complex analysis | `residue` (at a pole; **transcendental numerators** `Res cos x/x=1`, `sin x/x⁴=−1/6` via `f^{(n−1)}(a)/(n−1)!`), `laurent_series` (principal part), `modulus`, `roots_of_unity` | exact |
| Approximation | `approx`: Padé, Lagrange/Newton interpolation; `least_squares_polynomial`, `rationalize` (f64→ℚ), `nsimplify` (f64→closed form, 1.5708→π/2, **quadratic surds** (1+√5)/2, **ln(rational)** 0.693→ln2), `series_reversion` (compositional inverse) | exact |
| Integration | `integrate` → `CertifiedIntegral`: polynomials, **complete univariate rational over ℚ** (Horowitz rational part + partial-fractions over ℚ-irreducible factors → logs, `atan` for irreducible quadratics **incl. surd** `∫1/(x²+x+1)`, and algebraic surd-logs for real-irrational-root quadratics `∫1/(x²−2)`; mixed factors `∫1/(x³+1)`), `∫k·f(ax+b)`, `∫p·eˣ`, `∫p·sin\|cos`, `∫p·eˣ·sin\|cos` (exp×trig), `∫sinᵐ·cosⁿ`, `∫sin(ax)·sin(bx)` product-to-sum (Fourier orthogonality), `∫f+g` (linearity); **by-parts**: `∫p·ln`, `∫p·(ln x)ᵐ`, `∫p·{atan,asin,acos,asinh,acosh}`; **substitution/power-rule**: `∫k·g′·gⁿ = k·gⁿ⁺¹/(n+1)` (`∫(ln x)²/x`, `∫eˣ(eˣ+1)²`, `∫sin·cos³`), `∫k·g′/g = k·ln g` (`∫cos/sin`), `∫k·f′/√f = 2k√f`, `u=eˣ` (`∫1/(eˣ+1)`), `u=sin/cos/tan` (`∫cos x/(1+sin²x)`, `∫1/cos²x=tan x`), **Weierstrass** `t=tan(x/2)` for all rational-trig `∫1/(a+b·cos x)`, `∫sec x`, `∫csc x`, half-integer power rule `∫√(ax+b)`/`∫xᵐ√x`, `u=x²` for `∫x·S(x²)·{eˣ²,sin,cos}`; special-function antiderivatives (erf/Si/Ci/Ei/li/Shi/Fresnel); `definite_integrate` (FTC; **full- and half-period rational-trig** `∫₀^{2π}`/`∫₀^π 1/(a+b·cos x)` via Weierstrass→improper, correct past the tan(x/2) discontinuity; special-angle inverse-trig boundaries fold — `∫₀^{√3}1/(1+x²)=π/3`; **Beta integrals** `∫₀^1 x^p(1−x)^q=B(p+1,q+1)` incl. half-integer `∫₀^1 1/√(x(1−x))=π`), `fourier_series` (Euler coeffs — `f=x` → 2sin x−sin2x+…), `numeric_integrate` (Simpson — `∫₀¹e^{−x²}≈0.7468` for non-elementary), `improper_integrate` (±∞ bounds; Gaussian `∫_{−∞}^∞ e^{−x²}=√π` via erf asymptote; **Gaussian moments** `∫_{−∞}^∞ x²ⁿe^{−x²}` via `(2m−1)!!` recurrence; **Gamma integrals** `∫₀^∞ x^p e^{−x}=Γ(p+1)` incl. half-integer `∫₀^∞ e^{−x}/√x=√π`; **Dirichlet/Fresnel** `∫₀^∞ sin x/x=π/2` via Si/Fresnel asymptotes; **Fourier via residues** `∫_{−∞}^∞ cos x/(x²+1)=π/e`, `∫ x·sin x/(x²+1)=π/e`; **Frullani** `∫₀^∞ (cos x−cos bx)/x=ln b`, `∫₀^∞ (e^{−ax}−e^{−bx})/x=ln(b/a)` (Ci/Ei/Chi combine at 0, sound past the log-singularity); **combining-log** boundaries `∫₀^∞1/(1+x³)=2π/(3√3)` where individual log terms diverge (surd-coefficient logs too → `∫_{−∞}^∞1/(x⁴+1)=π/√2`); `∫₀^∞1/(1+x²)=π/2`); **even quartic denominators** `∫1/(x⁴+px²+q)` via the real (surd) quadratic factorization `∫1/(x⁴+1)` (beyond ℚ partial fractions) | ✓ (differentiate-and-check / FTC) |
| Analysis | `limit` (rational; transcendental `0/0` via series — `sin x/x=1`, `tan x/x=1`; **exponential dominance** at ±∞ — `x²/eˣ=0`; **log-vs-power** at 0 — `x·ln x=0`, and at +∞ — `ln x/x=0`, `x^{1/x}=1`; **algebraic/conjugate** at +∞ — `√(x²+x)−x=½`, `√(x²+x)−√(x²−x)=1` via leading-term/conjugate analysis; **squeeze** — `sin x/x=0`; **1^∞** — `(1+1/x)^x=e` via reciprocal substitution; **combining logs** at ±∞ — `⅓ln(x+1)−⅙ln(x²−x+1)→0`; **L'Hôpital** for 0/0 beyond the rational-series fragment — `(2ˣ−1)/x→ln2`; **combining Ci/Ei/Chi** at 0 — Frullani `Ci(x)−Ci(2x)→−ln2`), `series`/`series_at`/`laurent_series` (incl. `tan`, `asin`, `asinh`; **Taylor about any center** with transcendental coefficients — `exp` about 1 → `e·[1+(x−1)+…]` via the derivative definition), `sum_polynomial`, `evalf` (f64), finite calculus | limit/sum ✓ |
| Transforms | `laplace_transform` (poly×{1,sin,cos} with the **s-shift rule** `L{e^{at}f}=F(s−a)` — `L{e^t sin t}`, `L{t·e^t·sin t}`) + `inverse_laplace` (simple real poles **and irreducible quadratics** → damped sinusoids `L⁻¹{1/((s−1)²+4)}=½e^t sin2t`, rational frequency), `z_transform` + `inverse_z_transform` (discrete; simple poles); `inverse_laplace` also handles **repeated real poles** (`1/s²→t`, `1/(s−1)²→t·e^t`); all round-trip-certified | ✓ |
| ODEs / recurrences | `dsolve_homogeneous` (constant-coeff, **any degree** with one irreducible-quadratic factor — real/repeated/**surd** roots: `y‴−y=0`→`e^x`+`e^{−x/2}`(cos,sin), `y″−2y=0`→`e^{±√2 x}`), `dsolve_inhomogeneous` (polynomial forcing; **variation of parameters** for exp/trig forcing — `y″−y=eˣ` incl. resonance, `y″+y=sin x`), `dsolve_first_order_linear` (integrating factor, incl. **variable** `p=k/x`→`μ=x^k` via `exp(ln)` folding, and **resonant** forcing `y′−y=eˣ`), `dsolve_separable`, `dsolve_exact`, `dsolve_bernoulli`, `apply_initial_conditions` (IVPs — y″+y=0, y(0)=1,y′(0)=0 ⇒ cos x), `solve_recurrence` (rational **and** quadratic-irrational roots — incl. **Fibonacci**/Binet); `wronskian` | ✓ (substitute-and-check) |
| Trig | `evaluate_trig` (exact values at π/12 multiples, **inverse-trig** atan(1)=π/4, asin(√3/2)=π/3), `rewrite_exp` (Euler) → **all polynomial trig identities decidable**, `expand_trig` (angle-addition/multiple-angle → trig form); trig-equation solving via `solve` (`2sin x−1⇒π/6,5π/6`, principal in [0,2π); **surd RHS** `2cos x−√3⇒π/6,11π/6`; **polynomial-in-sin/cos** `sin²x=¼⇒{π/6,5π/6,7π/6,11π/6}`, `2sin²x−3sin x+1=0`; **multiple angle** `sin 2x=0⇒{0,π/2,π,3π/2}`, `sin 3x=0`; surd `tan x=√3`; **linear combination** `cos x+sin x=0⇒{3π/4,7π/4}`) | values compute; identities ✓ |
| Complex | `imaginary_unit` (`I²=−1`), `conjugate`, `real_part`, `imaginary_part`, `modulus`, `argument` (phase — arg(1+i)=π/4), `roots_of_unity` | ✓ |
| Linear algebra | `Matrix`: +/−/×, determinant (+ Bareiss), RREF, solve, inverse, `adjugate`/`cofactor`, `pow`, `hadamard`/`kronecker`, `null_space`, `lu`, `rank`, `trace`, char-poly, `eigenvalues`/`eigenvectors`, `minimal_polynomial`, `diagonalize` (P·D·P⁻¹), `jordan_form` (P·J·P⁻¹, **defective** via generalized eigenvectors), `matrix_exp` (e^{At}, rational spectrum incl. defective), `linear_ode_system` (x′=Ax), Hermite/Smith, `gram_schmidt`, **`qr_decomposition`** (A=QR, surd-certified), **`cholesky_decomposition`** (A=L·Lᵀ, SPD, surd-certified); `companion_matrix`, `solve_linear_system`, `least_squares_polynomial` | det/solve/eigvec/diag/jordan/matexp/ODE/companion ✓; A·P=P·J ✓ |
| Logic / sets | `boolean::BoolExpr` (truth tables, tautology/SAT, DNF/CNF, Quine–McCluskey); `sets::RealSet` (interval unions, set algebra, measure); `interval_arith::Interval` (rigorous enclosures) | truth-table / exact ✓ |
| Special functions | `special`: `gamma`/`beta`, `zeta`/`dirichlet_eta`/`dirichlet_lambda`, `polygamma_at_one`, `gamma` at negative half-integers; **integral-defined heads** `erf`, `Si`/`Ci`/`Ei`, `li`, `Shi`/`Chi`, Fresnel `S`/`C`, `BesselJ0`/`J1`, `asin`/`acos`/`asinh`/`acosh` — with **certified defining integrals** (∫e^{−x²}=(√π/2)erf incl. completing-the-square, ∫sin x/x=Si, ∫eˣ/x=Ei, ∫1/ln x=li, ∫sinh x/x=Shi, ∫sin(πx²/2)=S, ∫1/√(1−x²)=asin, ∫1/√(x²+1)=asinh) + numeric `evalf`; `hyperbolic`: sinh/cosh/…/atanh (via exp tower); **piecewise-constant heads** `abs`/`sign`/`floor`/`ceiling` (constant folds, derivative 0, `sign` resolves ±1/0 under sign assumptions) | ✓ (deriv-check / identities / Bernoulli) |
| Finite fields | `gfp`: 𝔽ₚ[x] ring ops, gcd, `is_irreducible`, `factor_berlekamp`, `roots` | re-multiply ✓ |
| Groups | `Permutation`: compose, inverse, cycles, order, sign (symmetric groups) | group laws ✓ |
| Boolean algebra | `boolean::BoolExpr`: truth tables, tautology/SAT, DNF/CNF, `equivalent`, Quine–McCluskey minimization | truth-table ✓ |
| Geometry | `geometry`: `Point`/`Line`/`Circle` — distance, midpoint, slope, collinear, triangle area, line ops, circumcircle | exact |
| Vector calculus | `gradient`, `jacobian`, `divergence`, `curl`, `hessian`, `laplacian` (certified partials); `dot`, `cross`, `norm` | ✓ |
| Special polys | `orthopoly`: `chebyshev_t`/`chebyshev_u`/`legendre`/`hermite`/`laguerre` (three-term recurrences) | ✓ (vs closed forms) |
| Combinatorics | `combinatorics`: `bernoulli`, `euler_number`, `stirling_first`/`second`, `bell`, `partition_count`, `catalan`, `fibonacci`/`lucas`, `harmonic`/`generalized_harmonic`, `derangements`, `double_factorial`, `multinomial`, `pell`/`jacobsthal`/`tribonacci`/`motzkin`, `eulerian`/`narayana`/`lah` (triangles); `bernoulli_polynomial`/`euler_polynomial`; **full classical orthogonal-polynomial suite** `legendre`, `hermite` (physicists'), `chebyshev_t`/`chebyshev_u`, `laguerre`/`generalized_laguerre(α)`, `gegenbauer(λ)`, `jacobi(α,β)` (three-term recurrences; parametric families cross-verified — `jacobi(0,0)=legendre`, `gegenbauer(1)=chebyshev_u`, …); `finite_product` (∏) | exact |
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
fold** `(√u)²=u` for any `u` (not just constants — so `x/√x=√x` certifies), `ln(exp u)=u`,
**fractional-coefficient exp arguments** (`exp(x/2)·exp(−x/2)=1`, needed for half-angle), and the
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
calculus/Jacobian, integer factorization. Longer tail: broader creative telescoping,
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
