# Computer Algebra System (CAS) — proof-carrying symbolic mathematics

Status: **implemented core, capability push paused at wave 24 (2026-07-22),
then a second capability wave plus a trust-registry gate landed 2026-09-05**
(kickoff 2026-07-20).
Last updated: 2026-09-05. This file's own capability-parity narrative (the
"Data-model frontier" note and the July "Active build wave" below) is
historical — see **Where the roadmap lives now**, just below, for where the
live picture is tracked.

Measured 2026-09-05 at `9914a1c0e` (`find crates/axeyum-cas/src -name '*.rs' | xargs cat | wc -l`;
`grep -rhE '^\s*pub fn ' crates/axeyum-cas/src --include=*.rs | wc -l`;
`grep -rh '#\[test\]' crates/axeyum-cas/src crates/axeyum-cas/tests | wc -l`):
98,595 source lines, 63 top-level modules plus 4 subdirectories, 975 `pub fn`
declarations, 1,296 `#[test]` functions. (This lane did not run `cargo`, so
these are static source counts, not a compiled/passing-test count; the most
recent compiled crate sweep is recorded in
[13-computer-algebra.md](../../math-department/13-computer-algebra.md)'s
progress log.) Per-function certificate classification — a materially
different question from "does it pass its own test" — is measured
separately below and in
[`artifacts/measurements/cas-trust-registry-2026-09-05.md`](../../../artifacts/measurements/cas-trust-registry-2026-09-05.md):
`python3 scripts/check-cas-trust-registry.py --report` finds 982 `pub fn`
(the two counts differ because the registry's brace-aware scanner excludes
`#[cfg(test)]`/`tests` module contents and non-`pub`-type `impl` blocks that
the flat `grep` above does not) — 78 certificate object, 59 checker, 845
uncertified.

## Where the roadmap lives now

This file's capability table below (the "Implemented" section, kickoff
2026-07-20) and its "Active build wave" paragraph are the **original July
roadmap**. That capability-parity push paused at **wave 24 on 2026-07-22**;
every CAS commit between 2026-08-26 and 2026-09-04 was trust-axis work, and
a second capability wave (ten new modules) plus a trust-registry gate landed
2026-09-05. Reading order for the live state:

- **The capability axis — what the CAS can compute today, judged by twelve
  practitioner chairs, with a ranked Next Ten** —
  [`docs/math-department/13-computer-algebra.md`](../../math-department/13-computer-algebra.md).
  This supersedes this file's "Active build wave" paragraph and the
  "next-wave" documents listed in *Documents in this section* below (each
  now carries a historical banner pointing back here).
- **The trust axis — the `cas-internal`/kernel-reconstructed residue and the
  bridges that reduce it** —
  [11-applied-and-computational.md](../../math-department/11-applied-and-computational.md)
  items 3 and 5, [ADR-0601](../09-decisions/adr-0601-three-producers-one-trust-anchor.md),
  [ADR-0622](../09-decisions/adr-0622-a-reconstruction-must-say-what-it-establishes.md),
  [ADR-1400](../09-decisions/adr-1400-a-certificate-must-record-every-distinction-its-acceptance-depends-on.md),
  [ADR-1617](../09-decisions/adr-1617-exact-real-cost-and-cas-internal-residue-measured.md),
  and [ADR-1622](../09-decisions/adr-1622-modular-exponentiation-is-what-makes-a-number-theory-certificate-reconstruct.md).
- **The arithmetic decision** — `i128` fast path, unbounded `Rational`/`BigPoly`
  fallback at the API boundary —
  [ADR-1670](../09-decisions/adr-1670-i128-fast-path-with-a-big-integer-overflow-fallback-for-the-cas-zero-test.md).
- **The trust-registry gate itself** — per-function certified/checker/
  uncertified classification, ratcheted —
  `scripts/check-cas-trust-registry.py`, measured in
  [`artifacts/measurements/cas-trust-registry-2026-09-05.md`](../../../artifacts/measurements/cas-trust-registry-2026-09-05.md).

## Implemented (`crates/axeyum-cas` — pure Rust, WASM-safe; capability-table snapshot as of 2026-07-23, historical — see above)

> **Data-model frontier now built** (special functions & fractional powers, none needing a `Pow`
> representation change): the **gamma family** `Γ`, arbitrary-order **polygamma** `ψ⁽ⁿ⁾` (via
> `UnaryFunc::PolyGamma(u32)` — the index carried in the variant, so the derivative tower
> `ψ⁽ⁿ⁾′=ψ⁽ⁿ⁺¹⁾` stays closed), symbolic **factorial** `Γ(n+1)`, **Beta** `B(a,b)`, **binomial**
> `C(n,k)`; arbitrary-order **Bessel** `Jₙ` and modified Bessel `Iₙ`; **Airy** `Ai/Bi` (closing tower `Ai″=x·Ai`); **Lambert W**
> (+ `solve` for `x·eˣ=c`); the **nth-root** head `x^{1/q}` with `∫x^{p/q}` and the `root_q(u)^q=u`
> zero-test fold; **Puiseux series** `sin√x=√x−(√x)³/6+…`; and **Euler–Cauchy ODEs** `a₂x²y″+a₁xy′+a₀y=0`
> (`xʳ=exp(r·ln x)`). Techniques: parameterize the `UnaryFunc` variant, `x^r=exp(r·ln x)`, closing towers.

A working proof-carrying CAS. Results are exact; those marked below as *certified*
carry a machine-checked proof (a decidable zero-test / differentiate-and-check),
which also acts as a correctness backstop (out-of-fragment cases decline, never
return a wrong answer). Runnable demos: `examples/certified_calculus.rs`,
`examples/cas_tour.rs`.

The certified integration table includes the direct rational-affine Bessel pairs
`∫J₁(u)dx=−J₀(u)/a` and `∫I₁(u)dx=I₀(u)/a`, plus the resource-bounded
weighted families `∫uⁿ⁺¹Jₙ(u)dx=uⁿ⁺¹Jₙ₊₁(u)/a` and
`∫uⁿ⁺¹Iₙ(u)dx=uⁿ⁺¹Iₙ₊₁(u)/a` for `u=ax+b` and `0≤n≤32`.
They certify through division-free polynomial recurrences valid for every public
integer order; mismatched weights and weighted discovery above order 32 decline.

**The "Certified" column below was corrected 2026-09-05** against
`scripts/check-cas-trust-registry.py` (measured in
[`artifacts/measurements/cas-trust-registry-2026-09-05.md`](../../../artifacts/measurements/cas-trust-registry-2026-09-05.md),
which found 25 of the table's 28 original rows disagreeing with the code).
Each cell below now names one of three gate-derived, falsifiable labels:
**certificate object** (the named function's return type names a
certificate-vocabulary type — a `pub struct`/`pub enum` ending in
`Certificate`/`Evidence`/`Report`/`Witness`, or exactly `ZeroTest`/
`CertifiedIntegral` — directly, or through `Option`/`Result`/`Vec`/a tuple);
**self-check** (the named function's own body re-derives its result and
gates the return value on an internal check — confirmed by reading the
function, not visible in its signature, and not itself a certificate);
**uncertified** (neither — an honest label about the signature, not a
correctness claim). Re-run: `python3 scripts/check-cas-trust-registry.py --report`.

| Area | Functions | Certified |
|---|---|---|
| Core | `differentiate`/`differentiate_n`, `substitute`, `expand`, `collect` (group by powers), `simplify`, `trigsimp`, `normalize`, `equal` (zero-test w/ witness, **Euler-sound for related trig atoms**, **log arithmetic** `2ln2−ln3=ln(4/3)` via prime-basis expansion, division-free **Bessel product recurrences** for every public integer order) | **uncertified** except `equal`: **certificate object** (`ZeroTest`). `differentiate`/`differentiate_n`/`substitute`/`expand`/`collect`/`simplify`/`trigsimp`/`normalize` return no vocabulary type and are not checker-named. |
| Rational | `cancel` (uni+multivariate), `apart`, `factor` (**full ℚ irreducible factorization** — peels rational roots then splits the degree-≥2 residual via Berlekamp–Zassenhaus, `x⁴+x²+1=(x²+x+1)(x²−x+1)`), `factor_univariate_over_q`/`factor_expr` (full ℤ/ℚ, Berlekamp–Zassenhaus); **bivariate** quadratics `x²−y²` and sum/difference of like powers `x³−y³=(x−y)(x²+xy+y²)`, `x⁵+y⁵`, `poly_gcd`, `poly_div`, `resultant`, `discriminant`, `cyclotomic_polynomial`, `degree`/`coeff`/`leading_coeff` | **uncertified** — none of `cancel`/`apart`/`factor`/`factor_univariate_over_q`/`factor_expr`/`poly_gcd`/`resultant`/`discriminant`/`cyclotomic_polynomial` are certified or checker. The crate's real certificate for this shape is a *different* function, `partial_fractions::partial_fractions` → `PartialFractionCertificate` (not named in this row). |
| Equations | `solve` (rational, quadratic w/ simplified surds, **complex**, degree-≥3 factoring over ℚ; **elementary transcendental** `eˣ−5⇒ln5`, `ln x−2⇒e²`, `√x−3⇒9`; **polynomial in eˣ** `e^{2x}−3e^x+2⇒{0,ln2}`); `solve_polynomial_system` (bivariate, Sylvester resultant); `real_roots` → `AlgebraicReal` (RootOf, any degree), `real_root_intervals`/`count_real_roots` (Sturm), `approximate_real_roots`; `solve_polynomial_inequality` | **uncertified** — none of `solve`/`real_roots`/`count_real_roots`/`real_root_intervals`/`solve_polynomial_system`/`solve_polynomial_inequality`/`approximate_real_roots` are certified or checker. The crate's actual Sturm/IVT certificate, `real_algebraic::polynomial_ivt` → `Option<IvtCertificate>`, is a *different* function not named in this row. |
| Summation | `sum_polynomial` (telescoping), `gosper_sum` (indefinite hypergeometric), `infinite_sum` (**convergent** Σ_{k}^∞ — geometric `Σr^k=1/(1−r)`, p-series `Σ1/k²=π²/6` via ζ) | **uncertified** — none of `sum_polynomial`/`gosper_sum`/`infinite_sum` are certified or checker. `gosper_sum` discards a certificate it already computed: it calls `gosper_sum_certified` (`Option<CertifiedGosperSum>`, carrying a `GosperEvidence` — itself in the vocabulary) and returns only the `antidifference` field; `CertifiedGosperSum` itself doesn't end in `Certificate`/`Evidence`/`Report`/`Witness`, so even `gosper_sum_certified` classifies uncertified. |
| Summation (definite) | `definite_sum` (Σ over bounds — polynomial via telescoping, **geometric/hypergeometric via Gosper**: `Σ 2^k = 2^{n+1}−1`, `Σ k·2^k`; geometric base recovered from any exponent spelling — `2^{−k}`, `(½)^k`, `Σ_{k≥0}2^{−k}=2`); `prove_wz_sum` (symbolically checked Wilf–Zeilberger certificates for binomial moments); `prove_fixed_shift_binomial_convolution` (direct checked-certificate family `ΣC(n,k)C(n,k+r)=C(2n,n−r)`, regressed for concrete `r=0..7`); `prove_squared_binomial_falling_moment` plus `prove_squared_binomial_moment` (directly checked falling-factorial WZ moments through order 255 and Stirling-composed raw moments through order 35) | **self-check**, not a certificate object — none of `definite_sum`/`prove_wz_sum`/`prove_fixed_shift_binomial_convolution`/`prove_squared_binomial_falling_moment`/`prove_squared_binomial_moment` return a vocabulary type, but `prove_wz_sum` symbolically verifies the WZ/telescoping identity before returning (confirmed in its own source comment: "the symbolic verification below is the real gate"), returning a plain `Option<CasExpr>`. |
| Complex analysis | `residue` (at a pole; **transcendental numerators** `Res cos x/x=1`, `sin x/x⁴=−1/6` via `f^{(n−1)}(a)/(n−1)!`), `laurent_series` (principal part), `modulus`, `roots_of_unity` | **uncertified** — none of `residue`/`laurent_series`/`modulus`/`roots_of_unity` are certified or checker per the gate. |
| Approximation | `approx`: Padé, Lagrange/Newton interpolation; `least_squares_polynomial`, `rationalize` (f64→ℚ), `nsimplify` (f64→closed form, 1.5708→π/2, **quadratic surds** (1+√5)/2, **ln(rational)** 0.693→ln2), `series_reversion` (compositional inverse) | **uncertified** — none of `approx`/`least_squares_polynomial`/`rationalize`/`nsimplify`/`series_reversion` are certified or checker (`approx.rs`: 0 certified, 0 checker). |
| Integration | `integrate` → `CertifiedIntegral`: polynomials, **complete univariate rational over ℚ** (Horowitz rational part + partial-fractions over ℚ-irreducible factors → logs, `atan` for irreducible quadratics **incl. surd** `∫1/(x²+x+1)`, and algebraic surd-logs for real-irrational-root quadratics `∫1/(x²−2)`; mixed factors `∫1/(x³+1)`), `∫k·f(ax+b)`, `∫p·eˣ`, `∫p·sin\|cos`, `∫p·eˣ·sin\|cos` (exp×trig), `∫sinᵐ·cosⁿ`, `∫sin(ax)·sin(bx)` product-to-sum (Fourier orthogonality), `∫f+g` (linearity); **by-parts**: `∫p·ln`, `∫p·(ln x)ᵐ`, `∫p·{atan,asin,acos,asinh,acosh}`; **substitution/power-rule**: `∫k·g′·gⁿ = k·gⁿ⁺¹/(n+1)` (`∫(ln x)²/x`, `∫eˣ(eˣ+1)²`, `∫sin·cos³`), `∫k·g′/g = k·ln g` (`∫cos/sin`), `∫k·f′/√f = 2k√f`, `u=eˣ` (`∫1/(eˣ+1)`), `u=sin/cos/tan` (`∫cos x/(1+sin²x)`, `∫1/cos²x=tan x`), **Weierstrass** `t=tan(x/2)` for all rational-trig `∫1/(a+b·cos x)`, `∫sec x`, `∫csc x`, half-integer power rule `∫√(ax+b)`/`∫xᵐ√x`, `u=x²` for `∫x·S(x²)·{eˣ²,sin,cos}`; special-function antiderivatives (erf/Si/Ci/Ei/li/Shi/Fresnel); `definite_integrate` (FTC; **full- and half-period rational-trig** `∫₀^{2π}`/`∫₋π^π`/`∫₀^π 1/(a+b·cos x)` via Weierstrass→improper, correct past the tan(x/2) discontinuity and exact for rational-trig Fourier coefficients; special-angle inverse-trig boundaries fold — `∫₀^{√3}1/(1+x²)=π/3`; **Beta integrals** `∫₀^1 x^p(1−x)^q=B(p+1,q+1)` incl. half-integer `∫₀^1 1/√(x(1−x))=π`), `fourier_series` (Euler coeffs — `f=x` → 2sin x−sin2x+…, `1/(2+cos x)` exact through the symmetric-period route), `numeric_integrate` (Simpson — `∫₀¹e^{−x²}≈0.7468` for non-elementary), `improper_integrate` (±∞ bounds; Gaussian `∫_{−∞}^∞ e^{−x²}=√π` via erf asymptote; **Gaussian moments** `∫_{−∞}^∞ x²ⁿe^{−x²}` via `(2m−1)!!` recurrence; **Gamma integrals** `∫₀^∞ x^p e^{−x}=Γ(p+1)` incl. half-integer `∫₀^∞ e^{−x}/√x=√π`; **integer-order Bessel-J family** `∫₀^∞cJₙ(ax)dx=c/|a|`, with an extra factor `(−1)ⁿ` when `a<0`, for nonzero rational `a`; **Dirichlet/Fresnel** `∫₀^∞ sin x/x=π/2` via Si/Fresnel asymptotes; **Fourier via residues** `∫_{−∞}^∞ cos x/(x²+1)=π/e`, `∫ x·sin x/(x²+1)=π/e`; **Frullani** `∫₀^∞ (cos x−cos bx)/x=ln b`, `∫₀^∞ (e^{−ax}−e^{−bx})/x=ln(b/a)` (Ci/Ei/Chi combine at 0, sound past the log-singularity); **combining-log** boundaries `∫₀^∞1/(1+x³)=2π/(3√3)` where individual log terms diverge (surd-coefficient logs too → `∫_{−∞}^∞1/(x⁴+1)=π/√2`); `∫₀^∞1/(1+x²)=π/2`); **even quartic denominators** `∫1/(x⁴+px²+q)` via the real (surd) quadratic factorization `∫1/(x⁴+1)` (beyond ℚ partial fractions) | `integrate`: **certificate object** (`Option<CertifiedIntegral>`) — the one row where the original claim and the gate agree. `definite_integrate`: **uncertified per the gate**, though it does carry a real `ZeroTest` internally — it returns `Option<DefiniteIntegral>` and `DefiniteIntegral` has a `certificate: ZeroTest` field, but the gate only peels `Option`/`Result`/`Vec`/tuple wrappers, not struct fields, so `DefiniteIntegral` itself is outside the naming-derived vocabulary. `fourier_series`: **self-check** — calls `definite_integrate` per coefficient and requires `.is_certified()`, returning `Option<CasExpr>`. `numeric_integrate`/`improper_integrate`: **uncertified**, no internal check found. |
| Analysis | `limit` (rational; **exact-rational continuity through existing globally real-continuous heads** `H(f(x))→H(q)` for `H∈{sin,cos,atan,erf,Si,Shi,FresnelS,FresnelC,asinh,Ai,Ai′,Bi,Bi′}` whenever the complete inner limit is the exact rational `q`; **exact-rational absolute-value continuity** `|f(x)|→|q|`; asymptotic unary-head arguments require **exact algebraic leading order plus strict leading-coefficient sign**, never floating samples; transcendental `0/0` via series — `sin x/x=1`, `tan x/x=1`, **integer-order Bessel zero limits** `Jₙ(x)/xⁿ=Iₙ(x)/xⁿ→1/(2ⁿn!)` (orders 0 through 8 tested); **integer-order Bessel finite-inner continuity** `Hₙ(r(x))→Hₙ(q)` for `H∈{J,I}` and exact rational inner limit `q`; **unbounded rational-function integer-order Bessel-J products at both infinities** `c·w(x)·∏Jₙᵢ(rᵢ(x))^mᵢ→0` for positive integer multiplicities `mᵢ` (including rational weights inside nested powered products, accounted structurally without expansion), rational-coefficient `rᵢ,w`, `2·max(0,deg num(w)−deg den(w))<Σᵢmᵢ(deg num(rᵢ)−deg den(rᵢ))`, every argument growth positive, and `x`-free `c`; **exponential dominance** at ±∞ — `x²/eˣ=0`; **log-vs-power** at 0 — `x·ln x=0`, and at +∞ — `ln x/x=0`, `x^{1/x}=1`; **algebraic/conjugate** at +∞ — `√(x²+x)−x=½`, `√(x²+x)−√(x²−x)=1` via leading-term/conjugate analysis; **squeeze** — `sin x/x=0`; **1^∞** — `(1+1/x)^x=e` via reciprocal substitution; **combining logs** at ±∞ — `⅓ln(x+1)−⅙ln(x²−x+1)→0`; **L'Hôpital** for 0/0 beyond the rational-series fragment — `(2ˣ−1)/x→ln2`; **combining Ci/Ei/Chi** at 0 — Frullani `Ci(x)−Ci(2x)→−ln2`), `series`/`series_at`/`laurent_series` (incl. `tan`, `asin`, `asinh`, and **integer-order `Jₙ`/`Iₙ` at vanishing arguments**; **Taylor about any center** with transcendental coefficients — `exp` about 1 → `e·[1+(x−1)+…]` via the derivative definition), `sum_polynomial`, `evalf` (f64), finite calculus | **uncertified** — none of `limit`/`series`/`series_at`/`laurent_series`/`sum_polynomial`/`evalf` are certified or checker per the gate. |
| Transforms | `laplace_transform` (poly×{1,sin,cos,**arbitrary-order Bessel Jₙ / modified Bessel Iₙ**} with the **s-shift rule** `L{e^{at}f}=F(s−a)` and transform differentiation; both exact order families are derivative-recurrence-replayed, and `Iₙ` records its convergence half-plane) + `inverse_laplace` (simple/repeated real poles and **irreducible quadratics** → damped sinusoids; repeated rational-frequency quadratic powers through multiplicity 7, including shifted/mixed factors; rational-scale/shift square-root quadratics → `Jₙ`/`Iₙ` for `0≤n≤32`; **finite additive radical-bearing combinations** when every summand independently inverts), `z_transform` (bounded `P(n)aⁿ`, rational `P`, `deg P≤32`, positive rational `a`) + `inverse_z_transform` (positive rational poles, multiplicity ≤32); inverse transforms are exact forward-round-trip-certified | `laplace_transform`/`z_transform`: **uncertified**, no internal check found (forward direction). `inverse_laplace`/`inverse_z_transform`: **self-check** — each reapplies the forward transform to its own candidate result and requires `equal(...) == ZeroTest::Certified{equal:true}` before returning, declining (`None`) otherwise; confirmed by reading both bodies (`lib.rs:12566`, `lib.rs:13436`). Neither exposes a certificate object. |
| ODEs / recurrences | `dsolve_homogeneous` (constant-coeff, **any degree** with one irreducible-quadratic factor — real/repeated/**surd** roots: `y‴−y=0`→`e^x`+`e^{−x/2}`(cos,sin), `y″−2y=0`→`e^{±√2 x}`), `dsolve_inhomogeneous` (polynomial forcing; **generic first-order non-polynomial routing** through the integrating-factor solver; **variation of parameters** for second-order exp/trig forcing — `y″−y=eˣ` incl. resonance, `y″+y=sin x`), `dsolve_first_order_linear` (integrating factor, incl. **variable** `p=k/x`→`μ=x^k` via `exp(ln)` folding, and **resonant** forcing `y′−y=eˣ`), `dsolve_separable`, `dsolve_exact`, `dsolve_bernoulli`, `apply_initial_conditions` (rational evaluated basis matrices with exact radical/symbolic data — `y(0)=A,y′(0)=B ⇒ A cos x+B sin x`; expression-valued path bounded to 16 constants; every condition replay-certified), `solve_recurrence` (rational **and** quadratic-irrational roots — incl. **Fibonacci**/Binet); `wronskian` | **self-check** for all of `dsolve_homogeneous`/`dsolve_inhomogeneous`/`dsolve_first_order_linear`/`dsolve_separable`/`dsolve_exact`/`dsolve_bernoulli`/`apply_initial_conditions`/`solve_recurrence` — each re-derives its candidate result (substitutes back into the ODE, re-checks every initial condition, or re-tests the recurrence residual) and requires `ZeroTest::Certified{equal:true}` before returning, declining (`None`) otherwise; confirmed by reading `dsolve_exact` (`lib.rs:5018`), `apply_initial_conditions` (`lib.rs:4855`) and `solve_recurrence` (`lib.rs:5216`). None return a certificate object. `wronskian`: **uncertified** — a plain determinant, no internal check found. |
| Trig | `evaluate_trig` (exact values at π/12 multiples, **inverse-trig** atan(1)=π/4, asin(√3/2)=π/3), `rewrite_exp` (Euler) → **all polynomial trig identities decidable**, `expand_trig` (angle-addition/multiple-angle → trig form); trig-equation solving via `solve` (`2sin x−1⇒π/6,5π/6`, principal in [0,2π); **surd RHS** `2cos x−√3⇒π/6,11π/6`; **polynomial-in-sin/cos** `sin²x=¼⇒{π/6,5π/6,7π/6,11π/6}`, `2sin²x−3sin x+1=0`; **multiple angle** `sin 2x=0⇒{0,π/2,π,3π/2}`, `sin 3x=0`; surd `tan x=√3`; **linear combination** `cos x+sin x=0⇒{3π/4,7π/4}`) | **uncertified** — none of `evaluate_trig`/`rewrite_exp`/`expand_trig`/`solve` are certified or checker per the gate. |
| Complex | `imaginary_unit` (`I²=−1`), `conjugate`, `real_part`, `imaginary_part`, `modulus`, `argument` (phase — arg(1+i)=π/4), `roots_of_unity` | **uncertified** — none of `imaginary_unit`/`conjugate`/`real_part`/`imaginary_part`/`modulus`/`argument`/`roots_of_unity` are certified or checker. |
| Linear algebra | `Matrix`: +/−/×, determinant (+ Bareiss), RREF, solve, inverse, `adjugate`/`cofactor`, `pow`, `hadamard`/`kronecker`, `null_space`, `lu`, `rank`, `trace`, char-poly, `eigenvalues`/`eigenvectors`, `minimal_polynomial`, `diagonalize` (P·D·P⁻¹), `jordan_form` (P·J·P⁻¹, **defective** via generalized eigenvectors), `matrix_exp` (e^{At}, rational spectrum incl. defective), `linear_ode_system` (x′=Ax), Hermite/Smith, `gram_schmidt`, **`qr_decomposition`** (A=QR, surd-certified), **`cholesky_decomposition`** (A=L·Lᵀ, SPD, surd-certified); `companion_matrix`, `solve_linear_system`, `least_squares_polynomial` | **uncertified** — none of the named `Matrix` methods are certified or checker (`matrix.rs`: 0 certified, 0 checker, 27 uncertified per the gate — note `matrix.rs` is itself a private (`mod`, not `pub mod`) module; the gate does not walk mod-visibility, so it still counts these). |
| Logic / sets | `boolean::BoolExpr` (truth tables, tautology/SAT, DNF/CNF, Quine–McCluskey); `sets::RealSet` (interval unions, set algebra, measure); `interval_arith::Interval` (rigorous enclosures) | **uncertified** — `boolean.rs`/`sets.rs`/`interval_arith.rs` each have 0 certified, 0 checker functions per the gate; an exhaustive truth table or a rigorous interval bound is exact by construction but is not a distinct, independently replayable certificate object. |
| Special functions | `special`: `gamma`/`beta`, `zeta`/`dirichlet_eta`/`dirichlet_lambda`, `polygamma_at_one`, `gamma` at negative half-integers; **integral-defined heads** `erf`, `Si`/`Ci`/`Ei`, `li`, `Shi`/`Chi`, Fresnel `S`/`C`, arbitrary-order Bessel `Jₙ` and modified Bessel `Iₙ`, `asin`/`acos`/`asinh`/`acosh` — with **certified defining integrals** (∫e^{−x²}=(√π/2)erf incl. completing-the-square, ∫sin x/x=Si, ∫eˣ/x=Ei, ∫1/ln x=li, ∫sinh x/x=Shi, ∫sin(πx²/2)=S, ∫1/√(1−x²)=asin, ∫1/√(x²+1)=asinh) + numeric `evalf`; `hyperbolic`: sinh/cosh/…/atanh (via exp tower); **piecewise-constant heads** `abs`/`sign`/`floor`/`ceiling` (constant folds, derivative 0, `sign` resolves ±1/0 under sign assumptions) | **uncertified** — `special.rs`/`hyperbolic.rs`: 0 certified, 0 checker per the gate. |
| Finite fields | `gfp`: 𝔽ₚ[x] ring ops, gcd, `is_irreducible`, `factor_berlekamp`, `roots` | **uncertified** — `gfp.rs`: 0 certified, 0 checker; no internal re-multiply check found in `factor_berlekamp` itself. |
| Groups | `Permutation`: compose, inverse, cycles, order, sign (symmetric groups) | **uncertified** — `permutation.rs`: 0 certified, 0 checker. The crate's real certified group machinery is a *different* module, the new `permgroup::PermutationGroup` (Schreier–Sims) — see the new row below. |
| Boolean algebra | `boolean::BoolExpr`: truth tables, tautology/SAT, DNF/CNF, `equivalent`, Quine–McCluskey minimization | **uncertified** — same module and count as the Logic / sets row above (`boolean.rs`: 0 certified, 0 checker). |
| Geometry | `geometry`: `Point`/`Line`/`Circle` — distance, midpoint, slope, collinear, triangle area, line ops, circumcircle | **uncertified** — `geometry.rs`: 0 certified, 0 checker. The crate's certified geometry route is a *different* module, `geometry_certify.rs` (Nullstellensatz cofactor certifier: 1 certified + 5 checker), plus the new `geometry_beyond.rs` — see the new row below. |
| Vector calculus | `gradient`, `jacobian`, `divergence`, `curl`, `hessian`, `laplacian` (certified partials); `dot`, `cross`, `norm` | **uncertified** — none of `gradient`/`jacobian`/`divergence`/`curl`/`hessian`/`laplacian`/`dot`/`cross`/`norm` are certified or checker (all live in `lib.rs`, which has 3 certified functions total — `equal`, `integrate`, `prove_derivative` — none of these). |
| Special polys | `orthopoly`: `chebyshev_t`/`chebyshev_u`/`legendre`/`hermite`/`laguerre` (three-term recurrences) | **uncertified** — `orthopoly.rs`: 0 certified, 0 checker. |
| Combinatorics | `combinatorics`: `bernoulli`, `euler_number`, `stirling_first`/`second`, `bell`, `partition_count`, `catalan`, `fibonacci`/`lucas`, `harmonic`/`generalized_harmonic`, `derangements`, `double_factorial`, `multinomial`, `pell`/`jacobsthal`/`tribonacci`/`motzkin`, `eulerian`/`narayana`/`lah` (triangles); `bernoulli_polynomial`/`euler_polynomial`; **full classical orthogonal-polynomial suite** `legendre`, `hermite` (physicists'), `chebyshev_t`/`chebyshev_u`, `laguerre`/`generalized_laguerre(α)`, `gegenbauer(λ)`, `jacobi(α,β)` (three-term recurrences; parametric families cross-verified — `jacobi(0,0)=legendre`, `gegenbauer(1)=chebyshev_u`, …); `finite_product` (∏) | **uncertified** — `combinatorics.rs`: 0 certified, 0 checker. |
| Logs / abs | `expand_log`, `logcombine` (product/quotient/power rules), `Abs` head (`|·|`, `√(x²)→|x|`) | **uncertified** — none of `expand_log`/`logcombine`/`Abs` are certified or checker. |
| Statistics | `stats`: mean/median/mode/variance/covariance; `standard_deviation`, `correlation` (surd-simplified) | **uncertified** — `stats.rs`: 0 certified, 0 checker. |
| Radicals | `simplify_radicals` (`√12→2√3`, rationalize denominators) | **uncertified** — `simplify_radicals` is not certified or checker. |
| Number theory | `ntheory` (gcd, mod-pow/inverse, `is_prime`, `factorize`, φ, CRT, binomial); `ntheory_advanced` (nPr, Legendre/Jacobi, quadratic residues, `sqrt_mod` (Tonelli–Shanks), `kronecker_symbol`, `solve_linear_congruence`, order, primitive root, discrete log, continued fractions, Pell); `ntheory_more` (Möbius, Mertens, σ_k, perfect/squarefree, radical, `perfect_power`, `integer_nth_root`, `aliquot_sum`/`are_amicable`, `primitive_pythagorean_triples`, Carmichael λ, primorial, next/prev prime, π(n), nth prime, Carmichael numbers) | **uncertified** — none of the named `ntheory`/`ntheory_advanced`/`ntheory_more` functions are certified or checker (0/0/15, 0/0/14, 0/0/21 respectively). The crate's real certified number-theory module is a *different* one, `ntheory_certify.rs` (4 certified + 4 checker: `certify_prime`/`certify_composite`/`certify_factorization`/`certify_crt`), not named in this row. |
| Multivariate | `mvpoly::MvPoly`: ring ops, division, **GCD** (primitive PRS), square-free | **uncertified** — the row's own `—` already said so; the gate agrees (`mvpoly.rs`: 0 certified, 0 checker). |

**The ten rows below are new** — the 2026-09-05 second capability wave (eight
new modules from
[13-computer-algebra.md](../../math-department/13-computer-algebra.md)'s
Next Ten) plus two capabilities that existed before but never had a row here
(Gröbner bases, GF(2)/SOS), added in the same style.

| Area | Functions | Certified |
|---|---|---|
| Formal power series & generating functions | `fps::FormalPowerSeries::{inverse, reversion, from_rational_function, from_recurrence}`, `guess_linear_recurrence`, `rational_generating_function` | **certificate object** for all 6 named: `inverse`/`reversion`/`from_rational_function` → `(FormalPowerSeries, TruncationIdentity)`; `from_recurrence` → `(FormalPowerSeries, RecurrenceCertificate)`; `guess_linear_recurrence` → `RecurrenceCertificate`; `rational_generating_function` → `RationalGeneratingFunction`; each certificate type has its own `verify`. 22 of the module's other 32 pub fns (coefficient extraction, composition, arithmetic) are uncertified. |
| Validated numerics (enclosures) | `enclosure::{enclose, enclose_with_reason, enclose_root, enclose_root_with_reason, enclose_constant}` | **certificate object** for all 5: return `Enclosure`/`Result<Enclosure, DeclineReason>`, each checked by `Enclosure::verify`/`verify_root`. 20 of the module's other 27 pub fns are uncertified; `gamma`, Bessel, `erf` and non-integer powers still decline. |
| Algebraic number fields | `numberfield::Element::{inverse, minimal_polynomial, norm_trace}`, `GaussianInt::factor`, `two_squares`, `QuadraticField::{fundamental_unit, pell_unit}` | **certificate object** for all 7 named (`InverseCertificate`/`ElementMinPolyCertificate`/`NormTraceCertificate`/`GaussianFactorizationCertificate`/`TwoSquaresCertificate`/`FundamentalUnitCertificate`), each with its own `verify`. 51 of the module's other 64 pub fns (ℚ(α) ring arithmetic, ℤ[i] arithmetic beyond factoring, unit-search internals) are uncertified; ideal factorization, class numbers and Galois groups remain open. |
| Finite group computation | `permgroup::PermutationGroup::{contains, cosets, orbit_stabilizer, is_abelian, derived_subgroup, center, cayley_table, order_certificate}` | **certificate object** for all 8 named (`MembershipCertificate`/`CosetCertificate`/`OrbitStabilizerCertificate`/`AbelianCertificate`/`DerivedSubgroupCertificate`/`CenterCertificate`/`CayleyTableCertificate`/`OrderCertificate`), each with its own `verify`. 6 of the module's other 22 pub fns are uncertified; Sylow, presentations and isomorphism testing remain open. |
| Symbolic probability | `probability::{Discrete, Continuous}::{total_mass, mean, variance, mgf}`, `convolve_poisson`, `chebyshev_bound`, `markov_bound` | **certificate object** for all 11 named — each returns `Certificate`/`Option<Certificate>`, each with its own `verify_*`. Poisson and Geometric moments, and the general `Normal(σ)` mgf, decline (`Uncertified(reason)`) on measured machinery gaps recorded in [13-computer-algebra.md](../../math-department/13-computer-algebra.md); 3 of the module's other 22 pub fns are uncertified. |
| Real quantifier elimination | `qe::{decide_exists, decide_forall}` | **certificate object**: `Decision`/`ForallDecision`, each with a `verify`; the underlying witness types `SampleCertificate`/`RefutationCertificate` are also each `verify`-checked. 9 of the module's other 15 pub fns are uncertified; root isolation is still `i128` (`x²−10³⁰` returns `Unknown`); multivariate and CAD remain open. |
| Simplicial homology | `homology::homology` | **certificate object**: `Option<HomologyCertificate>`, whose own `verify` re-derives a `HomologyReport` from the boundary matrices. 6 of the module's other 8 pub fns are uncertified. |
| Geometry beyond the plane | `geometry_beyond::{Conic::through_five_points, certify_preserves_distance}` | **certificate object** for these 2 (`ConicFiveCertificate`/`DistancePreservingCertificate`, each `verify`). 90 of the module's other 94 pub fns (3D points/planes/spheres, homogeneous join/meet, isometries beyond distance-preservation) are uncertified; Pascal and Desargues decline under the existing cofactor certifier. |
| Gröbner bases | `groebner::{buchberger, reduce, is_groebner_basis}`, `groebner_cert::{unit_ideal_cofactors, reduce_with_cofactors}` | **uncertified** per the gate — `groebner.rs`/`groebner_cert.rs`: 0 certified, 0 checker between them. `unit_ideal_cofactors` returns `CofactorOutcome`, the same cofactor-evidence machinery behind the `cas-certificate` ledger's `groebner-cofactor-unit-ideal-refutation` route (`cas-internal`, per `check-cas-internal-residue.py --report`), but `CofactorOutcome` doesn't end in `Certificate`/`Evidence`/`Report`/`Witness`, so the naming-derived vocabulary misses it. |
| GF(2) polynomials, tensors & SOS/Lyapunov/barrier certificates | `gf2::{certify_irreducible, half_degree_parity_split_report, search_shaped_compositions}`, `gf2_extension::binary_extension_*_trace*` (8 fns), `sos::check`, `sos::check::{check_artifact, check_lyapunov, check_barrier, check_psd_not_sos}` | **certificate object** for 16 named functions (`IrreducibilityCertificate`/`HalfDegreeParitySplitReport`/`ShapedCompositionSearchReport`, five `BinaryExtension*Report` types, `CheckReport`); `gf2::certify_irreducible` is checked by `gf2::check_irreducible_certificate` (and, independently, `gf2_independent::check_irreducible_certificate_independent`). The remaining GF(2) shard/tensor machinery (`gf2_shard.rs`, `gf2_tensor.rs`) and 12 of `sos.rs`'s other functions are checker-only or uncertified. |

Heads: `exp, sin, cos, tan, ln, atan, sqrt, abs`, the inverse pair
`asin/acos/asinh/acosh`, and the special functions `erf, Si, Ci, Ei, li, Shi, Chi,
FresnelS, FresnelC, BesselJ(u32), BesselI(u32)` (extensible `Unary` — each adds a `name`,
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
| [gap-analysis.md](gap-analysis.md) | Substrate vs. target; 16 build units (G0–G18, all shipped) | historical (2026-09-05) — see [13-computer-algebra.md](../../math-department/13-computer-algebra.md) |
| [build-plan.md](build-plan.md) | Phased (C0–C7), decidable-first, TDD sequence with exit gates | historical (2026-09-05) — see [13-computer-algebra.md](../../math-department/13-computer-algebra.md) |
| [rational-integration.md](rational-integration.md) | `∫ P/Q dx` algorithm (Horowitz) + certification + log-part roadmap | done |
| [next-wave-roadmap.md](next-wave-roadmap.md) | Post-G18 SymPy/Mathematica capability survey; prioritized top-15 | historical (2026-09-05) — see [13-computer-algebra.md](../../math-department/13-computer-algebra.md) |
| [curriculum-gaps.md](curriculum-gaps.md) | Union of the 7 per-branch curriculum reviews; Tier A–D ranked gaps | historical (2026-09-05) — see [13-computer-algebra.md](../../math-department/13-computer-algebra.md) |

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
