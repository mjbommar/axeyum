# Rational-function integration — design & certification

Status: shipped (Slice 1) + roadmap (2026-07-20)
Last updated: 2026-07-20

How `∫ P(x)/Q(x) dx` is computed and **certified** in `axeyum-cas`, and the
sequence for finishing the logarithmic part. This is the concrete realization of
Phase C6 (the flagship) in [build-plan.md](build-plan.md) for the univariate
rational case. Grounded in a research pass over Bronstein Ch. 2 and SymPy's
`ratint` (references below).

## The pipeline

For `P, Q ∈ ℚ[x]` (Laplace's theorem: the integral is a rational function plus a
finite sum of constant multiples of logs):

1. **Proper/improper split.** `P = S·Q + P₁`, `deg P₁ < deg Q`. `∫S dx` is the
   ordinary polynomial antiderivative. (New primitive `ratint::divrem`, built from
   `poly::rat_rem` + exact division.)
2. Reduce `gcd(P₁, Q) = 1` (`poly::rat_gcd` + `rat_exact_div`).
3. **Rational part (Horowitz–Ostrogradsky).** Split `∫ P₁/Q = B/D₂ + ∫ C/D₁`
   with `D₂ = gcd(Q, Q')`, `D₁ = Q/D₂`, `deg B < deg D₂`, `deg C < deg D₁`. The
   identity `A = B'·D₁ − B·H + C·D₂` with `H = Q'/D₂ − D₁'` is **linear** in the
   unknown coefficients of `B, C`, solved by one exact-rational Gauss–Jordan
   system (`ratint::solve_linear`, `ratint::horowitz`).
4. If `C = 0` the integral is **purely rational** → return `S_int + B/D₂`. If
   `C ≠ 0` a genuine **logarithmic part** `∫ C/D₁` remains (Slice 2 below).

## Why Horowitz, not Hermite (deviation from the research note)

The research note recommended Hermite reduction (needs a squarefree-factorization
list + extended-Euclid cofactors). We use **Horowitz–Ostrogradsky** instead — the
same method SymPy's `ratint_ratpart` uses — because it needs only `gcd`,
`derivative`, exact division, and **one linear solve** (which C3 linear algebra
needs anyway), and no squarefree-factorization list or extended-Euclid. Correct on
the same class. All integration internals live in `crates/axeyum-cas/src/ratint.rs`
(operating on `poly.rs`'s public functions), so the shared `axeyum-ir` core is
untouched — preserving parallel development.

## Certification (the load-bearing property)

Every returned antiderivative `F` is certified by **differentiating it and
zero-testing against the integrand**: `equal(F.differentiate(var), P/Q)` must be
`ZeroTest::Certified { equal: true }`. This is the existing rational zero-test
(cross-multiplication over the canonical polynomial form) — *no new certifier
machinery*. Crucially, this makes the certificate a **correctness backstop**: even
a buggy finder can only ever fail to certify (→ honest `None`), never emit a wrong
"certified" answer. The `integrate` entry point returns `Some(CertifiedIntegral)`
only when the certificate confirms.

Verified (Slice 1): `∫1/x² = −1/x`; improper `∫(x²+1)/x² = x − 1/x`; a
self-certifying roundtrip (differentiate a rational `R`, integrate back, confirm
`d/dx` returns the integrand) over `{1/x, 1/(x²+1), x/(x+1)}`; and honest decline
on `∫1/x`, `∫2x/(x²+1)` (which need logs).

## Roadmap — the logarithmic part

Per the research note (mapped onto in-tree primitives):

- **Slice 2a-i (linear log denominator) — SHIPPED.** `CasExpr::Ln` +
  `d/dx ln v = v'/v`; a linear log denominator `a·x+b` → `(C/a)·ln(a·x+b)`.
  Certified via the **opaque-atom** zero-test: `normalize_rational` maps each
  `ln(v)` to a fresh variable keyed by `v`'s rendering, so the product rule's
  spurious `c'·ln(v)` term drops and the derivative reduces to a rational identity
  (sound; genuine log identities conservatively decline, never a false cert).
  `∫1/x=ln(x)`, `∫1/(2x+1)=½ln(2x+1)` certified.
- **Slice 2a-ii (rational-root log part).** `∫ P̄/Q̄ = Σ cᵢ ln(vᵢ)` where the `cᵢ`
  are roots of the Rothstein–Trager resultant `R(t) = Res_x(P̄ − t·Q̄', Q̄)` and
  `vᵢ = gcd(P̄ − cᵢQ̄', Q̄)`. The resultant needs **no new code** — the existing
  `poly::sylvester_matrix`/`sylvester_determinant` accept polynomial entries, so
  `t` is the surviving variable. Add `CasExpr::Ln` + one differentiation rule
  (`d/dx ln v = v'/v`); when `R`'s roots are **rational**, `cᵢ, vᵢ ∈ ℚ[x]` and
  the whole thing certifies through the *existing* zero-test (the `Ln`
  differentiates away into a rational identity). New: rational root finder over
  `R(t)`.
- **Slice 2b (real-irrational roots).** Needs `RealAlgebraic::inv`/`div`
  (algebraic-number field inversion, itself an extended-Euclid) + a
  coefficient-generic polynomial GCD over `ℚ(cᵢ)` + an algebraic-coefficient
  zero-test path. Roots isolated via existing `sturm_chain`/`count_roots_in`.
- **Slice 2c (complex-conjugate pairs → `atan`).** Detect real quadratic factors
  of `R` with negative discriminant; emit `atan`-family closed forms (SymPy's
  `quadratic=True`), certified via `CasExpr::Atan` + `d/dx atan u = u'/(1+u²)`.
- **Slice 2d (optional, root-isolation-free).** Certify the whole log part as a
  single rational identity via the subresultant-PRS `v(t,x)` + Newton's-identities
  trace — stays entirely in ℚ, no algebraic numbers. Later hardening.

## References
- Bronstein, *Symbolic Integration I*, Ch. 2 (Hermite, Rothstein–Trager,
  Lazard–Rioboo–Trager) — https://link.springer.com/book/10.1007/b138171 ·
  ISSAC'98 tutorial https://www-sop.inria.fr/cafe/Manuel.Bronstein/publications/issac98.pdf
- SymPy `sympy/integrals/rationaltools.py` (`ratint`, `ratint_ratpart`,
  `ratint_logpart`) — https://github.com/sympy/sympy/blob/master/sympy/integrals/rationaltools.py
- Horowitz 1971 (rational-part linear system) —
  https://groups.csail.mit.edu/mac/users/gjs/6.945/readings/simplification/horowitz-ratint.pdf
- SciML SymbolicIntegration.jl (Bronstein Ch. 2 impl) —
  https://docs.sciml.ai/SymbolicIntegration/dev/methods/risch_rational_functions/
- Laplace's theorem — https://en.wikipedia.org/wiki/Risch_algorithm ;
  Newton's identities — https://en.wikipedia.org/wiki/Newton%27s_identities
