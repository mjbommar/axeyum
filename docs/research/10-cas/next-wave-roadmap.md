# Next-wave CAS roadmap (beyond G0–G18)

Status: roadmap (2026-07-20)
Last updated: 2026-07-20

The gap-analysis G0–G18 and phases C0–C6 are essentially implemented (see
[README](README.md#implemented), 130+ tests). This note is the **next wave**,
synthesized from a sourced SymPy/Mathematica capability survey and the per-branch
[curriculum](../../curriculum/) coverage review. It is prioritized by
**value × proof-carrying-fit × buildability given existing machinery**.

## The organizing principle (why these fit)

Every existing capability shares one design: the *finder* may be heuristic, but
the *certificate* is cheap, independent, and sound (differentiate-and-check;
zero-test; plug-back). So the prioritization lens is: **does the new capability
have a cheap independent certificate?**

| Certificate | Applies to |
|---|---|
| Multiply factors back, `equal` | factorization (ℚ/ℤ/𝔽ₚ/multivariate), Smith/Hermite (`U·A·V=D`, `det=±1`) |
| Plug back into equation/operator | eigenvectors (`Av=λv`), ODEs (all orders), Diophantine, discrete log |
| Differentiate & compare | Risch/Lazard–Rioboo–Trager integration, special-function rules, Laurent/Puiseux |
| Telescoping identity | Gosper, Zeilberger |
| Direct arithmetic re-check | Legendre/Jacobi, continued fractions/Pell, char/min poly (Cayley–Hamilton) |
| Sturm sign-count / interval witness | real root isolation, RootOf |

Weak-certificate items (flagged, not committed): full CAD / quantifier
elimination, Meijer-G table integration.

## Prioritized top 15 (value × fit × buildability)

1. **Gosper** — indefinite hypergeometric summation. Excellent fit (telescoping
   cert, extends `sum_polynomial`); high buildability; delegable.
2. **Eigenvectors + characteristic/minimal polynomial** (Faddeev–LeVerrier /
   Berkowitz). `Av=λv` cert. Builds on `Matrix`/`solve`. *(eigenvalues, char-poly
   already shipped — remaining: eigenvectors via nullspace, minimal polynomial.)*
3. **Nullspace, rank, exact Bareiss LU.** Thin RREF extension. *(rank shipped.)*
4. **First-order ODEs** — separable, exact, integrating-factor, Bernoulli,
   homogeneous. Substitution cert (mirrors `dsolve_homogeneous`); pure composition
   of `differentiate`/`integrate`/`substitute`. Delegable.
5. **Inhomogeneous linear ODEs** — undetermined coefficients + variation of
   parameters (uses `Matrix` solve / Wronskian). Builds on `dsolve_homogeneous`.
6. **Number-theory bundle** — discrete log (BSGS/Pohlig–Hellman), Legendre/Jacobi
   symbols & quadratic residues, continued fractions / Pell, primitive roots,
   linear Diophantine. Nearly free given `mod_pow`/`factorize`/`CRT`/`gcd`.
   Delegable — ideal low-risk first module.
7. **Factorization over ℤ/ℚ** — Berlekamp/Cantor–Zassenhaus over 𝔽ₚ + Hensel lift
   + recombination. Multiply-and-`equal` cert. Needs an 𝔽ₚ polynomial layer.
8. **Real root isolation (Sturm/Descartes) + RootOf** — algebraic numbers as
   (defining poly + isolating interval). Sturm sign-count *is* the cert. Unblocks
   many downstream items; build the RootOf interface first.
9. **Smith / Hermite normal form** — `U·A·V=D` unimodularity cert. Unblocks
   Diophantine systems, module theory.
10. **Laurent series + residues.** Thin generalization of `series` (multiply by
    `xᵐ`), same truncation cert.
11. **Special functions with known-derivative rules** — Γ, B, erf, Bessel,
    polylog (extend the opaque-atom pattern with *known* derivative identities).
    One function/family per agent.
12. **trigsimp beyond Pythagorean** — via Euler's formula (rewrite to
    exp/`I²=−1`, reduce in the existing canonical form, rewrite back). Touches the
    `simplify`/`equal` boundary — review, don't blind-delegate.
13. **Minimal assumptions system** — three-valued positive/real/integer logic
    gating `sqrt(x²)=|x|`, `logcombine`/`expand_log`/`radsimp`/`powsimp`.
    Cross-cutting; design centrally, then delegate individual gated rules.
14. **Zeilberger / creative telescoping** — definite hypergeometric sums; calls
    Gosper internally (sequence after #1).
15. **Lazard–Rioboo–Trager** — algebraic-number logarithmic integration
    (generalizes the shipped Rothstein–Trager rational-root case). Needs #8
    (RootOf). First real step toward full Risch.

**Beyond 15 / sequenced:** Risch–Norman `heurisch` (cheap win, pairs with #15);
full Risch (highest ceiling, after #15); multivariate factorization + van
Hoeij/LLL (after #7); Jordan form, ODE systems (after #2, #8); power-series &
Laplace ODE methods (Laplace reuses `apart`!); Puiseux & asymptotic/Gruntz
(extends #10 and generalizes `limit`); a sound **term-rewriting/e-graph engine**
(cross-cutting home for #12/#13 rules); code generation (free round-trip cert).

**Deprioritized:** CAD/quantifier elimination (weakest cert — research spike),
Meijer-G, Abel summation, tensor/noncommutative/p-adic algebra.

## Build order this session (in progress)

Starting with the cheapest high-value certifiable items: the number-theory bundle
(#6), eigenvectors + minimal polynomial (#2), Laurent series (#10), first-order
ODEs (#4), Gosper (#1) — each certified and TDD'd, delegating self-contained
modules (factorization, special functions) to sub-agents. Curriculum-branch
reviews (00-foundations … reconstruction-targets) are folded into
[curriculum-coverage.md](curriculum-coverage.md) as they land.

## Sources
Bronstein *Symbolic Integration I*; Cox–Little–O'Shea *Ideals, Varieties, and
Algorithms*; von zur Gathen–Gerhard *Modern Computer Algebra*; SymPy module docs
(integrals/heurisch, risch, solvers/ode, matrices/normalforms, functions/special,
simplify/fu, assumptions); Wikipedia (Berlekamp–Zassenhaus, Faddeev–LeVerrier,
Gosper, Sturm, real-root isolation, CAD, Jacobi/Legendre); van Hoeij knapsack;
Kannan–Bachem HNF/SNF; Lazard–Rioboo–Trager. Full URLs in the research transcript.
