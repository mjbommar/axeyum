# Curriculum coverage — the CAS as the compute engine for every node

Status: design note (2026-07-20)
Last updated: 2026-07-20

This note repairs a gap in the first plan: it did not map the CAS build units
onto the **whole** curriculum you already built. Here every node of the
[Formal Mathematics Tour](../../curriculum/curriculum.toml) (23 nodes) is mapped
to the CAS capability that makes it *computational*, and three areas the first
plan missed — **complex analysis**, **differential equations**, and **geometry**
— are added.

## The unifying frame

The curriculum's [self-checking corpus](oracle-as-test-harness.md) *verifies*
supplied statements at each node. The CAS is the other half: the **compute
engine** that produces the objects those statements are about (derivatives,
factorizations, solutions, normal forms). And the frame that ties them:

> **Each curriculum node's `decidability` tag is the CAS's trust ceiling for that
> node.** `decidable`/`computable` → the CAS *computes and certifies*;
> `bounded` → certified on the finite/decidable fragment, honest `unknown`
> beyond; `lean-horizon` → the CAS computes a *heuristic* result and the
> ∀-general theorem is a Lean proof-reconstruction target, never a false claim.

So the CAS does not "cover calculus" by proving ε–δ theorems; it *computes*
derivatives/integrals/series (certifying each by differentiate-and-check /
zero-test) while the ε–δ foundations remain the Lean rung. That is the honest
reading of "build SymPy/Mathematica functionality" against a decidability-tagged
curriculum.

## Node-by-node coverage (all 23 curriculum nodes)

Build units `G*` are from [gap-analysis.md](gap-analysis.md); phases `C*` from
[build-plan.md](build-plan.md).

| Layer | Node | Tag | What the CAS *computes* | Unit / phase | Trust ceiling |
|---|---|---|---|---|---|
| 0 | propositional-logic | decidable | CNF/DNF normal form, tautology decision, Boolean simplify | reuse SAT; CAS `simplify` | **certified** |
| 0 | predicate-logic | bounded | finite-domain instantiation / QE | reuse quantifier engine | certified (finite) |
| 0 | proof-methods | bounded | *produces* the witnesses/certificates other nodes need | cross-cutting | n/a (meta) |
| 0 | induction | bounded | closed forms (Gauss sum), base/step obligations | series/summation G13 | certified (instances) |
| 0 | sets | bounded | finite set-algebra normal forms | enumeration | certified (finite) |
| 0 | relations-and-functions | bounded | finite relation/function composition, properties | enumeration/EUF | certified (finite) |
| 0 | cardinality | lean-horizon | finite counting | G13/counting | certified finite; general → Lean |
| 1 | naturals | bounded | exact ℕ arithmetic | G16 | certified |
| 1 | integers | computable | exact ℤ arithmetic, gcd, factorization | G16 | **certified** |
| 1 | rationals | computable | **exact ℚ arithmetic — the substrate of everything** | in-tree (`Rational`) | **certified** |
| 1 | reals | bounded | real-algebraic numbers, RCF decision | `real_algebraic`, NRA | certified (algebraic/RCF); transcendental → heuristic |
| 1 | **complex** | lean-horizon | **ℚ(i) / complex-algebraic arithmetic, roots over ℂ** | **G17 (new)** | certified (algebraic); complex analysis → heuristic/Lean |
| 2 | divisibility-and-euclid | computable | gcd, Bézout, Euclid | G4 (`rat_gcd`) / G16 | **certified** |
| 2 | modular-arithmetic | bounded | 𝔽ₚ arithmetic, CRT, inverses | G3 domain tower (𝔽ₚ), G16 | certified |
| 2 | groups | bounded | finite group tables, orders | enumeration | certified (finite) |
| 2 | rings | bounded | finite ring compute; the domain tower ℤ/ℚ/𝔽ₚ | G3 | certified (finite) |
| 2 | fields | bounded | ℚ, 𝔽ₚ, ℚ(α) field arithmetic | G3 domain tower | certified |
| 2 | polynomials | computable | **the core: arithmetic, GCD, factor, Gröbner** | G1–G6 | **certified** |
| 2 | sequences-and-limits | lean-horizon | limit *values* (Gruntz), series to order | G12 | series certified; limit value decidable-uncertified; ε–δ → Lean |
| 2 | counting | computable | binomials, closed forms, hypergeometric sums | G13 (Gosper/Zeilberger) | **certified** |
| 3 | number-theory | bounded | primality certs, factorization, bounded Diophantine | G16 | certified (primality/factor); general Diophantine undecidable |
| 3 | linear-algebra | computable | Bareiss solve/det/rank, Hermite/Smith, char. poly | G9 / C3 | **certified** |
| 3 | calculus | lean-horizon | **differentiate (certified), integrate (certified-when-returned), limits/series** | G1/G11/G12 / C0,C6 | compute certified; ε–δ foundations → Lean |

## The three additions the first plan missed

### G17 — Complex numbers & the decidable fragment of complex analysis
Realizes the `complex` node. **Certified core:** exact **Gaussian-rational**
`ℚ(i)` arithmetic; **complex-algebraic numbers** (extend `real_algebraic.rs`'s
defining-poly + isolating-region idea to ℂ); polynomial arithmetic, GCD, and
**factorization/root-finding over ℂ** (fundamental theorem of algebra: an
`n`-degree polynomial has `n` complex roots, each an algebraic number — witness =
substitute-back zero-test). **Heuristic/Lean-horizon:** complex *analysis*
(contour integration, residues, branch cuts) — needs the assumptions engine (G15)
and is largely a proof/heuristic surface, exactly like real analysis.
Sequencing: after the real-algebraic and factorization core (post-C2), reusing
`poly_big`/`real_algebraic` machinery.

### G18 — Differential equations (symbolic ODE solving)
Not a curriculum node today (a candidate to add), but core SymPy (`dsolve`). The
**proof-carrying story is beautiful and mirrors integration**:
- **Decidable/certified fragment:** linear ODEs with constant coefficients →
  characteristic polynomial (reuse G5 factorization) → closed-form solution;
  certified by **substitute the solution back into the ODE and zero-test the
  residual** (the same differentiate-and-check pattern that makes integration
  certifiable). First-order separable / exact / linear ODEs likewise certify by
  substitute-and-check.
- **Heuristic/undecidable frontier:** general nonlinear ODEs, existence of
  closed-form solutions — no algorithm; compute heuristically, label, and certify
  *only* by substitute-and-check when a candidate is produced.
Sequencing: after integration (C6), since it depends on it. Adds a `Deriv`/ODE
representation to `axeyum-cas`.

### Geometry — a suite over the RCF/CAD core, not a new engine
Euclidean geometry is the first-order theory of real-closed fields (Tarski:
decidable). It is **not a new CAS engine** but an *application* of the
polynomial/RCF core (NRA/CAD) already planned — coordinatize points, express
incidence/midpoint/Pythagoras as polynomial (in)equalities, decide via NRA with a
rational witness (`sat`) or SOS/CAD certificate (`unsat`). This is exactly
[foundational-example-suites.md](../08-planning/foundational-example-suites.md)'s
suite B. Recorded here as a first-class *destination* of the CAS so it is not lost
again; it lands as a scenario/example suite consuming C1–C4, not a build unit.

## What stays Lean-horizon (honest, by the curriculum's own tags)

`cardinality`, `complex` (the *analysis*, not the arithmetic),
`sequences-and-limits` (the ε–δ layer), and `calculus` (the foundations) are
tagged lean-horizon. The CAS computes their decidable fragments and produces
heuristic results elsewhere; the ∀-general theorems are P3.6/P3.7 Lean
reconstruction targets. **The CAS never asserts a false result on these — it
labels the trust.** That labeling *is* the product.

## Consequence

- [gap-analysis.md](gap-analysis.md) gains **G17 (complex)** and **G18 (ODEs)**;
  geometry is a suite, not a unit.
- [build-plan.md](build-plan.md) gains a complex-numbers step (after C2) and an
  ODE step (after C6), and names the geometry suite as a C1–C4 destination.
- Every curriculum node now has a named CAS compute capability and an explicit
  trust ceiling — the node-by-node map the first plan lacked.
