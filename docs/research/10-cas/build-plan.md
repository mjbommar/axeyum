# Build plan — decidable-first, evidence-gated CAS

Status: plan (2026-07-20)
Last updated: 2026-07-20

## Progress snapshot (2026-07-20)

Shipped and verified in `crates/axeyum-cas` (pure Rust, WASM-green, clippy-clean,
**99 unit tests + 18 doctests + runnable example**). Every transform is either
denotation-preserving-by-construction or **certified** by the decidable zero-test
(`equal`) / differentiate-and-check; the certificate is a correctness backstop, so
out-of-fragment cases decline to `None`, never a wrong answer.

**Core algebra:** `differentiate` (full chain rule incl. transcendental heads),
`substitute`, `normalize`/`equal` (decidable polynomial zero-test with witness;
transcendental heads handled as sound opaque atoms), `expand`, `cancel`, `factor`
(rational linear factors, certified), `solve` (rational + quadratic roots),
`apart` (partial fractions, certified), `simplify`, `together`-via-`expand`,
`Display`.

**Calculus:** `integrate` → `CertifiedIntegral` across polynomials, the full
univariate **rational** fragment (Horowitz rational part + Rothstein–Trager logs +
irreducible-quadratic `atan`), and `∫ k·f(ax+b)` / `∫ p(x)·e^(ax)` /
`∫ p(x)·sin|cos(ax)`; `limit` (continuous, 0/0, ±∞); `series` (Maclaurin/Taylor);
`sum_polynomial` (certified by telescoping); `dsolve_homogeneous` (constant-coeff
linear ODEs, certified by the ODE operator).

**Heads:** `exp, sin, cos, tan, ln, atan, sqrt` (extensible `Unary`).

**Modules:** `matrix.rs` (symbolic linear algebra — det, RREF, solve, inverse,
rank, eigenvalues, characteristic polynomial), `mvpoly.rs` (multivariate ring ops,
GCD, square-free), `groebner.rs` (Buchberger, ideal membership), `ntheory.rs`
(gcd, mod-pow/inverse, deterministic `is_prime`, `factorize`, CRT, Euler φ, …),
`series.rs`, `ratint.rs` (integration internals). Complex numbers (`I` with
`I²=−1` in the zero-test, `conjugate`, `real_part`, `imaginary_part`) and
`dsolve_homogeneous` are shipped. So **G0–G18 are all implemented** — this
snapshot's earlier "Next" list (G4/G6/complex/ODEs) is superseded.

**Next wave (post-G18).** The prioritized continuation is now maintained in two
companion notes rather than this snapshot:
[next-wave-roadmap.md](next-wave-roadmap.md) (SymPy/Mathematica capability survey,
prioritized top-15) and [curriculum-gaps.md](curriculum-gaps.md) (the union of the
seven per-branch curriculum reviews, ranked Tier A–D by
value × certifiability × buildability). **Coverage target: at least SymPy's
compute surface, aiming at Mathematica's — which is exactly what the 23-node
curriculum + K-12 layer enumerate.** Tier A (eigenvectors, definite integration,
Taylor-about-a-point, radical simplification, the number-theory bundle, statistics,
vector calculus/Jacobian, integer factorization) is in active TDD build.

---

Phased sequence for the [CAS initiative](README.md), following the project's
standing rules: **thin vertical slice first** (ADR-0001), **decidable-first**,
**TDD**, and **no public transform without semantics + checker + self-checking
scenario** ([foundational-dag.md](../08-planning/foundational-dag.md), ADR-0008).
Build units `G*` are from [gap-analysis.md](gap-analysis.md). No time estimates
(per roadmap convention); each phase has a checkable exit gate.

## Phase C0 — the certified polynomial kernel (thin vertical slice)

**Units:** G0 (expr layer + reduce-to-decide spine, minimal), G1 (rational-function
differentiation), G2 (polynomial canonical form + decidable `equal?`).

**Deliverable.** A `axeyum-cas` crate exposing, over the rational-function
fragment (variables, ℚ constants, `+ − × ÷ ^ℤ`):
- `differentiate(expr, var) -> CasExpr` — sum/product/quotient/power rules on the
  term DAG;
- `normalize(expr) -> CasExpr` — polynomial/rational canonical form;
- `equal(a, b) -> Certified<bool>` — **decidable zero-test** of `a − b`, returning
  a trust-tagged answer with a witness.

**Certification.** `differentiate` on the polynomial fragment is checked *two
independent ways*: (1) extract coefficients and compare to `poly.rs::rat_derivative`
exactly; (2) lower `result − d/dx(p) ≡ 0` to QF_NRA and decide. `equal` is the
`poly.rs` normal form (the normal form *is* the witness), cross-checked by QF_NRA
on the rational fragment.

**Exit gate.**
- `differentiate` is evaluator-equivalent to numeric differentiation on random
  rational polynomials (finite-difference-free: compare against `rat_derivative`
  after extraction) at many degrees/widths;
- the exemplar `D[x² + c] = 2x` returns `equal(differentiate(x²+c, x), 2x) =
  certified(true)` with a re-checkable witness;
- a **self-checking scenario** (double-duty, ADR-0033 shape) lands in
  `axeyum-scenarios` for the differentiation-rule family, exhaustively self-checked
  at small width;
- `cargo test` + `cargo clippy` green; the CAS crate builds for `wasm32`.

**Why this slice.** Smallest capability that (a) is genuinely compute-side (returns
new expressions), (b) is fully decidable and certifiable with existing arithmetic,
(c) exercises the entire proof-carrying spine end to end, and (d) answers the
user's own exemplar. It buys the reusable G0 substitution/lowering API for
everything after.

## Phase C1 — the polynomial tower (certified heart)

**Units:** G3 (multivariate sparse polynomials over a domain tower ℚ/ℤ/𝔽ₚ),
G4 (multivariate subresultant GCD + square-free), G2-extended (multivariate
canonical form/zero-test).

**Exit gate.** Multivariate `gcd`, `normalize`, `equal` are `certified`
(cofactor/Bézout re-multiply checks + zero-test); differential-tested against a
reference (SymPy as a *test-only* oracle, never in the trust base); self-checking
scenarios for polynomial-identity families extended; exact-arithmetic
overflow paths degrade to `unknown`, never wrong.

## Phase C2 — factorization + directed simplification

**Units:** G5 (univariate factorization 𝔽ₚ/ℤ/ℚ: Berlekamp–Zassenhaus + Hensel +
LLL recombination), G7 (`expand`/`collect`/`factor`/`cancel`/`together` as
directed transforms), the first slice of G8 (rewrite-apply on the e-graph for the
directed rules).

**Exit gate.** `factor` output re-multiplies to the input (`certified`); directed
simplifiers are denotation-preserving by manifested rules; the heuristic frontier
(anything not lowering to a decidable zero-test) is labeled `heuristic`;
per-substep certification demonstrated on a mixed example.

## Phase C3 — exact symbolic linear algebra

**Unit:** G9 (matrix type; Bareiss fraction-free solve/det/rank; Hermite/Smith
normal forms; characteristic polynomial via Faddeev–LeVerrier/Berkowitz).

**Exit gate.** `solve`/`det`/`rref` return `certified` with residual/unimodular
witnesses; matches the linear-algebra self-checking scenarios; RCF-eigenvalue
identities route through QF_NRA where closed forms are unavailable (Abel–Ruffini
honesty).

## Phase C4 — Gröbner + polynomial system solving

**Units:** G6 (Buchberger → F4, ideal membership, FGLM), G14-poly (polynomial
equation systems via elimination/resultants).

**Exit gate.** Ideal membership returns the reduction-to-zero cofactor certificate
(`certified`); polynomial-system solutions substitute-back to zero; documented
doubly-exponential worst case with resource-bounded `unknown`.

## Phase C5 — transcendental heads + assumptions

**Units:** G10 (exp/log/sin/cos/sqrt as CAS heads + differentiation rules),
G15 (3-valued assumptions engine), G12-limits (Gruntz).

**Exit gate.** Transcendental differentiation is `decidable-uncertified` (per-rule
denotation, Lean-liftable target recorded); domain-sensitive rewrites gated by
assumptions; the certified surface from C0–C4 is unchanged and un-regressed.

## Phase C6 — integration (the flagship proof-carrying demo)

**Unit:** G11 (rational-function integration via partial fractions — `certified`;
then elementary via Risch–Norman/heurisch — `certified` **when returned**, by
differentiate-and-check; Meijer-G/definite — `heuristic`).

**Exit gate.** Every returned antiderivative is verified by differentiating it and
zero-testing against the integrand; a returned integral over the rational/decidable-
constant fragment is `certified`; fallthrough results are `heuristic`, never
mislabeled. This phase is the public demonstration that axeyum can hand back a
*certified* integral even when the search that found it was heuristic.

## Phase C7 — series, summation, number-theory compute

**Units:** G12-series, G13 (Gosper/Zeilberger), G16 (primality certs, integer
factorization).

**Exit gate.** Summation returns telescoping/recurrence certificates; primality
returns ECPP/AKS certificates; all re-checkable.

## Additional destinations (from [curriculum-coverage.md](curriculum-coverage.md))

These map the parts of the curriculum the first plan omitted; they are sequenced
by dependency, not bolted on.

- **C4b — Complex numbers (G17).** After C2 (factorization): exact `ℚ(i)` and
  complex-algebraic arithmetic; factorization/roots over ℂ (FTA), each root an
  algebraic number certified by substitute-back zero-test. Realizes the `complex`
  curriculum node. Complex *analysis* (residues, branch cuts) is heuristic /
  Lean-horizon, gated on the assumptions engine (C5).
- **C6b — Differential equations (G18).** After C6 (integration): symbolic ODE
  solving. Linear constant-coefficient ODEs are decidable (characteristic
  polynomial via C2 factorization) and **certified by substituting the solution
  into the ODE and zero-testing the residual** — the same differentiate-and-check
  property that certifies integration. General ODEs are heuristic, certified only
  by substitute-and-check when a candidate is produced.
- **Geometry suite (not a phase).** Euclidean geometry = the first-order theory of
  real-closed fields (decidable, Tarski). It lands as a scenario/example suite
  over the RCF/CAD core (C4/NRA), coordinatizing incidence/midpoint/Pythagoras as
  polynomial constraints — suite B of
  [foundational-example-suites.md](../08-planning/foundational-example-suites.md).

## Cross-cutting, every phase

- **Double-duty artifacts** (ADR-0033): each transform ships a self-checking
  scenario; `coverage.rs` audit shows no `certified` capability without a test.
- **Trust tag on every answer**; a golden test forbids an unsound `certified`.
- **SymPy/Mathematica are test-only differential oracles**, never in the trust
  base of a shipped answer.
- **WASM build stays green.**
- **The initiative never starves** the solver + Lean-parity mission; CAS phases
  reuse (and stress-test) the decision procedures rather than competing.

## First actions (Phase C0)

1. First-slice **ADR** ratifying the `axeyum-cas` layer + reduce-to-decide design
   (next number after `09-decisions/`).
2. Scaffold `crates/axeyum-cas` with the minimal `CasExpr`/lowering API.
3. TDD `differentiate` + `equal` on the rational fragment; certify via `poly.rs`
   + QF_NRA; land the `D[x²+c]=2x` test and a differentiation self-checking
   scenario.
