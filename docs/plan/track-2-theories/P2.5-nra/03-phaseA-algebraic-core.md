# P2.5 · Phase A — The algebraic core (`axeyum-poly`)

**Size:** XL (the long pole) · **Depends on:** — · **Blocks:** Phases B, C, D, E
and QE (P2.6), SOS reconstruction (Track 3).

> Everything complete about nonlinear arithmetic rests on this. Build it in a
> dedicated pure-Rust crate, test each layer to death (it's soundness-critical and
> reused everywhere), and use the existing single-variable `nra_real_root.rs` as a
> differential oracle. **No C/C++**: `num-bigint`/`num-rational` only (see
> [01-literature.md §9](01-literature.md)).

## Why a new crate (`axeyum-poly`)

The polynomial + real-algebraic-number core is consumed by NRA, NIA, quantifier
elimination, and SOS proof reconstruction — four boundaries, so per ADR-0001 the
boundary is proven by use. Keeping it out of `axeyum-solver` keeps the solver lean
and the math independently testable and WASM-buildable.

**ADR-A0 (write first):** "axeyum-poly: a pure-Rust polynomial & real-algebraic
core." Decide: bignum strategy (`num-bigint`/`num-rational` vs. own), the
distributed-vs-recursive polynomial representation split, and the
`forbid(unsafe_code)` + WASM build constraints.

## Tasks (dependency order)

| id | task | key references | size | exit |
|---|---|---|---|---|
| T-A.1 | **Bignum foundation** — adopt `num-bigint`/`num-rational`; wrap as `axeyum-poly::{Int,Rat}`; reconcile with `axeyum_ir::Rational` (i128, overflow-guarded). Keep a fast i128 path, big fallback on overflow (fixes the [Rational-overflow panic class](../../../research/) by construction). | `num-bigint` docs | M | exact arithmetic, no panics on huge constants; WASM build green |
| T-A.2 | **Multivariate polynomial** (`mpoly.rs`) — distributed sparse `Monomial→Coeff`; add/mul/eval, degree, variables, content/primitive part. | *Mathematics* 7(5):441 (2019) | M | round-trips IR real/int terms; property-tested vs. naive eval |
| T-A.3 | **Univariate polynomial** (`upoly.rs`) — dense; gcd, pseudo-division, derivative, squarefree decomposition. | Ducos 2000 | M | gcd/squarefree property-tested |
| T-A.4 | **Subresultant PRS + resultant + discriminant** (`resultant.rs`) — Ducos' optimized chain; Sylvester resultant; `disc = res(p,p')`. | Ducos 2000; Collins 1967 | L | resultants match a reference CAS on a fixed test set |
| T-A.5 | **Real root isolation** (`sturm.rs`, `root_isolation.rs`) — Sturm sequences + (optionally) VCA/VAS; isolating intervals with refinement. Lift the existing `nra_real_root.rs` isolation to arbitrary precision. | Sturm; Collins–Akritas SYMSAC '76; Akritas et al. ESA 2006 | L | exact root count on test polys; differential vs. current single-var path |
| T-A.6 | **Real algebraic numbers** (`algebraic.rs`) — `RealAlgebraic{defining_poly, interval}`; comparison by interval refinement; sum/product via resultants; `sign_at`. Generalize `Value::RealAlgebraic`. | Basu–Pollack–Roy 2006; Coste–Roy 1988 (Thom) | XL | α arithmetic + comparison property-tested; sign determination exact |
| T-A.7 | **Interval arithmetic** (`interval.rs`) — correctly-rounded rational intervals (for ICP and root refinement). | — | S–M | sound containment property |
| T-A.8 | **Projection operators** (`projection.rs`) — McCallum (default) + Lazard (optional); finest squarefree basis; required-coefficients. | McCallum 1998; Brown 2001; Lazard 1994 / Paunescu 2019 | XL | projection sets match reference on CAD test cases |

## Soundness method (this layer especially)

- **Differential testing is the spine.** The existing single-variable
  `nra_real_root.rs` is exact and trusted; every new isolation/algebraic result on
  single-variable inputs must agree with it. Property tests (random polynomials)
  check resultant/gcd/squarefree invariants against naive references.
- **Exact arithmetic only.** No floating point in the decision path. Floats may
  *guide* (e.g. initial sample) but never *decide*; every comparison resolves by
  exact interval refinement.
- **Overflow → big fallback, never wrap.** T-A.1 makes overflow a representation
  switch, not a panic and not a wrong answer (closes the Rational-overflow class
  for the nonlinear path).

## Exit criteria for Phase A

1. `axeyum-poly` builds on native + `wasm32-unknown-unknown`, `forbid(unsafe_code)`,
   no C/C++ dependency, clippy `-D warnings` clean.
2. Multivariate arithmetic, univariate gcd/squarefree, subresultant/resultant/
   discriminant, real root isolation, real algebraic number arithmetic + sign
   determination, and McCallum projection are all implemented and property-tested.
3. On every single-variable instance, the new core agrees with `nra_real_root.rs`
   (a CI differential test).
4. ADR-A0 merged; the crate is referenced from the foundational DAG.

This phase ships **no new decide-rate by itself** — it is infrastructure. Phases B
and C (built on it) deliver the first measured gains; D delivers completeness.
