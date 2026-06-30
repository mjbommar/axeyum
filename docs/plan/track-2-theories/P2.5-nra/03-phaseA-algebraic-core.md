# P2.5 · Phase A — The algebraic core (already in `axeyum-ir`)

> **Corrected 2026-06-30 — Phase A is largely DONE, and there is NO `axeyum-poly`
> crate.** Per ADR-0044/0045/0046 the exact-poly + Sturm + resultant primitives and
> the bignum `RealAlgebraic` already live in **`axeyum-ir`**
> (`rational.rs`, `poly.rs`, `poly_big.rs`, `real_algebraic.rs`), with the CAD
> elimination/isolation logic in `axeyum-solver/src/nra_real_root.rs`. The
> code-inventory below is retained as a *map of what exists* and the *small
> remaining additions* (McCallum/Hong projection; richer multivariate ops) — NOT a
> from-scratch build. Do not create a crate (ADR-0001: reuse satisfies the
> boundary). See [00-current-state.md](00-current-state.md) for the corrected
> baseline.

**Size:** ~~XL~~ → **mostly landed**; remaining = projection-quality + breadth ·
**Depends on:** — · **Blocks:** Phases B, C, D, E and QE (P2.6), SOS (Track 3).

## What already exists (inventory, 2026-06-30)

- `axeyum-ir::rational` — `Rational` (i128, `checked_*`, overflow-graceful).
- `axeyum-ir::poly` — `RatVec` univariate: trim/degree/derivative/rem/gcd/monic/
  exact-div/`squarefree_part`/eval; **Sturm** (`sturm_chain`, `sturm_sign_changes`,
  `count_roots_in`); **resultant** (`sylvester_matrix`, `sylvester_determinant` by
  eval-interpolation + a Leibniz oracle).
- `axeyum-ir::poly_big` — bignum (`Vec<BigInt>`/`BigRational`) versions of all the
  above + `big_bareiss_determinant`, `big_newton_interpolate`, and
  `combine_retry` (the full α±β/α·β field-arithmetic pipeline). Caps:
  `BIG_MAX_DEGREE = 24`, `BIG_MAX_SYLVESTER_DIM = 24`.
- `axeyum-ir::real_algebraic` — `RealAlgebraic{poly:Vec<BigInt>, lo,hi:BigRational}`,
  `sign_at`/`sign_at_big`, `compare_*`, `neg`/`add`/`mul` field arithmetic.
- `axeyum-solver::nra_real_root` — Sturm root isolation (`isolate_roots`,
  `sturm_isolate_rec`, `isolate_one`), bivariate resultant elimination
  (`resultant_univariate`, `MultiPoly`), 2-var + N-var CAD
  (`decide_*_cad_*`, `isolate_critical_values`, sign-invariant sections).

## Remaining Phase-A-ish additions (small, vs the original XL)

> The algebraic core is soundness-critical and reused everywhere, so any addition
> is tested to death and differential-checked against the existing exact code.
> **No C/C++**: `num-bigint`/`num-rational` only (already adopted; see
> [01-literature.md §9](01-literature.md)). The only genuinely-open items are
> interval arithmetic (for ICP) and a proper McCallum/Hong projection (performance).

| id | task | status | size | exit |
|---|---|---|---|---|
| T-A.1 | Bignum foundation (`num-bigint`/`num-rational`, i128 fast path) | **DONE** — `poly_big.rs`, `RealAlgebraic` bignum (ADR-0045/0046) | — | landed |
| T-A.2 | Multivariate polynomial | **DONE (enough)** — `MultiPoly` (`nra_real_root.rs`); richer sparse ops add as needed | S | as needed |
| T-A.3 | Univariate gcd / squarefree / derivative | **DONE** — `poly.rs` / `poly_big.rs` | — | landed |
| T-A.4 | Resultant + discriminant | **DONE** — `sylvester_*`, `big_bareiss_determinant`, discriminant via `Res(p,p')` | — | landed |
| T-A.5 | Real root isolation (Sturm) | **DONE** — `isolate_roots`, `sturm_*` (fuzz-found 2 bugs, fixed) | — | landed |
| T-A.6 | Real algebraic numbers + field arithmetic | **DONE** — `real_algebraic.rs` (`sign_at`, `compare`, `neg`/`add`/`mul`) | — | landed |
| **T-A.7** | **Interval arithmetic** (correctly-rounded rational intervals) for ICP (Phase C) | TODO | S–M | sound containment property |
| **T-A.8** | **McCallum/Hong projection** — replace resultant-elimination lifting; finest squarefree basis; required-coefficients | TODO (the real remaining Phase-A work — performance) | L | projection sets match a reference on CAD test cases; measured cell-count reduction |

> Original references retained for T-A.7/T-A.8: McCallum 1998; Brown 2001; Lazard
> 1994 / Paunescu 2019; Ducos 2000. The bignum-foundation/root-isolation/
> algebraic-number rows (T-A.1–T-A.6) are **already shipped** — see ADR-0044/45/46
> and `nra-cad-nlsat-plan.md`.

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

## Exit criteria for the remaining Phase-A work

1. **(T-A.7)** Interval arithmetic over exact rationals lands in `axeyum-ir`
   (`forbid(unsafe_code)`, WASM-green, clippy `-D warnings`), with a sound
   containment property test — the substrate Phase C (ICP) needs.
2. **(T-A.8)** A McCallum/Hong projection operator replaces the resultant-
   elimination lifting in the CAD path, property-tested against the existing
   resultant code and a reference, with a **measured** cell-count / wall-clock
   reduction on the public QF_NRA slice (no perf claim without the measurement).
3. Both keep the four differential-fuzz gates (NRA/NIA/UFLIA/ABV) at DISAGREE=0.

T-A.1–T-A.6 are **already shipped** (ADR-0044/45/46). This phase no longer blocks
the others — Phases B/C/D/E build on the existing core; T-A.8 is a *performance*
upgrade that can land in parallel with them.
