# ADR-0044: Algebraic field arithmetic (α±β, α·β, −α) in the IR value layer

Status: accepted
Date: 2026-06-21

## Context

[ADR-0038](adr-0038-real-algebraic-numbers.md) added `Value::RealAlgebraic
{poly, lo, hi}` — an exact irrational real carried as a defining integer
polynomial plus an isolating interval — but explicitly deferred *field
arithmetic*: combining two algebraic numbers (`√2 + √3`, `√2 · √3`). Its
evaluator therefore returns a graceful `Err` (`AlgebraicArithmeticUnsupported`)
the moment a Real `add`/`mul`/`neg`/`sub` has a `RealAlgebraic` operand. That
ceiling is exactly what blocks the move from "single-variable NRA decider" to a
real multivariate engine: every sample-point construction in a CAD/nlsat lifting
(the [NRA durability plan](../05-algorithms/nra-cad-nlsat-plan.md), step 1)
produces algebraic coordinates that must then be added and multiplied to
evaluate the next polynomial's sign. Without field arithmetic the ladder cannot
leave the single-variable rung.

The mathematics is classical and exact: `α + β` is a root of the univariate
**resultant** `Res_y(p_α(y), p_β(x − y))`, and `α · β` is a root of
`Res_y(p_α(y), y^{deg β} · p_β(x / y))`. The resultant may be reducible and carry
*extra* roots, so the result is only well-defined once the **correct** root is
isolated. That isolation is precisely the Sturm root-counting primitive landed
ahead of this work (commit `235e967`): the sum lies in `[α.lo+β.lo, α.hi+β.hi]`
and the product in the interval spanned by the four endpoint products; refine
until that interval brackets *exactly one* root of the resultant's squarefree
part (Sturm count `== 1`, strict opposite endpoint signs) — the `RealAlgebraic`
one-root invariant, re-established.

This ADR fixes **where** that capability lives and **how** it composes, because
it forces a cross-crate move that the plan flagged: the Sturm/resultant
primitives are in `axeyum-solver` but the value type they must operate on lives
in `axeyum-ir`.

## Decision

Implement algebraic field arithmetic as **methods on `RealAlgebraic` in
`crates/axeyum-ir/src/real_algebraic.rs`**, and **move the pure exact-rational
polynomial + Sturm primitives down into `axeyum-ir`** (a new
`crates/axeyum-ir/src/poly.rs`) so there is *one* isolation implementation that
both the IR value layer and the solver reuse.

### Why the IR value layer (not the solver)

Field arithmetic is an operation on the IR *value* `RealAlgebraic`, and the
**ground evaluator must compute it** — a model that mixes algebraic witnesses has
to evaluate `α + β` to replay-check a `Sat`. `eval` lives in `axeyum-ir` and
cannot call up into `axeyum-solver` (that would invert the dependency DAG).
Placing the arithmetic on the value, beside `sign_at`/`compare_rational`, keeps
the evaluator self-contained and every algebraic `Sat` checkable by the same
crate that produced the value.

### The primitive move (one isolation implementation)

The genuinely pure pieces — `RatVec` and the exact-`Rational` poly helpers
(trim/degree/derivative/`rem`/`gcd`/monic/exact-div/`squarefree_part`), the Sturm
core (`sturm_chain`/sign-changes/`count_roots_in`/`isolate_roots_sturm`), and
`resultant_univariate`/`sylvester_determinant` — move from
`axeyum-solver/nra_real_root.rs` into `axeyum-ir/src/poly.rs`. They depend only
on `Rational`/`Sign`, both already owned by `axeyum-ir` (the leaf crate), so the
move is dependency-clean. `nra_real_root.rs` then re-uses them via
`axeyum_ir::poly::…`. The move is **behavior-preserving**: the existing `nra`,
`nra_real_root`, and `sturm_roots` suites pass unchanged — that equivalence is
the move's correctness proof. Any primitive entangled with arena/solver types
stays in the solver; only the pure core descends.

### The operations (each exact, or a sound decline)

`neg`, `add`, `mul`, `sub` (= `add(neg)`) and the rational-lift wiring, each
returning `Option<RealAlgebraic>` — `None` on `i128` overflow or whenever single-
root isolation cannot be *guaranteed*. The contract is the ADR-0038 invariant,
re-established by Sturm: a returned `RealAlgebraic` brackets **exactly one** root
of its defining polynomial. A rational result (e.g. `√2 · √2 = 2`, or either
operand zero) collapses to `Value::Real`. No floating point; no new dependency
(bignum to lift the `i128` ceiling is the separately-gated
[step 2](../05-algorithms/nra-cad-nlsat-plan.md) — decline until then).

### Evaluator contract

`Op::RealAdd`/`RealMul`/`RealNeg`/`RealSub` upgrade from the blanket
`AlgebraicArithmeticUnsupported` `Err` to: when an operand is `RealAlgebraic`
(lifting a rational operand to `x − c`), compute via the methods above and return
`Value::RealAlgebraic` (or `Value::Real` when rational). On `None`, return the
**same graceful `Err`** as today — never a panic, never a wrong value. This is a
strict capability gain: no existing `eval` result changes except `Err →
computed`.

## Evidence

- `crates/axeyum-ir/tests/real_algebraic_field.rs`: `√2 + √3` is a root of
  `x⁴ − 10x² + 1` (`sign_at == Zero`) and brackets `≈ 3.146`; `√2 · √3` is a root
  of `x² − 6`; `−√2 < 0` and roots `x² − 2`; `eval` of an algebraic-operand
  `RealAdd` now computes (not `Err`) and replays via `sign_at`; overflow /
  un-isolable shapes decline (`None`/`Err`) without panic.
- The Phase-A move is validated by **zero** change in the `nra`,
  `nra_real_root`, and `sturm_roots` suites (the one-isolation-implementation
  equivalence), and the whole `axeyum-ir` + `axeyum-solver` suites stay green.

## Alternatives

- **Keep field arithmetic in the solver.** Rejected: `eval` (in `axeyum-ir`)
  must compute algebraic combinations to replay-check models, and it cannot
  depend on the solver. The value operation belongs on the value.
- **Duplicate the Sturm/resultant primitives into `axeyum-ir`.** Rejected:
  two isolation implementations drift, and isolation is soundness-critical (a
  divergence is a potential wrong root). One owner, re-used.
- **Bignum coefficients now.** Rejected for this slice: `i128`-with-decline is
  sound and covers the headline cases; bignum is the next gated step behind the
  same interface.
- **Approximate the combined value numerically.** Rejected outright: floating
  point on a soundness path is forbidden, and an approximate witness makes `Sat`
  replay fragile.

## Consequences

- Easier: algebraic witnesses now *compose* — the prerequisite for CAD/nlsat
  sample-point lifting (the multivariate unlock). The evaluator computes mixed
  algebraic/rational arithmetic and every such `Sat` stays replay-checkable.
- Structural: the exact-poly + Sturm primitives now live in `axeyum-ir`, one
  implementation shared by the value layer and the solver — a deliberate, proven
  boundary move (not a new crate; ADR-0001's "split only when a boundary is
  exercised" is satisfied by re-use, not speculation).
- Harder / later: the `i128` ceiling remains until the bignum step; higher-degree
  combinations decline to `unknown`. CAD/nlsat itself, and per-cell evidence,
  remain their own downstream slices — this ADR delivers only the field-arithmetic
  rung they stand on.
