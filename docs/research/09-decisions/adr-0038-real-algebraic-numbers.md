# ADR-0038: Real algebraic numbers (defining polynomial + isolating interval)

Status: accepted
Date: 2026-06-20

## Context

The model `Value` is rational-only (`Value::Real(Rational)`, ADR-0015), so a
satisfiable nonlinear-real query whose only witness is *irrational* could never be
reported `Sat`. Concretely, `real x*x = 2` should be **Sat with witness √2**, but
the NRA path ([ADR-0024](adr-0024-nra-linear-abstraction.md)) abstracts the
product `x·x` to a fresh unconstrained variable, losing the algebraic fact, and so
only ever returns `Unknown`. This is the first place the finite/rational model
representation blocks a correct verdict on the ladder toward Z3 parity (the NRA /
CAD rung; see the north-star note and the foundational DAG's P2.5/NRA entries).

This ADR closes the representation question: **how does the stack carry an exact
irrational real value in a model, and decide the single-variable case soundly?**
It must not paint the IR or evidence formats into a rational-only corner, and it
must not introduce floating point anywhere on a soundness path.

## Decision

Add a first-class **real algebraic number** value — `Value::RealAlgebraic` — and a
single-variable NRA decider that produces irrational witnesses, both bounded and
exact, declining (sound `unknown`) on any doubt. Slice 1 supports **sign tests and
comparison only**; algebraic *field arithmetic* (adding/multiplying/inverting two
algebraic numbers) and multivariate CAD are explicitly deferred.

### Representation

`RealAlgebraic { poly: Vec<i128>, lo: Rational, hi: Rational }` (new
`crates/axeyum-ir/src/real_algebraic.rs`): a defining integer polynomial
(LSB-first, mirroring the NIA/NRA `Poly` layout) plus a rational open interval
`(lo, hi)` that contains **exactly one** real root of `poly`. That root *is* the
value (e.g. `√2` = the root of `x² − 2` in `(1, 2)`). The one-root invariant is
established by the constructor (a strict, nonzero sign change of `poly` between the
endpoints; isolation from other roots guaranteed by the decider's root isolation).

### Operations (slice 1 only)

- `sign_at(q, α) -> Sign` — the exact sign of an arbitrary integer polynomial `q`
  at `α`, by **interval refinement**: bisect `(lo, hi)`, keeping the half that
  still brackets the defining root (exact Horner over `Rational`), until `q` is
  sign-constant and nonzero across the bracket. `q` vanishing at `α` is detected
  exactly by an integer **polynomial-divisibility** test (`poly | q` over ℚ ⇒
  `q(α) = 0`) — the only sound way to confirm a zero at an irrational point, and
  the path that decides the replay call `sign_at(poly, α) = 0`.
- `compare_rational(c) -> Ordering` — refine until `c` is outside `(lo, hi)`, or
  detect `poly(c) = 0` (then `α = c`).
- `Eq` / `Hash` / `Display` (`"root of 1*x^2 - 2 in (1, 2)"`), and a constructor
  that enforces the one-root-in-interval invariant.

Refinement is **bounded**; an `i128`/`Rational` overflow or a failure to converge
returns `None`, and the caller declines.

### Evaluator contract (the soundness-safe minimum)

The ground evaluator (`crates/axeyum-ir/src/eval.rs`, the trust anchor) handles a
`Value::RealAlgebraic` operand exactly for `Op::RealLt/Le/Gt/Ge` and `Op::Eq` (via
`compare_rational` / a root-aware `real_cmp`). Real **field arithmetic**
(`Op::RealAdd/Sub/Mul/Neg/Div`) over an algebraic operand returns a graceful
`Err(IrError::AlgebraicArithmeticUnsupported)`. `eval` already returns `Result`, so
this surfaces as a decline / `unknown`, never a wrong value.

Crucially, the decider **replay-checks its own algebraic witnesses** via
`RealAlgebraic::sign_at(p, α) = 0` against the polynomial `p` it already holds — it
never asks `eval` to multiply two algebraic numbers. So the evaluator need not
implement algebraic field arithmetic for slice 1 to be sound and useful. A rational
witness (for inequalities and rational roots) replays through the existing exact-
rational `eval` unchanged.

### The decider

`crates/axeyum-solver/src/nra_real_root.rs`,
`decide_real_poly_constraint(arena, assertions)`, hooked in `auto.rs` in the
`features.has_real` block **before** `check_with_nra` (mirroring the `nia_square`
hook). It fires only when the **whole** query is exactly **one** assertion that
collects to a single-variable real polynomial `p(x) ⋈ 0` (ops `RealAdd/Sub/Mul/Neg`
+ `RealConst`/symbol; denominators cleared to integer coefficients by a positive
multiplier, preserving every relation). Anything else — ≥ 2 variables, a non-Real
sort, a non-polynomial operator, a second assertion, oversized coefficients/degree,
any overflow — **declines** (`None`).

- `=`: isolate the real roots of `p` over the Cauchy bound (uniform rational grid
  for sign changes, then bisection per cell; rational-root-theorem recovery of
  exact rational roots). A rational root → `Value::Real`; an irrational root →
  `Value::RealAlgebraic`. No real root ⇒ **Unsat** (exact). `x*x = 2` ⇒
  `p = x² − 2` ⇒ Sat with `±√2`.
- `<, ≤, >, ≥`: the roots partition ℝ into sign-constant intervals; pick a
  **rational** sample in a matching-sign region. Unsat iff none matches
  (`x*x < 0` ⇒ Unsat).
- `≠`: Sat unless `p ≡ 0`; exhibit a rational non-root.

### Precision and soundness policy

`i128` coefficients with overflow-→-decline throughout (bigint deferred). The
soundness method is the project standard: the **isolating-interval invariant** +
**replay-check of every `Sat`** (`sign_at` for algebraic, ground `eval` for
rational) + **decline on any doubt**. No floating point appears in the
implementation; the only float in the codebase for this feature is a *test oracle*
that cross-checks `sign_at` against a brute-force float computation.

## Evidence

- `crates/axeyum-ir/src/real_algebraic.rs` unit tests: `sign_at` of the defining
  poly and rational multiples → `Zero`; linear-poly signs at `±√2`;
  `compare_rational` brackets; root-aware equality; a property test that `sign_at`
  agrees with a float oracle over all small `c₂x² + c₁x + c₀` at `√2`.
- `crates/axeyum-solver/tests/nra_real_root.rs` (end-to-end through `solve`):
  `x*x = 2` → Sat with a `RealAlgebraic` witness replaying `sign_at(x²−2, α) = 0`;
  `x*x = 3` → Sat (algebraic); `x*x = 4` → Sat (rational `±2`, replays through
  `eval`); `x*x = 0` → Sat(0); `x*x = −1` → Unsat; `x*x < 0` → Unsat; `x*x > 2`,
  `x*x ≠ 2` → Sat (rational); `x*x ≤ 0` → Sat(0); and decline-not-Unsat for the
  two-variable product, a second assertion, and the integer (NIA) square — the
  last confirming the integer path is unchanged.

## Alternatives

- **Bigint / arbitrary-precision coefficients now.** Rejected for slice 1: `i128`
  with overflow-→-decline is sound and covers the headline cases; bigint is a clean
  later extension behind the same interface.
- **Full CAD / multivariate from the start.** Rejected: a keystone is sliced, not
  deferred — the single-variable decider lands real capability now; multivariate
  CAD and algebraic field arithmetic are the next slices.
- **Store the witness as a high-precision rational approximation.** Rejected: not
  exact, would make `Sat` replay fragile and risk a wrong verdict.
- **Decide algebraic equality/sign by floating point.** Rejected outright: floating
  point on a soundness path is forbidden by the project's hard rules.

## Consequences

- Easier: irrational `Sat` witnesses are now representable and checkable; the
  evaluator comparison ops are algebraic-aware; the NRA ladder has a sound exact
  rung for the single-variable case.
- Harder / revisited later: `Value` gains a non-`Copy`, non-scalar variant — every
  exhaustive `match` on `Value` across the IR, rewrite, and solver crates handles
  it (compile-enforced; non-real consumers panic/`Err`/decline as apt). Algebraic
  field arithmetic and multivariate CAD remain `unknown` until their own slices.
- Forward: when field arithmetic lands, the evaluator's
  `AlgebraicArithmeticUnsupported` arms become real implementations, and the
  decider can compose roots — no representation change required.
