//! Sound, bounded NIA capability: decide a single-variable integer **square
//! constraint** `x*x ⋈ c` (constant `c`, `⋈ ∈ {=, ≠, <, ≤, >, ≥}`) *exactly*.
//!
//! This closes the hunt-flagged gap `int x*x = 2` → **Unsat** (`2` is not a
//! perfect square), which the bounded bit-blast width ladder and the real
//! relaxation only ever report as `Unknown`.
//!
//! # Scope (deliberately narrow — correctness over reach)
//!
//! The pass fires *only* when the **whole** query (after the dispatcher's
//! preprocessing) is exactly one assertion of the shape
//!
//! ```text
//! (x * x) ⋈ c      or      c ⋈ (x * x)
//! ```
//!
//! where `x` is a single `Int` **variable** (the same symbol on both factors),
//! `x*x` is the `IntMul` of that variable with itself, and `c` is an integer
//! **constant**. Everything else — two distinct variables (`x*y`), a cube
//! (`x*x*x`), an extra term (`x*x + x = c`), a non-constant right-hand side
//! (`x*x = y`), a `Real`-sorted square, or any query with *more than one*
//! assertion (which could otherwise constrain `x`) — **declines** by returning
//! `None`, leaving the value of `x` to the existing NIA dispatch. A wrong
//! `sat`/`unsat` is unacceptable; declining is always sound.
//!
//! # The math
//!
//! Let `r = isqrt(c)` (the integer square root, for `c ≥ 0`):
//!
//! - `x*x = c`: `c < 0` ⇒ Unsat (squares are `≥ 0`); else Sat iff `r*r == c`
//!   (witness `x = r`), otherwise Unsat.
//! - `x*x ≠ c`: always Sat — `x` ranges freely, so it can always avoid the
//!   single value `c` (e.g. `x = r + 1`, or `x = 0` when `c ≠ 0`).
//! - `x*x < c`: `c ≤ 0` ⇒ Unsat (`x*x ≥ 0`); `c > 0` ⇒ Sat (`x = 0`).
//! - `x*x ≤ c`: `c < 0` ⇒ Unsat; `c ≥ 0` ⇒ Sat (`x = 0`).
//! - `x*x > c`: always Sat (`c < 0` ⇒ `x = 0`; `c ≥ 0` ⇒ `x = r + 1`, since
//!   `(r+1)² > c`).
//! - `x*x ≥ c`: always Sat (`x = 0` when `c ≤ 0`; large `x` otherwise — in fact
//!   `x = r + 1` works for any `c`).
//!
//! Every `Sat` returns a **replay-checked** witness model: the witness is set on
//! `x` and the *original* assertion is re-evaluated through the ground
//! evaluator; the `Sat` is emitted only if it evaluates to `true`. `Unsat` cases
//! are exact by the case analysis above.

use axeyum_ir::{Assignment, Op, TermArena, TermId, TermNode, Value, eval};

use crate::backend::{CheckResult, SolverError};
use crate::model::Model;

/// Above this magnitude for `|c|` the pass declines (returns `None`) rather than
/// risk `i128` overflow in the `isqrt` verification `(r+1)*(r+1)`. `2^100` is far
/// below `i128::MAX ≈ 1.7·10^38`, so `(r+1)²` for `r ≈ 2^50` stays well in range,
/// and any larger constant is left to the existing NIA dispatch (sound).
const MAX_ABS_C: i128 = 1i128 << 100;

/// The six integer comparison shapes the square pass decides.
#[derive(Clone, Copy)]
enum Cmp {
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
}

/// Decides a single-assertion integer **square constraint** `x*x ⋈ c` exactly.
///
/// Returns `Some(Sat(model))` / `Some(Unsat)` for the exact pattern (every `Sat`
/// model replay-checked against the original assertion), and `None` for anything
/// outside it — a two-variable product, a cube, an extra term, a non-constant
/// right-hand side, a non-`Int` square, a constant out of the safe range, or a
/// query with any number of assertions other than one. Declining is always sound.
///
/// # Errors
///
/// Returns [`SolverError`] to match the dispatcher's `?`-chained call site; the
/// decision itself does not currently fail (the `Result` is part of the stable
/// dispatch contract, kept for forward compatibility).
#[allow(
    clippy::unnecessary_wraps,
    reason = "signature matches the ?-chained auto.rs dispatch contract"
)]
pub fn decide_int_square_constraint(
    arena: &TermArena,
    assertions: &[TermId],
) -> Result<Option<CheckResult>, SolverError> {
    // The pass fires only when the WHOLE query is exactly one assertion. A second
    // assertion could otherwise constrain `x` (e.g. `x*x = 4 ∧ x = 2`), so we must
    // not decide the square in isolation — decline and let the NIA dispatch see all
    // constraints together.
    let [assertion] = assertions else {
        return Ok(None);
    };
    let Some((var, cmp, c)) = match_square_constraint(arena, *assertion) else {
        return Ok(None);
    };

    // Overflow guard: only decide constants whose magnitude keeps `(r+1)²` within
    // `i128`. Larger constants decline (sound) to the existing NIA path.
    if c.abs() >= MAX_ABS_C {
        return Ok(None);
    }

    let verdict = decide(cmp, c);
    match verdict {
        Verdict::Unsat => Ok(Some(CheckResult::Unsat)),
        Verdict::SatWith(witness) => {
            // Replay-check: set `x := witness` and evaluate the ORIGINAL assertion
            // through the ground evaluator. The `Sat` is sound only if it holds.
            let mut assignment = Assignment::new();
            assignment.set(var, Value::Int(witness));
            if !matches!(eval(arena, *assertion, &assignment), Ok(Value::Bool(true))) {
                // The witness did not satisfy the original assertion. This must not
                // happen for the case analysis above, but soundness comes first:
                // decline rather than emit an unchecked `sat`.
                return Ok(None);
            }
            let mut model = Model::new();
            model.set(var, Value::Int(witness));
            Ok(Some(CheckResult::Sat(model)))
        }
    }
}

/// The decision for one shape, carrying the concrete witness for `Sat`.
enum Verdict {
    Unsat,
    SatWith(i128),
}

/// Exact case analysis for `x*x ⋈ c` (see the module docs).
fn decide(cmp: Cmp, c: i128) -> Verdict {
    match cmp {
        Cmp::Eq => {
            if c < 0 {
                Verdict::Unsat // squares are ≥ 0
            } else {
                let r = isqrt(c);
                if r * r == c {
                    Verdict::SatWith(r) // perfect square: x = r
                } else {
                    Verdict::Unsat // c ≥ 0 but not a perfect square
                }
            }
        }
        // `x*x ≠ c` is always satisfiable: x ranges freely, so it can avoid the
        // single value c. Use x = 0 when c ≠ 0, else x = 1 (1 ≠ 0).
        Cmp::Ne => Verdict::SatWith(i128::from(c == 0)),
        // `x*x < c`: needs c > 0 (x*x ≥ 0); witness x = 0 gives 0 < c.
        Cmp::Lt => {
            if c <= 0 {
                Verdict::Unsat
            } else {
                Verdict::SatWith(0)
            }
        }
        // `x*x ≤ c`: needs c ≥ 0; witness x = 0 gives 0 ≤ c.
        Cmp::Le => {
            if c < 0 {
                Verdict::Unsat
            } else {
                Verdict::SatWith(0)
            }
        }
        // `x*x > c`: always sat. c < 0 ⇒ x = 0 (0 > c); c ≥ 0 ⇒ x = r+1 with
        // (r+1)² > c (r = isqrt(c) so (r+1)² > c by the isqrt postcondition).
        Cmp::Gt => {
            if c < 0 {
                Verdict::SatWith(0)
            } else {
                Verdict::SatWith(isqrt(c) + 1)
            }
        }
        // `x*x ≥ c`: always sat. x = r+1 works for every c (for c ≤ 0, x = 0 also
        // works, but r+1 is uniformly correct since (r+1)² ≥ 0 ≥ c there, and
        // (r+1)² > c ≥ ... for c ≥ 0).
        Cmp::Ge => {
            if c <= 0 {
                Verdict::SatWith(0)
            } else {
                Verdict::SatWith(isqrt(c) + 1)
            }
        }
    }
}

/// The binary-search ceiling for [`isqrt`]: `2^51`. The caller guards
/// `|c| < 2^100`, so `r = ⌊√c⌋ < 2^50 ≤ 2^51 = HI`, and every probed `mid` is
/// `≤ 2^51`, keeping `mid*mid ≤ 2^102` (and the final `(r+1)*(r+1) < 2^102`) well
/// within `i128` (`≈ 2^127`). Starting `hi` at `c` would overflow `mid*mid` for
/// large `c`; this fixed safe ceiling never does.
const ISQRT_HI: i128 = 1i128 << 51;

/// Integer square root of `c ≥ 0`: the unique `r ≥ 0` with
/// `r*r ≤ c < (r+1)*(r+1)`.
///
/// Overflow-safe by construction: the caller guards `|c| < 2^100`, so `r < 2^50`,
/// and the binary search is capped at [`ISQRT_HI`] = `2^51`, keeping every
/// `mid*mid` (and the final `r*r` / `(r+1)*(r+1)`) far inside `i128`.
///
/// # Panics
///
/// Panics on `c < 0` (the callers only ever pass `c ≥ 0`).
fn isqrt(c: i128) -> i128 {
    assert!(c >= 0, "isqrt requires c >= 0");
    if c < 2 {
        return c; // isqrt(0)=0, isqrt(1)=1
    }
    let (mut lo, mut hi) = (0i128, ISQRT_HI);
    // Invariant: every kept `lo` satisfies `(lo-1)² ≤ c`. Find the largest `r`
    // with `r*r ≤ c`; `hi` converges to it.
    while lo <= hi {
        let mid = lo + (hi - lo) / 2;
        let sq = mid * mid; // safe: mid ≤ 2^51 ⇒ sq ≤ 2^102 < i128::MAX
        match sq.cmp(&c) {
            std::cmp::Ordering::Equal => return mid,
            std::cmp::Ordering::Less => lo = mid + 1,
            std::cmp::Ordering::Greater => hi = mid - 1,
        }
    }
    // `hi` is now the largest value with hi*hi ≤ c.
    hi
}

/// Matches `x*x ⋈ c` / `c ⋈ x*x` for a single `Int` variable `x` and integer
/// constant `c`. Returns `(x_symbol, comparison, c)` (the comparison already
/// oriented as `square ⋈ c`) or `None`.
fn match_square_constraint(
    arena: &TermArena,
    assertion: TermId,
) -> Option<(axeyum_ir::SymbolId, Cmp, i128)> {
    let TermNode::App { op, args } = arena.node(assertion) else {
        return None;
    };

    // `≠` is `not(=)`: peel a single Boolean negation over an `Eq`.
    if matches!(op, Op::BoolNot) {
        let inner = args[0];
        let TermNode::App {
            op: Op::Eq,
            args: eq_args,
        } = arena.node(inner)
        else {
            return None;
        };
        let (a, b) = (eq_args[0], eq_args[1]);
        let (var, c, _square_left) = match_square_vs_const(arena, a, b)?;
        return Some((var, Cmp::Ne, c));
    }

    // Direct comparison / equality. Each binary comparator orients the square
    // relative to the constant; flipping the comparator when the constant is on
    // the left keeps the semantics `square ⋈ c`.
    let (a, b) = (args[0], args[1]);
    let cmp_for = |square_left: bool| -> Option<Cmp> {
        Some(match op {
            Op::Eq => Cmp::Eq,
            Op::IntLt => {
                if square_left {
                    Cmp::Lt
                } else {
                    Cmp::Gt
                }
            }
            Op::IntLe => {
                if square_left {
                    Cmp::Le
                } else {
                    Cmp::Ge
                }
            }
            Op::IntGt => {
                if square_left {
                    Cmp::Gt
                } else {
                    Cmp::Lt
                }
            }
            Op::IntGe => {
                if square_left {
                    Cmp::Ge
                } else {
                    Cmp::Le
                }
            }
            _ => return None,
        })
    };
    // Only proceed for a comparison/equality op.
    if !matches!(op, Op::Eq | Op::IntLt | Op::IntLe | Op::IntGt | Op::IntGe) {
        return None;
    }
    let (var, c, square_left) = match_square_vs_const(arena, a, b)?;
    let cmp = cmp_for(square_left)?;
    Some((var, cmp, c))
}

/// Given the two operands of a binary comparison, identifies which side is `x*x`
/// (a single `Int` variable squared) and which is an integer constant. Returns
/// `(x_symbol, c, square_on_left)` or `None` if the operands are not exactly one
/// square and one constant.
fn match_square_vs_const(
    arena: &TermArena,
    a: TermId,
    b: TermId,
) -> Option<(axeyum_ir::SymbolId, i128, bool)> {
    if let (Some(var), Some(c)) = (match_square(arena, a), int_const(arena, b)) {
        return Some((var, c, true));
    }
    if let (Some(c), Some(var)) = (int_const(arena, a), match_square(arena, b)) {
        return Some((var, c, false));
    }
    None
}

/// Matches `x * x` where both factors are the *same* `Int` variable; returns that
/// variable's symbol, else `None`. Declines `x*y` (distinct vars), `x*x*x` (a
/// nested product, not a leaf variable), constants, and non-`Int` squares.
fn match_square(arena: &TermArena, t: TermId) -> Option<axeyum_ir::SymbolId> {
    let TermNode::App {
        op: Op::IntMul,
        args,
    } = arena.node(t)
    else {
        return None;
    };
    if args.len() != 2 {
        return None;
    }
    let (l, r) = (args[0], args[1]);
    let ls = symbol_of(arena, l)?;
    let rs = symbol_of(arena, r)?;
    // Same variable on both sides — and it is the `IntMul` of two leaf symbols,
    // so `x*x*x` (whose operand is itself a product) and `x*y` both decline.
    if ls == rs { Some(ls) } else { None }
}

/// The symbol of `t` iff `t` is a plain `Int`-sorted variable; else `None`.
fn symbol_of(arena: &TermArena, t: TermId) -> Option<axeyum_ir::SymbolId> {
    match arena.node(t) {
        TermNode::Symbol(s) if arena.sort_of(t) == axeyum_ir::Sort::Int => Some(*s),
        _ => None,
    }
}

/// The integer value of `t` iff `t` is an `IntConst`; else `None`. A wider or
/// non-integer constant (or any non-constant term) declines.
fn int_const(arena: &TermArena, t: TermId) -> Option<i128> {
    match arena.node(t) {
        TermNode::IntConst(n) => Some(*n),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::isqrt;

    #[test]
    fn isqrt_perfect_and_nonperfect() {
        assert_eq!(isqrt(0), 0);
        assert_eq!(isqrt(1), 1);
        assert_eq!(isqrt(2), 1);
        assert_eq!(isqrt(3), 1);
        assert_eq!(isqrt(4), 2);
        assert_eq!(isqrt(8), 2);
        assert_eq!(isqrt(9), 3);
        assert_eq!(isqrt(1_000_000), 1000);
        assert_eq!(isqrt(999_999), 999);
        // Large but within the guard.
        let big = 1i128 << 80;
        let r = isqrt(big);
        assert!(r * r <= big && (r + 1) * (r + 1) > big);
    }
}
