//! Nonlinear-integer (`QF_NIA` / `NIA`) commutativity must terminate fast.
//!
//! The ground disequality `a*b ≠ b*a` (and its universal forms `∀x. x*k = k*x`,
//! `∀x∀y. x*y = y*x`) reduces to a hard multiplier-equivalence sub-check. The
//! integer fallback used to grind a wide bit-blast width ladder over that
//! multiplier mountain *without honouring the configured timeout*, so the call
//! spun indefinitely.
//!
//! The fix is twofold: the real relaxation canonicalizes commutative
//! `mul`/`add` operands, so `a*b` and `b*a` relax to the **same** real term and
//! the disequality becomes `p ≠ p` ≡ `false` — refuted as `Unsat` *before* the
//! ladder runs; and the ladder itself is trimmed and now checks a wall-clock
//! deadline before each width, so even a goal it cannot refute terminates with a
//! graceful `Unknown` instead of hanging.
//!
//! Each test running to completion under the suite *is* the termination proof.

use std::time::Duration;

use axeyum_ir::{Sort, TermArena};
use axeyum_solver::{CheckResult, SolverConfig, solve};

/// `a*b ≠ b*a` over the integers is unsatisfiable (commutativity is a tautology),
/// and the fix decides it *fast* via the canonicalizing real relaxation.
#[test]
fn ground_mul_commutativity_disequality_is_unsat() {
    let mut a = TermArena::new();
    let u = a.int_var("u").unwrap();
    let v = a.int_var("v").unwrap();
    let uv = a.int_mul(u, v).unwrap();
    let vu = a.int_mul(v, u).unwrap();
    let eq = a.eq(uv, vu).unwrap();
    let neq = a.not(eq).unwrap();
    let result = solve(&mut a, &[neq], &SolverConfig::default()).expect("solve must not error");
    assert!(
        matches!(result, CheckResult::Unsat),
        "a*b != b*a must be Unsat, got {result:?}"
    );
}

/// The same ground goal with a tight timeout must **return** (it cannot hang); the
/// fast relaxation refutes it as `Unsat`, but `Unknown` would also be acceptable —
/// the point is termination within the budget.
#[test]
fn ground_mul_commutativity_honors_timeout() {
    let mut a = TermArena::new();
    let u = a.int_var("u").unwrap();
    let v = a.int_var("v").unwrap();
    let uv = a.int_mul(u, v).unwrap();
    let vu = a.int_mul(v, u).unwrap();
    let eq = a.eq(uv, vu).unwrap();
    let neq = a.not(eq).unwrap();
    let c = SolverConfig {
        timeout: Some(Duration::from_millis(500)),
        ..SolverConfig::default()
    };
    let result = solve(&mut a, &[neq], &c).expect("solve must not error");
    assert!(
        matches!(result, CheckResult::Unsat | CheckResult::Unknown(_)),
        "a*b != b*a with a timeout must return Unsat or Unknown (never hang), got {result:?}"
    );
}

/// The universal `∀x. x*k = k*x` is a valid universal (commutativity), so the
/// assertion is satisfiable — decided via the valid-universal pass whose sub-check
/// refutes `¬(c*k = k*c)` through the relaxation.
#[test]
fn forall_mul_commutativity_with_constant_is_sat() {
    let mut a = TermArena::new();
    let xsym = a.declare("x", Sort::Int).unwrap();
    let x = a.var(xsym);
    let k = a.int_var("k").unwrap();
    let xk = a.int_mul(x, k).unwrap();
    let kx = a.int_mul(k, x).unwrap();
    let body = a.eq(xk, kx).unwrap();
    let all = a.forall(xsym, body).unwrap();
    let result = solve(&mut a, &[all], &SolverConfig::default()).expect("solve must not error");
    assert!(
        matches!(result, CheckResult::Sat(_)),
        "∀x. x*k = k*x must be Sat (valid universal), got {result:?}"
    );
}

/// Regression: the small-witness nonlinear case `x*x = 4 ∧ x > 0` must still be
/// decided `Sat` (x = 2) — the trimmed ladder keeps the dense narrow range where
/// small witnesses replay.
#[test]
fn ground_x_squared_eq_4_positive_still_sat() {
    let mut a = TermArena::new();
    let x = a.int_var("x").unwrap();
    let xx = a.int_mul(x, x).unwrap();
    let four = a.int_const(4);
    let eq = a.eq(xx, four).unwrap();
    let zero = a.int_const(0);
    let pos = a.int_gt(x, zero).unwrap();
    let result = solve(&mut a, &[eq, pos], &SolverConfig::default()).expect("solve must not error");
    assert!(
        matches!(result, CheckResult::Sat(_)),
        "x*x = 4 ∧ x > 0 must still be Sat, got {result:?}"
    );
}
