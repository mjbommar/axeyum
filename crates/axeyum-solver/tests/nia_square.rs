//! Exact, bounded NIA decision for a single-variable integer **square
//! constraint** `x*x ⋈ c` (constant `c`).
//!
//! Closes the hunt-flagged gap `int x*x = 2` → **Unsat** (2 is not a perfect
//! square), which the bounded bit-blast width ladder and the real relaxation only
//! ever report as `Unknown`. Correctness is everything: every `Sat` here is
//! replay-checked against the *original* assertion, every `Unsat` is exact by the
//! perfect-square / sign analysis, and every shape outside the exact single-square
//! pattern must be **declined** (left to the existing NIA dispatch) — never
//! mis-decided.

use axeyum_ir::{Sort, TermArena, Value};
use axeyum_solver::{CheckResult, SolverConfig, solve};

/// Solve a single assertion built by `build`, returning the result and the arena
/// so a `Sat` model can be independently replayed.
fn solve_one(
    build: impl FnOnce(&mut TermArena) -> axeyum_ir::TermId,
) -> (CheckResult, TermArena, axeyum_ir::TermId) {
    let mut arena = TermArena::new();
    let assertion = build(&mut arena);
    let result =
        solve(&mut arena, &[assertion], &SolverConfig::default()).expect("solve must not error");
    (result, arena, assertion)
}

/// `x*x ⋈ c` for the integer comparison chosen by `cmp` (square on the left).
fn square_cmp_const(
    arena: &mut TermArena,
    c: i128,
    cmp: fn(&mut TermArena, axeyum_ir::TermId, axeyum_ir::TermId) -> axeyum_ir::TermId,
) -> axeyum_ir::TermId {
    let x = arena.declare("x", Sort::Int).unwrap();
    let xv = arena.var(x);
    let xx = arena.int_mul(xv, xv).unwrap();
    let k = arena.int_const(c);
    cmp(arena, xx, k)
}

fn eq(a: &mut TermArena, l: axeyum_ir::TermId, r: axeyum_ir::TermId) -> axeyum_ir::TermId {
    a.eq(l, r).unwrap()
}
fn ne(a: &mut TermArena, l: axeyum_ir::TermId, r: axeyum_ir::TermId) -> axeyum_ir::TermId {
    let e = a.eq(l, r).unwrap();
    a.not(e).unwrap()
}
fn lt(a: &mut TermArena, l: axeyum_ir::TermId, r: axeyum_ir::TermId) -> axeyum_ir::TermId {
    a.int_lt(l, r).unwrap()
}
fn le(a: &mut TermArena, l: axeyum_ir::TermId, r: axeyum_ir::TermId) -> axeyum_ir::TermId {
    a.int_le(l, r).unwrap()
}
fn gt(a: &mut TermArena, l: axeyum_ir::TermId, r: axeyum_ir::TermId) -> axeyum_ir::TermId {
    a.int_gt(l, r).unwrap()
}
fn ge(a: &mut TermArena, l: axeyum_ir::TermId, r: axeyum_ir::TermId) -> axeyum_ir::TermId {
    a.int_ge(l, r).unwrap()
}

/// Re-check a `Sat` independently: the model must assign integer `x` and the
/// original assertion must evaluate to `true` under it (the strongest possible
/// soundness witness).
fn assert_sat_replays(result: &CheckResult, arena: &TermArena, assertion: axeyum_ir::TermId) {
    let CheckResult::Sat(model) = result else {
        panic!("expected Sat, got {result:?}");
    };
    let assignment = model.to_assignment();
    assert!(
        matches!(
            axeyum_ir::eval(arena, assertion, &assignment),
            Ok(Value::Bool(true))
        ),
        "Sat model must satisfy the original assertion on replay"
    );
}

// --- DECIDES: equality (the headline gap) -------------------------------------

#[test]
fn square_eq_2_is_unsat() {
    // 2 is not a perfect square ⇒ Unsat. THE hunt-flagged gap.
    let (result, _a, _t) = solve_one(|a| square_cmp_const(a, 2, eq));
    assert!(
        matches!(result, CheckResult::Unsat),
        "x*x = 2 must be Unsat, got {result:?}"
    );
}

#[test]
fn square_eq_3_is_unsat() {
    let (result, _a, _t) = solve_one(|a| square_cmp_const(a, 3, eq));
    assert!(matches!(result, CheckResult::Unsat), "got {result:?}");
}

#[test]
fn square_eq_4_is_sat() {
    let (result, arena, t) = solve_one(|a| square_cmp_const(a, 4, eq));
    assert_sat_replays(&result, &arena, t); // x = 2 (or -2)
}

#[test]
fn square_eq_0_is_sat() {
    let (result, arena, t) = solve_one(|a| square_cmp_const(a, 0, eq));
    assert_sat_replays(&result, &arena, t); // x = 0
}

#[test]
fn square_eq_neg1_is_unsat() {
    let (result, _a, _t) = solve_one(|a| square_cmp_const(a, -1, eq));
    assert!(matches!(result, CheckResult::Unsat), "got {result:?}");
}

#[test]
fn square_eq_1000000_is_sat() {
    let (result, arena, t) = solve_one(|a| square_cmp_const(a, 1_000_000, eq));
    assert_sat_replays(&result, &arena, t); // x = 1000
}

#[test]
fn square_eq_large_perfect_square_is_sat() {
    // 12345^2 = 152399025 — well within the overflow guard.
    let (result, arena, t) = solve_one(|a| square_cmp_const(a, 12345i128 * 12345, eq));
    assert_sat_replays(&result, &arena, t);
}

#[test]
fn square_eq_large_nonsquare_is_unsat() {
    let (result, _a, _t) = solve_one(|a| square_cmp_const(a, 152_399_025 + 1, eq));
    assert!(matches!(result, CheckResult::Unsat), "got {result:?}");
}

// --- DECIDES: inequalities ----------------------------------------------------

#[test]
fn square_ne_2_is_sat() {
    let (result, arena, t) = solve_one(|a| square_cmp_const(a, 2, ne));
    assert_sat_replays(&result, &arena, t); // x = 0: 0 ≠ 2
}

#[test]
fn square_ne_0_is_sat() {
    let (result, arena, t) = solve_one(|a| square_cmp_const(a, 0, ne));
    assert_sat_replays(&result, &arena, t); // x = 1: 1 ≠ 0
}

#[test]
fn square_lt_2_is_sat() {
    let (result, arena, t) = solve_one(|a| square_cmp_const(a, 2, lt));
    assert_sat_replays(&result, &arena, t); // x = 0: 0 < 2
}

#[test]
fn square_lt_0_is_unsat() {
    let (result, _a, _t) = solve_one(|a| square_cmp_const(a, 0, lt));
    assert!(matches!(result, CheckResult::Unsat), "got {result:?}");
}

#[test]
fn square_lt_neg5_is_unsat() {
    let (result, _a, _t) = solve_one(|a| square_cmp_const(a, -5, lt));
    assert!(matches!(result, CheckResult::Unsat), "got {result:?}");
}

#[test]
fn square_le_0_is_sat() {
    let (result, arena, t) = solve_one(|a| square_cmp_const(a, 0, le));
    assert_sat_replays(&result, &arena, t); // x = 0
}

#[test]
fn square_le_neg1_is_unsat() {
    let (result, _a, _t) = solve_one(|a| square_cmp_const(a, -1, le));
    assert!(matches!(result, CheckResult::Unsat), "got {result:?}");
}

#[test]
fn square_gt_2_is_sat() {
    let (result, arena, t) = solve_one(|a| square_cmp_const(a, 2, gt));
    assert_sat_replays(&result, &arena, t); // x = 2: 4 > 2
}

#[test]
fn square_gt_neg1_is_sat() {
    let (result, arena, t) = solve_one(|a| square_cmp_const(a, -1, gt));
    assert_sat_replays(&result, &arena, t); // x = 0: 0 > -1
}

#[test]
fn square_ge_neg5_is_sat() {
    let (result, arena, t) = solve_one(|a| square_cmp_const(a, -5, ge));
    assert_sat_replays(&result, &arena, t);
}

#[test]
fn square_ge_100_is_sat() {
    let (result, arena, t) = solve_one(|a| square_cmp_const(a, 100, ge));
    assert_sat_replays(&result, &arena, t); // x = 11: 121 ≥ 100 (or x = 10)
}

// --- DECIDES: constant on the LEFT (`c ⋈ x*x`) --------------------------------

#[test]
fn const_eq_square_2_is_unsat() {
    // `2 = x*x` — square on the right, must decide the same as `x*x = 2`.
    let (result, _a, _t) = solve_one(|a| {
        let x = a.declare("x", Sort::Int).unwrap();
        let xv = a.var(x);
        let xx = a.int_mul(xv, xv).unwrap();
        let two = a.int_const(2);
        a.eq(two, xx).unwrap()
    });
    assert!(matches!(result, CheckResult::Unsat), "got {result:?}");
}

#[test]
fn const_lt_square_2_is_sat() {
    // `2 < x*x` ⟺ `x*x > 2` ⇒ Sat (x = 2).
    let (result, arena, t) = solve_one(|a| {
        let x = a.declare("x", Sort::Int).unwrap();
        let xv = a.var(x);
        let xx = a.int_mul(xv, xv).unwrap();
        let two = a.int_const(2);
        a.int_lt(two, xx).unwrap()
    });
    assert_sat_replays(&result, &arena, t);
}

// --- MUST DECLINE: outside the exact pattern (never mis-decide) ----------------

/// `x*y` (two distinct variables) — NOT a square. The pass must decline; the
/// query is satisfiable (e.g. x=y=2 ⇒ 4) so the dispatch must NOT return Unsat.
#[test]
fn two_variables_product_not_misdecided_unsat() {
    let mut arena = TermArena::new();
    let x = arena.int_var("x").unwrap();
    let y = arena.int_var("y").unwrap();
    let xy = arena.int_mul(x, y).unwrap();
    let two = arena.int_const(2);
    let assertion = arena.eq(xy, two).unwrap(); // x*y = 2 is SAT (x=1,y=2)
    let result =
        solve(&mut arena, &[assertion], &SolverConfig::default()).expect("solve must not error");
    assert!(
        !matches!(result, CheckResult::Unsat),
        "x*y = 2 is satisfiable; the square pass must decline, got {result:?}"
    );
}

/// `x*x*x = 2` (a cube) — must not be decided by the square pass. The cube has no
/// integer root, but the square pass must DECLINE; the result must not be a wrong
/// Sat (and an exact NIA refutation may report Unsat or Unknown — we only forbid
/// a wrong Sat here).
#[test]
fn cube_not_misdecided_sat() {
    let mut arena = TermArena::new();
    let x = arena.int_var("x").unwrap();
    let xx = arena.int_mul(x, x).unwrap();
    let xxx = arena.int_mul(xx, x).unwrap();
    let two = arena.int_const(2);
    let assertion = arena.eq(xxx, two).unwrap();
    let result =
        solve(&mut arena, &[assertion], &SolverConfig::default()).expect("solve must not error");
    assert!(
        !matches!(result, CheckResult::Sat(_)),
        "x*x*x = 2 has no integer root; must never be Sat, got {result:?}"
    );
}

/// `x*x + x = 2` (extra term) — the square pass must decline. The query IS
/// satisfiable (x = 1 ⇒ 1 + 1 = 2), so it must not be wrongly Unsat.
#[test]
fn square_plus_var_not_misdecided_unsat() {
    let mut arena = TermArena::new();
    let x = arena.int_var("x").unwrap();
    let xx = arena.int_mul(x, x).unwrap();
    let sum = arena.int_add(xx, x).unwrap();
    let two = arena.int_const(2);
    let assertion = arena.eq(sum, two).unwrap();
    let result =
        solve(&mut arena, &[assertion], &SolverConfig::default()).expect("solve must not error");
    assert!(
        !matches!(result, CheckResult::Unsat),
        "x*x + x = 2 is satisfiable (x=1); must not be Unsat, got {result:?}"
    );
}

/// `x*x = y` (rhs not constant) — must decline; satisfiable (x=2,y=4) so not Unsat.
#[test]
fn square_eq_var_not_misdecided_unsat() {
    let mut arena = TermArena::new();
    let x = arena.int_var("x").unwrap();
    let y = arena.int_var("y").unwrap();
    let xx = arena.int_mul(x, x).unwrap();
    let assertion = arena.eq(xx, y).unwrap();
    let result =
        solve(&mut arena, &[assertion], &SolverConfig::default()).expect("solve must not error");
    assert!(
        !matches!(result, CheckResult::Unsat),
        "x*x = y is satisfiable; must not be Unsat, got {result:?}"
    );
}

/// `x*x = 2 ∧ x > 0` (two assertions) — the square pass must DECLINE (other
/// constraints on x present), leaving the result to the existing dispatch. The
/// outcome must never be a wrong verdict; in particular it must not regress the
/// pre-existing `Unknown` to a *Sat* (no real x satisfies it). It is sound either
/// as Unsat or Unknown, but must NOT be Sat.
#[test]
fn square_with_extra_assertion_not_sat() {
    let mut arena = TermArena::new();
    let x = arena.int_var("x").unwrap();
    let xx = arena.int_mul(x, x).unwrap();
    let two = arena.int_const(2);
    let eq2 = arena.eq(xx, two).unwrap();
    let zero = arena.int_const(0);
    let pos = arena.int_gt(x, zero).unwrap();
    let result =
        solve(&mut arena, &[eq2, pos], &SolverConfig::default()).expect("solve must not error");
    assert!(
        !matches!(result, CheckResult::Sat(_)),
        "x*x = 2 ∧ x > 0 has no solution; must never be Sat, got {result:?}"
    );
}

/// Real square (`x:Real, x*x = 2`) — out of scope (the NRA √ case). The square
/// pass is Int-only and must decline; the query is genuinely satisfiable
/// (x = √2), so it must NOT be wrongly Unsat.
#[test]
fn real_square_not_misdecided_unsat() {
    let mut arena = TermArena::new();
    let x = arena.real_var("x").unwrap();
    let xx = arena.real_mul(x, x).unwrap();
    let two = arena.real_const(axeyum_ir::Rational::integer(2));
    let assertion = arena.eq(xx, two).unwrap();
    let result =
        solve(&mut arena, &[assertion], &SolverConfig::default()).expect("solve must not error");
    assert!(
        !matches!(result, CheckResult::Unsat),
        "Real x*x = 2 is satisfiable (x=√2); must not be Unsat, got {result:?}"
    );
}
