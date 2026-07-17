//! Exact, bounded NIA decision for a single-variable integer **quadratic
//! constraint** `a·x² + b·x + c ⋈ 0` — the generalization of the single-square
//! decider (`x*x ⋈ c`). Correctness is everything: every `Sat` here is
//! replay-checked against the *original* assertion, every `Unsat` is exact by the
//! discriminant / convexity analysis, and every shape outside the exact
//! single-variable degree-2 polynomial pattern must be **declined** (left to the
//! existing NIA dispatch) — never mis-decided.
#![cfg(feature = "full")]

use axeyum_ir::{Sort, TermArena, TermId, Value};
use axeyum_solver::{CheckResult, SolverConfig, solve};

/// Solve a single assertion built by `build`, returning the result, arena, and
/// the assertion term so a `Sat` model can be independently replayed.
fn solve_one(build: impl FnOnce(&mut TermArena) -> TermId) -> (CheckResult, TermArena, TermId) {
    let mut arena = TermArena::new();
    let assertion = build(&mut arena);
    let result =
        solve(&mut arena, &[assertion], &SolverConfig::default()).expect("solve must not error");
    (result, arena, assertion)
}

/// Re-check a `Sat` independently: the model must satisfy the original assertion
/// on replay (the strongest possible soundness witness).
fn assert_sat_replays(result: &CheckResult, arena: &TermArena, assertion: TermId) {
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

/// Build `a·x² + b·x + c` as an `Int` term over a fresh variable `x`.
fn quad(arena: &mut TermArena, a: i128, b: i128, c: i128) -> (TermId, TermId) {
    let x = arena.declare("x", Sort::Int).unwrap();
    let xv = arena.var(x);
    let xx = arena.int_mul(xv, xv).unwrap();
    let ac = arena.int_const(a);
    let ax2 = arena.int_mul(ac, xx).unwrap();
    let bc = arena.int_const(b);
    let bx = arena.int_mul(bc, xv).unwrap();
    let cc = arena.int_const(c);
    let s1 = arena.int_add(ax2, bx).unwrap();
    let poly = arena.int_add(s1, cc).unwrap();
    (poly, xv)
}

/// `a·x² + b·x + c ⋈ 0` via the chosen comparator builder.
fn quad_cmp_zero(
    arena: &mut TermArena,
    a: i128,
    b: i128,
    c: i128,
    cmp: fn(&mut TermArena, TermId, TermId) -> TermId,
) -> TermId {
    let (poly, _x) = quad(arena, a, b, c);
    let zero = arena.int_const(0);
    cmp(arena, poly, zero)
}

fn eq(a: &mut TermArena, l: TermId, r: TermId) -> TermId {
    a.eq(l, r).unwrap()
}
fn ne(a: &mut TermArena, l: TermId, r: TermId) -> TermId {
    let e = a.eq(l, r).unwrap();
    a.not(e).unwrap()
}
fn lt(a: &mut TermArena, l: TermId, r: TermId) -> TermId {
    a.int_lt(l, r).unwrap()
}
fn le(a: &mut TermArena, l: TermId, r: TermId) -> TermId {
    a.int_le(l, r).unwrap()
}
fn gt(a: &mut TermArena, l: TermId, r: TermId) -> TermId {
    a.int_gt(l, r).unwrap()
}
fn ge(a: &mut TermArena, l: TermId, r: TermId) -> TermId {
    a.int_ge(l, r).unwrap()
}

// --- EQUALITY: the discriminant / perfect-square path -------------------------

#[test]
fn quad_x2_minus_5x_plus_6_eq0_is_sat() {
    // x² − 5x + 6 = 0 ⇒ roots 2, 3 ⇒ Sat.
    let (result, arena, t) = solve_one(|a| quad_cmp_zero(a, 1, -5, 6, eq));
    assert_sat_replays(&result, &arena, t);
}

#[test]
fn quad_x2_plus_1_eq0_is_unsat() {
    // x² + 1 = 0 ⇒ D = −4 < 0 ⇒ Unsat.
    let (result, _a, _t) = solve_one(|a| quad_cmp_zero(a, 1, 0, 1, eq));
    assert!(matches!(result, CheckResult::Unsat), "got {result:?}");
}

#[test]
fn quad_x2_minus_2_eq0_is_unsat() {
    // x² − 2 = 0 ⇒ D = 8, not a perfect square ⇒ Unsat.
    let (result, _a, _t) = solve_one(|a| quad_cmp_zero(a, 1, 0, -2, eq));
    assert!(matches!(result, CheckResult::Unsat), "got {result:?}");
}

#[test]
fn quad_x2_minus_4x_plus_4_eq0_is_sat_double_root() {
    // x² − 4x + 4 = 0 ⇒ (x−2)² ⇒ double root x = 2 ⇒ Sat.
    let (result, arena, t) = solve_one(|a| quad_cmp_zero(a, 1, -4, 4, eq));
    assert_sat_replays(&result, &arena, t);
}

#[test]
fn quad_2x2_minus_4_eq0_is_unsat() {
    // 2x² − 4 = 0 ⇒ x² = 2 ⇒ D = 32, not a perfect square ⇒ Unsat.
    let (result, _a, _t) = solve_one(|a| quad_cmp_zero(a, 2, 0, -4, eq));
    assert!(matches!(result, CheckResult::Unsat), "got {result:?}");
}

#[test]
fn quad_perfect_square_disc_but_noninteger_root_is_unsat() {
    // 4x² − 1 = 0 ⇒ D = 16 (perfect square, s = 4), roots = (±4)/8 = ±1/2 — not
    // integers ⇒ Unsat. Guards the divisibility-by-2a check.
    let (result, _a, _t) = solve_one(|a| quad_cmp_zero(a, 4, 0, -1, eq));
    assert!(matches!(result, CheckResult::Unsat), "got {result:?}");
}

#[test]
fn quad_negative_leading_eq0_is_sat() {
    // −x² + 5x − 6 = 0 ⇒ same roots 2,3 (a < 0 reduction) ⇒ Sat.
    let (result, arena, t) = solve_one(|a| quad_cmp_zero(a, -1, 5, -6, eq));
    assert_sat_replays(&result, &arena, t);
}

// --- DISEQUALITY: always Sat for degree 2 -------------------------------------

#[test]
fn quad_ne0_always_sat() {
    // x² − 5x + 6 ≠ 0 ⇒ Sat (pick a non-root, e.g. x = 0 ⇒ 6 ≠ 0).
    let (result, arena, t) = solve_one(|a| quad_cmp_zero(a, 1, -5, 6, ne));
    assert_sat_replays(&result, &arena, t);
}

// --- INEQUALITIES: the soundness-critical interval test -----------------------

#[test]
fn quad_x2_minus_3x_plus_2_lt0_is_unsat() {
    // x² − 3x + 2 < 0 ⇒ roots 1, 2 ⇒ open interval (1, 2) has NO integer ⇒ Unsat.
    let (result, _a, _t) = solve_one(|a| quad_cmp_zero(a, 1, -3, 2, lt));
    assert!(matches!(result, CheckResult::Unsat), "got {result:?}");
}

#[test]
fn quad_x2_minus_2x_lt0_is_sat() {
    // x² − 2x < 0 ⇒ roots 0, 2 ⇒ x = 1 ∈ (0, 2) ⇒ Sat.
    let (result, arena, t) = solve_one(|a| quad_cmp_zero(a, 1, -2, 0, lt));
    assert_sat_replays(&result, &arena, t);
}

#[test]
fn quad_x2_minus_4_lt0_is_sat() {
    // x² − 4 < 0 ⇒ (−2, 2) ⇒ x ∈ {−1, 0, 1} ⇒ Sat.
    let (result, arena, t) = solve_one(|a| quad_cmp_zero(a, 1, 0, -4, lt));
    assert_sat_replays(&result, &arena, t);
}

#[test]
fn quad_x2_minus_3x_plus_2_le0_is_sat_at_roots() {
    // x² − 3x + 2 ≤ 0 ⇒ closed [1, 2] ⇒ x = 1 (or 2) ⇒ Sat (boundary now included).
    let (result, arena, t) = solve_one(|a| quad_cmp_zero(a, 1, -3, 2, le));
    assert_sat_replays(&result, &arena, t);
}

#[test]
fn quad_x2_plus_1_le0_is_unsat() {
    // x² + 1 ≤ 0 ⇒ minimum 1 > 0 ⇒ Unsat (D < 0, a > 0).
    let (result, _a, _t) = solve_one(|a| quad_cmp_zero(a, 1, 0, 1, le));
    assert!(matches!(result, CheckResult::Unsat), "got {result:?}");
}

#[test]
fn quad_x2_minus_4x_plus_4_lt0_is_unsat_double_root() {
    // (x−2)² < 0 ⇒ never (double root, min 0, strict) ⇒ Unsat.
    let (result, _a, _t) = solve_one(|a| quad_cmp_zero(a, 1, -4, 4, lt));
    assert!(matches!(result, CheckResult::Unsat), "got {result:?}");
}

#[test]
fn quad_x2_minus_4x_plus_4_le0_is_sat_double_root() {
    // (x−2)² ≤ 0 ⇒ only at x = 2 (vertex integral) ⇒ Sat.
    let (result, arena, t) = solve_one(|a| quad_cmp_zero(a, 1, -4, 4, le));
    assert_sat_replays(&result, &arena, t);
}

#[test]
fn quad_x2_gt0_is_sat() {
    // x² > 0 ⇒ x = 1 ⇒ Sat.
    let (result, arena, t) = solve_one(|a| quad_cmp_zero(a, 1, 0, 0, gt));
    assert_sat_replays(&result, &arena, t);
}

#[test]
fn quad_x2_plus_x_plus_1_gt0_always_sat() {
    // x² + x + 1 > 0 ⇒ D = −3 < 0, a > 0 ⇒ always positive ⇒ Sat.
    let (result, arena, t) = solve_one(|a| quad_cmp_zero(a, 1, 1, 1, gt));
    assert_sat_replays(&result, &arena, t);
}

#[test]
fn quad_x2_ge0_always_sat() {
    // x² ≥ 0 ⇒ always ⇒ Sat.
    let (result, arena, t) = solve_one(|a| quad_cmp_zero(a, 1, 0, 0, ge));
    assert_sat_replays(&result, &arena, t);
}

#[test]
fn quad_neg_x2_plus_2x_gt0_is_sat() {
    // −x² + 2x > 0 ⇒ a < 0 ⇒ between roots 0, 2 ⇒ x = 1 ⇒ Sat.
    let (result, arena, t) = solve_one(|a| quad_cmp_zero(a, -1, 2, 0, gt));
    assert_sat_replays(&result, &arena, t);
}

#[test]
fn quad_neg_x2_minus_1_ge0_is_unsat() {
    // −x² − 1 ≥ 0 ⇒ −(x² + 1) ≥ 0 ⇒ x² + 1 ≤ 0 ⇒ never ⇒ Unsat.
    let (result, _a, _t) = solve_one(|a| quad_cmp_zero(a, -1, 0, -1, ge));
    assert!(matches!(result, CheckResult::Unsat), "got {result:?}");
}

#[test]
fn quad_neg_x2_lt0_is_sat() {
    // −x² < 0 ⇒ x ≠ 0 ⇒ x = 1 ⇒ Sat.
    let (result, arena, t) = solve_one(|a| quad_cmp_zero(a, -1, 0, 0, lt));
    assert_sat_replays(&result, &arena, t);
}

// --- backwards-compatibility: the original `x*x ⋈ c` subcase still decides ----

#[test]
fn legacy_x2_eq_2_still_unsat() {
    // x*x = 2 in the original shape (square on the left, constant on the right).
    let (result, _a, _t) = solve_one(|a| {
        let x = a.declare("x", Sort::Int).unwrap();
        let xv = a.var(x);
        let xx = a.int_mul(xv, xv).unwrap();
        let two = a.int_const(2);
        a.eq(xx, two).unwrap()
    });
    assert!(matches!(result, CheckResult::Unsat), "got {result:?}");
}

#[test]
fn legacy_const_lt_square_still_sat() {
    // 2 < x*x ⇒ Sat (constant on the left orientation).
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

#[test]
fn two_variable_quadratic_not_misdecided() {
    // x² + y = 2 (two variables) — must decline; satisfiable (x=0,y=2) ⇒ not Unsat.
    let mut arena = TermArena::new();
    let x = arena.int_var("x").unwrap();
    let y = arena.int_var("y").unwrap();
    let xx = arena.int_mul(x, x).unwrap();
    let sum = arena.int_add(xx, y).unwrap();
    let two = arena.int_const(2);
    let assertion = arena.eq(sum, two).unwrap();
    let result =
        solve(&mut arena, &[assertion], &SolverConfig::default()).expect("solve must not error");
    assert!(
        !matches!(result, CheckResult::Unsat),
        "x²+y = 2 is satisfiable; must decline, got {result:?}"
    );
}

#[test]
fn cube_not_misdecided_sat() {
    // x³ = 2 — degree 3, must decline; no integer root ⇒ must never be Sat.
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
        "x³ = 2 has no integer root; must never be Sat, got {result:?}"
    );
}

#[test]
fn x2_times_x_not_misdecided_sat() {
    // x²·x (written as a product whose factor is itself a square) — degree 3,
    // decline. Same constraint as the cube; must never be Sat.
    let mut arena = TermArena::new();
    let x = arena.int_var("x").unwrap();
    let xx = arena.int_mul(x, x).unwrap();
    let cube = arena.int_mul(xx, x).unwrap();
    let two = arena.int_const(2);
    let assertion = arena.eq(cube, two).unwrap();
    let result =
        solve(&mut arena, &[assertion], &SolverConfig::default()).expect("solve must not error");
    assert!(
        !matches!(result, CheckResult::Sat(_)),
        "x²·x = 2 has no integer root; must never be Sat, got {result:?}"
    );
}

#[test]
fn real_quadratic_not_misdecided_unsat() {
    // Real x, x² = 2 — out of scope (NRA √2). Decline; satisfiable ⇒ not Unsat.
    let mut arena = TermArena::new();
    let x = arena.real_var("x").unwrap();
    let xx = arena.real_mul(x, x).unwrap();
    let two = arena.real_const(axeyum_ir::Rational::integer(2));
    let assertion = arena.eq(xx, two).unwrap();
    let result =
        solve(&mut arena, &[assertion], &SolverConfig::default()).expect("solve must not error");
    assert!(
        !matches!(result, CheckResult::Unsat),
        "Real x² = 2 is satisfiable (x=√2); must not be Unsat, got {result:?}"
    );
}

#[test]
fn two_assertions_on_x_not_misdecided_sat() {
    // x² − 2 = 0 ∧ x > 0 (two assertions) — must decline; no real x satisfies it,
    // so the result must never be a wrong Sat (Unsat or Unknown is sound).
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
        "x²=2 ∧ x>0 has no solution; must never be Sat, got {result:?}"
    );
}

#[test]
fn linear_only_not_misdecided() {
    // 2x + 3 = 0 — degree 1 (a = 0), declines to exact LIA. The query is Unsat
    // over the integers (x = −3/2 ∉ ℤ); we only require no wrong *Sat* here, since
    // LIA may decide it Unsat soundly.
    let mut arena = TermArena::new();
    let x = arena.int_var("x").unwrap();
    let two = arena.int_const(2);
    let twox = arena.int_mul(two, x).unwrap();
    let three = arena.int_const(3);
    let sum = arena.int_add(twox, three).unwrap();
    let zero = arena.int_const(0);
    let assertion = arena.eq(sum, zero).unwrap();
    let result =
        solve(&mut arena, &[assertion], &SolverConfig::default()).expect("solve must not error");
    assert!(
        !matches!(result, CheckResult::Sat(_)),
        "2x+3 = 0 has no integer solution; must never be Sat, got {result:?}"
    );
}
