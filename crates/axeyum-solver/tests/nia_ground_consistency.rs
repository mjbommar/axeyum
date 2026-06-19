//! Ground/`∃` consistency for small nonlinear-integer (`QF_NIA`) goals.
//!
//! A bounded integer bit-blast at a single fixed width is fragile for nonlinear
//! goals: a *modular* witness (`x` with `x*x ≡ 4 (mod 2^w)` but `x*x ≠ 4` over the
//! integers) satisfies the blasted query yet fails the exact-integer replay, so the
//! ground goal `x*x = 4 ∧ x > 0` used to report `Unknown` — while the
//! equisatisfiable `∃x. x*x = 4` (skolemized to a fresh constant) found `x = 2` and
//! reported `Sat`. Two answers for one satisfiability is the inconsistency these
//! tests pin closed.
//!
//! The fix is a deterministic small→large **width ladder** in the integer fallback
//! dispatch: a narrow width leaves no room for a wrapping witness, so the genuine
//! small solution is the only model and replays exactly. Every `Sat` here is
//! replay-checked (the solver only returns `Sat` after evaluating the model against
//! the original assertions), and a goal with no integer root (`x*x = 2`) still
//! degrades soundly to `Unknown` — never a wrong `unsat`.

use axeyum_ir::{Sort, TermArena, Value};
use axeyum_solver::{CheckResult, SolverConfig, solve};

/// Build and solve the ground goal `x*x = target` (optionally `∧ x > 0`), returning
/// the result together with the arena and `x` symbol so the caller can replay.
fn solve_ground(target: i128, positive: bool) -> CheckResult {
    let mut arena = TermArena::new();
    let x = arena.int_var("x").unwrap();
    let xx = arena.int_mul(x, x).unwrap();
    let t = arena.int_const(target);
    let eq = arena.eq(xx, t).unwrap();
    let mut assertions = vec![eq];
    if positive {
        let zero = arena.int_const(0);
        assertions.push(arena.int_gt(x, zero).unwrap());
    }
    solve(&mut arena, &assertions, &SolverConfig::default()).expect("solve must not error")
}

/// Independently re-check that a `Sat` model for `x*x = target ∧ x > 0` assigns an
/// integer `x` with `x > 0` and `x*x = target` over the *exact* integers.
fn assert_sat_replays(result: &CheckResult, target: i128) {
    let CheckResult::Sat(model) = result else {
        panic!("expected Sat for x*x = {target} ∧ x > 0, got {result:?}");
    };
    let x = model
        .iter()
        .find_map(|(_, v)| match v {
            Value::Int(n) => Some(n),
            _ => None,
        })
        .expect("model must assign an Int to x");
    assert!(x > 0, "witness x = {x} must satisfy x > 0");
    assert_eq!(x * x, target, "witness x = {x} must satisfy x*x = {target}");
}

#[test]
fn ground_x_squared_eq_4_positive_is_sat() {
    let result = solve_ground(4, true);
    assert_sat_replays(&result, 4); // x = 2
}

#[test]
fn ground_x_squared_eq_9_positive_is_sat() {
    let result = solve_ground(9, true);
    assert_sat_replays(&result, 9); // x = 3
}

#[test]
fn ground_x_squared_eq_25_positive_is_sat() {
    // A wider genuine witness (x = 5); the ladder must climb past the smallest
    // widths (where the constant 25 does not even fit) to decide it.
    let result = solve_ground(25, true);
    assert_sat_replays(&result, 25);
}

#[test]
fn ground_x_squared_eq_4_no_guard_is_sat() {
    // Without the `x > 0` guard the single-width path already found x = 2; the
    // ladder must not regress it.
    let result = solve_ground(4, false);
    let CheckResult::Sat(_) = result else {
        panic!("expected Sat for x*x = 4, got {result:?}");
    };
}

#[test]
fn exists_x_squared_eq_4_is_sat_consistency() {
    // The `∃` form (skolemized to a fresh constant) must still decide Sat — the
    // consistency partner of the ground case above.
    let mut arena = TermArena::new();
    let xsym = arena.declare("x", Sort::Int).unwrap();
    let x = arena.var(xsym);
    let xx = arena.int_mul(x, x).unwrap();
    let four = arena.int_const(4);
    let eq = arena.eq(xx, four).unwrap();
    let ex = arena.exists(xsym, eq).unwrap();
    let result = solve(&mut arena, &[ex], &SolverConfig::default()).expect("solve must not error");
    let CheckResult::Sat(_) = result else {
        panic!("expected Sat for ∃x. x*x = 4, got {result:?}");
    };
}

#[test]
fn ground_x_squared_eq_2_stays_unknown_not_unsat() {
    // `x*x = 2` has no integer root. Proving that `unsat` needs genuine NIA
    // reasoning beyond bounded blasting, so the sound outcome is `Unknown` —
    // crucially **not** a wrong `Unsat`.
    let result = solve_ground(2, true);
    assert!(
        matches!(result, CheckResult::Unknown(_)),
        "x*x = 2 ∧ x > 0 must be Unknown (sound), never Unsat/Sat, got {result:?}"
    );
}
