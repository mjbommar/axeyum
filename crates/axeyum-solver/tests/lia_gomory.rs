//! Gomory fractional cuts for `QF_LIA` (P2.4).
//!
//! Branch-and-bound over the exact-rational simplex decides bounded integer
//! systems, but STALLS (`Unknown`, grinding to its node budget) on systems whose
//! real relaxation is feasible yet whose integer hull is EMPTY over unbounded
//! variables. A bounded round of sound Gomory fractional cuts closes such cases
//! to `unsat` while never removing an integer point — so it can decide a case
//! B&B leaves `unknown`, and it can NEVER turn an integer-feasible system into a
//! wrong `unsat`.
//!
//! The cardinal rule: never a wrong sat/unsat. Every `sat` here is replayed
//! through the evaluator (the trust anchor); every `unsat` rests on cuts valid
//! for every integer point. A case the slice cannot decide is `unknown`, never a
//! guess.

use axeyum_ir::{Sort, TermArena, TermId, Value, eval};
use axeyum_solver::{CheckResult, check_with_lia_simplex};

fn int_var(arena: &mut TermArena, name: &str) -> TermId {
    let sym = arena.declare(name, Sort::Int).unwrap();
    arena.var(sym)
}

/// Replays a model against the assertions, asserting every one is satisfied.
fn assert_replays(arena: &TermArena, assertions: &[TermId], model: &axeyum_solver::Model) {
    let assignment = model.to_assignment();
    for &c in assertions {
        assert_eq!(
            eval(arena, c, &assignment).unwrap(),
            Value::Bool(true),
            "sat model must satisfy every assertion on replay"
        );
    }
}

#[test]
fn lp_feasible_no_integer_point_is_unsat_via_cuts() {
    // 2x + 2y <= 1  AND  2x + 2y >= 1   ⟺   x + y = 1/2.
    //
    // HAND PROOF (no integer point): for integers x, y, `x + y` is an integer, so
    // `x + y = 1/2` is impossible. Equivalently, `2x + 2y` is an EVEN integer, and
    // no even integer equals 1; so `2x + 2y <= 1` forces `2x + 2y <= 0` while
    // `2x + 2y >= 1` forces `2x + 2y >= 2` — contradiction. UNSAT.
    //
    // The REAL relaxation is feasible (e.g. x = 1/2, y = 0), so bounded
    // bit-blasting cannot decide it, and plain branch-and-bound keeps finding
    // shifted fractional vertices on the line and exhausts its node budget
    // (left `unknown`). The Gomory cut round decides it `unsat`.
    let mut a = TermArena::new();
    let x = int_var(&mut a, "x");
    let y = int_var(&mut a, "y");
    let two = a.int_const(2);
    let one = a.int_const(1);
    let tx = a.int_mul(two, x).unwrap();
    let ty = a.int_mul(two, y).unwrap();
    let s = a.int_add(tx, ty).unwrap();
    let le = a.int_le(s, one).unwrap();
    let ge = a.int_ge(s, one).unwrap();

    assert!(
        matches!(
            check_with_lia_simplex(&a, &[le, ge]).unwrap(),
            CheckResult::Unsat
        ),
        "x + y = 1/2 has no integer solution; expected Unsat"
    );
}

#[test]
fn three_x_minus_three_y_in_band_is_unsat_via_cuts() {
    // 3x - 3y >= 1  AND  3x - 3y <= 2.
    //
    // HAND PROOF: `3x - 3y = 3(x - y)` is a multiple of 3 for any integers x, y,
    // and the only multiple of 3 in the closed band [1, 2] is... none (1 and 2 are
    // not multiples of 3). So there is no integer point. The real relaxation is
    // feasible (e.g. x = 1/3, y = 0 gives 1), so B&B alone stalls. UNSAT.
    let mut a = TermArena::new();
    let x = int_var(&mut a, "x");
    let y = int_var(&mut a, "y");
    let three = a.int_const(3);
    let one = a.int_const(1);
    let two = a.int_const(2);
    let tx = a.int_mul(three, x).unwrap();
    let ty = a.int_mul(three, y).unwrap();
    let d = a.int_sub(tx, ty).unwrap();
    let ge = a.int_ge(d, one).unwrap();
    let le = a.int_le(d, two).unwrap();

    assert!(
        matches!(
            check_with_lia_simplex(&a, &[ge, le]).unwrap(),
            CheckResult::Unsat
        ),
        "3(x - y) cannot lie strictly inside [1, 2]; expected Unsat"
    );
}

#[test]
fn soundness_negative_integer_feasible_must_not_be_unsat() {
    // 2x >= 1  AND  2x <= 3.  The integer point x = 1 satisfies both (2*1 = 2 ∈
    // [1, 3]). The LP relaxation vertex is fractional (x = 1/2 or 3/2), so this
    // EXERCISES the cut/branch machinery — and the slice must NOT report `unsat`.
    // We assert it is `Sat` with a replay-checked witness (a sound non-`Unsat`).
    let mut a = TermArena::new();
    let x_sym = a.declare("x", Sort::Int).unwrap();
    let x = a.var(x_sym);
    let two = a.int_const(2);
    let one = a.int_const(1);
    let three = a.int_const(3);
    let tx = a.int_mul(two, x).unwrap();
    let lo = a.int_ge(tx, one).unwrap();
    let hi = a.int_le(tx, three).unwrap();
    let asserts = [lo, hi];

    match check_with_lia_simplex(&a, &asserts).unwrap() {
        CheckResult::Sat(model) => {
            assert_replays(&a, &asserts, &model);
            // The only integer in [1, 3] with 2x even is x = 1.
            assert_eq!(model.get(x_sym), Some(Value::Int(1)));
        }
        CheckResult::Unknown(_) => {
            // A sound non-`Unsat` is acceptable; the cardinal rule is only that
            // an integer-feasible system is NEVER reported `unsat`.
        }
        CheckResult::Unsat => {
            panic!("SOUNDNESS VIOLATION: integer-feasible 2x∈[1,3] reported Unsat")
        }
    }
}

#[test]
fn soundness_negative_larger_feasible_system() {
    // x + 2y = 4  AND  x - y = 1.  Solution x = 2, y = 1 (both integers).
    // A second integer-feasible witness check: must be Sat (not Unsat).
    let mut a = TermArena::new();
    let x = int_var(&mut a, "x");
    let y = int_var(&mut a, "y");
    let two = a.int_const(2);
    let four = a.int_const(4);
    let one = a.int_const(1);
    let ty = a.int_mul(two, y).unwrap();
    let sum = a.int_add(x, ty).unwrap();
    let c1 = a.eq(sum, four).unwrap();
    let diff = a.int_sub(x, y).unwrap();
    let c2 = a.eq(diff, one).unwrap();
    let asserts = [c1, c2];

    match check_with_lia_simplex(&a, &asserts).unwrap() {
        CheckResult::Sat(model) => assert_replays(&a, &asserts, &model),
        CheckResult::Unsat => {
            panic!("SOUNDNESS VIOLATION: integer-feasible system reported Unsat")
        }
        CheckResult::Unknown(_) => {} // sound, just less precise
    }
}

#[test]
fn declined_case_is_never_a_wrong_verdict() {
    // A system with non-integer coefficients in the LIA sense is uncommon, but a
    // genuinely satisfiable larger system where the slice may decline should yield
    // a SOUND result (Sat with replay, or Unknown) — never a wrong Unsat.
    //
    // 5x + 7y = 12 has the integer solution x = 1, y = 1. Whether the Gomory
    // round or B&B closes it, the verdict must be a sound Sat (or Unknown), never
    // Unsat.
    let mut a = TermArena::new();
    let x = int_var(&mut a, "x");
    let y = int_var(&mut a, "y");
    let five = a.int_const(5);
    let seven = a.int_const(7);
    let twelve = a.int_const(12);
    let fx = a.int_mul(five, x).unwrap();
    let sy = a.int_mul(seven, y).unwrap();
    let sum = a.int_add(fx, sy).unwrap();
    let c = a.eq(sum, twelve).unwrap();
    let asserts = [c];

    match check_with_lia_simplex(&a, &asserts).unwrap() {
        CheckResult::Sat(model) => assert_replays(&a, &asserts, &model),
        CheckResult::Unknown(_) => {}
        CheckResult::Unsat => panic!("SOUNDNESS VIOLATION: 5x+7y=12 (x=y=1) reported Unsat"),
    }
}
