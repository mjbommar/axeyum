//! Regression for a QF-LIA branch-and-bound hang and its completeness fix.
//!
//! `∀x:Int.(x≤y ∨ x≥y+1)` is VALID over the integers (no integer lies strictly
//! between consecutive integers `y` and `y+1`). The valid-universal pass decides it
//! by checking `¬body[x:=c]` = `c>y ∧ c<y+1` UNSAT. That QF subquery is real-feasible
//! (c=y+0.5) but integer-infeasible; without integer tightening, branch-and-bound
//! grinds toward its node budget (~minutes, ignoring the timeout). With strict-
//! inequality tightening it is immediately LP-infeasible ⇒ instant UNSAT, so the
//! universal decides **Sat** — fast and correct, never a hang.

use std::time::Duration;

use axeyum_ir::{Sort, TermArena};
use axeyum_solver::{CheckResult, SolverConfig, check_with_lia_simplex, solve};

#[test]
fn qf_strict_between_consecutive_is_unsat_fast() {
    // c > y ∧ c < y+1 over the integers — UNSAT, decided instantly by integer
    // tightening (c−y ≥ 1 ∧ c−y ≤ 0 is LP-infeasible), no branch-and-bound grind.
    let mut a = TermArena::new();
    let c = a.declare("c", Sort::Int).unwrap();
    let y = a.declare("y", Sort::Int).unwrap();
    let (cv, yv) = (a.var(c), a.var(y));
    let one = a.int_const(1);
    let c_gt_y = a.int_gt(cv, yv).unwrap();
    let yp1 = a.int_add(yv, one).unwrap();
    let c_lt_yp1 = a.int_lt(cv, yp1).unwrap();
    assert!(
        matches!(
            check_with_lia_simplex(&a, &[c_gt_y, c_lt_yp1]),
            Ok(CheckResult::Unsat)
        ),
        "c > y ∧ c < y+1 must be UNSAT over the integers (no integer strictly between)"
    );
}

#[test]
fn open_disjunctive_universal_is_valid_and_fast() {
    let mut a = TermArena::new();
    let x = a.declare("x", Sort::Int).unwrap();
    let y = a.declare("y", Sort::Int).unwrap();
    let xv = a.var(x);
    let yv = a.var(y);
    let one = a.int_const(1);
    let x_le_y = a.int_le(xv, yv).unwrap();
    let yp1 = a.int_add(yv, one).unwrap();
    let x_ge_yp1 = a.int_ge(xv, yp1).unwrap();
    let body = a.or(x_le_y, x_ge_yp1).unwrap();
    let forall = a.forall(x, body).unwrap();

    let cfg = SolverConfig {
        timeout: Some(Duration::from_secs(2)),
        ..SolverConfig::default()
    };
    // The universal is valid, so it must be Sat — the test returning at all (well
    // within the budget) proves the former hang is gone; the verdict proves the
    // completeness fix. Never a wrong Unsat.
    match solve(&mut a, &[forall], &cfg) {
        Ok(CheckResult::Sat(_)) => {}
        Ok(CheckResult::Unsat) => panic!("valid universal must NOT be reported Unsat"),
        // A graceful Unknown would still prove no-hang, but with the tightening the
        // valid-universal pass should now decide it Sat.
        other => panic!("expected Sat for the valid universal, got {other:?}"),
    }
}

#[test]
fn gcd_coefficient_strict_inequalities_decide_unsat() {
    use axeyum_ir::Sort;
    // 2x < 2y ∧ 2y < 2x+2  ⟺  x<y ∧ y≤x  → UNSAT. Needs gcd-aware tightening
    // (2x-2y < 0 ⟺ 2x-2y ≤ -2, not the loose ≤ -1) to be LP-infeasible immediately.
    let mut a = TermArena::new();
    let x = a.declare("x", Sort::Int).unwrap();
    let y = a.declare("y", Sort::Int).unwrap();
    let (xv, yv) = (a.var(x), a.var(y));
    let two = a.int_const(2);
    let x2 = a.int_mul(two, xv).unwrap();
    let y2 = a.int_mul(two, yv).unwrap();
    let c1 = a.int_lt(x2, y2).unwrap(); // 2x < 2y
    let x2p2 = a.int_add(x2, two).unwrap();
    let c2 = a.int_lt(y2, x2p2).unwrap(); // 2y < 2x+2
    assert!(
        matches!(
            check_with_lia_simplex(&a, &[c1, c2]),
            Ok(CheckResult::Unsat)
        ),
        "2x<2y ∧ 2y<2x+2 must be UNSAT (gcd-2 tightening)"
    );
}

#[test]
fn gcd_three_strict_inequalities_decide_unsat() {
    use axeyum_ir::Sort;
    // 3x > 3y ∧ 3x < 3y+3  ⟺  x≥y+1 ∧ x≤y  → UNSAT (gcd-3 tightening).
    let mut a = TermArena::new();
    let x = a.declare("x", Sort::Int).unwrap();
    let y = a.declare("y", Sort::Int).unwrap();
    let (xv, yv) = (a.var(x), a.var(y));
    let three = a.int_const(3);
    let x3 = a.int_mul(three, xv).unwrap();
    let y3 = a.int_mul(three, yv).unwrap();
    let c1 = a.int_gt(x3, y3).unwrap(); // 3x > 3y
    let y3p3 = a.int_add(y3, three).unwrap();
    let c2 = a.int_lt(x3, y3p3).unwrap(); // 3x < 3y+3
    assert!(
        matches!(
            check_with_lia_simplex(&a, &[c1, c2]),
            Ok(CheckResult::Unsat)
        ),
        "3x>3y ∧ 3x<3y+3 must be UNSAT (gcd-3 tightening)"
    );
}
