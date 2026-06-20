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
