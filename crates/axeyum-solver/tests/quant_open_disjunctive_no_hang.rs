//! Regression: an OPEN disjunctive integer universal `∀x:Int.(x≤y ∨ x≥y+1)` is
//! declined by the FM int-closed pass (symbolic `y`) and reaches the quantifier
//! search, whose instantiation generates ever-deeper ground terms. It MUST degrade
//! to a graceful `Unknown` within the budget — never hang (the "never hang" rule).

use std::time::Duration;

use axeyum_ir::{Sort, TermArena};
use axeyum_solver::{CheckResult, SolverConfig, solve};

#[test]
fn open_disjunctive_universal_does_not_hang() {
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
    // The test RETURNING at all (within the suite's own bound) proves termination;
    // the result must be sound — never a wrong Unsat (the universal is valid, so it
    // is Sat or a graceful Unknown).
    if let Ok(CheckResult::Unsat) = solve(&mut a, &[forall], &cfg) {
        panic!("valid universal must NOT be reported Unsat");
    }
}
