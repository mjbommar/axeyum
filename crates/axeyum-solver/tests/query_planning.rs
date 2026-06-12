//! Query-planning checks through the Z3 oracle.
//!
//! Sliced plans are allowed to submit fewer terms, but a `sat` model is
//! accepted only after replay against the original query.

#![cfg(feature = "z3")]

use axeyum_ir::{Sort, TermArena};
use axeyum_query::Query;
use axeyum_solver::{CheckResult, SolverBackend, SolverConfig, Z3Backend};

#[test]
fn sliced_sat_model_replays_original_query_contract() {
    let mut arena = TermArena::new();
    let x_sym = arena.declare("x", Sort::BitVec(8)).unwrap();
    let y_sym = arena.declare("y", Sort::BitVec(8)).unwrap();
    let x = arena.var(x_sym);
    let y = arena.var(y_sym);
    let one = arena.bv_const(8, 1).unwrap();
    let x_is_one = arena.eq(x, one).unwrap();
    let y_tautology = arena.eq(y, y).unwrap();
    let mut builder = Query::builder(&arena);
    builder.assert(x_is_one).unwrap();
    builder.assert(y_tautology).unwrap();
    let query = builder.build();
    let plan = query.slice_for_targets(&arena, &[x]);

    assert!(plan.is_sliced());
    assert_eq!(plan.dropped_terms().len(), 1);

    let terms = plan.solver_terms().collect::<Vec<_>>();
    let CheckResult::Sat(model) = Z3Backend::new()
        .check(&arena, &terms, &SolverConfig::default())
        .unwrap()
    else {
        panic!("sliced query should be sat");
    };
    plan.replay_original(&arena, &model.to_assignment())
        .expect("model completion plus identity projection replays original query");
}

#[test]
fn sliced_unsat_subset_is_unsat_for_full_query() {
    let mut arena = TermArena::new();
    let x = arena.bv_var("x", 8).unwrap();
    let y = arena.bv_var("y", 8).unwrap();
    let zero = arena.bv_const(8, 0).unwrap();
    let one = arena.bv_const(8, 1).unwrap();
    let x_below_zero = arena.bv_ult(x, zero).unwrap();
    let y_is_one = arena.eq(y, one).unwrap();
    let mut builder = Query::builder(&arena);
    builder.assert(x_below_zero).unwrap();
    builder.assert(y_is_one).unwrap();
    let query = builder.build();
    let plan = query.slice_for_targets(&arena, &[x]);
    let planned_terms = plan.solver_terms().collect::<Vec<_>>();

    assert!(plan.is_sliced());
    assert_eq!(
        Z3Backend::new()
            .check(&arena, &planned_terms, &SolverConfig::default())
            .unwrap(),
        CheckResult::Unsat
    );
    assert_eq!(
        Z3Backend::new()
            .check_query(&arena, &query, &SolverConfig::default())
            .unwrap(),
        CheckResult::Unsat
    );
}
