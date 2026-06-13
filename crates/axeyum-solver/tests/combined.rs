//! End-to-end full theory composition (`QF_AUFLIA`): arrays + uninterpreted
//! functions + bounded integers, all reduced to `QF_BV` (ADR-0010/0013/0014).
//!
//! [`check_with_all_theories`] composes the three eager reductions, solves with
//! [`SatBvBackend`], projects the model back through all three, and replays it
//! against the original mixed query — soundness checked without a native oracle.

use std::time::Duration;

use axeyum_ir::{Sort, TermArena, Value, eval};
use axeyum_solver::{
    CheckResult, DEFAULT_INT_WIDTH, SatBvBackend, SolverConfig, check_with_all_theories,
};

fn config() -> SolverConfig {
    SolverConfig::new().with_timeout(Duration::from_secs(30))
}

fn solve(arena: &mut TermArena, assertions: &[axeyum_ir::TermId]) -> CheckResult {
    let mut backend = SatBvBackend::new();
    check_with_all_theories(
        &mut backend,
        arena,
        assertions,
        DEFAULT_INT_WIDTH,
        &config(),
    )
    .expect("supported combined query decides without error")
}

#[test]
fn arrays_functions_and_integers_together_are_sat_and_replay() {
    let mut arena = TermArena::new();

    // Array part: select(store(mem, i, v), i) == v  (a read-after-write, valid).
    let mem = arena.array_var("mem", 4, 8).unwrap();
    let i = arena.bv_var("i", 4).unwrap();
    let v = arena.bv_var("v", 8).unwrap();
    let stored = arena.store(mem, i, v).unwrap();
    let loaded = arena.select(stored, i).unwrap();
    let arr_eq = arena.eq(loaded, v).unwrap();

    // Function part: f(v) == 0xaa  (pins the function at the loaded value).
    let f = arena
        .declare_fun("f", &[Sort::BitVec(8)], Sort::BitVec(8))
        .unwrap();
    let fv = arena.apply(f, &[v]).unwrap();
    let aa = arena.bv_const(8, 0xaa).unwrap();
    let fn_eq = arena.eq(fv, aa).unwrap();

    // Integer part: x + 2 == 5 && x >= 0  (x = 3).
    let x_sym = arena.declare("x", Sort::Int).unwrap();
    let x = arena.var(x_sym);
    let two = arena.int_const(2);
    let five = arena.int_const(5);
    let zero = arena.int_const(0);
    let sum = arena.int_add(x, two).unwrap();
    let int_eq = arena.eq(sum, five).unwrap();
    let int_pos = arena.int_ge(x, zero).unwrap();

    let assertions = [arr_eq, fn_eq, int_eq, int_pos];
    let CheckResult::Sat(model) = solve(&mut arena, &assertions) else {
        panic!("expected a satisfiable combined query");
    };
    // The model carries all theories and replays against the original query.
    assert!(model.function(f).is_some());
    assert_eq!(model.get(x_sym), Some(Value::Int(3)));
    let assignment = model.to_assignment();
    for &a in &assertions {
        assert_eq!(
            eval(&arena, a, &assignment).unwrap(),
            Value::Bool(true),
            "combined model must satisfy every original assertion"
        );
    }
}

#[test]
fn function_congruence_unsat_without_integers_is_exact() {
    // x == y && f(x) != f(y), no integers: arrays/functions are exact
    // reductions, so this is a genuine `unsat`, not `unknown`.
    let mut arena = TermArena::new();
    let f = arena
        .declare_fun("f", &[Sort::BitVec(8)], Sort::BitVec(8))
        .unwrap();
    let x = arena.bv_var("x", 8).unwrap();
    let y = arena.bv_var("y", 8).unwrap();
    let fx = arena.apply(f, &[x]).unwrap();
    let fy = arena.apply(f, &[y]).unwrap();
    let same_in = arena.eq(x, y).unwrap();
    let diff_out = {
        let e = arena.eq(fx, fy).unwrap();
        arena.not(e).unwrap()
    };
    assert_eq!(
        solve(&mut arena, &[same_in, diff_out]),
        CheckResult::Unsat,
        "exact (integer-free) congruence contradiction must be unsat"
    );
}

#[test]
fn contradictory_integers_are_unknown_even_when_mixed() {
    // A valid array fact AND contradictory integer bounds: the integer part has
    // no model in range, so the whole (integer-bearing) query is `unknown`.
    let mut arena = TermArena::new();
    let mem = arena.array_var("mem", 4, 8).unwrap();
    let i = arena.bv_var("i", 4).unwrap();
    let v = arena.bv_var("v", 8).unwrap();
    let stored = arena.store(mem, i, v).unwrap();
    let loaded = arena.select(stored, i).unwrap();
    let arr_eq = arena.eq(loaded, v).unwrap();

    let x_sym = arena.declare("x", Sort::Int).unwrap();
    let x = arena.var(x_sym);
    let zero = arena.int_const(0);
    let gt = arena.int_gt(x, zero).unwrap();
    let lt = arena.int_lt(x, zero).unwrap();

    let result = solve(&mut arena, &[arr_eq, gt, lt]);
    assert!(
        matches!(result, CheckResult::Unknown(_)),
        "bounded integer contradiction must be unknown, got {result:?}"
    );
}

#[test]
fn pure_bitvector_passes_through_all_reductions() {
    // No arrays/functions/integers: every reduction is the identity.
    let mut arena = TermArena::new();
    let x = arena.bv_var("x", 8).unwrap();
    let one = arena.bv_const(8, 1).unwrap();
    let five = arena.bv_const(8, 5).unwrap();
    let sum = arena.bv_add(x, one).unwrap();
    let eq = arena.eq(sum, five).unwrap();
    let CheckResult::Sat(model) = solve(&mut arena, &[eq]) else {
        panic!("expected sat for x + 1 == 5");
    };
    assert_eq!(
        model.get(arena.find_symbol("x").unwrap()),
        Some(Value::Bv { width: 8, value: 4 })
    );
}
