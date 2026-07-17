//! End-to-end full theory composition (`QF_AUFLIA`): arrays + uninterpreted
//! functions + bounded integers, all reduced to `QF_BV` (ADR-0010/0013/0014).
//!
//! [`check_with_all_theories`] composes the three eager reductions, solves with
//! [`SatBvBackend`], projects the model back through all three, and replays it
//! against the original mixed query — soundness checked without a native oracle.
#![cfg(feature = "full")]

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

// ---------------------------------------------------------------------------
// Arithmetic-sorted (Int) uninterpreted functions routed through the combined
// (UF + array + Int) path now decide `Sat` with a replay-verified model — the
// early arith-UF `Unknown` bail was relaxed to attempt-and-replay. SOUNDNESS:
// every returned `Sat` is replayed through the ground evaluator against the
// original assertions; a projection that cannot be reconstructed (a nested
// arith-sorted application) still declines to a sound `Unknown`.
// ---------------------------------------------------------------------------

#[test]
fn arith_sorted_uf_with_array_is_sat_and_replays() {
    // An `Int -> Int` uninterpreted function mixed with an array fact so the
    // query routes through `check_with_all_theories` (UF + array + Int):
    //   select(store(mem, i, v), i) == v   (valid read-after-write)
    //   f(x) == 7  AND  x == 3             (arith-sorted UF, pinned at x = 3)
    // Satisfiable; the projected Int-keyed UF interpretation must replay.
    let mut arena = TermArena::new();

    let mem = arena.array_var("mem", 4, 8).unwrap();
    let idx = arena.bv_var("i", 4).unwrap();
    let val = arena.bv_var("v", 8).unwrap();
    let stored = arena.store(mem, idx, val).unwrap();
    let loaded = arena.select(stored, idx).unwrap();
    let arr_eq = arena.eq(loaded, val).unwrap();

    let fun = arena.declare_fun("f", &[Sort::Int], Sort::Int).unwrap();
    let x_sym = arena.declare("x", Sort::Int).unwrap();
    let xv = arena.var(x_sym);
    let fx = arena.apply(fun, &[xv]).unwrap();
    let seven = arena.int_const(7);
    let three = arena.int_const(3);
    let fn_eq = arena.eq(fx, seven).unwrap();
    let x_eq = arena.eq(xv, three).unwrap();

    let assertions = [arr_eq, fn_eq, x_eq];
    let CheckResult::Sat(model) = solve(&mut arena, &assertions) else {
        panic!("expected SAT for the arith-sorted UF + array query");
    };
    assert!(
        model.function(fun).is_some(),
        "the projected model must carry the arith-sorted UF interpretation"
    );
    assert_eq!(model.get(x_sym), Some(Value::Int(3)));
    let assignment = model.to_assignment();
    for &a in &assertions {
        assert_eq!(
            eval(&arena, a, &assignment).unwrap(),
            Value::Bool(true),
            "the projected arith-UF model must replay against every original assertion"
        );
    }
}

#[test]
fn arith_sorted_uf_congruence_with_array_is_never_wrong_sat() {
    // A genuine `Int -> Int` congruence contradiction mixed with an array:
    //   select(store(mem, i, v), i) == v   (valid)
    //   x == y  AND  f(x) != f(y)          (unsatisfiable by congruence)
    // The combined path bit-blasts the Int sorts at a bounded width, so it
    // conservatively reports the bit-vector `unsat` as `Unknown` (a model might
    // exist outside the width) rather than `Unsat` — the existing soundness
    // contract. The relaxed guard does not change this (UNSAT/Unknown both return
    // before model projection): the only forbidden outcome is a (wrong) `Sat`.
    let mut arena = TermArena::new();
    let mem = arena.array_var("mem", 4, 8).unwrap();
    let idx = arena.bv_var("i", 4).unwrap();
    let val = arena.bv_var("v", 8).unwrap();
    let stored = arena.store(mem, idx, val).unwrap();
    let loaded = arena.select(stored, idx).unwrap();
    let arr_eq = arena.eq(loaded, val).unwrap();

    let fun = arena.declare_fun("f", &[Sort::Int], Sort::Int).unwrap();
    let x_sym = arena.declare("x", Sort::Int).unwrap();
    let y_sym = arena.declare("y", Sort::Int).unwrap();
    let xv = arena.var(x_sym);
    let yv = arena.var(y_sym);
    let fx = arena.apply(fun, &[xv]).unwrap();
    let fy = arena.apply(fun, &[yv]).unwrap();
    let same_in = arena.eq(xv, yv).unwrap();
    let diff_out = {
        let neq = arena.eq(fx, fy).unwrap();
        arena.not(neq).unwrap()
    };
    let result = solve(&mut arena, &[arr_eq, same_in, diff_out]);
    assert!(
        !matches!(result, CheckResult::Sat(_)),
        "x = y ∧ f(x) ≠ f(y) is unsatisfiable — never a (wrong) Sat; got {result:?}"
    );
}

#[test]
fn nested_arith_sorted_uf_declines_to_unknown_never_sat() {
    // A NESTED arith-sorted application — g(f(x), 0) — whose inner fresh result
    // symbol is unassigned in the base model cannot be projected. Mixed with an
    // array so it routes through the combined path. The instance is satisfiable,
    // so the only sound outcomes are `Sat` (if projectable) or `Unknown`; it
    // must NEVER be a wrong `Unsat` and must NEVER crash.
    let mut arena = TermArena::new();
    let mem = arena.array_var("mem", 4, 8).unwrap();
    let idx = arena.bv_var("i", 4).unwrap();
    let val = arena.bv_var("v", 8).unwrap();
    let stored = arena.store(mem, idx, val).unwrap();
    let loaded = arena.select(stored, idx).unwrap();
    let arr_eq = arena.eq(loaded, val).unwrap();

    let fun = arena.declare_fun("f", &[Sort::Int], Sort::Int).unwrap();
    let gun = arena
        .declare_fun("g", &[Sort::Int, Sort::Int], Sort::Int)
        .unwrap();
    let x_sym = arena.declare("x", Sort::Int).unwrap();
    let xv = arena.var(x_sym);
    let fx = arena.apply(fun, &[xv]).unwrap();
    let zero = arena.int_const(0);
    let gfx = arena.apply(gun, &[fx, zero]).unwrap();
    let zero2 = arena.int_const(0);
    let atom = arena.int_ge(gfx, zero2).unwrap(); // g(f(x), 0) >= 0  (satisfiable)

    let result = solve(&mut arena, &[arr_eq, atom]);
    assert!(
        !matches!(result, CheckResult::Unsat),
        "g(f(x), 0) >= 0 is satisfiable — never a wrong Unsat; got {result:?}"
    );
    // If it decides `Sat`, the model MUST replay (the soundness anchor); a
    // projectable nested case is fine, an un-projectable one is a sound Unknown.
    if let CheckResult::Sat(model) = &result {
        let assignment = model.to_assignment();
        assert_eq!(
            eval(&arena, atom, &assignment).unwrap(),
            Value::Bool(true),
            "any emitted Sat must replay the nested arith-UF assertion"
        );
    }
}
