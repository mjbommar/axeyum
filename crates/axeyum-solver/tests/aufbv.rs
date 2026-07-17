//! End-to-end `QF_AUFBV`: composed array + uninterpreted-function elimination
//! (ADR-0010 + ADR-0013).
//!
//! These tests exercise the theory-composition entry point
//! [`check_with_arrays_and_functions`]: a query mixing `select`/`store` with
//! uninterpreted-function applications is reduced to `QF_BV` by running array
//! elimination then function elimination, solved by [`SatBvBackend`], and its
//! model is projected back through both passes and **replayed against the
//! original query** with the ground evaluator — soundness checked without a
//! native oracle.
#![cfg(feature = "full")]

use axeyum_ir::{Sort, TermArena, Value, eval};
use axeyum_solver::{
    CheckResult, SatBvBackend, SolverConfig, SolverError, check_with_arrays_and_functions,
};

fn solve_qf_aufbv(arena: &mut TermArena, assertions: &[axeyum_ir::TermId]) -> CheckResult {
    let mut backend = SatBvBackend::new();
    check_with_arrays_and_functions(&mut backend, arena, assertions, &SolverConfig::default())
        .expect("supported `QF_AUFBV` query decides without error")
}

#[test]
fn function_of_equal_memory_loads_is_congruent() {
    // mem[i] == v && f(v) == 0xaa && f(mem[i]) != 0xaa is unsatisfiable:
    // mem[i] == v forces f(mem[i]) == f(v) == 0xaa by congruence.
    let mut arena = TermArena::new();
    let f = arena
        .declare_fun("f", &[Sort::BitVec(8)], Sort::BitVec(8))
        .unwrap();
    let mem = arena.array_var("mem", 4, 8).unwrap();
    let i = arena.bv_var("i", 4).unwrap();
    let v = arena.bv_var("v", 8).unwrap();
    let load = arena.select(mem, i).unwrap();
    let aa = arena.bv_const(8, 0xaa).unwrap();

    let load_is_v = arena.eq(load, v).unwrap();
    let fv = arena.apply(f, &[v]).unwrap();
    let fv_is_aa = arena.eq(fv, aa).unwrap();
    let f_load = arena.apply(f, &[load]).unwrap();
    let f_load_ne_aa = {
        let e = arena.eq(f_load, aa).unwrap();
        arena.not(e).unwrap()
    };

    assert_eq!(
        solve_qf_aufbv(&mut arena, &[load_is_v, fv_is_aa, f_load_ne_aa]),
        CheckResult::Unsat
    );
}

#[test]
fn function_over_stored_value_is_satisfiable_and_replays() {
    // After mem' = store(mem, i, v), require f(select(mem', i)) == 0x77.
    // select(mem', i) == v, so this pins f(v) == 0x77 — satisfiable; the
    // projected model (array + function) must replay against the original query.
    let mut arena = TermArena::new();
    let f = arena
        .declare_fun("f", &[Sort::BitVec(8)], Sort::BitVec(8))
        .unwrap();
    let mem = arena.array_var("mem", 4, 8).unwrap();
    let i = arena.bv_var("i", 4).unwrap();
    let v = arena.bv_var("v", 8).unwrap();
    let stored = arena.store(mem, i, v).unwrap();
    let loaded = arena.select(stored, i).unwrap();
    let applied = arena.apply(f, &[loaded]).unwrap();
    let target = arena.bv_const(8, 0x77).unwrap();
    let goal = arena.eq(applied, target).unwrap();

    let CheckResult::Sat(model) = solve_qf_aufbv(&mut arena, &[goal]) else {
        panic!("expected a satisfiable stored-then-applied query");
    };
    // The returned model carries both the array and the function; the original
    // (array + application) query replays to true under it.
    assert!(model.function(f).is_some());
    let assignment = model.to_assignment();
    assert_eq!(eval(&arena, goal, &assignment).unwrap(), Value::Bool(true));
}

#[test]
fn distinct_function_outputs_over_distinct_addresses_is_satisfiable() {
    // mem[i] != mem[j] is satisfiable, and so is requiring f to map the two
    // loads to two fixed distinct constants.
    let mut arena = TermArena::new();
    let f = arena
        .declare_fun("f", &[Sort::BitVec(8)], Sort::BitVec(8))
        .unwrap();
    let mem = arena.array_var("mem", 4, 8).unwrap();
    let i = arena.bv_var("i", 4).unwrap();
    let j = arena.bv_var("j", 4).unwrap();
    let load_i = arena.select(mem, i).unwrap();
    let load_j = arena.select(mem, j).unwrap();
    let f_i = arena.apply(f, &[load_i]).unwrap();
    let f_j = arena.apply(f, &[load_j]).unwrap();
    let c1 = arena.bv_const(8, 0x11).unwrap();
    let c2 = arena.bv_const(8, 0x22).unwrap();
    let g1 = arena.eq(f_i, c1).unwrap();
    let g2 = arena.eq(f_j, c2).unwrap();

    let CheckResult::Sat(_) = solve_qf_aufbv(&mut arena, &[g1, g2]) else {
        panic!("expected satisfiable distinct function outputs");
    };
}

#[test]
fn arith_sorted_uf_over_aufbv_path_is_graceful_never_wrong() {
    // The early arith-UF `Unknown` bail was relaxed to attempt-and-replay, but the
    // `QF_AUFBV` entry point targets the bit-vector fragment: an `Int`-sorted UF is
    // outside it, and the pure-Rust BV backend rejects the `Int` term at
    // `backend.check` (before any model projection) with a clean
    // `SolverError::Unsupported` — never a crash and never a wrong sat/unsat
    // verdict. (The auto-dispatcher routes `Int`-sorted UF to the euf/combined
    // paths, not here; this test pins the aufbv path's graceful rejection.)
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
    let one = arena.int_const(1);
    let one2 = arena.int_const(1);
    let fn_eq = arena.eq(fx, one).unwrap();
    let x_eq = arena.eq(xv, one2).unwrap();

    let mut backend = SatBvBackend::new();
    let result = check_with_arrays_and_functions(
        &mut backend,
        &mut arena,
        &[arr_eq, fn_eq, x_eq],
        &SolverConfig::default(),
    );
    // Graceful: either a clean `Unsupported` (the Int term is outside the BV
    // fragment, rejected at the backend) or a sound `Unknown`/replay-checked `Sat`.
    // It must NEVER be a wrong `Unsat`, and a `Sat`, if any, must replay.
    match result {
        Ok(CheckResult::Unsat) => panic!("f(x) = 1 ∧ x = 1 is satisfiable — never a wrong Unsat"),
        Ok(CheckResult::Sat(model)) => {
            let assignment = model.to_assignment();
            for &a in &[arr_eq, fn_eq, x_eq] {
                assert_eq!(
                    eval(&arena, a, &assignment).unwrap(),
                    Value::Bool(true),
                    "any emitted aufbv arith-UF Sat must replay"
                );
            }
        }
        Ok(CheckResult::Unknown(_)) | Err(SolverError::Unsupported(_)) => {}
        Err(other) => panic!("unexpected error from the aufbv arith-UF path: {other:?}"),
    }
}
