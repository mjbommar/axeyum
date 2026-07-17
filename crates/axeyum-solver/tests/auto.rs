//! The unified dispatcher [`check_auto`]: one front door routing each query to
//! the right engine (bit-blasting composition vs lazy-SMT for reals).
#![cfg(feature = "full")]

use std::time::Duration;

use axeyum_ir::{Sort, TermArena, Value, eval};
use axeyum_solver::{CheckResult, SolverConfig, check_auto, unsat_core};

fn config() -> SolverConfig {
    SolverConfig::new().with_timeout(Duration::from_secs(30))
}

fn solve(arena: &mut TermArena, assertions: &[axeyum_ir::TermId]) -> CheckResult {
    check_auto(arena, assertions, &config()).expect("supported query decides without error")
}

#[test]
fn routes_pure_bitvector_to_bit_blasting() {
    let mut arena = TermArena::new();
    let x = arena.bv_var("x", 8).unwrap();
    let one = arena.bv_const(8, 1).unwrap();
    let five = arena.bv_const(8, 5).unwrap();
    let sum = arena.bv_add(x, one).unwrap();
    let eq = arena.eq(sum, five).unwrap();
    assert!(matches!(solve(&mut arena, &[eq]), CheckResult::Sat(_)));
}

#[test]
fn routes_mixed_arrays_functions_integers_to_composition() {
    // mem[i] == v && f(v) == 0xaa && x + 2 == 5 (x:Int) — the full QF_AUFLIA
    // composition, dispatched automatically.
    let mut arena = TermArena::new();
    let mem = arena.array_var("mem", 4, 8).unwrap();
    let i = arena.bv_var("i", 4).unwrap();
    let v = arena.bv_var("v", 8).unwrap();
    let stored = arena.store(mem, i, v).unwrap();
    let loaded = arena.select(stored, i).unwrap();
    let arr_eq = arena.eq(loaded, v).unwrap();

    let f = arena
        .declare_fun("f", &[Sort::BitVec(8)], Sort::BitVec(8))
        .unwrap();
    let fv = arena.apply(f, &[v]).unwrap();
    let aa = arena.bv_const(8, 0xaa).unwrap();
    let fn_eq = arena.eq(fv, aa).unwrap();

    let x_sym = arena.declare("x", Sort::Int).unwrap();
    let x = arena.var(x_sym);
    let two = arena.int_const(2);
    let five = arena.int_const(5);
    let sum = arena.int_add(x, two).unwrap();
    let int_eq = arena.eq(sum, five).unwrap();

    assert!(matches!(
        solve(&mut arena, &[arr_eq, fn_eq, int_eq]),
        CheckResult::Sat(_)
    ));
}

#[test]
fn routes_real_disjunction_to_lazy_smt() {
    // A disjunction of real constraints — handled by the DPLL(T) path.
    let mut arena = TermArena::new();
    let x_sym = arena.declare("x", Sort::Real).unwrap();
    let x = arena.var(x_sym);
    let zero = arena.real_ratio(0, 1);
    let ten = arena.real_ratio(10, 1);
    let lt = arena.real_lt(x, zero).unwrap();
    let gt = arena.real_gt(x, ten).unwrap();
    let disj = arena.or(lt, gt).unwrap();
    let CheckResult::Sat(model) = solve(&mut arena, &[disj]) else {
        panic!("expected sat");
    };
    let assignment = model.to_assignment();
    assert_eq!(eval(&arena, disj, &assignment).unwrap(), Value::Bool(true));
}

#[test]
fn real_and_bitvector_combined_in_one_formula() {
    // Reals and bit-vectors coupled through Boolean structure in one assertion:
    // `r > 0 and b = 1`. Reals share no sort with bit-vectors, so the lazy-SMT
    // loop combines them completely (the bit-blaster handles `b`, LRA handles
    // `r`, coupled only propositionally).
    let mut arena = TermArena::new();
    let r_sym = arena.declare("r", Sort::Real).unwrap();
    let r = arena.var(r_sym);
    let zero = arena.real_ratio(0, 1);
    let r_pos = arena.real_gt(r, zero).unwrap();

    let b = arena.bv_var("b", 8).unwrap();
    let bc = arena.bv_const(8, 1).unwrap();
    let b_eq = arena.eq(b, bc).unwrap();
    let both = arena.and(r_pos, b_eq).unwrap();

    let CheckResult::Sat(model) = solve(&mut arena, &[both]) else {
        panic!("expected sat for the combined real + bit-vector formula");
    };
    let assignment = model.to_assignment();
    assert_eq!(eval(&arena, both, &assignment).unwrap(), Value::Bool(true));
}

#[test]
fn disjoint_real_and_bitvector_assertions_combine() {
    // Separate assertions over disjoint variables (r real, b bit-vector): the
    // disjoint base case of theory combination decides them together.
    let mut arena = TermArena::new();
    let r_sym = arena.declare("r", Sort::Real).unwrap();
    let r = arena.var(r_sym);
    let zero = arena.real_ratio(0, 1);
    let r_pos = arena.real_gt(r, zero).unwrap();

    let b = arena.bv_var("b", 8).unwrap();
    let bc = arena.bv_const(8, 1).unwrap();
    let b_eq = arena.eq(b, bc).unwrap();

    let CheckResult::Sat(model) = solve(&mut arena, &[r_pos, b_eq]) else {
        panic!("expected sat for disjoint real + bit-vector parts");
    };
    let assignment = model.to_assignment();
    assert_eq!(eval(&arena, r_pos, &assignment).unwrap(), Value::Bool(true));
    assert_eq!(eval(&arena, b_eq, &assignment).unwrap(), Value::Bool(true));
}

#[test]
fn disjoint_combination_is_unsat_when_one_part_is() {
    // r > 0 ∧ r < 0 (real, unsat) plus a fine bit-vector part → overall unsat.
    let mut arena = TermArena::new();
    let r_sym = arena.declare("r", Sort::Real).unwrap();
    let r = arena.var(r_sym);
    let zero = arena.real_ratio(0, 1);
    let r_pos = arena.real_gt(r, zero).unwrap();
    let r_neg = arena.real_lt(r, zero).unwrap();
    let b = arena.bv_var("b", 4).unwrap();
    let bc = arena.bv_const(4, 1).unwrap();
    let b_eq = arena.eq(b, bc).unwrap();
    assert_eq!(solve(&mut arena, &[r_pos, r_neg, b_eq]), CheckResult::Unsat);
}

#[test]
fn real_and_bitvector_sharing_a_bool_combine() {
    // (p or r>0) and (not p or b=1): the Boolean p links the real and
    // bit-vector parts; the lazy-SMT loop case-splits p and decides both.
    let mut arena = TermArena::new();
    let p_sym = arena.declare("p", Sort::Bool).unwrap();
    let p = arena.var(p_sym);
    let r_sym = arena.declare("r", Sort::Real).unwrap();
    let r = arena.var(r_sym);
    let zero = arena.real_ratio(0, 1);
    let r_pos = arena.real_gt(r, zero).unwrap();
    let b = arena.bv_var("b", 4).unwrap();
    let bc = arena.bv_const(4, 1).unwrap();
    let b_eq = arena.eq(b, bc).unwrap();
    let c1 = arena.or(p, r_pos).unwrap();
    let not_p = arena.not(p).unwrap();
    let c2 = arena.or(not_p, b_eq).unwrap();

    let CheckResult::Sat(model) = solve(&mut arena, &[c1, c2]) else {
        panic!("expected sat for the Boolean-linked real + bit-vector query");
    };
    let assignment = model.to_assignment();
    assert_eq!(eval(&arena, c1, &assignment).unwrap(), Value::Bool(true));
    assert_eq!(eval(&arena, c2, &assignment).unwrap(), Value::Bool(true));
}

#[test]
fn unsat_core_isolates_conflicting_bitvector_assertions() {
    // [x&1==1, x&1==0, z|0 == z] : the first two conflict; the third is a
    // tautology and must be excluded. The minimal core is {0, 1}.
    let mut arena = TermArena::new();
    let x = arena.bv_var("x", 4).unwrap();
    let z = arena.bv_var("z", 4).unwrap();
    let one = arena.bv_const(4, 1).unwrap();
    let zero = arena.bv_const(4, 0).unwrap();
    let masked = arena.bv_and(x, one).unwrap();
    let is_one = arena.eq(masked, one).unwrap();
    let is_zero = arena.eq(masked, zero).unwrap();
    let z_or_0 = arena.bv_or(z, zero).unwrap();
    let tautology = arena.eq(z_or_0, z).unwrap();
    let assertions = [is_one, is_zero, tautology];

    let core = unsat_core(&mut arena, &assertions, &config())
        .expect("decides without error")
        .expect("the query is unsatisfiable");
    assert_eq!(core, vec![0, 1], "core excludes the tautology");

    // Every core member is necessary: dropping either makes the rest sat.
    assert!(matches!(
        solve(&mut arena, &[assertions[0], assertions[2]]),
        CheckResult::Sat(_)
    ));
    assert!(matches!(
        solve(&mut arena, &[assertions[1], assertions[2]]),
        CheckResult::Sat(_)
    ));
}

#[test]
fn unsat_core_works_across_theories_for_reals() {
    // [x > 5, y < 10, x < 1] over the reals: core {0, 2}; y is irrelevant.
    let mut arena = TermArena::new();
    let x = arena.real_var("x").unwrap();
    let y = arena.real_var("y").unwrap();
    let one = arena.real_ratio(1, 1);
    let five = arena.real_ratio(5, 1);
    let ten = arena.real_ratio(10, 1);
    let assertions = [
        arena.real_gt(x, five).unwrap(),
        arena.real_lt(y, ten).unwrap(),
        arena.real_lt(x, one).unwrap(),
    ];

    let core = unsat_core(&mut arena, &assertions, &config())
        .expect("decides without error")
        .expect("unsatisfiable");
    assert_eq!(core, vec![0, 2]);
}

#[test]
fn satisfiable_query_has_no_unsat_core() {
    let mut arena = TermArena::new();
    let x = arena.bv_var("x", 8).unwrap();
    let one = arena.bv_const(8, 1).unwrap();
    let five = arena.bv_const(8, 5).unwrap();
    let sum = arena.bv_add(x, one).unwrap();
    let eq = arena.eq(sum, five).unwrap();
    assert!(unsat_core(&mut arena, &[eq], &config()).unwrap().is_none());
}
