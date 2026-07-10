//! Retained warm array equality/extensionality gates for ADR-0089.

use axeyum_ir::{ArraySortKey, Sort, TermArena, TermId, Value, eval};
use axeyum_solver::{
    AssumptionOutcome, CheckResult, IncrementalBvSolver, SolverConfig, check_auto,
};
#[cfg(feature = "z3")]
use z3::ast::{Array, BV, Bool};
#[cfg(feature = "z3")]
use z3::{FuncDecl, SatResult, Solver, Sort as Z3Sort};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Verdict {
    Sat,
    Unsat,
    Unknown,
}

fn verdict(result: &CheckResult) -> Verdict {
    match result {
        CheckResult::Sat(_) => Verdict::Sat,
        CheckResult::Unsat => Verdict::Unsat,
        CheckResult::Unknown(_) => Verdict::Unknown,
    }
}

fn not_eq(arena: &mut TermArena, left: TermId, right: TermId) -> TermId {
    let equal = arena.eq(left, right).unwrap();
    arena.not(equal).unwrap()
}

fn assert_replays(arena: &TermArena, assertions: &[TermId], result: &CheckResult) {
    let CheckResult::Sat(model) = result else {
        return;
    };
    for &assertion in assertions {
        assert_eq!(
            eval(arena, assertion, &model.to_assignment()),
            Ok(Value::Bool(true)),
            "warm array-relation model failed assertion #{}",
            assertion.index()
        );
    }
}

fn bv_array_sort(width: u32) -> Sort {
    Sort::Array {
        index: ArraySortKey::BitVec(width),
        element: ArraySortKey::BitVec(width),
    }
}

#[test]
fn projection_equality_without_reads_builds_full_function_results() {
    let mut arena = TermArena::new();
    let array_sort = bv_array_sort(8);
    let f = arena
        .declare_fun("warm_relation_no_read_f", &[Sort::BitVec(8)], array_sort)
        .unwrap();
    let g = arena
        .declare_fun("warm_relation_no_read_g", &[Sort::BitVec(8)], array_sort)
        .unwrap();
    let x = arena.bv_var("warm_relation_no_read_x", 8).unwrap();
    let y = arena.bv_var("warm_relation_no_read_y", 8).unwrap();
    let fx = arena.apply(f, &[x]).unwrap();
    let gy = arena.apply(g, &[y]).unwrap();
    let equality = arena.eq(fx, gy).unwrap();

    assert!(IncrementalBvSolver::term_supported_by_warm_abstraction(
        &arena, equality
    ));
    let mut solver = IncrementalBvSolver::new();
    solver
        .assert_simplifying_memory(&mut arena, equality)
        .unwrap();
    assert!(!solver.has_deferred_theory_assertions());
    assert_eq!(solver.retained_warm_array_uf_app_count(), 2);

    let result = solver.check(&arena).unwrap();
    assert_eq!(verdict(&result), Verdict::Sat);
    assert_replays(&arena, &[equality], &result);
    let CheckResult::Sat(model) = result else {
        unreachable!()
    };
    assert!(model.function(f).is_some());
    assert!(model.function(g).is_some());
    for (symbol, _) in model.iter() {
        let (name, _) = arena.symbol(symbol);
        assert!(!name.starts_with("!axeyum_warm_"), "private owner leaked");
    }
}

#[test]
fn projection_equality_chains_refute_prior_conflicting_reads() {
    let mut arena = TermArena::new();
    let array_sort = bv_array_sort(8);
    let f = arena
        .declare_fun("warm_relation_chain_f", &[Sort::BitVec(8)], array_sort)
        .unwrap();
    let x = arena.bv_var("warm_relation_chain_x", 8).unwrap();
    let a = arena
        .array_var_with_sorts("warm_relation_chain_a", Sort::BitVec(8), Sort::BitVec(8))
        .unwrap();
    let b = arena
        .array_var_with_sorts("warm_relation_chain_b", Sort::BitVec(8), Sort::BitVec(8))
        .unwrap();
    let fx = arena.apply(f, &[x]).unwrap();
    let index = arena.bv_var("warm_relation_chain_i", 8).unwrap();
    let one = arena.bv_const(8, 1).unwrap();
    let two = arena.bv_const(8, 2).unwrap();
    let a_read = arena.select(a, index).unwrap();
    let b_read = arena.select(b, index).unwrap();
    let a_is_one = arena.eq(a_read, one).unwrap();
    let b_is_two = arena.eq(b_read, two).unwrap();
    let a_eq_fx = arena.eq(a, fx).unwrap();
    let fx_eq_b = arena.eq(fx, b).unwrap();
    let assertions = [a_is_one, b_is_two, a_eq_fx, fx_eq_b];

    let mut solver = IncrementalBvSolver::new();
    for &assertion in &assertions {
        solver
            .assert_simplifying_memory(&mut arena, assertion)
            .unwrap();
    }
    assert!(!solver.has_deferred_theory_assertions());
    assert_eq!(solver.check(&arena).unwrap(), CheckResult::Unsat);
}

#[test]
fn symbol_application_disequality_projects_a_private_diff_witness() {
    let mut arena = TermArena::new();
    let array_sort = bv_array_sort(8);
    let f = arena
        .declare_fun("warm_relation_diff_f", &[Sort::BitVec(8)], array_sort)
        .unwrap();
    let x = arena.bv_var("warm_relation_diff_x", 8).unwrap();
    let a = arena
        .array_var_with_sorts("warm_relation_diff_a", Sort::BitVec(8), Sort::BitVec(8))
        .unwrap();
    let fx = arena.apply(f, &[x]).unwrap();
    let disequality = not_eq(&mut arena, a, fx);

    let mut solver = IncrementalBvSolver::new();
    solver
        .assert_simplifying_memory(&mut arena, disequality)
        .unwrap();
    assert!(!solver.has_deferred_theory_assertions());
    assert_eq!(solver.retained_warm_array_diff_witness_count(), 1);
    assert_eq!(solver.retained_warm_array_uf_app_count(), 1);

    let result = solver.check(&arena).unwrap();
    assert_eq!(verdict(&result), Verdict::Sat);
    assert_replays(&arena, &[disequality], &result);
    let CheckResult::Sat(model) = result else {
        unreachable!()
    };
    for (symbol, _) in model.iter() {
        let (name, _) = arena.symbol(symbol);
        assert!(!name.starts_with("!axeyum_warm_"), "private witness leaked");
    }
}

#[test]
fn self_disequality_refutes_without_fallback() {
    let mut arena = TermArena::new();
    let a = arena
        .array_var_with_sorts("warm_relation_self_a", Sort::BitVec(8), Sort::BitVec(8))
        .unwrap();
    let disequality = not_eq(&mut arena, a, a);
    let mut solver = IncrementalBvSolver::new();
    solver
        .assert_simplifying_memory(&mut arena, disequality)
        .unwrap();
    assert!(!solver.has_deferred_theory_assertions());
    assert_eq!(solver.check(&arena).unwrap(), CheckResult::Unsat);
}

#[test]
fn structural_store_const_ite_bool_and_wide_disequalities_stay_warm() {
    let mut arena = TermArena::new();
    let index = arena.bv_var("warm_relation_struct_i", 8).unwrap();
    let zero = arena.bv_const(8, 0).unwrap();
    let one = arena.bv_const(8, 1).unwrap();
    let zero_array = arena.const_array(8, zero).unwrap();
    let stored = arena.store(zero_array, index, one).unwrap();
    let store_disequality = not_eq(&mut arena, stored, zero_array);
    let mut store_solver = IncrementalBvSolver::new();
    store_solver
        .assert_simplifying_memory(&mut arena, store_disequality)
        .unwrap();
    assert!(!store_solver.has_deferred_theory_assertions());
    let result = store_solver.check(&arena).unwrap();
    assert_eq!(verdict(&result), Verdict::Sat);
    assert_replays(&arena, &[store_disequality], &result);
    assert!(store_solver.retained_warm_structural_definition_count() >= 1);

    let condition = arena.bool_var("warm_relation_struct_c").unwrap();
    let a = arena
        .array_var_with_sorts("warm_relation_struct_a", Sort::BitVec(8), Sort::BitVec(8))
        .unwrap();
    let b = arena
        .array_var_with_sorts("warm_relation_struct_b", Sort::BitVec(8), Sort::BitVec(8))
        .unwrap();
    let chosen = arena.ite(condition, a, b).unwrap();
    let chosen_ne_a = not_eq(&mut arena, chosen, a);
    let mut ite_solver = IncrementalBvSolver::new();
    ite_solver.assert(&arena, condition).unwrap();
    ite_solver
        .assert_simplifying_memory(&mut arena, chosen_ne_a)
        .unwrap();
    assert!(!ite_solver.has_deferred_theory_assertions());
    assert_eq!(ite_solver.check(&arena).unwrap(), CheckResult::Unsat);

    let bool_false = arena.bool_const(false);
    let bool_true = arena.bool_const(true);
    let bool_array = arena
        .const_array_with_index_sort(Sort::BitVec(8), bool_false)
        .unwrap();
    let bool_stored = arena.store(bool_array, index, bool_true).unwrap();
    let bool_disequality = not_eq(&mut arena, bool_stored, bool_array);
    let mut bool_solver = IncrementalBvSolver::new();
    bool_solver
        .assert_simplifying_memory(&mut arena, bool_disequality)
        .unwrap();
    let result = bool_solver.check(&arena).unwrap();
    assert_eq!(verdict(&result), Verdict::Sat);
    assert_replays(&arena, &[bool_disequality], &result);

    let wide_index = arena.bv_var("warm_relation_wide_i", 256).unwrap();
    let wide_zero = arena.bv_const(256, 0).unwrap();
    let wide_one = arena.bv_const(256, 1).unwrap();
    let wide_array = arena.const_array(256, wide_zero).unwrap();
    let wide_stored = arena.store(wide_array, wide_index, wide_one).unwrap();
    let wide_disequality = not_eq(&mut arena, wide_stored, wide_array);
    let mut wide_solver = IncrementalBvSolver::new();
    wide_solver
        .assert_simplifying_memory(&mut arena, wide_disequality)
        .unwrap();
    let result = wide_solver.check(&arena).unwrap();
    assert_eq!(verdict(&result), Verdict::Sat);
    assert_replays(&arena, &[wide_disequality], &result);
}

#[test]
fn relation_roots_are_scoped_and_assumption_cores_are_user_facing() {
    let mut arena = TermArena::new();
    let array_sort = bv_array_sort(4);
    let f = arena
        .declare_fun("warm_relation_scope_f", &[Sort::BitVec(4)], array_sort)
        .unwrap();
    let x = arena.bv_var("warm_relation_scope_x", 4).unwrap();
    let a = arena
        .array_var_with_sorts("warm_relation_scope_a", Sort::BitVec(4), Sort::BitVec(4))
        .unwrap();
    let fx = arena.apply(f, &[x]).unwrap();
    let equality = arena.eq(a, fx).unwrap();
    let disequality = arena.not(equality).unwrap();

    let mut solver = IncrementalBvSolver::new();
    solver
        .assert_simplifying_memory(&mut arena, equality)
        .unwrap();
    let base = solver.check(&arena).unwrap();
    assert_eq!(verdict(&base), Verdict::Sat);
    assert_replays(&arena, &[equality], &base);

    let outcome = solver
        .check_assuming_core_simplifying_memory(&mut arena, &[disequality])
        .unwrap();
    let AssumptionOutcome::Unsat { core } = outcome else {
        panic!("opposite one-shot array relation must refute");
    };
    assert_eq!(core, vec![disequality]);
    assert_eq!(verdict(&solver.check(&arena).unwrap()), Verdict::Sat);

    solver.push().unwrap();
    solver
        .assert_simplifying_memory(&mut arena, disequality)
        .unwrap();
    assert_eq!(solver.check(&arena).unwrap(), CheckResult::Unsat);
    assert!(solver.pop());
    let after_pop = solver.check(&arena).unwrap();
    assert_eq!(verdict(&after_pop), Verdict::Sat);
    assert_replays(&arena, &[equality], &after_pop);
}

fn deep_store_relation(arena: &mut TermArena, depth: usize) -> TermId {
    let base = arena
        .array_var_with_sorts("warm_relation_limit_a", Sort::BitVec(8), Sort::BitVec(8))
        .unwrap();
    let index = arena.bv_var("warm_relation_limit_i", 8).unwrap();
    let value = arena.bv_const(8, 1).unwrap();
    let mut parent = base;
    for _ in 0..depth {
        parent = arena.store(parent, index, value).unwrap();
    }
    not_eq(arena, parent, base)
}

#[test]
fn unsupported_positive_structure_nested_boolean_and_one_over_depth_defer_cleanly() {
    let mut structural_arena = TermArena::new();
    let base = structural_arena
        .array_var_with_sorts(
            "warm_relation_unsupported_a",
            Sort::BitVec(8),
            Sort::BitVec(8),
        )
        .unwrap();
    let index = structural_arena
        .bv_var("warm_relation_unsupported_i", 8)
        .unwrap();
    let value = structural_arena.bv_const(8, 1).unwrap();
    let stored = structural_arena.store(base, index, value).unwrap();
    let structural_equality = structural_arena.eq(stored, base).unwrap();
    assert!(!IncrementalBvSolver::term_supported_by_warm_abstraction(
        &structural_arena,
        structural_equality
    ));
    let mut structural_solver = IncrementalBvSolver::new();
    structural_solver
        .assert_simplifying_memory(&mut structural_arena, structural_equality)
        .unwrap();
    assert!(structural_solver.has_deferred_theory_assertions());
    assert_eq!(
        structural_solver.retained_warm_array_diff_witness_count(),
        0
    );

    let mut nested_arena = TermArena::new();
    let array_sort = bv_array_sort(8);
    let f = nested_arena
        .declare_fun("warm_relation_nested_f", &[Sort::BitVec(8)], array_sort)
        .unwrap();
    let x = nested_arena.bv_var("warm_relation_nested_x", 8).unwrap();
    let a = nested_arena
        .array_var_with_sorts("warm_relation_nested_a", Sort::BitVec(8), Sort::BitVec(8))
        .unwrap();
    let fx = nested_arena.apply(f, &[x]).unwrap();
    let equality = nested_arena.eq(fx, a).unwrap();
    let flag = nested_arena.bool_var("warm_relation_nested_flag").unwrap();
    let nested = nested_arena.or(flag, equality).unwrap();
    assert!(!IncrementalBvSolver::term_supported_by_warm_abstraction(
        &nested_arena,
        nested
    ));
    let mut nested_solver = IncrementalBvSolver::new();
    nested_solver
        .assert_simplifying_memory(&mut nested_arena, nested)
        .unwrap();
    assert!(nested_solver.has_deferred_theory_assertions());
    assert_eq!(nested_solver.retained_warm_array_uf_app_count(), 0);

    let mut at_limit = TermArena::new();
    let relation = deep_store_relation(&mut at_limit, 256);
    assert!(IncrementalBvSolver::term_supported_by_warm_abstraction(
        &at_limit, relation
    ));

    let mut over_limit = TermArena::new();
    let relation = deep_store_relation(&mut over_limit, 257);
    assert!(!IncrementalBvSolver::term_supported_by_warm_abstraction(
        &over_limit,
        relation
    ));
    let mut over_solver = IncrementalBvSolver::new();
    over_solver
        .assert_simplifying_memory(&mut over_limit, relation)
        .unwrap();
    assert!(over_solver.has_deferred_theory_assertions());
    assert_eq!(over_solver.retained_warm_array_diff_witness_count(), 0);
}

fn expected(seed: u64) -> Verdict {
    match seed % 8 {
        0 | 3 | 5 | 7 => Verdict::Unsat,
        _ => Verdict::Sat,
    }
}

fn build_case(seed: u64, arena: &mut TermArena) -> Vec<TermId> {
    let array_sort = bv_array_sort(3);
    let f = arena
        .declare_fun("warm_relation_matrix_f", &[Sort::BitVec(3)], array_sort)
        .unwrap();
    let x = arena.bv_var("warm_relation_matrix_x", 3).unwrap();
    let a = arena
        .array_var_with_sorts("warm_relation_matrix_a", Sort::BitVec(3), Sort::BitVec(3))
        .unwrap();
    let b = arena
        .array_var_with_sorts("warm_relation_matrix_b", Sort::BitVec(3), Sort::BitVec(3))
        .unwrap();
    let condition = arena.bool_var("warm_relation_matrix_c").unwrap();
    let zero = arena.bv_const(3, 0).unwrap();
    let one_index = arena.bv_const(3, 1).unwrap();
    let one = arena.bv_const(3, 1).unwrap();
    let two = arena.bv_const(3, 2).unwrap();
    let fx = arena.apply(f, &[x]).unwrap();
    let equality = arena.eq(fx, a).unwrap();
    let disequality = arena.not(equality).unwrap();

    match seed % 8 {
        0 => {
            let fx_read = arena.select(fx, zero).unwrap();
            let a_read = arena.select(a, zero).unwrap();
            vec![
                equality,
                arena.eq(fx_read, one).unwrap(),
                arena.eq(a_read, two).unwrap(),
            ]
        }
        1 => {
            let fx_read = arena.select(fx, zero).unwrap();
            let a_read = arena.select(a, one_index).unwrap();
            vec![
                equality,
                arena.eq(fx_read, one).unwrap(),
                arena.eq(a_read, two).unwrap(),
            ]
        }
        2 => vec![disequality],
        3 => vec![equality, disequality],
        4 => {
            let zero_array = arena.const_array(3, zero).unwrap();
            let stored = arena.store(zero_array, zero, one).unwrap();
            vec![not_eq(arena, stored, zero_array)]
        }
        5 => {
            let chosen = arena.ite(condition, a, b).unwrap();
            vec![condition, not_eq(arena, chosen, a)]
        }
        6 => {
            let false_value = arena.bool_const(false);
            let true_value = arena.bool_const(true);
            let bool_array = arena
                .const_array_with_index_sort(Sort::BitVec(3), false_value)
                .unwrap();
            let stored = arena.store(bool_array, zero, true_value).unwrap();
            vec![not_eq(arena, stored, bool_array)]
        }
        _ => {
            let a_read = arena.select(a, zero).unwrap();
            let b_read = arena.select(b, zero).unwrap();
            vec![
                arena.eq(a_read, one).unwrap(),
                arena.eq(b_read, two).unwrap(),
                arena.eq(a, fx).unwrap(),
                arena.eq(fx, b).unwrap(),
            ]
        }
    }
}

#[test]
fn warm_matrix_matches_check_auto_and_replays() {
    for seed in 0..64 {
        let expected = expected(seed);
        let mut warm_arena = TermArena::new();
        let assertions = build_case(seed, &mut warm_arena);
        let mut warm = IncrementalBvSolver::new();
        for &assertion in &assertions {
            warm.assert_simplifying_memory(&mut warm_arena, assertion)
                .unwrap();
        }
        assert!(!warm.has_deferred_theory_assertions(), "seed {seed}");
        let result = warm.check(&warm_arena).unwrap();
        assert_eq!(verdict(&result), expected, "warm seed {seed}: {result:?}");
        assert_replays(&warm_arena, &assertions, &result);

        let mut canonical_arena = TermArena::new();
        let canonical_assertions = build_case(seed, &mut canonical_arena);
        let canonical = check_auto(
            &mut canonical_arena,
            &canonical_assertions,
            &SolverConfig::default(),
        )
        .unwrap();
        assert_eq!(
            verdict(&canonical),
            expected,
            "check_auto seed {seed}: {canonical:?}"
        );
    }
}

#[cfg(feature = "z3")]
fn z3_verdict(seed: u64) -> Verdict {
    let bv_sort = Z3Sort::bitvector(3);
    let array_sort = Z3Sort::array(&bv_sort, &bv_sort);
    let f = FuncDecl::new("warm_relation_matrix_f", &[&bv_sort], &array_sort);
    let x = BV::new_const("warm_relation_matrix_x", 3);
    let a = Array::new_const("warm_relation_matrix_a", &bv_sort, &bv_sort);
    let b = Array::new_const("warm_relation_matrix_b", &bv_sort, &bv_sort);
    let condition = Bool::new_const("warm_relation_matrix_c");
    let zero = BV::from_u64(0, 3);
    let one_index = BV::from_u64(1, 3);
    let one = BV::from_u64(1, 3);
    let two = BV::from_u64(2, 3);
    let fx = f.apply(&[&x]).as_array().unwrap();
    let equality = fx.eq(&a);
    let disequality = equality.not();

    let assertions: Vec<Bool> = match seed % 8 {
        0 => vec![
            equality,
            fx.select(&zero).as_bv().unwrap().eq(&one),
            a.select(&zero).as_bv().unwrap().eq(&two),
        ],
        1 => vec![
            equality,
            fx.select(&zero).as_bv().unwrap().eq(&one),
            a.select(&one_index).as_bv().unwrap().eq(&two),
        ],
        2 => vec![disequality],
        3 => vec![equality, disequality],
        4 => {
            let zero_array = Array::const_array(&bv_sort, &zero);
            vec![zero_array.store(&zero, &one).eq(&zero_array).not()]
        }
        5 => vec![condition.clone(), condition.ite(&a, &b).eq(&a).not()],
        6 => {
            let false_value = Bool::from_bool(false);
            let true_value = Bool::from_bool(true);
            let bool_array = Array::const_array(&bv_sort, &false_value);
            vec![bool_array.store(&zero, &true_value).eq(&bool_array).not()]
        }
        _ => vec![
            a.select(&zero).as_bv().unwrap().eq(&one),
            b.select(&zero).as_bv().unwrap().eq(&two),
            a.eq(&fx),
            fx.eq(&b),
        ],
    };
    let solver = Solver::new();
    for assertion in assertions {
        solver.assert(&assertion);
    }
    match solver.check() {
        SatResult::Sat => Verdict::Sat,
        SatResult::Unsat => Verdict::Unsat,
        SatResult::Unknown => Verdict::Unknown,
    }
}

#[cfg(feature = "z3")]
#[test]
fn warm_matrix_matches_z3() {
    for seed in 0..64 {
        assert_eq!(z3_verdict(seed), expected(seed), "Z3 seed {seed}");
    }
}
