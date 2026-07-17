//! Retained warm array-valued UF parent gates for ADR-0088.
#![cfg(feature = "full")]

use axeyum_ir::{ArraySortKey, Sort, TermArena, TermId, Value, eval};
use axeyum_solver::{
    AssumptionOutcome, CheckResult, IncrementalBvSolver, SolverConfig, check_auto,
};
#[cfg(feature = "z3")]
use z3::ast::{BV, Bool};
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
            "warm array-UF model failed assertion #{}",
            assertion.index()
        );
    }
}

#[test]
fn single_application_projects_function_and_hides_private_array_owner() {
    let mut arena = TermArena::new();
    let array_sort = Sort::Array {
        index: ArraySortKey::BitVec(8),
        element: ArraySortKey::BitVec(8),
    };
    let function = arena
        .declare_fun("warm_array_uf_single_f", &[Sort::BitVec(8)], array_sort)
        .unwrap();
    let x = arena.bv_var("warm_array_uf_single_x", 8).unwrap();
    let index = arena.bv_var("warm_array_uf_single_i", 8).unwrap();
    let target = arena.bv_const(8, 0x42).unwrap();
    let app = arena.apply(function, &[x]).unwrap();
    let read = arena.select(app, index).unwrap();
    let assertion = arena.eq(read, target).unwrap();

    let mut solver = IncrementalBvSolver::new();
    solver
        .assert_simplifying_memory(&mut arena, assertion)
        .unwrap();
    assert!(!solver.has_deferred_theory_assertions());
    assert_eq!(solver.retained_warm_array_uf_app_count(), 1);

    let result = solver.check(&arena).unwrap();
    assert_eq!(verdict(&result), Verdict::Sat);
    assert_replays(&arena, &[assertion], &result);
    let CheckResult::Sat(model) = result else {
        unreachable!()
    };
    assert!(model.function(function).is_some());
    for (symbol, _) in model.iter() {
        let (name, _) = arena.symbol(symbol);
        assert!(!name.starts_with("!axeyum_warm_"), "private owner leaked");
    }
}

#[test]
fn equal_arguments_and_indices_enforce_array_result_read_congruence() {
    let mut arena = TermArena::new();
    let array_sort = Sort::Array {
        index: ArraySortKey::BitVec(4),
        element: ArraySortKey::BitVec(4),
    };
    let function = arena
        .declare_fun("warm_array_uf_cong_f", &[Sort::BitVec(4)], array_sort)
        .unwrap();
    let x = arena.bv_var("warm_array_uf_cong_x", 4).unwrap();
    let y = arena.bv_var("warm_array_uf_cong_y", 4).unwrap();
    let i = arena.bv_var("warm_array_uf_cong_i", 4).unwrap();
    let j = arena.bv_var("warm_array_uf_cong_j", 4).unwrap();
    let one = arena.bv_const(4, 1).unwrap();
    let two = arena.bv_const(4, 2).unwrap();
    let fx = arena.apply(function, &[x]).unwrap();
    let fy = arena.apply(function, &[y]).unwrap();
    let left = arena.select(fx, i).unwrap();
    let right = arena.select(fy, j).unwrap();
    let assertions = [
        arena.eq(x, y).unwrap(),
        arena.eq(i, j).unwrap(),
        arena.eq(left, one).unwrap(),
        arena.eq(right, two).unwrap(),
    ];

    let mut solver = IncrementalBvSolver::new();
    for &assertion in &assertions {
        solver
            .assert_simplifying_memory(&mut arena, assertion)
            .unwrap();
    }
    assert!(!solver.has_deferred_theory_assertions());
    assert_eq!(solver.retained_warm_array_uf_app_count(), 2);
    assert_eq!(solver.check(&arena).unwrap(), CheckResult::Unsat);
}

#[test]
fn equal_concrete_argument_tuple_merges_split_observations() {
    let mut arena = TermArena::new();
    let array_sort = Sort::Array {
        index: ArraySortKey::BitVec(4),
        element: ArraySortKey::BitVec(4),
    };
    let function = arena
        .declare_fun("warm_array_uf_merge_f", &[Sort::BitVec(4)], array_sort)
        .unwrap();
    let x = arena.bv_var("warm_array_uf_merge_x", 4).unwrap();
    let y = arena.bv_var("warm_array_uf_merge_y", 4).unwrap();
    let zero = arena.bv_const(4, 0).unwrap();
    let one_index = arena.bv_const(4, 1).unwrap();
    let one = arena.bv_const(4, 1).unwrap();
    let two = arena.bv_const(4, 2).unwrap();
    let fx = arena.apply(function, &[x]).unwrap();
    let fy = arena.apply(function, &[y]).unwrap();
    let left = arena.select(fx, zero).unwrap();
    let right = arena.select(fy, one_index).unwrap();
    let assertions = [
        arena.eq(x, y).unwrap(),
        arena.eq(left, one).unwrap(),
        arena.eq(right, two).unwrap(),
    ];

    let mut solver = IncrementalBvSolver::new();
    for &assertion in &assertions {
        solver
            .assert_simplifying_memory(&mut arena, assertion)
            .unwrap();
    }
    let result = solver.check(&arena).unwrap();
    assert_eq!(verdict(&result), Verdict::Sat);
    assert_replays(&arena, &assertions, &result);
}

#[test]
fn nested_scalar_uf_arguments_and_indices_replay() {
    let mut arena = TermArena::new();
    let array_sort = Sort::Array {
        index: ArraySortKey::BitVec(8),
        element: ArraySortKey::BitVec(8),
    };
    let scalar = arena
        .declare_fun(
            "warm_array_uf_nested_g",
            &[Sort::BitVec(8)],
            Sort::BitVec(8),
        )
        .unwrap();
    let array_function = arena
        .declare_fun("warm_array_uf_nested_f", &[Sort::BitVec(8)], array_sort)
        .unwrap();
    let x = arena.bv_var("warm_array_uf_nested_x", 8).unwrap();
    let index_seed = arena.bv_var("warm_array_uf_nested_i", 8).unwrap();
    let gx = arena.apply(scalar, &[x]).unwrap();
    let gi = arena.apply(scalar, &[index_seed]).unwrap();
    let app = arena.apply(array_function, &[gx]).unwrap();
    let read = arena.select(app, gi).unwrap();
    let target = arena.bv_const(8, 0xa5).unwrap();
    let assertion = arena.eq(read, target).unwrap();

    let mut solver = IncrementalBvSolver::new();
    solver
        .assert_simplifying_memory(&mut arena, assertion)
        .unwrap();
    assert!(!solver.has_deferred_theory_assertions());
    let result = solver.check(&arena).unwrap();
    assert_eq!(verdict(&result), Verdict::Sat);
    assert_replays(&arena, &[assertion], &result);
}

#[test]
fn structural_store_ite_bool_and_wide_application_parents_stay_warm() {
    let mut arena = TermArena::new();
    let bv_array_sort = Sort::Array {
        index: ArraySortKey::BitVec(8),
        element: ArraySortKey::BitVec(8),
    };
    let function = arena
        .declare_fun("warm_array_uf_struct_f", &[Sort::BitVec(8)], bv_array_sort)
        .unwrap();
    let x = arena.bv_var("warm_array_uf_struct_x", 8).unwrap();
    let write = arena.bv_var("warm_array_uf_struct_w", 8).unwrap();
    let read_index = arena.bv_var("warm_array_uf_struct_r", 8).unwrap();
    let one = arena.bv_const(8, 1).unwrap();
    let app = arena.apply(function, &[x]).unwrap();
    let stored = arena.store(app, write, one).unwrap();
    let loaded = arena.select(stored, read_index).unwrap();
    let store_assertions = [
        arena.eq(write, read_index).unwrap(),
        not_eq(&mut arena, loaded, one),
    ];
    let mut store_solver = IncrementalBvSolver::new();
    for &assertion in &store_assertions {
        store_solver
            .assert_simplifying_memory(&mut arena, assertion)
            .unwrap();
    }
    assert!(!store_solver.has_deferred_theory_assertions());
    assert_eq!(store_solver.check(&arena).unwrap(), CheckResult::Unsat);
    assert_eq!(store_solver.retained_warm_structural_definition_count(), 1);

    let condition = arena.bool_var("warm_array_uf_struct_c").unwrap();
    let other = arena
        .array_var_with_sorts("warm_array_uf_struct_a", Sort::BitVec(8), Sort::BitVec(8))
        .unwrap();
    let chosen = arena.ite(condition, app, other).unwrap();
    let chosen_read = arena.select(chosen, read_index).unwrap();
    let app_read = arena.select(app, read_index).unwrap();
    let ite_assertions = [condition, not_eq(&mut arena, chosen_read, app_read)];
    let mut ite_solver = IncrementalBvSolver::new();
    for &assertion in &ite_assertions {
        ite_solver
            .assert_simplifying_memory(&mut arena, assertion)
            .unwrap();
    }
    assert_eq!(ite_solver.check(&arena).unwrap(), CheckResult::Unsat);

    let bool_array_sort = Sort::Array {
        index: ArraySortKey::BitVec(8),
        element: ArraySortKey::Bool,
    };
    let predicate = arena
        .declare_fun("warm_array_uf_bool_f", &[Sort::BitVec(8)], bool_array_sort)
        .unwrap();
    let predicate_app = arena.apply(predicate, &[x]).unwrap();
    let predicate_read = arena.select(predicate_app, read_index).unwrap();
    let mut bool_solver = IncrementalBvSolver::new();
    bool_solver
        .assert_simplifying_memory(&mut arena, predicate_read)
        .unwrap();
    let result = bool_solver.check(&arena).unwrap();
    assert_eq!(verdict(&result), Verdict::Sat);
    assert_replays(&arena, &[predicate_read], &result);

    let wide_array_sort = Sort::Array {
        index: ArraySortKey::BitVec(256),
        element: ArraySortKey::BitVec(256),
    };
    let wide_function = arena
        .declare_fun(
            "warm_array_uf_wide_f",
            &[Sort::BitVec(256)],
            wide_array_sort,
        )
        .unwrap();
    let wide_x = arena.bv_var("warm_array_uf_wide_x", 256).unwrap();
    let wide_i = arena.bv_var("warm_array_uf_wide_i", 256).unwrap();
    let wide_target = arena.bv_const(256, 7).unwrap();
    let wide_app = arena.apply(wide_function, &[wide_x]).unwrap();
    let wide_read = arena.select(wide_app, wide_i).unwrap();
    let wide_assertion = arena.eq(wide_read, wide_target).unwrap();
    let mut wide_solver = IncrementalBvSolver::new();
    wide_solver
        .assert_simplifying_memory(&mut arena, wide_assertion)
        .unwrap();
    let result = wide_solver.check(&arena).unwrap();
    assert_eq!(verdict(&result), Verdict::Sat);
    assert_replays(&arena, &[wide_assertion], &result);
}

#[test]
fn array_application_congruence_is_scoped_and_one_shot_core_is_user_facing() {
    let mut arena = TermArena::new();
    let array_sort = Sort::Array {
        index: ArraySortKey::BitVec(4),
        element: ArraySortKey::BitVec(4),
    };
    let function = arena
        .declare_fun("warm_array_uf_scope_f", &[Sort::BitVec(4)], array_sort)
        .unwrap();
    let x = arena.bv_var("warm_array_uf_scope_x", 4).unwrap();
    let y = arena.bv_var("warm_array_uf_scope_y", 4).unwrap();
    let index = arena.bv_var("warm_array_uf_scope_i", 4).unwrap();
    let one = arena.bv_const(4, 1).unwrap();
    let fx = arena.apply(function, &[x]).unwrap();
    let fy = arena.apply(function, &[y]).unwrap();
    let left = arena.select(fx, index).unwrap();
    let right = arena.select(fy, index).unwrap();
    let left_is_one = arena.eq(left, one).unwrap();
    let right_not_one = not_eq(&mut arena, right, one);
    let same_args = arena.eq(x, y).unwrap();

    let mut solver = IncrementalBvSolver::new();
    solver
        .assert_simplifying_memory(&mut arena, left_is_one)
        .unwrap();
    solver.push().unwrap();
    solver
        .assert_simplifying_memory(&mut arena, right_not_one)
        .unwrap();
    solver.assert(&arena, same_args).unwrap();
    assert_eq!(solver.check(&arena).unwrap(), CheckResult::Unsat);
    assert!(solver.pop());
    let base = solver.check(&arena).unwrap();
    assert_eq!(verdict(&base), Verdict::Sat);
    assert_replays(&arena, &[left_is_one], &base);

    let outcome = solver
        .check_assuming_core_simplifying_memory(&mut arena, &[same_args, right_not_one])
        .unwrap();
    let AssumptionOutcome::Unsat { core } = outcome else {
        panic!("one-shot equal-argument conflict must be unsat");
    };
    assert!(
        core.iter()
            .all(|term| [same_args, right_not_one].contains(term))
    );
    assert_eq!(verdict(&solver.check(&arena).unwrap()), Verdict::Sat);
}

#[test]
fn direct_array_parameters_project_distinct_function_keys() {
    let mut arena = TermArena::new();
    let array_sort = Sort::Array {
        index: ArraySortKey::BitVec(4),
        element: ArraySortKey::BitVec(4),
    };
    let function = arena
        .declare_fun("warm_array_param_f", &[array_sort], array_sort)
        .unwrap();
    let a = arena
        .array_var_with_sorts("warm_array_param_a", Sort::BitVec(4), Sort::BitVec(4))
        .unwrap();
    let b = arena
        .array_var_with_sorts("warm_array_param_b", Sort::BitVec(4), Sort::BitVec(4))
        .unwrap();
    let zero = arena.bv_const(4, 0).unwrap();
    let one = arena.bv_const(4, 1).unwrap();
    let two = arena.bv_const(4, 2).unwrap();
    let fa = arena.apply(function, &[a]).unwrap();
    let fb = arena.apply(function, &[b]).unwrap();
    let left = arena.select(fa, zero).unwrap();
    let right = arena.select(fb, zero).unwrap();
    let assertions = [arena.eq(left, one).unwrap(), arena.eq(right, two).unwrap()];

    let mut solver = IncrementalBvSolver::new();
    for &assertion in &assertions {
        solver
            .assert_simplifying_memory(&mut arena, assertion)
            .unwrap();
    }
    assert!(!solver.has_deferred_theory_assertions());
    assert_eq!(solver.retained_warm_array_uf_app_count(), 2);
    assert_eq!(solver.retained_warm_array_relation_flag_count(), 1);
    let result = solver.check(&arena).unwrap();
    assert_eq!(verdict(&result), Verdict::Sat, "result={result:?}");
    assert_replays(&arena, &assertions, &result);
}

#[test]
fn nested_array_application_parameter_projects_and_replays() {
    let mut arena = TermArena::new();
    let array_sort = Sort::Array {
        index: ArraySortKey::BitVec(4),
        element: ArraySortKey::BitVec(4),
    };
    let key_function = arena
        .declare_fun("warm_nested_array_param_g", &[array_sort], array_sort)
        .unwrap();
    let result_function = arena
        .declare_fun("warm_nested_array_param_f", &[array_sort], array_sort)
        .unwrap();
    let a = arena
        .array_var_with_sorts(
            "warm_nested_array_param_a",
            Sort::BitVec(4),
            Sort::BitVec(4),
        )
        .unwrap();
    let zero = arena.bv_const(4, 0).unwrap();
    let three = arena.bv_const(4, 3).unwrap();
    let nested_key = arena.apply(key_function, &[a]).unwrap();
    let app = arena.apply(result_function, &[nested_key]).unwrap();
    let read = arena.select(app, zero).unwrap();
    let assertion = arena.eq(read, three).unwrap();

    assert!(IncrementalBvSolver::term_supported_by_warm_abstraction(
        &arena, assertion
    ));
    let mut solver = IncrementalBvSolver::new();
    solver
        .assert_simplifying_memory(&mut arena, assertion)
        .unwrap();
    assert!(!solver.has_deferred_theory_assertions());
    assert_eq!(solver.retained_warm_array_uf_app_count(), 2);

    let result = solver.check(&arena).unwrap();
    assert_eq!(verdict(&result), Verdict::Sat, "result={result:?}");
    assert_replays(&arena, &[assertion], &result);
    let CheckResult::Sat(model) = result else {
        unreachable!()
    };
    assert!(model.function(key_function).is_some());
    assert!(model.function(result_function).is_some());
}

#[test]
fn nested_array_application_parameter_equality_refutes_conflicting_results() {
    let mut arena = TermArena::new();
    let array_sort = Sort::Array {
        index: ArraySortKey::BitVec(4),
        element: ArraySortKey::BitVec(4),
    };
    let key_function = arena
        .declare_fun("warm_nested_array_param_cong_g", &[array_sort], array_sort)
        .unwrap();
    let result_function = arena
        .declare_fun("warm_nested_array_param_cong_f", &[array_sort], array_sort)
        .unwrap();
    let a = arena
        .array_var_with_sorts(
            "warm_nested_array_param_cong_a",
            Sort::BitVec(4),
            Sort::BitVec(4),
        )
        .unwrap();
    let b = arena
        .array_var_with_sorts(
            "warm_nested_array_param_cong_b",
            Sort::BitVec(4),
            Sort::BitVec(4),
        )
        .unwrap();
    let index = arena.bv_var("warm_nested_array_param_cong_i", 4).unwrap();
    let one = arena.bv_const(4, 1).unwrap();
    let two = arena.bv_const(4, 2).unwrap();
    let ga = arena.apply(key_function, &[a]).unwrap();
    let gb = arena.apply(key_function, &[b]).unwrap();
    let fga = arena.apply(result_function, &[ga]).unwrap();
    let fgb = arena.apply(result_function, &[gb]).unwrap();
    let left = arena.select(fga, index).unwrap();
    let right = arena.select(fgb, index).unwrap();
    let assertions = [
        arena.eq(ga, gb).unwrap(),
        arena.eq(left, one).unwrap(),
        arena.eq(right, two).unwrap(),
    ];

    let mut solver = IncrementalBvSolver::new();
    for &assertion in &assertions {
        solver
            .assert_simplifying_memory(&mut arena, assertion)
            .unwrap();
    }
    assert!(!solver.has_deferred_theory_assertions());
    assert_eq!(solver.retained_warm_array_uf_app_count(), 4);
    assert_eq!(solver.check(&arena).unwrap(), CheckResult::Unsat);
}

#[test]
fn structural_store_parameter_projects_and_replays() {
    let mut arena = TermArena::new();
    let array_sort = Sort::Array {
        index: ArraySortKey::BitVec(4),
        element: ArraySortKey::BitVec(4),
    };
    let function = arena
        .declare_fun("warm_structural_param_f", &[array_sort], array_sort)
        .unwrap();
    let scalar = arena
        .declare_fun(
            "warm_structural_param_h",
            &[Sort::BitVec(4)],
            Sort::BitVec(4),
        )
        .unwrap();
    let base = arena
        .array_var_with_sorts("warm_structural_param_a", Sort::BitVec(4), Sort::BitVec(4))
        .unwrap();
    let x = arena.bv_var("warm_structural_param_x", 4).unwrap();
    let hx = arena.apply(scalar, &[x]).unwrap();
    let zero = arena.bv_const(4, 0).unwrap();
    let two = arena.bv_const(4, 2).unwrap();
    let three = arena.bv_const(4, 3).unwrap();
    let key = arena.store(base, hx, two).unwrap();
    let app = arena.apply(function, &[key]).unwrap();
    let read = arena.select(app, zero).unwrap();
    let assertion = arena.eq(read, three).unwrap();

    let mut solver = IncrementalBvSolver::new();
    solver
        .assert_simplifying_memory(&mut arena, assertion)
        .unwrap();
    assert!(!solver.has_deferred_theory_assertions());
    assert_eq!(solver.retained_warm_array_uf_app_count(), 1);
    assert_eq!(solver.retained_warm_structural_array_owner_count(), 1);

    let result = solver.check(&arena).unwrap();
    assert_eq!(verdict(&result), Verdict::Sat);
    assert_replays(&arena, &[assertion], &result);
}

#[test]
fn structural_key_with_nested_application_base_projects_and_replays() {
    let mut arena = TermArena::new();
    let array_sort = Sort::Array {
        index: ArraySortKey::BitVec(4),
        element: ArraySortKey::BitVec(4),
    };
    let key_function = arena
        .declare_fun("warm_structural_nested_param_g", &[array_sort], array_sort)
        .unwrap();
    let result_function = arena
        .declare_fun("warm_structural_nested_param_f", &[array_sort], array_sort)
        .unwrap();
    let base = arena
        .array_var_with_sorts(
            "warm_structural_nested_param_a",
            Sort::BitVec(4),
            Sort::BitVec(4),
        )
        .unwrap();
    let key_index = arena.bv_var("warm_structural_nested_param_k", 4).unwrap();
    let read_index = arena.bv_const(4, 0).unwrap();
    let one = arena.bv_const(4, 1).unwrap();
    let two = arena.bv_const(4, 2).unwrap();
    let nested = arena.apply(key_function, &[base]).unwrap();
    let key = arena.store(nested, key_index, one).unwrap();
    let app = arena.apply(result_function, &[key]).unwrap();
    let read = arena.select(app, read_index).unwrap();
    let assertion = arena.eq(read, two).unwrap();

    assert!(IncrementalBvSolver::term_supported_by_warm_abstraction(
        &arena, assertion
    ));
    let mut solver = IncrementalBvSolver::new();
    solver
        .assert_simplifying_memory(&mut arena, assertion)
        .unwrap();
    assert!(!solver.has_deferred_theory_assertions());
    assert_eq!(solver.retained_warm_array_uf_app_count(), 2);
    assert_eq!(solver.retained_warm_structural_array_owner_count(), 1);

    let result = solver.check(&arena).unwrap();
    assert_eq!(verdict(&result), Verdict::Sat, "result={result:?}");
    assert_replays(&arena, &[assertion], &result);
}

#[test]
fn structural_array_parameter_relation_flag_separates_independent_keys() {
    let mut arena = TermArena::new();
    let array_sort = Sort::Array {
        index: ArraySortKey::BitVec(4),
        element: ArraySortKey::BitVec(4),
    };
    let function = arena
        .declare_fun("warm_structural_param_rel_f", &[array_sort], array_sort)
        .unwrap();
    let a = arena
        .array_var_with_sorts(
            "warm_structural_param_rel_a",
            Sort::BitVec(4),
            Sort::BitVec(4),
        )
        .unwrap();
    let b = arena
        .array_var_with_sorts(
            "warm_structural_param_rel_b",
            Sort::BitVec(4),
            Sort::BitVec(4),
        )
        .unwrap();
    let key_index = arena.bv_var("warm_structural_param_rel_k", 4).unwrap();
    let read_index = arena.bv_const(4, 0).unwrap();
    let one = arena.bv_const(4, 1).unwrap();
    let two = arena.bv_const(4, 2).unwrap();
    let left_key = arena.store(a, key_index, one).unwrap();
    let right_key = arena.store(b, key_index, one).unwrap();
    let left_app = arena.apply(function, &[left_key]).unwrap();
    let right_app = arena.apply(function, &[right_key]).unwrap();
    let left = arena.select(left_app, read_index).unwrap();
    let right = arena.select(right_app, read_index).unwrap();
    let assertions = [arena.eq(left, one).unwrap(), arena.eq(right, two).unwrap()];

    let mut solver = IncrementalBvSolver::new();
    for &assertion in &assertions {
        solver
            .assert_simplifying_memory(&mut arena, assertion)
            .unwrap();
    }
    assert!(!solver.has_deferred_theory_assertions());
    assert_eq!(solver.retained_warm_array_uf_app_count(), 2);
    assert_eq!(solver.retained_warm_array_relation_flag_count(), 1);
    let result = solver.check(&arena).unwrap();
    assert_eq!(verdict(&result), Verdict::Sat, "result={result:?}");
    assert_replays(&arena, &assertions, &result);
}

#[test]
fn structural_array_parameter_active_equality_refutes_conflicting_results() {
    let mut arena = TermArena::new();
    let array_sort = Sort::Array {
        index: ArraySortKey::BitVec(4),
        element: ArraySortKey::BitVec(4),
    };
    let function = arena
        .declare_fun("warm_structural_param_cong_f", &[array_sort], array_sort)
        .unwrap();
    let a = arena
        .array_var_with_sorts(
            "warm_structural_param_cong_a",
            Sort::BitVec(4),
            Sort::BitVec(4),
        )
        .unwrap();
    let b = arena
        .array_var_with_sorts(
            "warm_structural_param_cong_b",
            Sort::BitVec(4),
            Sort::BitVec(4),
        )
        .unwrap();
    let key_index = arena.bv_var("warm_structural_param_cong_k", 4).unwrap();
    let read_index = arena.bv_const(4, 0).unwrap();
    let one = arena.bv_const(4, 1).unwrap();
    let two = arena.bv_const(4, 2).unwrap();
    let left_key = arena.store(a, key_index, one).unwrap();
    let right_key = arena.store(b, key_index, one).unwrap();
    let left_app = arena.apply(function, &[left_key]).unwrap();
    let right_app = arena.apply(function, &[right_key]).unwrap();
    let left = arena.select(left_app, read_index).unwrap();
    let right = arena.select(right_app, read_index).unwrap();
    let assertions = [
        arena.eq(left_key, right_key).unwrap(),
        arena.eq(left, one).unwrap(),
        arena.eq(right, two).unwrap(),
    ];

    let mut solver = IncrementalBvSolver::new();
    for &assertion in &assertions {
        solver
            .assert_simplifying_memory(&mut arena, assertion)
            .unwrap();
    }
    assert!(!solver.has_deferred_theory_assertions());
    assert_eq!(solver.retained_warm_array_uf_app_count(), 2);
    assert_eq!(solver.check(&arena).unwrap(), CheckResult::Unsat);
}

#[test]
fn direct_array_parameter_equality_guard_refutes_conflicting_results() {
    let mut arena = TermArena::new();
    let array_sort = Sort::Array {
        index: ArraySortKey::BitVec(4),
        element: ArraySortKey::BitVec(4),
    };
    let function = arena
        .declare_fun("warm_array_param_cong_f", &[array_sort], array_sort)
        .unwrap();
    let a = arena
        .array_var_with_sorts("warm_array_param_cong_a", Sort::BitVec(4), Sort::BitVec(4))
        .unwrap();
    let b = arena
        .array_var_with_sorts("warm_array_param_cong_b", Sort::BitVec(4), Sort::BitVec(4))
        .unwrap();
    let index = arena.bv_var("warm_array_param_cong_i", 4).unwrap();
    let one = arena.bv_const(4, 1).unwrap();
    let two = arena.bv_const(4, 2).unwrap();
    let fa = arena.apply(function, &[a]).unwrap();
    let fb = arena.apply(function, &[b]).unwrap();
    let left = arena.select(fa, index).unwrap();
    let right = arena.select(fb, index).unwrap();
    let same_arrays = arena.eq(a, b).unwrap();
    let assertions = [
        same_arrays,
        arena.eq(left, one).unwrap(),
        arena.eq(right, two).unwrap(),
    ];

    let mut solver = IncrementalBvSolver::new();
    for &assertion in &assertions {
        solver
            .assert_simplifying_memory(&mut arena, assertion)
            .unwrap();
    }
    assert!(!solver.has_deferred_theory_assertions());
    assert_eq!(solver.retained_warm_array_uf_app_count(), 2);
    assert_eq!(solver.check(&arena).unwrap(), CheckResult::Unsat);
}

fn application_parent_root(arena: &mut TermArena, count: usize) -> TermId {
    let array_sort = Sort::Array {
        index: ArraySortKey::BitVec(8),
        element: ArraySortKey::BitVec(8),
    };
    let function = arena
        .declare_fun("warm_array_uf_limit_f", &[Sort::BitVec(8)], array_sort)
        .unwrap();
    let index = arena.bv_var("warm_array_uf_limit_i", 8).unwrap();
    let zero = arena.bv_const(8, 0).unwrap();
    let mut root = arena.bool_const(true);
    for value in 0..count {
        let arg = arena.bv_const(8, value as u128).unwrap();
        let app = arena.apply(function, &[arg]).unwrap();
        let read = arena.select(app, index).unwrap();
        let assertion = arena.eq(read, zero).unwrap();
        root = arena.and(root, assertion).unwrap();
    }
    root
}

#[test]
fn array_application_parent_limit_is_exact_and_one_over_defers() {
    let mut at_limit = TermArena::new();
    let root = application_parent_root(&mut at_limit, 64);
    assert!(IncrementalBvSolver::term_supported_by_warm_abstraction(
        &at_limit, root
    ));
    let mut warm = IncrementalBvSolver::new();
    warm.assert_simplifying_memory(&mut at_limit, root).unwrap();
    assert!(!warm.has_deferred_theory_assertions());
    assert_eq!(warm.retained_warm_array_uf_app_count(), 64);

    let mut over_limit = TermArena::new();
    let root = application_parent_root(&mut over_limit, 65);
    assert!(!IncrementalBvSolver::term_supported_by_warm_abstraction(
        &over_limit,
        root
    ));
    let mut deferred = IncrementalBvSolver::new();
    deferred
        .assert_simplifying_memory(&mut over_limit, root)
        .unwrap();
    assert!(deferred.has_deferred_theory_assertions());
    assert_eq!(deferred.retained_warm_array_uf_app_count(), 0);
}

#[test]
fn unsupported_signatures_defer_without_partial_state() {
    let mut arena = TermArena::new();
    let array_sort = Sort::Array {
        index: ArraySortKey::BitVec(8),
        element: ArraySortKey::BitVec(8),
    };
    let int_function = arena
        .declare_fun("warm_array_uf_int_key", &[Sort::Int], array_sort)
        .unwrap();
    let int_arg = arena.int_var("warm_array_uf_int_arg").unwrap();
    let index = arena.bv_var("warm_array_uf_unsupported_i", 8).unwrap();
    let zero = arena.bv_const(8, 0).unwrap();
    let int_app = arena.apply(int_function, &[int_arg]).unwrap();
    let int_read = arena.select(int_app, index).unwrap();
    let int_root = arena.eq(int_read, zero).unwrap();
    assert!(!IncrementalBvSolver::term_supported_by_warm_abstraction(
        &arena, int_root
    ));
    let mut solver = IncrementalBvSolver::new();
    solver
        .assert_simplifying_memory(&mut arena, int_root)
        .unwrap();
    assert!(solver.has_deferred_theory_assertions());
    assert_eq!(solver.retained_warm_array_uf_app_count(), 0);

    let mut int_index_arena = TermArena::new();
    let int_index_sort = Sort::Array {
        index: ArraySortKey::Int,
        element: ArraySortKey::BitVec(8),
    };
    let function = int_index_arena
        .declare_fun(
            "warm_array_uf_int_index",
            &[Sort::BitVec(8)],
            int_index_sort,
        )
        .unwrap();
    let arg = int_index_arena
        .bv_var("warm_array_uf_int_index_arg", 8)
        .unwrap();
    let index = int_index_arena
        .int_var("warm_array_uf_int_index_i")
        .unwrap();
    let zero = int_index_arena.bv_const(8, 0).unwrap();
    let app = int_index_arena.apply(function, &[arg]).unwrap();
    let read = int_index_arena.select(app, index).unwrap();
    let root = int_index_arena.eq(read, zero).unwrap();
    assert!(!IncrementalBvSolver::term_supported_by_warm_abstraction(
        &int_index_arena,
        root
    ));
}

fn expected(seed: u64) -> Verdict {
    match seed % 8 {
        0 | 4 | 5 | 6 | 7 => Verdict::Unsat,
        _ => Verdict::Sat,
    }
}

fn build_case(seed: u64, arena: &mut TermArena) -> Vec<TermId> {
    let array_sort = Sort::Array {
        index: ArraySortKey::BitVec(3),
        element: ArraySortKey::BitVec(3),
    };
    let function = arena
        .declare_fun("warm_matrix_array_f", &[Sort::BitVec(3)], array_sort)
        .unwrap();
    let scalar = arena
        .declare_fun("warm_matrix_scalar_g", &[Sort::BitVec(3)], Sort::BitVec(3))
        .unwrap();
    let x = arena.bv_var("warm_matrix_array_x", 3).unwrap();
    let y = arena.bv_var("warm_matrix_array_y", 3).unwrap();
    let i = arena.bv_var("warm_matrix_array_i", 3).unwrap();
    let j = arena.bv_var("warm_matrix_array_j", 3).unwrap();
    let condition = arena.bool_var("warm_matrix_array_c").unwrap();
    let one = arena.bv_const(3, 1).unwrap();
    let two = arena.bv_const(3, 2).unwrap();
    let fx = arena.apply(function, &[x]).unwrap();
    let fy = arena.apply(function, &[y]).unwrap();
    let left = arena.select(fx, i).unwrap();
    let right = arena.select(fy, j).unwrap();
    let same_args = arena.eq(x, y).unwrap();
    let different_args = arena.not(same_args).unwrap();
    let same_indices = arena.eq(i, j).unwrap();
    let left_is_one = arena.eq(left, one).unwrap();
    let right_is_two = arena.eq(right, two).unwrap();

    match seed % 8 {
        0 => vec![same_args, same_indices, left_is_one, right_is_two],
        1 => vec![different_args, same_indices, left_is_one, right_is_two],
        2 => {
            let other_read = arena.select(fx, j).unwrap();
            vec![left_is_one, arena.eq(other_read, two).unwrap()]
        }
        3 => vec![same_args, left_is_one, right_is_two],
        4 => {
            let stored = arena.store(fx, i, one).unwrap();
            let read = arena.select(stored, j).unwrap();
            vec![same_indices, not_eq(arena, read, one)]
        }
        5 => {
            let chosen = arena.ite(condition, fx, fy).unwrap();
            let chosen_read = arena.select(chosen, i).unwrap();
            vec![condition, not_eq(arena, chosen_read, left)]
        }
        6 => {
            let bool_sort = Sort::Array {
                index: ArraySortKey::BitVec(3),
                element: ArraySortKey::Bool,
            };
            let predicate = arena
                .declare_fun("warm_matrix_bool_f", &[Sort::BitVec(3)], bool_sort)
                .unwrap();
            let px = arena.apply(predicate, &[x]).unwrap();
            let py = arena.apply(predicate, &[y]).unwrap();
            let pxi = arena.select(px, i).unwrap();
            let pyj = arena.select(py, j).unwrap();
            vec![same_args, same_indices, pxi, arena.not(pyj).unwrap()]
        }
        _ => {
            let gx = arena.apply(scalar, &[x]).unwrap();
            let gy = arena.apply(scalar, &[y]).unwrap();
            let fgx = arena.apply(function, &[gx]).unwrap();
            let fgy = arena.apply(function, &[gy]).unwrap();
            let nested_left = arena.select(fgx, i).unwrap();
            let nested_right = arena.select(fgy, j).unwrap();
            vec![
                same_args,
                same_indices,
                arena.eq(nested_left, one).unwrap(),
                arena.eq(nested_right, two).unwrap(),
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
    let function = FuncDecl::new("warm_matrix_array_f", &[&bv_sort], &array_sort);
    let scalar = FuncDecl::new("warm_matrix_scalar_g", &[&bv_sort], &bv_sort);
    let x = BV::new_const("warm_matrix_array_x", 3);
    let y = BV::new_const("warm_matrix_array_y", 3);
    let i = BV::new_const("warm_matrix_array_i", 3);
    let j = BV::new_const("warm_matrix_array_j", 3);
    let condition = Bool::new_const("warm_matrix_array_c");
    let one = BV::from_u64(1, 3);
    let two = BV::from_u64(2, 3);
    let fx = function.apply(&[&x]).as_array().unwrap();
    let fy = function.apply(&[&y]).as_array().unwrap();
    let left = fx.select(&i).as_bv().unwrap();
    let right = fy.select(&j).as_bv().unwrap();
    let same_args = x.eq(&y);
    let different_args = same_args.not();
    let same_indices = i.eq(&j);

    let assertions: Vec<Bool> = match seed % 8 {
        0 => vec![same_args, same_indices, left.eq(&one), right.eq(&two)],
        1 => vec![different_args, same_indices, left.eq(&one), right.eq(&two)],
        2 => vec![left.eq(&one), fx.select(&j).as_bv().unwrap().eq(&two)],
        3 => vec![same_args, left.eq(&one), right.eq(&two)],
        4 => vec![
            same_indices,
            fx.store(&i, &one)
                .select(&j)
                .as_bv()
                .unwrap()
                .eq(&one)
                .not(),
        ],
        5 => vec![
            condition.clone(),
            condition
                .ite(&fx, &fy)
                .select(&i)
                .as_bv()
                .unwrap()
                .eq(&left)
                .not(),
        ],
        6 => {
            let bool_sort = Z3Sort::bool();
            let bool_array_sort = Z3Sort::array(&bv_sort, &bool_sort);
            let predicate = FuncDecl::new("warm_matrix_bool_f", &[&bv_sort], &bool_array_sort);
            let px = predicate.apply(&[&x]).as_array().unwrap();
            let py = predicate.apply(&[&y]).as_array().unwrap();
            vec![
                same_args,
                same_indices,
                px.select(&i).as_bool().unwrap(),
                py.select(&j).as_bool().unwrap().not(),
            ]
        }
        _ => {
            let gx = scalar.apply(&[&x]).as_bv().unwrap();
            let gy = scalar.apply(&[&y]).as_bv().unwrap();
            let fgx = function.apply(&[&gx]).as_array().unwrap();
            let fgy = function.apply(&[&gy]).as_array().unwrap();
            vec![
                same_args,
                same_indices,
                fgx.select(&i).as_bv().unwrap().eq(&one),
                fgy.select(&j).as_bv().unwrap().eq(&two),
            ]
        }
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
