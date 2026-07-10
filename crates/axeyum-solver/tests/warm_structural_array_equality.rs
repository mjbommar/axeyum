//! Retained warm structural array equality gates for ADR-0090.

use std::time::Duration;

use axeyum_ir::{ArraySortKey, Sort, TermArena, TermId, Value, eval};
use axeyum_solver::{
    AssumptionOutcome, CheckResult, IncrementalBvSolver, SolverConfig, UnknownKind, check_auto,
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

fn array_sort(index_width: u32, element: ArraySortKey) -> Sort {
    Sort::Array {
        index: ArraySortKey::BitVec(index_width),
        element,
    }
}

fn array_var(arena: &mut TermArena, name: &str, sort: Sort) -> TermId {
    let Sort::Array { index, element } = sort else {
        panic!("expected array sort");
    };
    arena
        .array_var_with_sorts(name, index.to_sort(), element.to_sort())
        .unwrap()
}

fn not_eq(arena: &mut TermArena, left: TermId, right: TermId) -> TermId {
    let equal = arena.eq(left, right).unwrap();
    arena.not(equal).unwrap()
}

fn assert_sat_replays(arena: &TermArena, assertions: &[TermId], result: &CheckResult) {
    let CheckResult::Sat(model) = result else {
        panic!("expected sat, got {result:?}");
    };
    for &assertion in assertions {
        assert_eq!(
            eval(arena, assertion, &model.to_assignment()),
            Ok(Value::Bool(true)),
            "structural equality assertion #{} did not replay",
            assertion.index()
        );
    }
    for (symbol, _) in model.iter() {
        assert!(
            !arena.symbol(symbol).0.starts_with("!axeyum_warm_"),
            "private warm owner leaked"
        );
    }
}

#[test]
fn no_read_store_constant_and_store_store_equalities_replay_total_models() {
    let mut arena = TermArena::new();
    let sort = array_sort(8, ArraySortKey::BitVec(8));
    let a = array_var(&mut arena, "warm_structural_no_read_a", sort);
    let b = array_var(&mut arena, "warm_structural_no_read_b", sort);
    let index = arena.bv_var("warm_structural_no_read_i", 8).unwrap();
    let one = arena.bv_const(8, 1).unwrap();
    let store_a = arena.store(a, index, one).unwrap();
    let store_b = arena.store(b, index, one).unwrap();
    let eq_store_symbol = arena.eq(store_a, b).unwrap();
    let eq_store_store = arena.eq(store_a, store_b).unwrap();

    let mut solver = IncrementalBvSolver::new();
    solver
        .assert_simplifying_memory(&mut arena, eq_store_symbol)
        .unwrap();
    solver
        .assert_simplifying_memory(&mut arena, eq_store_store)
        .unwrap();
    assert!(!solver.has_deferred_theory_assertions());
    assert_eq!(solver.retained_warm_structural_array_owner_count(), 2);
    assert_eq!(solver.retained_warm_array_equality_probe_count(), 2);
    let result = solver.check(&arena).unwrap();
    assert_sat_replays(&arena, &[eq_store_symbol, eq_store_store], &result);

    let mut constant_arena = TermArena::new();
    let a = array_var(&mut constant_arena, "warm_structural_constant_a", sort);
    let zero = constant_arena.bv_const(8, 0).unwrap();
    let constant = constant_arena.const_array(8, zero).unwrap();
    let eq_constant = constant_arena.eq(a, constant).unwrap();
    let mut constant_solver = IncrementalBvSolver::new();
    constant_solver
        .assert_simplifying_memory(&mut constant_arena, eq_constant)
        .unwrap();
    let result = constant_solver.check(&constant_arena).unwrap();
    assert_sat_replays(&constant_arena, &[eq_constant], &result);
}

#[test]
fn unequal_constants_and_store_write_conflicts_are_unsat_in_both_orders() {
    let mut arena = TermArena::new();
    let sort = array_sort(8, ArraySortKey::BitVec(8));
    let a = array_var(&mut arena, "warm_structural_conflict_a", sort);
    let b = array_var(&mut arena, "warm_structural_conflict_b", sort);
    let index = arena.bv_var("warm_structural_conflict_i", 8).unwrap();
    let zero = arena.bv_const(8, 0).unwrap();
    let one = arena.bv_const(8, 1).unwrap();
    let constant_zero = arena.const_array(8, zero).unwrap();
    let constant_one = arena.const_array(8, one).unwrap();
    let unequal_constants = arena.eq(constant_zero, constant_one).unwrap();

    let mut constants = IncrementalBvSolver::new();
    constants
        .assert_simplifying_memory(&mut arena, unequal_constants)
        .unwrap();
    assert!(matches!(
        constants.check(&arena).unwrap(),
        CheckResult::Unsat
    ));

    let stored = arena.store(a, index, one).unwrap();
    let equality = arena.eq(stored, b).unwrap();
    let read_b = arena.select(b, index).unwrap();
    let conflict = not_eq(&mut arena, read_b, one);
    for equality_first in [false, true] {
        let mut solver = IncrementalBvSolver::new();
        let roots = if equality_first {
            [equality, conflict]
        } else {
            [conflict, equality]
        };
        for root in roots {
            solver.assert_simplifying_memory(&mut arena, root).unwrap();
        }
        assert!(matches!(solver.check(&arena).unwrap(), CheckResult::Unsat));
    }
}

#[test]
fn selected_ite_equality_conflicts_with_branch_disequality() {
    let mut arena = TermArena::new();
    let sort = array_sort(8, ArraySortKey::BitVec(8));
    let a = array_var(&mut arena, "warm_structural_ite_a", sort);
    let b = array_var(&mut arena, "warm_structural_ite_b", sort);
    let d = array_var(&mut arena, "warm_structural_ite_d", sort);
    let condition = arena.bool_var("warm_structural_ite_c").unwrap();
    let choice = arena.ite(condition, a, b).unwrap();
    let equality = arena.eq(choice, d).unwrap();
    let a_distinct = not_eq(&mut arena, a, d);

    let mut selected = IncrementalBvSolver::new();
    for root in [condition, equality, a_distinct] {
        selected
            .assert_simplifying_memory(&mut arena, root)
            .unwrap();
    }
    assert!(matches!(
        selected.check(&arena).unwrap(),
        CheckResult::Unsat
    ));

    let mut unselected_arena = TermArena::new();
    let a = array_var(&mut unselected_arena, "warm_structural_ite2_a", sort);
    let b = array_var(&mut unselected_arena, "warm_structural_ite2_b", sort);
    let d = array_var(&mut unselected_arena, "warm_structural_ite2_d", sort);
    let condition = unselected_arena.bool_var("warm_structural_ite2_c").unwrap();
    let choice = unselected_arena.ite(condition, a, b).unwrap();
    let equality = unselected_arena.eq(choice, d).unwrap();
    let b_distinct = not_eq(&mut unselected_arena, b, d);
    let mut unselected = IncrementalBvSolver::new();
    for root in [condition, equality, b_distinct] {
        unselected
            .assert_simplifying_memory(&mut unselected_arena, root)
            .unwrap();
    }
    let result = unselected.check(&unselected_arena).unwrap();
    assert_sat_replays(
        &unselected_arena,
        &[condition, equality, b_distinct],
        &result,
    );
}

#[test]
fn array_result_uf_composes_with_structural_owner_and_stays_private() {
    let mut arena = TermArena::new();
    let sort = array_sort(8, ArraySortKey::BitVec(8));
    let f = arena
        .declare_fun("warm_structural_f", &[Sort::BitVec(8)], sort)
        .unwrap();
    let x = arena.bv_var("warm_structural_f_x", 8).unwrap();
    let a = array_var(&mut arena, "warm_structural_f_a", sort);
    let index = arena.bv_var("warm_structural_f_i", 8).unwrap();
    let value = arena.bv_var("warm_structural_f_v", 8).unwrap();
    let fx = arena.apply(f, &[x]).unwrap();
    let stored = arena.store(a, index, value).unwrap();
    let equality = arena.eq(fx, stored).unwrap();

    let mut solver = IncrementalBvSolver::new();
    solver
        .assert_simplifying_memory(&mut arena, equality)
        .unwrap();
    assert_eq!(solver.retained_warm_array_uf_app_count(), 1);
    assert_eq!(solver.retained_warm_structural_array_owner_count(), 1);
    let result = solver.check(&arena).unwrap();
    assert_sat_replays(&arena, &[equality], &result);
    let CheckResult::Sat(model) = result else {
        unreachable!()
    };
    assert!(model.function(f).is_some());
}

#[test]
fn structural_equality_scopes_and_one_shot_cores_are_user_facing() {
    let mut arena = TermArena::new();
    let sort = array_sort(8, ArraySortKey::BitVec(8));
    let a = array_var(&mut arena, "warm_structural_scope_a", sort);
    let b = array_var(&mut arena, "warm_structural_scope_b", sort);
    let index = arena.bv_var("warm_structural_scope_i", 8).unwrap();
    let one = arena.bv_const(8, 1).unwrap();
    let stored = arena.store(a, index, one).unwrap();
    let equality = arena.eq(stored, b).unwrap();
    let read = arena.select(b, index).unwrap();
    let conflict = not_eq(&mut arena, read, one);

    let mut solver = IncrementalBvSolver::new();
    solver
        .assert_simplifying_memory(&mut arena, conflict)
        .unwrap();
    solver.push().unwrap();
    solver
        .assert_simplifying_memory(&mut arena, equality)
        .unwrap();
    assert!(matches!(solver.check(&arena).unwrap(), CheckResult::Unsat));
    assert!(solver.pop());
    assert!(matches!(solver.check(&arena).unwrap(), CheckResult::Sat(_)));

    let outcome = solver
        .check_assuming_core_simplifying_memory(&mut arena, &[equality])
        .unwrap();
    let AssumptionOutcome::Unsat { core } = outcome else {
        panic!("expected one-shot structural equality conflict");
    };
    assert_eq!(core, vec![equality]);
}

#[test]
fn bool_elements_and_bv256_components_replay() {
    let mut arena = TermArena::new();
    let bool_sort = array_sort(256, ArraySortKey::Bool);
    let a = array_var(&mut arena, "warm_structural_wide_a", bool_sort);
    let b = array_var(&mut arena, "warm_structural_wide_b", bool_sort);
    let index = arena.bv_var("warm_structural_wide_i", 256).unwrap();
    let value = arena.bool_var("warm_structural_wide_v").unwrap();
    let stored = arena.store(a, index, value).unwrap();
    let equality = arena.eq(stored, b).unwrap();

    let mut solver = IncrementalBvSolver::new();
    solver
        .assert_simplifying_memory(&mut arena, equality)
        .unwrap();
    let result = solver.check(&arena).unwrap();
    assert_sat_replays(&arena, &[equality], &result);

    let mut wide_arena = TermArena::new();
    let bv_sort = array_sort(256, ArraySortKey::BitVec(256));
    let x = array_var(&mut wide_arena, "warm_structural_wide_x", bv_sort);
    let y = array_var(&mut wide_arena, "warm_structural_wide_y", bv_sort);
    let index = wide_arena.bv_var("warm_structural_wide_i", 256).unwrap();
    let wide_value = wide_arena
        .bv_var("warm_structural_wide_value", 256)
        .unwrap();
    let stored = wide_arena.store(x, index, wide_value).unwrap();
    let equality = wide_arena.eq(stored, y).unwrap();
    let mut wide = IncrementalBvSolver::new();
    wide.assert_simplifying_memory(&mut wide_arena, equality)
        .unwrap();
    let result = wide.check(&wide_arena).unwrap();
    assert_sat_replays(&wide_arena, &[equality], &result);
}

fn deep_positive_equality(arena: &mut TermArena, depth: usize) -> TermId {
    let sort = array_sort(8, ArraySortKey::BitVec(8));
    let base = array_var(arena, "warm_structural_limit_a", sort);
    let other = array_var(arena, "warm_structural_limit_b", sort);
    let index = arena.bv_var("warm_structural_limit_i", 8).unwrap();
    let value = arena.bv_const(8, 1).unwrap();
    let mut parent = base;
    for _ in 0..depth {
        parent = arena.store(parent, index, value).unwrap();
    }
    arena.eq(parent, other).unwrap()
}

#[test]
fn exact_depth_observation_budget_and_timeout_boundaries_are_clean() {
    let mut nested_arena = TermArena::new();
    let sort = array_sort(8, ArraySortKey::BitVec(8));
    let a = array_var(&mut nested_arena, "warm_structural_nested_a", sort);
    let b = array_var(&mut nested_arena, "warm_structural_nested_b", sort);
    let index = nested_arena.bv_var("warm_structural_nested_i", 8).unwrap();
    let value = nested_arena.bv_const(8, 1).unwrap();
    let stored = nested_arena.store(a, index, value).unwrap();
    let equality = nested_arena.eq(stored, b).unwrap();
    let flag = nested_arena
        .bool_var("warm_structural_nested_flag")
        .unwrap();
    let nested = nested_arena.or(flag, equality).unwrap();
    assert!(IncrementalBvSolver::term_supported_by_warm_abstraction(
        &nested_arena,
        nested
    ));
    let mut nested_solver = IncrementalBvSolver::new();
    nested_solver
        .assert_simplifying_memory(&mut nested_arena, nested)
        .unwrap();
    assert!(!nested_solver.has_deferred_theory_assertions());
    assert_eq!(nested_solver.retained_warm_array_relation_flag_count(), 1);
    assert_eq!(
        nested_solver.retained_warm_structural_array_owner_count(),
        1
    );
    assert_eq!(nested_solver.retained_warm_array_equality_probe_count(), 1);
    let result = nested_solver.check(&nested_arena).unwrap();
    assert_sat_replays(&nested_arena, &[nested], &result);

    let mut at_limit_arena = TermArena::new();
    let equality = deep_positive_equality(&mut at_limit_arena, 256);
    assert!(IncrementalBvSolver::term_supported_by_warm_abstraction(
        &at_limit_arena,
        equality
    ));

    let mut over_limit_arena = TermArena::new();
    let equality = deep_positive_equality(&mut over_limit_arena, 257);
    assert!(!IncrementalBvSolver::term_supported_by_warm_abstraction(
        &over_limit_arena,
        equality
    ));
    let mut over_limit = IncrementalBvSolver::new();
    over_limit
        .assert_simplifying_memory(&mut over_limit_arena, equality)
        .unwrap();
    assert!(over_limit.has_deferred_theory_assertions());
    assert_eq!(over_limit.retained_warm_structural_array_owner_count(), 0);
    assert_eq!(over_limit.retained_warm_array_equality_probe_count(), 0);

    let mut budget_arena = TermArena::new();
    let sort = array_sort(16, ArraySortKey::BitVec(8));
    let a = array_var(&mut budget_arena, "warm_structural_budget_a", sort);
    let b = array_var(&mut budget_arena, "warm_structural_budget_b", sort);
    let write_index = budget_arena.bv_const(16, 511).unwrap();
    let zero = budget_arena.bv_const(8, 0).unwrap();
    let one = budget_arena.bv_const(8, 1).unwrap();
    let stored = budget_arena.store(a, write_index, one).unwrap();
    let equality = budget_arena.eq(stored, b).unwrap();
    let mut budget = IncrementalBvSolver::new();
    budget
        .assert_simplifying_memory(&mut budget_arena, equality)
        .unwrap();
    let owner_count = budget.retained_warm_structural_array_owner_count();
    let probe_count = budget.retained_warm_array_equality_probe_count();
    let mut combined = budget_arena.bool_const(true);
    for raw_index in 0..257u128 {
        let index = budget_arena.bv_const(16, raw_index).unwrap();
        let read = budget_arena.select(b, index).unwrap();
        let root = budget_arena.eq(read, zero).unwrap();
        combined = budget_arena.and(combined, root).unwrap();
    }
    budget
        .assert_simplifying_memory(&mut budget_arena, combined)
        .unwrap();
    assert!(budget.has_deferred_theory_assertions());
    assert_eq!(
        budget.retained_warm_structural_array_owner_count(),
        owner_count
    );
    assert_eq!(
        budget.retained_warm_array_equality_probe_count(),
        probe_count
    );

    let mut timeout_arena = TermArena::new();
    let equality = deep_positive_equality(&mut timeout_arena, 1);
    let config = SolverConfig {
        timeout: Some(Duration::ZERO),
        ..SolverConfig::default()
    };
    let mut timeout = IncrementalBvSolver::with_config(config);
    timeout
        .assert_simplifying_memory(&mut timeout_arena, equality)
        .unwrap();
    let CheckResult::Unknown(reason) = timeout.check(&timeout_arena).unwrap() else {
        panic!("zero-deadline structural equality must return unknown");
    };
    assert_eq!(reason.kind, UnknownKind::Timeout);
}

fn expected(seed: u64) -> Verdict {
    match seed % 8 {
        1 | 2 | 3 | 7 => Verdict::Unsat,
        _ => Verdict::Sat,
    }
}

#[allow(clippy::many_single_char_names)]
fn build_case(seed: u64, arena: &mut TermArena) -> Vec<TermId> {
    let sort = array_sort(3, ArraySortKey::BitVec(3));
    let a = array_var(arena, "warm_structural_matrix_a", sort);
    let b = array_var(arena, "warm_structural_matrix_b", sort);
    let d = array_var(arena, "warm_structural_matrix_d", sort);
    let condition = arena.bool_var("warm_structural_matrix_c").unwrap();
    let index = arena.bv_var("warm_structural_matrix_i", 3).unwrap();
    let x = arena.bv_var("warm_structural_matrix_x", 3).unwrap();
    let zero = arena.bv_const(3, 0).unwrap();
    let one = arena.bv_const(3, 1).unwrap();
    let two = arena.bv_const(3, 2).unwrap();
    let f = arena
        .declare_fun("warm_structural_matrix_f", &[Sort::BitVec(3)], sort)
        .unwrap();
    match seed % 8 {
        0 => {
            let stored = arena.store(a, index, one).unwrap();
            vec![arena.eq(stored, b).unwrap()]
        }
        1 => {
            let stored = arena.store(a, index, one).unwrap();
            let equality = arena.eq(stored, b).unwrap();
            let read = arena.select(b, index).unwrap();
            vec![equality, not_eq(arena, read, one)]
        }
        2 => {
            let zero_array = arena.const_array(3, zero).unwrap();
            let one_array = arena.const_array(3, one).unwrap();
            vec![arena.eq(zero_array, one_array).unwrap()]
        }
        3 => {
            let choice = arena.ite(condition, a, b).unwrap();
            vec![condition, arena.eq(choice, d).unwrap(), not_eq(arena, a, d)]
        }
        4 => {
            let choice = arena.ite(condition, a, b).unwrap();
            vec![condition, arena.eq(choice, d).unwrap(), not_eq(arena, b, d)]
        }
        5 => {
            let left = arena.store(a, index, one).unwrap();
            let right = arena.store(b, index, one).unwrap();
            vec![arena.eq(left, right).unwrap()]
        }
        6 => {
            let fx = arena.apply(f, &[x]).unwrap();
            let stored = arena.store(a, index, two).unwrap();
            vec![arena.eq(fx, stored).unwrap()]
        }
        _ => {
            let stored = arena.store(a, index, one).unwrap();
            let first = arena.eq(stored, b).unwrap();
            let second = arena.eq(b, d).unwrap();
            let read = arena.select(d, index).unwrap();
            vec![first, second, not_eq(arena, read, one)]
        }
    }
}

#[test]
fn structural_matrix_matches_check_auto_and_replays() {
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
        if matches!(result, CheckResult::Sat(_)) {
            assert_sat_replays(&warm_arena, &assertions, &result);
        }

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
#[allow(clippy::many_single_char_names)]
fn z3_verdict(seed: u64) -> Verdict {
    let bv_sort = Z3Sort::bitvector(3);
    let array_sort = Z3Sort::array(&bv_sort, &bv_sort);
    let a = Array::new_const("warm_structural_matrix_a", &bv_sort, &bv_sort);
    let b = Array::new_const("warm_structural_matrix_b", &bv_sort, &bv_sort);
    let d = Array::new_const("warm_structural_matrix_d", &bv_sort, &bv_sort);
    let condition = Bool::new_const("warm_structural_matrix_c");
    let index = BV::new_const("warm_structural_matrix_i", 3);
    let x = BV::new_const("warm_structural_matrix_x", 3);
    let zero = BV::from_u64(0, 3);
    let one = BV::from_u64(1, 3);
    let two = BV::from_u64(2, 3);
    let f = FuncDecl::new("warm_structural_matrix_f", &[&bv_sort], &array_sort);
    let assertions: Vec<Bool> = match seed % 8 {
        0 => vec![a.store(&index, &one).eq(&b)],
        1 => vec![
            a.store(&index, &one).eq(&b),
            b.select(&index).as_bv().unwrap().eq(&one).not(),
        ],
        2 => vec![Array::const_array(&bv_sort, &zero).eq(Array::const_array(&bv_sort, &one))],
        3 => vec![
            condition.clone(),
            condition.ite(&a, &b).eq(&d),
            a.eq(&d).not(),
        ],
        4 => vec![
            condition.clone(),
            condition.ite(&a, &b).eq(&d),
            b.eq(&d).not(),
        ],
        5 => vec![a.store(&index, &one).eq(b.store(&index, &one))],
        6 => vec![f.apply(&[&x]).as_array().unwrap().eq(a.store(&index, &two))],
        _ => vec![
            a.store(&index, &one).eq(&b),
            b.eq(&d),
            d.select(&index).as_bv().unwrap().eq(&one).not(),
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
fn structural_matrix_matches_z3() {
    for seed in 0..64 {
        assert_eq!(z3_verdict(seed), expected(seed), "Z3 seed {seed}");
    }
}
