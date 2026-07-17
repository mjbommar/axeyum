//! Retained warm Boolean array-relation flag gates for ADR-0091.
#![cfg(feature = "full")]

use axeyum_ir::{ArraySortKey, Sort, TermArena, TermId, Value, eval};
use axeyum_solver::{AssumptionOutcome, CheckResult, IncrementalBvSolver};

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

fn bv_array_sort(width: u32) -> Sort {
    Sort::Array {
        index: ArraySortKey::BitVec(width),
        element: ArraySortKey::BitVec(width),
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
            "relation-flag assertion #{} did not replay",
            assertion.index()
        );
    }
    for (symbol, _) in model.iter() {
        assert!(
            !arena.symbol(symbol).0.starts_with("!axeyum_warm_"),
            "private warm relation flag leaked"
        );
    }
}

#[test]
fn nested_relation_flag_true_branch_uses_structural_equality() {
    let mut arena = TermArena::new();
    let sort = bv_array_sort(8);
    let a = array_var(&mut arena, "warm_relation_flag_true_a", sort);
    let b = array_var(&mut arena, "warm_relation_flag_true_b", sort);
    let index = arena.bv_var("warm_relation_flag_true_i", 8).unwrap();
    let one = arena.bv_const(8, 1).unwrap();
    let stored = arena.store(a, index, one).unwrap();
    let equality = arena.eq(stored, b).unwrap();
    let guard = arena.bool_var("warm_relation_flag_true_g").unwrap();
    let not_guard = arena.not(guard).unwrap();
    let relation_or_guard = arena.or(guard, equality).unwrap();
    let read_b = arena.select(b, index).unwrap();
    let conflict = not_eq(&mut arena, read_b, one);

    let mut solver = IncrementalBvSolver::new();
    for root in [not_guard, relation_or_guard, conflict] {
        solver.assert_simplifying_memory(&mut arena, root).unwrap();
    }
    assert!(!solver.has_deferred_theory_assertions());
    assert_eq!(solver.retained_warm_array_relation_flag_count(), 1);
    assert!(matches!(solver.check(&arena).unwrap(), CheckResult::Unsat));
}

#[test]
fn nested_relation_flag_true_branch_projects_total_model_without_reads() {
    let mut arena = TermArena::new();
    let sort = bv_array_sort(8);
    let a = array_var(&mut arena, "warm_relation_flag_model_a", sort);
    let b = array_var(&mut arena, "warm_relation_flag_model_b", sort);
    let index = arena.bv_var("warm_relation_flag_model_i", 8).unwrap();
    let one = arena.bv_const(8, 1).unwrap();
    let stored = arena.store(a, index, one).unwrap();
    let equality = arena.eq(stored, b).unwrap();
    let guard = arena.bool_var("warm_relation_flag_model_g").unwrap();
    let not_guard = arena.not(guard).unwrap();
    let relation_or_guard = arena.or(guard, equality).unwrap();

    let mut solver = IncrementalBvSolver::new();
    for root in [not_guard, relation_or_guard] {
        solver.assert_simplifying_memory(&mut arena, root).unwrap();
    }
    assert!(!solver.has_deferred_theory_assertions());
    let result = solver.check(&arena).unwrap();
    assert_eq!(verdict(&result), Verdict::Sat);
    assert_sat_replays(&arena, &[not_guard, relation_or_guard], &result);
}

#[test]
fn nested_relation_flag_false_branch_uses_guarded_diff_witness() {
    let mut arena = TermArena::new();
    let sort = bv_array_sort(8);
    let a = array_var(&mut arena, "warm_relation_flag_false_a", sort);
    let b = array_var(&mut arena, "warm_relation_flag_false_b", sort);
    let equality = arena.eq(a, b).unwrap();
    let disequality = arena.not(equality).unwrap();
    let guard = arena.bool_var("warm_relation_flag_false_g").unwrap();
    let not_guard = arena.not(guard).unwrap();
    let relation_or_guard = arena.or(guard, disequality).unwrap();

    let mut solver = IncrementalBvSolver::new();
    for root in [not_guard, relation_or_guard] {
        solver.assert_simplifying_memory(&mut arena, root).unwrap();
    }
    assert!(!solver.has_deferred_theory_assertions());
    assert_eq!(solver.retained_warm_array_relation_flag_count(), 1);
    assert_eq!(solver.retained_warm_array_diff_witness_count(), 1);
    let result = solver.check(&arena).unwrap();
    assert_eq!(verdict(&result), Verdict::Sat);
    assert_sat_replays(&arena, &[not_guard, relation_or_guard], &result);
}

#[test]
fn relation_flag_false_branch_conflicts_with_active_equality() {
    let mut arena = TermArena::new();
    let sort = bv_array_sort(8);
    let a = array_var(&mut arena, "warm_relation_flag_conflict_a", sort);
    let b = array_var(&mut arena, "warm_relation_flag_conflict_b", sort);
    let equality = arena.eq(a, b).unwrap();
    let disequality = arena.not(equality).unwrap();
    let guard = arena.bool_var("warm_relation_flag_conflict_g").unwrap();
    let not_guard = arena.not(guard).unwrap();
    let relation_or_guard = arena.or(guard, disequality).unwrap();

    let mut solver = IncrementalBvSolver::new();
    for root in [equality, not_guard, relation_or_guard] {
        solver.assert_simplifying_memory(&mut arena, root).unwrap();
    }
    assert!(!solver.has_deferred_theory_assertions());
    assert!(matches!(solver.check(&arena).unwrap(), CheckResult::Unsat));
}

#[test]
fn relation_flags_are_scoped_and_one_shot_cores_are_user_facing() {
    let mut arena = TermArena::new();
    let sort = bv_array_sort(4);
    let a = array_var(&mut arena, "warm_relation_flag_scope_a", sort);
    let b = array_var(&mut arena, "warm_relation_flag_scope_b", sort);
    let equality = arena.eq(a, b).unwrap();
    let disequality = arena.not(equality).unwrap();
    let guard = arena.bool_var("warm_relation_flag_scope_g").unwrap();
    let not_guard = arena.not(guard).unwrap();
    let relation_or_guard = arena.or(guard, disequality).unwrap();

    let mut solver = IncrementalBvSolver::new();
    solver
        .assert_simplifying_memory(&mut arena, equality)
        .unwrap();
    solver.push().unwrap();
    solver
        .assert_simplifying_memory(&mut arena, not_guard)
        .unwrap();
    solver
        .assert_simplifying_memory(&mut arena, relation_or_guard)
        .unwrap();
    assert!(matches!(solver.check(&arena).unwrap(), CheckResult::Unsat));
    assert!(solver.pop());
    assert_eq!(verdict(&solver.check(&arena).unwrap()), Verdict::Sat);

    let outcome = solver
        .check_assuming_core_simplifying_memory(&mut arena, &[not_guard, relation_or_guard])
        .unwrap();
    let AssumptionOutcome::Unsat { core } = outcome else {
        panic!("expected relation-flag one-shot conflict");
    };
    assert!(
        core.iter()
            .all(|term| [not_guard, relation_or_guard].contains(term))
    );
}
