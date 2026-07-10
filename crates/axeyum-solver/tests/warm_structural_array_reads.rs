//! Retained incremental structural-array read gates for ADR-0086.

use axeyum_ir::{Sort, TermArena, TermId, Value, eval};
use axeyum_solver::{CheckResult, IncrementalBvSolver, SolverConfig, check_auto};
#[cfg(feature = "z3")]
use z3::ast::{Array, BV, Bool};
#[cfg(feature = "z3")]
use z3::{SatResult, Solver, Sort as Z3Sort};

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
            eval(arena, assertion, &model.to_assignment()).unwrap(),
            Value::Bool(true),
            "warm SAT model must replay original assertion #{}",
            assertion.index()
        );
    }
}

#[test]
fn structural_store_definition_is_retained_and_scoped_roots_pop() {
    let mut arena = TermArena::new();
    let array = arena
        .array_var_with_sorts("warm_retained_a", Sort::BitVec(8), Sort::BitVec(8))
        .unwrap();
    let write_index = arena.bv_var("warm_retained_wi", 8).unwrap();
    let read_index = arena.bv_var("warm_retained_ri", 8).unwrap();
    let zero = arena.bv_const(8, 0).unwrap();
    let one = arena.bv_const(8, 1).unwrap();
    let base_read = arena.select(array, read_index).unwrap();
    let stored = arena.store(array, write_index, one).unwrap();
    let loaded = arena.select(stored, read_index).unwrap();
    let base_is_zero = arena.eq(base_read, zero).unwrap();
    let loaded_is_zero = arena.eq(loaded, zero).unwrap();
    let hit = arena.eq(write_index, read_index).unwrap();

    let mut solver = IncrementalBvSolver::new();
    solver
        .assert_simplifying_memory(&mut arena, base_is_zero)
        .unwrap();
    solver
        .assert_simplifying_memory(&mut arena, loaded_is_zero)
        .unwrap();
    assert!(!solver.has_deferred_theory_assertions());
    assert_eq!(solver.retained_warm_structural_read_count(), 1);
    assert_eq!(solver.retained_warm_structural_definition_count(), 1);
    assert!(solver.retained_warm_array_read_count() >= 2);

    let first = solver.check(&arena).unwrap();
    assert_eq!(verdict(&first), Verdict::Sat);
    assert_replays(&arena, &[base_is_zero, loaded_is_zero], &first);
    let clauses = solver.encoded_clause_count();
    let variables = solver.encoded_variable_count();
    let definitions = solver.retained_warm_structural_definition_count();
    let reads = solver.retained_warm_array_read_count();
    assert_eq!(verdict(&solver.check(&arena).unwrap()), Verdict::Sat);
    assert_eq!(solver.encoded_clause_count(), clauses);
    assert_eq!(solver.encoded_variable_count(), variables);
    assert_eq!(
        solver.retained_warm_structural_definition_count(),
        definitions
    );
    assert_eq!(solver.retained_warm_array_read_count(), reads);

    solver.push().unwrap();
    solver.assert(&arena, hit).unwrap();
    assert_eq!(solver.check(&arena).unwrap(), CheckResult::Unsat);
    assert!(solver.pop());
    let after_pop = solver.check(&arena).unwrap();
    assert_eq!(verdict(&after_pop), Verdict::Sat);
    assert_replays(&arena, &[base_is_zero, loaded_is_zero], &after_pop);
    assert_eq!(
        solver.retained_warm_structural_definition_count(),
        definitions
    );
}

#[test]
fn opposite_one_shot_branches_reuse_structural_definitions() {
    let mut arena = TermArena::new();
    let array = arena
        .array_var_with_sorts("warm_branch_a", Sort::BitVec(8), Sort::BitVec(8))
        .unwrap();
    let write_index = arena.bv_var("warm_branch_wi", 8).unwrap();
    let read_index = arena.bv_var("warm_branch_ri", 8).unwrap();
    let one = arena.bv_const(8, 1).unwrap();
    let stored = arena.store(array, write_index, one).unwrap();
    let loaded = arena.select(stored, read_index).unwrap();
    let hit = arena.eq(write_index, read_index).unwrap();
    let loaded_is_one = arena.eq(loaded, one).unwrap();
    let loaded_is_not_one = arena.not(loaded_is_one).unwrap();

    let mut solver = IncrementalBvSolver::new();
    solver.assert(&arena, hit).unwrap();
    let positive = solver
        .check_assuming_simplifying_memory(&mut arena, &[loaded_is_one])
        .unwrap();
    assert_eq!(verdict(&positive), Verdict::Sat);
    assert_replays(&arena, &[hit, loaded_is_one], &positive);
    let definitions = solver.retained_warm_structural_definition_count();
    let reads = solver.retained_warm_array_read_count();
    assert_eq!(definitions, 1);

    assert_eq!(
        solver
            .check_assuming_simplifying_memory(&mut arena, &[loaded_is_not_one])
            .unwrap(),
        CheckResult::Unsat
    );
    assert_eq!(
        solver.retained_warm_structural_definition_count(),
        definitions
    );
    assert_eq!(solver.retained_warm_array_read_count(), reads);
    assert_eq!(verdict(&solver.check(&arena).unwrap()), Verdict::Sat);
}

#[test]
fn constant_ite_nested_and_bool_reads_stay_warm() {
    let mut arena = TermArena::new();
    let flag = arena.bool_var("warm_structural_flag").unwrap();
    let index = arena.bv_var("warm_structural_index", 4).unwrap();
    let zero = arena.bv_const(4, 0).unwrap();
    let one = arena.bv_const(4, 1).unwrap();
    let zero_array = arena.const_array(4, zero).unwrap();
    let one_array = arena.const_array(4, one).unwrap();
    let chosen = arena.ite(flag, zero_array, one_array).unwrap();
    let stored = arena.store(chosen, index, one).unwrap();
    let loaded = arena.select(stored, index).unwrap();
    let impossible = not_eq(&mut arena, loaded, one);

    let bool_default = arena.bool_const(false);
    let bool_array = arena
        .const_array_with_index_sort(Sort::BitVec(4), bool_default)
        .unwrap();
    let bool_stored = arena.store(bool_array, index, flag).unwrap();
    let bool_loaded = arena.select(bool_stored, index).unwrap();
    let bool_mismatch = not_eq(&mut arena, bool_loaded, flag);

    let mut solver = IncrementalBvSolver::new();
    solver
        .assert_simplifying_memory(&mut arena, impossible)
        .unwrap();
    assert_eq!(solver.check(&arena).unwrap(), CheckResult::Unsat);
    assert!(!solver.has_deferred_theory_assertions());

    let mut bool_solver = IncrementalBvSolver::new();
    bool_solver
        .assert_simplifying_memory(&mut arena, bool_mismatch)
        .unwrap();
    assert_eq!(bool_solver.check(&arena).unwrap(), CheckResult::Unsat);
    assert!(!bool_solver.has_deferred_theory_assertions());

    let chosen_read = arena.select(chosen, index).unwrap();
    let chosen_is_zero = arena.eq(chosen_read, zero).unwrap();
    let mut ite_solver = IncrementalBvSolver::new();
    ite_solver.assert(&arena, flag).unwrap();
    ite_solver
        .assert_simplifying_memory(&mut arena, chosen_is_zero)
        .unwrap();
    let result = ite_solver.check(&arena).unwrap();
    assert_eq!(verdict(&result), Verdict::Sat);
    assert_replays(&arena, &[flag, chosen_is_zero], &result);
    assert!(ite_solver.retained_warm_structural_read_count() >= 3);
}

fn build_store_depth(arena: &mut TermArena, depth: usize) -> TermId {
    let mut array = arena
        .array_var_with_sorts("warm_depth_base", Sort::BitVec(8), Sort::BitVec(8))
        .unwrap();
    let value = arena.bv_const(8, 1).unwrap();
    for step in 0..depth {
        let index = arena
            .bv_var(&format!("warm_depth_index_{step}"), 8)
            .unwrap();
        array = arena.store(array, index, value).unwrap();
    }
    let read_index = arena.bv_var("warm_depth_read", 8).unwrap();
    arena.select(array, read_index).unwrap()
}

fn build_ite_tree(arena: &mut TermArena, leaf_count: usize) -> TermId {
    let mut level = (0..leaf_count)
        .map(|leaf| {
            arena
                .array_var_with_sorts(
                    &format!("warm_node_leaf_{leaf}"),
                    Sort::BitVec(4),
                    Sort::BitVec(4),
                )
                .unwrap()
        })
        .collect::<Vec<_>>();
    let mut node = 0usize;
    while level.len() > 1 {
        let mut next = Vec::with_capacity(level.len() / 2);
        for pair in level.chunks_exact(2) {
            let condition = arena.bool_var(&format!("warm_node_cond_{node}")).unwrap();
            node += 1;
            next.push(arena.ite(condition, pair[0], pair[1]).unwrap());
        }
        level = next;
    }
    level[0]
}

#[test]
fn structural_admission_limits_are_exact_and_over_limit_defers() {
    let mut at_depth = TermArena::new();
    let read = build_store_depth(&mut at_depth, 256);
    let zero = at_depth.bv_const(8, 0).unwrap();
    let root = at_depth.eq(read, zero).unwrap();
    assert!(IncrementalBvSolver::term_supported_by_warm_abstraction(
        &at_depth, root
    ));

    let mut over_depth = TermArena::new();
    let read = build_store_depth(&mut over_depth, 257);
    let zero = over_depth.bv_const(8, 0).unwrap();
    let root = over_depth.eq(read, zero).unwrap();
    assert!(!IncrementalBvSolver::term_supported_by_warm_abstraction(
        &over_depth,
        root
    ));
    let mut deferred = IncrementalBvSolver::new();
    deferred
        .assert_simplifying_memory(&mut over_depth, root)
        .unwrap();
    assert!(deferred.has_deferred_theory_assertions());

    let mut at_nodes = TermArena::new();
    let tree = build_ite_tree(&mut at_nodes, 512);
    let index = at_nodes.bv_var("warm_node_read", 4).unwrap();
    let read = at_nodes.select(tree, index).unwrap();
    let zero = at_nodes.bv_const(4, 0).unwrap();
    let root = at_nodes.eq(read, zero).unwrap();
    assert!(IncrementalBvSolver::term_supported_by_warm_abstraction(
        &at_nodes, root
    ));

    let write_index = at_nodes.bv_var("warm_node_write", 4).unwrap();
    let one = at_nodes.bv_const(4, 1).unwrap();
    let over_tree = at_nodes.store(tree, write_index, one).unwrap();
    let over_read = at_nodes.select(over_tree, index).unwrap();
    let over_root = at_nodes.eq(over_read, zero).unwrap();
    assert!(!IncrementalBvSolver::term_supported_by_warm_abstraction(
        &at_nodes, over_root
    ));
}

fn build_case(seed: u64, arena: &mut TermArena) -> (Vec<TermId>, Verdict) {
    let left_array = arena
        .array_var_with_sorts("warm_matrix_a", Sort::BitVec(3), Sort::BitVec(3))
        .unwrap();
    let right_array = arena
        .array_var_with_sorts("warm_matrix_b", Sort::BitVec(3), Sort::BitVec(3))
        .unwrap();
    let write_index = arena.bv_var("warm_matrix_x", 3).unwrap();
    let read_index = arena.bv_var("warm_matrix_y", 3).unwrap();
    let condition = arena.bool_var("warm_matrix_c").unwrap();
    let one = arena.bv_const(3, 1).unwrap();
    let two = arena.bv_const(3, 2).unwrap();
    let store = arena.store(left_array, write_index, one).unwrap();
    let store_read_y = arena.select(store, read_index).unwrap();
    let same_index = arena.eq(write_index, read_index).unwrap();
    let distinct_index = arena.not(same_index).unwrap();
    let const_two = arena.const_array(3, two).unwrap();
    let chosen = arena.ite(condition, left_array, right_array).unwrap();

    match seed % 8 {
        0 => {
            let wrong = not_eq(arena, store_read_y, one);
            (vec![same_index, wrong], Verdict::Unsat)
        }
        1 => {
            let base_read = arena.select(left_array, read_index).unwrap();
            let base_is_two = arena.eq(base_read, two).unwrap();
            let store_is_two = arena.eq(store_read_y, two).unwrap();
            (
                vec![distinct_index, base_is_two, store_is_two],
                Verdict::Sat,
            )
        }
        2 => {
            let read = arena.select(const_two, write_index).unwrap();
            let wrong = not_eq(arena, read, two);
            (vec![wrong], Verdict::Unsat)
        }
        3 => {
            let chosen_read = arena.select(chosen, write_index).unwrap();
            let a_read = arena.select(left_array, write_index).unwrap();
            let wrong = not_eq(arena, chosen_read, a_read);
            (vec![condition, wrong], Verdict::Unsat)
        }
        4 => {
            let not_c = arena.not(condition).unwrap();
            let b_read = arena.select(right_array, write_index).unwrap();
            let b_is_two = arena.eq(b_read, two).unwrap();
            let chosen_read = arena.select(chosen, write_index).unwrap();
            let chosen_is_two = arena.eq(chosen_read, two).unwrap();
            (vec![not_c, b_is_two, chosen_is_two], Verdict::Sat)
        }
        5 => {
            let nested = arena.store(store, read_index, two).unwrap();
            let nested_read = arena.select(nested, read_index).unwrap();
            let nested_is_two = arena.eq(nested_read, two).unwrap();
            (vec![nested_is_two], Verdict::Sat)
        }
        6 => {
            let bool_default = arena.bool_const(false);
            let bool_array = arena
                .const_array_with_index_sort(Sort::BitVec(3), bool_default)
                .unwrap();
            let bool_store = arena.store(bool_array, write_index, condition).unwrap();
            let bool_read = arena.select(bool_store, read_index).unwrap();
            let wrong = not_eq(arena, bool_read, condition);
            (vec![same_index, wrong], Verdict::Unsat)
        }
        _ => {
            let left = arena.select(store, write_index).unwrap();
            let right = arena.select(store, read_index).unwrap();
            let different = not_eq(arena, left, right);
            (vec![same_index, different], Verdict::Unsat)
        }
    }
}

#[test]
fn warm_matrix_matches_check_auto_and_replays() {
    for seed in 0..64 {
        let mut warm_arena = TermArena::new();
        let (assertions, expected) = build_case(seed, &mut warm_arena);
        let mut warm = IncrementalBvSolver::new();
        for &assertion in &assertions {
            warm.assert_simplifying_memory(&mut warm_arena, assertion)
                .unwrap();
        }
        assert!(!warm.has_deferred_theory_assertions(), "seed {seed}");
        let warm_result = warm.check(&warm_arena).unwrap();
        assert_eq!(verdict(&warm_result), expected, "warm seed {seed}");
        assert_replays(&warm_arena, &assertions, &warm_result);

        let mut canonical_arena = TermArena::new();
        let (canonical_assertions, _) = build_case(seed, &mut canonical_arena);
        let canonical = check_auto(
            &mut canonical_arena,
            &canonical_assertions,
            &SolverConfig::default(),
        )
        .unwrap();
        assert_eq!(verdict(&canonical), expected, "check_auto seed {seed}");
    }
}

#[cfg(feature = "z3")]
fn z3_verdict(seed: u64) -> Verdict {
    let bv_sort = Z3Sort::bitvector(3);
    let left_array = Array::new_const("warm_matrix_a", &bv_sort, &bv_sort);
    let right_array = Array::new_const("warm_matrix_b", &bv_sort, &bv_sort);
    let write_index = BV::new_const("warm_matrix_x", 3);
    let read_index = BV::new_const("warm_matrix_y", 3);
    let condition = Bool::new_const("warm_matrix_c");
    let one = BV::from_u64(1, 3);
    let two = BV::from_u64(2, 3);
    let store = left_array.store(&write_index, &one);
    let store_read_y = store.select(&read_index).as_bv().unwrap();
    let same_index = write_index.eq(&read_index);
    let distinct_index = same_index.not();
    let const_two = Array::const_array(&bv_sort, &two);
    let chosen = condition.ite(&left_array, &right_array);

    let assertions: Vec<Bool> = match seed % 8 {
        0 => vec![same_index, store_read_y.eq(&one).not()],
        1 => {
            let base_read = left_array.select(&read_index).as_bv().unwrap();
            vec![distinct_index, base_read.eq(&two), store_read_y.eq(&two)]
        }
        2 => {
            let read = const_two.select(&write_index).as_bv().unwrap();
            vec![read.eq(&two).not()]
        }
        3 => {
            let chosen_read = chosen.select(&write_index).as_bv().unwrap();
            let a_read = left_array.select(&write_index).as_bv().unwrap();
            vec![condition.clone(), chosen_read.eq(&a_read).not()]
        }
        4 => {
            let b_read = right_array.select(&write_index).as_bv().unwrap();
            let chosen_read = chosen.select(&write_index).as_bv().unwrap();
            vec![condition.not(), b_read.eq(&two), chosen_read.eq(&two)]
        }
        5 => {
            let nested = store.store(&read_index, &two);
            let nested_read = nested.select(&read_index).as_bv().unwrap();
            vec![nested_read.eq(&two)]
        }
        6 => {
            let bool_default = Bool::from_bool(false);
            let bool_array = Array::const_array(&bv_sort, &bool_default);
            let bool_store = bool_array.store(&write_index, &condition);
            let bool_read = bool_store.select(&read_index).as_bool().unwrap();
            vec![same_index, bool_read.eq(&condition).not()]
        }
        _ => {
            let left = store.select(&write_index).as_bv().unwrap();
            let right = store.select(&read_index).as_bv().unwrap();
            vec![same_index, left.eq(&right).not()]
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
        let mut arena = TermArena::new();
        let (_, expected) = build_case(seed, &mut arena);
        assert_eq!(z3_verdict(seed), expected, "Z3 seed {seed}");
    }
}
