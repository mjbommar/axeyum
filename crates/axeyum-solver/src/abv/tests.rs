use super::{
    ExtReplay, LastExtReplay, ProjectionRepairStats, RowCtx, RowKind, RowSite, StoreChainSide,
    array_value_from_entries, check_qf_abv_lazy, check_with_array_elimination,
    collect_base_array_entries, complete_assignment, const_array_default_mismatch_refutation,
    cross_store_array_disequality_refutation, default_value_for_symbol,
    first_false_replay_conjunct, first_projected_replay_failure,
    positive_replay_conjunct_count, positive_replay_false_count, project_online_row_assignment,
    project_replay_ext_candidate, prove_unsat_by_symmetric_swap_chain,
    repair_projected_branch_as_candidate,
    repair_projected_branch_best_candidate_with_scalar_closure_guard,
    repair_projected_branch_disjunctions, repair_projected_branch_scalar_choice_candidate,
    repair_projected_branch_schedule, repair_projected_replay_branch_beam,
    repair_projected_replay_branch_choice, repair_projected_replay_branch_pair_choice,
    repair_projected_replay_branch_select_cycle, repair_projected_replay_failure,
    repair_projected_scalar_equalities, replay_failure_with_branch_candidate_diagnostics,
    replay_last_ext_candidate, select_value, store_chain_readback_refutation, store_value,
};
use crate::backend::{CheckResult, SolverConfig};
use crate::sat_bv_backend::SatBvBackend;
use axeyum_ir::{ArraySortKey, ArrayValue, Assignment, Sort, TermArena, TermNode, Value, eval};
use axeyum_smtlib::parse_script;
use std::time::Instant;

fn bv_value(width: u32, value: u128) -> Value {
    Value::Bv { width, value }
}

#[test]
fn array_projection_uses_majority_bv_default() {
    let mut arena = TermArena::new();
    let array = arena.array_var("majority_bv_array", 4, 8).unwrap();
    let TermNode::Symbol(array) = arena.node(array) else {
        panic!("array variable must be a symbol");
    };
    let entries = [
        (bv_value(4, 0), bv_value(8, 7)),
        (bv_value(4, 1), bv_value(8, 7)),
        (bv_value(4, 2), bv_value(8, 7)),
        (bv_value(4, 3), bv_value(8, 3)),
        (bv_value(4, 4), bv_value(8, 4)),
    ];

    let projected = array_value_from_entries(&arena, *array, &entries).unwrap();
    let value = projected.as_array().unwrap();
    assert_eq!(value.default_element(), 7);
    assert_eq!(value.entries().collect::<Vec<_>>(), vec![(3, 3), (4, 4)]);
    for (index, expected) in [7, 7, 7, 3, 4].into_iter().enumerate() {
        assert_eq!(value.select(u128::try_from(index).unwrap()), expected);
    }
}

#[test]
fn array_projection_majority_tie_uses_smallest_value() {
    let mut arena = TermArena::new();
    let array = arena.array_var("majority_tie_array", 4, 8).unwrap();
    let TermNode::Symbol(array) = arena.node(array) else {
        panic!("array variable must be a symbol");
    };
    let entries = [
        (bv_value(4, 0), bv_value(8, 9)),
        (bv_value(4, 1), bv_value(8, 3)),
    ];

    let projected = array_value_from_entries(&arena, *array, &entries).unwrap();
    let value = projected.as_array().unwrap();
    assert_eq!(value.default_element(), 3);
    assert_eq!(value.entries().collect::<Vec<_>>(), vec![(0, 9)]);
}

#[test]
fn structural_projection_honors_an_expired_deadline() {
    let mut arena = TermArena::new();
    let base = arena.array_var("deadline_structural_base", 3, 3).unwrap();
    let target = arena.array_var("deadline_structural_target", 3, 3).unwrap();
    let base_symbol = match arena.node(base) {
        TermNode::Symbol(symbol) => *symbol,
        _ => panic!("base must be a symbol"),
    };
    let target_symbol = match arena.node(target) {
        TermNode::Symbol(symbol) => *symbol,
        _ => panic!("target must be a symbol"),
    };
    let zero = arena.bv_const(3, 0).unwrap();
    let one = arena.bv_const(3, 1).unwrap();
    let stored = arena.store(base, zero, one).unwrap();
    let mut assignment = Assignment::new();
    assignment.set(base_symbol, Value::Array(ArrayValue::constant(3, 3, 0)));
    assignment.set(target_symbol, Value::Array(ArrayValue::constant(3, 3, 0)));

    let error = project_online_row_assignment(
        &arena,
        &[],
        &[],
        &[(stored, target)],
        &assignment,
        Some(Instant::now()),
    )
    .expect_err("expired structural projection declines");
    assert!(error.to_string().contains("shared deadline"), "{error}");
}

#[test]
fn generic_array_projection_uses_majority_default() {
    let mut arena = TermArena::new();
    let array = arena
        .declare(
            "majority_generic_array",
            Sort::Array {
                index: ArraySortKey::Int,
                element: ArraySortKey::Int,
            },
        )
        .unwrap();
    let entries = [
        (Value::Int(0), Value::Int(7)),
        (Value::Int(1), Value::Int(7)),
        (Value::Int(2), Value::Int(3)),
    ];

    let projected = array_value_from_entries(&arena, array, &entries).unwrap();
    let value = projected.as_generic_array().unwrap();
    assert_eq!(value.default_value(), &Value::Int(7));
    assert_eq!(value.entries().collect::<Vec<_>>().len(), 1);
    assert_eq!(value.select(&Value::Int(0)), Value::Int(7));
    assert_eq!(value.select(&Value::Int(2)), Value::Int(3));
}

#[test]
fn lazy_abv_refutes_select_congruence() {
    // select(a, i) != select(a, j) AND i = j  =>  UNSAT (a lemma is required
    // to refute: the abstraction alone, with two unconstrained fresh select
    // results, is SAT).
    let mut arena = TermArena::new();
    let a = arena.array_var("a", 3, 4).unwrap();
    let i = arena.bv_var("i", 3).unwrap();
    let j = arena.bv_var("j", 3).unwrap();
    let read_i = arena.select(a, i).unwrap();
    let read_j = arena.select(a, j).unwrap();
    let reads_ne = {
        let eq = arena.eq(read_i, read_j).unwrap();
        arena.not(eq).unwrap()
    };
    let i_eq_j = arena.eq(i, j).unwrap();

    let mut backend = SatBvBackend::new();
    let config = SolverConfig::default();
    let result =
        check_qf_abv_lazy(&mut backend, &mut arena, &[reads_ne, i_eq_j], &config).unwrap();
    assert_eq!(result, CheckResult::Unsat);
}

#[test]
fn lazy_abv_sat_model_replays() {
    // select(store(a, i, v), i) = w AND v = w  =>  SAT. Read-over-write
    // forces select(store(a,i,v),i) = v, so w = v is consistent. The
    // returned model must replay against every original assertion.
    let mut arena = TermArena::new();
    let a = arena.array_var("a", 3, 4).unwrap();
    let i = arena.bv_var("i", 3).unwrap();
    let v = arena.bv_var("v", 4).unwrap();
    let w = arena.bv_var("w", 4).unwrap();
    let stored = arena.store(a, i, v).unwrap();
    let read = arena.select(stored, i).unwrap();
    let read_eq_w = arena.eq(read, w).unwrap();
    let v_eq_w = arena.eq(v, w).unwrap();
    let originals = [read_eq_w, v_eq_w];

    let mut backend = SatBvBackend::new();
    let config = SolverConfig::default();
    let result = check_qf_abv_lazy(&mut backend, &mut arena, &originals, &config).unwrap();
    let CheckResult::Sat(model) = result else {
        panic!("expected SAT, got {result:?}");
    };
    let assignment = model.to_assignment();
    for &t in &originals {
        assert_eq!(
            eval(&arena, t, &assignment).unwrap(),
            Value::Bool(true),
            "original assertion must replay to true"
        );
    }
}

#[test]
fn lazy_ext_last_candidate_replay_accepts_only_real_models() {
    // The timeout/unknown shortcut is sound only because it rebuilds a model
    // and evaluates the original assertions. This pins the positive path:
    // even if refinement is incomplete, a candidate that replays is a real
    // SAT model.
    let mut arena = TermArena::new();
    let a = arena.array_var("a", 16, 8).unwrap();
    let b = arena.array_var("b", 16, 8).unwrap();
    let c = arena.array_var("c", 16, 8).unwrap();
    let i = arena.bv_var("i", 16).unwrap();
    let j = arena.bv_var("j", 16).unwrap();
    let k = arena.bv_var("k", 16).unwrap();
    let v = arena.bv_var("v", 8).unwrap();
    let p = arena.bool_var("p").unwrap();
    let zero = arena.bv_const(8, 0).unwrap();

    let lhs = arena.store(a, i, v).unwrap();
    let rhs = arena.store(b, i, v).unwrap();
    let array_eq = arena.eq(lhs, rhs).unwrap();
    let cj = arena.select(c, j).unwrap();
    let ck = arena.select(c, k).unwrap();
    let cj_zero = arena.eq(cj, zero).unwrap();
    let ck_zero = arena.eq(ck, zero).unwrap();
    let loose_j = arena.or(cj_zero, p).unwrap();
    let loose_k = arena.or(ck_zero, p).unwrap();
    let originals = [array_eq, loose_j, loose_k, p];

    let mut ctx = RowCtx::default();
    for &assertion in &originals {
        ctx.abstract_with_array_eq(&mut arena, assertion)
            .unwrap()
            .expect("lazy-ext abstraction");
    }

    let mut candidate = Assignment::new();
    let mut row_value = 1u128;
    for (symbol, name, sort) in arena.symbols() {
        if name.starts_with("!ext_eq_") || name == "p" {
            candidate.set(symbol, Value::Bool(true));
        } else if name.starts_with("!row_sel_") {
            candidate.set(
                symbol,
                Value::Bv {
                    width: 8,
                    value: row_value,
                },
            );
            row_value ^= 1;
        } else if sort == Sort::BitVec(16) {
            candidate.set(
                symbol,
                Value::Bv {
                    width: 16,
                    value: 0,
                },
            );
        } else if sort == Sort::BitVec(8) {
            candidate.set(symbol, Value::Bv { width: 8, value: 0 });
        }
    }

    let LastExtReplay::Sat(model) =
        replay_last_ext_candidate(&arena, &ctx, &originals, Some(&candidate))
    else {
        panic!("expected replay helper to accept the candidate");
    };
    let assignment = model.to_assignment();
    for &t in &originals {
        assert_eq!(eval(&arena, t, &assignment).unwrap(), Value::Bool(true));
    }

    let mut failing = candidate.clone();
    for (symbol, name, _sort) in arena.symbols() {
        if name == "p" {
            failing.set(symbol, Value::Bool(false));
        }
    }
    let LastExtReplay::Failed(failure) =
        replay_last_ext_candidate(&arena, &ctx, &originals, Some(&failing))
    else {
        panic!("expected replay helper to reject the candidate");
    };
    assert_eq!(failure.assertion_ordinal, 3);
    assert_eq!(failure.assertion_term, p);
    assert_eq!(failure.conjunct_ordinal, 0);
    assert_eq!(failure.conjunct_term, p);
    assert!(failure.note().contains("failed_conjunct_term="));
}

#[test]
fn lazy_ext_replay_failure_reports_best_false_or_branch() {
    let mut arena = TermArena::new();
    let x = arena.int_var("x").unwrap();
    let y = arena.int_var("y").unwrap();
    let zero = arena.int_const(0);
    let one = arena.int_const(1);
    let two = arena.int_const(2);
    let x_eq_zero = arena.eq(x, zero).unwrap();
    let y_eq_zero = arena.eq(y, zero).unwrap();
    let x_eq_one = arena.eq(x, one).unwrap();
    let y_eq_two = arena.eq(y, two).unwrap();
    let branch0 = arena.and(x_eq_zero, y_eq_zero).unwrap();
    let branch1 = arena.and(x_eq_one, y_eq_two).unwrap();
    let assertion = arena.or(branch0, branch1).unwrap();

    let mut assignment = Assignment::new();
    let TermNode::Symbol(x_sym) = arena.node(x) else {
        panic!("x should be a symbol");
    };
    let TermNode::Symbol(y_sym) = arena.node(y) else {
        panic!("y should be a symbol");
    };
    assignment.set(*x_sym, Value::Int(1));
    assignment.set(*y_sym, Value::Int(3));

    let failure = first_false_replay_conjunct(
        &arena,
        assertion,
        0,
        &assignment,
        ProjectionRepairStats::default(),
    )
    .unwrap();
    let note = failure.note();
    assert!(note.contains("failed_or_branches=2"));
    assert!(note.contains("failed_or_best_branch=1"));
    assert!(note.contains(&format!("failed_or_best_branch_term={}", branch1.index())));
    assert!(note.contains("failed_or_best_branch_false_literals=1"));
    assert!(note.contains("failed_or_best_branch_first_false_term="));
    assert!(note.contains("failed_or_best_branch_first_false_lhs_value=3"));
}

#[test]
fn lazy_ext_replay_failure_reports_branch_candidate_diagnostics() {
    let mut arena = TermArena::new();
    let q = arena.bool_var("q").unwrap();
    let r = arena.bool_var("r").unwrap();
    let branch_assertion = arena.or(q, r).unwrap();

    let TermNode::Symbol(q_symbol) = arena.node(q) else {
        panic!("q should be a symbol");
    };
    let TermNode::Symbol(r_symbol) = arena.node(r) else {
        panic!("r should be a symbol");
    };

    let mut candidate = Assignment::new();
    candidate.set(*q_symbol, Value::Bool(false));
    candidate.set(*r_symbol, Value::Bool(false));

    let ctx = RowCtx::default();
    let originals = [branch_assertion];
    let ExtReplay::Failed(failure) =
        project_replay_ext_candidate(&arena, &ctx, &originals, &candidate).unwrap()
    else {
        panic!("expected unrepairable branch replay failure");
    };
    let note = failure.note();
    assert!(note.contains("branch_candidate_diagnostics=["));
    assert!(note.contains("#0:init=1,status=no_repair"));
    assert!(note.contains("#1:init=1,status=no_repair"));
}

#[test]
fn lazy_ext_branch_pair_choice_scores_adjacent_or_repairs() {
    let mut arena = TermArena::new();
    let x = arena.int_var("x").unwrap();
    let y = arena.int_var("y").unwrap();
    let q = arena.bool_var("q").unwrap();
    let one = arena.int_const(1);
    let two = arena.int_const(2);
    let x_eq_one = arena.eq(x, one).unwrap();
    let y_eq_one = arena.eq(y, one).unwrap();
    let first_or = arena.or(x_eq_one, y_eq_one).unwrap();
    let x_eq_two = arena.eq(x, two).unwrap();
    let second_or = arena.or(x_eq_two, q).unwrap();

    let TermNode::Symbol(x_symbol) = arena.node(x) else {
        panic!("x should be a symbol");
    };
    let TermNode::Symbol(y_symbol) = arena.node(y) else {
        panic!("y should be a symbol");
    };
    let TermNode::Symbol(q_symbol) = arena.node(q) else {
        panic!("q should be a symbol");
    };

    let mut projected = Assignment::new();
    projected.set(*x_symbol, Value::Int(0));
    projected.set(*y_symbol, Value::Int(0));
    projected.set(*q_symbol, Value::Bool(false));
    let originals = [first_or, second_or];
    assert_eq!(
        positive_replay_false_count(&arena, &originals, &projected).unwrap(),
        2
    );

    let mut single = projected.clone();
    repair_projected_replay_branch_choice(&arena, &originals, first_or, &mut single)
        .unwrap()
        .expect("single-OR repair should choose the local branch tie");
    assert_eq!(single.get(*x_symbol), Some(Value::Int(1)));
    assert_eq!(single.get(*y_symbol), Some(Value::Int(0)));
    assert_eq!(
        positive_replay_false_count(&arena, &originals, &single).unwrap(),
        1
    );

    let mut paired = projected;
    repair_projected_replay_branch_pair_choice(&arena, &originals, first_or, &mut paired)
        .unwrap()
        .expect("paired repair should compose adjacent OR choices");
    assert_eq!(paired.get(*x_symbol), Some(Value::Int(2)));
    assert_eq!(paired.get(*y_symbol), Some(Value::Int(1)));
    assert_eq!(
        positive_replay_false_count(&arena, &originals, &paired).unwrap(),
        0
    );
    for &original in &originals {
        assert_eq!(eval(&arena, original, &paired).unwrap(), Value::Bool(true));
    }
}

#[test]
fn lazy_ext_branch_beam_allows_temporary_uphill_schedule() {
    let mut arena = TermArena::new();
    let x = arena.int_var("x").unwrap();
    let y = arena.int_var("y").unwrap();
    let z = arena.int_var("z").unwrap();
    let w = arena.int_var("w").unwrap();
    let q = arena.bool_var("q").unwrap();
    let zero = arena.int_const(0);
    let one = arena.int_const(1);
    let two = arena.int_const(2);
    let three = arena.int_const(3);

    let x_eq_one = arena.eq(x, one).unwrap();
    let first_or = arena.or(x_eq_one, q).unwrap();
    let x_eq_zero = arena.eq(x, zero).unwrap();
    let z_eq_one = arena.eq(z, one).unwrap();
    let second_or = arena.or(x_eq_zero, z_eq_one).unwrap();
    let z_eq_zero = arena.eq(z, zero).unwrap();
    let y_eq_two = arena.eq(y, two).unwrap();
    let third_or = arena.or(z_eq_zero, y_eq_two).unwrap();
    let w_eq_three = arena.eq(w, three).unwrap();
    let fourth_or = arena.or(z_eq_zero, w_eq_three).unwrap();
    let prefix = arena.and(first_or, second_or).unwrap();
    let suffix = arena.and(third_or, fourth_or).unwrap();
    let assertion = arena.and(prefix, suffix).unwrap();

    let TermNode::Symbol(x_symbol) = arena.node(x) else {
        panic!("x should be a symbol");
    };
    let TermNode::Symbol(y_symbol) = arena.node(y) else {
        panic!("y should be a symbol");
    };
    let TermNode::Symbol(z_symbol) = arena.node(z) else {
        panic!("z should be a symbol");
    };
    let TermNode::Symbol(w_symbol) = arena.node(w) else {
        panic!("w should be a symbol");
    };
    let TermNode::Symbol(q_symbol) = arena.node(q) else {
        panic!("q should be a symbol");
    };

    let mut projected = Assignment::new();
    projected.set(*x_symbol, Value::Int(0));
    projected.set(*y_symbol, Value::Int(0));
    projected.set(*z_symbol, Value::Int(0));
    projected.set(*w_symbol, Value::Int(0));
    projected.set(*q_symbol, Value::Bool(false));
    let originals = [assertion];
    assert_eq!(
        positive_replay_false_count(&arena, &originals, &projected).unwrap(),
        1
    );

    let mut paired = projected.clone();
    assert!(
        repair_projected_replay_branch_pair_choice(&arena, &originals, first_or, &mut paired)
            .unwrap()
            .is_none(),
        "strict pair repair should reject the temporary two-false state"
    );

    let stats =
        repair_projected_replay_branch_beam(&arena, &originals, first_or, &mut projected)
            .unwrap()
            .expect("beam should find the final improving branch schedule");
    assert!(stats.branch_symbol_changes >= 4);
    assert_eq!(
        positive_replay_false_count(&arena, &originals, &projected).unwrap(),
        0
    );
    assert_eq!(projected.get(*x_symbol), Some(Value::Int(1)));
    assert_eq!(projected.get(*z_symbol), Some(Value::Int(1)));
    assert_eq!(projected.get(*y_symbol), Some(Value::Int(2)));
    assert_eq!(projected.get(*w_symbol), Some(Value::Int(3)));
    assert_eq!(
        eval(&arena, assertion, &projected).unwrap(),
        Value::Bool(true)
    );
}

#[test]
fn lazy_ext_branch_beam_stabilizes_direct_select_readbacks() {
    let mut arena = TermArena::new();
    let a = arena.array_var("a", 4, 8).unwrap();
    let b = arena.array_var("b", 4, 8).unwrap();
    let i = arena.bv_var("i", 4).unwrap();
    let v = arena.bv_var("v", 8).unwrap();
    let y = arena.bv_var("y", 8).unwrap();
    let p = arena.bool_var("p").unwrap();
    let stored = arena.store(b, i, v).unwrap();
    let a_eq_store = arena.eq(a, stored).unwrap();
    let branch_or = arena.or(a_eq_store, p).unwrap();
    let read_a_i = arena.select(a, i).unwrap();
    let y_eq_read = arena.eq(y, read_a_i).unwrap();
    let assertion = arena.and(branch_or, y_eq_read).unwrap();

    let TermNode::Symbol(a_symbol) = arena.node(a) else {
        panic!("a should be a symbol");
    };
    let TermNode::Symbol(b_symbol) = arena.node(b) else {
        panic!("b should be a symbol");
    };
    let TermNode::Symbol(i_symbol) = arena.node(i) else {
        panic!("i should be a symbol");
    };
    let TermNode::Symbol(v_symbol) = arena.node(v) else {
        panic!("v should be a symbol");
    };
    let TermNode::Symbol(y_symbol) = arena.node(y) else {
        panic!("y should be a symbol");
    };
    let TermNode::Symbol(p_symbol) = arena.node(p) else {
        panic!("p should be a symbol");
    };

    let mut projected = Assignment::new();
    let default_a = default_value_for_symbol(&arena, *a_symbol).unwrap();
    let default_b = default_value_for_symbol(&arena, *b_symbol).unwrap();
    projected.set(*a_symbol, default_a);
    projected.set(*b_symbol, default_b);
    projected.set(*i_symbol, Value::Bv { width: 4, value: 1 });
    projected.set(*v_symbol, Value::Bv { width: 8, value: 7 });
    projected.set(*y_symbol, Value::Bv { width: 8, value: 0 });
    projected.set(*p_symbol, Value::Bool(false));

    let originals = [assertion];
    assert_eq!(
        positive_replay_false_count(&arena, &originals, &projected).unwrap(),
        1
    );
    repair_projected_replay_branch_beam(&arena, &originals, branch_or, &mut projected)
        .unwrap()
        .expect("beam should repair the store branch and align readback");
    assert_eq!(
        projected.get(*y_symbol),
        Some(Value::Bv { width: 8, value: 7 })
    );
    assert_eq!(
        positive_replay_false_count(&arena, &originals, &projected).unwrap(),
        0
    );
    assert_eq!(
        eval(&arena, assertion, &projected).unwrap(),
        Value::Bool(true)
    );
}

#[test]
fn lazy_ext_replay_failure_reports_branch_pair_candidate_diagnostics() {
    let mut arena = TermArena::new();
    let x = arena.int_var("x").unwrap();
    let y = arena.int_var("y").unwrap();
    let q = arena.bool_var("q").unwrap();
    let h = arena.bool_var("h").unwrap();
    let one = arena.int_const(1);
    let two = arena.int_const(2);
    let x_eq_one = arena.eq(x, one).unwrap();
    let y_eq_one = arena.eq(y, one).unwrap();
    let first_or = arena.or(x_eq_one, y_eq_one).unwrap();
    let x_eq_two = arena.eq(x, two).unwrap();
    let second_or = arena.or(x_eq_two, q).unwrap();
    let first_two = arena.and(first_or, second_or).unwrap();
    let assertion = arena.and(first_two, h).unwrap();

    let TermNode::Symbol(x_symbol) = arena.node(x) else {
        panic!("x should be a symbol");
    };
    let TermNode::Symbol(y_symbol) = arena.node(y) else {
        panic!("y should be a symbol");
    };
    let TermNode::Symbol(q_symbol) = arena.node(q) else {
        panic!("q should be a symbol");
    };
    let TermNode::Symbol(h_symbol) = arena.node(h) else {
        panic!("h should be a symbol");
    };

    let mut projected = Assignment::new();
    projected.set(*x_symbol, Value::Int(0));
    projected.set(*y_symbol, Value::Int(0));
    projected.set(*q_symbol, Value::Bool(false));
    projected.set(*h_symbol, Value::Bool(false));
    let originals = [assertion];
    let failure = first_projected_replay_failure(
        &arena,
        &originals,
        &projected,
        ProjectionRepairStats::default(),
    )
    .unwrap()
    .expect("expected first OR replay failure");
    let failure = replay_failure_with_branch_candidate_diagnostics(
        &arena, &originals, &projected, failure,
    )
    .unwrap();
    let note = failure.note();
    assert!(note.contains("branch_pair_candidate_diagnostics=["));
    assert!(note.contains("#1->1#0:init=1,status=candidate"), "{note}");
    assert!(note.contains("global_false_ordinal=2"), "{note}");
}

#[test]
fn lazy_ext_replay_failure_reports_branch_select_candidate_diagnostics() {
    let mut arena = TermArena::new();
    let a = arena.array_var("a", 4, 8).unwrap();
    let i = arena.bv_var("i", 4).unwrap();
    let j = arena.bv_var("j", 4).unwrap();
    let y = arena.bv_var("y", 8).unwrap();
    let q = arena.bool_var("q").unwrap();
    let i_eq_j = arena.eq(i, j).unwrap();
    let branch_or = arena.or(i_eq_j, q).unwrap();
    let read = arena.select(a, i).unwrap();
    let y_eq_read = arena.eq(y, read).unwrap();
    let assertion = arena.and(branch_or, y_eq_read).unwrap();

    let TermNode::Symbol(a_symbol) = arena.node(a) else {
        panic!("a should be a symbol");
    };
    let TermNode::Symbol(i_symbol) = arena.node(i) else {
        panic!("i should be a symbol");
    };
    let TermNode::Symbol(j_symbol) = arena.node(j) else {
        panic!("j should be a symbol");
    };
    let TermNode::Symbol(y_symbol) = arena.node(y) else {
        panic!("y should be a symbol");
    };
    let TermNode::Symbol(q_symbol) = arena.node(q) else {
        panic!("q should be a symbol");
    };

    let mut projected = Assignment::new();
    let default_a = default_value_for_symbol(&arena, *a_symbol).unwrap();
    let a_with_entry = store_value(
        &default_a,
        Value::Bv { width: 4, value: 2 },
        Value::Bv { width: 8, value: 7 },
    )
    .unwrap();
    projected.set(*a_symbol, a_with_entry);
    projected.set(*i_symbol, Value::Bv { width: 4, value: 1 });
    projected.set(*j_symbol, Value::Bv { width: 4, value: 2 });
    projected.set(*y_symbol, Value::Bv { width: 8, value: 0 });
    projected.set(*q_symbol, Value::Bool(false));

    let originals = [assertion];
    let failure = first_projected_replay_failure(
        &arena,
        &originals,
        &projected,
        ProjectionRepairStats::default(),
    )
    .unwrap()
    .expect("expected first OR replay failure");
    let failure = replay_failure_with_branch_candidate_diagnostics(
        &arena, &originals, &projected, failure,
    )
    .unwrap();
    let note = failure.note();
    assert!(note.contains("branch_select_candidate_diagnostics=["));
    assert!(note.contains("#0->1:direct,status=candidate"), "{note}");
    assert!(note.contains("target_true=true"), "{note}");
    assert!(note.contains("total_false=0"), "{note}");
}

#[test]
#[allow(clippy::too_many_lines)]
fn lazy_ext_branch_select_cycle_repair_forces_alternate_or_branch() {
    let mut arena = TermArena::new();
    let a = arena.array_var("a", 4, 8).unwrap();
    let b = arena.array_var("b", 4, 8).unwrap();
    let i = arena.bv_var("i", 4).unwrap();
    let q = arena.bool_var("q").unwrap();
    let two4 = arena.bv_const(4, 2).unwrap();
    let three4 = arena.bv_const(4, 3).unwrap();
    let zero8 = arena.bv_const(8, 0).unwrap();
    let seven8 = arena.bv_const(8, 7).unwrap();
    let nine8 = arena.bv_const(8, 9).unwrap();
    let true_term = arena.bool_const(true);
    let i_eq_two = arena.eq(i, two4).unwrap();
    let a_eq_b = arena.eq(a, b).unwrap();
    let copy_branch = arena.and(i_eq_two, a_eq_b).unwrap();
    let q_eq_true = arena.eq(q, true_term).unwrap();
    let branch_or = arena.or(copy_branch, q_eq_true).unwrap();
    let read_a_i = arena.select(a, i).unwrap();
    let zero_eq_read = arena.eq(zero8, read_a_i).unwrap();
    let read_b_two = arena.select(b, two4).unwrap();
    let seven_eq_read = arena.eq(seven8, read_b_two).unwrap();
    let read_b_three = arena.select(b, three4).unwrap();
    let nine_eq_read = arena.eq(nine8, read_b_three).unwrap();
    let first = arena.and(branch_or, zero_eq_read).unwrap();
    let second = arena.and(seven_eq_read, nine_eq_read).unwrap();
    let assertion = arena.and(first, second).unwrap();

    let TermNode::Symbol(a_symbol) = arena.node(a) else {
        panic!("a should be a symbol");
    };
    let TermNode::Symbol(b_symbol) = arena.node(b) else {
        panic!("b should be a symbol");
    };
    let TermNode::Symbol(i_symbol) = arena.node(i) else {
        panic!("i should be a symbol");
    };
    let TermNode::Symbol(q_symbol) = arena.node(q) else {
        panic!("q should be a symbol");
    };

    let mut projected = Assignment::new();
    projected.set(
        *a_symbol,
        default_value_for_symbol(&arena, *a_symbol).unwrap(),
    );
    let default_b = default_value_for_symbol(&arena, *b_symbol).unwrap();
    let b_with_two = store_value(
        &default_b,
        Value::Bv { width: 4, value: 2 },
        Value::Bv { width: 8, value: 7 },
    )
    .unwrap();
    let b_with_entries = store_value(
        &b_with_two,
        Value::Bv { width: 4, value: 3 },
        Value::Bv { width: 8, value: 9 },
    )
    .unwrap();
    projected.set(*b_symbol, b_with_entries);
    projected.set(*i_symbol, Value::Bv { width: 4, value: 1 });
    projected.set(*q_symbol, Value::Bool(false));

    let originals = [assertion];
    assert_eq!(
        positive_replay_false_count(&arena, &originals, &projected).unwrap(),
        1
    );
    let failure = first_projected_replay_failure(
        &arena,
        &originals,
        &projected,
        ProjectionRepairStats::default(),
    )
    .unwrap()
    .expect("expected first OR replay failure");
    let failure = replay_failure_with_branch_candidate_diagnostics(
        &arena, &originals, &projected, failure,
    )
    .unwrap();
    let note = failure.note();
    assert!(
        note.contains("branch_select_candidate_diagnostics=["),
        "{note}"
    );
    assert!(
        note.contains("global_false_or_best_branch=0")
            || note.contains("global_false_or_best_branch=1"),
        "{note}"
    );
    assert!(note.contains("global_false_or_best_branch_term="), "{note}");
    assert!(
        note.contains("global_false_or_best_branch_false_literals=1"),
        "{note}"
    );
    let stats = repair_projected_replay_branch_select_cycle(
        &arena,
        &originals,
        branch_or,
        &mut projected,
    )
    .unwrap()
    .expect("expected branch/select cycle repair");
    assert!(stats.branch_symbol_changes >= 2, "{stats:?}");
    assert!(stats.array_changes >= 1, "{stats:?}");
    assert_eq!(projected.get(*q_symbol), Some(Value::Bool(true)));
    assert_eq!(
        positive_replay_false_count(&arena, &originals, &projected).unwrap(),
        0
    );
}

#[test]
fn lazy_ext_branch_select_cycle_repairs_same_branch_store_residual() {
    let mut arena = TermArena::new();
    let a = arena.array_var("a", 4, 8).unwrap();
    let c = arena.array_var("c", 4, 8).unwrap();
    let i = arena.bv_var("i", 4).unwrap();
    let two4 = arena.bv_const(4, 2).unwrap();
    let three4 = arena.bv_const(4, 3).unwrap();
    let five8 = arena.bv_const(8, 5).unwrap();
    let seven8 = arena.bv_const(8, 7).unwrap();
    let false_term = arena.bool_const(false);
    let i_eq_two = arena.eq(i, two4).unwrap();
    let store_a_three = arena.store(a, three4, seven8).unwrap();
    let c_eq_store = arena.eq(c, store_a_three).unwrap();
    let store_branch = arena.and(i_eq_two, c_eq_store).unwrap();
    let blocked_branch = arena.and(false_term, false_term).unwrap();
    let branch_or = arena.or(store_branch, blocked_branch).unwrap();
    let read_a_i = arena.select(a, i).unwrap();
    let five_eq_read = arena.eq(five8, read_a_i).unwrap();
    let assertion = arena.and(branch_or, five_eq_read).unwrap();

    let TermNode::Symbol(a_symbol) = arena.node(a) else {
        panic!("a should be a symbol");
    };
    let TermNode::Symbol(c_symbol) = arena.node(c) else {
        panic!("c should be a symbol");
    };
    let TermNode::Symbol(i_symbol) = arena.node(i) else {
        panic!("i should be a symbol");
    };

    let mut projected = Assignment::new();
    projected.set(
        *a_symbol,
        default_value_for_symbol(&arena, *a_symbol).unwrap(),
    );
    projected.set(
        *c_symbol,
        default_value_for_symbol(&arena, *c_symbol).unwrap(),
    );
    projected.set(*i_symbol, Value::Bv { width: 4, value: 1 });

    let originals = [assertion];
    assert_eq!(
        positive_replay_false_count(&arena, &originals, &projected).unwrap(),
        2
    );
    let failure = first_projected_replay_failure(
        &arena,
        &originals,
        &projected,
        ProjectionRepairStats::default(),
    )
    .unwrap()
    .expect("expected first OR replay failure");
    let failure = replay_failure_with_branch_candidate_diagnostics(
        &arena, &originals, &projected, failure,
    )
    .unwrap();
    let note = failure.note();
    assert!(
        note.contains("chain+same_branch_store_target,status=candidate"),
        "{note}"
    );
    assert!(note.contains("total_false=0"), "{note}");

    let stats = repair_projected_replay_branch_select_cycle(
        &arena,
        &originals,
        branch_or,
        &mut projected,
    )
    .unwrap()
    .expect("expected same-branch store residual repair");
    assert!(stats.branch_symbol_changes >= 2, "{stats:?}");
    assert!(stats.array_changes >= 1, "{stats:?}");
    assert_eq!(
        positive_replay_false_count(&arena, &originals, &projected).unwrap(),
        0
    );
    assert_eq!(
        eval(&arena, five_eq_read, &projected).unwrap(),
        Value::Bool(true)
    );
    assert_eq!(
        eval(&arena, c_eq_store, &projected).unwrap(),
        Value::Bool(true)
    );
}

#[test]
fn lazy_ext_replay_failure_reports_residual_followup_or_diagnostic() {
    let mut arena = TermArena::new();
    let a = arena.array_var("a", 4, 8).unwrap();
    let c = arena.array_var("c", 4, 8).unwrap();
    let d = arena.array_var("d", 4, 8).unwrap();
    let i = arena.bv_var("i", 4).unwrap();
    let two4 = arena.bv_const(4, 2).unwrap();
    let three4 = arena.bv_const(4, 3).unwrap();
    let five8 = arena.bv_const(8, 5).unwrap();
    let seven8 = arena.bv_const(8, 7).unwrap();
    let false_term = arena.bool_const(false);
    let i_eq_two = arena.eq(i, two4).unwrap();
    let store_a_three = arena.store(a, three4, seven8).unwrap();
    let c_eq_store = arena.eq(c, store_a_three).unwrap();
    let store_branch = arena.and(i_eq_two, c_eq_store).unwrap();
    let blocked_branch = arena.and(false_term, false_term).unwrap();
    let first_or = arena.or(store_branch, blocked_branch).unwrap();
    let read_a_i = arena.select(a, i).unwrap();
    let five_eq_read = arena.eq(five8, read_a_i).unwrap();
    let d_eq_c = arena.eq(d, c).unwrap();
    let second_or = arena.or(d_eq_c, blocked_branch).unwrap();
    let first = arena.and(first_or, five_eq_read).unwrap();
    let assertion = arena.and(first, second_or).unwrap();

    let TermNode::Symbol(a_symbol) = arena.node(a) else {
        panic!("a should be a symbol");
    };
    let TermNode::Symbol(c_symbol) = arena.node(c) else {
        panic!("c should be a symbol");
    };
    let TermNode::Symbol(d_symbol) = arena.node(d) else {
        panic!("d should be a symbol");
    };
    let TermNode::Symbol(i_symbol) = arena.node(i) else {
        panic!("i should be a symbol");
    };

    let mut projected = Assignment::new();
    projected.set(
        *a_symbol,
        default_value_for_symbol(&arena, *a_symbol).unwrap(),
    );
    projected.set(
        *c_symbol,
        default_value_for_symbol(&arena, *c_symbol).unwrap(),
    );
    let default_d = default_value_for_symbol(&arena, *d_symbol).unwrap();
    let d_with_entry = store_value(
        &default_d,
        Value::Bv { width: 4, value: 1 },
        Value::Bv { width: 8, value: 9 },
    )
    .unwrap();
    projected.set(*d_symbol, d_with_entry);
    projected.set(*i_symbol, Value::Bv { width: 4, value: 1 });

    let originals = [assertion];
    let failure = first_projected_replay_failure(
        &arena,
        &originals,
        &projected,
        ProjectionRepairStats::default(),
    )
    .unwrap()
    .expect("expected first OR replay failure");
    let failure = replay_failure_with_branch_candidate_diagnostics(
        &arena, &originals, &projected, failure,
    )
    .unwrap();
    let note = failure.note();
    assert!(
        note.contains("chain+same_branch_store_target,status=candidate"),
        "{note}"
    );
    assert!(
        note.contains("chain+same_branch_store_target+followup_or"),
        "{note}"
    );
    assert!(note.contains("target_true=true"), "{note}");
    assert!(note.contains("total_false=0"), "{note}");
}

#[test]
fn lazy_ext_branch_select_cycle_repairs_residual_followup_or_chain() {
    let mut arena = TermArena::new();
    let a = arena.array_var("a", 4, 8).unwrap();
    let c = arena.array_var("c", 4, 8).unwrap();
    let d = arena.array_var("d", 4, 8).unwrap();
    let i = arena.bv_var("i", 4).unwrap();
    let two4 = arena.bv_const(4, 2).unwrap();
    let three4 = arena.bv_const(4, 3).unwrap();
    let five8 = arena.bv_const(8, 5).unwrap();
    let seven8 = arena.bv_const(8, 7).unwrap();
    let false_term = arena.bool_const(false);
    let i_eq_two = arena.eq(i, two4).unwrap();
    let store_a_three = arena.store(a, three4, seven8).unwrap();
    let c_eq_store = arena.eq(c, store_a_three).unwrap();
    let store_branch = arena.and(i_eq_two, c_eq_store).unwrap();
    let blocked_branch = arena.and(false_term, false_term).unwrap();
    let first_or = arena.or(store_branch, blocked_branch).unwrap();
    let read_a_i = arena.select(a, i).unwrap();
    let five_eq_read = arena.eq(five8, read_a_i).unwrap();
    let d_eq_c = arena.eq(d, c).unwrap();
    let second_or = arena.or(d_eq_c, blocked_branch).unwrap();
    let first = arena.and(first_or, five_eq_read).unwrap();
    let assertion = arena.and(first, second_or).unwrap();

    let TermNode::Symbol(a_symbol) = arena.node(a) else {
        panic!("a should be a symbol");
    };
    let TermNode::Symbol(c_symbol) = arena.node(c) else {
        panic!("c should be a symbol");
    };
    let TermNode::Symbol(d_symbol) = arena.node(d) else {
        panic!("d should be a symbol");
    };
    let TermNode::Symbol(i_symbol) = arena.node(i) else {
        panic!("i should be a symbol");
    };

    let default_a = default_value_for_symbol(&arena, *a_symbol).unwrap();
    let default_c = default_value_for_symbol(&arena, *c_symbol).unwrap();
    let default_d = default_value_for_symbol(&arena, *d_symbol).unwrap();
    let mut projected = Assignment::new();
    projected.set(*a_symbol, default_a);
    projected.set(*c_symbol, default_c);
    projected.set(*d_symbol, default_d);
    projected.set(*i_symbol, Value::Bv { width: 4, value: 1 });

    let originals = [assertion];
    assert_eq!(
        positive_replay_false_count(&arena, &originals, &projected).unwrap(),
        2
    );
    let stats = repair_projected_replay_branch_select_cycle(
        &arena,
        &originals,
        first_or,
        &mut projected,
    )
    .unwrap()
    .expect("expected residual follow-up OR repair");
    assert!(stats.branch_symbol_changes >= 3, "{stats:?}");
    assert_eq!(
        positive_replay_false_count(&arena, &originals, &projected).unwrap(),
        0
    );
    assert_eq!(
        eval(&arena, five_eq_read, &projected).unwrap(),
        Value::Bool(true)
    );
    assert_eq!(
        eval(&arena, c_eq_store, &projected).unwrap(),
        Value::Bool(true)
    );
    assert_eq!(eval(&arena, d_eq_c, &projected).unwrap(), Value::Bool(true));
}

#[test]
fn lazy_ext_scalar_branch_choice_prefers_replay_safe_direction() {
    let mut arena = TermArena::new();
    let u = arena.int_var("u").unwrap();
    let v = arena.int_var("v").unwrap();
    let zero = arena.int_const(0);
    let false_term = arena.bool_const(false);
    let u_eq_v = arena.eq(u, v).unwrap();
    let branch_or = arena.or(u_eq_v, false_term).unwrap();
    let u_eq_zero = arena.eq(u, zero).unwrap();
    let assertion = arena.and(branch_or, u_eq_zero).unwrap();

    let TermNode::Symbol(u_symbol) = arena.node(u) else {
        panic!("u should be a symbol");
    };
    let TermNode::Symbol(v_symbol) = arena.node(v) else {
        panic!("v should be a symbol");
    };

    let mut greedy = Assignment::new();
    greedy.set(*u_symbol, Value::Int(0));
    greedy.set(*v_symbol, Value::Int(1));
    let originals = [assertion];
    let greedy_stats =
        repair_projected_branch_as_candidate(&arena, &originals, u_eq_v, &mut greedy)
            .unwrap()
            .expect("expected greedy branch repair");
    assert!(greedy_stats.branch_symbol_changes >= 1);
    assert_eq!(
        positive_replay_false_count(&arena, &originals, &greedy).unwrap(),
        1
    );

    let mut projected = Assignment::new();
    projected.set(*u_symbol, Value::Int(0));
    projected.set(*v_symbol, Value::Int(1));
    let stats = repair_projected_branch_scalar_choice_candidate(
        &arena,
        &originals,
        u_eq_v,
        &mut projected,
    )
    .unwrap()
    .expect("expected scalar choice repair");
    assert_eq!(stats.branch_symbol_changes, 1);
    assert_eq!(projected.get(*u_symbol), Some(Value::Int(0)));
    assert_eq!(projected.get(*v_symbol), Some(Value::Int(0)));
    assert_eq!(
        positive_replay_false_count(&arena, &originals, &projected).unwrap(),
        0
    );
}

#[test]
fn lazy_ext_scalar_closure_guard_rejects_returned_or_loop() {
    let mut arena = TermArena::new();
    let x = arena.int_var("x").unwrap();
    let y = arena.int_var("y").unwrap();
    let z = arena.int_var("z").unwrap();
    let one = arena.int_const(1);
    let two = arena.int_const(2);
    let false_term = arena.bool_const(false);
    let y_eq_x = arena.eq(y, x).unwrap();
    let z_eq_x = arena.eq(z, x).unwrap();
    let branch = arena.and(y_eq_x, z_eq_x).unwrap();
    let disjunction = arena.or(branch, false_term).unwrap();
    let y_eq_one = arena.eq(y, one).unwrap();
    let z_eq_two = arena.eq(z, two).unwrap();
    let rest = arena.and(y_eq_one, z_eq_two).unwrap();
    let assertion = arena.and(disjunction, rest).unwrap();

    let TermNode::Symbol(x_symbol) = arena.node(x) else {
        panic!("x should be a symbol");
    };
    let TermNode::Symbol(y_symbol) = arena.node(y) else {
        panic!("y should be a symbol");
    };
    let TermNode::Symbol(z_symbol) = arena.node(z) else {
        panic!("z should be a symbol");
    };

    let mut projected = Assignment::new();
    projected.set(*x_symbol, Value::Int(0));
    projected.set(*y_symbol, Value::Int(1));
    projected.set(*z_symbol, Value::Int(2));
    let originals = [assertion];
    assert_eq!(
        positive_replay_false_count(&arena, &originals, &projected).unwrap(),
        1
    );

    let mut raw_candidate = projected.clone();
    repair_projected_branch_as_candidate(&arena, &originals, branch, &mut raw_candidate)
        .unwrap()
        .expect("expected raw branch repair");
    assert_eq!(
        eval(&arena, disjunction, &raw_candidate).unwrap(),
        Value::Bool(true)
    );
    assert_eq!(
        positive_replay_false_count(&arena, &originals, &raw_candidate).unwrap(),
        2
    );

    let guarded = repair_projected_branch_best_candidate_with_scalar_closure_guard(
        &arena,
        &originals,
        disjunction,
        branch,
        &mut projected,
    )
    .unwrap();
    assert!(
        guarded.is_none(),
        "closure returns to the same OR without replay improvement"
    );
    assert_eq!(projected.get(*x_symbol), Some(Value::Int(0)));
    assert_eq!(projected.get(*y_symbol), Some(Value::Int(1)));
    assert_eq!(projected.get(*z_symbol), Some(Value::Int(2)));
}

#[test]
fn lazy_ext_branch_schedule_rejects_scalar_closure_loop() {
    let mut arena = TermArena::new();
    let x = arena.int_var("x").unwrap();
    let y = arena.int_var("y").unwrap();
    let z = arena.int_var("z").unwrap();
    let one = arena.int_const(1);
    let two = arena.int_const(2);
    let false_term = arena.bool_const(false);
    let y_eq_x = arena.eq(y, x).unwrap();
    let z_eq_x = arena.eq(z, x).unwrap();
    let branch = arena.and(y_eq_x, z_eq_x).unwrap();
    let disjunction = arena.or(branch, false_term).unwrap();
    let y_eq_one = arena.eq(y, one).unwrap();
    let z_eq_two = arena.eq(z, two).unwrap();
    let rest = arena.and(y_eq_one, z_eq_two).unwrap();
    let assertion = arena.and(disjunction, rest).unwrap();

    let TermNode::Symbol(x_symbol) = arena.node(x) else {
        panic!("x should be a symbol");
    };
    let TermNode::Symbol(y_symbol) = arena.node(y) else {
        panic!("y should be a symbol");
    };
    let TermNode::Symbol(z_symbol) = arena.node(z) else {
        panic!("z should be a symbol");
    };

    let mut projected = Assignment::new();
    projected.set(*x_symbol, Value::Int(0));
    projected.set(*y_symbol, Value::Int(1));
    projected.set(*z_symbol, Value::Int(2));
    let originals = [assertion];

    let mut raw_schedule = projected.clone();
    let raw_stats =
        repair_projected_branch_schedule(&arena, &originals, branch, &mut raw_schedule)
            .unwrap()
            .expect("expected raw schedule to force the branch");
    assert!(raw_stats.branch_symbol_changes >= 2, "{raw_stats:?}");
    assert_eq!(
        positive_replay_false_count(&arena, &originals, &raw_schedule).unwrap(),
        2
    );

    let guarded_stats =
        repair_projected_branch_disjunctions(&arena, &originals, &mut projected).unwrap();
    assert_eq!(guarded_stats.changes(), 0, "{guarded_stats:?}");
    assert_eq!(projected.get(*x_symbol), Some(Value::Int(0)));
    assert_eq!(projected.get(*y_symbol), Some(Value::Int(1)));
    assert_eq!(projected.get(*z_symbol), Some(Value::Int(2)));
}

#[test]
fn lazy_ext_branch_schedule_repairs_select_backed_scalar_literals() {
    let mut arena = TermArena::new();
    let a = arena.array_var("a", 4, 8).unwrap();
    let two = arena.bv_const(4, 2).unwrap();
    let three = arena.bv_const(4, 3).unwrap();
    let one8 = arena.bv_const(8, 1).unwrap();
    let two8 = arena.bv_const(8, 2).unwrap();
    let three8 = arena.bv_const(8, 3).unwrap();
    let y = arena.bv_var("y", 8).unwrap();
    let z = arena.bv_var("z", 8).unwrap();
    let read_two = arena.select(a, two).unwrap();
    let read_three = arena.select(a, three).unwrap();
    let y_eq_read = arena.eq(y, read_two).unwrap();
    let z_eq_read = arena.eq(z, read_three).unwrap();
    let three_eq_y = arena.eq(three8, y).unwrap();
    let three_eq_z = arena.eq(three8, z).unwrap();
    let branch = arena.and(three_eq_y, three_eq_z).unwrap();
    let readbacks = arena.and(y_eq_read, z_eq_read).unwrap();
    let assertion = arena.and(branch, readbacks).unwrap();

    let TermNode::Symbol(a_symbol) = arena.node(a) else {
        panic!("a should be a symbol");
    };
    let TermNode::Symbol(y_symbol) = arena.node(y) else {
        panic!("y should be a symbol");
    };
    let TermNode::Symbol(z_symbol) = arena.node(z) else {
        panic!("z should be a symbol");
    };

    let default_a = default_value_for_symbol(&arena, *a_symbol).unwrap();
    let a_with_two = store_value(
        &default_a,
        Value::Bv { width: 4, value: 2 },
        Value::Bv { width: 8, value: 1 },
    )
    .unwrap();
    let a_with_entries = store_value(
        &a_with_two,
        Value::Bv { width: 4, value: 3 },
        Value::Bv { width: 8, value: 2 },
    )
    .unwrap();
    let mut projected = Assignment::new();
    projected.set(*a_symbol, a_with_entries);
    projected.set(*y_symbol, Value::Bv { width: 8, value: 1 });
    projected.set(*z_symbol, Value::Bv { width: 8, value: 2 });
    let originals = [assertion];
    assert_eq!(
        positive_replay_false_count(&arena, &originals, &projected).unwrap(),
        2
    );

    let stats = repair_projected_branch_schedule(&arena, &originals, branch, &mut projected)
        .unwrap()
        .expect("expected select-backed scalar branch repair");
    assert!(stats.array_changes >= 2, "{stats:?}");
    assert_eq!(
        positive_replay_false_count(&arena, &originals, &projected).unwrap(),
        0
    );
    assert_eq!(
        eval(&arena, y_eq_read, &projected).unwrap(),
        Value::Bool(true)
    );
    assert_eq!(
        eval(&arena, z_eq_read, &projected).unwrap(),
        Value::Bool(true)
    );
    assert_eq!(eval(&arena, branch, &projected).unwrap(), Value::Bool(true));
    assert_eq!(
        eval(&arena, one8, &projected).unwrap(),
        Value::Bv { width: 8, value: 1 }
    );
    assert_eq!(
        eval(&arena, two8, &projected).unwrap(),
        Value::Bv { width: 8, value: 2 }
    );
}

#[test]
fn lazy_ext_scalar_repair_updates_select_backed_symbol() {
    let mut arena = TermArena::new();
    let a = arena.array_var("a", 4, 8).unwrap();
    let two = arena.bv_const(4, 2).unwrap();
    let three8 = arena.bv_const(8, 3).unwrap();
    let y = arena.bv_var("y", 8).unwrap();
    let read = arena.select(a, two).unwrap();
    let y_eq_read = arena.eq(y, read).unwrap();
    let y_eq_three = arena.eq(y, three8).unwrap();

    let TermNode::Symbol(a_symbol) = arena.node(a) else {
        panic!("a should be a symbol");
    };
    let TermNode::Symbol(y_symbol) = arena.node(y) else {
        panic!("y should be a symbol");
    };

    let default_a = default_value_for_symbol(&arena, *a_symbol).unwrap();
    let a_with_two = store_value(
        &default_a,
        Value::Bv { width: 4, value: 2 },
        Value::Bv { width: 8, value: 1 },
    )
    .unwrap();
    let mut projected = Assignment::new();
    projected.set(*a_symbol, a_with_two);
    projected.set(*y_symbol, Value::Bv { width: 8, value: 1 });
    let originals = [y_eq_read, y_eq_three];
    assert_eq!(
        positive_replay_false_count(&arena, &originals, &projected).unwrap(),
        1
    );

    let stats = repair_projected_scalar_equalities(&arena, &originals, &mut projected).unwrap();
    assert!(stats.array_changes >= 1, "{stats:?}");
    assert_eq!(
        positive_replay_false_count(&arena, &originals, &projected).unwrap(),
        0
    );
    assert_eq!(
        eval(&arena, y_eq_read, &projected).unwrap(),
        Value::Bool(true)
    );
    assert_eq!(
        eval(&arena, y_eq_three, &projected).unwrap(),
        Value::Bool(true)
    );
}

#[test]
fn lazy_ext_scalar_repair_stabilizes_returned_array_or() {
    let mut arena = TermArena::new();
    let a = arena.array_var("a", 4, 8).unwrap();
    let b = arena.array_var("b", 4, 8).unwrap();
    let c = arena.array_var("c", 4, 8).unwrap();
    let two = arena.bv_const(4, 2).unwrap();
    let three = arena.bv_const(4, 3).unwrap();
    let one8 = arena.bv_const(8, 1).unwrap();
    let y = arena.bv_var("y", 8).unwrap();
    let z = arena.bv_var("z", 8).unwrap();
    let q = arena.bool_var("q").unwrap();

    let y_read = arena.select(a, two).unwrap();
    let z_read_two = arena.select(c, two).unwrap();
    let z_read_three = arena.select(c, three).unwrap();
    let y_eq_read = arena.eq(y, y_read).unwrap();
    let z_eq_read_two = arena.eq(z, z_read_two).unwrap();
    let z_eq_read_three = arena.eq(z, z_read_three).unwrap();
    let y_eq_z = arena.eq(y, z).unwrap();
    let y_eq_one = arena.eq(y, one8).unwrap();
    let a_eq_b = arena.eq(a, b).unwrap();
    let false_term = arena.bool_const(false);
    let branch_or = arena.or(a_eq_b, false_term).unwrap();
    let prefix = arena.and(y_eq_read, z_eq_read_two).unwrap();
    let prefix = arena.and(prefix, z_eq_read_three).unwrap();
    let prefix = arena.and(prefix, y_eq_z).unwrap();
    let prefix = arena.and(prefix, y_eq_one).unwrap();
    let suffix = arena.and(branch_or, q).unwrap();
    let assertion = arena.and(prefix, suffix).unwrap();

    let TermNode::Symbol(a_symbol) = arena.node(a) else {
        panic!("a should be a symbol");
    };
    let TermNode::Symbol(b_symbol) = arena.node(b) else {
        panic!("b should be a symbol");
    };
    let TermNode::Symbol(c_symbol) = arena.node(c) else {
        panic!("c should be a symbol");
    };
    let TermNode::Symbol(y_symbol) = arena.node(y) else {
        panic!("y should be a symbol");
    };
    let TermNode::Symbol(z_symbol) = arena.node(z) else {
        panic!("z should be a symbol");
    };
    let TermNode::Symbol(q_symbol) = arena.node(q) else {
        panic!("q should be a symbol");
    };

    let default_a = default_value_for_symbol(&arena, *a_symbol).unwrap();
    let default_b = default_value_for_symbol(&arena, *b_symbol).unwrap();
    let default_c = default_value_for_symbol(&arena, *c_symbol).unwrap();
    let c_with_two = store_value(
        &default_c,
        Value::Bv { width: 4, value: 2 },
        Value::Bv { width: 8, value: 1 },
    )
    .unwrap();
    let c_with_entries = store_value(
        &c_with_two,
        Value::Bv { width: 4, value: 3 },
        Value::Bv { width: 8, value: 1 },
    )
    .unwrap();

    let mut projected = Assignment::new();
    projected.set(*a_symbol, default_a);
    projected.set(*b_symbol, default_b);
    projected.set(*c_symbol, c_with_entries);
    projected.set(*y_symbol, Value::Bv { width: 8, value: 0 });
    projected.set(*z_symbol, Value::Bv { width: 8, value: 1 });
    projected.set(*q_symbol, Value::Bool(false));
    let originals = [assertion];
    assert_eq!(
        positive_replay_false_count(&arena, &originals, &projected).unwrap(),
        3
    );
    assert_eq!(
        eval(&arena, branch_or, &projected).unwrap(),
        Value::Bool(true)
    );

    let stats = repair_projected_scalar_equalities(&arena, &originals, &mut projected).unwrap();
    assert!(stats.scalar_stabilized_trials >= 1, "{stats:?}");
    assert!(stats.branch_symbol_changes >= 1, "{stats:?}");
    assert_eq!(
        positive_replay_false_count(&arena, &originals, &projected).unwrap(),
        1
    );
    assert_eq!(eval(&arena, y_eq_z, &projected).unwrap(), Value::Bool(true));
    assert_eq!(
        eval(&arena, y_eq_one, &projected).unwrap(),
        Value::Bool(true)
    );
    assert_eq!(
        eval(&arena, branch_or, &projected).unwrap(),
        Value::Bool(true)
    );
    assert_eq!(eval(&arena, q, &projected).unwrap(), Value::Bool(false));
}

#[test]
#[allow(clippy::too_many_lines)]
fn lazy_ext_scalar_candidate_reports_returned_or_stabilization() {
    let mut arena = TermArena::new();
    let a = arena.array_var("a", 4, 8).unwrap();
    let b = arena.array_var("b", 4, 8).unwrap();
    let c = arena.array_var("c", 4, 8).unwrap();
    let two = arena.bv_const(4, 2).unwrap();
    let three = arena.bv_const(4, 3).unwrap();
    let one8 = arena.bv_const(8, 1).unwrap();
    let y = arena.bv_var("y", 8).unwrap();
    let z = arena.bv_var("z", 8).unwrap();
    let q = arena.bool_var("q").unwrap();

    let y_read = arena.select(a, two).unwrap();
    let z_read_two = arena.select(c, two).unwrap();
    let z_read_three = arena.select(c, three).unwrap();
    let y_eq_read = arena.eq(y, y_read).unwrap();
    let z_eq_read_two = arena.eq(z, z_read_two).unwrap();
    let z_eq_read_three = arena.eq(z, z_read_three).unwrap();
    let y_eq_z = arena.eq(y, z).unwrap();
    let y_eq_one = arena.eq(y, one8).unwrap();
    let a_eq_b = arena.eq(a, b).unwrap();
    let false_term = arena.bool_const(false);
    let branch_or = arena.or(a_eq_b, false_term).unwrap();
    let mut assertion = arena.and(y_eq_read, z_eq_read_two).unwrap();
    assertion = arena.and(assertion, z_eq_read_three).unwrap();
    assertion = arena.and(assertion, y_eq_z).unwrap();
    assertion = arena.and(assertion, y_eq_one).unwrap();
    assertion = arena.and(assertion, branch_or).unwrap();
    assertion = arena.and(assertion, q).unwrap();
    for _ in 0..65 {
        let true_term = arena.bool_const(true);
        assertion = arena.and(true_term, assertion).unwrap();
    }

    let TermNode::Symbol(a_symbol) = arena.node(a) else {
        panic!("a should be a symbol");
    };
    let TermNode::Symbol(b_symbol) = arena.node(b) else {
        panic!("b should be a symbol");
    };
    let TermNode::Symbol(c_symbol) = arena.node(c) else {
        panic!("c should be a symbol");
    };
    let TermNode::Symbol(y_symbol) = arena.node(y) else {
        panic!("y should be a symbol");
    };
    let TermNode::Symbol(z_symbol) = arena.node(z) else {
        panic!("z should be a symbol");
    };
    let TermNode::Symbol(q_symbol) = arena.node(q) else {
        panic!("q should be a symbol");
    };

    let default_c = default_value_for_symbol(&arena, *c_symbol).unwrap();
    let c_with_two = store_value(
        &default_c,
        Value::Bv { width: 4, value: 2 },
        Value::Bv { width: 8, value: 1 },
    )
    .unwrap();
    let c_with_entries = store_value(
        &c_with_two,
        Value::Bv { width: 4, value: 3 },
        Value::Bv { width: 8, value: 1 },
    )
    .unwrap();
    let mut projected = Assignment::new();
    projected.set(
        *a_symbol,
        default_value_for_symbol(&arena, *a_symbol).unwrap(),
    );
    projected.set(
        *b_symbol,
        default_value_for_symbol(&arena, *b_symbol).unwrap(),
    );
    projected.set(*c_symbol, c_with_entries);
    projected.set(*y_symbol, Value::Bv { width: 8, value: 0 });
    projected.set(*z_symbol, Value::Bv { width: 8, value: 1 });
    projected.set(*q_symbol, Value::Bool(false));

    let originals = [assertion];
    assert!(positive_replay_conjunct_count(&arena, &originals) > 64);
    let failure = first_projected_replay_failure(
        &arena,
        &originals,
        &projected,
        ProjectionRepairStats::default(),
    )
    .unwrap()
    .expect("expected scalar replay failure");
    assert_eq!(failure.conjunct_term, y_eq_z);
    let enriched = replay_failure_with_branch_candidate_diagnostics(
        &arena, &originals, &projected, failure,
    )
    .unwrap();
    let note = enriched.note();
    assert!(
        note.contains(&format!(
            "returned_or_stabilization_branch_term={}",
            a_eq_b.index()
        )),
        "{note}"
    );
    assert!(
        note.contains("returned_or_stabilization_status=improves"),
        "{note}"
    );
    assert!(
        note.contains("returned_or_stabilization_total_false=1"),
        "{note}"
    );
    assert!(
        note.contains(&format!(
            "returned_or_stabilization_global_false_term={}",
            q.index()
        )),
        "{note}"
    );
}

#[test]
fn lazy_ext_replay_failure_reports_scalar_candidate_diagnostics() {
    let mut arena = TermArena::new();
    let a = arena.array_var("a", 4, 8).unwrap();
    let two = arena.bv_const(4, 2).unwrap();
    let three8 = arena.bv_const(8, 3).unwrap();
    let y = arena.bv_var("y", 8).unwrap();
    let read = arena.select(a, two).unwrap();
    let y_eq_read = arena.eq(y, read).unwrap();
    let y_eq_three = arena.eq(y, three8).unwrap();

    let TermNode::Symbol(a_symbol) = arena.node(a) else {
        panic!("a should be a symbol");
    };
    let TermNode::Symbol(y_symbol) = arena.node(y) else {
        panic!("y should be a symbol");
    };

    let default_a = default_value_for_symbol(&arena, *a_symbol).unwrap();
    let a_with_two = store_value(
        &default_a,
        Value::Bv { width: 4, value: 2 },
        Value::Bv { width: 8, value: 1 },
    )
    .unwrap();
    let mut projected = Assignment::new();
    projected.set(*a_symbol, a_with_two);
    projected.set(*y_symbol, Value::Bv { width: 8, value: 1 });
    let originals = [y_eq_read, y_eq_three];

    let failure = first_projected_replay_failure(
        &arena,
        &originals,
        &projected,
        ProjectionRepairStats::default(),
    )
    .unwrap()
    .expect("expected scalar replay failure");
    assert_eq!(failure.conjunct_term, y_eq_three);

    let enriched = replay_failure_with_branch_candidate_diagnostics(
        &arena, &originals, &projected, failure,
    )
    .unwrap();
    let note = enriched.note();
    assert!(note.contains("scalar_candidate_diagnostics=["), "{note}");
    assert!(note.contains("literal_true=true"), "{note}");
    assert!(note.contains("status=improves,total_false=0"), "{note}");
}

#[test]
fn lazy_ext_scalar_candidate_reports_followup_or_diagnostic() {
    let mut arena = TermArena::new();
    let x = arena.int_var("x").unwrap();
    let y = arena.int_var("y").unwrap();
    let z = arena.int_var("z").unwrap();
    let one = arena.int_const(1);
    let false_term = arena.bool_const(false);
    let x_eq_y = arena.eq(x, y).unwrap();
    let z_eq_x = arena.eq(z, x).unwrap();
    let followup_or = arena.or(z_eq_x, false_term).unwrap();
    let z_eq_one = arena.eq(z, one).unwrap();
    let prefix = arena.and(x_eq_y, followup_or).unwrap();
    let assertion = arena.and(prefix, z_eq_one).unwrap();

    let TermNode::Symbol(x_symbol) = arena.node(x) else {
        panic!("x should be a symbol");
    };
    let TermNode::Symbol(y_symbol) = arena.node(y) else {
        panic!("y should be a symbol");
    };
    let TermNode::Symbol(z_symbol) = arena.node(z) else {
        panic!("z should be a symbol");
    };

    let mut projected = Assignment::new();
    projected.set(*x_symbol, Value::Int(0));
    projected.set(*y_symbol, Value::Int(1));
    projected.set(*z_symbol, Value::Int(0));
    let originals = [assertion];
    assert_eq!(eval(&arena, z_eq_x, &projected).unwrap(), Value::Bool(true));
    assert_eq!(
        positive_replay_false_count(&arena, &originals, &projected).unwrap(),
        2
    );

    let failure = first_projected_replay_failure(
        &arena,
        &originals,
        &projected,
        ProjectionRepairStats::default(),
    )
    .unwrap()
    .expect("expected scalar replay failure");
    assert_eq!(failure.conjunct_term, x_eq_y);

    let enriched = replay_failure_with_branch_candidate_diagnostics(
        &arena, &originals, &projected, failure,
    )
    .unwrap();
    let note = enriched.note();
    assert!(note.contains("scalar_candidate_diagnostics=["), "{note}");
    assert!(
        note.contains(&format!("followup_or_term={}", followup_or.index())),
        "{note}"
    );
    assert!(
        note.contains(&format!("followup_branch_term={}", z_eq_x.index())),
        "{note}"
    );
    assert!(note.contains("followup_status=closes"), "{note}");
    assert!(note.contains("followup_kind=branch"), "{note}");
    assert!(note.contains("followup_final_branch_false=0"), "{note}");
    assert!(note.contains("followup_total_false=0"), "{note}");
}

#[test]
fn lazy_ext_scalar_candidate_reports_followup_or_closure_loop() {
    let mut arena = TermArena::new();
    let x = arena.int_var("x").unwrap();
    let y = arena.int_var("y").unwrap();
    let z = arena.int_var("z").unwrap();
    let zero = arena.int_const(0);
    let false_term = arena.bool_const(false);
    let y_plus_zero = arena.int_add(y, zero).unwrap();
    let x_eq_y = arena.eq(x, y_plus_zero).unwrap();
    let x_eq_z = arena.eq(x, z).unwrap();
    let followup_or = arena.or(x_eq_z, false_term).unwrap();
    let z_eq_zero = arena.eq(z, zero).unwrap();
    let prefix = arena.and(x_eq_y, followup_or).unwrap();
    let assertion = arena.and(prefix, z_eq_zero).unwrap();

    let TermNode::Symbol(x_symbol) = arena.node(x) else {
        panic!("x should be a symbol");
    };
    let TermNode::Symbol(y_symbol) = arena.node(y) else {
        panic!("y should be a symbol");
    };
    let TermNode::Symbol(z_symbol) = arena.node(z) else {
        panic!("z should be a symbol");
    };

    let mut projected = Assignment::new();
    projected.set(*x_symbol, Value::Int(0));
    projected.set(*y_symbol, Value::Int(1));
    projected.set(*z_symbol, Value::Int(0));
    let originals = [assertion];
    let failure = first_projected_replay_failure(
        &arena,
        &originals,
        &projected,
        ProjectionRepairStats::default(),
    )
    .unwrap()
    .expect("expected scalar replay failure");
    assert_eq!(failure.conjunct_term, x_eq_y);

    let enriched = replay_failure_with_branch_candidate_diagnostics(
        &arena, &originals, &projected, failure,
    )
    .unwrap();
    let note = enriched.note();
    assert!(
        note.contains(&format!("followup_or_term={}", followup_or.index())),
        "{note}"
    );
    assert!(note.contains("followup_status=guarded_loop"), "{note}");
    assert!(note.contains("followup_closure_steps=1"), "{note}");
    assert!(note.contains("followup_closure_step_details=["), "{note}");
    assert!(note.contains("followup_closure_branch_false=1"), "{note}");
    assert!(note.contains("followup_closure_total_false=1"), "{note}");
    assert!(
        note.contains(&format!(
            "followup_closure_global_false_term={}",
            followup_or.index()
        )),
        "{note}"
    );
    assert!(
        note.contains(&format!(
            "followup_closure_global_false_or_best_branch_term={}",
            x_eq_z.index()
        )),
        "{note}"
    );
    assert!(
        note.contains(&format!(
            "followup_closure_global_false_or_best_branch_first_false_term={}",
            x_eq_z.index()
        )),
        "{note}"
    );
}

#[test]
fn lazy_ext_scalar_candidate_reports_followup_two_or_cycle() {
    let mut arena = TermArena::new();
    let x = arena.int_var("x").unwrap();
    let y = arena.int_var("y").unwrap();
    let z = arena.int_var("z").unwrap();
    let zero = arena.int_const(0);
    let false_term = arena.bool_const(false);
    let y_plus_zero = arena.int_add(y, zero).unwrap();
    let x_plus_zero = arena.int_add(x, zero).unwrap();
    let x_eq_y = arena.eq(x, y_plus_zero).unwrap();
    let z_eq_x = arena.eq(z, x_plus_zero).unwrap();
    let first_or = arena.or(z_eq_x, false_term).unwrap();
    let z_eq_zero = arena.eq(z, zero).unwrap();
    let second_or = arena.or(z_eq_zero, false_term).unwrap();
    let prefix = arena.and(x_eq_y, first_or).unwrap();
    let assertion = arena.and(prefix, second_or).unwrap();

    let TermNode::Symbol(x_symbol) = arena.node(x) else {
        panic!("x should be a symbol");
    };
    let TermNode::Symbol(y_symbol) = arena.node(y) else {
        panic!("y should be a symbol");
    };
    let TermNode::Symbol(z_symbol) = arena.node(z) else {
        panic!("z should be a symbol");
    };

    let mut projected = Assignment::new();
    projected.set(*x_symbol, Value::Int(0));
    projected.set(*y_symbol, Value::Int(1));
    projected.set(*z_symbol, Value::Int(0));
    let originals = [assertion];
    let failure = first_projected_replay_failure(
        &arena,
        &originals,
        &projected,
        ProjectionRepairStats::default(),
    )
    .unwrap()
    .expect("expected scalar replay failure");
    assert_eq!(failure.conjunct_term, x_eq_y);

    let enriched = replay_failure_with_branch_candidate_diagnostics(
        &arena, &originals, &projected, failure,
    )
    .unwrap();
    let note = enriched.note();
    assert!(
        note.contains(&format!("followup_or_term={}", first_or.index())),
        "{note}"
    );
    assert!(
        note.contains(&format!("followup_next_or_term={}", second_or.index())),
        "{note}"
    );
    assert!(
        note.contains(&format!("followup_branch_term={}", z_eq_x.index())),
        "{note}"
    );
    assert!(
        note.contains(&format!("followup_next_branch_term={}", z_eq_zero.index())),
        "{note}"
    );
    assert!(
        note.contains("followup_next_status=returns_first_or"),
        "{note}"
    );
    assert!(note.contains("followup_next_total_false=1"), "{note}");
    assert!(
        note.contains(&format!(
            "followup_next_global_false_term={}",
            first_or.index()
        )),
        "{note}"
    );
    assert!(
        note.contains(&format!(
            "followup_next_global_false_or_best_branch_term={}",
            z_eq_x.index()
        )),
        "{note}"
    );
    assert!(
        note.contains(&format!(
            "followup_next_global_false_or_best_branch_first_false_term={}",
            z_eq_x.index()
        )),
        "{note}"
    );
}

#[test]
fn lazy_ext_branch_repair_rejects_followup_two_or_cycle() {
    let mut arena = TermArena::new();
    let x = arena.int_var("x").unwrap();
    let y = arena.int_var("y").unwrap();
    let z = arena.int_var("z").unwrap();
    let zero = arena.int_const(0);
    let false_term = arena.bool_const(false);
    let y_plus_zero = arena.int_add(y, zero).unwrap();
    let x_plus_zero = arena.int_add(x, zero).unwrap();
    let x_eq_y = arena.eq(x, y_plus_zero).unwrap();
    let z_eq_x = arena.eq(z, x_plus_zero).unwrap();
    let first_or = arena.or(z_eq_x, false_term).unwrap();
    let z_eq_zero = arena.eq(z, zero).unwrap();
    let second_or = arena.or(z_eq_zero, false_term).unwrap();
    let prefix = arena.and(x_eq_y, first_or).unwrap();
    let assertion = arena.and(prefix, second_or).unwrap();

    let TermNode::Symbol(x_symbol) = arena.node(x) else {
        panic!("x should be a symbol");
    };
    let TermNode::Symbol(y_symbol) = arena.node(y) else {
        panic!("y should be a symbol");
    };
    let TermNode::Symbol(z_symbol) = arena.node(z) else {
        panic!("z should be a symbol");
    };

    let mut projected = Assignment::new();
    projected.set(*x_symbol, Value::Int(1));
    projected.set(*y_symbol, Value::Int(1));
    projected.set(*z_symbol, Value::Int(0));
    let originals = [assertion];
    assert_eq!(eval(&arena, x_eq_y, &projected).unwrap(), Value::Bool(true));
    assert_eq!(
        first_projected_replay_failure(
            &arena,
            &originals,
            &projected,
            ProjectionRepairStats::default(),
        )
        .unwrap()
        .expect("expected first OR failure")
        .conjunct_term,
        first_or
    );
    assert_eq!(
        positive_replay_false_count(&arena, &originals, &projected).unwrap(),
        1
    );

    let mut raw = projected.clone();
    repair_projected_branch_as_candidate(&arena, &originals, z_eq_x, &mut raw)
        .unwrap()
        .expect("expected raw first-OR branch repair");
    assert_eq!(eval(&arena, first_or, &raw).unwrap(), Value::Bool(true));
    assert_eq!(eval(&arena, second_or, &raw).unwrap(), Value::Bool(false));

    let failure = first_projected_replay_failure(
        &arena,
        &originals,
        &projected,
        ProjectionRepairStats::default(),
    )
    .unwrap()
    .expect("expected first OR failure");
    let guarded =
        repair_projected_replay_failure(&arena, &originals, &mut projected, &failure).unwrap();
    assert!(guarded.is_none(), "two-OR toggle should be rejected");
    assert_eq!(projected.get(*x_symbol), Some(Value::Int(1)));
    assert_eq!(projected.get(*y_symbol), Some(Value::Int(1)));
    assert_eq!(projected.get(*z_symbol), Some(Value::Int(0)));
}

#[test]
fn lazy_ext_targeted_replay_repairs_select_backed_scalar_failure() {
    let mut arena = TermArena::new();
    let a = arena.array_var("a", 4, 8).unwrap();
    let two = arena.bv_const(4, 2).unwrap();
    let three8 = arena.bv_const(8, 3).unwrap();
    let y = arena.bv_var("y", 8).unwrap();
    let read = arena.select(a, two).unwrap();
    let y_eq_read = arena.eq(y, read).unwrap();
    let y_eq_three = arena.eq(y, three8).unwrap();

    let TermNode::Symbol(a_symbol) = arena.node(a) else {
        panic!("a should be a symbol");
    };
    let TermNode::Symbol(y_symbol) = arena.node(y) else {
        panic!("y should be a symbol");
    };

    let default_a = default_value_for_symbol(&arena, *a_symbol).unwrap();
    let a_with_two = store_value(
        &default_a,
        Value::Bv { width: 4, value: 2 },
        Value::Bv { width: 8, value: 1 },
    )
    .unwrap();
    let mut projected = Assignment::new();
    projected.set(*a_symbol, a_with_two);
    projected.set(*y_symbol, Value::Bv { width: 8, value: 1 });
    let originals = [y_eq_read, y_eq_three];
    let failure = first_projected_replay_failure(
        &arena,
        &originals,
        &projected,
        ProjectionRepairStats::default(),
    )
    .unwrap()
    .expect("expected scalar replay failure");

    let stats = repair_projected_replay_failure(&arena, &originals, &mut projected, &failure)
        .unwrap()
        .expect("expected targeted scalar repair");
    assert!(stats.array_changes >= 1, "{stats:?}");
    assert_eq!(
        positive_replay_false_count(&arena, &originals, &projected).unwrap(),
        0
    );
}

#[test]
fn lazy_ext_replay_failure_reports_scalar_choice_side_effects() {
    let mut arena = TermArena::new();
    let x = arena.int_var("x").unwrap();
    let y = arena.int_var("y").unwrap();
    let z = arena.int_var("z").unwrap();
    let zero = arena.int_const(0);
    let false_term = arena.bool_const(false);
    let x_eq_y = arena.eq(x, y).unwrap();
    let y_eq_z = arena.eq(y, z).unwrap();
    let branch = arena.and(x_eq_y, y_eq_z).unwrap();
    let blocked_branch = arena.and(false_term, false_term).unwrap();
    let branch_or = arena.or(branch, blocked_branch).unwrap();
    let x_eq_zero = arena.eq(x, zero).unwrap();
    let assertion = arena.and(branch_or, x_eq_zero).unwrap();

    let TermNode::Symbol(x_symbol) = arena.node(x) else {
        panic!("x should be a symbol");
    };
    let TermNode::Symbol(y_symbol) = arena.node(y) else {
        panic!("y should be a symbol");
    };
    let TermNode::Symbol(z_symbol) = arena.node(z) else {
        panic!("z should be a symbol");
    };

    let mut projected = Assignment::new();
    projected.set(*x_symbol, Value::Int(0));
    projected.set(*y_symbol, Value::Int(1));
    projected.set(*z_symbol, Value::Int(2));

    let originals = [assertion];
    let failure = first_projected_replay_failure(
        &arena,
        &originals,
        &projected,
        ProjectionRepairStats::default(),
    )
    .unwrap()
    .expect("expected scalar OR replay failure");
    let failure = replay_failure_with_branch_candidate_diagnostics(
        &arena, &originals, &projected, failure,
    )
    .unwrap();
    let note = failure.note();
    assert!(
        note.contains("failed_or_best_branch_false_literal_details=["),
        "{note}"
    );
    assert!(note.contains(&format!("term={}", x_eq_y.index())), "{note}");
    assert!(note.contains(&format!("term={}", y_eq_z.index())), "{note}");
    assert!(note.contains("scalar_choices=("), "{note}");
    assert!(note.contains("literal_true=true"), "{note}");
    assert!(note.contains("branch_false=1"), "{note}");
    assert!(note.contains("global_false_term="), "{note}");
    assert!(
        note.contains("failed_or_best_branch_paired_scalar_chain=("),
        "{note}"
    );
    assert!(note.contains("branch_steps=["), "{note}");
    assert!(note.contains("followup_steps=[]"), "{note}");
    assert!(note.contains("final_branch_false=0"), "{note}");
    assert!(note.contains("final_total_false=0"), "{note}");
    assert!(
        note.contains("failed_or_scalar_closure_branch_candidates=["),
        "{note}"
    );
    assert!(note.contains("#0:init=2"), "{note}");
    assert!(note.contains("raw_branch_false=0"), "{note}");
    assert!(note.contains("final_branch_false=0"), "{note}");
    assert!(note.contains("final_total_false=0"), "{note}");
}

#[test]
fn lazy_ext_replay_failure_reports_select_candidate_diagnostics() {
    let mut arena = TermArena::new();
    let a = arena.array_var("a", 4, 8).unwrap();
    let i = arena.bv_var("i", 4).unwrap();
    let y = arena.bv_var("y", 8).unwrap();
    let h = arena.bool_var("h").unwrap();
    let read = arena.select(a, i).unwrap();
    let y_eq_read = arena.eq(y, read).unwrap();
    let assertion = arena.and(y_eq_read, h).unwrap();

    let TermNode::Symbol(a_symbol) = arena.node(a) else {
        panic!("a should be a symbol");
    };
    let TermNode::Symbol(i_symbol) = arena.node(i) else {
        panic!("i should be a symbol");
    };
    let TermNode::Symbol(y_symbol) = arena.node(y) else {
        panic!("y should be a symbol");
    };
    let TermNode::Symbol(h_symbol) = arena.node(h) else {
        panic!("h should be a symbol");
    };

    let mut projected = Assignment::new();
    let default_a = default_value_for_symbol(&arena, *a_symbol).unwrap();
    projected.set(*a_symbol, default_a);
    projected.set(*i_symbol, Value::Bv { width: 4, value: 1 });
    projected.set(*y_symbol, Value::Bv { width: 8, value: 7 });
    projected.set(*h_symbol, Value::Bool(false));

    let originals = [assertion];
    let failure = first_projected_replay_failure(
        &arena,
        &originals,
        &projected,
        ProjectionRepairStats::default(),
    )
    .unwrap()
    .expect("expected select replay failure");
    let failure = replay_failure_with_branch_candidate_diagnostics(
        &arena, &originals, &projected, failure,
    )
    .unwrap();
    let note = failure.note();
    assert!(note.contains("select_candidate_diagnostics=["));
    assert!(note.contains("chain:status=candidate"), "{note}");
    assert!(note.contains("direct:status=candidate"), "{note}");
    assert!(note.contains("global_false_ordinal=1"), "{note}");
}

#[test]
fn lazy_ext_select_repair_beam_composes_followup_or_repair() {
    let mut arena = TermArena::new();
    let a = arena.array_var("a", 4, 8).unwrap();
    let i = arena.bv_var("i", 4).unwrap();
    let y = arena.bv_var("y", 8).unwrap();
    let z = arena.bv_var("z", 8).unwrap();
    let x = arena.int_var("x").unwrap();
    let q = arena.bool_var("q").unwrap();
    let read = arena.select(a, i).unwrap();
    let y_eq_read = arena.eq(y, read).unwrap();
    let one = arena.int_const(1);
    let x_eq_one = arena.eq(x, one).unwrap();
    let branch_or = arena.or(x_eq_one, q).unwrap();
    let z_eq_read = arena.eq(z, read).unwrap();
    let zero8 = arena.bv_const(8, 0).unwrap();
    let z_eq_zero = arena.eq(z, zero8).unwrap();
    let prefix = arena.and(y_eq_read, branch_or).unwrap();
    let suffix = arena.and(z_eq_read, z_eq_zero).unwrap();
    let assertion = arena.and(prefix, suffix).unwrap();

    let TermNode::Symbol(a_symbol) = arena.node(a) else {
        panic!("a should be a symbol");
    };
    let TermNode::Symbol(i_symbol) = arena.node(i) else {
        panic!("i should be a symbol");
    };
    let TermNode::Symbol(y_symbol) = arena.node(y) else {
        panic!("y should be a symbol");
    };
    let TermNode::Symbol(z_symbol) = arena.node(z) else {
        panic!("z should be a symbol");
    };
    let TermNode::Symbol(x_symbol) = arena.node(x) else {
        panic!("x should be a symbol");
    };
    let TermNode::Symbol(q_symbol) = arena.node(q) else {
        panic!("q should be a symbol");
    };

    let mut projected = Assignment::new();
    projected.set(
        *a_symbol,
        default_value_for_symbol(&arena, *a_symbol).unwrap(),
    );
    projected.set(*i_symbol, Value::Bv { width: 4, value: 1 });
    projected.set(*y_symbol, Value::Bv { width: 8, value: 7 });
    projected.set(*z_symbol, Value::Bv { width: 8, value: 0 });
    projected.set(*x_symbol, Value::Int(0));
    projected.set(*q_symbol, Value::Bool(false));

    let originals = [assertion];
    assert_eq!(
        positive_replay_false_count(&arena, &originals, &projected).unwrap(),
        2
    );
    let failure = first_projected_replay_failure(
        &arena,
        &originals,
        &projected,
        ProjectionRepairStats::default(),
    )
    .unwrap()
    .expect("expected direct select replay failure");
    assert_eq!(failure.conjunct_term, y_eq_read);

    let stats = repair_projected_replay_failure(&arena, &originals, &mut projected, &failure)
        .unwrap()
        .expect("expected composed select/OR repair");
    assert!(stats.array_changes >= 1, "{stats:?}");
    assert!(stats.branch_symbol_changes >= 1, "{stats:?}");
    assert_eq!(projected.get(*x_symbol), Some(Value::Int(1)));
    assert_eq!(
        positive_replay_false_count(&arena, &originals, &projected).unwrap(),
        1
    );
    assert_eq!(
        first_projected_replay_failure(
            &arena,
            &originals,
            &projected,
            ProjectionRepairStats::default(),
        )
        .unwrap()
        .expect("only the dependent z readback should remain false")
        .conjunct_term,
        z_eq_read
    );
}

#[test]
fn lazy_ext_or_repair_beam_composes_followup_select_repair() {
    let mut arena = TermArena::new();
    let a = arena.array_var("a", 4, 8).unwrap();
    let i = arena.bv_var("i", 4).unwrap();
    let j = arena.bv_var("j", 4).unwrap();
    let y = arena.bv_var("y", 8).unwrap();
    let q = arena.bool_var("q").unwrap();
    let h = arena.bool_var("h").unwrap();
    let i_eq_j = arena.eq(i, j).unwrap();
    let branch_or = arena.or(i_eq_j, q).unwrap();
    let read = arena.select(a, i).unwrap();
    let y_eq_read = arena.eq(y, read).unwrap();
    let zero8 = arena.bv_const(8, 0).unwrap();
    let y_eq_zero = arena.eq(y, zero8).unwrap();
    let prefix = arena.and(branch_or, y_eq_read).unwrap();
    let suffix = arena.and(y_eq_zero, h).unwrap();
    let assertion = arena.and(prefix, suffix).unwrap();

    let TermNode::Symbol(a_symbol) = arena.node(a) else {
        panic!("a should be a symbol");
    };
    let TermNode::Symbol(i_symbol) = arena.node(i) else {
        panic!("i should be a symbol");
    };
    let TermNode::Symbol(j_symbol) = arena.node(j) else {
        panic!("j should be a symbol");
    };
    let TermNode::Symbol(y_symbol) = arena.node(y) else {
        panic!("y should be a symbol");
    };
    let TermNode::Symbol(q_symbol) = arena.node(q) else {
        panic!("q should be a symbol");
    };
    let TermNode::Symbol(h_symbol) = arena.node(h) else {
        panic!("h should be a symbol");
    };

    let mut projected = Assignment::new();
    let default_a = default_value_for_symbol(&arena, *a_symbol).unwrap();
    let a_value = store_value(
        &default_a,
        Value::Bv { width: 4, value: 2 },
        Value::Bv { width: 8, value: 7 },
    )
    .unwrap();
    projected.set(*a_symbol, a_value);
    projected.set(*i_symbol, Value::Bv { width: 4, value: 1 });
    projected.set(*j_symbol, Value::Bv { width: 4, value: 2 });
    projected.set(*y_symbol, Value::Bv { width: 8, value: 0 });
    projected.set(*q_symbol, Value::Bool(false));
    projected.set(*h_symbol, Value::Bool(false));

    let originals = [assertion];
    assert_eq!(
        positive_replay_false_count(&arena, &originals, &projected).unwrap(),
        2
    );
    let failure = first_projected_replay_failure(
        &arena,
        &originals,
        &projected,
        ProjectionRepairStats::default(),
    )
    .unwrap()
    .expect("expected generated OR replay failure");
    assert_eq!(failure.conjunct_term, branch_or);

    let stats = repair_projected_replay_failure(&arena, &originals, &mut projected, &failure)
        .unwrap()
        .expect("expected composed OR/select repair");
    assert!(stats.branch_symbol_changes >= 1, "{stats:?}");
    assert!(stats.array_changes >= 1, "{stats:?}");
    assert_eq!(
        projected.get(*i_symbol),
        Some(Value::Bv { width: 4, value: 2 })
    );
    assert_eq!(
        positive_replay_false_count(&arena, &originals, &projected).unwrap(),
        1
    );
    assert_eq!(
        first_projected_replay_failure(
            &arena,
            &originals,
            &projected,
            ProjectionRepairStats::default(),
        )
        .unwrap()
        .expect("only h should remain false")
        .conjunct_term,
        h
    );
}

#[test]
fn lazy_ext_projection_repairs_single_false_branch_symbol_equality() {
    let mut arena = TermArena::new();
    let a = arena.array_var("a", 4, 8).unwrap();
    let b = arena.array_var("b", 4, 8).unwrap();
    let i = arena.bv_var("i", 4).unwrap();
    let j = arena.bv_var("j", 4).unwrap();
    let v = arena.bv_var("v", 8).unwrap();
    let y = arena.bv_var("y", 8).unwrap();
    let z = arena.bv_var("z", 8).unwrap();
    let p = arena.bool_var("p").unwrap();
    let stored = arena.store(a, i, v).unwrap();
    let b_eq_stored = arena.eq(b, stored).unwrap();
    let branch_assertion = arena.or(b_eq_stored, p).unwrap();
    let read_b_j = arena.select(b, j).unwrap();
    let y_eq_read = arena.eq(y, read_b_j).unwrap();
    let read_a_j = arena.select(a, j).unwrap();
    let z_eq_base_read = arena.eq(z, read_a_j).unwrap();

    let mut candidate = Assignment::new();
    for (symbol, name, sort) in arena.symbols() {
        match name {
            "i" => candidate.set(symbol, Value::Bv { width: 4, value: 0 }),
            "j" => candidate.set(symbol, Value::Bv { width: 4, value: 1 }),
            "v" => candidate.set(symbol, Value::Bv { width: 8, value: 7 }),
            "y" => candidate.set(symbol, Value::Bv { width: 8, value: 3 }),
            "z" => candidate.set(symbol, Value::Bv { width: 8, value: 0 }),
            "p" => candidate.set(symbol, Value::Bool(false)),
            _ if sort == Sort::BitVec(4) => {
                candidate.set(symbol, Value::Bv { width: 4, value: 0 });
            }
            _ if sort == Sort::BitVec(8) => {
                candidate.set(symbol, Value::Bv { width: 8, value: 0 });
            }
            _ => {}
        }
    }

    let ctx = RowCtx::default();
    let originals = [branch_assertion, y_eq_read, z_eq_base_read];
    let ExtReplay::Sat(model) =
        project_replay_ext_candidate(&arena, &ctx, &originals, &candidate).unwrap()
    else {
        panic!("expected branch-repaired projection to replay");
    };
    let assignment = model.to_assignment();
    let TermNode::Symbol(z_symbol) = arena.node(z) else {
        panic!("z should be a symbol");
    };
    assert_eq!(
        assignment.get(*z_symbol),
        Some(Value::Bv { width: 8, value: 3 })
    );
    for &original in &originals {
        assert_eq!(
            eval(&arena, original, &assignment).unwrap(),
            Value::Bool(true)
        );
    }
}

#[test]
fn lazy_ext_targeted_replay_repairs_single_store_branch_literal() {
    let mut arena = TermArena::new();
    let a = arena.array_var("a", 4, 8).unwrap();
    let b = arena.array_var("b", 4, 8).unwrap();
    let i = arena.bv_var("i", 4).unwrap();
    let v = arena.bv_var("v", 8).unwrap();
    let p = arena.bool_var("p").unwrap();
    let stored = arena.store(a, i, v).unwrap();
    let b_eq_store = arena.eq(b, stored).unwrap();
    let branch_assertion = arena.or(b_eq_store, p).unwrap();

    let mut candidate = Assignment::new();
    for (symbol, name, sort) in arena.symbols() {
        match name {
            "i" => candidate.set(symbol, Value::Bv { width: 4, value: 0 }),
            "v" => candidate.set(symbol, Value::Bv { width: 8, value: 7 }),
            "p" => candidate.set(symbol, Value::Bool(false)),
            _ if sort == Sort::BitVec(4) => {
                candidate.set(symbol, Value::Bv { width: 4, value: 0 });
            }
            _ if sort == Sort::BitVec(8) => {
                candidate.set(symbol, Value::Bv { width: 8, value: 0 });
            }
            _ => {}
        }
    }

    let originals = [branch_assertion];
    let mut projected = complete_assignment(&arena, &candidate);
    let failure = first_projected_replay_failure(
        &arena,
        &originals,
        &projected,
        ProjectionRepairStats::default(),
    )
    .unwrap()
    .expect("expected the store branch to fail before targeted repair");
    assert_eq!(failure.conjunct_term, branch_assertion);

    let stats = repair_projected_replay_failure(&arena, &originals, &mut projected, &failure)
        .unwrap()
        .expect("expected targeted branch repair to change the projection");
    assert_eq!(stats.branch_symbol_changes, 1);
    assert!(
        first_projected_replay_failure(
            &arena,
            &originals,
            &projected,
            ProjectionRepairStats::default(),
        )
        .unwrap()
        .is_none()
    );
}

#[test]
fn lazy_ext_targeted_replay_repairs_direct_select_equality() {
    let mut arena = TermArena::new();
    let a = arena.array_var("a", 4, 8).unwrap();
    let i = arena.bv_var("i", 4).unwrap();
    let y = arena.bv_var("y", 8).unwrap();
    let read = arena.select(a, i).unwrap();
    let y_eq_read = arena.eq(y, read).unwrap();

    let TermNode::Symbol(y_symbol) = arena.node(y) else {
        panic!("y should be a symbol");
    };

    let mut candidate = Assignment::new();
    for (symbol, name, sort) in arena.symbols() {
        match name {
            "i" => candidate.set(symbol, Value::Bv { width: 4, value: 1 }),
            "y" => candidate.set(symbol, Value::Bv { width: 8, value: 7 }),
            _ if sort == Sort::BitVec(4) => {
                candidate.set(symbol, Value::Bv { width: 4, value: 0 });
            }
            _ if sort == Sort::BitVec(8) => {
                candidate.set(symbol, Value::Bv { width: 8, value: 0 });
            }
            _ => {}
        }
    }

    let originals = [y_eq_read];
    let mut projected = complete_assignment(&arena, &candidate);
    let failure = first_projected_replay_failure(
        &arena,
        &originals,
        &projected,
        ProjectionRepairStats::default(),
    )
    .unwrap()
    .expect("expected the direct select equality to fail before repair");

    let stats = repair_projected_replay_failure(&arena, &originals, &mut projected, &failure)
        .unwrap()
        .expect("expected targeted select repair to change the projection");
    assert_eq!(stats.array_changes, 1);
    assert_eq!(
        projected.get(*y_symbol),
        Some(Value::Bv { width: 8, value: 7 })
    );
    assert!(
        first_projected_replay_failure(
            &arena,
            &originals,
            &projected,
            ProjectionRepairStats::default(),
        )
        .unwrap()
        .is_none()
    );
}

#[test]
fn lazy_ext_targeted_replay_repairs_select_through_store_chain() {
    let mut arena = TermArena::new();
    let a = arena.array_var("a", 4, 8).unwrap();
    let b = arena.array_var("b", 4, 8).unwrap();
    let i = arena.bv_var("i", 4).unwrap();
    let j = arena.bv_var("j", 4).unwrap();
    let v = arena.bv_var("v", 8).unwrap();
    let y = arena.bv_var("y", 8).unwrap();
    let p = arena.bool_var("p").unwrap();
    let stored = arena.store(a, j, v).unwrap();
    let b_eq_store = arena.eq(b, stored).unwrap();
    let branch_assertion = arena.or(b_eq_store, p).unwrap();
    let read_b_i = arena.select(b, i).unwrap();
    let y_eq_read = arena.eq(y, read_b_i).unwrap();

    let TermNode::Symbol(a_symbol) = arena.node(a) else {
        panic!("a should be a symbol");
    };
    let TermNode::Symbol(b_symbol) = arena.node(b) else {
        panic!("b should be a symbol");
    };

    let mut candidate = Assignment::new();
    for (symbol, name, sort) in arena.symbols() {
        match name {
            "i" => candidate.set(symbol, Value::Bv { width: 4, value: 1 }),
            "j" => candidate.set(symbol, Value::Bv { width: 4, value: 2 }),
            "v" => candidate.set(symbol, Value::Bv { width: 8, value: 9 }),
            "y" => candidate.set(symbol, Value::Bv { width: 8, value: 7 }),
            "p" => candidate.set(symbol, Value::Bool(false)),
            _ if sort == Sort::BitVec(4) => {
                candidate.set(symbol, Value::Bv { width: 4, value: 0 });
            }
            _ if sort == Sort::BitVec(8) => {
                candidate.set(symbol, Value::Bv { width: 8, value: 0 });
            }
            _ => {}
        }
    }

    let originals = [y_eq_read, branch_assertion];
    let mut projected = complete_assignment(&arena, &candidate);
    let base_value = default_value_for_symbol(&arena, *a_symbol).unwrap();
    let initially_stored = store_value(
        &base_value,
        Value::Bv { width: 4, value: 2 },
        Value::Bv { width: 8, value: 9 },
    )
    .unwrap();
    projected.set(*b_symbol, initially_stored);
    assert_eq!(
        eval(&arena, branch_assertion, &projected).unwrap(),
        Value::Bool(true),
        "the store-definition branch should start true"
    );

    let failure = first_projected_replay_failure(
        &arena,
        &originals,
        &projected,
        ProjectionRepairStats::default(),
    )
    .unwrap()
    .expect("expected the inherited direct select equality to fail before repair");
    assert_eq!(failure.conjunct_term, y_eq_read);

    let stats = repair_projected_replay_failure(&arena, &originals, &mut projected, &failure)
        .unwrap()
        .expect("expected targeted store-chain select repair to change the projection");
    assert_eq!(stats.array_changes, 1);
    assert_eq!(stats.branch_symbol_changes, 1);

    let repaired_a = projected.get(*a_symbol).expect("repaired base array");
    assert_eq!(
        select_value(&repaired_a, &Value::Bv { width: 4, value: 1 }).unwrap(),
        Value::Bv { width: 8, value: 7 }
    );
    assert_eq!(
        first_projected_replay_failure(
            &arena,
            &originals,
            &projected,
            ProjectionRepairStats::default(),
        )
        .unwrap(),
        None
    );
    for &original in &originals {
        assert_eq!(
            eval(&arena, original, &projected).unwrap(),
            Value::Bool(true)
        );
    }
}

#[test]
#[allow(clippy::too_many_lines)]
fn lazy_ext_branch_equality_repairs_target_through_store_definition() {
    let mut arena = TermArena::new();
    let base = arena.array_var("base", 4, 8).unwrap();
    let a = arena.array_var("a", 4, 8).unwrap();
    let b = arena.array_var("b", 4, 8).unwrap();
    let i = arena.bv_var("i", 4).unwrap();
    let j = arena.bv_var("j", 4).unwrap();
    let v = arena.bv_var("v", 8).unwrap();
    let y = arena.bv_var("y", 8).unwrap();
    let p = arena.bool_var("p").unwrap();
    let q = arena.bool_var("q").unwrap();
    let seven = arena.bv_const(8, 7).unwrap();
    let stored = arena.store(base, j, v).unwrap();
    let a_eq_store = arena.eq(a, stored).unwrap();
    let lower_branch = arena.or(a_eq_store, p).unwrap();
    let b_eq_a = arena.eq(b, a).unwrap();
    let equality_branch = arena.or(b_eq_a, q).unwrap();
    let read_b_i = arena.select(b, i).unwrap();
    let y_eq_read = arena.eq(y, read_b_i).unwrap();
    let y_eq_seven = arena.eq(y, seven).unwrap();

    let TermNode::Symbol(base_symbol) = arena.node(base) else {
        panic!("base should be a symbol");
    };
    let TermNode::Symbol(a_symbol) = arena.node(a) else {
        panic!("a should be a symbol");
    };
    let TermNode::Symbol(b_symbol) = arena.node(b) else {
        panic!("b should be a symbol");
    };

    let mut candidate = Assignment::new();
    for (symbol, name, sort) in arena.symbols() {
        match name {
            "i" => candidate.set(symbol, Value::Bv { width: 4, value: 1 }),
            "j" => candidate.set(symbol, Value::Bv { width: 4, value: 2 }),
            "v" => candidate.set(symbol, Value::Bv { width: 8, value: 9 }),
            "y" => candidate.set(symbol, Value::Bv { width: 8, value: 7 }),
            "p" | "q" => candidate.set(symbol, Value::Bool(false)),
            _ if sort == Sort::BitVec(4) => {
                candidate.set(symbol, Value::Bv { width: 4, value: 0 });
            }
            _ if sort == Sort::BitVec(8) => {
                candidate.set(symbol, Value::Bv { width: 8, value: 0 });
            }
            _ => {}
        }
    }

    let mut projected = complete_assignment(&arena, &candidate);
    let base_value = default_value_for_symbol(&arena, *base_symbol).unwrap();
    let a_initial = store_value(
        &base_value,
        Value::Bv { width: 4, value: 2 },
        Value::Bv { width: 8, value: 9 },
    )
    .unwrap();
    let b_desired = store_value(
        &a_initial,
        Value::Bv { width: 4, value: 1 },
        Value::Bv { width: 8, value: 7 },
    )
    .unwrap();
    projected.set(*a_symbol, a_initial);
    projected.set(*b_symbol, b_desired);
    assert_eq!(
        eval(&arena, lower_branch, &projected).unwrap(),
        Value::Bool(true),
        "the selected store definition should start true"
    );
    assert_eq!(
        eval(&arena, equality_branch, &projected).unwrap(),
        Value::Bool(false),
        "the branch equality should be the only initial failure"
    );

    let originals = [equality_branch, lower_branch, y_eq_read, y_eq_seven];
    let failure = first_projected_replay_failure(
        &arena,
        &originals,
        &projected,
        ProjectionRepairStats::default(),
    )
    .unwrap()
    .expect("expected the branch equality to fail before repair");
    assert_eq!(failure.conjunct_term, equality_branch);

    let stats = repair_projected_replay_failure(&arena, &originals, &mut projected, &failure)
        .unwrap()
        .expect("expected branch equality repair through the store definition");
    assert!(stats.changes() > 0);

    let repaired_base = projected.get(*base_symbol).expect("repaired base array");
    assert_eq!(
        select_value(&repaired_base, &Value::Bv { width: 4, value: 1 }).unwrap(),
        Value::Bv { width: 8, value: 7 }
    );
    assert!(
        first_projected_replay_failure(
            &arena,
            &originals,
            &projected,
            ProjectionRepairStats::default(),
        )
        .unwrap()
        .is_none()
    );
    for &original in &originals {
        assert_eq!(
            eval(&arena, original, &projected).unwrap(),
            Value::Bool(true)
        );
    }
}

#[test]
fn lazy_ext_targeted_replay_can_choose_non_best_repairable_branch() {
    let mut arena = TermArena::new();
    let q = arena.bool_var("q").unwrap();
    let x = arena.int_var("x").unwrap();
    let y = arena.int_var("y").unwrap();
    let one = arena.int_const(1);
    let two = arena.int_const(2);
    let x_eq_one = arena.eq(x, one).unwrap();
    let y_eq_two = arena.eq(y, two).unwrap();
    let repairable_branch = arena.and(x_eq_one, y_eq_two).unwrap();
    let branch_assertion = arena.or(q, repairable_branch).unwrap();

    let TermNode::Symbol(q_symbol) = arena.node(q) else {
        panic!("q should be a symbol");
    };
    let TermNode::Symbol(x_symbol) = arena.node(x) else {
        panic!("x should be a symbol");
    };
    let TermNode::Symbol(y_symbol) = arena.node(y) else {
        panic!("y should be a symbol");
    };

    let mut candidate = Assignment::new();
    candidate.set(*q_symbol, Value::Bool(false));
    candidate.set(*x_symbol, Value::Int(0));
    candidate.set(*y_symbol, Value::Int(0));

    let originals = [branch_assertion];
    let projected = complete_assignment(&arena, &candidate);
    let failure = first_projected_replay_failure(
        &arena,
        &originals,
        &projected,
        ProjectionRepairStats::default(),
    )
    .unwrap()
    .expect("expected the branch disjunction to fail before targeted repair");
    let or_failure = failure
        .failed_or
        .as_ref()
        .expect("expected branch failure details");
    assert_eq!(or_failure.best_branch_ordinal, 0);
    assert_eq!(or_failure.best_branch_term, q);
    assert_eq!(or_failure.best_branch_false_literals, 1);

    let ctx = RowCtx::default();
    let ExtReplay::Sat(model) =
        project_replay_ext_candidate(&arena, &ctx, &originals, &candidate).unwrap()
    else {
        panic!("expected targeted replay to choose the repairable non-best branch");
    };
    let assignment = model.to_assignment();
    assert_eq!(assignment.get(*q_symbol), Some(Value::Bool(false)));
    assert_eq!(assignment.get(*x_symbol), Some(Value::Int(1)));
    assert_eq!(assignment.get(*y_symbol), Some(Value::Int(2)));
    assert_eq!(
        eval(&arena, branch_assertion, &assignment).unwrap(),
        Value::Bool(true)
    );
}

#[test]
fn lazy_ext_targeted_replay_repairs_order_guarded_branch_choice() {
    let mut arena = TermArena::new();
    let q = arena.bool_var("q").unwrap();
    let x = arena.int_var("x").unwrap();
    let y = arena.int_var("y").unwrap();
    let z = arena.int_var("z").unwrap();
    let x_le_y = arena.int_le(x, y).unwrap();
    let x_gt_y = arena.not(x_le_y).unwrap();
    let z_eq_x = arena.eq(z, x).unwrap();
    let guarded_branch = arena.and(x_gt_y, z_eq_x).unwrap();
    let branch_assertion = arena.or(q, guarded_branch).unwrap();

    let TermNode::Symbol(q_symbol) = arena.node(q) else {
        panic!("q should be a symbol");
    };
    let TermNode::Symbol(x_symbol) = arena.node(x) else {
        panic!("x should be a symbol");
    };
    let TermNode::Symbol(y_symbol) = arena.node(y) else {
        panic!("y should be a symbol");
    };
    let TermNode::Symbol(z_symbol) = arena.node(z) else {
        panic!("z should be a symbol");
    };

    let mut candidate = Assignment::new();
    candidate.set(*q_symbol, Value::Bool(false));
    candidate.set(*x_symbol, Value::Int(0));
    candidate.set(*y_symbol, Value::Int(0));
    candidate.set(*z_symbol, Value::Int(2));

    let originals = [branch_assertion];
    let projected = complete_assignment(&arena, &candidate);
    let failure = first_projected_replay_failure(
        &arena,
        &originals,
        &projected,
        ProjectionRepairStats::default(),
    )
    .unwrap()
    .expect("expected the branch disjunction to fail before targeted repair");
    let or_failure = failure
        .failed_or
        .as_ref()
        .expect("expected branch failure details");
    assert_eq!(or_failure.best_branch_ordinal, 0);
    assert_eq!(or_failure.best_branch_false_literals, 1);

    let ctx = RowCtx::default();
    let ExtReplay::Sat(model) =
        project_replay_ext_candidate(&arena, &ctx, &originals, &candidate).unwrap()
    else {
        panic!("expected targeted replay to repair the order-guarded branch");
    };
    let assignment = model.to_assignment();
    assert_eq!(assignment.get(*q_symbol), Some(Value::Bool(false)));
    let Some(Value::Int(x_value)) = assignment.get(*x_symbol) else {
        panic!("x should have an integer value");
    };
    let Some(Value::Int(y_value)) = assignment.get(*y_symbol) else {
        panic!("y should have an integer value");
    };
    assert!(x_value > y_value);
    assert_eq!(assignment.get(*z_symbol), Some(Value::Int(x_value)));
    assert_eq!(
        eval(&arena, branch_assertion, &assignment).unwrap(),
        Value::Bool(true)
    );
}

#[test]
fn lazy_ext_projection_repairs_supported_branch_array_equality() {
    let mut arena = TermArena::new();
    let a = arena.array_var("a", 4, 8).unwrap();
    let b = arena.array_var("b", 4, 8).unwrap();
    let j = arena.bv_var("j", 4).unwrap();
    let y = arena.bv_var("y", 8).unwrap();
    let z = arena.bv_var("z", 8).unwrap();
    let p = arena.bool_var("p").unwrap();
    let a_eq_b = arena.eq(a, b).unwrap();
    let branch_assertion = arena.or(a_eq_b, p).unwrap();
    let read_a_j = arena.select(a, j).unwrap();
    let y_eq_a_read = arena.eq(y, read_a_j).unwrap();
    let read_b_j = arena.select(b, j).unwrap();
    let z_eq_b_read = arena.eq(z, read_b_j).unwrap();

    let TermNode::Symbol(a_symbol) = arena.node(a) else {
        panic!("a should be a symbol");
    };
    let TermNode::Symbol(y_symbol) = arena.node(y) else {
        panic!("y should be a symbol");
    };
    let TermNode::Symbol(z_symbol) = arena.node(z) else {
        panic!("z should be a symbol");
    };

    let mut ctx = RowCtx::default();
    ctx.sites.push(RowSite {
        fresh: *y_symbol,
        index: j,
        kind: RowKind::Var { array: *a_symbol },
    });

    let mut candidate = Assignment::new();
    for (symbol, name, sort) in arena.symbols() {
        match name {
            "j" => candidate.set(symbol, Value::Bv { width: 4, value: 1 }),
            "y" => candidate.set(symbol, Value::Bv { width: 8, value: 9 }),
            "z" => candidate.set(symbol, Value::Bv { width: 8, value: 0 }),
            "p" => candidate.set(symbol, Value::Bool(false)),
            _ if sort == Sort::BitVec(4) => {
                candidate.set(symbol, Value::Bv { width: 4, value: 0 });
            }
            _ if sort == Sort::BitVec(8) => {
                candidate.set(symbol, Value::Bv { width: 8, value: 0 });
            }
            _ => {}
        }
    }

    let originals = [branch_assertion, y_eq_a_read, z_eq_b_read];
    let ExtReplay::Sat(model) =
        project_replay_ext_candidate(&arena, &ctx, &originals, &candidate).unwrap()
    else {
        panic!("expected branch array-equality repair to replay");
    };
    let assignment = model.to_assignment();
    assert_eq!(
        assignment.get(*z_symbol),
        Some(Value::Bv { width: 8, value: 9 })
    );
    for &original in &originals {
        assert_eq!(
            eval(&arena, original, &assignment).unwrap(),
            Value::Bool(true)
        );
    }
}

#[test]
#[allow(clippy::too_many_lines)]
fn lazy_ext_projection_repairs_selected_array_equality_component() {
    let mut arena = TermArena::new();
    let a = arena.array_var("a", 4, 8).unwrap();
    let b = arena.array_var("b", 4, 8).unwrap();
    let c = arena.array_var("c", 4, 8).unwrap();
    let i = arena.bv_var("i", 4).unwrap();
    let k0 = arena.bv_var("k0", 4).unwrap();
    let k2 = arena.bv_var("k2", 4).unwrap();
    let y = arena.bv_var("y", 8).unwrap();
    let p = arena.bool_var("p").unwrap();
    let q = arena.bool_var("q").unwrap();
    let two = arena.bv_const(8, 2).unwrap();
    let c_eq_b = arena.eq(c, b).unwrap();
    let b_eq_a = arena.eq(b, a).unwrap();
    let c_branch = arena.or(c_eq_b, p).unwrap();
    let b_branch = arena.or(b_eq_a, q).unwrap();
    let read_b_i = arena.select(b, i).unwrap();
    let y_eq_read_b = arena.eq(y, read_b_i).unwrap();
    let y_eq_two = arena.eq(y, two).unwrap();

    let a_symbol = match arena.node(a) {
        TermNode::Symbol(symbol) => *symbol,
        _ => panic!("a should be a symbol"),
    };
    let b_symbol = match arena.node(b) {
        TermNode::Symbol(symbol) => *symbol,
        _ => panic!("b should be a symbol"),
    };
    let c_symbol = match arena.node(c) {
        TermNode::Symbol(symbol) => *symbol,
        _ => panic!("c should be a symbol"),
    };
    let y_symbol = match arena.node(y) {
        TermNode::Symbol(symbol) => *symbol,
        _ => panic!("y should be a symbol"),
    };

    let mut ctx = RowCtx::default();
    let c_at_k0 = ctx.fresh_symbol(&mut arena, Sort::BitVec(8)).unwrap();
    let c_at_k2 = ctx.fresh_symbol(&mut arena, Sort::BitVec(8)).unwrap();
    ctx.sites.push(RowSite {
        fresh: y_symbol,
        index: i,
        kind: RowKind::Var { array: b_symbol },
    });
    ctx.sites.push(RowSite {
        fresh: c_at_k0,
        index: k0,
        kind: RowKind::Var { array: c_symbol },
    });
    ctx.sites.push(RowSite {
        fresh: c_at_k2,
        index: k2,
        kind: RowKind::Var { array: c_symbol },
    });

    let mut candidate = Assignment::new();
    for (symbol, name, sort) in arena.symbols() {
        match name {
            "i" => candidate.set(symbol, Value::Bv { width: 4, value: 1 }),
            "k0" => candidate.set(symbol, Value::Bv { width: 4, value: 0 }),
            "k2" => candidate.set(symbol, Value::Bv { width: 4, value: 2 }),
            "y" => candidate.set(symbol, Value::Bv { width: 8, value: 2 }),
            "p" | "q" => candidate.set(symbol, Value::Bool(false)),
            _ if symbol == c_at_k0 || symbol == c_at_k2 => {
                candidate.set(symbol, Value::Bv { width: 8, value: 3 });
            }
            _ if sort == Sort::BitVec(4) => {
                candidate.set(symbol, Value::Bv { width: 4, value: 0 });
            }
            _ if sort == Sort::BitVec(8) => {
                candidate.set(symbol, Value::Bv { width: 8, value: 0 });
            }
            _ => {}
        }
    }

    let arrays =
        collect_base_array_entries(&arena, &ctx, &candidate, "test projection").unwrap();
    let mut projected = complete_assignment(&arena, &candidate);
    for (&array, entries) in &arrays {
        projected.set(
            array,
            array_value_from_entries(&arena, array, entries).unwrap(),
        );
    }

    let originals = [c_branch, b_branch, y_eq_read_b, y_eq_two];
    let failure = first_projected_replay_failure(
        &arena,
        &originals,
        &projected,
        ProjectionRepairStats::default(),
    )
    .unwrap()
    .expect("expected the component carry branch to fail before repair");
    assert_eq!(failure.conjunct_term, c_branch);
    let stats = repair_projected_replay_failure(&arena, &originals, &mut projected, &failure)
        .unwrap()
        .expect("expected component array-equality repair to change the projection");
    assert!(stats.branch_symbol_changes >= 2);
    assert!(
        first_projected_replay_failure(
            &arena,
            &originals,
            &projected,
            ProjectionRepairStats::default(),
        )
        .unwrap()
        .is_none()
    );

    let a_value = projected.get(a_symbol).expect("a value");
    let b_value = projected.get(b_symbol).expect("b value");
    let c_value = projected.get(c_symbol).expect("c value");
    assert_eq!(a_value, b_value);
    assert_eq!(b_value, c_value);
    assert_eq!(
        projected.get(y_symbol),
        Some(Value::Bv { width: 8, value: 2 })
    );
    for &original in &originals {
        assert_eq!(
            eval(&arena, original, &projected).unwrap(),
            Value::Bool(true)
        );
    }
}

#[test]
fn lazy_ext_projection_repairs_multi_literal_branch_schedule() {
    let mut arena = TermArena::new();
    let a = arena.array_var("a", 4, 8).unwrap();
    let b = arena.array_var("b", 4, 8).unwrap();
    let i = arena.bv_var("i", 4).unwrap();
    let j = arena.bv_var("j", 4).unwrap();
    let v = arena.bv_var("v", 8).unwrap();
    let y = arena.bv_var("y", 8).unwrap();
    let z = arena.bv_var("z", 8).unwrap();
    let q = arena.bool_var("q").unwrap();
    let r = arena.bool_var("r").unwrap();
    let s = arena.bool_var("s").unwrap();

    let i_eq_j = arena.eq(i, j).unwrap();
    let stored = arena.store(a, i, v).unwrap();
    let b_eq_store = arena.eq(b, stored).unwrap();
    let wanted_branch = arena.and(i_eq_j, b_eq_store).unwrap();
    let r_and_s = arena.and(r, s).unwrap();
    let noisy_alt = arena.and(q, r_and_s).expect("alternate branch");
    let branch_assertion = arena.or(wanted_branch, noisy_alt).unwrap();
    let read_a_j = arena.select(a, j).unwrap();
    let y_eq_a_read = arena.eq(y, read_a_j).unwrap();
    let read_b_j = arena.select(b, j).unwrap();
    let z_eq_b_read = arena.eq(z, read_b_j).unwrap();

    let TermNode::Symbol(a_symbol) = arena.node(a) else {
        panic!("a should be a symbol");
    };
    let TermNode::Symbol(y_symbol) = arena.node(y) else {
        panic!("y should be a symbol");
    };
    let TermNode::Symbol(z_symbol) = arena.node(z) else {
        panic!("z should be a symbol");
    };

    let mut ctx = RowCtx::default();
    ctx.sites.push(RowSite {
        fresh: *y_symbol,
        index: j,
        kind: RowKind::Var { array: *a_symbol },
    });

    let mut candidate = Assignment::new();
    for (symbol, name, sort) in arena.symbols() {
        match name {
            "i" => candidate.set(symbol, Value::Bv { width: 4, value: 0 }),
            "j" => candidate.set(symbol, Value::Bv { width: 4, value: 1 }),
            "v" => candidate.set(symbol, Value::Bv { width: 8, value: 9 }),
            "y" => candidate.set(symbol, Value::Bv { width: 8, value: 5 }),
            "z" => candidate.set(symbol, Value::Bv { width: 8, value: 0 }),
            "q" | "r" | "s" => candidate.set(symbol, Value::Bool(false)),
            _ if sort == Sort::BitVec(4) => {
                candidate.set(symbol, Value::Bv { width: 4, value: 0 });
            }
            _ if sort == Sort::BitVec(8) => {
                candidate.set(symbol, Value::Bv { width: 8, value: 0 });
            }
            _ => {}
        }
    }

    let originals = [branch_assertion, y_eq_a_read, z_eq_b_read];
    let ExtReplay::Sat(model) =
        project_replay_ext_candidate(&arena, &ctx, &originals, &candidate).unwrap()
    else {
        panic!("expected multi-literal branch repair to replay");
    };
    let assignment = model.to_assignment();
    assert_eq!(
        assignment.get(*z_symbol),
        Some(Value::Bv { width: 8, value: 9 })
    );
    for &original in &originals {
        assert_eq!(
            eval(&arena, original, &assignment).unwrap(),
            Value::Bool(true)
        );
    }
}

#[test]
fn lazy_ext_projection_repairs_scalar_equality_by_replay_improvement() {
    let mut arena = TermArena::new();
    let x = arena.int_var("x").unwrap();
    let y = arena.int_var("y").unwrap();
    let one = arena.int_const(1);
    let y_eq_x = arena.eq(y, x).unwrap();
    let y_eq_one = arena.eq(y, one).unwrap();

    let TermNode::Symbol(x_symbol) = arena.node(x) else {
        panic!("x should be a symbol");
    };
    let TermNode::Symbol(y_symbol) = arena.node(y) else {
        panic!("y should be a symbol");
    };

    let mut candidate = Assignment::new();
    candidate.set(*x_symbol, Value::Int(0));
    candidate.set(*y_symbol, Value::Int(1));

    let ctx = RowCtx::default();
    let originals = [y_eq_x, y_eq_one];
    let ExtReplay::Sat(model) =
        project_replay_ext_candidate(&arena, &ctx, &originals, &candidate).unwrap()
    else {
        panic!("expected scalar equality repair to replay");
    };
    let assignment = model.to_assignment();
    assert_eq!(assignment.get(*x_symbol), Some(Value::Int(1)));
    assert_eq!(assignment.get(*y_symbol), Some(Value::Int(1)));
    for &original in &originals {
        assert_eq!(
            eval(&arena, original, &assignment).unwrap(),
            Value::Bool(true)
        );
    }
}

#[test]
fn lazy_ext_projection_propagates_select_supported_scalar_equalities() {
    let mut arena = TermArena::new();
    let a = arena.array_var("a", 4, 8).unwrap();
    let i = arena.bv_var("i", 4).unwrap();
    let y = arena.bv_var("y", 8).unwrap();
    let x = arena.bv_var("x", 8).unwrap();
    let z = arena.bv_var("z", 8).unwrap();
    let seven = arena.bv_const(8, 7).unwrap();
    let read = arena.select(a, i).unwrap();
    let y_eq_read = arena.eq(y, read).unwrap();
    let y_eq_seven = arena.eq(y, seven).unwrap();
    let x_eq_y = arena.eq(x, y).unwrap();
    let x_eq_z = arena.eq(x, z).unwrap();
    let z_eq_y = arena.eq(z, y).unwrap();

    let TermNode::Symbol(array) = arena.node(a) else {
        panic!("array should be a symbol");
    };
    let TermNode::Symbol(y_symbol) = arena.node(y) else {
        panic!("y should be a symbol");
    };
    let TermNode::Symbol(x_symbol) = arena.node(x) else {
        panic!("x should be a symbol");
    };
    let TermNode::Symbol(z_symbol) = arena.node(z) else {
        panic!("z should be a symbol");
    };

    let mut ctx = RowCtx::default();
    ctx.sites.push(RowSite {
        fresh: *y_symbol,
        index: i,
        kind: RowKind::Var { array: *array },
    });

    let mut candidate = Assignment::new();
    for (symbol, name, sort) in arena.symbols() {
        match name {
            "i" => candidate.set(symbol, Value::Bv { width: 4, value: 0 }),
            "y" => candidate.set(symbol, Value::Bv { width: 8, value: 7 }),
            "x" | "z" => candidate.set(symbol, Value::Bv { width: 8, value: 0 }),
            _ if sort == Sort::BitVec(4) => {
                candidate.set(symbol, Value::Bv { width: 4, value: 0 });
            }
            _ if sort == Sort::BitVec(8) => {
                candidate.set(symbol, Value::Bv { width: 8, value: 0 });
            }
            _ => {}
        }
    }

    let originals = [y_eq_read, y_eq_seven, x_eq_y, x_eq_z, z_eq_y];
    let ExtReplay::Sat(model) =
        project_replay_ext_candidate(&arena, &ctx, &originals, &candidate).unwrap()
    else {
        panic!("expected select-supported scalar propagation to replay");
    };
    let assignment = model.to_assignment();
    assert_eq!(
        assignment.get(*x_symbol),
        Some(Value::Bv { width: 8, value: 7 })
    );
    assert_eq!(
        assignment.get(*z_symbol),
        Some(Value::Bv { width: 8, value: 7 })
    );
    for &original in &originals {
        assert_eq!(
            eval(&arena, original, &assignment).unwrap(),
            Value::Bool(true)
        );
    }
}

#[test]
fn lazy_ext_projection_prefers_asserted_select_equalities() {
    // Timeout salvage must not let auxiliary extensionality reads overwrite
    // an original select equality in the projected array model. The final
    // full replay remains the soundness gate; this only chooses the candidate
    // array entry that the original formula explicitly demands.
    let mut arena = TermArena::new();
    let a = arena.array_var("a", 4, 8).unwrap();
    let i = arena.bv_var("i", 4).unwrap();
    let j = arena.bv_var("j", 4).unwrap();
    let x = arena.bv_var("x", 8).unwrap();
    let y = arena.bv_var("y", 8).unwrap();
    let read = arena.select(a, i).unwrap();
    let other_read = arena.select(a, j).unwrap();
    let x_read = arena.eq(x, read).unwrap();
    let y_read = arena.eq(y, other_read).unwrap();
    let i_eq_j = arena.eq(i, j).unwrap();

    let TermNode::Symbol(array) = arena.node(a) else {
        panic!("array variable should be a symbol");
    };
    let array = *array;

    let mut ctx = RowCtx::default();
    let demanded = ctx.fresh_symbol(&mut arena, Sort::BitVec(8)).unwrap();
    let same_index = ctx.fresh_symbol(&mut arena, Sort::BitVec(8)).unwrap();
    let auxiliary = ctx.fresh_symbol(&mut arena, Sort::BitVec(8)).unwrap();
    ctx.sites.push(RowSite {
        fresh: demanded,
        index: i,
        kind: RowKind::Var { array },
    });
    ctx.sites.push(RowSite {
        fresh: same_index,
        index: j,
        kind: RowKind::Var { array },
    });
    ctx.sites.push(RowSite {
        fresh: auxiliary,
        index: i,
        kind: RowKind::Var { array },
    });

    let mut candidate = Assignment::new();
    for (symbol, name, sort) in arena.symbols() {
        if name == "i" || name == "j" {
            candidate.set(symbol, Value::Bv { width: 4, value: 0 });
        } else if name == "x" {
            candidate.set(symbol, Value::Bv { width: 8, value: 7 });
        } else if name == "y" {
            candidate.set(symbol, Value::Bv { width: 8, value: 3 });
        } else if symbol == demanded {
            candidate.set(symbol, Value::Bv { width: 8, value: 7 });
        } else if symbol == same_index {
            candidate.set(symbol, Value::Bv { width: 8, value: 3 });
        } else if symbol == auxiliary {
            candidate.set(symbol, Value::Bv { width: 8, value: 0 });
        } else if sort == Sort::BitVec(4) {
            candidate.set(symbol, Value::Bv { width: 4, value: 0 });
        } else if sort == Sort::BitVec(8) {
            candidate.set(symbol, Value::Bv { width: 8, value: 0 });
        }
    }

    let originals = [x_read, y_read, i_eq_j];
    let ExtReplay::Sat(model) =
        project_replay_ext_candidate(&arena, &ctx, &originals, &candidate).unwrap()
    else {
        panic!("expected repaired projection to replay");
    };
    let assignment = model.to_assignment();
    for &original in &originals {
        assert_eq!(
            eval(&arena, original, &assignment).unwrap(),
            Value::Bool(true)
        );
    }
}

#[test]
fn lazy_abv_matches_eager_differential() {
    // ~200 deterministic-random small QF_ABV formulas; the lazy verdict must
    // agree with the eager array-elimination verdict whenever both decide.
    let config = SolverConfig::default();
    let mut jointly_decided = 0usize;
    let mut unsat_count = 0usize;

    // Simple LCG (no `rand` crate); seeded by a constant, varied per case.
    let mut state: u64 = 0x9e37_79b9_7f4a_7c15;

    for _case in 0..200usize {
        let mut arena = TermArena::new();
        let assertions = [build_case(&mut arena, &mut state)];

        let mut lazy_backend = SatBvBackend::new();
        let mut eager_backend = SatBvBackend::new();
        let lazy = check_qf_abv_lazy(&mut lazy_backend, &mut arena, &assertions, &config)
            .expect("lazy check");
        let eager =
            check_with_array_elimination(&mut eager_backend, &mut arena, &assertions, &config)
                .expect("eager check");

        if let (Some(l), Some(e)) = (verdict(&lazy), verdict(&eager)) {
            assert_eq!(
                l, e,
                "lazy/eager disagree on a jointly-decided case (lazy={lazy:?}, eager={eager:?})"
            );
            jointly_decided += 1;
            if !l {
                unsat_count += 1;
            }
        }
    }

    assert!(
        jointly_decided > 0,
        "expected some jointly-decided cases, got none"
    );
    assert!(
        unsat_count > 0,
        "expected at least one UNSAT case, got none"
    );
}

#[test]
fn symmetric_swap_chain_refuter_closes_cvc5_regression() {
    let script = parse_script(include_str!(
        "../../../../corpus/public-curated/non-incremental/QF_AUFLIA/cvc5-regress-clean/cli__regress4__swap_t1_pp_nf_ai_00010_004.cvc.smt2"
    ))
    .unwrap();

    assert!(
        prove_unsat_by_symmetric_swap_chain(&script.arena, &script.assertions),
        "expected the structural swap-chain refuter to close the real cvc5 regression"
    );
}

#[test]
fn cross_store_array_refuter_closes_qf_ax_unsats_only() {
    for (tag, input) in [
        (
            "arrays0",
            include_str!(
                "../../../../corpus/public-curated/non-incremental/QF_AX/cvc5-regress-clean/cli__regress0__arrays__arrays0.smt2"
            ),
        ),
        (
            "arrays4",
            include_str!(
                "../../../../corpus/public-curated/non-incremental/QF_AX/cvc5-regress-clean/cli__regress0__arrays__arrays4.smt2"
            ),
        ),
    ] {
        let script = parse_script(input).unwrap_or_else(|error| panic!("{tag}: {error}"));
        let cert = cross_store_array_disequality_refutation(&script.arena, &script.assertions)
            .unwrap_or_else(|| panic!("{tag}: expected cross-store certificate"));
        assert!(
            cert.recheck(&script.arena, &script.assertions),
            "{tag}: cross-store certificate must recheck"
        );
        assert!(
            prove_unsat_by_symmetric_swap_chain(&script.arena, &script.assertions),
            "expected structural cross-store refuter to close {tag}"
        );
    }

    let sat_script = parse_script(include_str!(
        "../../../../corpus/public-curated/non-incremental/QF_AX/cvc5-regress-clean/cli__regress0__arrays__arrays3.smt2"
    ))
    .unwrap();
    assert!(
        cross_store_array_disequality_refutation(&sat_script.arena, &sat_script.assertions)
            .is_none(),
        "arrays3 is SAT and must not produce a cross-store certificate"
    );
    assert!(
        !prove_unsat_by_symmetric_swap_chain(&sat_script.arena, &sat_script.assertions),
        "arrays3 is SAT and must not match the same-index cross-store refuter"
    );
}

#[test]
fn const_array_default_mismatch_certificate_rechecks_constarr3() {
    let script = parse_script(include_str!(
        "../../../../corpus/public-curated/non-incremental/QF_ALIA/cvc5-regress-clean/cli__regress1__constarr3.smt2"
    ))
    .unwrap();

    let cert = const_array_default_mismatch_refutation(&script.arena, &script.assertions)
        .expect("constarr3 has finite writes over different constant defaults");
    assert_eq!(cert.lhs_writes, 1);
    assert_eq!(cert.rhs_writes, 1);
    assert!(
        cert.recheck(&script.arena, &script.assertions),
        "certificate must rederive from the original assertions"
    );
}

#[test]
fn store_chain_readback_certificate_rechecks_ios_np_sf() {
    let script = parse_script(include_str!(
        "../../../../corpus/public-curated/non-incremental/QF_ALIA/cvc5-regress-clean/cli__regress0__proofs__ios_np_sf.smt2"
    ))
    .unwrap();

    let cert = store_chain_readback_refutation(&script.arena, &script.assertions)
        .expect("ios_np_sf has a finite store-chain readback contradiction");
    assert_eq!(cert.write_side, StoreChainSide::Left);
    assert_eq!(cert.lhs_writes, 3);
    assert_eq!(cert.rhs_writes, 3);
    assert!(
        cert.recheck(&script.arena, &script.assertions),
        "certificate must rederive from the original assertions"
    );
}

/// Advances a 64-bit LCG and returns a 32-bit draw (no `rand` crate).
fn next_rand(state: &mut u64) -> u32 {
    *state = state
        .wrapping_mul(6_364_136_223_846_793_005)
        .wrapping_add(1_442_695_040_888_963_407);
    (*state >> 33) as u32
}

/// Builds one deterministic-random small `QF_ABV` formula over `BitVec(3)`
/// indices / `BitVec(4)` elements and 1-2 array variables, returning its
/// single top-level assertion.
fn build_case(arena: &mut TermArena, state: &mut u64) -> axeyum_ir::TermId {
    let iw = 3u32;
    let ew = 4u32;
    let a = arena.array_var("a", iw, ew).unwrap();
    let b = arena.array_var("b", iw, ew).unwrap();
    let arrays = [a, b];

    // Index/element pools (scalars).
    let mut idx_pool: Vec<axeyum_ir::TermId> = vec![
        arena.bv_var("i", iw).unwrap(),
        arena.bv_var("j", iw).unwrap(),
        arena.bv_var("k", iw).unwrap(),
    ];
    idx_pool.push(
        arena
            .bv_const(iw, u128::from(next_rand(state) & 0x7))
            .unwrap(),
    );
    let mut elem_pool: Vec<axeyum_ir::TermId> = vec![
        arena.bv_var("v", ew).unwrap(),
        arena.bv_var("w", ew).unwrap(),
    ];
    elem_pool.push(
        arena
            .bv_const(ew, u128::from(next_rand(state) & 0xf))
            .unwrap(),
    );

    // Array pool: variables plus a few stores.
    let mut arr_pool: Vec<axeyum_ir::TermId> = arrays.to_vec();
    for _ in 0..2 {
        let base = arr_pool[(next_rand(state) as usize) % arr_pool.len()];
        let idx = idx_pool[(next_rand(state) as usize) % idx_pool.len()];
        let elem = elem_pool[(next_rand(state) as usize) % elem_pool.len()];
        let stored = arena.store(base, idx, elem).unwrap();
        arr_pool.push(stored);
    }

    // A few selects feed the element pool.
    for _ in 0..3 {
        let arr = arr_pool[(next_rand(state) as usize) % arr_pool.len()];
        let idx = idx_pool[(next_rand(state) as usize) % idx_pool.len()];
        let read = arena.select(arr, idx).unwrap();
        elem_pool.push(read);
    }

    // eq/diseq atoms over the element pool.
    let atom_count = 2 + (next_rand(state) % 3) as usize;
    let mut atoms: Vec<axeyum_ir::TermId> = Vec::with_capacity(atom_count);
    for _ in 0..atom_count {
        let lhs = elem_pool[(next_rand(state) as usize) % elem_pool.len()];
        let rhs = elem_pool[(next_rand(state) as usize) % elem_pool.len()];
        let eq = arena.eq(lhs, rhs).unwrap();
        let atom = if next_rand(state).is_multiple_of(2) {
            eq
        } else {
            arena.not(eq).unwrap()
        };
        atoms.push(atom);
    }

    // Combine atoms into one formula with and/or, then maybe negate.
    let mut formula = atoms[0];
    for &atom in &atoms[1..] {
        formula = if next_rand(state).is_multiple_of(2) {
            arena.and(formula, atom).unwrap()
        } else {
            arena.or(formula, atom).unwrap()
        };
    }
    if next_rand(state).is_multiple_of(4) {
        formula = arena.not(formula).unwrap();
    }
    formula
}

/// `Some(true)` for SAT, `Some(false)` for UNSAT, `None` for Unknown — the
/// shared verdict for differential comparison.
fn verdict(result: &CheckResult) -> Option<bool> {
    match result {
        CheckResult::Sat(_) => Some(true),
        CheckResult::Unsat => Some(false),
        CheckResult::Unknown(_) => None,
    }
}
