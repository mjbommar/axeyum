//! Outcome separation, artifact determinism, and semantic replay for the
//! reason-preserving directed-fuzz handoff.

use std::cell::Cell;

use axeyum_ir::{Assignment, Sort, TermArena, TermId, Value, eval};
use axeyum_smtlib::parse_script;
use axeyum_solver::{SolverConfig, UnknownKind};
use axeyum_verify::directed_fuzz::{
    DirectedFuzzError, DirectedFuzzPlan, FuzzInput, HybridOutcome, SampleValue,
    check_with_directed_fuzz,
};

struct GuardedSum {
    arena: TermArena,
    x: axeyum_ir::SymbolId,
    y: axeyum_ir::SymbolId,
    hypothesis_x: TermId,
    hypothesis_y: TermId,
    true_goal: TermId,
    false_goal: TermId,
}

fn guarded_sum() -> GuardedSum {
    let mut arena = TermArena::new();
    let x = arena.declare("x", Sort::BitVec(8)).unwrap();
    let y = arena.declare("y", Sort::BitVec(8)).unwrap();
    let xt = arena.var(x);
    let yt = arena.var(y);
    let fifteen = arena.bv_const(8, 15).unwrap();
    let hypothesis_x = arena.bv_ule(xt, fifteen).unwrap();
    let hypothesis_y = arena.bv_ule(yt, fifteen).unwrap();
    let sum = arena.bv_add(xt, yt).unwrap();
    let true_goal = arena.bv_uge(sum, xt).unwrap();
    let false_goal = arena.eq(sum, xt).unwrap();
    GuardedSum {
        arena,
        x,
        y,
        hypothesis_x,
        hypothesis_y,
        true_goal,
        false_goal,
    }
}

fn plan(x: axeyum_ir::SymbolId, y: axeyum_ir::SymbolId) -> DirectedFuzzPlan {
    DirectedFuzzPlan::new(
        "guarded_sum_no_wrap",
        vec![
            FuzzInput::bitvec_range(x, 0, 31),
            FuzzInput::bitvec_range(y, 0, 31),
        ],
        32,
    )
    .unwrap()
}

fn sample_u8(sample: &[SampleValue], index: usize) -> u8 {
    let Value::Bv { width: 8, value } = sample[index].value else {
        panic!("expected u8 sample")
    };
    u8::try_from(value).unwrap()
}

#[test]
fn proof_refutation_and_unknown_keep_callbacks_disjoint() {
    let mut query = guarded_sum();
    let hypotheses = [query.hypothesis_x, query.hypothesis_y];
    let fuzz_plan = plan(query.x, query.y);
    let replay_calls = Cell::new(0);
    let oracle_calls = Cell::new(0);
    let outcome = check_with_directed_fuzz(
        &mut query.arena,
        &hypotheses,
        query.true_goal,
        &SolverConfig::default(),
        fuzz_plan,
        |_| {
            replay_calls.set(replay_calls.get() + 1);
            true
        },
        |_| {
            oracle_calls.set(oracle_calls.get() + 1);
            true
        },
    )
    .unwrap();
    assert!(matches!(outcome, HybridOutcome::Proved(_)));
    assert_eq!(replay_calls.get(), 0);
    assert_eq!(oracle_calls.get(), 0);

    let replay_calls = Cell::new(0);
    let oracle_calls = Cell::new(0);
    let x = query.x;
    let y = query.y;
    let fuzz_plan = plan(x, y);
    let outcome = check_with_directed_fuzz(
        &mut query.arena,
        &hypotheses,
        query.false_goal,
        &SolverConfig::default(),
        fuzz_plan,
        |model| {
            replay_calls.set(replay_calls.get() + 1);
            let Some(Value::Bv { value: xv, .. }) = model.get(x) else {
                return false;
            };
            let Some(Value::Bv { value: yv, .. }) = model.get(y) else {
                return false;
            };
            xv <= 15 && yv <= 15 && ((xv + yv) & 0xff) != xv
        },
        |_| {
            oracle_calls.set(oracle_calls.get() + 1);
            true
        },
    )
    .unwrap();
    assert!(matches!(outcome, HybridOutcome::RefutedReplayed(_)));
    assert_eq!(replay_calls.get(), 1);
    assert_eq!(oracle_calls.get(), 0);

    let replay_calls = Cell::new(0);
    let oracle_calls = Cell::new(0);
    let config = SolverConfig {
        node_budget: Some(0),
        ..SolverConfig::default()
    };
    let fuzz_plan = plan(query.x, query.y);
    let outcome = check_with_directed_fuzz(
        &mut query.arena,
        &hypotheses,
        query.true_goal,
        &config,
        fuzz_plan,
        |_| {
            replay_calls.set(replay_calls.get() + 1);
            true
        },
        |sample| {
            oracle_calls.set(oracle_calls.get() + 1);
            let x = sample_u8(sample, 0);
            let y = sample_u8(sample, 1);
            x.wrapping_add(y) >= x
        },
    )
    .unwrap();
    let HybridOutcome::FuzzedOnly {
        reason,
        target,
        report,
    } = outcome
    else {
        panic!("expected sampled-only handoff")
    };
    assert_eq!(reason.kind, UnknownKind::NodeBudget);
    assert_eq!(target.reason, reason);
    assert_eq!(replay_calls.get(), 0);
    assert_eq!(oracle_calls.get(), report.admitted);
    assert!(report.admitted > 0);
    assert!(report.guard_rejected > 0);
    assert_eq!(report.admitted + report.guard_rejected, report.requested);
    assert_eq!(report.violations, 0);
    assert_eq!(report.disagreements, 0);
}

#[test]
fn replay_failure_and_oracle_disagreement_are_explicit() {
    let mut query = guarded_sum();
    let hypotheses = [query.hypothesis_x, query.hypothesis_y];
    let fuzz_plan = plan(query.x, query.y);
    let error = check_with_directed_fuzz(
        &mut query.arena,
        &hypotheses,
        query.false_goal,
        &SolverConfig::default(),
        fuzz_plan,
        |_| false,
        |_| true,
    )
    .unwrap_err();
    assert!(matches!(error, DirectedFuzzError::CountermodelReplayFailed));

    let config = SolverConfig {
        node_budget: Some(0),
        ..SolverConfig::default()
    };
    let fuzz_plan = plan(query.x, query.y);
    let outcome = check_with_directed_fuzz(
        &mut query.arena,
        &hypotheses,
        query.true_goal,
        &config,
        fuzz_plan,
        |_| true,
        |_| false,
    )
    .unwrap();
    let HybridOutcome::FuzzedOnly { report, .. } = outcome else {
        panic!("expected sampled-only handoff")
    };
    assert!(report.disagreements > 0);
    assert!(report.first_disagreement.is_some());
    assert_eq!(report.violations, 0);
}

#[test]
fn artifacts_repeat_and_embedded_query_has_original_violation_semantics() {
    let mut query = guarded_sum();
    let hypotheses = [query.hypothesis_x, query.hypothesis_y];
    let config = SolverConfig {
        node_budget: Some(0),
        ..SolverConfig::default()
    };

    let run = |query: &mut GuardedSum| {
        let fuzz_plan = plan(query.x, query.y);
        check_with_directed_fuzz(
            &mut query.arena,
            &hypotheses,
            query.true_goal,
            &config,
            fuzz_plan,
            |_| true,
            |sample| {
                sample_u8(sample, 0).wrapping_add(sample_u8(sample, 1)) >= sample_u8(sample, 0)
            },
        )
        .unwrap()
    };
    let first = run(&mut query);
    let second = run(&mut query);
    let HybridOutcome::FuzzedOnly { target, report, .. } = first else {
        panic!("expected first handoff")
    };
    let HybridOutcome::FuzzedOnly {
        target: target2,
        report: report2,
        ..
    } = second
    else {
        panic!("expected second handoff")
    };
    assert_eq!(target.to_json(), target2.to_json());
    assert_eq!(report.to_json(), report2.to_json());

    let parsed = parse_script(&target.violation_query_smt2).expect("target query parses");
    assert_eq!(parsed.assertions.len(), 3);
    let px = parsed.arena.find_symbol("x").unwrap();
    let py = parsed.arena.find_symbol("y").unwrap();
    for x in 0_u128..=31 {
        for y in 0_u128..=31 {
            let mut assignment = Assignment::new();
            assignment.set(px, Value::Bv { width: 8, value: x });
            assignment.set(py, Value::Bv { width: 8, value: y });
            let parsed_violation = parsed
                .assertions
                .iter()
                .all(|&term| eval(&parsed.arena, term, &assignment) == Ok(Value::Bool(true)));
            let expected = x <= 15 && y <= 15 && ((x + y) & 0xff) < x;
            assert_eq!(parsed_violation, expected, "x={x}, y={y}");
        }
    }
}
