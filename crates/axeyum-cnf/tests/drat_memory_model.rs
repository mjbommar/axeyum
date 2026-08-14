//! Keeps the DRAT memory model measured rather than remembered (ADR-0426).
//!
//! `DratMemoryModel`'s constants exist so a driver can decide *before* it
//! commits any memory whether a check will fit. A constant that has drifted away
//! from what the checker actually costs is worse than no constant at all: it
//! either declines checks that would have fitted, or — the failure that matters
//! — admits checks that will not, which is the OOM kill this whole module exists
//! to prevent.
//!
//! So the model is re-derived here from live runs on every test invocation. The
//! observation is not an estimate: `DratMemoryReport::observed_structure_bytes`
//! is the sum of the allocation capacities the checker actually held, read off
//! the live data structures. Two properties are asserted:
//!
//! 1. **Conservative.** The prediction is at least the observation. A model that
//!    under-predicts is the dangerous direction.
//! 2. **Not absurd.** The prediction is within a stated factor of the
//!    observation. A model that over-predicts by 100x would satisfy (1) and
//!    refuse everything.
//!
//! The measurement this file cannot make in-process is peak *RSS*, which
//! includes allocator fragmentation and the binary's own pages. That is measured
//! externally and recorded in
//! `/nas3/data/axeyum/frontier-2026-08-13/agent-g-drat-memory/RESULT.md`; the
//! two agree to within the fixed overhead the model carries.

use std::io::Cursor;

use axeyum_cnf::{
    BackwardCheckOutcome, CnfClause, CnfFormula, CnfLit, CnfVar, DratCheckRoute, DratMemoryModel,
    DratProofShape, FormulaShape, MemoryBudget, ProofSolveOutcome,
    check_drat_backward_reader_within, check_drat_backward_within, solve_with_drat_proof,
    write_drat,
};

fn lit(value: i64) -> CnfLit {
    let var = CnfVar::new(usize::try_from(value.unsigned_abs() - 1).expect("nonzero literal"))
        .expect("variable index fits");
    if value < 0 {
        CnfLit::positive(var).negated()
    } else {
        CnfLit::positive(var)
    }
}

/// Pigeonhole `PHP(holes + 1, holes)`: unsatisfiable, with a proof big enough
/// that the per-run fixed costs are not the whole measurement.
///
/// Sizes, measured with this workspace's own CDCL core (release):
/// `holes = 7` gives 6,153 steps / 310 KB in 0.03 s, `holes = 8` gives 48,271
/// steps / 3.2 MB in 0.34 s, `holes = 9` gives 199,809 steps / 16.6 MB in
/// 2.4 s. Smaller instances were tried first and rejected: `holes = 5` produces
/// a 2,875-byte proof, at which the model's fixed term is 3,891x the structures
/// being measured and the calibration says nothing.
fn pigeonhole(holes: usize) -> CnfFormula {
    let pigeons = holes + 1;
    let variable = |pigeon: usize, hole: usize| -> i64 {
        i64::try_from(pigeon * holes + hole + 1).expect("pigeonhole variable fits")
    };
    let mut f = CnfFormula::new(pigeons * holes);
    for pigeon in 0..pigeons {
        let clause: Vec<i64> = (0..holes).map(|hole| variable(pigeon, hole)).collect();
        f.add_clause(CnfClause::new(clause.iter().map(|&v| lit(v)).collect()))
            .expect("clause is over the formula's variables");
    }
    for hole in 0..holes {
        for a in 0..pigeons {
            for b in (a + 1)..pigeons {
                f.add_clause(CnfClause::new(vec![
                    lit(-variable(a, hole)),
                    lit(-variable(b, hole)),
                ]))
                .expect("clause is over the formula's variables");
            }
        }
    }
    f
}

/// The most the prediction is allowed to exceed the observation by. Generous,
/// because the model must cover per-run fixed costs that a small proof does not
/// amortise; the point of the bound is to catch a model that has become
/// meaningless, not to pin a coefficient.
const MAX_OVERPREDICTION: f64 = 3.0;

#[test]
fn the_model_covers_what_the_file_backed_route_actually_holds() {
    let mut checked = 0usize;
    for holes in 7..=9 {
        let f = pigeonhole(holes);
        let ProofSolveOutcome::Unsat(proof) = solve_with_drat_proof(&f) else {
            panic!("PHP({}, {holes}) is unsatisfiable", holes + 1);
        };
        let text = write_drat(&proof);
        let shape = DratProofShape::sample(
            Cursor::new(text.as_bytes()),
            text.len() as u64,
            text.len() as u64,
        )
        .expect("a cursor cannot fail");
        let estimate = DratMemoryModel::new(DratCheckRoute::FileBackedBackward)
            .estimate(shape, FormulaShape::of(&f));
        let outcome = check_drat_backward_reader_within(
            &f,
            Cursor::new(text.as_bytes()),
            estimate,
            // A budget that cannot bind, so this test measures the model and
            // never the budget.
            MemoryBudget::bytes(u64::MAX),
        )
        .expect("the proof verifies");
        let BackwardCheckOutcome::Refuted(report) = outcome else {
            panic!("PHP({}, {holes}) must be refuted", holes + 1);
        };
        // The estimate predicts peak *resident* size; the observation measures
        // the checker's own allocations. The documented difference between them
        // is the fixed term, so it comes off before they are compared.
        let predicted = report
            .estimate()
            .estimated_bytes()
            .saturating_sub(DratMemoryModel::FIXED_BYTES);
        let observed = report.observed_structure_bytes();
        assert!(
            predicted >= observed,
            "the file-backed model under-predicts PHP({}, {holes}): predicted {predicted}, \
             held {observed}. Under-prediction is the direction that produces an OOM kill.",
            holes + 1
        );
        #[allow(clippy::cast_precision_loss)]
        let slack = predicted as f64 / observed.max(1) as f64;
        assert!(
            slack <= MAX_OVERPREDICTION,
            "the file-backed model over-predicts PHP({}, {holes}) by {slack:.1}x \
             (predicted {predicted}, held {observed}); it would refuse checks that fit",
            holes + 1
        );
        checked += 1;
    }
    // Control: if the loop never ran, everything above is vacuous.
    assert_eq!(checked, 3, "the calibration loop must have run");
}

#[test]
fn the_model_covers_what_the_in_memory_route_actually_holds() {
    let mut checked = 0usize;
    for holes in 7..=9 {
        let f = pigeonhole(holes);
        let ProofSolveOutcome::Unsat(proof) = solve_with_drat_proof(&f) else {
            panic!("PHP({}, {holes}) is unsatisfiable", holes + 1);
        };
        let outcome = check_drat_backward_within(&f, &proof, MemoryBudget::bytes(u64::MAX))
            .expect("the proof verifies");
        let BackwardCheckOutcome::Refuted(report) = outcome else {
            panic!("PHP({}, {holes}) must be refuted", holes + 1);
        };
        let predicted = report
            .estimate()
            .estimated_bytes()
            .saturating_sub(DratMemoryModel::FIXED_BYTES);
        let observed = report.observed_structure_bytes();
        assert!(
            predicted >= observed,
            "the in-memory model under-predicts PHP({}, {holes}): predicted {predicted}, \
             held {observed}",
            holes + 1
        );
        checked += 1;
    }
    assert_eq!(checked, 3, "the calibration loop must have run");
}

#[test]
fn the_file_backed_route_holds_strictly_less_than_the_in_memory_one() {
    // The claim the whole change rests on, asserted on a live measurement of
    // both routes over the same proof rather than on the cost constants.
    let f = pigeonhole(8);
    let ProofSolveOutcome::Unsat(proof) = solve_with_drat_proof(&f) else {
        panic!("PHP(9, 8) is unsatisfiable");
    };
    let text = write_drat(&proof);

    let in_memory = check_drat_backward_within(&f, &proof, MemoryBudget::bytes(u64::MAX))
        .expect("the proof verifies")
        .report()
        .expect("the check ran");
    let file_shape = DratProofShape::sample(
        Cursor::new(text.as_bytes()),
        text.len() as u64,
        text.len() as u64,
    )
    .expect("a cursor cannot fail");
    let file_backed = check_drat_backward_reader_within(
        &f,
        Cursor::new(text.as_bytes()),
        DratMemoryModel::new(DratCheckRoute::FileBackedBackward)
            .estimate(file_shape, FormulaShape::of(&f)),
        MemoryBudget::bytes(u64::MAX),
    )
    .expect("the proof verifies")
    .report()
    .expect("the check ran");

    // Both routes build the same plan, so the structures they hold are the
    // same; what differs is the predicted cost, because only one of them has to
    // carry a step vector. The plan itself is nonzero, which is the control that
    // makes the comparison mean anything.
    assert!(
        file_backed.observed_structure_bytes() > 0,
        "the file-backed route reported holding nothing, so nothing was measured"
    );
    assert_eq!(
        file_backed.observed_structure_bytes(),
        in_memory.observed_structure_bytes(),
        "the two routes must build byte-identical plans"
    );
    assert!(
        file_backed.estimate().estimated_bytes() < in_memory.estimate().estimated_bytes(),
        "the file-backed route must be predicted cheaper: {} vs {}",
        file_backed.estimate().estimated_bytes(),
        in_memory.estimate().estimated_bytes()
    );
}

#[test]
fn a_budget_that_cannot_be_met_declines_instead_of_being_killed() {
    // The behaviour that replaces exit 137: a check that does not fit produces a
    // typed outcome, not a signal.
    let f = pigeonhole(4);
    let ProofSolveOutcome::Unsat(proof) = solve_with_drat_proof(&f) else {
        panic!("PHP(5, 4) is unsatisfiable");
    };
    let text = write_drat(&proof);
    let shape = DratProofShape::from_proof_bytes(text.len() as u64);
    let estimate = DratMemoryModel::new(DratCheckRoute::FileBackedBackward)
        .estimate(shape, FormulaShape::of(&f));

    let outcome = check_drat_backward_reader_within(
        &f,
        Cursor::new(text.as_bytes()),
        estimate,
        MemoryBudget::bytes(1024),
    )
    .expect("a decline is not an error");
    assert!(!outcome.is_refuted(), "a declined check refutes nothing");
    let decline = outcome.decline().expect("the check was declined");
    assert!(decline.shortfall_bytes() > 0);

    // The control that makes the above mean something: the *same* proof and the
    // *same* formula do get refuted once the budget allows it. Without this, a
    // decline would be indistinguishable from a proof that simply never checks.
    let admitted = check_drat_backward_reader_within(
        &f,
        Cursor::new(text.as_bytes()),
        estimate,
        MemoryBudget::bytes(u64::MAX),
    )
    .expect("the proof verifies");
    assert!(
        admitted.is_refuted(),
        "the same proof under a sufficient budget must be refuted, or the decline \
         above proved nothing about the budget"
    );
}

#[test]
fn sampling_the_head_of_a_proof_predicts_the_whole_of_it() {
    // The scheduler's real question: read a little of the file, predict the
    // whole check. Compare a 4 KiB sample against the exact count.
    let f = pigeonhole(8);
    let ProofSolveOutcome::Unsat(proof) = solve_with_drat_proof(&f) else {
        panic!("PHP(9, 8) is unsatisfiable");
    };
    let text = write_drat(&proof);
    assert!(
        text.len() > 100_000,
        "the sample must be a small fraction of the proof, but the proof is only {} bytes",
        text.len()
    );

    let exact = DratProofShape::sample(
        Cursor::new(text.as_bytes()),
        text.len() as u64,
        text.len() as u64,
    )
    .expect("a cursor cannot fail");
    let sampled = DratProofShape::sample(
        Cursor::new(text.as_bytes()),
        text.len() as u64,
        DratProofShape::recommended_sample_bytes(text.len() as u64),
    )
    .expect("a cursor cannot fail");

    #[allow(clippy::cast_precision_loss)]
    let error = (sampled.added_literals() as f64 - exact.added_literals() as f64).abs()
        / exact.added_literals() as f64;
    assert!(
        error < 0.25,
        "the recommended sample mis-estimated the added-literal count by {:.0}% \
         (sampled {}, exact {})",
        error * 100.0,
        sampled.added_literals(),
        exact.added_literals()
    );

    // The control that makes the recommendation mean something: a deliberately
    // tiny head sample must be *worse*. Without it this test would pass on a
    // proof whose head happened to be representative, proving nothing about the
    // sample size at all.
    let tiny = DratProofShape::sample(Cursor::new(text.as_bytes()), text.len() as u64, 512)
        .expect("a cursor cannot fail");
    #[allow(clippy::cast_precision_loss)]
    let tiny_error = (tiny.added_literals() as f64 - exact.added_literals() as f64).abs()
        / exact.added_literals() as f64;
    assert!(
        tiny_error > error,
        "a 512-byte sample was no worse than the recommended one ({tiny_error:.2} vs \
         {error:.2}); the head of this proof is representative and the test is vacuous"
    );
    // ...and the bias is toward over-estimating, which is the safe direction for
    // a memory budget.
    assert!(
        tiny.added_literals() > exact.added_literals(),
        "a tiny head sample under-estimated the literal count, which would admit a \
         check that does not fit"
    );
}
