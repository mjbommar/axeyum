//! The double-duty thesis, demonstrated end to end (ADR-0033).
//!
//! One run shows the *same* self-checking artifacts serving as a curriculum and
//! as test/benchmark coverage:
//!
//! 1. the concept DAG as a teaching sequence;
//! 2. a scenario rendered as a problem statement + worked solution;
//! 3. the **sound auto-grader** accepting a correct answer and rejecting a wrong
//!    one — judged by the evaluator, never by a search;
//! 4. a real, re-checked Alethe **proof** for an UNSAT bit-vector identity, with
//!    its step count as a measured, proof-level difficulty signal;
//! 5. the curriculum/coverage audit.
//!
//! Run with:
//!
//! ```sh
//! cargo run -p axeyum-bench --example curriculum_demo
//! ```

use axeyum_cnf::check_alethe;
use axeyum_scenarios::{
    Answer, Concept, Exercise, Expectation, all_catalog_scenarios, coverage_report,
    de_morgan_identity, full_adder_identity, mixing_inversion, topological_order,
};
use axeyum_solver::prove_qf_bv_unsat_alethe;

fn main() {
    print_curriculum();
    print_example_exercise();
    demonstrate_sound_grading();
    demonstrate_checked_proof();
    print_coverage();
}

/// 1. The concept DAG as a bottom-up teaching sequence.
fn print_curriculum() {
    println!("== Curriculum (topological teaching order) ==\n");
    for (i, concept) in topological_order().into_iter().enumerate() {
        let prereqs: Vec<&str> = concept.prerequisites().iter().map(|c| c.title()).collect();
        let after = if prereqs.is_empty() {
            String::new()
        } else {
            format!("  (after: {})", prereqs.join(", "))
        };
        println!("{:>2}. {}{after}", i + 1, concept.title());
        println!("    {}", concept.summary());
    }
    println!();
}

/// 2. A scenario rendered as a problem + worked solution.
fn print_example_exercise() {
    println!("== A scenario rendered as a homework problem ==\n");
    let scenario = de_morgan_identity(8);
    let ex = Exercise::new(&scenario);
    println!("{}", ex.prompt());
    let d = ex.difficulty();
    println!(
        "Difficulty: {:?} (symbols {}, constraints {}, enumeration bits {:?})\n",
        d.tier, d.symbols, d.constraints, d.enumeration_bits
    );
    println!("--- worked solution ---");
    println!("{}", ex.solution());
}

/// 3. The sound grader: a correct answer is Correct, a wrong one is rejected by
///    the evaluator — never silently accepted.
fn demonstrate_sound_grading() {
    println!("== Sound auto-grading (the evaluator is the judge) ==\n");

    let sat = mixing_inversion(8, 3, 0x00C0_FFEE);
    sat.self_check().expect("scenario self-checks");
    let ex = Exercise::new(&sat);
    if let Expectation::Sat { witness } = &sat.expectation {
        let good = ex.grade(&Answer::Sat {
            witness: witness.clone(),
        });
        println!("  correct witness for a SAT scenario  -> {good:?}");
    }
    let bad = ex.grade(&Answer::Sat {
        witness: axeyum_ir::Assignment::new(),
    });
    println!("  empty (unbound) witness               -> {bad:?}  <- rejected, not accepted");
    println!(
        "  claiming UNSAT on a SAT scenario      -> {:?}",
        ex.grade(&Answer::Unsat)
    );

    let unsat = full_adder_identity(4);
    let ex = Exercise::new(&unsat);
    println!(
        "  correct UNSAT verdict                 -> {:?}\n",
        ex.grade(&Answer::Unsat)
    );
}

/// 4. A real Alethe proof for an UNSAT bit-vector identity, re-checked by the
///    in-tree checker. The proof IS the worked solution at the proof level, and
///    its length is a measured, proof-level difficulty signal.
fn demonstrate_checked_proof() {
    println!("== Trusted small checking: a re-checked proof ==\n");
    let scenario = de_morgan_identity(8);
    let assertions: Vec<_> = scenario.query.solver_terms().collect();
    match prove_qf_bv_unsat_alethe(&scenario.arena, &assertions) {
        Some(proof) => {
            let accepted = check_alethe(&proof).unwrap_or(false);
            println!(
                "  De Morgan (BV) is UNSAT: emitted a {}-command Alethe proof.",
                proof.len()
            );
            println!(
                "  Re-checked by the in-tree checker: {}",
                if accepted { "VALID" } else { "REJECTED" }
            );
            println!(
                "  Proof length ({}) is a proof-level difficulty signal.\n",
                proof.len()
            );
        }
        None => println!("  (this instance is outside the QF_BV Alethe fragment)\n"),
    }
}

/// 5. The curriculum/coverage audit over every self-checking scenario.
fn print_coverage() {
    println!("== Coverage audit (curriculum node <-> exercises) ==\n");
    let scenarios = all_catalog_scenarios();
    print!("{}", coverage_report(&scenarios));
    // Show that the bottom rung is now covered, and that proofs remain a gap.
    let covered = Concept::PropositionalLogic.has_exercise();
    println!("\nPropositional logic has a self-checking exercise: {covered}");
}
