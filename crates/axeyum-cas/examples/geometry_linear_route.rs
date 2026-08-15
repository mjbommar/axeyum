//! The linear-elimination route against the Gröbner route, theorem by theorem.
//!
//! The `geometry-frontier` lane established that `euler-line` does not fail on
//! width, memory or arithmetic: it fails because the intermediate basis keeps
//! growing and the S-pair queue is quadratic in a basis that never saturates. Its
//! ladder (`geometry_obstruction`) is the measurement, and the numbers to beat
//! are 65 S-pairs processed / 528 still queued / a 33-element basis, still
//! climbing.
//!
//! This example reports the same quantities for the linear route, which is the
//! only way the comparison is like-for-like: how many S-pairs does it process,
//! how large does the basis get, and what is left queued. It also prints the
//! block decomposition the route found, the determinant it multiplied through by,
//! and the power of the non-degeneracy condition it had to divide back out —
//! because "the multiplier is the square of the condition polynomial" is the
//! whole reason the certificate can stay in the original generators.
//!
//! Run from the repository root:
//! `cargo run -p axeyum-cas --release --example geometry_linear_route`
//!
//! Trailing arguments restrict the run to the named theorem ids.

use std::time::Instant;

use axeyum_cas::geometry_certify::{
    GeometryProblem, ProofOutcome, certify_by_linear_elimination, geometry_limits,
};
use axeyum_cas::geometry_check::{CheckOptions, GeometryVerdict, check_certificate};
use axeyum_cas::geometry_corpus::{corpus, frontier};
use axeyum_cas::groebner_cert::reduce_many_with_cofactors_traced;
use axeyum_cas::linear_elim::eliminate;
use axeyum_cas::mvpoly::MvPoly;

fn main() {
    let wanted: Vec<String> = std::env::args().skip(1).collect();
    let problems: Vec<GeometryProblem> = corpus().into_iter().chain(frontier()).collect();

    for problem in problems {
        if !wanted.is_empty() && !wanted.contains(&problem.id) {
            continue;
        }
        println!("=== {} ===", problem.id);
        let hypotheses: Vec<MvPoly> = problem
            .hypotheses
            .iter()
            .map(|hypothesis| hypothesis.poly.clone())
            .collect();

        for conclusion in &problem.conclusions {
            let Some(done) = eliminate(&hypotheses, &conclusion.poly) else {
                println!("  {:<24} elimination overflowed", conclusion.id);
                continue;
            };
            println!(
                "  {:<24} blocks={} multiplier={} terms, deg {}  residue={} terms",
                conclusion.id,
                done.blocks.len(),
                done.multiplier.term_count(),
                done.multiplier.total_degree(),
                done.residue.term_count()
            );
            for (block, power) in done.blocks.iter().zip(done.powers.iter()) {
                println!(
                    "      block {:?} rows {:?} det={} terms ^{power}",
                    block.unknowns,
                    block.rows,
                    block.determinant.term_count()
                );
            }
            // The like-for-like number. Whatever linear algebra could not remove
            // is what a Gröbner route would still have to chew on; these are the
            // counters `geometry_obstruction` reports for the whole problem.
            //
            // A zero residue is short-circuited rather than reduced, and that is
            // not bookkeeping: reducing the zero polynomial still computes a
            // Gröbner basis of the hypotheses, which is exactly the divergent
            // computation this route exists to avoid. Asking for the counters
            // unconditionally hangs on `euler-line`.
            if done.residue.is_zero() {
                println!(
                    "      handover to Buchberger: 0 S-pairs processed, 0 queued, basis 0 \
                     (the residue is zero -- nothing left to do)"
                );
            } else {
                let (_, stats) = reduce_many_with_cofactors_traced(
                    &hypotheses,
                    std::slice::from_ref(&done.residue),
                    geometry_limits(),
                );
                println!(
                    "      handover to Buchberger: {} S-pairs processed, {} queued, basis {}",
                    stats.pairs_processed, stats.pairs_queued, stats.max_basis_len
                );
            }
        }

        let started = Instant::now();
        let outcome = certify_by_linear_elimination(&problem, Some(geometry_limits()));
        let elapsed = started.elapsed();
        match outcome {
            ProofOutcome::Certified(certificate) => {
                let conditions: Vec<&str> = certificate
                    .saturations
                    .iter()
                    .map(|saturation| saturation.condition_id.as_str())
                    .collect();
                let cofactor_terms: usize = certificate
                    .conclusions
                    .iter()
                    .flat_map(|conclusion| conclusion.cofactors.iter())
                    .map(MvPoly::term_count)
                    .sum();
                let verdict = check_certificate(&certificate, &CheckOptions::default());
                println!(
                    "  CERTIFIED in {elapsed:.1?}  conditions={conditions:?}  \
                     {cofactor_terms} cofactor terms  checker={}",
                    match &verdict {
                        GeometryVerdict::Verified(report) => format!(
                            "verified ({} conclusion(s), {} numeric points)",
                            report.conclusions_checked, report.numeric_points_checked
                        ),
                        GeometryVerdict::Rejected(reason) => format!("REJECTED: {reason}"),
                    }
                );
                if let GeometryVerdict::Rejected(_) = verdict {
                    std::process::exit(1);
                }
            }
            ProofOutcome::NotInSaturatedIdeal {
                conclusion_id,
                remainder,
            } => println!(
                "  not in the ideal: `{conclusion_id}` leaves a {}-term remainder ({elapsed:.1?})",
                remainder.term_count()
            ),
            ProofOutcome::Declined(reason) => println!("  declined: {reason:?} ({elapsed:.1?})"),
        }
        println!();
    }
}
