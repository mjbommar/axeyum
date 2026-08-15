//! Bounded-degree linear algebra against Buchberger, on the residues the linear
//! route actually hands over.
//!
//! [`axeyum_cas::cofactor_ansatz`] and [`axeyum_cas::groebner_cert`] answer
//! overlapping questions by unrelated means, and the linear-elimination route
//! reaches for whichever settles its residue. This example makes the comparison
//! reproducible rather than asserted: for each condition subset of each corpus
//! theorem, it reports which blocks the subset **licenses**, how big the residue
//! that leaves is, and what each of the two routes does with it.
//!
//! The case that motivated the module is `pappus-hexagon` under its
//! one-condition subset. The X block is licensed, the Y and Z blocks are not, and
//! the residue is 48 terms of degree 4 over the six untouched hypotheses:
//!
//! ```text
//!   ansatz     solved at cofactor degree 2 in ~25 ms
//!   buchberger killed at 7.5 minutes, no answer
//! ```
//!
//! That is not a constant factor, and it is why the ansatz is tried first.
//!
//! The Buchberger column is **opt-in**, behind `--buchberger`, for the reason the
//! table above records: on `pappus-hexagon` it does not come back, and a default
//! that hangs is not a comparison anyone runs. `geometry_limits`'s ceilings do not
//! rescue it either — they are step counts, and a single reduction step against a
//! basis this wide is not cheap. Add `--patient` to raise them further.
//!
//! Run from the repository root:
//! `cargo run -p axeyum-cas --release --example geometry_cofactor_routes`
//!
//! Trailing arguments restrict the run to the named theorem ids.

use std::time::Instant;

use axeyum_cas::cofactor_ansatz::{AnsatzLimits, AnsatzOutcome, cofactors_by_ansatz};
use axeyum_cas::geometry_certify::{Constraint, GeometryProblem, geometry_limits};
use axeyum_cas::geometry_corpus::{corpus, frontier};
use axeyum_cas::groebner_cert::{CofactorOutcome, Limits, reduce_many_with_cofactors};
use axeyum_cas::linear_elim::{LinearBlock, detect_linear_blocks, eliminate_blocks};
use axeyum_cas::mvpoly::MvPoly;

/// Is `polynomial` a nonzero rational times a product of powers of `conditions`?
/// The same rule `geometry_certify::licensed_blocks` applies, restated here so the
/// example does not depend on a private helper.
fn licensed(polynomial: &MvPoly, conditions: &[MvPoly]) -> bool {
    if polynomial.is_zero() {
        return false;
    }
    let mut remaining = polynomial.clone();
    let mut progressed = true;
    while progressed {
        progressed = false;
        for condition in conditions {
            if condition.total_degree() == 0 {
                continue;
            }
            while let Some(quotient) = remaining.exact_div(condition) {
                remaining = quotient;
                progressed = true;
            }
        }
    }
    remaining.total_degree() == 0
}

/// One condition subset of one conclusion: which blocks it licenses, what
/// residue that leaves, and what each route does with it.
fn report_subset(
    problem: &GeometryProblem,
    hypotheses: &[MvPoly],
    conclusion: &Constraint,
    subset: &[usize],
    groebner: Limits,
    compare: bool,
) {
    let conditions: Vec<MvPoly> = subset
        .iter()
        .map(|&slot| problem.nondegeneracy[slot].poly.clone())
        .collect();
    let names: Vec<&str> = subset
        .iter()
        .map(|&slot| problem.nondegeneracy[slot].id.as_str())
        .collect();
    let all = detect_linear_blocks(hypotheses, &conclusion.poly);
    let detected = all.len();
    let kept: Vec<LinearBlock> = all
        .into_iter()
        .filter(|block| licensed(&block.determinant, &conditions))
        .collect();
    let consumed: Vec<usize> = kept
        .iter()
        .flat_map(|block| block.rows.iter().copied())
        .collect();
    let Some(done) = eliminate_blocks(hypotheses, &conclusion.poly, kept) else {
        println!("  {{{}}} elimination overflowed", names.join(","));
        return;
    };
    print!(
        "  {{{}}} {} blocks detected, {} licensed, residue {} terms",
        names.join(","),
        detected,
        done.blocks.len(),
        done.residue.term_count()
    );
    if done.blocks.is_empty() {
        println!("   (no block consumed — the route declines without handing over)");
        return;
    }
    if done.residue.is_zero() {
        println!("   (zero residue — no handover needed)");
        return;
    }
    let unconsumed: Vec<MvPoly> = (0..hypotheses.len())
        .filter(|index| !consumed.contains(index))
        .map(|index| hypotheses[index].clone())
        .collect();
    let start = Instant::now();
    let ansatz = cofactors_by_ansatz(&unconsumed, &done.residue, AnsatzLimits::geometry());
    let ansatz_elapsed = start.elapsed();
    let start = Instant::now();
    let buchberger = compare.then(|| {
        reduce_many_with_cofactors(&unconsumed, std::slice::from_ref(&done.residue), groebner)
    });
    let buchberger_elapsed = start.elapsed();
    println!(
        "\n      over {} unconsumed hypotheses:\n        ansatz     {} in {:?}\n        \
         buchberger {} in {:?}",
        unconsumed.len(),
        match &ansatz {
            AnsatzOutcome::Solved { degree, cofactors } => format!(
                "solved at cofactor degree {degree}, {} cofactor terms",
                cofactors.iter().map(MvPoly::term_count).sum::<usize>()
            ),
            AnsatzOutcome::NotInDegree(degree) =>
                format!("decided: not in the degree-{degree} slice"),
            AnsatzOutcome::Declined(reason) => format!("declined: {reason:?}"),
        },
        ansatz_elapsed,
        match buchberger.as_ref().map(|outcomes| &outcomes[0]) {
            None => "not run (pass --buchberger)".to_string(),
            Some(CofactorOutcome::Reduced { remainder, .. }) if remainder.is_zero() =>
                "reduced to zero".to_string(),
            Some(CofactorOutcome::Reduced { remainder, .. }) => format!(
                "remainder of {} terms — not in the ideal",
                remainder.term_count()
            ),
            Some(CofactorOutcome::Declined(reason)) => format!("declined: {reason:?}"),
        },
        buchberger_elapsed
    );
}

fn main() {
    let arguments: Vec<String> = std::env::args().skip(1).collect();
    let patient = arguments.iter().any(|argument| argument == "--patient");
    let compare = patient || arguments.iter().any(|argument| argument == "--buchberger");
    let wanted: Vec<&String> = arguments
        .iter()
        .filter(|argument| !argument.starts_with("--"))
        .collect();

    let groebner = if patient {
        Limits {
            reduction_steps: 5_000_000,
            pair_iterations: 200_000,
            basis_size: 5_000,
            poly_terms: 400_000,
            ..geometry_limits()
        }
    } else {
        geometry_limits()
    };

    for problem in corpus().into_iter().chain(frontier()) {
        if !wanted.is_empty() && !wanted.iter().any(|id| **id == problem.id) {
            continue;
        }
        println!("=== {} ===", problem.id);
        let hypotheses: Vec<MvPoly> = problem
            .hypotheses
            .iter()
            .map(|hypothesis| hypothesis.poly.clone())
            .collect();
        let count = problem.nondegeneracy.len();
        for mask in 0u32..(1u32 << count) {
            let subset: Vec<usize> = (0..count).filter(|slot| mask & (1 << slot) != 0).collect();
            for conclusion in &problem.conclusions {
                report_subset(
                    &problem,
                    &hypotheses,
                    conclusion,
                    &subset,
                    groebner,
                    compare,
                );
            }
        }
    }
}
