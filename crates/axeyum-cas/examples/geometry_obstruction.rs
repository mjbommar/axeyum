//! *Why* a geometry theorem does not return — the growth curve, not the clock.
//!
//! `geometry_probe` answers "does this reduce inside the budget", and for a
//! theorem that does not it prints a duration. A duration names no obstruction:
//! `euler-line` was recorded as "no verdict within 600 s" by one lane and "no
//! verdict within 1200 s under either monomial order" by the next, and neither
//! sentence says what the computation was *doing*.
//!
//! This example says. It runs the same reduction under a **ladder** of S-pair
//! ceilings, with every other ceiling generous, and reports
//! [`ReductionStats`](axeyum_cas::groebner_cert::ReductionStats) at each rung: how
//! many pairs were processed, how many are still queued, how far the basis grew,
//! and — the number that matters — the widest intermediate polynomial reached.
//! Reading down the columns shows whether the cost is a queue that keeps
//! refilling, a basis that keeps growing, or single polynomials that keep getting
//! wider, and whether any of the three is levelling off.
//!
//! ```text
//! cargo run -p axeyum-cas --release --example geometry_obstruction -- <id> [max-pairs]
//! AXEYUM_MONOMIAL_ORDER=grevlex  selects degree-reverse-lexicographic.
//! AXEYUM_CONDITIONS=all|none     selects the condition subset (default: none).
//! ```

use std::time::Instant;

use axeyum_cas::geometry_certify::{Condition, GeometryProblem, INVERSE_PREFIX};
use axeyum_cas::geometry_corpus::{corpus, frontier};
use axeyum_cas::groebner::MonomialOrder;
use axeyum_cas::groebner_cert::{CofactorOutcome, Limits, reduce_many_with_cofactors_traced};
use axeyum_cas::mvpoly::MvPoly;
use axeyum_ir::Rational;

fn order_from_env() -> MonomialOrder {
    match std::env::var("AXEYUM_MONOMIAL_ORDER").as_deref() {
        Ok("grevlex" | "degrevlex") => MonomialOrder::DegRevLex,
        _ => MonomialOrder::Lex,
    }
}

fn generators(problem: &GeometryProblem, subset: &[&Condition]) -> Vec<MvPoly> {
    let mut generators: Vec<MvPoly> = problem.hypotheses.iter().map(|h| h.poly.clone()).collect();
    for (slot, condition) in subset.iter().enumerate() {
        generators.push(
            condition
                .poly
                .mul(&MvPoly::var(&format!("{INVERSE_PREFIX}{slot}")))
                .expect("product")
                .sub(&MvPoly::constant(Rational::integer(1)))
                .expect("difference"),
        );
    }
    generators
}

/// One rung's verdict: `COMPLETE` when the basis closed inside the rung, and
/// otherwise the ceiling that stopped it.
fn describe(outcomes: &[CofactorOutcome]) -> String {
    if let Some(reason) = outcomes.iter().find_map(|outcome| match outcome {
        CofactorOutcome::Declined(reason) => Some(*reason),
        CofactorOutcome::Reduced { .. } => None,
    }) {
        return format!("stopped at the rung ({reason:?})");
    }
    if outcomes
        .iter()
        .all(|o| matches!(o, CofactorOutcome::Reduced { remainder, .. } if remainder.is_zero()))
    {
        let terms: usize = outcomes
            .iter()
            .filter_map(|outcome| match outcome {
                CofactorOutcome::Reduced { cofactors, .. } => {
                    Some(cofactors.iter().map(MvPoly::term_count).sum::<usize>())
                }
                CofactorOutcome::Declined(_) => None,
            })
            .sum();
        return format!("COMPLETE: in ideal ({terms} cofactor terms)");
    }
    "COMPLETE: not in ideal".to_string()
}

fn main() {
    let mut arguments = std::env::args().skip(1);
    let wanted = arguments.next().unwrap_or_else(|| "euler-line".to_string());
    let ceiling: u64 = arguments
        .next()
        .and_then(|text| text.parse().ok())
        .unwrap_or(4_096);
    let order = order_from_env();
    let use_conditions = matches!(std::env::var("AXEYUM_CONDITIONS").as_deref(), Ok("all"));

    let problem = corpus()
        .into_iter()
        .chain(frontier())
        .find(|problem| problem.id == wanted)
        .unwrap_or_else(|| panic!("no corpus or frontier theorem named `{wanted}`"));

    let subset: Vec<&Condition> = if use_conditions {
        problem.nondegeneracy.iter().collect()
    } else {
        Vec::new()
    };
    let generators = generators(&problem, &subset);
    let targets: Vec<MvPoly> = problem.conclusions.iter().map(|c| c.poly.clone()).collect();
    let variables = generators
        .iter()
        .flat_map(MvPoly::variables)
        .chain(targets.iter().flat_map(MvPoly::variables))
        .collect::<std::collections::BTreeSet<_>>();

    println!(
        "{} under {order:?}: {} generators, {} variables, conditions {}",
        problem.id,
        generators.len(),
        variables.len(),
        if subset.is_empty() { "none" } else { "all" }
    );
    println!(
        "  generator term counts: {:?}",
        generators
            .iter()
            .map(MvPoly::term_count)
            .collect::<Vec<_>>()
    );
    println!(
        "\n{:>10}  {:>10}  {:>10}  {:>8}  {:>8}  {:>8}  {:>8}  {:>10}  {:>11}  outcome",
        "pair cap",
        "processed",
        "queued",
        "wasted",
        "coprime",
        "basis",
        "widest",
        "red. steps",
        "elapsed"
    );

    let mut cap = 1u64;
    while cap <= ceiling {
        let limits = Limits {
            // Everything except the pair ceiling is set out of the way, so the
            // rung is the only thing that stops the run and the counters describe
            // the state at exactly that many S-pairs.
            reduction_steps: u64::MAX,
            pair_iterations: cap,
            basis_size: usize::MAX,
            poly_terms: usize::MAX,
            order,
        };
        let started = Instant::now();
        let (outcomes, stats) = reduce_many_with_cofactors_traced(&generators, &targets, limits);
        let elapsed = started.elapsed();
        let outcome = describe(&outcomes);
        println!(
            "{cap:>10}  {:>10}  {:>10}  {:>8}  {:>8}  {:>8}  {:>8}  {:>10}  {elapsed:>11.1?}  \
             {outcome}",
            stats.pairs_processed,
            stats.pairs_queued,
            // Pairs that reduced all the way to zero: work that taught the basis
            // nothing, and the work Buchberger's criteria exist to skip.
            stats.pairs_processed.saturating_sub(stats.basis_extensions),
            stats.pairs_coprime_lead,
            stats.max_basis_len,
            stats.max_poly_terms,
            stats.reduction_steps_spent,
        );
        if outcome.starts_with("COMPLETE") {
            break;
        }
        cap = cap.saturating_mul(2);
    }
}
