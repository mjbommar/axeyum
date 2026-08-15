//! Where the cofactor route stops: per-theorem, per-condition-subset cost.
//!
//! [`axeyum_cas::geometry_certify::certify`] tries condition subsets smallest
//! first, so the cost of a theorem is dominated by the subsets that do **not**
//! work — the ones whose Gröbner basis is computed only to find a nonzero
//! remainder. This example reports each subset separately, which is what sizes
//! the budget in `geometry_limits` and what identifies the theorems the route
//! cannot reach.
//!
//! `cargo run -p axeyum-cas --release --example geometry_probe [budget-scale]`

use std::time::Instant;

use axeyum_cas::geometry_certify::{Condition, GeometryProblem, INVERSE_PREFIX};
use axeyum_cas::geometry_corpus::{corpus, frontier};
use axeyum_cas::groebner::MonomialOrder;
use axeyum_cas::groebner_cert::{CofactorOutcome, Limits, reduce_many_with_cofactors};
use axeyum_cas::mvpoly::MvPoly;
use axeyum_ir::Rational;

fn budget(scale: u64, order: MonomialOrder) -> Limits {
    Limits {
        reduction_steps: 50_000 * scale,
        pair_iterations: 2_000 * scale,
        basis_size: 200,
        poly_terms: 8_000,
        order,
    }
}

/// The monomial order to probe with, from `AXEYUM_MONOMIAL_ORDER`.
///
/// An environment switch rather than a positional argument so the documented
/// `[budget-scale] [ids...]` invocation keeps working while the comparison this
/// example exists to make becomes a one-word change.
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

fn main() {
    let scale: u64 = std::env::args()
        .nth(1)
        .and_then(|text| text.parse().ok())
        .unwrap_or(1);
    let order = order_from_env();
    let limits = budget(scale, order);
    let wanted: Vec<String> = std::env::args().skip(2).collect();
    println!("budget scale {scale}, order {order:?}: {limits:?}\n");

    for problem in corpus().into_iter().chain(frontier()) {
        if !wanted.is_empty() && !wanted.contains(&problem.id) {
            continue;
        }
        let targets: Vec<MvPoly> = problem.conclusions.iter().map(|c| c.poly.clone()).collect();
        let variables = problem
            .hypotheses
            .iter()
            .flat_map(|h| h.poly.variables())
            .chain(problem.conclusions.iter().flat_map(|c| c.poly.variables()))
            .collect::<std::collections::BTreeSet<_>>()
            .len();
        println!(
            "{} ({variables} coordinates, {} hypotheses, {} conclusions)",
            problem.id,
            problem.hypotheses.len(),
            problem.conclusions.len()
        );
        let empty: Vec<&Condition> = Vec::new();
        let full: Vec<&Condition> = problem.nondegeneracy.iter().collect();
        let mut subsets: Vec<(String, Vec<&Condition>)> = vec![("{}".to_string(), empty)];
        if !full.is_empty() {
            let label = full
                .iter()
                .map(|c| c.id.as_str())
                .collect::<Vec<_>>()
                .join(", ");
            subsets.push((format!("{{{label}}}"), full));
        }
        for (label, subset) in subsets {
            let generators = generators(&problem, &subset);
            let started = Instant::now();
            let outcomes = reduce_many_with_cofactors(&generators, &targets, limits);
            let elapsed = started.elapsed();
            // A decline now names its cause. That is the whole point of the
            // measurement: "DECLINED" alone cannot distinguish a budget the
            // caller chose from an `i128` the caller cannot choose, and a lane
            // that reads the first as the second re-tunes limits forever.
            let declined = outcomes.iter().find_map(|o| match o {
                CofactorOutcome::Declined(reason) => Some(*reason),
                CofactorOutcome::Reduced { .. } => None,
            });
            let verdict = if let Some(reason) = declined {
                let kind = if reason.is_ceiling() {
                    "ceiling"
                } else {
                    "overflow"
                };
                format!("DECLINED ({kind}: {reason:?})")
            } else if outcomes.iter().all(
                |o| matches!(o, CofactorOutcome::Reduced { remainder, .. } if remainder.is_zero()),
            ) {
                let terms: usize = outcomes
                    .iter()
                    .filter_map(|o| match o {
                        CofactorOutcome::Reduced { cofactors, .. } => {
                            Some(cofactors.iter().map(MvPoly::term_count).sum::<usize>())
                        }
                        CofactorOutcome::Declined(_) => None,
                    })
                    .sum();
                format!("IN IDEAL ({terms} cofactor terms)")
            } else {
                "not in ideal".to_string()
            };
            println!("    conditions {label:<24} {elapsed:>10.1?}  {verdict}   [tracked]");
            // The same question WITHOUT cofactor tracking, through the plain
            // `Buchberger` path. When this succeeds and the tracked one declines,
            // what blew up is the representation in the generators, not the
            // ideal membership question.
            let started = Instant::now();
            let untracked: Vec<Option<bool>> = targets
                .iter()
                .map(|target| axeyum_cas::ideal_contains(&generators, target))
                .collect();
            let elapsed = started.elapsed();
            let verdict = if untracked.iter().any(Option::is_none) {
                "DECLINED".to_string()
            } else if untracked.iter().all(|answer| *answer == Some(true)) {
                "IN IDEAL".to_string()
            } else {
                "not in ideal".to_string()
            };
            println!("    {:<35} {elapsed:>10.1?}  {verdict}   [untracked]", "");
        }
    }
}
