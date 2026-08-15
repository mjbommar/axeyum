//! Does changing the monomial order change what the geometry facts *claim*?
//!
//! [`axeyum_cas::geometry_certify::certify`] returns the certificate for the
//! **smallest condition subset that succeeds**, and "succeeds" is budget-relative:
//! a subset that *declines* is skipped rather than decided. So a faster monomial
//! order can in principle move a certificate onto a smaller condition set — and
//! those conditions are hypotheses in the facts' `formal.statement`. Switching the
//! default order is therefore a change to what the facts assert unless this is
//! measured, not argued.
//!
//! This example measures it. For every corpus theorem it runs **every** condition
//! subset under both orders and prints the verdict for each, then runs the full
//! `certify` under both and compares the condition set and the serialized
//! certificate byte for byte.
//!
//! The two things to read off the output:
//!
//! 1. `conditions` agree between the orders, per theorem. A `MOVED` row — both
//!    orders certify, with *different* condition sets — is a change to a fact's
//!    statement and must be handled as one. A `REACH ONLY` row, where one order
//!    certifies and the other does not, is a difference in reach: the failing
//!    order's condition set is unknown rather than equal, so there is nothing to
//!    compare, and point 2 is what settles the theorem instead.
//! 2. every subset is **decided** (`in ideal` / `not in ideal`) rather than
//!    declined, reported per order. Ideal membership does not depend on the
//!    order, so once every subset is decided under the order that produced the
//!    certificate, the minimality of the reported condition set is absolute
//!    rather than scoped to the budget — and no order, budget or algorithm can
//!    move it.
//!
//! `cargo run -p axeyum-cas --release --example geometry_order_audit [ids...]`
//!
//! Minutes, not seconds: `lex` pays the full cost of the theorems it cannot
//! reach, which is the point of running it.

use std::time::{Duration, Instant};

use axeyum_cas::geometry_certify::{
    Condition, GeometryProblem, INVERSE_PREFIX, ProofOutcome, certify, geometry_limits,
};
use axeyum_cas::geometry_corpus::corpus;
use axeyum_cas::geometry_json::to_json;
use axeyum_cas::groebner::MonomialOrder;
use axeyum_cas::groebner_cert::{CofactorOutcome, Limits, reduce_many_with_cofactors};
use axeyum_cas::mvpoly::MvPoly;
use axeyum_ir::Rational;

const ORDERS: [MonomialOrder; 2] = [MonomialOrder::Lex, MonomialOrder::DegRevLex];

fn limits_with(order: MonomialOrder) -> Limits {
    Limits {
        order,
        ..geometry_limits()
    }
}

/// The generators for one condition subset, in the same layout `certify` builds:
/// the hypotheses, then `d·z − 1` per condition.
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

/// Every subset of the stated conditions, in `certify`'s enumeration order:
/// increasing size, then ascending index.
fn subsets(problem: &GeometryProblem) -> Vec<Vec<usize>> {
    let count = problem.nondegeneracy.len();
    let mut all: Vec<Vec<usize>> = (0u32..(1u32 << count))
        .map(|mask| {
            (0..count)
                .filter(|index| mask & (1 << index) != 0)
                .collect::<Vec<usize>>()
        })
        .collect();
    all.sort_by(|left, right| left.len().cmp(&right.len()).then_with(|| left.cmp(right)));
    all
}

/// What one subset did under one order.
struct SubsetVerdict {
    decided: bool,
    in_ideal: bool,
    label: String,
    elapsed: Duration,
}

fn probe(problem: &GeometryProblem, subset: &[usize], order: MonomialOrder) -> SubsetVerdict {
    let chosen: Vec<&Condition> = subset
        .iter()
        .map(|&index| &problem.nondegeneracy[index])
        .collect();
    let generators = generators(problem, &chosen);
    let targets: Vec<MvPoly> = problem.conclusions.iter().map(|c| c.poly.clone()).collect();
    let started = Instant::now();
    let outcomes = reduce_many_with_cofactors(&generators, &targets, limits_with(order));
    let elapsed = started.elapsed();

    if let Some(reason) = outcomes.iter().find_map(|outcome| match outcome {
        CofactorOutcome::Declined(reason) => Some(*reason),
        CofactorOutcome::Reduced { .. } => None,
    }) {
        return SubsetVerdict {
            decided: false,
            in_ideal: false,
            label: format!("DECLINED ({reason:?})"),
            elapsed,
        };
    }
    let in_ideal = outcomes
        .iter()
        .all(|o| matches!(o, CofactorOutcome::Reduced { remainder, .. } if remainder.is_zero()));
    let terms: usize = outcomes
        .iter()
        .filter_map(|outcome| match outcome {
            CofactorOutcome::Reduced { cofactors, .. } => {
                Some(cofactors.iter().map(MvPoly::term_count).sum::<usize>())
            }
            CofactorOutcome::Declined(_) => None,
        })
        .sum();
    SubsetVerdict {
        decided: true,
        in_ideal,
        label: if in_ideal {
            format!("in ideal ({terms} cofactor terms)")
        } else {
            "not in ideal".to_string()
        },
        elapsed,
    }
}

/// The condition ids `certify` ends up using, or a description of why it did not
/// produce a certificate, plus the serialized certificate for byte comparison.
fn certified(problem: &GeometryProblem, order: MonomialOrder) -> (String, Option<String>) {
    match certify(problem, limits_with(order)) {
        ProofOutcome::Certified(certificate) => {
            let conditions = certificate
                .saturations
                .iter()
                .map(|saturation| saturation.condition_id.clone())
                .collect::<Vec<_>>();
            let label = if conditions.is_empty() {
                "{}".to_string()
            } else {
                format!("{{{}}}", conditions.join(", "))
            };
            (label, Some(to_json(&certificate)))
        }
        ProofOutcome::NotInSaturatedIdeal { conclusion_id, .. } => (
            format!("NOT CERTIFIED (`{conclusion_id}` has a remainder)"),
            None,
        ),
        ProofOutcome::Declined(reason) => (format!("NOT CERTIFIED ({reason:?})"), None),
    }
}

/// What auditing one theorem concluded, for the summary line.
#[derive(Default)]
struct Tally {
    agreed: usize,
    moved: usize,
    reach_only: usize,
    identical_bytes: usize,
    all_decided: usize,
}

/// Every condition subset of one theorem, under every order, then the two full
/// `certify` runs compared.
fn audit(problem: &GeometryProblem, tally: &mut Tally) {
    println!(
        "{} ({} hypotheses, {} conditions, {} conclusions)",
        problem.id,
        problem.hypotheses.len(),
        problem.nondegeneracy.len(),
        problem.conclusions.len()
    );

    // Tracked per order: "every subset decided" is what upgrades the reported
    // condition set from smallest-the-budget-could-decide to smallest absolutely,
    // and it is a property of the order the certificate was produced under, not
    // of both.
    let mut decided_under = [true; ORDERS.len()];
    for subset in subsets(problem) {
        let label = if subset.is_empty() {
            "{}".to_string()
        } else {
            format!(
                "{{{}}}",
                subset
                    .iter()
                    .map(|&index| problem.nondegeneracy[index].id.as_str())
                    .collect::<Vec<_>>()
                    .join(", ")
            )
        };
        print!("    {label:<26}");
        for (slot, order) in ORDERS.into_iter().enumerate() {
            let verdict = probe(problem, &subset, order);
            decided_under[slot] &= verdict.decided;
            let name = match order {
                MonomialOrder::Lex => "lex",
                MonomialOrder::DegRevLex => "grevlex",
            };
            print!(
                "  {name:>7} {:>9.1?} {:<28}",
                verdict.elapsed, verdict.label
            );
            let _ = verdict.in_ideal;
        }
        println!();
    }
    if decided_under.iter().all(|decided| *decided) {
        tally.all_decided += 1;
    }

    let (lex_conditions, lex_bytes) = certified(problem, MonomialOrder::Lex);
    let (grevlex_conditions, grevlex_bytes) = certified(problem, MonomialOrder::DegRevLex);
    let same_bytes = lex_bytes.is_some() && lex_bytes == grevlex_bytes;
    // Three outcomes, not two. "One order does not certify at all" is a
    // difference in REACH; only two orders that both certify, with different
    // condition sets, is a difference in what the theorem CLAIMS — and collapsing
    // them would raise an alarm about the wrong thing.
    let verdict = match (&lex_bytes, &grevlex_bytes) {
        (Some(_), Some(_)) if lex_conditions == grevlex_conditions => {
            tally.agreed += 1;
            "SAME"
        }
        (Some(_), Some(_)) => {
            tally.moved += 1;
            "MOVED"
        }
        _ => {
            tally.reach_only += 1;
            "REACH ONLY"
        }
    };
    if same_bytes {
        tally.identical_bytes += 1;
    }
    println!(
        "    => certify: lex {lex_conditions} | grevlex {grevlex_conditions}  [{verdict}]  \
         certificate bytes {}  every subset decided: lex {} / grevlex {}\n",
        if same_bytes { "IDENTICAL" } else { "differ" },
        if decided_under[0] { "yes" } else { "NO" },
        if decided_under[1] { "yes" } else { "NO" }
    );
}

// Theorems this audit cannot be run on, because the Gröbner route does not
// return on them at all -- which is precisely why they exist on the linear
// route. Naming them is not a convenience: an audit that silently skipped
// them would be indistinguishable from one that covered them, and the
// skipped count is printed for exactly that reason.
//
// This list is retro-active. `euler-line` joined the corpus on 2026-08-15 and
// this example was not updated, so from that moment an unrestricted run hung
// rather than reporting anything -- a broken instrument that still looked
// like a slow one. `pappus-hexagon` would have been the second.
const UNREACHED_BY_BUCHBERGER: [&str; 2] = ["euler-line", "pappus-hexagon"];

fn main() {
    let wanted: Vec<String> = std::env::args().skip(1).collect();
    println!(
        "geometry monomial-order audit: every condition subset, both orders\nbudget {:?}\n",
        geometry_limits()
    );

    let mut tally = Tally::default();
    let mut examined = 0usize;
    let mut skipped: Vec<String> = Vec::new();
    for problem in corpus() {
        if !wanted.is_empty() && !wanted.contains(&problem.id) {
            continue;
        }
        if UNREACHED_BY_BUCHBERGER.contains(&problem.id.as_str()) && wanted.is_empty() {
            skipped.push(problem.id.clone());
            continue;
        }
        examined += 1;
        audit(&problem, &mut tally);
    }
    if !skipped.is_empty() {
        println!(
            "SKIPPED {} theorem(s) the Gröbner route does not return on, so this audit \
             says NOTHING about them: {}\nTheir condition sets are established minimal by \
             refuting every proper subset with a committed counterexample instead -- see \
             `every_used_condition_set_is_minimal_absolutely`.\n",
            skipped.len(),
            skipped.join(", ")
        );
    }
    let Tally {
        agreed,
        moved,
        reach_only,
        identical_bytes,
        all_decided,
    } = tally;

    println!(
        "{examined} theorems: {agreed} condition sets unchanged, {moved} MOVED, \
         {reach_only} certified by one order only, {identical_bytes} certificates \
         byte-identical, {all_decided} with every subset decided under both orders"
    );
    if moved > 0 {
        println!(
            "\nA MOVED row changes the hypotheses of the corresponding fact's \
             `formal.statement`. Do not regenerate the artifact without editing the fact."
        );
    }
    if reach_only > 0 {
        println!(
            "\nA REACH ONLY row is a theorem one order certifies and the other does not. \
             That is a difference in reach, not in claim -- but the condition set of the \
             order that FAILS is unknown rather than equal, so it cannot be compared. Read \
             the per-subset rows above: if every subset is decided under the certifying \
             order, its condition set is minimal absolutely and nothing is left open."
        );
    }
}
