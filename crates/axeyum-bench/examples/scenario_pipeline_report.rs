//! Pipeline measurement over the self-checking scenario catalog.
//!
//! This example runs every [`axeyum_scenarios`] scenario through the pure-Rust
//! `sat-bv` backend and reports the named pipeline stages ([`BvLayerStats`]):
//! AIG size, CNF size, encoding density, and per-stage timing. It turns the
//! lowering/optimization pipeline into something measurable over a realistic,
//! oracle-free corpus, so an optimization can be justified by its effect on
//! these numbers rather than on a single public-slice frontier instance.
//!
//! Sizes are deterministic; timings are informational. Run with:
//!
//! ```sh
//! cargo run -p axeyum-bench --example scenario_pipeline_report
//! ```

use std::time::Duration;

use axeyum_scenarios::{Expectation, Family, Scenario, catalog};
use axeyum_solver::{BvLayerStats, CheckResult, SatBvBackend, SolverBackend, SolverConfig};

/// Per-check budget; the catalog is sized to decide well inside this.
const TIMEOUT: Duration = Duration::from_secs(30);

#[derive(Default)]
struct FamilyTotals {
    scenarios: u64,
    decided: u64,
    unknown: u64,
    aig_inputs: u64,
    aig_nodes: u64,
    cnf_variables: u64,
    cnf_clauses: u64,
    bit_blast_ms: f64,
    cnf_encode_ms: f64,
    solve_ms: f64,
}

impl FamilyTotals {
    fn add(&mut self, layers: &BvLayerStats, decided: bool) {
        self.scenarios += 1;
        if decided {
            self.decided += 1;
        }
        self.aig_inputs += layers.aig_inputs;
        self.aig_nodes += layers.aig_nodes;
        self.cnf_variables += layers.cnf_variables;
        self.cnf_clauses += layers.cnf_clauses;
        self.bit_blast_ms += ms(layers.bit_blast);
        self.cnf_encode_ms += ms(layers.cnf_encode);
        self.solve_ms += ms(layers.solve);
    }
}

fn main() {
    let config = SolverConfig::new().with_timeout(TIMEOUT);

    println!(
        "{:<34} {:>6} {:>8} {:>8} {:>9} {:>8} {:>9}",
        "scenario", "status", "aig_in", "aig_nds", "cnf_vars", "clauses", "total_ms"
    );
    println!("{}", "-".repeat(86));

    let mut totals: Vec<(Family, FamilyTotals)> = vec![
        (Family::Mixing, FamilyTotals::default()),
        (Family::Machine, FamilyTotals::default()),
        (Family::Identity, FamilyTotals::default()),
        (Family::Arithmetic, FamilyTotals::default()),
    ];

    for scenario in catalog() {
        let (status, layers, decided) = run(&scenario, &config);
        if let Some(layers) = layers {
            println!(
                "{:<34} {:>6} {:>8} {:>8} {:>9} {:>8} {:>9.2}",
                truncate(&scenario.name, 34),
                status,
                layers.aig_inputs,
                layers.aig_nodes,
                layers.cnf_variables,
                layers.cnf_clauses,
                ms(layers.total()),
            );
            let entry = totals
                .iter_mut()
                .find(|(family, _)| *family == scenario.family)
                .expect("every family has a totals bucket");
            entry.1.add(&layers, decided);
            if !decided {
                entry.1.unknown += 1;
            }
        } else {
            println!(
                "{:<34} {:>6} (no pipeline stats)",
                truncate(&scenario.name, 34),
                status
            );
        }
    }

    println!();
    println!(
        "{:<12} {:>6} {:>8} {:>9} {:>9} {:>9} {:>9} {:>9}",
        "family", "n", "decided", "aig_nds", "cnf_vars", "clauses", "enc_ms", "solve_ms"
    );
    println!("{}", "-".repeat(82));
    for (family, total) in &totals {
        if total.scenarios == 0 {
            continue;
        }
        let n = total.scenarios;
        println!(
            "{:<12} {:>6} {:>8} {:>9} {:>9} {:>9} {:>9.2} {:>9.2}",
            family.slug(),
            n,
            total.decided,
            mean_u64(total.aig_nodes, n),
            mean_u64(total.cnf_variables, n),
            mean_u64(total.cnf_clauses, n),
            (total.bit_blast_ms + total.cnf_encode_ms) / count_f64(n),
            total.solve_ms / count_f64(n),
        );
    }
}

fn run(scenario: &Scenario, config: &SolverConfig) -> (&'static str, Option<BvLayerStats>, bool) {
    let mut backend = SatBvBackend::new();
    let result = backend.check_query(&scenario.arena, &scenario.query, config);
    let layers = backend
        .last_stats()
        .and_then(BvLayerStats::from_solve_stats);
    match result {
        Ok(CheckResult::Sat(_)) => {
            let decided = matches!(scenario.expectation, Expectation::Sat { .. });
            (if decided { "sat" } else { "SAT!" }, layers, decided)
        }
        Ok(CheckResult::Unsat) => {
            let decided = matches!(scenario.expectation, Expectation::Unsat { .. });
            (if decided { "unsat" } else { "UNS!" }, layers, decided)
        }
        Ok(CheckResult::Unknown(_)) => ("unkwn", layers, false),
        Err(_) => ("err", layers, false),
    }
}

fn ms(duration: Duration) -> f64 {
    duration.as_secs_f64() * 1000.0
}

fn mean_u64(sum: u64, count: u64) -> u64 {
    sum.checked_div(count).unwrap_or(0)
}

#[allow(clippy::cast_precision_loss)]
fn count_f64(count: u64) -> f64 {
    count as f64
}

fn truncate(text: &str, width: usize) -> String {
    if text.len() <= width {
        text.to_owned()
    } else {
        format!("{}…", &text[..width.saturating_sub(1)])
    }
}
