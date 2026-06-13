//! Scaling profile of the `sat-bv` pipeline over a realistic workload.
//!
//! This example sweeps the round count of the `mixing` keyed-function inversion
//! family at a few widths and reports how AIG/CNF size and solve time grow. It
//! closes the consumer-models loop: a self-checking, oracle-free workload is
//! scaled toward the frontier so the next optimization can target the stage
//! that actually grows, with ground truth that never depends on Z3.
//!
//! Run with:
//!
//! ```sh
//! cargo run -p axeyum-bench --example scenario_scaling
//! ```

use std::time::Duration;

use axeyum_scenarios::mixing_inversion;
use axeyum_solver::{BvLayerStats, CheckResult, SatBvBackend, SolverBackend, SolverConfig};

const TIMEOUT: Duration = Duration::from_secs(60);
const WIDTHS: [u32; 3] = [16, 32, 64];
const ROUNDS: [usize; 6] = [2, 4, 8, 16, 32, 64];

fn main() {
    let config = SolverConfig::new().with_timeout(TIMEOUT);

    println!(
        "{:>5} {:>6} {:>8} {:>9} {:>9} {:>8} {:>9} {:>10}",
        "width", "rounds", "aig_nds", "cnf_vars", "clauses", "dens", "solve_ms", "status"
    );
    println!("{}", "-".repeat(72));

    for width in WIDTHS {
        for rounds in ROUNDS {
            let scenario = mixing_inversion(width, rounds, 0x00C0_FFEE ^ u64::from(width));
            // Trust the workload before trusting any measurement from it.
            scenario
                .self_check()
                .expect("scaling scenario must self-check");

            let mut backend = SatBvBackend::new();
            let result = backend.check_query(&scenario.arena, &scenario.query, &config);
            let layers = backend
                .last_stats()
                .and_then(BvLayerStats::from_solve_stats);

            let status = match &result {
                Ok(CheckResult::Sat(_)) => "sat",
                Ok(CheckResult::Unsat) => "UNSAT!",
                Ok(CheckResult::Unknown(_)) => "unknown",
                Err(_) => "error",
            };

            if let Some(layers) = layers {
                println!(
                    "{:>5} {:>6} {:>8} {:>9} {:>9} {:>8.2} {:>9.2} {:>10}",
                    width,
                    rounds,
                    layers.aig_nodes,
                    layers.cnf_variables,
                    layers.cnf_clauses,
                    layers.clause_density(),
                    ms(layers.solve),
                    status,
                );
            } else {
                println!("{:>5} {:>6} {:>61}", width, rounds, "(no pipeline stats)");
            }
        }
        println!();
    }
}

fn ms(duration: Duration) -> f64 {
    duration.as_secs_f64() * 1000.0
}
