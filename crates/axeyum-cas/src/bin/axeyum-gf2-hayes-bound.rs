//! Exact arithmetic checker for the Lemire/Hayes sufficient conductor bound.

use axeyum_cas::gf2_hayes::{ConductorBoundAssumption, check_conductor_bound_sufficiency};

fn main() {
    let assumption = ConductorBoundAssumption::default();
    match check_conductor_bound_sufficiency(assumption) {
        Ok(report) => println!(
            "GF2_HAYES_SUFFICIENT_RUST|status=PASS|conductor_bound={}*j^{}*2^((n+j)/2)|ell>={}|endpoint_abs_discrepancy_le_2powell=true|proper_divisor_margin=true|finite_remainder_degrees=1..{}|first_symbolic_degrees={},{}",
            assumption.constant,
            assumption.power,
            assumption.threshold,
            assumption.finite_max_degree,
            report.first_odd_degree,
            report.first_even_degree
        ),
        Err(error) => {
            eprintln!("GF2_HAYES_SUFFICIENT_RUST|status=FAIL|error={error}");
            std::process::exit(1);
        }
    }
}
