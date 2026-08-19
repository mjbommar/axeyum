//! Exact arithmetic checker for the Lemire/Hayes sufficient conductor bound.

use axeyum_cas::gf2_hayes::{
    ConductorBoundAssumption, SquareRootLayerBoundAssumption, check_conductor_bound_sufficiency,
    check_square_root_layer_bound_sufficiency,
};

fn main() {
    if let Err(error) = run() {
        eprintln!("GF2_HAYES_SUFFICIENT_RUST|status=FAIL|error={error}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), Box<dyn std::error::Error>> {
    let assumption = ConductorBoundAssumption::default();
    let report = check_conductor_bound_sufficiency(assumption)?;
    println!(
        "GF2_HAYES_SUFFICIENT_RUST|status=PASS|conductor_bound={}*j^{}*2^((n+j)/2)|ell>={}|endpoint_abs_discrepancy_le_2powell=true|proper_divisor_margin=true|finite_remainder_degrees=1..{}|first_symbolic_degrees={},{}",
        assumption.constant,
        assumption.power,
        assumption.threshold,
        assumption.finite_max_degree,
        report.first_odd_degree,
        report.first_even_degree
    );

    let square_root = SquareRootLayerBoundAssumption::default();
    let square_root_report = check_square_root_layer_bound_sufficiency(square_root)?;
    println!(
        "GF2_HAYES_LAYER_SUFFICIENT_RUST|status=PASS|implication=checked|assumption_status=REFUTED|counterexample_level=5|counterexample_degree=45|counterexample_normalized_layer=7080448|layer_bound=T_j(n)^2<=2^(2j-2+n)|ell>={}|square_divisor_class_restriction=true|proper_divisor_margin=true|finite_remainder_degrees=1..{}|first_symbolic_degrees={},{}|sqrt2_upper={}/{}",
        square_root.threshold,
        square_root.finite_max_degree,
        square_root_report.first_odd_degree,
        square_root_report.first_even_degree,
        square_root.sqrt_two_upper_numerator,
        square_root.sqrt_two_upper_denominator,
    );
    Ok(())
}
