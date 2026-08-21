//! Exact Galois/order-layer Hayes trace audit for one endpoint row.
//!
//! This runner is intentionally bounded to level 24.  It tests the explicit
//! polynomial envelope `max_s |T_(j,s)(n)| <= j^2 (j-1) 2^ceil(n/2)` after
//! summing every cyclotomic Galois orbit of exact character order `2^s`.
//! Passing rows are finite evidence only; the runner never upgrades the
//! envelope to a universal theorem.

use axeyum_cas::gf2_hayes::{
    HayesLimits, hayes_exact_order_spatial_trace_report, hayes_galois_orbit_trace_report,
};

const MAX_LEVEL: usize = 24;

fn main() {
    if let Err(error) = run() {
        eprintln!("GF2_HAYES_GALOIS_ORBITS|status=FAIL|error={error}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), Box<dyn std::error::Error>> {
    let mut arguments = std::env::args().skip(1);
    let level = arguments
        .next()
        .ok_or("usage: axeyum-gf2-hayes-galois-orbits <level: 2..=24> <odd|even>")?
        .parse::<usize>()?;
    let parity = arguments
        .next()
        .ok_or("usage: axeyum-gf2-hayes-galois-orbits <level: 2..=24> <odd|even>")?;
    if arguments.next().is_some() || !(2..=MAX_LEVEL).contains(&level) {
        return Err("usage: axeyum-gf2-hayes-galois-orbits <level: 2..=24> <odd|even>".into());
    }
    let degree = match parity.as_str() {
        "odd" => 2 * level + 1,
        "even" => 2 * level + 2,
        _ => {
            return Err("usage: axeyum-gf2-hayes-galois-orbits <level: 2..=24> <odd|even>".into());
        }
    };
    let group_order = 1_usize << level;
    let limits = HayesLimits {
        max_ell: level,
        max_degree: degree,
        max_group_order: group_order,
        max_table_cells: (degree + level + 1)
            .checked_mul(group_order)
            .ok_or("table-cell admission overflow")?,
    };
    let started = std::time::Instant::now();
    let report = hayes_galois_orbit_trace_report(level, degree, limits)?;
    let spatial = hayes_exact_order_spatial_trace_report(level, degree, limits)?;
    let orbit_layers = report
        .orders
        .iter()
        .map(|row| (row.character_order, row.signed_trace_sum))
        .collect::<Vec<_>>();
    let spatial_layers = spatial
        .orders
        .iter()
        .map(|row| (row.character_order, row.signed_trace_sum))
        .collect::<Vec<_>>();
    if orbit_layers != spatial_layers {
        return Err("cyclotomic and spatial exact-order layers disagree".into());
    }
    let polynomial_coefficient = (level as u128) * (level as u128);
    let candidate_holds = report.required_order_layer_coefficient <= polynomial_coefficient;
    println!(
        "GF2_HAYES_GALOIS_ORBITS|status=PASS|level={level}|degree={degree}|parity={parity}|primitive_characters={}|galois_orbits={}|order_layers={}|required_coefficient={}|candidate_coefficient={polynomial_coefficient}|candidate_holds={candidate_holds}|conductor_trace={}|elapsed_seconds={:.3}",
        report.primitive_character_count,
        report.orbit_count,
        report.orders.len(),
        report.required_order_layer_coefficient,
        report.direct_conductor_trace,
        started.elapsed().as_secs_f64(),
    );
    for row in report.orders {
        println!(
            "GF2_HAYES_GALOIS_ORDER|level={level}|degree={degree}|character_order={}|orbit_count={}|maximum_absolute_orbit_trace={}|signed_trace_sum={}",
            row.character_order, row.orbit_count, row.maximum_absolute_trace, row.signed_trace_sum,
        );
    }
    for row in spatial.orders {
        println!(
            "GF2_HAYES_ORDER_SPATIAL|level={level}|degree={degree}|character_order={}|exact_characters={}|full_cumulative_characters={}|lower_cumulative_characters={}|full_power_population={}|lower_power_population={}|new_coefficient_forced_zero={}|coefficient_imbalance={}|cumulative_conductor_trace={}|signed_trace_sum={}",
            row.character_order,
            row.exact_character_count,
            row.full_cumulative_character_count,
            row.lower_cumulative_character_count,
            row.full_power_subgroup_population,
            row.lower_power_subgroup_population,
            row.new_coefficient_forced_zero,
            row.coefficient_imbalance,
            row.cumulative_conductor_trace,
            row.signed_trace_sum,
        );
    }
    if !candidate_holds {
        return Err("polynomial exact-order envelope is refuted".into());
    }
    Ok(())
}
