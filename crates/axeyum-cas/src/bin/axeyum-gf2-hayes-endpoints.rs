//! Exact finite transform oracle for the two Lemire/Hayes endpoint degrees.
//!
//! The reusable bounded algebra lives in `axeyum_cas::gf2_hayes`. This CLI
//! retains committed finite controls and prints diagnostics; it does not turn
//! an observed bound into a universal theorem.

use axeyum_cas::gf2_hayes::{HayesLimits, conductor_layers, endpoint_discrepancies};

const DEFAULT_MAX_ELL: usize = 12;
const MAX_ELL: usize = 23;

const EXPECTED: &[(i128, i128)] = &[
    (0, 0),
    (-2, 0),
    (6, -8),
    (5, 12),
    (-19, 32),
    (-49, 32),
    (45, -40),
    (50, 75),
    (-92, 48),
    (53, 63),
    (206, -352),
    (359, 335),
    (-345, 980),
    (-896, 645),
    (340, -1832),
    (2744, 660),
    (-1988, 6587),
    (928, 9592),
    (4074, -13496),
    (3115, -4509),
    (-20938, 25007),
    (-7582, 28402),
    (57574, -88336),
];

fn main() {
    if let Err(error) = run() {
        eprintln!("GF2_HAYES_ENDPOINTS|status=FAIL|error={error}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), String> {
    let mut arguments = std::env::args().skip(1);
    let max_ell = match arguments.next() {
        Some(value) => value
            .parse::<usize>()
            .map_err(|_| "max ell must be an integer".to_owned())?,
        None => DEFAULT_MAX_ELL,
    };
    let print_layers = match arguments.next().as_deref() {
        Some("--conductor-layers") => true,
        Some(_) => return Err(usage()),
        None => false,
    };
    if arguments.next().is_some() || !(1..=MAX_ELL).contains(&max_ell) {
        return Err(usage());
    }

    let limits = HayesLimits::default();
    let mut rows = Vec::with_capacity(max_ell);
    for ell in 1..=max_ell {
        let row = endpoint_discrepancies(ell, limits).map_err(|error| error.to_string())?;
        if (row.odd, row.even) != EXPECTED[ell - 1] {
            return Err(format!(
                "ell={ell}: endpoint discrepancies ({}, {}) differ from the committed control {:?}",
                row.odd,
                row.even,
                EXPECTED[ell - 1]
            ));
        }
        rows.push(row);
    }

    let bound_holds = rows.iter().all(|row| row.satisfies_candidate_bound());
    let details = rows
        .iter()
        .map(|row| format!("{}:{}:{}", row.ell, row.odd, row.even))
        .collect::<Vec<_>>()
        .join(",");
    println!(
        "GF2_HAYES_ENDPOINTS|status=PASS|ell=1..{max_ell}|degrees=3..{}|exact=two_ntt_primes_plus_crt|candidate_abs_discrepancy_le_2powell={bound_holds}|discrepancies={details}",
        2 * max_ell + 2
    );
    if print_layers {
        for degree in [2 * max_ell + 1, 2 * max_ell + 2] {
            let layers =
                conductor_layers(max_ell, degree, limits).map_err(|error| error.to_string())?;
            let details = layers
                .iter()
                .map(|layer| format!("{}:{}", layer.level, layer.value))
                .collect::<Vec<_>>()
                .join(",");
            let all_observed_layers_satisfy_square_root_bound = layers
                .iter()
                .all(|layer| layer.satisfies_square_root_bound(degree));
            println!(
                "GF2_HAYES_CONDUCTORS|status=PASS|ell={max_ell}|degree={degree}|identity=fourier_exact_conductor_difference|all_observed_layers_satisfy_square_root_bound={all_observed_layers_satisfy_square_root_bound}|layers={details}"
            );
        }
    }
    Ok(())
}

fn usage() -> String {
    format!("usage: axeyum-gf2-hayes-endpoints [max-ell: 1..={MAX_ELL}] [--conductor-layers]")
}
