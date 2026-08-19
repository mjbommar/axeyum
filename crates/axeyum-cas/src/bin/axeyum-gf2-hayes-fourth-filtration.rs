//! Exact conductor filtration of the Lemire/Hayes fourth-moment diagnostic.

use axeyum_cas::gf2_hayes::{HayesLimits, class_population_distribution};

const DEFAULT_ELL: usize = 12;
const MAX_ELL: usize = 20;
const MAX_PROJECTION_CELLS: usize = MAX_ELL * (1 << MAX_ELL);

fn main() {
    if let Err(error) = run() {
        eprintln!("GF2_HAYES_FOURTH_FILTRATION|status=FAIL|error={error}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), String> {
    let mut arguments = std::env::args().skip(1);
    let ell = match arguments.next() {
        Some(value) => value
            .parse::<usize>()
            .map_err(|_| "ell must be an integer".to_owned())?,
        None => DEFAULT_ELL,
    };
    if arguments.next().is_some() || !(1..=MAX_ELL).contains(&ell) {
        return Err(format!(
            "usage: axeyum-gf2-hayes-fourth-filtration [ell: 1..={MAX_ELL}]"
        ));
    }

    for degree in [2 * ell + 1, 2 * ell + 2] {
        let distribution = class_population_distribution(ell, degree, HayesLimits::default())
            .map_err(|error| error.to_string())?;
        let decomposition = distribution
            .fourth_moment_conductor_decomposition(MAX_PROJECTION_CELLS)
            .map_err(|error| error.to_string())?;
        let exact_energy = decomposition
            .levels
            .iter()
            .map(|level| format!("{}:{}", level.level, level.exact_fourier_energy))
            .collect::<Vec<_>>()
            .join(",");
        println!(
            "GF2_HAYES_FOURTH_FILTRATION|status=PASS|ell={ell}|degree={degree}|second_moment={}|fourth_moment={}|exact_conductor_energy={exact_energy}",
            decomposition.second_moment, decomposition.fourth_moment
        );
    }
    Ok(())
}
