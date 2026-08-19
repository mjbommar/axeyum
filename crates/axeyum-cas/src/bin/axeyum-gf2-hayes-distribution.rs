//! Exact full-class endpoint diagnostics for the Lemire/Hayes problem.

use axeyum_cas::gf2_hayes::{HayesLimits, class_population_distribution};

const DEFAULT_ELL: usize = 12;
const MAX_ELL: usize = 23;

fn main() {
    if let Err(error) = run() {
        eprintln!("GF2_HAYES_DISTRIBUTION|status=FAIL|error={error}");
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
            "usage: axeyum-gf2-hayes-distribution [ell: 1..={MAX_ELL}]"
        ));
    }

    let limits = HayesLimits::default();
    for degree in [2 * ell + 1, 2 * ell + 2] {
        let distribution = class_population_distribution(ell, degree, limits)
            .map_err(|error| error.to_string())?;
        let mean = distribution
            .uniform_mean()
            .ok_or_else(|| "class distribution has no exact uniform mean".to_owned())?;
        let maximum_deviation = distribution
            .maximum_absolute_deviation()
            .ok_or_else(|| "class distribution is empty".to_owned())?;
        let minimum = distribution
            .counts
            .iter()
            .copied()
            .min()
            .ok_or_else(|| "class distribution is empty".to_owned())?;
        let maximum = distribution
            .counts
            .iter()
            .copied()
            .max()
            .ok_or_else(|| "class distribution is empty".to_owned())?;
        let central_absolute_power_sums = [2_u32, 4, 6, 8]
            .into_iter()
            .map(|power| {
                distribution
                    .central_absolute_power_sum(power)
                    .map(|value| format!("{power}:{value}"))
            })
            .collect::<Result<Vec<_>, _>>()
            .map_err(|error| error.to_string())?
            .join(",");
        let fourth_moment_candidate_bound = distribution
            .fourth_moment_candidate_bound()
            .map_err(|error| error.to_string())?;
        let fourth_moment_candidate_holds = distribution
            .satisfies_fourth_moment_candidate()
            .map_err(|error| error.to_string())?;
        let fourth_moment_proves_candidate_discrepancy_bound = distribution
            .fourth_moment_proves_candidate_discrepancy_bound()
            .map_err(|error| error.to_string())?;
        let fourth_cumulant_numerator = distribution
            .fourth_cumulant_numerator()
            .map_err(|error| error.to_string())?;
        println!(
            "GF2_HAYES_DISTRIBUTION|status=PASS|ell={ell}|degree={degree}|exact=two_ntt_primes_plus_crt|classes={}|uniform_mean={mean}|minimum={minimum}|maximum={maximum}|maximum_absolute_deviation={maximum_deviation}|all_classes_positive={}|central_absolute_power_sums={central_absolute_power_sums}|fourth_cumulant_numerator={fourth_cumulant_numerator}|fourth_moment_candidate_bound={fourth_moment_candidate_bound}|fourth_moment_candidate_holds={fourth_moment_candidate_holds}|fourth_moment_proves_candidate_discrepancy_bound={fourth_moment_proves_candidate_discrepancy_bound}",
            distribution.counts.len(),
            distribution.all_classes_positive(),
        );
    }
    Ok(())
}
