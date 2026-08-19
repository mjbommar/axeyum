//! Exact second-moment diagnostic for the Lemire/Hayes conductor families.

use axeyum_cas::gf2_hayes::{HayesLimits, exact_conductor_second_moment};

const DEFAULT_ELL: usize = 12;
const MAX_ELL: usize = 16;

fn main() {
    if let Err(error) = run() {
        eprintln!("GF2_HAYES_MOMENTS|status=FAIL|error={error}");
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
            "usage: axeyum-gf2-hayes-moments [ell: 1..={MAX_ELL}]"
        ));
    }

    let limits = HayesLimits::default();
    for degree in [2 * ell + 1, 2 * ell + 2] {
        let mut rows = Vec::with_capacity(ell);
        let mut candidate = true;
        for level in 1..=ell {
            let moment = exact_conductor_second_moment(level, degree, limits)
                .map_err(|error| error.to_string())?;
            candidate &= moment.proves_square_root_layer_bound();
            rows.push(format!("{}:{}", level, moment.value));
        }
        println!(
            "GF2_HAYES_MOMENTS|status=PASS|ell={ell}|degree={degree}|exact=two_ntt_primes_plus_crt|all_second_moments_meet_cauchy_threshold={candidate}|moments={}",
            rows.join(",")
        );
    }
    Ok(())
}
