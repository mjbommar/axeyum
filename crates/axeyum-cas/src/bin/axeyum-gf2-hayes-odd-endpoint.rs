//! Compute one exact odd Hayes endpoint with a single admitted NTT prime.

use axeyum_cas::gf2_hayes::{HayesLimits, odd_endpoint_two_adic_report};

const MAX_ELL: usize = 27;

fn main() {
    if let Err(error) = run() {
        eprintln!("GF2_HAYES_ODD_ENDPOINT|status=FAIL|error={error}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), Box<dyn std::error::Error>> {
    let mut arguments = std::env::args().skip(1);
    let ell = arguments
        .next()
        .ok_or("usage: axeyum-gf2-hayes-odd-endpoint <ell: 1..=27>")?
        .parse::<usize>()?;
    if arguments.next().is_some() || !(1..=MAX_ELL).contains(&ell) {
        return Err("usage: axeyum-gf2-hayes-odd-endpoint <ell: 1..=27>".into());
    }
    let degree = 2 * ell + 1;
    let group_order = 1_usize << ell;
    let limits = HayesLimits {
        max_ell: ell,
        max_degree: degree,
        max_group_order: group_order,
        max_table_cells: (ell + degree + 1) * group_order,
    };
    let started = std::time::Instant::now();
    let report = odd_endpoint_two_adic_report(ell, limits)?;
    let main_term = 1_i128 << (degree - ell);
    let discrepancy = i128::try_from(report.mangoldt_population)? - main_term;
    println!(
        "GF2_HAYES_ODD_ENDPOINT|status=PASS|ell={ell}|degree={degree}|count={}|discrepancy={discrepancy}|irreducibles={}|irreducibles_mod_8={}|irreducibles_mod_16={}|irreducibles_v2={}|carlitz_2_rank={}|curve_point_precision_bits={}|exact=single_ntt_prime_plus_odd_endpoint_bound|elapsed_seconds={:.3}",
        report.mangoldt_population,
        report.irreducible_count,
        report.irreducible_residue_mod_8,
        report.irreducible_residue_mod_16,
        report
            .irreducible_two_adic_valuation
            .map_or_else(|| "infinity".to_owned(), |value| value.to_string()),
        report.carlitz_two_rank,
        report.required_curve_point_modulus_bits,
        started.elapsed().as_secs_f64(),
    );
    Ok(())
}
