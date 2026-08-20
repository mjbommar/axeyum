//! Exact raw-population Haar refinement triangle at the Lemire endpoints.

use axeyum_cas::gf2_hayes::{
    HayesLimits, carlitz_connected_top_geometry, class_population_distribution,
    population_refinement_connected_top_implication, population_refinement_envelope_implication,
};

const DEFAULT_ELL: usize = 12;
const MAX_ELL: usize = 20;
const MAX_PROJECTION_CELLS: usize = 2 * MAX_ELL * (1 << MAX_ELL);

fn main() {
    if let Err(error) = run() {
        eprintln!("GF2_HAYES_REFINEMENT|status=FAIL|error={error}");
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
            "usage: axeyum-gf2-hayes-refinement [ell: 1..={MAX_ELL}]"
        ));
    }

    for degree in [2 * ell + 1, 2 * ell + 2] {
        let distribution = class_population_distribution(ell, degree, HayesLimits::default())
            .map_err(|error| error.to_string())?;
        let report = distribution
            .population_refinement_triangle(MAX_PROJECTION_CELLS)
            .map_err(|error| error.to_string())?;
        let implication = population_refinement_envelope_implication(ell, degree)
            .map_err(|error| error.to_string())?;
        let connected_implication = population_refinement_connected_top_implication(ell, degree)
            .map_err(|error| error.to_string())?;
        let geometry =
            carlitz_connected_top_geometry(ell, degree).map_err(|error| error.to_string())?;
        let maxima = report
            .levels
            .iter()
            .map(|level| {
                format!(
                    "{}:{}:{}",
                    level.level, level.witness_parent, level.maximum_sibling_difference
                )
            })
            .collect::<Vec<_>>()
            .join(",");
        println!(
            "GF2_HAYES_REFINEMENT|status=PASS|ell={ell}|degree={degree}|candidate_holds={}|square_root_fibre_envelope_holds={}|envelope_implication_holds={}|connected_top_candidate_holds={}|connected_top_implication_holds={}|triangle_numerator={}|identity_path_triangle_numerator={}|envelope_triangle_numerator={}|connected_top_first_level={}|connected_top_signed_numerator={}|connected_top_candidate_numerator={}|connected_low_weil_numerator={}|connected_top_individual_weil_numerator={}|connected_top_required_saving_ceiling={}|carlitz_coarse_conductor_exponent={}|carlitz_artin_schreier_step_count={}|carlitz_relative_h1_dimension={}|target_numerator={}|actual_maximum_absolute_deviation={}|level_parent_maxima={maxima}",
            report.proves_candidate_discrepancy_bound(),
            report.satisfies_square_root_fibre_envelope(),
            implication.proves_candidate_discrepancy_bound(),
            report.satisfies_connected_top_candidate(),
            connected_implication.proves_candidate_discrepancy_bound(),
            report.triangle_numerator,
            report.identity_path_triangle_numerator,
            implication.envelope_triangle_numerator,
            report.connected_top_first_level,
            report.connected_top_signed_numerator,
            report.connected_top_candidate_numerator,
            connected_implication.low_weil_triangle_numerator,
            connected_implication.connected_top_individual_weil_numerator,
            connected_implication.connected_top_required_saving_ceiling,
            geometry.coarse_conductor_exponent,
            geometry.artin_schreier_step_count,
            geometry.relative_first_cohomology_dimension,
            report.candidate_target_numerator,
            report.actual_maximum_absolute_deviation,
        );
    }
    Ok(())
}
