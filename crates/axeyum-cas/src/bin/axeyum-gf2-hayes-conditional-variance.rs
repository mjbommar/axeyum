//! Exact identity-cylinder conditional-variance diagnostic for `(REL)`.

use axeyum_cas::gf2_hayes::{HayesLimits, identity_cylinder_conditional_variance};

const DEFAULT_ELL: usize = 18;
const MAX_ELL: usize = 23;

fn main() {
    if let Err(error) = run() {
        eprintln!("GF2_HAYES_CONDITIONAL_VARIANCE|status=FAIL|error={error}");
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
    if arguments.next().is_some() || !(4..=MAX_ELL).contains(&ell) {
        return Err(format!(
            "usage: axeyum-gf2-hayes-conditional-variance [ell: 4..={MAX_ELL}]"
        ));
    }

    for degree in [2 * ell + 1, 2 * ell + 2] {
        let report = identity_cylinder_conditional_variance(ell, degree, HayesLimits::default())
            .map_err(|error| error.to_string())?;
        println!(
            "GF2_HAYES_CONDITIONAL_VARIANCE|status=PASS|ell={ell}|degree={degree}|coarse_level={}|descendant_count={}|identity_population={}|coarse_identity_population={}|identity_scaled_deviation={}|connected_trace={}|conditional_scaled_square_sum={}|conditional_variance_numerator={}|quarter_scale_variance_target_numerator={}|maximum_conditional_scaled_square_sum_for_rel={}|conditional_cauchy_proves_rel={}|quarter_scale_variance_holds={}|rel_holds_exactly={}|exact_global_required_saving_ceiling={}|proved_weil_required_saving_ceiling={}|negative_allowance={}",
            report.coarse_level,
            report.descendant_count,
            report.identity_population,
            report.coarse_identity_population,
            report.identity_scaled_deviation,
            report.connected_trace,
            report.conditional_scaled_square_sum,
            report.conditional_variance_numerator,
            report.quarter_scale_variance_target_numerator,
            report.maximum_conditional_scaled_square_sum_for_rel,
            report.conditional_cauchy_proves_rel(),
            report.satisfies_quarter_scale_variance(),
            report.rel_holds_exactly(),
            report.exact_global_required_saving_ceiling,
            report.proved_weil_required_saving_ceiling,
            report.negative_allowance_numerator,
        );
        for level in &report.variance_levels {
            println!(
                "GF2_HAYES_CONDITIONAL_VARIANCE_LEVEL|status=PASS|ell={ell}|degree={degree}|level={}|parent_count={}|sibling_difference_square_sum={}|global_sibling_difference_square_sum={}|global_sibling_difference_fourth_sum={}|identity_share_at_most_uniform={}|identity_localization_multiplier_ceiling={}|identity_share_within_linear_carleson={}|weak_kurtosis_implies_polynomial_share={}|conditional_variance_numerator_contribution={}",
                level.level,
                level.parent_count,
                level.sibling_difference_square_sum,
                level.global_sibling_difference_square_sum,
                level.global_sibling_difference_fourth_sum,
                level.identity_share_at_most_uniform,
                level.identity_localization_multiplier_ceiling,
                level.identity_share_within_linear_carleson,
                level.weak_kurtosis_implies_polynomial_share,
                level.conditional_variance_numerator_contribution,
            );
        }
    }
    Ok(())
}
