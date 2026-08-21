//! Exact identity-cylinder conditional-variance diagnostic for `(REL)`.

use axeyum_cas::gf2_hayes::{
    HayesLimits, IdentityCylinderAggregatePathImplication,
    IdentityCylinderConditionalVarianceReport, identity_cylinder_aggregate_path_implication,
    identity_cylinder_conditional_variance, identity_cylinder_path_split_implication,
    identity_cylinder_translation_split_implication,
};

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
        let split = identity_cylinder_path_split_implication(ell, degree)
            .map_err(|error| error.to_string())?;
        let translation = identity_cylinder_translation_split_implication(ell, degree)
            .map_err(|error| error.to_string())?;
        let aggregate = identity_cylinder_aggregate_path_implication(ell, degree)
            .map_err(|error| error.to_string())?;
        let report = identity_cylinder_conditional_variance(ell, degree, HayesLimits::default())
            .map_err(|error| error.to_string())?;
        println!(
            "GF2_HAYES_CONDITIONAL_VARIANCE|status=PASS|ell={ell}|degree={degree}|coarse_level={}|descendant_count={}|identity_population={}|coarse_identity_population={}|identity_scaled_deviation={}|connected_trace={}|conditional_scaled_square_sum={}|conditional_variance_numerator={}|quarter_scale_variance_target_numerator={}|maximum_conditional_scaled_square_sum_for_rel={}|conditional_cauchy_proves_rel={}|quarter_scale_variance_holds={}|rel_holds_exactly={}|exact_global_required_saving_ceiling={}|proved_weil_required_saving_ceiling={}|negative_allowance={}|required_half_balanced_steps={}|required_three_quarter_balanced_steps={}|half_balanced_depth_available={}|three_quarter_depth_available={}|translation_split_level={}|translation_split_within_path={}|residual_half_balanced_steps={}|residual_three_quarter_balanced_steps={}",
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
            split.required_half_balanced_steps,
            split.required_three_quarter_balanced_steps,
            split.half_balanced_depth_available,
            split.three_quarter_depth_available,
            translation.first_odd_binomial_index,
            translation.forced_split_within_identity_path,
            translation.residual_half_balanced_steps,
            translation.residual_three_quarter_balanced_steps,
        );
        print_aggregate_path(ell, degree, &aggregate, &report);
        for level in &report.variance_levels {
            println!(
                "GF2_HAYES_CONDITIONAL_VARIANCE_LEVEL|status=PASS|ell={ell}|degree={degree}|level={}|parent_count={}|sibling_difference_square_sum={}|global_sibling_difference_square_sum={}|global_sibling_difference_fourth_sum={}|identity_share_at_most_uniform={}|identity_localization_multiplier_ceiling={}|identity_share_within_linear_carleson={}|weak_kurtosis_implies_polynomial_share={}|half_balanced_identity_path_steps={}|three_quarter_balanced_identity_path_steps={}|half_balanced_path_implies_polynomial_share={}|three_quarter_path_implies_polynomial_share={}|conditional_variance_numerator_contribution={}",
                level.level,
                level.parent_count,
                level.sibling_difference_square_sum,
                level.global_sibling_difference_square_sum,
                level.global_sibling_difference_fourth_sum,
                level.identity_share_at_most_uniform,
                level.identity_localization_multiplier_ceiling,
                level.identity_share_within_linear_carleson,
                level.weak_kurtosis_implies_polynomial_share,
                level.identity_path_balance.half_balanced_steps,
                level.identity_path_balance.three_quarter_balanced_steps,
                level
                    .identity_path_balance
                    .half_balanced_implies_polynomial_share,
                level
                    .identity_path_balance
                    .three_quarter_implies_polynomial_share,
                level.conditional_variance_numerator_contribution,
            );
            for step in &level.identity_energy_path {
                println!(
                    "GF2_HAYES_CONDITIONAL_VARIANCE_PATH|status=PASS|ell={ell}|degree={degree}|level={}|coarse_level={}|identity_square_mass={}|parent_identity_square_mass={}|signed_fourier_layer_sum={}|at_most_one_half={}|at_most_three_quarters={}",
                    level.level,
                    step.coarse_level,
                    step.identity_square_mass,
                    step.parent_identity_square_mass,
                    step.signed_fourier_layer_sum,
                    step.at_most_one_half,
                    step.at_most_three_quarters,
                );
            }
        }
    }
    Ok(())
}

fn print_aggregate_path(
    ell: usize,
    degree: usize,
    aggregate: &IdentityCylinderAggregatePathImplication,
    report: &IdentityCylinderConditionalVarianceReport,
) {
    println!(
        "GF2_HAYES_CONDITIONAL_VARIANCE_AGGREGATE|status=PASS|ell={ell}|degree={degree}|coarse_level={}|global_weil_envelope={}|maximum_terminal_mass_for_rel={}|required_half_balanced_steps={}|required_three_quarter_balanced_steps={}|translation_split_level={}|translation_split_within_path={}|residual_half_balanced_steps={}|residual_three_quarter_balanced_steps={}|observed_half_balanced_steps={}|observed_three_quarter_balanced_steps={}|half_balanced_path_implies_rel={}|three_quarter_path_implies_rel={}",
        aggregate.coarse_level,
        aggregate.aggregate_global_weil_envelope,
        aggregate.maximum_aggregate_terminal_mass_for_rel,
        aggregate.required_half_balanced_steps,
        aggregate.required_three_quarter_balanced_steps,
        aggregate.translation_split_level,
        aggregate.translation_split_within_path,
        aggregate.residual_half_balanced_steps,
        aggregate.residual_three_quarter_balanced_steps,
        report.aggregate_identity_path_balance.half_balanced_steps,
        report
            .aggregate_identity_path_balance
            .three_quarter_balanced_steps,
        report
            .aggregate_identity_path_balance
            .half_balanced_implies_rel,
        report
            .aggregate_identity_path_balance
            .three_quarter_balanced_implies_rel,
    );
    for step in &report.aggregate_identity_energy_path {
        println!(
            "GF2_HAYES_CONDITIONAL_VARIANCE_AGGREGATE_PATH|status=PASS|ell={ell}|degree={degree}|coarse_level={}|identity_square_mass={}|parent_identity_square_mass={}|signed_fourier_layer_sum={}|at_most_one_half={}|at_most_three_quarters={}",
            step.coarse_level,
            step.identity_square_mass,
            step.parent_identity_square_mass,
            step.signed_fourier_layer_sum,
            step.at_most_one_half,
            step.at_most_three_quarters,
        );
    }
}
