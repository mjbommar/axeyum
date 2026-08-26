//! AC-Bridge resurrection audit: `ell`-scaling of refuted phase-erasing
//! shortcuts, measured against the weak sufficient target `M_4<2^(4(n-ell))`.
//!
//! Read-only diagnostic. Every retained quantity is an exact integer; the
//! only floating point is in the printed ratios, which are diagnostics and
//! never a certificate. Finite computation is evidence, never a theorem.
//!
//! Usage: `acb_ra_scaling <probe> <ell-min> <ell-max>` where `<probe>` is one
//! of `core`, `cauchy`, `regroup`, `cumulant`, `fomenko`, `cylinder`,
//! `triangle`, `efron`.

use axeyum_cas::gf2_hayes::{
    HayesLimits, class_population_distribution, connected_order_cumulant_report,
    connected_top_inverse_mobius_fourier_regroup, connected_top_second_moment_cauchy,
    hayes_fomenko_restriction_packet_report,
};
use num_bigint::BigInt;
use num_traits::Signed;

fn limits(ell: usize, degree: usize) -> HayesLimits {
    HayesLimits {
        max_ell: ell.max(24),
        max_degree: degree.max(60),
        max_group_order: 1 << 24,
        max_table_cells: 1_600_000_000,
    }
}

fn endpoints(ell: usize) -> [usize; 2] {
    [2 * ell + 1, 2 * ell + 2]
}

#[allow(clippy::too_many_lines)]
fn main() -> Result<(), String> {
    let args: Vec<String> = std::env::args().skip(1).collect();
    if args.len() != 3 {
        return Err("usage: acb_ra_scaling <probe> <ell-min> <ell-max>".to_owned());
    }
    let probe = args[0].clone();
    let lo: usize = args[1].parse().map_err(|_| "bad ell-min".to_owned())?;
    let hi: usize = args[2].parse().map_err(|_| "bad ell-max".to_owned())?;

    for ell in lo..=hi {
        for degree in endpoints(ell) {
            let lim = limits(ell, degree);
            match probe.as_str() {
                "core" | "cylinder" | "triangle" | "efron" => {
                    let dist = match class_population_distribution(ell, degree, lim) {
                        Ok(value) => value,
                        Err(error) => {
                            println!(
                                "ACB_RA|probe={probe}|ell={ell}|n={degree}|declined={error:?}"
                            );
                            continue;
                        }
                    };
                    let mean = dist.uniform_mean().ok_or("no uniform mean")?;
                    let m2 = dist
                        .central_absolute_power_sum(2)
                        .map_err(|e| format!("{e:?}"))?;
                    let m4 = dist
                        .central_absolute_power_sum(4)
                        .map_err(|e| format!("{e:?}"))?;
                    let maxabs = dist.maximum_absolute_deviation().ok_or("no max")?;
                    match probe.as_str() {
                        "core" => {
                            println!(
                                "ACB_RA|probe=core|ell={ell}|n={degree}|mean={mean}|max_abs_d={maxabs}|m2={m2}|m4={m4}"
                            );
                        }
                        "cylinder" => {
                            let report = dist
                                .witt_cylinder_concentration(1_600_000_000)
                                .map_err(|e| format!("{e:?}"))?;
                            for level in &report.levels {
                                println!(
                                    "ACB_RA|probe=cylinder|ell={ell}|n={degree}|level={}|ratio_num={}|ratio_den={}|dom_num={}|dom_den={}",
                                    level.level,
                                    level.maximum_ratio_numerator,
                                    level.maximum_ratio_denominator,
                                    level.maximum_dominance_numerator,
                                    level.maximum_dominance_denominator
                                );
                            }
                        }
                        "triangle" => {
                            let report = dist
                                .population_refinement_triangle(1_600_000_000)
                                .map_err(|e| format!("{e:?}"))?;
                            for level in &report.levels {
                                println!(
                                    "ACB_RA|probe=triangle|ell={ell}|n={degree}|j={}|h_star={}",
                                    level.level, level.maximum_sibling_difference
                                );
                            }
                            println!(
                                "ACB_RA|probe=triangle_total|ell={ell}|n={degree}|triangle_num={}|target={}|actual_max={}|identity_path={}|top_first={}|top_signed={}|top_target={}",
                                report.triangle_numerator,
                                report.candidate_target_numerator,
                                report.actual_maximum_absolute_deviation,
                                report.identity_path_triangle_numerator,
                                report.connected_top_first_level,
                                report.connected_top_signed_numerator,
                                report.connected_top_candidate_numerator
                            );
                        }
                        "efron" => {
                            let report = dist
                                .efron_stein_spectral_weight_report(1_600_000_000)
                                .map_err(|e| format!("{e:?}"))?;
                            let factors: Vec<String> = report
                                .factor_weights
                                .iter()
                                .map(ToString::to_string)
                                .collect();
                            println!(
                                "ACB_RA|probe=efron|ell={ell}|n={degree}|factors={}|total={}",
                                factors.join(","),
                                report.total_spectral_second_moment
                            );
                            for row in &report.weights {
                                println!(
                                    "ACB_RA|probe=efron_w|ell={ell}|n={degree}|w={}|chars={}|mass={}",
                                    row.weight, row.character_count, row.spectral_second_moment
                                );
                            }
                        }
                        _ => unreachable!(),
                    }
                }
                "cauchy" => match connected_top_second_moment_cauchy(ell, degree, lim) {
                    Ok(report) => println!(
                        "ACB_RA|probe=cauchy|ell={ell}|n={degree}|first_top={}|chars={}|exact_m2={}|cauchy_sq={}|allow_sq={}|max_m2={}|saving={}",
                        report.first_top_level,
                        report.character_count,
                        report.exact_second_moment,
                        report.cauchy_bound_square,
                        report.connected_allowance_square,
                        report.maximum_second_moment_for_candidate,
                        report.required_second_moment_saving_ceiling
                    ),
                    Err(error) => {
                        println!("ACB_RA|probe=cauchy|ell={ell}|n={degree}|declined={error:?}");
                    }
                },
                "regroup" => match connected_top_inverse_mobius_fourier_regroup(ell, degree, lim) {
                    Ok(report) => println!(
                        "ACB_RA|probe=regroup|ell={ell}|n={degree}|first_top={}|support={}|trace={}|cellwise={}|orderwise={}|freqwise={}|layerwise={}|freq_sq={}|cauchy_sq={}|allow_sq={}|max_sq={}|saving={}",
                        report.first_top_level,
                        report.high_frequency_support_bound,
                        report.connected_trace,
                        report.cellwise_absolute_numerator,
                        report.orderwise_absolute_numerator,
                        report.frequencywise_absolute_numerator,
                        report.layerwise_absolute_numerator,
                        report.frequency_square_sum,
                        report.frequency_cauchy_bound_square,
                        report.connected_allowance_square,
                        report.maximum_frequency_square_sum_for_candidate,
                        report.required_frequency_square_sum_saving_ceiling
                    ),
                    Err(error) => {
                        println!("ACB_RA|probe=regroup|ell={ell}|n={degree}|declined={error:?}");
                    }
                },
                "cumulant" => match connected_order_cumulant_report(ell, degree, lim) {
                    Ok(report) => {
                        let mut absolute = BigInt::from(0);
                        let mut largest = BigInt::from(0);
                        let mut largest_cell = [0_usize; 4];
                        for cell in &report.cells {
                            let weighted = &cell.connected_numerator
                                * BigInt::from(cell.permutation_multiplicity);
                            absolute += weighted.abs();
                            if weighted.abs() > largest {
                                largest = weighted.abs();
                                largest_cell = cell.interval_degrees;
                            }
                        }
                        let mut pairing_signed = BigInt::from(0);
                        let mut pairing_absolute = BigInt::from(0);
                        let mut worst_num = BigInt::from(0);
                        let mut worst_den = BigInt::from(1);
                        let mut worst_cell = [0_usize; 4];
                        for cell in &report.cells {
                            let m = BigInt::from(cell.permutation_multiplicity);
                            pairing_signed += &m * &cell.pairing_sum;
                            pairing_absolute += &m * cell.pairing_sum.abs();
                            let den = cell.pairing_sum.abs();
                            if den > BigInt::from(0)
                                && &cell.connected_numerator.abs() * &worst_den > &worst_num * &den
                            {
                                worst_num = cell.connected_numerator.abs();
                                worst_den = den;
                                worst_cell = cell.interval_degrees;
                            }
                        }
                        println!(
                            "ACB_RA|probe=kappa|ell={ell}|n={degree}|pairing_signed={pairing_signed}|pairing_abs={pairing_absolute}|worst_num={worst_num}|worst_den={worst_den}|worst_cell={worst_cell:?}"
                        );
                        println!(
                            "ACB_RA|probe=cumulant|ell={ell}|n={degree}|cells={}|abs_total={absolute}|largest={largest}|largest_cell={largest_cell:?}|signed={}|direct={}",
                            report.cells.len(),
                            report.reconstructed_fourth_cumulant_numerator,
                            report.direct_fourth_cumulant_numerator
                        );
                    }
                    Err(error) => {
                        println!("ACB_RA|probe=cumulant|ell={ell}|n={degree}|declined={error:?}");
                    }
                },
                "fomenko" => {
                    // Literal t=1 and the connected-window t=ceil(log2 ell)+1,
                    // at the top exact-conductor level (= ell).
                    let window = (usize::BITS - (ell - 1).leading_zeros()) as usize + 1;
                    for restriction in [1_usize, window] {
                        if restriction >= ell {
                            continue;
                        }
                        match hayes_fomenko_restriction_packet_report(ell, restriction, degree, lim)
                        {
                            Ok(report) => println!(
                                "ACB_RA|probe=fomenko|ell={ell}|n={degree}|t={restriction}|packets={}|max_packet={}|allow={}|max_abs={}|abs_total={}|violations={}|coeff={}|signed={}|direct={}",
                                report.packet_count,
                                report.maximum_packet_size,
                                report.square_root_allowance,
                                report.maximum_absolute_packet_trace,
                                report.packetwise_absolute_trace,
                                report.square_root_violation_count,
                                report.required_square_root_coefficient,
                                report.reconstructed_conductor_trace,
                                report.direct_conductor_trace
                            ),
                            Err(error) => println!(
                                "ACB_RA|probe=fomenko|ell={ell}|n={degree}|t={restriction}|declined={error:?}"
                            ),
                        }
                    }
                }
                other => return Err(format!("unknown probe {other}")),
            }
        }
    }
    Ok(())
}
