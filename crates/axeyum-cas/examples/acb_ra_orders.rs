//! AC-Bridge resurrection audit, part two: the order-decomposition and
//! Galois-orbit shortcuts, re-measured across `ell`.
//!
//! Read-only diagnostic; exact integers only. Finite computation is
//! evidence, never a theorem.
//!
//! Usage: `acb_ra_orders <probe> <ell-min> <ell-max>` with `<probe>` in
//! `mobius`, `topmobius`, `orbit`.

use axeyum_cas::gf2_hayes::{
    HayesLimits, connected_top_mobius_convolution, hayes_galois_orbit_trace_report,
    identity_class_mobius_convolution,
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

fn main() -> Result<(), String> {
    let args: Vec<String> = std::env::args().skip(1).collect();
    if args.len() != 3 {
        return Err("usage: acb_ra_orders <probe> <ell-min> <ell-max>".to_owned());
    }
    let probe = args[0].clone();
    let lo: usize = args[1].parse().map_err(|_| "bad ell-min".to_owned())?;
    let hi: usize = args[2].parse().map_err(|_| "bad ell-max".to_owned())?;
    for ell in lo..=hi {
        for degree in [2 * ell + 1, 2 * ell + 2] {
            let lim = limits(ell, degree);
            match probe.as_str() {
                "mobius" => match identity_class_mobius_convolution(ell, degree, lim) {
                    Ok(report) => {
                        let absolute: i128 = report.terms.iter().map(|t| t.value.abs()).sum();
                        println!(
                            "ACB_RA|probe=mobius|ell={ell}|n={degree}|orders={}|abs_total={absolute}|signed={}|mean={}",
                            report.terms.len(),
                            report.discrepancy,
                            report.uniform_mean
                        );
                    }
                    Err(error) => {
                        println!("ACB_RA|probe=mobius|ell={ell}|n={degree}|declined={error:?}");
                    }
                },
                "topmobius" => match connected_top_mobius_convolution(ell, degree, lim) {
                    Ok(report) => println!(
                        "ACB_RA|probe=topmobius|ell={ell}|n={degree}|first_top={}|orders={}|nonzero={}|abs_total={}|signed={}",
                        report.first_top_level,
                        report.terms.len(),
                        report.nonzero_order_count,
                        report.orderwise_absolute_trace,
                        report.signed_connected_trace
                    ),
                    Err(error) => {
                        println!("ACB_RA|probe=topmobius|ell={ell}|n={degree}|declined={error:?}");
                    }
                },
                "orbit" => match hayes_galois_orbit_trace_report(ell, degree, lim) {
                    Ok(report) => {
                        let layer_absolute: BigInt = report
                            .orders
                            .iter()
                            .map(|row| BigInt::from(row.signed_trace_sum).abs())
                            .sum();
                        println!(
                            "ACB_RA|probe=orbit|ell={ell}|n={degree}|orbits={}|allow={}|max_orbit={}|violations={}|order_layers={}|max_layer={}|layer_allow={}|layer_violations={}|coeff={}|layer_abs={layer_absolute}|signed={}|direct={}",
                            report.orbit_count,
                            report.candidate_orbit_allowance,
                            report.maximum_absolute_orbit_trace,
                            report.candidate_violation_count,
                            report.orders.len(),
                            report.maximum_absolute_order_layer_trace,
                            report.order_layer_candidate_allowance,
                            report.order_layer_candidate_violation_count,
                            report.required_order_layer_coefficient,
                            report.reconstructed_conductor_trace,
                            report.direct_conductor_trace
                        );
                    }
                    Err(error) => {
                        println!("ACB_RA|probe=orbit|ell={ell}|n={degree}|declined={error:?}");
                    }
                },
                other => return Err(format!("unknown probe {other}")),
            }
        }
    }
    Ok(())
}
