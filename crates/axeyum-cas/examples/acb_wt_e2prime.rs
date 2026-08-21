//! AC-Bridge workstream 04, task 4: the sweep-08 accumulator `(E2')`.
//!
//! With `c_F` the exact signed dyadic-character correlation of an affine
//! inverse-difference fibre `F`, `N_points` the total number of contributing
//! points, and `Delta = sum_F c_F`, the split proposed by the boolean-complexity
//! sweep is
//!
//! ```text
//! (E2')  sum_F c_F^2 <= N_points                (within-fibre off-diagonal
//!                                                correlation is nonpositive)
//! (E2)   sum_F c_F^2 <= 2^(k+d-1)
//! (S)    |Delta| <= C (sum_F c_F^2)^(1/2)
//! ```
//!
//! This example reports, per `(ell, k, d)` row, the exact integer second
//! moment, the point count, the `(E2')` ratio, the `(E2)` ratio, and the
//! observed `(S)` constant.  All values are exact integers from the CAS; only
//! the printed ratios are floating point.

use axeyum_cas::gf2_hayes::{HayesLimits, binary_dyadic_autocorrelation_fibre_report};
use num_bigint::BigUint;
use num_traits::ToPrimitive;

fn main() {
    if let Err(error) = run() {
        eprintln!("ACB_WT_E2PRIME|status=FAIL|error={error}");
        std::process::exit(1);
    }
}

fn emit_row(ell: usize, degree: usize, interval: usize, limits: HayesLimits) -> Result<(), String> {
    let report = binary_dyadic_autocorrelation_fibre_report(ell, degree, interval, limits)
        .map_err(|error| error.to_string())?;
    let square_sum = report.fibre_correlation_square_sum.clone();
    let points = BigUint::from(report.total_fibre_points);
    let off_diagonal = report.within_fibre_off_diagonal_correlation();
    let holds = report.satisfies_nonpositive_within_fibre_correlation();
    let e2_threshold = BigUint::from(1_u8) << (degree + interval - 1);
    let square_sum_f = square_sum.to_f64().unwrap_or(f64::NAN);
    let points_f = points.to_f64().unwrap_or(f64::NAN);
    let e2_threshold_f = e2_threshold.to_f64().unwrap_or(f64::NAN);
    let delta = report.off_diagonal_signed_correlation;
    #[allow(clippy::cast_precision_loss)]
    let sign_constant = (delta as f64).abs() / square_sum_f.sqrt();
    println!(
        "ACB_WT_E2PRIME|status=PASS|ell={ell}|k={degree}|d={interval}|\
fibre_count={fibres}|points={points}|square_sum={square_sum}|\
delta={delta}|abs_correlation={abs}|\
within_fibre_off_diagonal={off_diagonal}|e2_prime_holds={holds}|\
square_sum_over_points={ratio:.6}|square_sum_over_2_k_d_minus_1={e2ratio:.6}|\
e2_holds={e2_holds}|sign_constant_S={sign_constant:.6}|\
nonzero_fibres={nonzero}|power_of_two_fibres={pow2}",
        fibres = report.fibre_count,
        abs = report.fibrewise_absolute_correlation,
        ratio = square_sum_f / points_f,
        e2ratio = square_sum_f / e2_threshold_f,
        e2_holds = square_sum <= e2_threshold,
        nonzero = report.nonzero_fibre_correlation_count,
        pow2 = report.power_of_two_magnitude_fibre_count,
    );
    Ok(())
}

fn run() -> Result<(), String> {
    let mut arguments = std::env::args().skip(1);
    let first = arguments
        .next()
        .map_or(Ok(4), |value| value.parse::<usize>())
        .map_err(|_| "ell bounds must be integers".to_owned())?;
    let last = arguments
        .next()
        .map_or(Ok(first), |value| value.parse::<usize>())
        .map_err(|_| "ell bounds must be integers".to_owned())?;
    if arguments.next().is_some() || first < 2 || last < first {
        return Err("usage: acb_wt_e2prime [ell_min] [ell_max]".to_owned());
    }
    let limits = HayesLimits {
        max_ell: 24,
        max_degree: 50,
        max_group_order: 1 << 24,
        max_table_cells: 1_600_000_000,
    };
    for ell in first..=last {
        for degree in [ell + 2, ell + 3] {
            emit_row(ell, degree, ell - 1, limits)?;
        }
    }
    Ok(())
}
