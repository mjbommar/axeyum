//! AC-Bridge workstream 04: independent verification of the weak fourth-moment
//! endpoint target `(T-weak)`.
//!
//! For every admitted `ell` and both Lemire endpoint parities this example
//! recomputes, from the exact class populations alone:
//!
//! ```text
//! mu   = 2^(n-ell)                     uniform Mangoldt class mean
//! D_e  = N_n(e) - mu                   class discrepancy (mean zero)
//! M_2  = sum_e D_e^2,  M_4 = sum_e D_e^4
//! K_4  = 2^ell M_4 - 3 M_2^2           connected fourth cumulant numerator
//! R_0  = 2^ell M_4 / M_2^2             root (kurtosis) ratio
//! P_n  = proper-prime-power upper bound in the identity class
//! ```
//!
//! and then compares `M_4` against three thresholds:
//!
//! ```text
//! mu^4          positivity only  (NOT sufficient for an irreducible)
//! (mu - P_n)^4  the corrected weak target (W4)
//! 2^(4 ell)     the older pointwise candidate |D_e| <= 2^ell
//! ```
//!
//! Every quantity is recomputed here from `counts` with exact integer
//! arithmetic and is then cross-checked against the library's own methods, so
//! a mutation in either implementation is visible.

use axeyum_cas::gf2_hayes::{
    ClassPopulationDistribution, HayesLimits, class_population_distribution,
    weak_fourth_moment_endpoint_ledger,
};
use num_bigint::{BigInt, BigUint};
use num_traits::ToPrimitive;

fn main() {
    if let Err(error) = run() {
        eprintln!("ACB_WT_MOMENTS|status=FAIL|error={error}");
        std::process::exit(1);
    }
}

/// `Sigma(ell) = sum_(j=2)^ell 2^(j-1) (j-1)^2`, recomputed by summation.
fn sigma_by_sum(ell: usize) -> BigUint {
    let mut total = BigUint::from(0_u8);
    for j in 2..=ell {
        total += BigUint::from(j - 1).pow(2) << (j - 1);
    }
    total
}

/// The claimed closed form `2^ell (ell^2 - 4 ell + 6) - 6`.
fn sigma_closed_form(ell: usize) -> Option<BigUint> {
    let ell_i = BigInt::from(ell);
    let inner = &ell_i * &ell_i - BigInt::from(4_u8) * &ell_i + BigInt::from(6_u8);
    let value = (inner << ell) - BigInt::from(6_u8);
    value.try_into().ok()
}

/// Independent re-derivation of the identity-class proper-prime-power bound.
///
/// Odd endpoint `n = 2 ell + 1`: every proper prime power is `P^k` with
/// `k | n`, `k >= 3` odd, so `deg P = n/k <= ell`.  A degree-`d <= ell`
/// polynomial in the identity class has all `ell` leading coefficients zero,
/// hence equals `x^d`; irreducibility forces `d = 1`.  The only proper prime
/// power in the identity class is therefore `x^n`, of Mangoldt weight one.
///
/// Even endpoint `n = 2 ell + 2`: the `k = 2` layer has `deg P = ell + 1 > ell`
/// and needs only `class(P)^2 = 1`, i.e. `class(P)` in the 2-torsion of
/// `E_ell`, whose order is `2^ceil(ell/2)`.  Each class has exactly
/// `2^(ell+1-ell) = 2` monic degree-`(ell+1)` preimages and weight `n/2`, so
/// that layer is at most `(n/2) 2^(ceil(ell/2)+1)`.  Layers `k >= 3` are
/// bounded by `n 2^ceil(n/3)`.
fn independent_proper_power_bound(ell: usize, degree: usize) -> BigUint {
    if degree == 2 * ell + 1 {
        return BigUint::from(1_u8);
    }
    let half = degree / 2;
    let square_layer = BigUint::from(half) << (ell.div_ceil(2) + 1);
    let higher_layers = BigUint::from(degree) << degree.div_ceil(3);
    square_layer + higher_layers
}

fn log2_f64(value: &BigUint) -> f64 {
    if *value == BigUint::from(0_u8) {
        return f64::NEG_INFINITY;
    }
    let bits = value.bits();
    if bits <= 900 {
        value.to_f64().map_or(f64::NAN, f64::log2)
    } else {
        let shift = bits - 800;
        let head = value >> shift;
        head.to_f64().map_or(f64::NAN, |head| {
            head.log2() + shift.to_f64().unwrap_or(f64::NAN)
        })
    }
}

fn ratio_f64(numerator: &BigUint, denominator: &BigUint) -> f64 {
    log2_f64(numerator).exp2() / log2_f64(denominator).exp2()
}

#[allow(clippy::too_many_lines)]
fn emit_row(ell: usize, degree: usize, limits: HayesLimits) -> Result<(), String> {
    let distribution: ClassPopulationDistribution =
        class_population_distribution(ell, degree, limits).map_err(|error| error.to_string())?;
    let group_order = distribution.counts.len();
    if group_order != 1_usize << ell {
        return Err(format!("class count {group_order} is not 2^{ell}"));
    }
    let mean = u128::from(1_u8) << (degree - ell);

    // --- independent exact recomputation from the raw populations -----------
    let mut total_population = BigUint::from(0_u8);
    let mut m2 = BigUint::from(0_u8);
    let mut m4 = BigUint::from(0_u8);
    let mut raw2 = BigUint::from(0_u8);
    let mut raw3 = BigUint::from(0_u8);
    let mut raw4 = BigUint::from(0_u8);
    let mut max_absolute = 0_u128;
    let mut minimum = u128::MAX;
    let mut maximum = 0_u128;
    for &count in &distribution.counts {
        total_population += BigUint::from(count);
        let deviation = count.abs_diff(mean);
        let deviation_big = BigUint::from(deviation);
        m2 += deviation_big.pow(2);
        m4 += deviation_big.pow(4);
        let raw = BigUint::from(count);
        raw2 += raw.pow(2);
        raw3 += raw.pow(3);
        raw4 += raw.pow(4);
        max_absolute = max_absolute.max(deviation);
        minimum = minimum.min(count);
        maximum = maximum.max(count);
    }
    if total_population != BigUint::from(1_u8) << degree {
        return Err(format!(
            "Mangoldt populations sum to {total_population}, expected 2^{degree}"
        ));
    }
    let identity_population = distribution.counts[0];
    let identity_deviation = BigInt::from(identity_population) - BigInt::from(mean);

    // --- library cross-checks ----------------------------------------------
    let library_m2 = distribution
        .central_absolute_power_sum(2)
        .map_err(|error| error.to_string())?;
    let library_m4 = distribution
        .central_absolute_power_sum(4)
        .map_err(|error| error.to_string())?;
    if library_m2 != m2 || library_m4 != m4 {
        return Err("independent central moments disagree with the library".to_owned());
    }
    let library_cumulant = distribution
        .fourth_cumulant_numerator()
        .map_err(|error| error.to_string())?;
    let cumulant = BigInt::from((BigUint::from(group_order)) * &m4)
        - BigInt::from(BigUint::from(3_u8) * m2.pow(2));
    if library_cumulant != cumulant {
        return Err("independent cumulant disagrees with the library".to_owned());
    }

    // --- thresholds ---------------------------------------------------------
    let ledger = weak_fourth_moment_endpoint_ledger(ell, degree);
    let independent_proper = independent_proper_power_bound(ell, degree);
    let mean_big = BigUint::from(mean);
    let positivity_threshold = mean_big.pow(4);
    let pointwise_threshold = BigUint::from(1_u8) << (4 * ell);
    let sigma = sigma_by_sum(ell);
    let sigma_closed = sigma_closed_form(ell).unwrap_or_else(|| BigUint::from(0_u8));
    let sigma_closed_form_agrees = ell < 2 || sigma_closed == sigma;
    let second_moment_envelope = &mean_big * &sigma;
    let weil_envelope_holds = m2 <= second_moment_envelope;

    let (proper_bound, strict_threshold, ledger_status) = match &ledger {
        Ok(value) => {
            if value.proper_prime_power_upper_bound != independent_proper {
                return Err(format!(
                    "library proper-power bound {} disagrees with the independent {independent_proper}",
                    value.proper_prime_power_upper_bound
                ));
            }
            if value.second_moment_weil_factor != sigma {
                return Err("library Sigma(ell) disagrees with the independent sum".to_owned());
            }
            (
                value.proper_prime_power_upper_bound.clone(),
                value.strict_irreducible_fourth_moment_threshold.clone(),
                "ok".to_owned(),
            )
        }
        Err(error) => {
            let margin_defined = independent_proper < mean_big;
            let strict = if margin_defined {
                (&mean_big - &independent_proper).pow(4)
            } else {
                BigUint::from(0_u8)
            };
            (
                independent_proper.clone(),
                strict,
                format!("declined:{error}"),
            )
        }
    };

    let weak_target_holds = strict_threshold > BigUint::from(0_u8) && m4 < strict_threshold;
    let positivity_only_holds = m4 < positivity_threshold;
    let pointwise_holds = m4 <= pointwise_threshold;
    // Integrality refinement: N_n(1) lies in P_n' + n Z at the odd endpoint,
    // so the non-strict threshold (mu - P_n - n)^4 already suffices there.
    let integral_margin = if mean_big > &proper_bound + BigUint::from(degree) {
        &mean_big - &proper_bound - BigUint::from(degree)
    } else {
        BigUint::from(0_u8)
    };
    let integral_threshold = integral_margin.pow(4);
    let integral_holds = integral_threshold > BigUint::from(0_u8) && m4 <= integral_threshold;

    // sufficient root-ratio allowance  R_0 < 2^ell (mu-P_n)^4 / (mu Sigma)^2
    let allowance_numerator = (BigUint::from(1_u8) << ell) * &strict_threshold;
    let allowance_denominator = second_moment_envelope.pow(2);
    let allowance_log2 = log2_f64(&allowance_numerator) - log2_f64(&allowance_denominator);
    let root_ratio =
        log2_f64(&(BigUint::from(group_order) * &m4)).exp2() / log2_f64(&m2.pow(2)).exp2();

    let cumulant_sign = match cumulant.sign() {
        num_bigint::Sign::Minus => "-",
        num_bigint::Sign::NoSign => "0",
        num_bigint::Sign::Plus => "+",
    };
    let cumulant_over_m2sq = {
        let magnitude = cumulant.magnitude().clone();
        let value = log2_f64(&magnitude).exp2() / log2_f64(&m2.pow(2)).exp2();
        if cumulant.sign() == num_bigint::Sign::Minus {
            -value
        } else {
            value
        }
    };
    // The Wick part alone, bounded by the PROVED Weil envelope:
    // 3 M_2^2 <= 3 (mu Sigma)^2.  Sufficient connected allowance is then
    // K_4 <= 2^ell (mu-P_n)^4 - 3 (mu Sigma)^2.
    let wick_envelope = BigUint::from(3_u8) * &allowance_denominator;
    let connected_allowance =
        BigInt::from(allowance_numerator.clone()) - BigInt::from(wick_envelope.clone());
    let connected_allowance_positive = connected_allowance > BigInt::from(0_u8);
    let connected_target_holds = connected_allowance_positive && cumulant < connected_allowance;

    println!(
        "ACB_WT_MOMENTS|status=PASS|ell={ell}|degree={degree}|parity={parity}|\
group_order={group_order}|mean={mean}|min_population={minimum}|max_population={maximum}|\
max_abs_deviation={max_absolute}|identity_deviation={identity_deviation}|\
M_2={m2}|M_4={m4}|K_4={cumulant}|K_4_sign={cumulant_sign}|\
R_0={root_ratio:.9}|K_4_over_M_2_squared={cumulant_over_m2sq:.9}|\
raw_C2={raw2}|raw_C3={raw3}|raw_C4={raw4}|\
sigma={sigma}|sigma_closed_form_agrees={sigma_closed_form_agrees}|\
second_moment_envelope={second_moment_envelope}|weil_envelope_holds={weil_envelope_holds}|\
M_2_over_envelope={m2_ratio:.9}|\
proper_power_bound={proper_bound}|ledger={ledger_status}|\
positivity_only_threshold={positivity_threshold}|positivity_only_holds={positivity_only_holds}|\
weak_strict_threshold={strict_threshold}|weak_target_holds={weak_target_holds}|\
integral_threshold={integral_threshold}|integral_target_holds={integral_holds}|\
pointwise_threshold={pointwise_threshold}|pointwise_holds={pointwise_holds}|\
log2_M_4={log2_m4:.6}|log2_weak_threshold={log2_weak:.6}|log2_slack={log2_slack:.6}|\
M_4_over_weak_threshold={m4_over_weak:.9}|M_4_over_mean_fourth={m4_over_mean:.9}|\
log2_sufficient_R_0={allowance_log2:.6}|log2_R_0={log2_r0:.6}|\
connected_allowance={connected_allowance}|connected_allowance_positive={connected_allowance_positive}|\
connected_target_holds={connected_target_holds}",
        parity = if degree.is_multiple_of(2) {
            "even"
        } else {
            "odd"
        },
        m2_ratio = ratio_f64(&m2, &second_moment_envelope),
        log2_m4 = log2_f64(&m4),
        log2_weak = log2_f64(&strict_threshold),
        log2_slack = log2_f64(&strict_threshold) - log2_f64(&m4),
        m4_over_weak = ratio_f64(&m4, &strict_threshold),
        m4_over_mean = ratio_f64(&m4, &positivity_threshold),
        log2_r0 = root_ratio.log2(),
    );
    Ok(())
}

fn run() -> Result<(), String> {
    let mut arguments = std::env::args().skip(1);
    let first = arguments
        .next()
        .map_or(Ok(2), |value| value.parse::<usize>())
        .map_err(|_| "ell bounds must be integers".to_owned())?;
    let last = arguments
        .next()
        .map_or(Ok(first), |value| value.parse::<usize>())
        .map_err(|_| "ell bounds must be integers".to_owned())?;
    if arguments.next().is_some() || first == 0 || last < first {
        return Err("usage: acb_wt_moments [ell_min] [ell_max]".to_owned());
    }
    let limits = HayesLimits {
        max_ell: 24,
        max_degree: 50,
        max_group_order: 1 << 24,
        max_table_cells: 900_000_000,
    };
    for ell in first..=last {
        for degree in [2 * ell + 1, 2 * ell + 2] {
            emit_row(ell, degree, limits)?;
        }
    }
    Ok(())
}
