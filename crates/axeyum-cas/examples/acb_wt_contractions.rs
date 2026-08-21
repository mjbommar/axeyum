//! AC-Bridge workstream 04, task 3: which fourth-order object does the weak
//! endpoint implication actually need?
//!
//! Three distinct fourth-order contractions of the same spectrum are printed
//! side by side, all as exact integers:
//!
//! ```text
//! A = sum_chi |S_chi|^4                      pointwise / diagonal energy
//! B = sum_(chi1 chi2 chi3 chi4 = 1) prod S   = 2^(3 ell) M_4  (constrained)
//! W = 3 (sum_chi |S_chi|^2)^2                = 3 (2^ell M_2)^2  (Wick)
//! C = B - W                                  = 2^(2 ell) K_4    (connected)
//! ```
//!
//! The endpoint implication consumes `max_e |D_e|^4 <= M_4 = B / 2^(3 ell)`.
//! `A` is a different tensor contraction and does not bound `max_e |D_e|`.
//! The row also prints how much of the required `M_4` budget is already
//! discharged by the PROVED Weil second-moment envelope through the Wick part,
//! which is the quantity that decides whether the ladder should target `M_4` or
//! the connected `K_4`.

use axeyum_cas::gf2_hayes::{HayesLimits, class_population_distribution};
use num_bigint::{BigInt, BigUint};
use num_traits::ToPrimitive;

fn main() {
    if let Err(error) = run() {
        eprintln!("ACB_WT_CONTRACTIONS|status=FAIL|error={error}");
        std::process::exit(1);
    }
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
        (value >> shift).to_f64().map_or(f64::NAN, |head| {
            head.log2() + shift.to_f64().unwrap_or(f64::NAN)
        })
    }
}

fn emit_row(ell: usize, degree: usize, limits: HayesLimits) -> Result<(), String> {
    let distribution =
        class_population_distribution(ell, degree, limits).map_err(|error| error.to_string())?;
    let comparison = distribution
        .character_fourth_moment_comparison(1 << 28)
        .map_err(|error| error.to_string())?;
    let m2 = distribution
        .central_absolute_power_sum(2)
        .map_err(|error| error.to_string())?;
    let m4 = distribution
        .central_absolute_power_sum(4)
        .map_err(|error| error.to_string())?;

    // proved Weil envelope on M_2
    let mut sigma = BigUint::from(0_u8);
    for j in 2..=ell {
        sigma += BigUint::from(j - 1).pow(2) << (j - 1);
    }
    let mean = BigUint::from(1_u8) << (degree - ell);
    let envelope = &mean * &sigma;
    // The Wick part of 2^ell M_4 is 3 M_2^2; bounding M_2 by the envelope
    // gives the proved share of the budget.
    let wick_from_envelope = BigUint::from(3_u8) * envelope.pow(2);
    let wick_exact = BigUint::from(3_u8) * m2.pow(2);
    let scaled_m4 = (BigUint::from(1_u8) << ell) * &m4;
    let connected = BigInt::from(scaled_m4.clone()) - BigInt::from(wick_exact.clone());

    println!(
        "ACB_WT_CONTRACTIONS|status=PASS|ell={ell}|degree={degree}|\
pointwise_A={a}|constrained_B={b}|three_wick_W={w}|connected_C={c}|\
scaled_M_4={scaled_m4}|wick_exact={wick_exact}|connected_K_4_numerator={connected}|\
A_over_B={a_over_b:.9}|log2_A={log2_a:.6}|log2_B={log2_b:.6}|\
wick_share_of_scaled_M_4={wick_share:.9}|\
proved_wick_envelope={wick_from_envelope}|\
proved_wick_over_scaled_M_4={proved_share:.6}",
        a = comparison.pointwise_character_fourth_moment,
        b = comparison.product_constrained_fourth_moment,
        w = comparison.three_wick_pairings,
        c = comparison.connected_product_constrained_numerator,
        a_over_b = log2_f64(&comparison.pointwise_character_fourth_moment).exp2()
            / log2_f64(&comparison.product_constrained_fourth_moment).exp2(),
        log2_a = log2_f64(&comparison.pointwise_character_fourth_moment),
        log2_b = log2_f64(&comparison.product_constrained_fourth_moment),
        wick_share = log2_f64(&wick_exact).exp2() / log2_f64(&scaled_m4).exp2(),
        proved_share = log2_f64(&wick_from_envelope) - log2_f64(&scaled_m4),
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
        return Err("usage: acb_wt_contractions [ell_min] [ell_max]".to_owned());
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
