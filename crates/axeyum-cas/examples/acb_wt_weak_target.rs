//! AC-Bridge workstream 04: the EXACT weak fourth-moment endpoint target.
//!
//! This example is deliberately independent of the Hayes Fourier transform for
//! everything except the class population vector.  It rebuilds, by direct
//! enumeration over binary polynomials:
//!
//! * `I_n(1)`, the number of monic degree-`n` irreducibles whose top `ell`
//!   coefficients vanish (the Lemire shape);
//! * `Pi_n`, the EXACT Mangoldt mass of proper prime powers in the identity
//!   Hayes class (the quantity the library only upper-bounds);
//! * the resulting exact strict threshold `(mu - Pi_n)^4` of the weak target.
//!
//! It then checks the reconstruction `N_n(1) = Pi_n + n I_n(1)` against the
//! CAS class population vector, which ties the two computations together, and
//! reports `M_4` against the exact threshold, the library's upper-bound
//! threshold, the positivity-only threshold `mu^4`, and the old pointwise
//! candidate `2^(4 ell)`.

use axeyum_cas::gf2_hayes::{
    HayesLimits, class_population_distribution, principal_unit_structure,
    weak_fourth_moment_endpoint_ledger,
};
use num_bigint::{BigInt, BigUint};
use num_traits::ToPrimitive;

const MAX_ENUMERATION_BITS: u32 = 26;

fn main() {
    if let Err(error) = run() {
        eprintln!("ACB_WT_WEAK_TARGET|status=FAIL|error={error}");
        std::process::exit(1);
    }
}

// ---------------------------------------------------------------------------
// GF(2)[x] arithmetic on u128 bit masks (bit i is the coefficient of x^i).
// ---------------------------------------------------------------------------

fn poly_degree(value: u128) -> Option<usize> {
    if value == 0 {
        None
    } else {
        Some(127 - value.leading_zeros() as usize)
    }
}

fn poly_mul(left: u128, right: u128) -> u128 {
    let mut product = 0_u128;
    let mut remaining = right;
    let mut shift = 0_u32;
    while remaining != 0 {
        if remaining & 1 == 1 {
            product ^= left << shift;
        }
        remaining >>= 1;
        shift += 1;
    }
    product
}

fn poly_rem(mut value: u128, modulus: u128, modulus_degree: usize) -> u128 {
    while let Some(degree) = poly_degree(value) {
        if degree < modulus_degree {
            break;
        }
        value ^= modulus << (degree - modulus_degree);
    }
    value
}

fn poly_mul_mod(left: u128, right: u128, modulus: u128, modulus_degree: usize) -> u128 {
    poly_rem(poly_mul(left, right), modulus, modulus_degree)
}

fn poly_gcd(mut left: u128, mut right: u128) -> u128 {
    while right != 0 {
        let degree = poly_degree(right).unwrap_or(0);
        left = poly_rem(left, right, degree);
        std::mem::swap(&mut left, &mut right);
    }
    left
}

/// `x^(2^exponent) mod modulus`, by repeated squaring of the Frobenius.
fn frobenius_power(exponent: usize, modulus: u128, modulus_degree: usize) -> u128 {
    let mut value = poly_rem(0b10, modulus, modulus_degree);
    for _ in 0..exponent {
        value = poly_mul_mod(value, value, modulus, modulus_degree);
    }
    value
}

fn prime_factors(mut value: usize) -> Vec<usize> {
    let mut factors = Vec::new();
    let mut candidate = 2;
    while candidate * candidate <= value {
        if value.is_multiple_of(candidate) {
            factors.push(candidate);
            while value.is_multiple_of(candidate) {
                value /= candidate;
            }
        }
        candidate += 1;
    }
    if value > 1 {
        factors.push(value);
    }
    factors
}

/// Rabin's irreducibility test for a monic `f` of degree `degree >= 1`.
fn is_irreducible(f: u128, degree: usize) -> bool {
    if degree == 0 {
        return false;
    }
    if degree == 1 {
        return true;
    }
    if f & 1 == 0 {
        // divisible by x
        return false;
    }
    if frobenius_power(degree, f, degree) != 0b10 {
        return false;
    }
    for prime in prime_factors(degree) {
        let candidate = frobenius_power(degree / prime, f, degree) ^ 0b10;
        // `candidate == 0` means every root already lies in the degree-`d/p`
        // subfield, so `f` is reducible; it is NOT a pass.
        if candidate == 0 || poly_degree(poly_gcd(f, candidate)) != Some(0) {
            return false;
        }
    }
    true
}

// ---------------------------------------------------------------------------
// The principal-unit group E_ell as truncated units 1 + c_1 t + ... + c_ell t^ell.
// ---------------------------------------------------------------------------

/// Hayes class of a monic degree-`d` polynomial: `c_i` is the coefficient of
/// `x^(d-i)`, retained for `0 <= i <= ell`.  Bit 0 is always set.
fn hayes_class(f: u128, d: usize, ell: usize) -> u64 {
    let mut class = 0_u64;
    for i in 0..=ell.min(d) {
        if (f >> (d - i)) & 1 == 1 {
            class |= 1_u64 << i;
        }
    }
    class
}

fn class_mul(left: u64, right: u64, ell: usize) -> u64 {
    let mut product = 0_u64;
    let mut remaining = right;
    let mut shift = 0_u32;
    while remaining != 0 {
        if remaining & 1 == 1 {
            product ^= left << shift;
        }
        remaining >>= 1;
        shift += 1;
    }
    let mask = if ell >= 63 {
        u64::MAX
    } else {
        (1_u64 << (ell + 1)) - 1
    };
    product & mask
}

fn class_pow(base: u64, mut exponent: usize, ell: usize) -> u64 {
    let mut result = 1_u64;
    let mut factor = base;
    while exponent > 0 {
        if exponent & 1 == 1 {
            result = class_mul(result, factor, ell);
        }
        factor = class_mul(factor, factor, ell);
        exponent >>= 1;
    }
    result
}

fn divisors(value: usize) -> Vec<usize> {
    let mut result = Vec::new();
    let mut candidate = 1;
    while candidate * candidate <= value {
        if value.is_multiple_of(candidate) {
            result.push(candidate);
            if candidate != value / candidate {
                result.push(value / candidate);
            }
        }
        candidate += 1;
    }
    result.sort_unstable();
    result
}

/// Number of monic degree-`d` irreducibles in the identity Hayes class.
fn identity_class_irreducibles(d: usize, ell: usize) -> Result<u128, String> {
    if d <= ell {
        // A degree-`d` polynomial with `d <= ell` in the identity class has
        // every non-leading coefficient zero, so it is `x^d`; that is
        // irreducible only for d = 1.
        return Ok(u128::from(d == 1));
    }
    let free_bits = d - ell;
    if u32::try_from(free_bits).map_err(|_| "free-bit overflow".to_owned())? > MAX_ENUMERATION_BITS
    {
        return Err(format!("identity-class enumeration needs 2^{free_bits}"));
    }
    let mut total = 0_u128;
    for low in 0_u128..(1_u128 << free_bits) {
        let f = (1_u128 << d) | low;
        if is_irreducible(f, d) {
            total += 1;
        }
    }
    Ok(total)
}

/// Exact Mangoldt mass of PROPER prime powers in the identity class at
/// degree `n`, plus the exact identity-class irreducible count `I_n(1)`.
fn exact_identity_class_split(n: usize, ell: usize) -> Result<(u128, u128), String> {
    let mut proper = 0_u128;
    for k in divisors(n) {
        if k == 1 {
            continue;
        }
        let d = n / k;
        if d <= ell {
            // class(P) determines P completely; class(P)^k = 1 with the class
            // group a 2-group.
            if k % 2 == 1 {
                // odd k inverts on a 2-group, so class(P) = 1, so P = x^d,
                // irreducible only for d = 1.
                if d == 1 {
                    proper += 1;
                }
                continue;
            }
            let free_bits = d;
            if u32::try_from(free_bits).map_err(|_| "free-bit overflow".to_owned())?
                > MAX_ENUMERATION_BITS
            {
                return Err(format!("prime-power layer needs 2^{free_bits}"));
            }
            for low in 0_u128..(1_u128 << d) {
                let f = (1_u128 << d) | low;
                if !is_irreducible(f, d) {
                    continue;
                }
                if class_pow(hayes_class(f, d, ell), k, ell) == 1 {
                    proper += d as u128;
                }
            }
            continue;
        }
        let free_bits = d;
        if u32::try_from(free_bits).map_err(|_| "free-bit overflow".to_owned())?
            > MAX_ENUMERATION_BITS
        {
            return Err(format!("prime-power layer needs 2^{free_bits}"));
        }
        for low in 0_u128..(1_u128 << d) {
            let f = (1_u128 << d) | low;
            if !is_irreducible(f, d) {
                continue;
            }
            if class_pow(hayes_class(f, d, ell), k, ell) == 1 {
                proper += d as u128;
            }
        }
    }
    let irreducibles = identity_class_irreducibles(n, ell)?;
    Ok((proper, irreducibles))
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

#[allow(clippy::too_many_lines)]
fn emit_row(ell: usize, degree: usize, limits: HayesLimits) -> Result<(), String> {
    let structure = principal_unit_structure(ell, limits).map_err(|error| error.to_string())?;
    let two_torsion: u128 = structure
        .factors
        .iter()
        .map(|factor| u128::from(factor.order.min(2) as u64))
        .product();
    let rank = structure.factors.len();

    let (exact_proper, irreducibles) = exact_identity_class_split(degree, ell)?;

    let distribution =
        class_population_distribution(ell, degree, limits).map_err(|error| error.to_string())?;
    let mean = u128::from(1_u8) << (degree - ell);
    let identity_population = distribution.counts[0];
    let reconstruction = exact_proper + (degree as u128) * irreducibles;
    if reconstruction != identity_population {
        return Err(format!(
            "identity reconstruction {reconstruction} != CAS population {identity_population} at ell={ell}, degree={degree}"
        ));
    }

    let m2 = distribution
        .central_absolute_power_sum(2)
        .map_err(|error| error.to_string())?;
    let m4 = distribution
        .central_absolute_power_sum(4)
        .map_err(|error| error.to_string())?;

    let mean_big = BigUint::from(mean);
    let exact_proper_big = BigUint::from(exact_proper);
    let exact_margin = if mean_big > exact_proper_big {
        &mean_big - &exact_proper_big
    } else {
        BigUint::from(0_u8)
    };
    let exact_threshold = exact_margin.pow(4);
    let exact_holds = exact_threshold > BigUint::from(0_u8) && m4 < exact_threshold;

    let (library_bound, library_threshold, library_status) =
        match weak_fourth_moment_endpoint_ledger(ell, degree) {
            Ok(value) => (
                value.proper_prime_power_upper_bound.to_string(),
                value.strict_irreducible_fourth_moment_threshold.clone(),
                "ok".to_owned(),
            ),
            Err(error) => ("n/a".to_owned(), BigUint::from(0_u8), error.to_string()),
        };
    let library_holds = library_threshold > BigUint::from(0_u8) && m4 < library_threshold;

    let positivity_threshold = mean_big.pow(4);
    let pointwise_threshold = BigUint::from(1_u8) << (4 * ell);

    // Integrality: N_n(1) = Pi_n + n I_n(1), so N_n(1) > Pi_n already follows
    // from the non-strict |D_1| <= mu - Pi_n - n.
    let integral_margin = if mean_big > &exact_proper_big + BigUint::from(degree) {
        &mean_big - &exact_proper_big - BigUint::from(degree)
    } else {
        BigUint::from(0_u8)
    };
    let integral_threshold = integral_margin.pow(4);
    let integral_holds = integral_threshold > BigUint::from(0_u8) && m4 <= integral_threshold;

    let mut sigma = BigUint::from(0_u8);
    for j in 2..=ell {
        sigma += BigUint::from(j - 1).pow(2) << (j - 1);
    }
    let envelope = &mean_big * &sigma;
    let allowance_log2 =
        ell.to_f64().unwrap_or(f64::NAN) + log2_f64(&exact_threshold) - 2.0 * log2_f64(&envelope);
    let group_order = BigUint::from(distribution.counts.len());
    let root_ratio = log2_f64(&(group_order * &m4)).exp2() / log2_f64(&m2.pow(2)).exp2();
    let cumulant = distribution
        .fourth_cumulant_numerator()
        .map_err(|error| error.to_string())?;
    let connected_allowance = BigInt::from((BigUint::from(1_u8) << ell) * &exact_threshold)
        - BigInt::from(BigUint::from(3_u8) * envelope.pow(2));

    println!(
        "ACB_WT_WEAK_TARGET|status=PASS|ell={ell}|degree={degree}|parity={parity}|\
witt_rank={rank}|two_torsion_order={two_torsion}|mean={mean}|\
I_n_identity={irreducibles}|exact_proper_power_mass={exact_proper}|\
identity_population={identity_population}|identity_deviation={identity_deviation}|\
reconstruction_ok=true|\
exact_margin={exact_margin}|exact_threshold={exact_threshold}|exact_target_holds={exact_holds}|\
library_proper_bound={library_bound}|library_status={library_status}|\
library_threshold={library_threshold}|library_target_holds={library_holds}|\
integral_threshold={integral_threshold}|integral_target_holds={integral_holds}|\
positivity_only_holds={positivity_holds}|pointwise_holds={pointwise_holds}|\
M_2={m2}|M_4={m4}|K_4={cumulant}|R_0={root_ratio:.9}|\
log2_M_4={log2_m4:.6}|log2_exact_threshold={log2_exact:.6}|log2_exact_slack={log2_slack:.6}|\
log2_sufficient_R_0={allowance_log2:.6}|connected_allowance={connected_allowance}",
        parity = if degree.is_multiple_of(2) {
            "even"
        } else {
            "odd"
        },
        identity_deviation = BigInt::from(identity_population) - BigInt::from(mean),
        positivity_holds = m4 < positivity_threshold,
        pointwise_holds = m4 <= pointwise_threshold,
        log2_m4 = log2_f64(&m4),
        log2_exact = log2_f64(&exact_threshold),
        log2_slack = log2_f64(&exact_threshold) - log2_f64(&m4),
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
        return Err("usage: acb_wt_weak_target [ell_min] [ell_max]".to_owned());
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
