//! AC-Bridge phase-3 workstream 22 ((CDL) assault): from-scratch verification of
//! the polynomial-pair form of the shifted second moment `T_chi`.
//!
//! This example shares NO code, no algorithm and no coordinate convention with
//! `axeyum_cas::gf2_hayes`: it enumerates the monic degree-`n` prime powers of
//! `GF(2)[x]` by trial division, builds `G_ell` as truncated reciprocal
//! polynomials with its own multiplication, and computes discrete logarithms
//! against the generators `1 + x^i` to get character coordinates.  It then
//! checks, exactly, in `Z[zeta_N]`:
//!
//! ```text
//! (PAIR)   sum_(F,G monic deg n, <F> = <G>) Lambda(F) Lambda(G) chi(<F>)
//!            =  sum_e N_n(e)^2 chi(e)                                (literal pair enumeration)
//! (PP)     fhat(chi) = sum_e N_n(e)^2 chi(e) - 2 mu S_chi            for chi != 1
//! (TWIST)  T_chi := sum_psi S_psi conj(S_(psi chi)) = 2^ell fhat(chi^(-1))
//! (COARSE) sum_b n_j(b)^2 = 2^(2 ell - j) mu^2 + A_j   and   A_j <= 2^(n-j) Sigma_j
//! ```
//!
//! `(PAIR)` is the identity that pins the SCALE of the constraint: the pairs are
//! constrained by `<F> = <G>`, i.e. `F - G` of degree `< n - ell`, a short
//! interval of length `2^(n-ell)` -- the square-root scale -- and NOT by an
//! index-`2^j` condition.  `(COARSE)` is the index-`2^j` object, which lives at
//! scale `2^(n-j)` and IS bounded by the proved Weil window.

#![allow(clippy::cast_precision_loss)]

use num_bigint::BigInt;
use num_traits::{ToPrimitive, Zero};

/// Exact element of `Z[zeta_N]`, `N = 2^K >= 2`, basis `1..zeta^(N/2-1)`.
#[derive(Clone, Debug, PartialEq, Eq)]
struct Cyc {
    order: usize,
    coefficients: Vec<BigInt>,
}

impl Cyc {
    fn zero(order: usize) -> Self {
        Self {
            order,
            coefficients: vec![BigInt::from(0_u8); order / 2],
        }
    }
    fn add_term(&mut self, exponent: usize, value: &BigInt) {
        let half = self.order / 2;
        let reduced = exponent % self.order;
        if reduced < half {
            self.coefficients[reduced] += value;
        } else {
            self.coefficients[reduced - half] -= value;
        }
    }
    fn add_assign(&mut self, other: &Self) {
        for (slot, value) in self.coefficients.iter_mut().zip(other.coefficients.iter()) {
            *slot += value;
        }
    }
    fn scale(&self, factor: &BigInt) -> Self {
        Self {
            order: self.order,
            coefficients: self
                .coefficients
                .iter()
                .map(|value| value * factor)
                .collect(),
        }
    }
    fn conjugate(&self) -> Self {
        let mut result = Self::zero(self.order);
        for (exponent, value) in self.coefficients.iter().enumerate() {
            result.add_term((self.order - exponent) % self.order, value);
        }
        result
    }
    fn multiply(&self, other: &Self) -> Self {
        let mut result = Self::zero(self.order);
        for (left, lvalue) in self.coefficients.iter().enumerate() {
            if lvalue.is_zero() {
                continue;
            }
            for (right, rvalue) in other.coefficients.iter().enumerate() {
                if rvalue.is_zero() {
                    continue;
                }
                result.add_term(left + right, &(lvalue * rvalue));
            }
        }
        result
    }
    fn magnitude(&self) -> f64 {
        let mut real = 0.0_f64;
        let mut imaginary = 0.0_f64;
        for (exponent, value) in self.coefficients.iter().enumerate() {
            let angle = 2.0 * std::f64::consts::PI * (exponent as f64) / (self.order as f64);
            let scaled = value.to_f64().unwrap_or(f64::NAN);
            real += scaled * angle.cos();
            imaginary += scaled * angle.sin();
        }
        real.hypot(imaginary)
    }
}

/// Carryless product of two `GF(2)` polynomials held as bit masks.
fn poly_multiply(left: u64, right: u64) -> u64 {
    let mut product = 0_u64;
    let mut shifted = left;
    let mut bits = right;
    while bits != 0 {
        if bits & 1 == 1 {
            product ^= shifted;
        }
        bits >>= 1;
        shifted <<= 1;
    }
    product
}

fn degree_of(value: u64) -> Option<u32> {
    if value == 0 {
        None
    } else {
        Some(63 - value.leading_zeros())
    }
}

/// Remainder of `value` modulo `modulus` in `GF(2)[x]`.
fn poly_remainder(mut value: u64, modulus: u64) -> u64 {
    let modulus_degree = degree_of(modulus).expect("nonzero modulus");
    while let Some(degree) = degree_of(value) {
        if degree < modulus_degree {
            break;
        }
        value ^= modulus << (degree - modulus_degree);
    }
    value
}

/// Every monic irreducible of degree exactly `degree`, by trial division.
fn irreducibles_of_degree(degree: u32, smaller: &[u64]) -> Vec<u64> {
    let base = 1_u64 << degree;
    let mut found = Vec::new();
    for tail in 0..base {
        let candidate = base | tail;
        let divisible = smaller.iter().any(|divisor| {
            degree_of(*divisor).expect("nonzero") * 2 <= degree
                && poly_remainder(candidate, *divisor) == 0
        });
        if !divisible {
            found.push(candidate);
        }
    }
    found
}

/// `<F>` for monic `F` of degree `n`: the top `ell` coefficients below the
/// leading one, read as `1 + a_1 t + ... + a_ell t^ell`, packed as an `ell`-bit
/// mask with bit `i-1` holding `a_i`.
fn hayes_class(polynomial: u64, degree: u32, ell: usize) -> usize {
    let mut mask = 0_usize;
    for index in 1..=ell {
        let position = degree as usize - index;
        if (polynomial >> position) & 1 == 1 {
            mask |= 1 << (index - 1);
        }
    }
    mask
}

/// Product in the principal-unit group `G_ell`, elements packed as above.
fn unit_multiply(left: usize, right: usize, ell: usize) -> usize {
    // (1 + A(t)) (1 + B(t)) mod t^(ell+1), A and B having no constant term.
    let mut result = left ^ right;
    for i in 1..=ell {
        if (left >> (i - 1)) & 1 == 0 {
            continue;
        }
        for j in 1..=ell {
            if i + j > ell {
                break;
            }
            if (right >> (j - 1)) & 1 == 1 {
                result ^= 1 << (i + j - 1);
            }
        }
    }
    result
}

struct Coordinates {
    orders: Vec<usize>,
    odd_degrees: Vec<usize>,
    /// coordinate vector of every group element, in packed-mask order
    table: Vec<Vec<usize>>,
}

/// Discrete logarithms of every element of `G_ell` against `1 + t^i`, `i` odd.
fn build_coordinates(ell: usize) -> Result<Coordinates, String> {
    let odd_degrees: Vec<usize> = (1..=ell).step_by(2).collect();
    let orders: Vec<usize> = odd_degrees
        .iter()
        .map(|odd| {
            let mut order = 1_usize;
            while *odd <= ell / order {
                order *= 2;
            }
            order
        })
        .collect();
    if orders.iter().product::<usize>() != 1_usize << ell {
        return Err("generator orders do not multiply to 2^ell".to_owned());
    }
    let mut table = vec![Vec::new(); 1_usize << ell];
    let mut seen = vec![false; 1_usize << ell];
    let mut exponents = vec![0_usize; odd_degrees.len()];
    for _ in 0..(1_usize << ell) {
        let mut element = 0_usize; // the identity 1
        for (position, odd) in odd_degrees.iter().enumerate() {
            let generator = 1_usize << (odd - 1);
            for _ in 0..exponents[position] {
                element = unit_multiply(element, generator, ell);
            }
        }
        if seen[element] {
            return Err("generator tuple map is not injective".to_owned());
        }
        seen[element] = true;
        table[element] = exponents.clone();
        for (position, order) in orders.iter().enumerate() {
            exponents[position] += 1;
            if exponents[position] < *order {
                break;
            }
            exponents[position] = 0;
        }
    }
    Ok(Coordinates {
        orders,
        odd_degrees,
        table,
    })
}

fn character_exponent(
    duals: &[usize],
    coordinates: &[usize],
    orders: &[usize],
    cyclotomic_order: usize,
) -> usize {
    let mut exponent = 0_usize;
    for (position, order) in orders.iter().enumerate() {
        exponent += duals[position] * coordinates[position] * (cyclotomic_order / order);
    }
    exponent
}

/// Conductor level of a character given by dual coordinates on `G_ell`.
fn conductor_level(duals: &[usize], odd_degrees: &[usize], orders: &[usize], ell: usize) -> usize {
    for candidate in 0..=ell {
        let mut trivial = true;
        for (position, odd) in odd_degrees.iter().enumerate() {
            if *odd > candidate {
                if duals[position] != 0 {
                    trivial = false;
                }
                continue;
            }
            let mut target = 1_usize;
            while *odd <= candidate / target {
                target *= 2;
            }
            let step = orders[position] / target;
            if duals[position] % step != 0 {
                trivial = false;
            }
        }
        if trivial {
            return candidate;
        }
    }
    ell
}

#[allow(clippy::too_many_lines)]
fn emit_row(ell: usize, degree: usize, twist_cap: usize) -> Result<(), String> {
    let n = u32::try_from(degree).map_err(|_| "degree too large".to_owned())?;
    // All monic irreducibles up to degree n/2, plus those of the divisor degrees.
    let mut irreducibles: Vec<u64> = Vec::new();
    let mut by_degree: Vec<Vec<u64>> = vec![Vec::new(); degree + 1];
    for d in 1..=degree {
        let level = irreducibles_of_degree(
            u32::try_from(d).map_err(|_| "degree too large".to_owned())?,
            &irreducibles,
        );
        by_degree[d] = level.clone();
        irreducibles.extend(level);
        if 2 * d > degree {
            // higher degrees are only needed when d divides n
            if degree % d != 0 {
                by_degree[d].clear();
            }
        }
    }
    // The Mangoldt-supported monic polynomials of degree n: F = P^k, k deg P = n.
    let mut prime_powers: Vec<(usize, u64)> = Vec::new(); // (Lambda, class)
    for d in 1..=degree {
        if degree % d != 0 {
            continue;
        }
        let power = degree / d;
        let candidates = if 2 * d > degree {
            irreducibles_of_degree(
                u32::try_from(d).map_err(|_| "degree too large".to_owned())?,
                &irreducibles
                    .iter()
                    .copied()
                    .filter(|value| 2 * degree_of(*value).expect("nonzero") as usize <= d)
                    .collect::<Vec<_>>(),
            )
        } else {
            by_degree[d].clone()
        };
        for prime in candidates {
            let mut value = 1_u64;
            for _ in 0..power {
                value = poly_multiply(value, prime);
            }
            if degree_of(value) != Some(n) {
                return Err("prime power has the wrong degree".to_owned());
            }
            prime_powers.push((d, u64::try_from(hayes_class(value, n, ell)).unwrap_or(0)));
        }
    }
    let mangoldt_total: usize = prime_powers.iter().map(|(weight, _)| weight).sum();
    if mangoldt_total != 1_usize << degree {
        return Err(format!(
            "sum of Lambda is {mangoldt_total}, not 2^{degree}: prime-power enumeration is wrong"
        ));
    }

    let classes = 1_usize << ell;
    let mean = BigInt::from(1_u64 << (degree - ell));
    let mut populations = vec![BigInt::from(0_u8); classes];
    for (weight, class) in &prime_powers {
        populations[usize::try_from(*class).unwrap_or(0)] += BigInt::from(*weight);
    }
    let mut class_buckets: Vec<Vec<usize>> = vec![Vec::new(); classes];
    for (weight, class) in &prime_powers {
        class_buckets[usize::try_from(*class).unwrap_or(0)].push(*weight);
    }
    let enumerated_pairs: usize = class_buckets.iter().map(|bucket| bucket.len().pow(2)).sum();
    let discrepancies: Vec<BigInt> = populations.iter().map(|value| value - &mean).collect();
    if discrepancies.iter().sum::<BigInt>() != BigInt::from(0_u8) {
        return Err("discrepancies are not mean zero".to_owned());
    }
    let m2: BigInt = discrepancies.iter().map(|value| value * value).sum();

    let coordinates = build_coordinates(ell)?;
    let mut cyclotomic_order = 2_usize;
    while cyclotomic_order <= ell {
        cyclotomic_order *= 2;
    }

    // Full spectrum S_psi = sum_e D_e psi(e), exact, over every character.
    let dual_count = classes;
    let mut spectrum: Vec<Cyc> = Vec::with_capacity(dual_count);
    let mut dual_index: Vec<Vec<usize>> = Vec::with_capacity(dual_count);
    let mut duals = vec![0_usize; coordinates.orders.len()];
    for _ in 0..dual_count {
        let mut value = Cyc::zero(cyclotomic_order);
        for element in 0..classes {
            let exponent = character_exponent(
                &duals,
                &coordinates.table[element],
                &coordinates.orders,
                cyclotomic_order,
            );
            value.add_term(exponent, &discrepancies[element]);
        }
        spectrum.push(value);
        dual_index.push(duals.clone());
        for (position, order) in coordinates.orders.iter().enumerate() {
            duals[position] += 1;
            if duals[position] < *order {
                break;
            }
            duals[position] = 0;
        }
    }
    // index of a dual tuple in the odometer order above
    let dual_key = |tuple: &[usize]| -> usize {
        let mut index = 0_usize;
        let mut stride = 1_usize;
        for (position, order) in coordinates.orders.iter().enumerate() {
            index += tuple[position] * stride;
            stride *= order;
        }
        index
    };

    // Low-conductor twists: every chi with 1 <= cond(chi) <= 3.
    let mut checked = 0_usize;
    let mut report = Vec::new();
    for (index, tuple) in dual_index.iter().enumerate() {
        let level = conductor_level(tuple, &coordinates.odd_degrees, &coordinates.orders, ell);
        if level == 0 || level > 3 {
            continue;
        }
        // fhat(chi) = sum_e D_e^2 chi(e)
        let mut transform = Cyc::zero(cyclotomic_order);
        let mut population_square = Cyc::zero(cyclotomic_order);
        let mut population_sum = Cyc::zero(cyclotomic_order);
        for element in 0..classes {
            let exponent = character_exponent(
                tuple,
                &coordinates.table[element],
                &coordinates.orders,
                cyclotomic_order,
            );
            transform.add_term(
                exponent,
                &(&discrepancies[element] * &discrepancies[element]),
            );
            population_square.add_term(exponent, &(&populations[element] * &populations[element]));
            population_sum.add_term(exponent, &populations[element]);
        }

        // (PAIR): literal enumeration of the ordered Mangoldt pairs with
        // <F> = <G>, organized by class so that only admissible pairs are
        // visited (the pair set enumerated is exactly the same set).
        let mut pair_sum = Cyc::zero(cyclotomic_order);
        for (element, bucket) in class_buckets.iter().enumerate() {
            if bucket.is_empty() {
                continue;
            }
            let exponent = character_exponent(
                tuple,
                &coordinates.table[element],
                &coordinates.orders,
                cyclotomic_order,
            );
            for left_weight in bucket {
                for right_weight in bucket {
                    pair_sum.add_term(exponent, &BigInt::from(left_weight * right_weight));
                }
            }
        }
        if pair_sum != population_square {
            return Err("literal pair enumeration disagrees with sum_e N_e^2 chi(e)".to_owned());
        }

        // (PP): fhat(chi) = sum_e N_e^2 chi(e) - 2 mu S_chi.
        let mut pair_form = population_square.clone();
        pair_form.add_assign(&population_sum.scale(&(BigInt::from(-2_i8) * &mean)));
        if pair_form != transform {
            return Err("(PP) fails".to_owned());
        }
        // S_chi computed from D must agree with the one computed from N.
        if spectrum[index] != population_sum {
            return Err("S_chi from D disagrees with S_chi from N".to_owned());
        }

        // (TWIST): T_chi = sum_psi S_psi conj(S_(psi chi)) = 2^ell fhat(chi^(-1)).
        // The full dual convolution is 2^(2 ell) cyclotomic products; run it
        // where that is affordable and report the cutoff otherwise.
        let twist_checked = ell <= twist_cap;
        let mut twist = Cyc::zero(cyclotomic_order);
        if twist_checked {
            for (psi_index, psi_tuple) in dual_index.iter().enumerate() {
                let mut product_tuple = vec![0_usize; coordinates.orders.len()];
                for (position, order) in coordinates.orders.iter().enumerate() {
                    product_tuple[position] = (psi_tuple[position] + tuple[position]) % order;
                }
                let shifted = dual_key(&product_tuple);
                twist.add_assign(&spectrum[psi_index].multiply(&spectrum[shifted].conjugate()));
            }
        }
        let mut inverse_tuple = vec![0_usize; coordinates.orders.len()];
        for (position, order) in coordinates.orders.iter().enumerate() {
            inverse_tuple[position] = (order - tuple[position]) % order;
        }
        let mut inverse_transform = Cyc::zero(cyclotomic_order);
        for element in 0..classes {
            let exponent = character_exponent(
                &inverse_tuple,
                &coordinates.table[element],
                &coordinates.orders,
                cyclotomic_order,
            );
            inverse_transform.add_term(
                exponent,
                &(&discrepancies[element] * &discrepancies[element]),
            );
        }
        if twist_checked && twist != inverse_transform.scale(&BigInt::from(classes)) {
            return Err("(TWIST) fails".to_owned());
        }

        checked += 1;
        report.push(format!(
            "ACB_CDL_PAIRS_CHAR|ell={ell}|degree={degree}|j={level}|duals={tuple:?}|\
abs_fhat={magnitude:.9e}|abs_fhat_over_M2={share:.12e}|abs_T_chi_over_2ell_M2={twist_share:.12e}",
            magnitude = transform.magnitude(),
            share = transform.magnitude() / m2.to_f64().unwrap_or(f64::NAN),
            twist_share = if twist_checked {
                twist.magnitude() / ((classes as f64) * m2.to_f64().unwrap_or(f64::NAN))
            } else {
                f64::NAN
            },
        ));
    }

    // (COARSE): sum_b n_j(b)^2 = 2^(2 ell - j) mu^2 + A_j, and A_j <= 2^(n-j) Sigma_j.
    let mut coarse_rows = Vec::new();
    for level in 1..=ell.min(6) {
        let cylinders = 1_usize << level;
        let mut coarse_population = vec![BigInt::from(0_u8); cylinders];
        let mut coarse_signed = vec![BigInt::from(0_u8); cylinders];
        for element in 0..classes {
            // truncation mod t^(level+1): keep the low `level` bits of the mask
            let cylinder = element & ((1_usize << level) - 1);
            coarse_population[cylinder] += &populations[element];
            coarse_signed[cylinder] += &discrepancies[element];
        }
        let pair_count: BigInt = coarse_population.iter().map(|value| value * value).sum();
        let pushforward: BigInt = coarse_signed.iter().map(|value| value * value).sum();
        let expected = (BigInt::from(1_u64) << (2 * ell - level)) * &mean * &mean + &pushforward;
        if pair_count != expected {
            return Err(format!("(COARSE) identity fails at level {level}"));
        }
        let sigma_level: BigInt = (2..=level)
            .map(|i| BigInt::from(i - 1).pow(2) << (i - 1))
            .sum();
        let allowance = sigma_level << (degree - level);
        if pushforward > allowance {
            return Err(format!("proved coarse Weil bound fails at level {level}"));
        }
        coarse_rows.push(format!(
            "ACB_CDL_COARSE|ell={ell}|degree={degree}|j={level}|\
coarse_pair_count={pair_count}|A_j={pushforward}|weil_allowance={allowance}|\
ratio={ratio:.6e}",
            ratio =
                pushforward.to_f64().unwrap_or(f64::NAN) / allowance.to_f64().unwrap_or(f64::NAN),
        ));
    }

    println!(
        "ACB_CDL_PAIRS|status=PASS|ell={ell}|degree={degree}|parity={parity}|\
mangoldt_total={mangoldt_total}|M_2={m2}|characters_checked={checked}|\
enumerated_pairs={enumerated_pairs}|twist_cap={twist_cap}|\
identities=PAIR,PP,TWIST,COARSE",
        parity = if degree % 2 == 0 { "even" } else { "odd" },
    );
    for row in coarse_rows {
        println!("{row}");
    }
    for row in report {
        println!("{row}");
    }
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
    let twist_cap = arguments
        .next()
        .map_or(Ok(8), |value| value.parse::<usize>())
        .map_err(|_| "twist cap must be an integer".to_owned())?;
    if arguments.next().is_some() || first < 2 || last < first || last > 9 {
        return Err("usage: acb_cdl_pairs [ell_min] [ell_max<=9] [twist_cap]".to_owned());
    }
    for ell in first..=last {
        for degree in [2 * ell + 1, 2 * ell + 2] {
            emit_row(ell, degree, twist_cap)?;
        }
    }
    Ok(())
}

fn main() {
    if let Err(error) = run() {
        eprintln!("ACB_CDL_PAIRS|status=FAIL|error={error}");
        std::process::exit(1);
    }
}
