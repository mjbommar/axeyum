//! Exact finite transform oracle for the two Lemire/Hayes endpoint degrees.
//!
//! This binary evaluates the integral type-II Hayes recurrence after a finite
//! abelian-group Fourier transform.  Two NTT primes and CRT recover the exact
//! identity coefficient.  The reported `2^ell` discrepancy bound is an
//! observation over the requested finite range, not a universal theorem.

use std::collections::BTreeMap;

const PRIME_ONE: u64 = 998_244_353;
const PRIME_TWO: u64 = 1_004_535_809;
const PRIMITIVE_ROOT: u64 = 3;
const DEFAULT_MAX_ELL: usize = 12;
const MAX_ELL: usize = 18;

const EXPECTED: &[(i64, i64)] = &[
    (0, 0),
    (-2, 0),
    (6, -8),
    (5, 12),
    (-19, 32),
    (-49, 32),
    (45, -40),
    (50, 75),
    (-92, 48),
    (53, 63),
    (206, -352),
    (359, 335),
];

fn main() {
    if let Err(error) = run() {
        eprintln!("GF2_HAYES_ENDPOINTS|status=FAIL|error={error}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), String> {
    let mut arguments = std::env::args().skip(1);
    let max_ell = match arguments.next() {
        Some(value) => value
            .parse::<usize>()
            .map_err(|_| "max ell must be an integer".to_owned())?,
        None => DEFAULT_MAX_ELL,
    };
    if arguments.next().is_some() || !(1..=MAX_ELL).contains(&max_ell) {
        return Err(format!(
            "usage: axeyum-gf2-hayes-endpoints [max-ell: 1..={MAX_ELL}]"
        ));
    }

    let mut rows = Vec::with_capacity(max_ell);
    for ell in 1..=max_ell {
        let mut discrepancies = [0_i64; 2];
        for (slot, degree) in [2 * ell + 1, 2 * ell + 2].into_iter().enumerate() {
            let first = endpoint_residue(ell, degree, PRIME_ONE)?;
            let second = endpoint_residue(ell, degree, PRIME_TWO)?;
            let exact = crt(first, PRIME_ONE, second, PRIME_TWO)?;
            let upper_bound = 1_u128 << degree;
            if exact > upper_bound {
                return Err(format!(
                    "ell={ell} degree={degree}: recovered count {exact} exceeds 2^{degree}"
                ));
            }
            let main_term = 1_u128 << (degree - ell);
            let discrepancy = i64::try_from(exact)
                .map_err(|_| "recovered count does not fit i64".to_owned())?
                - i64::try_from(main_term).map_err(|_| "main term does not fit i64".to_owned())?;
            discrepancies[slot] = discrepancy;
        }
        if ell <= EXPECTED.len() && discrepancies != [EXPECTED[ell - 1].0, EXPECTED[ell - 1].1] {
            return Err(format!(
                "ell={ell}: endpoint discrepancies {:?} differ from the committed control {:?}",
                discrepancies,
                EXPECTED[ell - 1]
            ));
        }
        let observed_bound = discrepancies
            .iter()
            .all(|value| value.unsigned_abs() <= (1_u64 << ell));
        rows.push((ell, discrepancies, observed_bound));
    }

    let bound_holds = rows.iter().all(|row| row.2);
    let details = rows
        .iter()
        .map(|(ell, values, _)| format!("{ell}:{}:{}", values[0], values[1]))
        .collect::<Vec<_>>()
        .join(",");
    println!(
        "GF2_HAYES_ENDPOINTS|status=PASS|ell=1..{max_ell}|degrees=3..{}|exact=two_ntt_primes_plus_crt|candidate_abs_discrepancy_le_2powell={bound_holds}|discrepancies={details}",
        2 * max_ell + 2
    );
    Ok(())
}

fn endpoint_residue(ell: usize, target: usize, modulus: u64) -> Result<u64, String> {
    let mut odd_degrees = Vec::new();
    let mut dimensions = Vec::new();
    for odd in (1..=ell).step_by(2) {
        let mut order = 1_usize;
        while odd * order <= ell {
            order *= 2;
        }
        odd_degrees.push(odd);
        dimensions.push(order);
    }
    let size = 1_usize << ell;
    let mut unit_to_index = BTreeMap::new();
    for index in 0..size {
        let mut quotient = index;
        let mut value = 1_u64;
        for (&odd, &dimension) in odd_degrees.iter().zip(&dimensions) {
            let exponent = quotient % dimension;
            quotient /= dimension;
            let generator = 1 | (1_u64 << odd);
            for _ in 0..exponent {
                value = unit_multiply(value, generator, ell);
            }
        }
        if unit_to_index.insert(value, index).is_some() {
            return Err(format!(
                "ell={ell}: principal-unit decomposition is not injective"
            ));
        }
    }
    if unit_to_index.len() != size {
        return Err(format!(
            "ell={ell}: principal-unit decomposition is incomplete"
        ));
    }

    let mut class_sums = vec![vec![0_u64; size]; target + 1];
    class_sums[0][0] = 1;
    group_transform(&mut class_sums[0], &dimensions, modulus);
    for (degree, class_sum) in class_sums.iter_mut().enumerate().skip(1) {
        if degree >= ell {
            class_sum[0] = mod_pow(2, degree as u64, modulus);
        } else {
            for tail in 0..(1_u64 << degree) {
                let unit = 1 | (tail << 1);
                class_sum[unit_to_index[&unit]] = 1;
            }
            group_transform(class_sum, &dimensions, modulus);
        }
    }

    let mut mangoldt = vec![vec![0_u64; size]; target + 1];
    for degree in 1..=target {
        for character in 0..size {
            let mut value = multiply_mod(
                degree as u64 % modulus,
                class_sums[degree][character],
                modulus,
            );
            for earlier in 1..degree {
                let correction = multiply_mod(
                    mangoldt[earlier][character],
                    class_sums[degree - earlier][character],
                    modulus,
                );
                value = subtract_mod(value, correction, modulus);
            }
            mangoldt[degree][character] = value;
        }
    }
    let sum = mangoldt[target].iter().fold(0_u64, |accumulator, value| {
        add_mod(accumulator, *value, modulus)
    });
    Ok(multiply_mod(
        sum,
        mod_pow(size as u64, modulus - 2, modulus),
        modulus,
    ))
}

fn unit_multiply(mut left: u64, right: u64, ell: usize) -> u64 {
    let mut product = 0_u64;
    while left != 0 {
        let degree = left.trailing_zeros() as usize;
        left &= left - 1;
        product ^= right << degree;
    }
    product & ((1_u64 << (ell + 1)) - 1)
}

fn group_transform(values: &mut [u64], dimensions: &[usize], modulus: u64) {
    let mut stride = 1;
    for &dimension in dimensions {
        let mut line = vec![0_u64; dimension];
        for base in (0..values.len()).step_by(stride * dimension) {
            for offset in 0..stride {
                for index in 0..dimension {
                    line[index] = values[base + offset + index * stride];
                }
                ntt(&mut line, modulus);
                for index in 0..dimension {
                    values[base + offset + index * stride] = line[index];
                }
            }
        }
        stride *= dimension;
    }
}

fn ntt(values: &mut [u64], modulus: u64) {
    let length = values.len();
    let mut target = 0;
    for index in 1..length {
        let mut bit = length >> 1;
        while target & bit != 0 {
            target ^= bit;
            bit >>= 1;
        }
        target ^= bit;
        if index < target {
            values.swap(index, target);
        }
    }
    let mut width = 2;
    while width <= length {
        let root = mod_pow(PRIMITIVE_ROOT, (modulus - 1) / width as u64, modulus);
        for start in (0..length).step_by(width) {
            let mut power = 1;
            for offset in 0..width / 2 {
                let left = values[start + offset];
                let right = multiply_mod(values[start + offset + width / 2], power, modulus);
                values[start + offset] = add_mod(left, right, modulus);
                values[start + offset + width / 2] = subtract_mod(left, right, modulus);
                power = multiply_mod(power, root, modulus);
            }
        }
        width *= 2;
    }
}

fn crt(first: u64, first_modulus: u64, second: u64, second_modulus: u64) -> Result<u128, String> {
    let delta = subtract_mod(second, first % second_modulus, second_modulus);
    let inverse = mod_pow(
        first_modulus % second_modulus,
        second_modulus - 2,
        second_modulus,
    );
    let multiplier = multiply_mod(delta, inverse, second_modulus);
    let recovered = u128::from(first) + u128::from(first_modulus) * u128::from(multiplier);
    if recovered % u128::from(first_modulus) != u128::from(first)
        || recovered % u128::from(second_modulus) != u128::from(second)
    {
        return Err("CRT reconstruction failed its residue check".to_owned());
    }
    Ok(recovered)
}

fn mod_pow(mut base: u64, mut exponent: u64, modulus: u64) -> u64 {
    let mut result = 1_u64;
    while exponent != 0 {
        if exponent & 1 != 0 {
            result = multiply_mod(result, base, modulus);
        }
        base = multiply_mod(base, base, modulus);
        exponent >>= 1;
    }
    result
}

fn multiply_mod(left: u64, right: u64, modulus: u64) -> u64 {
    match u64::try_from((u128::from(left) * u128::from(right)) % u128::from(modulus)) {
        Ok(value) => value,
        Err(_) => unreachable!("a remainder modulo u64 must fit u64"),
    }
}

fn add_mod(left: u64, right: u64, modulus: u64) -> u64 {
    let sum = left + right;
    if sum >= modulus { sum - modulus } else { sum }
}

fn subtract_mod(left: u64, right: u64, modulus: u64) -> u64 {
    if left >= right {
        left - right
    } else {
        left + modulus - right
    }
}
