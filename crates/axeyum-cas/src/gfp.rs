//! Univariate polynomial arithmetic over a prime finite field 𝔽ₚ.
//!
//! A small, self-contained toolbox for computing with polynomials whose
//! coefficients live in the field of integers modulo a prime `p`. It is
//! deliberately independent of the symbolic `CasExpr` layer: everything here
//! speaks only in terms of coefficient vectors, so it can serve as a trusted
//! numerical kernel for factorization, root finding and irreducibility testing.
//!
//! # Representation
//!
//! A polynomial is a coefficient vector stored **least-significant coefficient
//! first**: `vec![c0, c1, c2]` denotes `c0 + c1·x + c2·x²`. Every coefficient is
//! kept reduced into the canonical range `0..p`, and trailing (high-degree) zero
//! coefficients are trimmed, so the zero polynomial is the empty vector and the
//! leading coefficient of a non-zero polynomial is always its last entry. The
//! functions accept slices and re-normalize their inputs, so callers may pass
//! unreduced or untrimmed data freely.
//!
//! # Overflow discipline
//!
//! Every routine is written to **never panic on overflow** and never uses
//! `unsafe`. Coefficient arithmetic runs through overflow-safe modular add,
//! subtract and multiply helpers that are correct for any prime `p` up to
//! `i128::MAX`. Operations whose result may not exist (division by the zero
//! polynomial, factoring the zero polynomial, a modulus that is too large for
//! the Frobenius map) return [`Option`] rather than panicking.
//!
//! # Limitations
//!
//! The irreducibility test and Berlekamp factorization apply the Frobenius map
//! `y ↦ yᵖ`, which requires raising to the `p`-th power; this needs `p` to fit
//! in a `u64`, and the Berlekamp splitting step iterates over the field, so both
//! are intended for the small-to-moderate primes that arise in practice. When
//! `p` does not fit in a `u64` these routines return `None` (or an empty result
//! for [`roots`]) rather than attempting an infeasible computation.

use crate::ntheory::{is_prime, mod_inverse};
use core::cmp::Ordering;

// ---------------------------------------------------------------------------
// Overflow-safe coefficient arithmetic
// ---------------------------------------------------------------------------

/// Modular multiplication `(left · right) mod modulus` on `u128`, overflow-safe.
///
/// For moduli that fit in a `u64` a single widening `u128` multiply suffices;
/// larger moduli fall back to a binary double-and-add so the running sum never
/// exceeds `2^128`.
fn mul_mod_u128(left: u128, right: u128, modulus: u128) -> u128 {
    if modulus <= u128::from(u64::MAX) {
        return (left % modulus) * (right % modulus) % modulus;
    }
    let mut result: u128 = 0;
    let mut addend = left % modulus;
    let mut multiplier = right % modulus;
    while multiplier > 0 {
        if multiplier & 1 == 1 {
            result = (result + addend) % modulus;
        }
        addend = (addend + addend) % modulus;
        multiplier >>= 1;
    }
    result
}

/// Modular product of two coefficients, reduced into `0..p`.
///
/// Overflow-safe for every prime `p` up to `i128::MAX`.
fn mul_coeff(left: i128, right: i128, p: i128) -> i128 {
    let modulus = p.unsigned_abs();
    let left_u = left.rem_euclid(p).unsigned_abs();
    let right_u = right.rem_euclid(p).unsigned_abs();
    // The product is below `p`, hence representable as an `i128`.
    i128::try_from(mul_mod_u128(left_u, right_u, modulus)).unwrap_or(0)
}

/// Modular sum of two coefficients, reduced into `0..p`, without overflowing.
fn add_coeff(left: i128, right: i128, p: i128) -> i128 {
    let left = left.rem_euclid(p);
    let right = right.rem_euclid(p);
    // Both operands are below `p`, so exactly one of the branches stays in range.
    if left < p - right {
        left + right
    } else {
        left - (p - right)
    }
}

/// Modular difference `(left - right) mod p`, reduced into `0..p`.
fn sub_coeff(left: i128, right: i128, p: i128) -> i128 {
    let left = left.rem_euclid(p);
    let right = right.rem_euclid(p);
    if left >= right {
        left - right
    } else {
        // `left < right < p`, so `left + (p - right)` stays below `p`.
        left + (p - right)
    }
}

// ---------------------------------------------------------------------------
// Normalization helpers
// ---------------------------------------------------------------------------

/// Drop trailing (high-degree) zero coefficients in place.
fn trim(coeffs: &mut Vec<i128>) {
    while let Some(&last) = coeffs.last() {
        if last == 0 {
            coeffs.pop();
        } else {
            break;
        }
    }
}

/// Reduce every coefficient into `0..p` and trim trailing zeros.
fn reduce(coeffs: &[i128], p: i128) -> Vec<i128> {
    let mut result: Vec<i128> = coeffs.iter().map(|&value| value.rem_euclid(p)).collect();
    trim(&mut result);
    result
}

/// Degree of a trimmed polynomial, or `None` for the zero polynomial.
fn degree(coeffs: &[i128]) -> Option<usize> {
    coeffs.len().checked_sub(1)
}

/// Make a polynomial monic (leading coefficient `1`) over 𝔽ₚ.
///
/// Returns the empty (zero) polynomial unchanged; for a non-zero polynomial the
/// leading coefficient of a prime field is always invertible.
fn make_monic(coeffs: &[i128], p: i128) -> Vec<i128> {
    let reduced = reduce(coeffs, p);
    match degree(&reduced) {
        None => Vec::new(),
        Some(lead) => match mod_inverse(reduced[lead], p) {
            Some(inverse) => scale(&reduced, inverse, p),
            None => reduced,
        },
    }
}

// ---------------------------------------------------------------------------
// Ring operations
// ---------------------------------------------------------------------------

/// Add two polynomials over 𝔽ₚ.
///
/// # Examples
///
/// ```
/// use axeyum_cas::gfp::add;
/// // (1 + 2x + 3x²) + (4 + 4x) over 𝔽₅ = 3x² + x   (LSB-first)
/// assert_eq!(add(&[1, 2, 3], &[4, 4], 5), vec![0, 1, 3]);
/// ```
#[must_use]
pub fn add(a: &[i128], b: &[i128], p: i128) -> Vec<i128> {
    let length = a.len().max(b.len());
    let mut result = Vec::with_capacity(length);
    for index in 0..length {
        let left = a.get(index).copied().unwrap_or(0);
        let right = b.get(index).copied().unwrap_or(0);
        result.push(add_coeff(left, right, p));
    }
    trim(&mut result);
    result
}

/// Subtract `b` from `a` over 𝔽ₚ.
///
/// # Examples
///
/// ```
/// use axeyum_cas::gfp::sub;
/// // (x) - (2) over 𝔽₅ = x + 3   (since -2 ≡ 3)
/// assert_eq!(sub(&[0, 1], &[2], 5), vec![3, 1]);
/// ```
#[must_use]
pub fn sub(a: &[i128], b: &[i128], p: i128) -> Vec<i128> {
    let length = a.len().max(b.len());
    let mut result = Vec::with_capacity(length);
    for index in 0..length {
        let left = a.get(index).copied().unwrap_or(0);
        let right = b.get(index).copied().unwrap_or(0);
        result.push(sub_coeff(left, right, p));
    }
    trim(&mut result);
    result
}

/// Multiply two polynomials over 𝔽ₚ (schoolbook convolution).
///
/// # Examples
///
/// ```
/// use axeyum_cas::gfp::mul;
/// // (x + 1)(x + 4) = x² + 4 over 𝔽₅   (5x ≡ 0)
/// assert_eq!(mul(&[1, 1], &[4, 1], 5), vec![4, 0, 1]);
/// ```
#[must_use]
pub fn mul(a: &[i128], b: &[i128], p: i128) -> Vec<i128> {
    let a = reduce(a, p);
    let b = reduce(b, p);
    if a.is_empty() || b.is_empty() {
        return Vec::new();
    }
    let mut result = vec![0i128; a.len() + b.len() - 1];
    for (pos_a, &coeff_a) in a.iter().enumerate() {
        for (pos_b, &coeff_b) in b.iter().enumerate() {
            let term = mul_coeff(coeff_a, coeff_b, p);
            result[pos_a + pos_b] = add_coeff(result[pos_a + pos_b], term, p);
        }
    }
    trim(&mut result);
    result
}

/// Multiply a polynomial by a scalar `c` over 𝔽ₚ.
///
/// # Examples
///
/// ```
/// use axeyum_cas::gfp::scale;
/// // 3·(1 + 2x) = 3 + 6x ≡ 3 + x over 𝔽₅
/// assert_eq!(scale(&[1, 2], 3, 5), vec![3, 1]);
/// ```
#[must_use]
pub fn scale(a: &[i128], c: i128, p: i128) -> Vec<i128> {
    let mut result: Vec<i128> = a.iter().map(|&coeff| mul_coeff(coeff, c, p)).collect();
    trim(&mut result);
    result
}

/// Negate a polynomial over 𝔽ₚ.
///
/// # Examples
///
/// ```
/// use axeyum_cas::gfp::neg;
/// // -(1 + 2x) ≡ 4 + 3x over 𝔽₅
/// assert_eq!(neg(&[1, 2], 5), vec![4, 3]);
/// ```
#[must_use]
pub fn neg(a: &[i128], p: i128) -> Vec<i128> {
    let mut result: Vec<i128> = a
        .iter()
        .map(|&coeff| {
            let reduced = coeff.rem_euclid(p);
            if reduced == 0 { 0 } else { p - reduced }
        })
        .collect();
    trim(&mut result);
    result
}

/// Polynomial division with remainder over 𝔽ₚ.
///
/// Returns `(quotient, remainder)` with `a = quotient·b + remainder` and
/// `deg(remainder) < deg(b)`. Requires the leading coefficient of `b` to be
/// invertible modulo `p` (automatic for a prime modulus and non-zero `b`).
/// Returns `None` when `b` is the zero polynomial.
///
/// # Examples
///
/// ```
/// use axeyum_cas::gfp::div_rem;
/// // (x² + 4) / (x + 4) = (x + 1) remainder 0 over 𝔽₅
/// assert_eq!(div_rem(&[4, 0, 1], &[4, 1], 5), Some((vec![1, 1], vec![])));
/// ```
pub fn div_rem(a: &[i128], b: &[i128], p: i128) -> Option<(Vec<i128>, Vec<i128>)> {
    let mut remainder = reduce(a, p);
    let divisor = reduce(b, p);
    let divisor_deg = degree(&divisor)?;
    let lead_inverse = mod_inverse(divisor[divisor_deg], p)?;
    let mut quotient: Vec<i128> = Vec::new();
    while let Some(rem_deg) = degree(&remainder) {
        if rem_deg < divisor_deg {
            break;
        }
        let shift = rem_deg - divisor_deg;
        let factor = mul_coeff(remainder[rem_deg], lead_inverse, p);
        if quotient.len() <= shift {
            quotient.resize(shift + 1, 0);
        }
        quotient[shift] = factor;
        for (pos, &divisor_coeff) in divisor.iter().enumerate() {
            let term = mul_coeff(factor, divisor_coeff, p);
            remainder[pos + shift] = sub_coeff(remainder[pos + shift], term, p);
        }
        trim(&mut remainder);
    }
    trim(&mut quotient);
    Some((quotient, remainder))
}

/// Monic greatest common divisor of `a` and `b` over 𝔽ₚ (Euclidean algorithm).
///
/// The result is monic (or the empty polynomial when both inputs are zero).
///
/// # Examples
///
/// ```
/// use axeyum_cas::gfp::gcd;
/// // gcd(x² + 4, x + 4) = x + 4 over 𝔽₅  ((x+4) divides x²+4)
/// assert_eq!(gcd(&[4, 0, 1], &[4, 1], 5), vec![4, 1]);
/// ```
#[must_use]
pub fn gcd(a: &[i128], b: &[i128], p: i128) -> Vec<i128> {
    let mut first = reduce(a, p);
    let mut second = reduce(b, p);
    while !second.is_empty() {
        match div_rem(&first, &second, p) {
            Some((_, remainder)) => {
                first = second;
                second = remainder;
            }
            None => break,
        }
    }
    make_monic(&first, p)
}

/// Multiply `a·b` and reduce modulo `modulus` in 𝔽ₚ[x].
///
/// Returns `None` only when `modulus` is the zero polynomial.
fn mul_mod_poly(a: &[i128], b: &[i128], modulus: &[i128], p: i128) -> Option<Vec<i128>> {
    let product = mul(a, b, p);
    Some(div_rem(&product, modulus, p)?.1)
}

/// Modular exponentiation `a^e mod modulus` in 𝔽ₚ[x] by repeated squaring.
///
/// Used to apply the Frobenius map when testing irreducibility and factoring.
/// Returns `None` when `modulus` is the zero polynomial.
///
/// # Examples
///
/// ```
/// use axeyum_cas::gfp::pow_mod;
/// // x² ≡ x + 1 (mod x² + x + 1) over 𝔽₂
/// assert_eq!(pow_mod(&[0, 1], 2, &[1, 1, 1], 2), Some(vec![1, 1]));
/// ```
pub fn pow_mod(a: &[i128], e: u64, modulus: &[i128], p: i128) -> Option<Vec<i128>> {
    let modulus = reduce(modulus, p);
    degree(&modulus)?;
    let mut base = div_rem(a, &modulus, p)?.1;
    let mut result = div_rem(&[1], &modulus, p)?.1;
    let mut exponent = e;
    while exponent > 0 {
        if exponent & 1 == 1 {
            result = mul_mod_poly(&result, &base, &modulus, p)?;
        }
        base = mul_mod_poly(&base, &base, &modulus, p)?;
        exponent >>= 1;
    }
    Some(result)
}

// ---------------------------------------------------------------------------
// Irreducibility (Rabin's test)
// ---------------------------------------------------------------------------

/// Distinct prime divisors of `n`, ascending, via trial division.
fn distinct_prime_factors(mut n: usize) -> Vec<usize> {
    let mut result = Vec::new();
    let mut divisor = 2usize;
    while divisor.saturating_mul(divisor) <= n {
        if n.is_multiple_of(divisor) {
            result.push(divisor);
            while n.is_multiple_of(divisor) {
                n /= divisor;
            }
        }
        divisor += 1;
    }
    if n > 1 {
        result.push(n);
    }
    result
}

/// Apply the Frobenius map `steps` times: `x^{p^steps} mod modulus` in 𝔽ₚ[x].
fn frobenius_power(steps: usize, exponent: u64, modulus: &[i128], p: i128) -> Option<Vec<i128>> {
    let start = [0i128, 1];
    let mut current = div_rem(&start, modulus, p)?.1;
    for _ in 0..steps {
        current = pow_mod(&current, exponent, modulus, p)?;
    }
    Some(current)
}

/// Test whether `a` is irreducible over 𝔽ₚ using Rabin's test.
///
/// For a monic polynomial `a` of degree `n ≥ 1`, `a` is irreducible iff
/// `x^{pⁿ} ≡ x (mod a)` and, for every prime `q` dividing `n`,
/// `gcd(x^{p^{n/q}} - x, a) = 1`.
///
/// Returns `None` when `p` is not prime, when `a` is zero or a non-zero
/// constant (irreducibility is undefined there), or when `p` does not fit in a
/// `u64` (see the module-level limitations).
///
/// # Examples
///
/// ```
/// use axeyum_cas::gfp::is_irreducible;
/// // x³ + x + 1 is irreducible over 𝔽₂
/// assert_eq!(is_irreducible(&[1, 1, 0, 1], 2), Some(true));
/// // x² + 1 = (x + 2)(x + 3) is reducible over 𝔽₅
/// assert_eq!(is_irreducible(&[1, 0, 1], 5), Some(false));
/// // x² + 2 is irreducible over 𝔽₅ (2 is a non-residue)
/// assert_eq!(is_irreducible(&[2, 0, 1], 5), Some(true));
/// ```
pub fn is_irreducible(a: &[i128], p: i128) -> Option<bool> {
    if !is_prime(p) {
        return None;
    }
    let poly = make_monic(a, p);
    let degree_n = degree(&poly)?;
    if degree_n == 0 {
        return None;
    }
    if degree_n == 1 {
        return Some(true);
    }
    let exponent = u64::try_from(p).ok()?;
    let x = [0i128, 1];
    let x_mod = div_rem(&x, &poly, p)?.1;
    for prime in distinct_prime_factors(degree_n) {
        let steps = degree_n / prime;
        let power = frobenius_power(steps, exponent, &poly, p)?;
        let difference = sub(&power, &x, p);
        let common = gcd(&poly, &difference, p);
        if degree(&common) != Some(0) {
            return Some(false);
        }
    }
    let full = frobenius_power(degree_n, exponent, &poly, p)?;
    Some(full == x_mod)
}

// ---------------------------------------------------------------------------
// Berlekamp factorization
// ---------------------------------------------------------------------------

/// Formal derivative of a polynomial over 𝔽ₚ.
fn derivative(a: &[i128], p: i128) -> Vec<i128> {
    let reduced = reduce(a, p);
    let mut result = Vec::new();
    for (index, &coeff) in reduced.iter().enumerate().skip(1) {
        let multiplier = i128::try_from(index).unwrap_or(0);
        result.push(mul_coeff(coeff, multiplier, p));
    }
    trim(&mut result);
    result
}

/// Extract the `p`-th root of a polynomial that is a perfect `p`-th power.
///
/// Such a polynomial has non-zero coefficients only at exponents divisible by
/// `p`; since every element of 𝔽ₚ is its own `p`-th root, the root's `j`-th
/// coefficient is the input's `(p·j)`-th coefficient. Returns `None` when `p`
/// does not fit in a `usize`.
fn pth_root(a: &[i128], p: i128) -> Option<Vec<i128>> {
    let step = usize::try_from(p).ok()?;
    let reduced = reduce(a, p);
    let mut result = Vec::new();
    let mut index = 0;
    while index < reduced.len() {
        result.push(reduced[index]);
        index += step;
    }
    trim(&mut result);
    Some(result)
}

/// Squarefree factorization of a monic polynomial over 𝔽ₚ.
///
/// Returns pairs `(squarefree_factor, multiplicity)` such that the product of
/// `squarefree_factor^multiplicity` equals the (monic) input. Each returned
/// factor is a squarefree product of the distinct irreducibles that occur in
/// the input with exactly that multiplicity. Handles the characteristic-`p`
/// case where the derivative vanishes.
fn squarefree_factorization(a: &[i128], p: i128) -> Option<Vec<(Vec<i128>, u32)>> {
    let f = make_monic(a, p);
    let mut result: Vec<(Vec<i128>, u32)> = Vec::new();
    match degree(&f) {
        None | Some(0) => return Some(result),
        Some(_) => {}
    }
    let deriv = derivative(&f, p);
    if deriv.is_empty() {
        // The derivative vanishes: `f` is a perfect `p`-th power.
        append_pth_power(&f, p, &mut result)?;
        return Some(result);
    }
    let mut repeated = gcd(&f, &deriv, p);
    let mut squarefree = div_rem(&f, &repeated, p)?.0;
    let mut multiplicity: u32 = 1;
    while degree(&squarefree).is_some_and(|deg| deg >= 1) {
        let shared = gcd(&squarefree, &repeated, p);
        let exact = div_rem(&squarefree, &shared, p)?.0;
        if degree(&exact).is_some_and(|deg| deg >= 1) {
            result.push((make_monic(&exact, p), multiplicity));
        }
        squarefree = shared;
        repeated = div_rem(&repeated, &squarefree, p)?.0;
        multiplicity += 1;
    }
    if degree(&repeated).is_some_and(|deg| deg >= 1) {
        // Whatever remains is a perfect `p`-th power.
        append_pth_power(&repeated, p, &mut result)?;
    }
    Some(result)
}

/// Factor a perfect `p`-th power and fold its factors (with multiplicities
/// scaled by `p`) into `result`.
fn append_pth_power(a: &[i128], p: i128, result: &mut Vec<(Vec<i128>, u32)>) -> Option<()> {
    let root = pth_root(a, p)?;
    let scale_factor = u32::try_from(p).ok()?;
    for (factor, multiplicity) in squarefree_factorization(&root, p)? {
        let scaled = multiplicity.checked_mul(scale_factor)?;
        result.push((factor, scaled));
    }
    Some(())
}

/// Order polynomials by degree, then lexicographically by coefficients.
fn compare_poly(left: &[i128], right: &[i128]) -> Ordering {
    left.len().cmp(&right.len()).then_with(|| left.cmp(right))
}

/// Right null-space basis of a square matrix over 𝔽ₚ (Gaussian elimination).
fn null_space(matrix: &[Vec<i128>], p: i128) -> Option<Vec<Vec<i128>>> {
    let rows = matrix.len();
    let cols = matrix.first().map_or(0, Vec::len);
    let mut work: Vec<Vec<i128>> = matrix.to_vec();
    let mut pivot_cols: Vec<usize> = Vec::new();
    let mut pivot_row = 0;
    for col in 0..cols {
        if pivot_row >= rows {
            break;
        }
        let Some(found) =
            (pivot_row..rows).find(|&candidate| work[candidate][col].rem_euclid(p) != 0)
        else {
            continue;
        };
        work.swap(pivot_row, found);
        let inverse = mod_inverse(work[pivot_row][col], p)?;
        for value in &mut work[pivot_row] {
            *value = mul_coeff(*value, inverse, p);
        }
        let pivot_values = work[pivot_row].clone();
        for (other, row) in work.iter_mut().enumerate() {
            if other == pivot_row {
                continue;
            }
            let factor = row[col].rem_euclid(p);
            if factor == 0 {
                continue;
            }
            for column in 0..cols {
                let term = mul_coeff(factor, pivot_values[column], p);
                row[column] = sub_coeff(row[column], term, p);
            }
        }
        pivot_cols.push(col);
        pivot_row += 1;
    }
    let mut basis: Vec<Vec<i128>> = Vec::new();
    for free_col in 0..cols {
        if pivot_cols.contains(&free_col) {
            continue;
        }
        let mut vector = vec![0i128; cols];
        vector[free_col] = 1;
        for (row_index, &pivot_col) in pivot_cols.iter().enumerate() {
            let value = work[row_index][free_col].rem_euclid(p);
            vector[pivot_col] = if value == 0 { 0 } else { p - value };
        }
        basis.push(vector);
    }
    Some(basis)
}

/// Berlekamp subalgebra basis for a squarefree monic `f` of degree `n ≥ 2`.
///
/// Returns a basis of the space of polynomials `g` with `g^p ≡ g (mod f)`; its
/// size equals the number of distinct irreducible factors of `f`.
fn berlekamp_basis(f: &[i128], p: i128) -> Option<Vec<Vec<i128>>> {
    let n = degree(f)?;
    let exponent = u64::try_from(p).ok()?;
    let x = [0i128, 1];
    let x_to_p = pow_mod(&x, exponent, f, p)?;
    // Row `k` of `q_rows` holds `x^{p·k} mod f`, padded to length `n`.
    let mut q_rows: Vec<Vec<i128>> = Vec::with_capacity(n);
    let mut current = div_rem(&[1], f, p)?.1;
    for _ in 0..n {
        let mut row = current.clone();
        row.resize(n, 0);
        q_rows.push(row);
        current = mul_mod_poly(&current, &x_to_p, f, p)?;
    }
    // Build `M = (Q - I)^T` so that its right null space is the Berlekamp basis.
    let mut matrix = vec![vec![0i128; n]; n];
    for (row_index, matrix_row) in matrix.iter_mut().enumerate() {
        for (col_index, entry) in matrix_row.iter_mut().enumerate() {
            let mut value = q_rows[col_index][row_index];
            if row_index == col_index {
                value = sub_coeff(value, 1, p);
            }
            *entry = value.rem_euclid(p);
        }
    }
    null_space(&matrix, p)
}

/// Split a squarefree monic polynomial into its distinct monic irreducibles.
fn berlekamp_factors(f: &[i128], p: i128) -> Option<Vec<Vec<i128>>> {
    let f = make_monic(f, p);
    let n = degree(&f)?;
    if n == 0 {
        return Some(Vec::new());
    }
    if n == 1 {
        return Some(vec![f]);
    }
    let basis = berlekamp_basis(&f, p)?;
    let target = basis.len();
    if target <= 1 {
        return Some(vec![f]);
    }
    let mut factors: Vec<Vec<i128>> = vec![f];
    for g in &basis {
        if factors.len() >= target {
            break;
        }
        if degree(g).is_none_or(|deg| deg < 1) {
            continue;
        }
        let mut candidate = 0i128;
        while candidate < p && factors.len() < target {
            let shifted = sub(g, &[candidate], p);
            factors = split_with(&factors, &shifted, p)?;
            candidate += 1;
        }
    }
    factors.sort_by(|left, right| compare_poly(left, right));
    Some(factors)
}

/// Refine a factor list by taking gcds against `shifted` over 𝔽ₚ.
fn split_with(factors: &[Vec<i128>], shifted: &[i128], p: i128) -> Option<Vec<Vec<i128>>> {
    let mut next: Vec<Vec<i128>> = Vec::with_capacity(factors.len());
    for factor in factors {
        if degree(factor).is_some_and(|deg| deg <= 1) {
            next.push(factor.clone());
            continue;
        }
        let common = gcd(factor, shifted, p);
        let common_deg = degree(&common);
        let factor_deg = degree(factor);
        if common_deg.is_some_and(|deg| deg >= 1) && common_deg < factor_deg {
            let quotient = div_rem(factor, &common, p)?.0;
            next.push(make_monic(&common, p));
            next.push(make_monic(&quotient, p));
        } else {
            next.push(factor.clone());
        }
    }
    Some(next)
}

/// Factor a polynomial into monic irreducibles over 𝔽ₚ (Berlekamp's algorithm).
///
/// Returns pairs `(irreducible, multiplicity)` whose product of
/// `irreducible^multiplicity` equals the monic form of `a`. Multiplicities come
/// from a squarefree decomposition; each squarefree part is split into distinct
/// irreducibles by Berlekamp's algorithm (Q-matrix null space plus gcd
/// splitting). Factors are sorted by degree then lexicographically.
///
/// Returns `None` when `p` is not prime, when `a` is the zero polynomial, or
/// when `p` is too large for the Frobenius map (see the module limitations).
/// A non-zero constant factors into the empty list.
///
/// # Examples
///
/// ```
/// use axeyum_cas::gfp::factor_berlekamp;
/// // x² + 1 = (x + 2)(x + 3) over 𝔽₅
/// assert_eq!(
///     factor_berlekamp(&[1, 0, 1], 5),
///     Some(vec![(vec![2, 1], 1), (vec![3, 1], 1)])
/// );
/// ```
pub fn factor_berlekamp(a: &[i128], p: i128) -> Option<Vec<(Vec<i128>, u32)>> {
    if !is_prime(p) {
        return None;
    }
    let f = make_monic(a, p);
    match degree(&f) {
        None => return None,
        Some(0) => return Some(Vec::new()),
        Some(_) => {}
    }
    let squarefree = squarefree_factorization(&f, p)?;
    let mut result: Vec<(Vec<i128>, u32)> = Vec::new();
    for (part, multiplicity) in squarefree {
        for irreducible in berlekamp_factors(&part, p)? {
            result.push((irreducible, multiplicity));
        }
    }
    result.sort_by(|left, right| compare_poly(&left.0, &right.0).then(left.1.cmp(&right.1)));
    Some(result)
}

/// Roots of `a` in 𝔽ₚ: the elements `r` with `a(r) ≡ 0 (mod p)`.
///
/// Computes `gcd(a, xᵖ - x)`, whose linear factors correspond exactly to the
/// roots, then reads off each root. Returns an empty vector when `p` is not
/// prime, when `a` is zero or a non-zero constant, when `a` has no roots, or
/// when `p` is too large for the Frobenius map.
///
/// # Examples
///
/// ```
/// use axeyum_cas::gfp::roots;
/// // x² + x = x(x + 1) has roots {0, 1} over 𝔽₂
/// assert_eq!(roots(&[0, 1, 1], 2), vec![0, 1]);
/// ```
#[must_use]
pub fn roots(a: &[i128], p: i128) -> Vec<i128> {
    if !is_prime(p) {
        return Vec::new();
    }
    let poly = reduce(a, p);
    match degree(&poly) {
        None | Some(0) => return Vec::new(),
        Some(_) => {}
    }
    let Ok(exponent) = u64::try_from(p) else {
        return Vec::new();
    };
    let x = [0i128, 1];
    let Some(x_to_p) = pow_mod(&x, exponent, &poly, p) else {
        return Vec::new();
    };
    let linear_part = gcd(&poly, &sub(&x_to_p, &x, p), p);
    if degree(&linear_part).is_none_or(|deg| deg < 1) {
        return Vec::new();
    }
    let Some(factors) = berlekamp_factors(&linear_part, p) else {
        return Vec::new();
    };
    let mut result: Vec<i128> = factors
        .into_iter()
        .filter_map(|factor| {
            if degree(&factor) == Some(1) {
                let constant = factor.first().copied().unwrap_or(0).rem_euclid(p);
                Some(if constant == 0 { 0 } else { p - constant })
            } else {
                None
            }
        })
        .collect();
    result.sort_unstable();
    result
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Re-multiply a factorization `∏ factor^multiplicity` back into a single
    /// polynomial over 𝔽ₚ.
    fn remultiply(factors: &[(Vec<i128>, u32)], p: i128) -> Vec<i128> {
        let mut product = vec![1i128];
        for (factor, multiplicity) in factors {
            for _ in 0..*multiplicity {
                product = mul(&product, factor, p);
            }
        }
        product
    }

    #[test]
    fn ring_operations_over_f5() {
        assert_eq!(add(&[1, 2, 3], &[4, 4], 5), vec![0, 1, 3]);
        assert_eq!(sub(&[0, 1], &[2], 5), vec![3, 1]);
        assert_eq!(mul(&[1, 1], &[4, 1], 5), vec![4, 0, 1]);
        assert_eq!(scale(&[1, 2], 3, 5), vec![3, 1]);
        assert_eq!(neg(&[1, 2], 5), vec![4, 3]);
        // Adding a polynomial to its negation yields zero.
        assert_eq!(add(&[1, 2, 3], &neg(&[1, 2, 3], 5), 5), Vec::<i128>::new());
        // Multiplying by zero yields the zero polynomial.
        assert_eq!(mul(&[1, 2, 3], &[], 5), Vec::<i128>::new());
    }

    #[test]
    fn div_rem_reconstructs_dividend() {
        // (x² + 4) / (x + 4) over 𝔽₅.
        let (quotient, remainder) = div_rem(&[4, 0, 1], &[4, 1], 5).unwrap();
        assert_eq!(quotient, vec![1, 1]);
        assert_eq!(remainder, Vec::<i128>::new());
        // General reconstruction a = q·b + r with deg(r) < deg(b).
        for (dividend, divisor, p) in [
            (vec![1i128, 2, 3, 4], vec![1i128, 1], 7i128),
            (vec![6, 0, 0, 1], vec![1, 1, 1], 7),
            (vec![1, 0, 0, 0, 1], vec![2, 1], 5),
        ] {
            let (q, r) = div_rem(&dividend, &divisor, p).unwrap();
            let reconstructed = add(&mul(&q, &divisor, p), &r, p);
            assert_eq!(reconstructed, reduce(&dividend, p));
            if let Some(rdeg) = degree(&r) {
                assert!(rdeg < degree(&divisor).unwrap());
            }
        }
        // Division by the zero polynomial is undefined.
        assert_eq!(div_rem(&[1, 2, 3], &[], 5), None);
    }

    #[test]
    fn gcd_sanity() {
        // (x + 4) divides x² + 4 over 𝔽₅.
        assert_eq!(gcd(&[4, 0, 1], &[4, 1], 5), vec![4, 1]);
        // gcd of coprime polynomials is the monic constant 1.
        assert_eq!(gcd(&[2, 0, 1], &[1, 1], 5), vec![1]);
        // gcd((x+1)(x+2), (x+1)(x+3)) = (x + 1) over 𝔽₅.
        let left = mul(&[1, 1], &[2, 1], 5);
        let right = mul(&[1, 1], &[3, 1], 5);
        assert_eq!(gcd(&left, &right, 5), vec![1, 1]);
        // gcd with zero returns the monic form of the other argument.
        assert_eq!(gcd(&[2, 0, 4], &[], 5), vec![3, 0, 1]);
    }

    #[test]
    fn pow_mod_frobenius() {
        // x² ≡ x + 1 (mod x² + x + 1) over 𝔽₂.
        assert_eq!(pow_mod(&[0, 1], 2, &[1, 1, 1], 2), Some(vec![1, 1]));
        // x⁴ ≡ x (mod x² + x + 1) over 𝔽₂ (order-3 Frobenius orbit closes).
        assert_eq!(pow_mod(&[0, 1], 4, &[1, 1, 1], 2), Some(vec![0, 1]));
        // Modulus zero is rejected.
        assert_eq!(pow_mod(&[0, 1], 2, &[], 2), None);
    }

    #[test]
    fn is_irreducible_known_cases() {
        // x³ + x + 1 is irreducible over 𝔽₂.
        assert_eq!(is_irreducible(&[1, 1, 0, 1], 2), Some(true));
        // x² + x = x(x + 1) is reducible over 𝔽₂.
        assert_eq!(is_irreducible(&[0, 1, 1], 2), Some(false));
        // x² + 2 is irreducible over 𝔽₅ (2 is a quadratic non-residue).
        assert_eq!(is_irreducible(&[2, 0, 1], 5), Some(true));
        // x² + 1 = (x + 2)(x + 3) is reducible over 𝔽₅.
        assert_eq!(is_irreducible(&[1, 0, 1], 5), Some(false));
        // x² - 2 = (x - 3)(x + 3) is reducible over 𝔽₇ (2 is a residue: 3² = 2).
        assert_eq!(is_irreducible(&[-2, 0, 1], 7), Some(false));
        // Linear polynomials are always irreducible.
        assert_eq!(is_irreducible(&[3, 1], 7), Some(true));
        // Undefined cases.
        assert_eq!(is_irreducible(&[1], 5), None); // non-zero constant
        assert_eq!(is_irreducible(&[1, 0, 1], 4), None); // 4 is not prime
    }

    #[test]
    fn roots_known_cases() {
        // x² + x over 𝔽₂ has roots {0, 1}.
        assert_eq!(roots(&[0, 1, 1], 2), vec![0, 1]);
        // x² + 1 over 𝔽₅ has roots {2, 3}.
        assert_eq!(roots(&[1, 0, 1], 5), vec![2, 3]);
        // x² - 2 over 𝔽₇ has roots {3, 4}.
        assert_eq!(roots(&[-2, 0, 1], 7), vec![3, 4]);
        // x² + 2 over 𝔽₅ is irreducible: no roots.
        assert_eq!(roots(&[2, 0, 1], 5), Vec::<i128>::new());
        // A root really is a root.
        for &r in &roots(&[-2, 0, 1], 7) {
            // Evaluate x² - 2 at r: r² - 2 ≡ 0 (mod 7).
            let value = sub_coeff(mul_coeff(r, r, 7), 2, 7);
            assert_eq!(value, 0);
        }
    }

    #[test]
    fn factor_over_f2() {
        // x² + x = x(x + 1) over 𝔽₂.
        let factors = factor_berlekamp(&[0, 1, 1], 2).unwrap();
        assert_eq!(factors, vec![(vec![0, 1], 1), (vec![1, 1], 1)]);
        assert_eq!(remultiply(&factors, 2), make_monic(&[0, 1, 1], 2));
    }

    #[test]
    fn factor_over_f5_and_f7() {
        // x² + 1 = (x + 2)(x + 3) over 𝔽₅.
        let f5 = factor_berlekamp(&[1, 0, 1], 5).unwrap();
        assert_eq!(f5, vec![(vec![2, 1], 1), (vec![3, 1], 1)]);
        assert_eq!(remultiply(&f5, 5), make_monic(&[1, 0, 1], 5));
        // x² - 2 = (x + 3)(x + 4) over 𝔽₇ (roots 3 and 4).
        let f7 = factor_berlekamp(&[-2, 0, 1], 7).unwrap();
        assert_eq!(f7, vec![(vec![3, 1], 1), (vec![4, 1], 1)]);
        assert_eq!(remultiply(&f7, 7), make_monic(&[-2, 0, 1], 7));
    }

    #[test]
    fn factor_with_multiplicity() {
        // (x + 1)² = x² + 1 over 𝔽₂.
        let factors = factor_berlekamp(&[1, 0, 1], 2).unwrap();
        assert_eq!(factors, vec![(vec![1, 1], 2)]);
        assert_eq!(remultiply(&factors, 2), make_monic(&[1, 0, 1], 2));
        // x³ + x² = x²(x + 1) over 𝔽₂: factor x with multiplicity 2, (x+1) once.
        let cubic = factor_berlekamp(&[0, 0, 1, 1], 2).unwrap();
        assert_eq!(cubic, vec![(vec![0, 1], 2), (vec![1, 1], 1)]);
        assert_eq!(remultiply(&cubic, 2), make_monic(&[0, 0, 1, 1], 2));
    }

    #[test]
    fn factor_irreducible_and_constant() {
        // An irreducible cubic factors as itself with multiplicity one.
        let irreducible = factor_berlekamp(&[1, 1, 0, 1], 2).unwrap();
        assert_eq!(irreducible, vec![(vec![1, 1, 0, 1], 1)]);
        // Non-zero constant: empty factor list.
        assert_eq!(factor_berlekamp(&[3], 5), Some(Vec::new()));
        // Zero polynomial cannot be factored; non-prime modulus rejected.
        assert_eq!(factor_berlekamp(&[], 5), None);
        assert_eq!(factor_berlekamp(&[1, 0, 1], 6), None);
    }

    #[test]
    fn factorization_reproduces_input() {
        // Cross-check: build products of linears and irreducibles, factor, and
        // confirm re-multiplication reproduces the monic input.
        let cases: &[(&[i128], i128)] = &[
            (&[6, 11, 6, 1], 7),   // (x+1)(x+2)(x+3)
            (&[1, 0, 0, 0, 1], 5), // x⁴ + 1
            (&[0, 0, 0, 1, 1], 3), // x³(x + 1) shifted -> x⁴ + x³
            (&[1, 1, 1, 1, 1], 2), // x⁴ + x³ + x² + x + 1
            (&[4, 0, 0, 0, 1], 5), // x⁴ + 4
        ];
        for &(poly, p) in cases {
            let factors =
                factor_berlekamp(poly, p).unwrap_or_else(|| panic!("factor {poly:?} over F{p}"));
            let expected = make_monic(poly, p);
            assert_eq!(
                remultiply(&factors, p),
                expected,
                "re-multiply mismatch for {poly:?} over F{p}"
            );
            // Every returned factor must itself be irreducible.
            for (factor, _) in &factors {
                assert_eq!(
                    is_irreducible(factor, p),
                    Some(true),
                    "factor {factor:?} of {poly:?} over F{p} should be irreducible"
                );
            }
        }
    }

    #[test]
    fn coefficient_reduction_is_canonical() {
        // Inputs with out-of-range and negative coefficients are normalized.
        assert_eq!(add(&[7, -1], &[0, 0], 5), vec![2, 4]);
        assert_eq!(mul(&[-1], &[-1], 5), vec![1]);
        assert_eq!(scale(&[3], 10, 5), Vec::<i128>::new()); // 30 ≡ 0
    }
}
