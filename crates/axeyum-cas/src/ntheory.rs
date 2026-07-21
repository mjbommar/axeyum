//! Exact integer number theory over `i128` — overflow-safe primitives.
//!
//! A small, dependency-free toolbox of classical number-theoretic routines used
//! by the computer-algebra layer: greatest common divisors, modular
//! exponentiation and inverses, deterministic primality testing, integer
//! factorization, divisor functions, the Chinese remainder theorem, and
//! binomial/factorial values.
//!
//! # Overflow discipline
//!
//! Every routine is written to **never panic on overflow**. Operations whose
//! mathematical result can exceed the `i128` range return [`Option`] (or, for
//! the pathological `i128::MIN` inputs of [`gcd`], saturate to `i128::MAX` — see
//! that function's note). Internally the heavy arithmetic (`Miller–Rabin`,
//! `Pollard` rho) runs on `u128` with a modular multiply that is safe for any
//! modulus below `2^127`, i.e. every positive `i128` modulus.
//!
//! # Sign conventions
//!
//! Primality, factorization and the divisor functions operate on the *absolute
//! value* of their argument (mathematical primes are the positive integers
//! greater than one). The individual functions document their edge behaviour on
//! `0`, `1` and negative inputs.

// ---------------------------------------------------------------------------
// Internal `u128` arithmetic core
// ---------------------------------------------------------------------------

/// Modular multiplication `(left * right) mod modulus`, overflow-safe.
///
/// Correct for any `modulus` in `1..2^127` (hence every positive `i128`
/// modulus). For moduli that fit in `u64` a single `u128` widening multiply is
/// used; larger moduli fall back to a binary (double-and-add) multiply so the
/// running sum never exceeds `2^128`.
fn mul_mod(left: u128, right: u128, modulus: u128) -> u128 {
    debug_assert!(modulus != 0, "mul_mod requires a non-zero modulus");
    if modulus <= u128::from(u64::MAX) {
        // Each operand reduces below `2^64`, so the product fits in `u128`.
        return (left % modulus) * (right % modulus) % modulus;
    }
    let mut result: u128 = 0;
    let mut addend = left % modulus;
    let mut multiplier = right % modulus;
    while multiplier > 0 {
        if multiplier & 1 == 1 {
            // `result` and `addend` are both below `modulus < 2^127`, so the
            // sum stays below `2^128` and cannot overflow `u128`.
            result = (result + addend) % modulus;
        }
        addend = (addend + addend) % modulus;
        multiplier >>= 1;
    }
    result
}

/// Modular exponentiation `(base ^ exponent) mod modulus` on `u128`.
///
/// Uses [`mul_mod`], so it is overflow-safe for any positive `modulus` below
/// `2^127`.
fn pow_mod(base: u128, exponent: u128, modulus: u128) -> u128 {
    if modulus == 1 {
        return 0;
    }
    let mut result: u128 = 1;
    let mut factor = base % modulus;
    let mut remaining = exponent;
    while remaining > 0 {
        if remaining & 1 == 1 {
            result = mul_mod(result, factor, modulus);
        }
        factor = mul_mod(factor, factor, modulus);
        remaining >>= 1;
    }
    result
}

/// Binary greatest common divisor on `u128` (Euclid's algorithm).
fn gcd_u128(mut first: u128, mut second: u128) -> u128 {
    while second != 0 {
        let remainder = first % second;
        first = second;
        second = remainder;
    }
    first
}

/// The 12-witness base set that makes `Miller–Rabin` deterministic well beyond
/// the full `u64` range (see [`is_prime`]).
const MILLER_RABIN_WITNESSES: [u128; 12] =
    [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37];

/// A single `Miller–Rabin` strong-probable-prime round for base `witness`.
///
/// `odd_part` and `shift_count` are the decomposition `n - 1 = odd_part *
/// 2^shift_count` with `odd_part` odd. Returns `true` when `n` passes the round.
fn miller_rabin_round(n: u128, witness: u128, odd_part: u128, shift_count: u32) -> bool {
    let mut value = pow_mod(witness, odd_part, n);
    if value == 1 || value == n - 1 {
        return true;
    }
    for _ in 1..shift_count {
        value = mul_mod(value, value, n);
        if value == n - 1 {
            return true;
        }
    }
    false
}

/// Deterministic primality test on `u128` using the fixed witness set.
fn is_prime_u128(candidate: u128) -> bool {
    if candidate < 2 {
        return false;
    }
    for &witness in &MILLER_RABIN_WITNESSES {
        if candidate == witness {
            return true;
        }
        if candidate.is_multiple_of(witness) {
            return false;
        }
    }
    // Every witness is smaller than `candidate` here, so no reduction is needed.
    let mut odd_part = candidate - 1;
    let mut shift_count: u32 = 0;
    while odd_part & 1 == 0 {
        odd_part >>= 1;
        shift_count += 1;
    }
    for &witness in &MILLER_RABIN_WITNESSES {
        if !miller_rabin_round(candidate, witness, odd_part, shift_count) {
            return false;
        }
    }
    true
}

/// `Brent`'s improvement of `Pollard`'s rho, seeded deterministically.
///
/// Returns a non-trivial factor of the odd composite `n`, or `None` when the
/// chosen polynomial parameter `increment` fails to split `n` (the caller
/// retries with the next parameter). The iteration is fully deterministic — no
/// randomness — which the surrounding runtime forbids.
fn brent(n: u128, increment: u128) -> Option<u128> {
    const BATCH: u128 = 128;
    let step = |value: u128| (mul_mod(value, value, n) + increment) % n;

    let mut anchor = 2u128;
    let mut hare = 2u128;
    let mut hare_snapshot = 2u128;
    let mut divisor = 1u128;
    let mut range = 1u128;
    let mut product = 1u128;

    while divisor == 1 {
        anchor = hare;
        for _ in 0..range {
            hare = step(hare);
        }
        let mut done = 0u128;
        while done < range && divisor == 1 {
            hare_snapshot = hare;
            let limit = BATCH.min(range - done);
            for _ in 0..limit {
                hare = step(hare);
                let diff = anchor.abs_diff(hare);
                product = mul_mod(product, diff, n);
            }
            divisor = gcd_u128(product, n);
            done += BATCH;
        }
        range *= 2;
    }

    if divisor == n {
        // The batched gcd overshot to `n`; recover by stepping one at a time.
        loop {
            hare_snapshot = step(hare_snapshot);
            let diff = anchor.abs_diff(hare_snapshot);
            divisor = gcd_u128(diff, n);
            if divisor > 1 {
                break;
            }
        }
    }

    if divisor == n || divisor == 1 {
        None
    } else {
        Some(divisor)
    }
}

/// Return a non-trivial factor of the composite `n` (`n > 1`, not prime).
fn pollard_factor(n: u128) -> u128 {
    if n.is_multiple_of(2) {
        return 2;
    }
    let mut increment = 1u128;
    loop {
        if let Some(divisor) = brent(n, increment) {
            return divisor;
        }
        increment += 1;
    }
}

/// Fully factor `n` (as `u128`), pushing prime factors with multiplicity into
/// `out`. Uses [`is_prime_u128`] as the recursion base case and
/// [`pollard_factor`] to split composites.
fn factor_recurse(n: u128, out: &mut Vec<u128>) {
    if n == 1 {
        return;
    }
    if is_prime_u128(n) {
        out.push(n);
        return;
    }
    let divisor = pollard_factor(n);
    factor_recurse(divisor, out);
    factor_recurse(n / divisor, out);
}

/// Factor the magnitude `n` into `(prime, exponent)` pairs sorted by prime.
///
/// Trial division peels off factors up to 1000, then `Pollard` rho (Brent)
/// handles the remaining part. Returns an empty vector for `n <= 1`.
fn factor_u128(n: u128) -> Vec<(u128, u32)> {
    if n <= 1 {
        return Vec::new();
    }
    let mut magnitude = n;
    let mut primes: Vec<u128> = Vec::new();

    while magnitude.is_multiple_of(2) {
        primes.push(2);
        magnitude /= 2;
    }
    let mut candidate = 3u128;
    while candidate <= 1000 && candidate * candidate <= magnitude {
        while magnitude.is_multiple_of(candidate) {
            primes.push(candidate);
            magnitude /= candidate;
        }
        candidate += 2;
    }
    if magnitude > 1 {
        factor_recurse(magnitude, &mut primes);
    }

    primes.sort_unstable();
    let mut result: Vec<(u128, u32)> = Vec::new();
    for prime in primes {
        if let Some(last) = result.last_mut()
            && last.0 == prime
        {
            last.1 += 1;
            continue;
        }
        result.push((prime, 1));
    }
    result
}

// ---------------------------------------------------------------------------
// Public API
// ---------------------------------------------------------------------------

/// Greatest common divisor of `a` and `b` (Euclid's algorithm).
///
/// The result is non-negative and `gcd(0, 0) == 0`.
///
/// # Overflow
///
/// The only value whose true gcd is not representable as an `i128` is `2^127`,
/// which can arise solely when both inputs equal `i128::MIN`. In that unique
/// case the result saturates to `i128::MAX`; the function never panics.
///
/// # Examples
///
/// ```
/// use axeyum_cas::ntheory::gcd;
/// assert_eq!(gcd(54, 24), 6);
/// assert_eq!(gcd(-54, 24), 6);
/// assert_eq!(gcd(17, 0), 17);
/// ```
#[must_use]
pub fn gcd(a: i128, b: i128) -> i128 {
    let result = gcd_u128(a.unsigned_abs(), b.unsigned_abs());
    i128::try_from(result).unwrap_or(i128::MAX)
}

/// Least common multiple of `a` and `b`, or `None` on overflow.
///
/// The result is non-negative, and `lcm(a, 0) == 0` for every `a`.
///
/// # Examples
///
/// ```
/// use axeyum_cas::ntheory::lcm;
/// assert_eq!(lcm(4, 6), Some(12));
/// assert_eq!(lcm(0, 5), Some(0));
/// assert_eq!(lcm(i128::MAX, i128::MAX - 1), None);
/// ```
#[must_use]
pub fn lcm(a: i128, b: i128) -> Option<i128> {
    if a == 0 || b == 0 {
        return Some(0);
    }
    let divisor = gcd_u128(a.unsigned_abs(), b.unsigned_abs());
    let product = (a.unsigned_abs() / divisor).checked_mul(b.unsigned_abs())?;
    i128::try_from(product).ok()
}

/// Extended Euclidean algorithm.
///
/// Returns `(g, x, y)` such that `a * x + b * y == g`, where `g` is the
/// (non-negative) greatest common divisor. The `Bezout` coefficients are
/// bounded in magnitude by the inputs, so they cannot overflow for ordinary
/// inputs; the degenerate `i128::MIN` cases (whose normalization would overflow)
/// fall back to returning the coefficients with an unnormalized sign rather than
/// panicking.
///
/// # Examples
///
/// ```
/// use axeyum_cas::ntheory::extended_gcd;
/// let (g, x, y) = extended_gcd(240, 46);
/// assert_eq!(g, 2);
/// assert_eq!(240 * x + 46 * y, g);
/// ```
#[must_use]
pub fn extended_gcd(a: i128, b: i128) -> (i128, i128, i128) {
    let (mut old_remainder, mut remainder) = (a, b);
    let (mut old_x, mut coeff_x) = (1i128, 0i128);
    let (mut old_y, mut coeff_y) = (0i128, 1i128);
    while remainder != 0 {
        let quotient = old_remainder / remainder;
        let next_remainder = old_remainder - quotient * remainder;
        old_remainder = remainder;
        remainder = next_remainder;
        let next_x = old_x - quotient * coeff_x;
        old_x = coeff_x;
        coeff_x = next_x;
        let next_y = old_y - quotient * coeff_y;
        old_y = coeff_y;
        coeff_y = next_y;
    }
    if old_remainder < 0
        && let (Some(g), Some(x), Some(y)) = (
            old_remainder.checked_neg(),
            old_x.checked_neg(),
            old_y.checked_neg(),
        )
    {
        return (g, x, y);
    }
    (old_remainder, old_x, old_y)
}

/// Modular exponentiation `(base ^ exponent) mod modulus`.
///
/// `base` may be negative (it is reduced into `0..modulus`). Returns `None` when
/// `modulus <= 0`; the result otherwise lies in `0..modulus`. Overflow-safe for
/// every positive `i128` modulus.
///
/// # Examples
///
/// ```
/// use axeyum_cas::ntheory::mod_pow;
/// assert_eq!(mod_pow(2, 10, 1000), Some(24));
/// assert_eq!(mod_pow(-3, 3, 7), Some(1)); // (-3)^3 = -27 ≡ 1 (mod 7)
/// assert_eq!(mod_pow(2, 5, 0), None);
/// ```
pub fn mod_pow(base: i128, exponent: u128, modulus: i128) -> Option<i128> {
    if modulus <= 0 {
        return None;
    }
    let modulus_u = u128::try_from(modulus).ok()?;
    let base_reduced = u128::try_from(base.rem_euclid(modulus)).ok()?;
    let result = pow_mod(base_reduced, exponent, modulus_u);
    i128::try_from(result).ok()
}

/// Modular multiplicative inverse of `a` modulo `modulus`, via [`extended_gcd`].
///
/// Returns `Some(x)` with `x` in `0..modulus` and `a * x ≡ 1 (mod modulus)`, or
/// `None` when the inverse does not exist (`gcd(a, modulus) != 1`) or when
/// `modulus <= 0`.
///
/// # Examples
///
/// ```
/// use axeyum_cas::ntheory::mod_inverse;
/// assert_eq!(mod_inverse(3, 11), Some(4)); // 3 * 4 = 12 ≡ 1 (mod 11)
/// assert_eq!(mod_inverse(2, 4), None);      // not coprime
/// ```
pub fn mod_inverse(a: i128, modulus: i128) -> Option<i128> {
    if modulus <= 0 {
        return None;
    }
    if modulus == 1 {
        return Some(0);
    }
    let reduced = a.rem_euclid(modulus);
    let (gcd_value, coeff, _) = extended_gcd(reduced, modulus);
    if gcd_value != 1 {
        return None;
    }
    Some(coeff.rem_euclid(modulus))
}

/// Deterministic primality test.
///
/// Values below `2` (including `0`, `1` and every negative integer) are not
/// prime. For positive inputs this is a deterministic `Miller–Rabin` test using
/// the witness set `{2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37}`.
///
/// # Correctness range
///
/// That witness set is **proven** to give the exact answer for all `n` below
/// `3_317_044_064_679_887_385_961_981` (≈ `3.3 * 10^24`, comfortably past the
/// whole `u64` range). Above that bound the test remains an extremely strong
/// probabilistic check but is no longer a proof; no known composite up to
/// `i128::MAX` is misclassified by these bases.
///
/// # Examples
///
/// ```
/// use axeyum_cas::ntheory::is_prime;
/// assert!(is_prime(2_147_483_647)); // 2^31 - 1, a Mersenne prime
/// assert!(!is_prime(561));          // a Carmichael number
/// assert!(!is_prime(1));
/// assert!(!is_prime(-7));
/// ```
#[must_use]
pub fn is_prime(n: i128) -> bool {
    if n < 2 {
        return false;
    }
    is_prime_u128(n.unsigned_abs())
}

/// Prime factorization of `|n|` as sorted `(prime, exponent)` pairs.
///
/// The product of `prime^exponent` over the returned pairs equals `|n|`, so the
/// result is independently checkable. Returns an empty vector for `n` in
/// `{-1, 0, 1}` (the empty product is `1`, matching `|±1|`; `0` has no finite
/// factorization).
///
/// # Examples
///
/// ```
/// use axeyum_cas::ntheory::factorize;
/// assert_eq!(factorize(360), vec![(2, 3), (3, 2), (5, 1)]);
/// assert_eq!(factorize(-12), vec![(2, 2), (3, 1)]);
/// assert!(factorize(1).is_empty());
/// ```
#[must_use]
pub fn factorize(n: i128) -> Vec<(i128, u32)> {
    factor_u128(n.unsigned_abs())
        .into_iter()
        .filter_map(|(prime, exponent)| i128::try_from(prime).ok().map(|p| (p, exponent)))
        .collect()
}

/// Prime factors of `|n|` listed with multiplicity in ascending order.
///
/// A flattened view of [`factorize`]: `factor_list(360)` is
/// `[2, 2, 2, 3, 3, 5]`. Multiplying the entries together reproduces `|n|`.
///
/// # Examples
///
/// ```
/// use axeyum_cas::ntheory::factor_list;
/// assert_eq!(factor_list(360), vec![2, 2, 2, 3, 3, 5]);
/// ```
#[must_use]
pub fn factor_list(n: i128) -> Vec<i128> {
    let mut result = Vec::new();
    for (prime, exponent) in factorize(n) {
        for _ in 0..exponent {
            result.push(prime);
        }
    }
    result
}

/// All positive divisors of `|n|`, sorted ascending.
///
/// Returns `[1]` for `n` in `{-1, 1}` and an empty vector for `n == 0` (zero is
/// divisible by every integer, so it has no finite divisor list). Divisors that
/// would exceed `i128::MAX` — possible only for `|n| == 2^127` — are omitted.
///
/// # Examples
///
/// ```
/// use axeyum_cas::ntheory::divisors;
/// assert_eq!(divisors(28), vec![1, 2, 4, 7, 14, 28]);
/// assert_eq!(divisors(1), vec![1]);
/// assert!(divisors(0).is_empty());
/// ```
#[must_use]
pub fn divisors(n: i128) -> Vec<i128> {
    if n == 0 {
        return Vec::new();
    }
    let mut divisors_u: Vec<u128> = vec![1];
    for (prime, exponent) in factor_u128(n.unsigned_abs()) {
        let mut extended: Vec<u128> = Vec::new();
        for &base_divisor in &divisors_u {
            let mut value = base_divisor;
            extended.push(value);
            for _ in 0..exponent {
                // `value` is always a divisor of `|n|`, so it stays within range.
                value *= prime;
                extended.push(value);
            }
        }
        divisors_u = extended;
    }
    let mut result: Vec<i128> = divisors_u
        .into_iter()
        .filter_map(|d| i128::try_from(d).ok())
        .collect();
    result.sort_unstable();
    result
}

/// Euler's totient `phi(|n|)`: the count of integers in `1..=|n|` coprime to
/// `|n|`.
///
/// Defined via the factorization as `phi = prod prime^(e-1) * (prime - 1)`.
/// `phi(1) == 1` (empty product) and `phi(0) == 0` by convention.
///
/// # Examples
///
/// ```
/// use axeyum_cas::ntheory::euler_phi;
/// assert_eq!(euler_phi(36), 12);      // 36 = 2^2 * 3^2
/// assert_eq!(euler_phi(7), 6);        // phi(prime) = prime - 1
/// assert_eq!(euler_phi(1), 1);
/// ```
#[must_use]
pub fn euler_phi(n: i128) -> i128 {
    let magnitude = n.unsigned_abs();
    if magnitude == 0 {
        return 0;
    }
    let mut result: u128 = 1;
    for (prime, exponent) in factor_u128(magnitude) {
        // `prime^(e-1) * (prime - 1)` divides `magnitude`, so it fits in `u128`.
        result *= prime.pow(exponent - 1) * (prime - 1);
    }
    i128::try_from(result).unwrap_or(i128::MAX)
}

/// Number of positive divisors of `|n|` (the divisor function `d(n)`).
///
/// Computed as the product of `exponent + 1` over the prime factorization.
/// Returns `0` for `n == 0` and `1` for `n` in `{-1, 1}`.
///
/// # Examples
///
/// ```
/// use axeyum_cas::ntheory::num_divisors;
/// assert_eq!(num_divisors(28), 6); // 1, 2, 4, 7, 14, 28
/// assert_eq!(num_divisors(1), 1);
/// ```
#[must_use]
pub fn num_divisors(n: i128) -> u64 {
    if n == 0 {
        return 0;
    }
    let mut count: u64 = 1;
    for (_prime, exponent) in factor_u128(n.unsigned_abs()) {
        count = count.saturating_mul(u64::from(exponent) + 1);
    }
    count
}

/// Sum of the positive divisors of `|n|` (the divisor function `sigma(n)`), or
/// `None` on overflow.
///
/// Computed as `prod (prime^(e+1) - 1) / (prime - 1)`. Returns `None` for
/// `n == 0` (undefined) and `Some(1)` for `n` in `{-1, 1}`.
///
/// # Examples
///
/// ```
/// use axeyum_cas::ntheory::sum_divisors;
/// assert_eq!(sum_divisors(28), Some(56)); // 28 is perfect: sigma(28) = 2 * 28
/// assert_eq!(sum_divisors(1), Some(1));
/// assert_eq!(sum_divisors(0), None);
/// ```
pub fn sum_divisors(n: i128) -> Option<i128> {
    if n == 0 {
        return None;
    }
    let mut result: u128 = 1;
    for (prime, exponent) in factor_u128(n.unsigned_abs()) {
        // Geometric series 1 + prime + prime^2 + ... + prime^exponent.
        let mut term: u128 = 1;
        let mut power: u128 = 1;
        for _ in 0..exponent {
            power = power.checked_mul(prime)?;
            term = term.checked_add(power)?;
        }
        result = result.checked_mul(term)?;
    }
    i128::try_from(result).ok()
}

/// Chinese remainder theorem over a list of congruences.
///
/// Each pair `(a, m)` asserts `x ≡ a (mod m)`. Returns `Some((solution,
/// modulus))` where `modulus` is the least common multiple of the individual
/// moduli and `solution` is the unique residue in `0..modulus`. An empty input
/// yields `Some((0, 1))`.
///
/// The general (not necessarily coprime) case is supported: congruences whose
/// moduli share a factor are merged when consistent. Returns `None` when any
/// modulus is `<= 0`, when a modulus product overflows `i128`, or when the
/// congruences are mutually **inconsistent** (no simultaneous solution exists).
///
/// # Examples
///
/// ```
/// use axeyum_cas::ntheory::crt;
/// // x ≡ 2 (mod 3), x ≡ 3 (mod 5), x ≡ 2 (mod 7)  =>  x ≡ 23 (mod 105)
/// assert_eq!(crt(&[(2, 3), (3, 5), (2, 7)]), Some((23, 105)));
/// // Non-coprime but consistent: x ≡ 1 (mod 4), x ≡ 3 (mod 6)
/// assert_eq!(crt(&[(1, 4), (3, 6)]), Some((9, 12)));
/// // Inconsistent:
/// assert_eq!(crt(&[(0, 2), (1, 4)]), None);
/// ```
pub fn crt(residues: &[(i128, i128)]) -> Option<(i128, i128)> {
    let mut acc_remainder: i128 = 0;
    let mut acc_modulus: i128 = 1;
    for &(residue, modulus) in residues {
        if modulus <= 0 {
            return None;
        }
        let residue = residue.rem_euclid(modulus);
        let (common, coeff, _) = extended_gcd(acc_modulus, modulus);
        let difference = residue - acc_remainder;
        if difference % common != 0 {
            return None;
        }
        let combined = (acc_modulus / common).checked_mul(modulus)?;
        let reduced_modulus = modulus / common;
        let inverse = coeff.rem_euclid(reduced_modulus);
        let scaled = (difference / common).rem_euclid(reduced_modulus);
        let step = mul_mod_signed(scaled, inverse, reduced_modulus);
        let shift = mul_mod_signed(acc_modulus, step, combined);
        acc_remainder = add_mod_signed(acc_remainder, shift, combined);
        acc_modulus = combined;
    }
    Some((acc_remainder, acc_modulus))
}

/// Signed modular multiply `(left * right) mod modulus` returning a value in
/// `0..modulus`, overflow-safe for any positive `modulus <= i128::MAX`.
fn mul_mod_signed(left: i128, right: i128, modulus: i128) -> i128 {
    let modulus_u = modulus.unsigned_abs();
    let left_u = left.rem_euclid(modulus).unsigned_abs();
    let right_u = right.rem_euclid(modulus).unsigned_abs();
    let product = mul_mod(left_u, right_u, modulus_u);
    i128::try_from(product).unwrap_or(0)
}

/// Signed modular addition `(left + right) mod modulus` in `0..modulus`, without
/// overflowing even when `modulus` is close to `i128::MAX`.
fn add_mod_signed(left: i128, right: i128, modulus: i128) -> i128 {
    let left = left.rem_euclid(modulus);
    let right = right.rem_euclid(modulus);
    if left < modulus - right {
        left + right
    } else {
        left - (modulus - right)
    }
}

/// Factorial `n!`, or `None` when `n` is negative or the result overflows
/// `i128` (i.e. for `n >= 34`).
///
/// # Examples
///
/// ```
/// use axeyum_cas::ntheory::factorial;
/// assert_eq!(factorial(0), Some(1));
/// assert_eq!(factorial(5), Some(120));
/// assert_eq!(factorial(-1), None);
/// assert_eq!(factorial(34), None); // overflows i128
/// ```
pub fn factorial(n: i128) -> Option<i128> {
    if n < 0 {
        return None;
    }
    let mut result: i128 = 1;
    let mut factor: i128 = 2;
    while factor <= n {
        result = result.checked_mul(factor)?;
        factor += 1;
    }
    Some(result)
}

/// Binomial coefficient `C(n, k)`, or `None` on overflow.
///
/// Uses the exact incremental product `prod_{i=1}^{k} (n - k + i) / i`, which
/// keeps every partial value an integer. Returns `Some(0)` when `k < 0` or
/// `k > n`, and `None` when `n < 0` or when an intermediate product overflows
/// `i128`.
///
/// # Examples
///
/// ```
/// use axeyum_cas::ntheory::binomial;
/// assert_eq!(binomial(10, 3), Some(120));
/// assert_eq!(binomial(52, 5), Some(2_598_960));
/// assert_eq!(binomial(5, 6), Some(0));
/// ```
pub fn binomial(n: i128, k: i128) -> Option<i128> {
    if n < 0 {
        return None;
    }
    if k < 0 || k > n {
        return Some(0);
    }
    let smaller = k.min(n - k);
    let mut result: i128 = 1;
    for step in 1..=smaller {
        result = result.checked_mul(n - smaller + step)?;
        result /= step;
    }
    Some(result)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn gcd_and_lcm_known_values() {
        assert_eq!(gcd(54, 24), 6);
        assert_eq!(gcd(-54, 24), 6);
        assert_eq!(gcd(0, 0), 0);
        assert_eq!(gcd(17, 0), 17);
        assert_eq!(lcm(4, 6), Some(12));
        assert_eq!(lcm(21, 6), Some(42));
        assert_eq!(lcm(0, 99), Some(0));
        assert_eq!(lcm(i128::MAX, i128::MAX - 1), None);
    }

    #[test]
    fn extended_gcd_satisfies_bezout() {
        for &(a, b) in &[(240i128, 46i128), (1071, 462), (-54, 24), (17, 5), (0, 9)] {
            let (g, x, y) = extended_gcd(a, b);
            assert_eq!(a * x + b * y, g, "Bezout identity for ({a}, {b})");
            assert_eq!(g, gcd(a, b), "returned gcd for ({a}, {b})");
        }
    }

    #[test]
    fn mod_pow_known_and_fermat() {
        assert_eq!(mod_pow(2, 10, 1000), Some(24));
        assert_eq!(mod_pow(-3, 3, 7), Some(1));
        assert_eq!(mod_pow(5, 0, 13), Some(1));
        assert_eq!(mod_pow(2, 5, 0), None);
        // Fermat's little theorem: a^(p-1) ≡ 1 (mod p) for prime p.
        let prime: i128 = 1_000_003;
        for base in [2i128, 3, 7, 999_983] {
            assert_eq!(
                mod_pow(base, u128::try_from(prime - 1).unwrap(), prime),
                Some(1),
                "Fermat for base {base}"
            );
        }
    }

    #[test]
    fn mod_inverse_round_trips() {
        assert_eq!(mod_inverse(3, 11), Some(4));
        assert_eq!(mod_inverse(2, 4), None);
        assert_eq!(mod_inverse(2, 0), None);
        let modulus: i128 = 1_000_003;
        for value in [1i128, 2, 5, 123_456] {
            let inverse = mod_inverse(value, modulus).expect("prime modulus is invertible");
            assert_eq!((value * inverse).rem_euclid(modulus), 1);
        }
    }

    #[test]
    fn is_prime_small_and_edge_cases() {
        assert!(!is_prime(0));
        assert!(!is_prime(1));
        assert!(!is_prime(-7));
        assert!(is_prime(2));
        assert!(is_prime(3));
        for composite in [4i128, 6, 9, 15, 21, 100] {
            assert!(!is_prime(composite), "{composite} should be composite");
        }
        for prime in [11i128, 13, 97, 7919] {
            assert!(is_prime(prime), "{prime} should be prime");
        }
    }

    #[test]
    fn is_prime_carmichael_and_large() {
        // Carmichael numbers are composite but fool the Fermat test.
        for carmichael in [561i128, 1105, 1729, 2465, 6601] {
            assert!(!is_prime(carmichael), "{carmichael} is a Carmichael number");
        }
        assert!(is_prime(2_147_483_647)); // 2^31 - 1
        assert!(is_prime(2_305_843_009_213_693_951)); // 2^61 - 1
        assert!(!is_prime(2_147_483_647 * 3));
        // A genuine product of two large primes must read as composite.
        assert!(!is_prime(1_000_003 * 1_000_033));
    }

    fn factorization_product(pairs: &[(i128, u32)]) -> i128 {
        pairs
            .iter()
            .map(|&(prime, exponent)| prime.pow(exponent))
            .product()
    }

    #[test]
    fn factorize_correctness() {
        assert_eq!(factorize(360), vec![(2, 3), (3, 2), (5, 1)]);
        assert!(factorize(0).is_empty());
        assert!(factorize(1).is_empty());
        assert!(factorize(-1).is_empty());
        assert_eq!(factorize(-12), vec![(2, 2), (3, 1)]);

        for n in [360i128, 1_000_000, 999_983, 13_195, 600_851_475_143] {
            let pairs = factorize(n);
            assert_eq!(factorization_product(&pairs), n, "product for {n}");
            for &(prime, _) in &pairs {
                assert!(is_prime(prime), "{prime} in factorization of {n} is prime");
            }
        }

        // A hard semiprime: two large primes.
        let semiprime: i128 = 1_000_003 * 1_000_033;
        let pairs = factorize(semiprime);
        assert_eq!(factorization_product(&pairs), semiprime);
        assert!(pairs.iter().all(|&(prime, _)| is_prime(prime)));
    }

    #[test]
    fn factor_list_flattens() {
        assert_eq!(factor_list(360), vec![2, 2, 2, 3, 3, 5]);
        let product: i128 = factor_list(360).into_iter().product();
        assert_eq!(product, 360);
    }

    #[test]
    fn divisor_functions() {
        assert_eq!(divisors(28), vec![1, 2, 4, 7, 14, 28]);
        assert_eq!(divisors(1), vec![1]);
        assert!(divisors(0).is_empty());
        assert_eq!(divisors(-12), vec![1, 2, 3, 4, 6, 12]);

        assert_eq!(num_divisors(28), 6);
        assert_eq!(num_divisors(360), 24);
        assert_eq!(num_divisors(1), 1);

        assert_eq!(sum_divisors(28), Some(56)); // perfect number
        assert_eq!(sum_divisors(6), Some(12)); // perfect number
        assert_eq!(sum_divisors(1), Some(1));
        assert_eq!(sum_divisors(0), None);

        // Cross-check num_divisors against the divisor list length.
        for n in [1i128, 12, 28, 360, 1_000_000] {
            assert_eq!(u64::try_from(divisors(n).len()).unwrap(), num_divisors(n));
        }
    }

    #[test]
    fn euler_phi_values() {
        assert_eq!(euler_phi(1), 1);
        assert_eq!(euler_phi(0), 0);
        assert_eq!(euler_phi(36), 12);
        // phi(prime) = prime - 1.
        for prime in [7i128, 13, 1_000_003] {
            assert_eq!(euler_phi(prime), prime - 1);
        }
        // Multiplicativity: phi(a*b) = phi(a)*phi(b) for coprime a, b.
        assert_eq!(euler_phi(35), euler_phi(5) * euler_phi(7));
        assert_eq!(euler_phi(72), euler_phi(8) * euler_phi(9));
    }

    #[test]
    fn crt_examples() {
        assert_eq!(crt(&[(2, 3), (3, 5), (2, 7)]), Some((23, 105)));
        assert_eq!(crt(&[]), Some((0, 1)));
        assert_eq!(crt(&[(4, 9)]), Some((4, 9)));
        // Non-coprime but consistent.
        assert_eq!(crt(&[(1, 4), (3, 6)]), Some((9, 12)));
        // Inconsistent congruences.
        assert_eq!(crt(&[(0, 2), (1, 4)]), None);
        assert_eq!(crt(&[(2, 3), (1, 0)]), None);

        // Verify a random-ish solution satisfies every congruence.
        let system = [(1i128, 5i128), (2, 7), (3, 9), (4, 11)];
        let (solution, modulus) = crt(&system).expect("coprime system solvable");
        for &(residue, base) in &system {
            assert_eq!(solution.rem_euclid(base), residue.rem_euclid(base));
        }
        assert_eq!(modulus, 5 * 7 * 9 * 11);
    }

    #[test]
    fn binomial_and_factorial_values() {
        assert_eq!(factorial(0), Some(1));
        assert_eq!(factorial(1), Some(1));
        assert_eq!(factorial(5), Some(120));
        assert_eq!(factorial(20), Some(2_432_902_008_176_640_000));
        assert_eq!(factorial(-1), None);
        assert_eq!(factorial(34), None);

        assert_eq!(binomial(10, 3), Some(120));
        assert_eq!(binomial(20, 10), Some(184_756));
        assert_eq!(binomial(52, 5), Some(2_598_960));
        assert_eq!(binomial(6, 0), Some(1));
        assert_eq!(binomial(6, 6), Some(1));
        assert_eq!(binomial(5, 6), Some(0));
        assert_eq!(binomial(-1, 0), None);

        // Pascal's rule: C(n, k) = C(n-1, k-1) + C(n-1, k).
        for n in 1i128..=25 {
            for k in 1..=n {
                assert_eq!(
                    binomial(n, k),
                    Some(binomial(n - 1, k - 1).unwrap() + binomial(n - 1, k).unwrap())
                );
            }
        }
    }
}
