//! Advanced classical number theory over `i128` — overflow-safe, self-certifying.
//!
//! A second tier of decidable, cheaply-certifiable number-theoretic routines
//! built directly on the primitives of [`crate::ntheory`] (`gcd`, `mod_pow`,
//! `euler_phi`, `divisors`, `factorize`, ...). Everything here is *classical* —
//! Euler's criterion, the Jacobi reciprocity recursion, baby-step/giant-step
//! discrete logarithms, the continued-fraction machinery, and the resulting
//! Pell solver — and every result is trivially re-checkable by a caller:
//!
//! - a Legendre/Jacobi symbol is a single modular exponentiation to re-verify;
//! - a discrete-log answer `x` is confirmed by one `mod_pow(base, x, m) == target`;
//! - a multiplicative order or primitive root is confirmed by re-running the
//!   `order == euler_phi(n)` / `a^k == 1` checks;
//! - a Pell solution `(x, y)` is confirmed by the single identity
//!   `x*x - d*y*y == 1`.
//!
//! # Overflow discipline
//!
//! As in [`crate::ntheory`], no routine ever panics. Values whose mathematical
//! result can leave the `i128` range (a permutation count, a Pell solution for a
//! large `d`, an intermediate continued-fraction product) return [`Option`] and
//! yield `None` rather than overflowing. All modular arithmetic goes through the
//! overflow-safe helpers below, which are correct for every positive `i128`
//! modulus.

use std::collections::BTreeMap;

use crate::ntheory::{divisors, euler_phi, factorize, gcd, mod_pow};

// ---------------------------------------------------------------------------
// Internal overflow-safe helpers
// ---------------------------------------------------------------------------

/// Modular multiplication `(left * right) mod modulus` on unsigned values.
///
/// Correct for any `modulus` in `1..2^127` (hence every positive `i128`
/// modulus). Small moduli use a single widening multiply; larger moduli fall
/// back to a binary double-and-add so the running sum never exceeds `2^128`.
fn mul_mod_u128(left: u128, right: u128, modulus: u128) -> u128 {
    debug_assert!(modulus != 0, "mul_mod_u128 requires a non-zero modulus");
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

/// Floor of the integer square root of `value` (`0` for `value <= 0`).
///
/// A midpoint-guarded binary search: the candidate is compared against
/// `value / mid` so no squaring is performed and nothing can overflow.
fn integer_sqrt(value: i128) -> i128 {
    if value < 2 {
        return value.max(0);
    }
    let mut low: i128 = 1;
    let mut high: i128 = value;
    let mut root: i128 = 1;
    while low <= high {
        let mid = low.midpoint(high);
        if mid <= value / mid {
            root = mid;
            low = mid + 1;
        } else {
            high = mid - 1;
        }
    }
    root
}

/// Whether `value` is a perfect square (non-negative inputs only give `true`).
fn is_perfect_square(value: i128) -> bool {
    if value < 0 {
        return false;
    }
    let root = integer_sqrt(value);
    root * root == value
}

// ---------------------------------------------------------------------------
// Public API
// ---------------------------------------------------------------------------

/// Number of ordered `k`-permutations of `n` items, `nPr = n! / (n - k)!`.
///
/// Computed as the exact rising product `(n - k + 1) * ... * n`, which stays an
/// integer at every step. Returns `Some(0)` when `k > n`, `None` when either
/// argument is negative, and `None` when the product overflows `i128`.
///
/// # Examples
///
/// ```
/// use axeyum_cas::ntheory_advanced::permutations;
/// assert_eq!(permutations(5, 2), Some(20)); // 5 * 4
/// assert_eq!(permutations(5, 0), Some(1));
/// assert_eq!(permutations(3, 5), Some(0));
/// assert_eq!(permutations(-1, 2), None);
/// ```
pub fn permutations(n: i128, k: i128) -> Option<i128> {
    if n < 0 || k < 0 {
        return None;
    }
    if k > n {
        return Some(0);
    }
    let mut result: i128 = 1;
    let mut factor = n - k + 1;
    while factor <= n {
        result = result.checked_mul(factor)?;
        factor += 1;
    }
    Some(result)
}

/// Legendre symbol `(a / p)` for an **odd prime** `p`, via Euler's criterion.
///
/// Returns `+1` when `a` is a non-zero quadratic residue mod `p`, `-1` when it
/// is a non-residue, and `0` when `p | a`. The value is `a^((p-1)/2) mod p`
/// interpreted as `0`, `1`, or `p - 1`, computed with the overflow-safe
/// [`mod_pow`].
///
/// # Precondition
///
/// `p` **must be an odd prime**. The symbol is only defined there; for any
/// `p <= 2` this function returns `0` rather than panicking, but the result is
/// not meaningful and the caller is responsible for supplying a prime modulus.
///
/// # Examples
///
/// ```
/// use axeyum_cas::ntheory_advanced::legendre_symbol;
/// assert_eq!(legendre_symbol(2, 7), 1);   // 3^2 = 9 ≡ 2 (mod 7)
/// assert_eq!(legendre_symbol(3, 7), -1);  // 3 is a non-residue mod 7
/// assert_eq!(legendre_symbol(7, 7), 0);
/// ```
pub fn legendre_symbol(a: i128, p: i128) -> i32 {
    if p <= 2 {
        return 0;
    }
    let Ok(exponent) = u128::try_from((p - 1) / 2) else {
        return 0;
    };
    match mod_pow(a, exponent, p) {
        Some(1) => 1,
        Some(value) if value == p - 1 => -1,
        _ => 0,
    }
}

/// Jacobi symbol `(a / n)` for an **odd positive** `n`, via the reciprocity law.
///
/// Generalises the Legendre symbol to composite odd moduli: it equals the
/// product of the Legendre symbols over the prime factorization of `n`, but is
/// computed directly by the quadratic-reciprocity recursion in `O(log n)`
/// steps without factoring. When `gcd(a, n) != 1` the result is `0`.
///
/// # Precondition
///
/// `n` must be odd and positive; this function returns `0` for any other `n`.
/// Note that `(a / n) = 1` does **not** by itself prove `a` is a residue when
/// `n` is composite (unlike the Legendre case).
///
/// # Examples
///
/// ```
/// use axeyum_cas::ntheory_advanced::jacobi_symbol;
/// assert_eq!(jacobi_symbol(1, 9907), 1);
/// assert_eq!(jacobi_symbol(2, 15), 1);   // (2/3)*(2/5) = (-1)*(-1)
/// assert_eq!(jacobi_symbol(5, 15), 0);   // gcd(5, 15) = 5
/// ```
pub fn jacobi_symbol(a: i128, n: i128) -> i32 {
    if n <= 0 || n.unsigned_abs().is_multiple_of(2) {
        return 0;
    }
    let mut top = a.rem_euclid(n);
    let mut bottom = n;
    let mut result: i32 = 1;
    while top != 0 {
        while top.unsigned_abs().is_multiple_of(2) {
            top /= 2;
            // A factor of 2 flips the sign when `bottom` is ≡ 3 or 5 (mod 8).
            let residue = bottom % 8;
            if residue == 3 || residue == 5 {
                result = -result;
            }
        }
        std::mem::swap(&mut top, &mut bottom);
        // Quadratic reciprocity: flip when both are ≡ 3 (mod 4).
        if top % 4 == 3 && bottom % 4 == 3 {
            result = -result;
        }
        top %= bottom;
    }
    if bottom == 1 { result } else { 0 }
}

/// Whether `a` is a quadratic residue modulo the **odd prime** `p`.
///
/// True exactly when `x*x ≡ a (mod p)` has a solution `x`, i.e. when the
/// [`legendre_symbol`] is not `-1` (both a non-zero residue and `a ≡ 0` count).
///
/// # Precondition
///
/// `p` must be an odd prime — see [`legendre_symbol`].
///
/// # Examples
///
/// ```
/// use axeyum_cas::ntheory_advanced::is_quadratic_residue;
/// assert!(is_quadratic_residue(2, 7));
/// assert!(!is_quadratic_residue(3, 7));
/// ```
pub fn is_quadratic_residue(a: i128, p: i128) -> bool {
    legendre_symbol(a, p) != -1
}

/// Multiplicative order of `a` modulo `n`: the least `k > 0` with `a^k ≡ 1`.
///
/// Returns `None` when `gcd(a, n) != 1` (no such `k` exists) or when `n <= 1`.
/// The order always divides Euler's totient `euler_phi(n)`, so the search only
/// tries the divisors of `phi` in ascending order and returns the first that
/// works — giving the exact least order.
///
/// # Examples
///
/// ```
/// use axeyum_cas::ntheory_advanced::multiplicative_order;
/// assert_eq!(multiplicative_order(2, 7), Some(3));  // 2^3 = 8 ≡ 1 (mod 7)
/// assert_eq!(multiplicative_order(3, 7), Some(6));  // 3 is a primitive root
/// assert_eq!(multiplicative_order(2, 4), None);     // gcd(2, 4) = 2
/// ```
pub fn multiplicative_order(a: i128, n: i128) -> Option<i128> {
    if n <= 1 {
        return None;
    }
    let reduced = a.rem_euclid(n);
    if gcd(reduced, n) != 1 {
        return None;
    }
    let phi = euler_phi(n);
    for divisor in divisors(phi) {
        let exponent = u128::try_from(divisor).ok()?;
        if mod_pow(a, exponent, n) == Some(1) {
            return Some(divisor);
        }
    }
    None
}

/// A primitive root modulo `n` (a generator of the unit group `(Z/nZ)^x`), or
/// `None` when none exists.
///
/// A primitive root exists exactly for `n` in `{1, 2, 4, p^k, 2*p^k}` for an odd
/// prime `p`; the smallest generator is returned. A candidate `a` coprime to `n`
/// is a primitive root iff `a^(phi/q) != 1 (mod n)` for every prime `q` dividing
/// `phi = euler_phi(n)` — the pruning check used here, avoiding a full order
/// computation per candidate.
///
/// # Examples
///
/// ```
/// use axeyum_cas::ntheory_advanced::primitive_root;
/// assert_eq!(primitive_root(7), Some(3));
/// assert_eq!(primitive_root(8), None);   // (Z/8Z)^x is not cyclic
/// ```
pub fn primitive_root(n: i128) -> Option<i128> {
    if n <= 1 {
        return None;
    }
    let phi = euler_phi(n);
    let prime_factors: Vec<i128> = factorize(phi).into_iter().map(|(prime, _)| prime).collect();
    let mut candidate = 1i128;
    while candidate < n {
        if gcd(candidate, n) == 1 {
            let generates = prime_factors.iter().all(|&prime| {
                let exponent = phi / prime;
                u128::try_from(exponent)
                    .ok()
                    .and_then(|e| mod_pow(candidate, e, n))
                    != Some(1)
            });
            if generates {
                return Some(candidate);
            }
        }
        candidate += 1;
    }
    None
}

/// Discrete logarithm by baby-step/giant-step: least-effort `x` with
/// `base^x ≡ target (mod modulus)`, or `None` when no solution exists.
///
/// Runs in `O(sqrt(modulus))` time and space. The formulation used matches
/// `base^(i*n) == target * base^j` on reduced residues, so it needs no modular
/// inverse and is correct even when `base` is not coprime to `modulus`. Any
/// returned `x` satisfies `mod_pow(base, x, modulus) == Some(target mod
/// modulus)`, so the caller can re-verify in a single exponentiation.
///
/// Returns `None` for `modulus <= 0`, and `Some(0)` for `modulus == 1`.
///
/// # Examples
///
/// ```
/// use axeyum_cas::ntheory_advanced::discrete_log;
/// assert_eq!(discrete_log(2, 3, 5), Some(3)); // 2^3 = 8 ≡ 3 (mod 5)
/// assert_eq!(discrete_log(2, 1, 5), Some(0));
/// assert_eq!(discrete_log(2, 0, 5), None);    // 2^x is never 0 (mod 5)
/// ```
pub fn discrete_log(base: i128, target: i128, modulus: i128) -> Option<i128> {
    if modulus <= 0 {
        return None;
    }
    let modulus_u = u128::try_from(modulus).ok()?;
    if modulus_u == 1 {
        return Some(0);
    }
    let base_u = u128::try_from(base.rem_euclid(modulus)).ok()?;
    let target_u = u128::try_from(target.rem_euclid(modulus)).ok()?;

    // Step size n = ceil(sqrt(modulus)); the search covers exponents in
    // [0, n^2] ⊇ [0, modulus), which contains any solution's first occurrence.
    let step = integer_sqrt(modulus - 1) + 1;
    let step_u = u128::try_from(step).ok()?;

    // Baby steps: map (target * base^j) mod modulus -> j, keeping the least j.
    let mut table: BTreeMap<u128, i128> = BTreeMap::new();
    let mut baby = target_u;
    for j in 0..step {
        table.entry(baby).or_insert(j);
        baby = mul_mod_u128(baby, base_u, modulus_u);
    }

    // Giant steps: walk base^(i*n) and look for a stored baby value.
    let base_step = u128::try_from(mod_pow(base, step_u, modulus)?).ok()?;
    let mut giant = 1u128;
    for i in 0..=step {
        if let Some(&j) = table.get(&giant) {
            let exponent = i.checked_mul(step)?.checked_sub(j)?;
            if exponent >= 0 {
                return Some(exponent);
            }
        }
        giant = mul_mod_u128(giant, base_step, modulus_u);
    }
    None
}

/// Regular continued-fraction expansion of the rational `num / den`.
///
/// Returns the partial quotients `[a0, a1, a2, ...]` produced by the Euclidean
/// algorithm, so that `num/den = a0 + 1/(a1 + 1/(a2 + ...))`. The leading term
/// may be negative; every later term is positive. Returns an empty vector when
/// `den == 0`.
///
/// # Examples
///
/// ```
/// use axeyum_cas::ntheory_advanced::continued_fraction;
/// assert_eq!(continued_fraction(415, 93), vec![4, 2, 6, 7]);
/// assert_eq!(continued_fraction(3, 1), vec![3]);
/// ```
pub fn continued_fraction(num: i128, den: i128) -> Vec<i128> {
    let mut result = Vec::new();
    if den == 0 {
        return result;
    }
    let mut num = num;
    let mut den = den;
    if den < 0 {
        // Normalise so the denominator is positive; guard the i128::MIN corner.
        match (num.checked_neg(), den.checked_neg()) {
            (Some(neg_num), Some(neg_den)) => {
                num = neg_num;
                den = neg_den;
            }
            _ => return result,
        }
    }
    while den != 0 {
        let quotient = num.div_euclid(den);
        let remainder = num.rem_euclid(den);
        result.push(quotient);
        num = den;
        den = remainder;
    }
    result
}

/// Convergents `(p_k, q_k)` of a continued fraction `cf = [a0, a1, ...]`.
///
/// Applies the standard recurrence `p_k = a_k*p_{k-1} + p_{k-2}` and
/// `q_k = a_k*q_{k-1} + q_{k-2}`. The last convergent of `continued_fraction(n,
/// d)` reproduces `n/d` in lowest terms, so the pair is independently checkable.
/// Iteration stops early (returning the convergents computed so far) if a term
/// would overflow `i128`.
///
/// # Examples
///
/// ```
/// use axeyum_cas::ntheory_advanced::convergents;
/// assert_eq!(
///     convergents(&[4, 2, 6, 7]),
///     vec![(4, 1), (9, 2), (58, 13), (415, 93)]
/// );
/// ```
pub fn convergents(cf: &[i128]) -> Vec<(i128, i128)> {
    let mut result = Vec::with_capacity(cf.len());
    let mut prior = (0i128, 1i128); // (p_{-2}, q_{-2})
    let mut recent = (1i128, 0i128); // (p_{-1}, q_{-1})
    for &term in cf {
        let Some(numerator) = term
            .checked_mul(recent.0)
            .and_then(|value| value.checked_add(prior.0))
        else {
            break;
        };
        let Some(denominator) = term
            .checked_mul(recent.1)
            .and_then(|value| value.checked_add(prior.1))
        else {
            break;
        };
        result.push((numerator, denominator));
        prior = recent;
        recent = (numerator, denominator);
    }
    result
}

/// Periodic continued fraction of `sqrt(d)` for a non-square `d > 0`.
///
/// Returns `Some((a0, period))` where `a0 = floor(sqrt(d))` and `period` is one
/// full repeating block, so that `sqrt(d) = [a0; period, period, ...]`. Returns
/// `None` when `d <= 0`, when `d` is a perfect square (the expansion is finite),
/// or on the rare overflow of an intermediate product for a very large `d`.
///
/// # Examples
///
/// ```
/// use axeyum_cas::ntheory_advanced::sqrt_continued_fraction;
/// assert_eq!(sqrt_continued_fraction(2), Some((1, vec![2])));
/// assert_eq!(sqrt_continued_fraction(23), Some((4, vec![1, 3, 1, 8])));
/// assert_eq!(sqrt_continued_fraction(9), None); // perfect square
/// ```
pub fn sqrt_continued_fraction(d: i128) -> Option<(i128, Vec<i128>)> {
    if d <= 0 || is_perfect_square(d) {
        return None;
    }
    let a0 = integer_sqrt(d);
    let mut numerator_add = 0i128; // m_k
    let mut denominator = 1i128; // d_k
    let mut term = a0; // a_k
    let mut period = Vec::new();
    loop {
        numerator_add = denominator.checked_mul(term)?.checked_sub(numerator_add)?;
        let squared = numerator_add.checked_mul(numerator_add)?;
        // `denominator` divides `d - m^2` exactly throughout the expansion.
        denominator = (d - squared) / denominator;
        if denominator == 0 {
            return None;
        }
        term = (a0 + numerator_add) / denominator;
        period.push(term);
        // The block closes precisely when the partial quotient reaches 2*a0.
        if term == 2 * a0 {
            break;
        }
    }
    Some((a0, period))
}

/// Fundamental solution `(x, y)` of the Pell equation `x^2 - d*y^2 = 1`.
///
/// For a non-square `d > 0` this is the smallest positive solution; it is read
/// off the convergents of the [`sqrt_continued_fraction`] of `d` — the first
/// convergent `p/q` (with `q > 0`) satisfying `p^2 - d*q^2 == 1`. Returns `None`
/// when `d <= 0`, when `d` is a perfect square (no non-trivial solution), or
/// when the solution overflows `i128`.
///
/// # Examples
///
/// ```
/// use axeyum_cas::ntheory_advanced::pell_fundamental_solution;
/// assert_eq!(pell_fundamental_solution(2), Some((3, 2))); // 3^2 - 2*2^2 = 1
/// assert_eq!(pell_fundamental_solution(4), None);          // perfect square
/// ```
pub fn pell_fundamental_solution(d: i128) -> Option<(i128, i128)> {
    if d <= 0 {
        return None;
    }
    let (a0, period) = sqrt_continued_fraction(d)?;
    // `a0` followed by two full periods reaches the fundamental solution
    // whether the period length is even (at index r-1) or odd (at index 2r-1).
    let mut cf = Vec::with_capacity(1 + 2 * period.len());
    cf.push(a0);
    for _ in 0..2 {
        cf.extend_from_slice(&period);
    }
    for (numerator, denominator) in convergents(&cf) {
        if denominator <= 0 {
            continue;
        }
        let numerator_sq = numerator.checked_mul(numerator)?;
        let scaled = denominator
            .checked_mul(denominator)
            .and_then(|value| value.checked_mul(d))?;
        if numerator_sq.checked_sub(scaled)? == 1 {
            return Some((numerator, denominator));
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ntheory::{factorial, is_prime};

    #[test]
    fn permutations_known_values() {
        assert_eq!(permutations(5, 2), Some(20));
        assert_eq!(permutations(5, 0), Some(1));
        assert_eq!(permutations(5, 5), Some(120)); // 5!
        assert_eq!(permutations(10, 3), Some(720));
        assert_eq!(permutations(3, 5), Some(0)); // k > n
        assert_eq!(permutations(-1, 2), None);
        assert_eq!(permutations(4, -1), None);

        // Certify against the factorial identity nPr = n! / (n - k)!.
        for n in 0i128..=20 {
            for k in 0..=n {
                let expected = factorial(n).unwrap() / factorial(n - k).unwrap();
                assert_eq!(permutations(n, k), Some(expected), "nPr({n}, {k})");
            }
        }
    }

    #[test]
    fn legendre_matches_brute_force() {
        // Fixtures from the task.
        assert_eq!(legendre_symbol(2, 7), 1);
        assert_eq!(legendre_symbol(3, 7), -1);
        assert_eq!(legendre_symbol(7, 7), 0);

        // Re-check via an exhaustive quadratic-residue scan for small primes.
        for &p in &[3i128, 5, 7, 11, 13, 17, 19, 23, 97] {
            assert!(is_prime(p));
            for a in 0..p {
                let residue = a.rem_euclid(p);
                let brute_is_qr = (0..p).any(|x| mod_pow(x, 2, p) == Some(residue));
                let symbol = legendre_symbol(a, p);
                if residue == 0 {
                    assert_eq!(symbol, 0);
                } else if brute_is_qr {
                    assert_eq!(symbol, 1, "({a}/{p}) should be +1");
                } else {
                    assert_eq!(symbol, -1, "({a}/{p}) should be -1");
                }
                // is_quadratic_residue agrees with the brute-force existence test.
                assert_eq!(is_quadratic_residue(a, p), brute_is_qr, "QR({a}, {p})");
            }
        }
    }

    #[test]
    fn jacobi_symbol_values_and_prime_agreement() {
        // Task fixture.
        assert_eq!(jacobi_symbol(1001, 9907), -1);

        // 9907 is prime, so the Jacobi symbol must equal the Legendre symbol.
        assert!(is_prime(9907));
        for a in [1001i128, 2, 3, 5, 42, 9906] {
            assert_eq!(
                jacobi_symbol(a, 9907),
                legendre_symbol(a, 9907),
                "Jacobi vs Legendre for {a}"
            );
        }

        // Multiplicativity in the numerator: (ab/n) = (a/n)(b/n).
        let n = 45045; // odd composite
        for &(a, b) in &[(2i128, 7i128), (3, 11), (13, 17), (8, 9)] {
            assert_eq!(
                jacobi_symbol(a * b, n),
                jacobi_symbol(a, n) * jacobi_symbol(b, n),
                "multiplicativity for ({a}*{b}/{n})"
            );
        }

        // Even / non-positive modulus is undefined -> 0.
        assert_eq!(jacobi_symbol(3, 8), 0);
        assert_eq!(jacobi_symbol(3, 0), 0);
    }

    #[test]
    fn multiplicative_order_certified() {
        assert_eq!(multiplicative_order(2, 7), Some(3));
        assert_eq!(multiplicative_order(3, 7), Some(6));
        assert_eq!(multiplicative_order(1, 7), Some(1));
        assert_eq!(multiplicative_order(2, 4), None); // not coprime

        for n in [7i128, 9, 10, 13, 15, 100, 101] {
            for a in 1..n {
                match multiplicative_order(a, n) {
                    Some(order) => {
                        // Re-check: a^order ≡ 1 and no smaller positive power is 1.
                        assert_eq!(mod_pow(a, u128::try_from(order).unwrap(), n), Some(1));
                        for smaller in 1..order {
                            assert_ne!(
                                mod_pow(a, u128::try_from(smaller).unwrap(), n),
                                Some(1),
                                "order of {a} mod {n} is not minimal"
                            );
                        }
                    }
                    None => assert_ne!(gcd(a, n), 1),
                }
            }
        }
    }

    #[test]
    fn primitive_root_certified() {
        // Task fixture: a primitive root of 7 lies in {3, 5}.
        let root = primitive_root(7).unwrap();
        assert!(root == 3 || root == 5, "got {root}");

        // No primitive root modulo 8 or 12 (unit groups are not cyclic).
        assert_eq!(primitive_root(8), None);
        assert_eq!(primitive_root(12), None);

        // Where one exists, its order must equal phi(n).
        for n in [2i128, 3, 4, 5, 6, 7, 9, 10, 11, 13, 14, 18, 22, 25, 27] {
            let root = primitive_root(n).expect("primitive root should exist");
            assert_eq!(
                multiplicative_order(root, n),
                Some(euler_phi(n)),
                "root {root} must generate (Z/{n}Z)^x"
            );
        }
    }

    #[test]
    fn discrete_log_certified() {
        // Task fixture: 2^3 = 8 ≡ 3 (mod 5).
        assert_eq!(discrete_log(2, 3, 5), Some(3));
        assert_eq!(discrete_log(2, 1, 5), Some(0));
        assert_eq!(discrete_log(2, 0, 5), None);
        assert_eq!(discrete_log(3, 1, 1), Some(0));

        // Every returned exponent must re-verify; unsolvable systems return None.
        for modulus in [5i128, 7, 11, 13, 23, 101, 1009] {
            for base in 2..modulus.min(20) {
                for target in 0..modulus.min(20) {
                    if let Some(x) = discrete_log(base, target, modulus) {
                        assert_eq!(
                            mod_pow(base, u128::try_from(x).unwrap(), modulus),
                            Some(target.rem_euclid(modulus)),
                            "discrete_log({base}, {target}, {modulus}) = {x}"
                        );
                    } else {
                        // Confirm no exponent up to the modulus reaches target.
                        let reachable = (0..modulus).any(|x| {
                            mod_pow(base, u128::try_from(x).unwrap(), modulus)
                                == Some(target.rem_euclid(modulus))
                        });
                        assert!(
                            !reachable,
                            "discrete_log({base}, {target}, {modulus}) wrongly None"
                        );
                    }
                }
            }
        }
    }

    #[test]
    fn continued_fraction_and_convergents() {
        // Task fixture: 415/93 = [4; 2, 6, 7].
        assert_eq!(continued_fraction(415, 93), vec![4, 2, 6, 7]);
        assert_eq!(continued_fraction(3, 1), vec![3]);
        assert!(continued_fraction(1, 0).is_empty());

        // The last convergent reproduces the original fraction in lowest terms.
        for &(num, den) in &[(415i128, 93i128), (355, 113), (1, 7), (22, 7), (100, 3)] {
            let cf = continued_fraction(num, den);
            let convs = convergents(&cf);
            let &(p, q) = convs.last().unwrap();
            let g = gcd(num, den);
            assert_eq!((p, q), (num / g, den / g), "convergent for {num}/{den}");
            // Cross-check every convergent multiplies out consistently.
            assert_eq!(
                convergents(&[4, 2, 6, 7]),
                vec![(4, 1), (9, 2), (58, 13), (415, 93)]
            );
        }
    }

    #[test]
    fn sqrt_continued_fraction_values() {
        // Task fixture: sqrt(2) = (1, [2]).
        assert_eq!(sqrt_continued_fraction(2), Some((1, vec![2])));
        assert_eq!(sqrt_continued_fraction(3), Some((1, vec![1, 2])));
        assert_eq!(sqrt_continued_fraction(7), Some((2, vec![1, 1, 1, 4])));
        assert_eq!(sqrt_continued_fraction(23), Some((4, vec![1, 3, 1, 8])));
        // Perfect squares have no periodic expansion.
        assert_eq!(sqrt_continued_fraction(9), None);
        assert_eq!(sqrt_continued_fraction(1), None);
        assert_eq!(sqrt_continued_fraction(0), None);
    }

    #[test]
    fn pell_fundamental_solutions_certified() {
        // Task fixtures, each re-verified against x^2 - d*y^2 == 1.
        assert_eq!(pell_fundamental_solution(2), Some((3, 2)));
        assert_eq!(
            pell_fundamental_solution(61),
            Some((1_766_319_049, 226_153_980))
        );
        assert_eq!(pell_fundamental_solution(4), None); // perfect square

        for d in [2i128, 3, 5, 6, 7, 13, 61, 109, 149] {
            let (x, y) = pell_fundamental_solution(d).expect("non-square d has a solution");
            let identity = x
                .checked_mul(x)
                .and_then(|xx| y.checked_mul(y).and_then(|yy| yy.checked_mul(d)).map(|dyy| xx - dyy))
                .unwrap();
            assert_eq!(identity, 1, "Pell identity for d = {d}: ({x}, {y})");
            assert!(x > 0 && y > 0);
        }
    }
}
