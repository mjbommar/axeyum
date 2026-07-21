//! Classical multiplicative number theory over `i128` — overflow-safe.
//!
//! A third tier of dependency-free, self-certifying number-theoretic routines
//! built on the primitives of [`crate::ntheory`] (`factorize`, `divisors`,
//! `is_prime`, `lcm`, ...). Everything here is *classical* — the Möbius and
//! Mertens functions, the divisor power-sums `sigma_k`, perfect / squarefree /
//! Carmichael predicates, the radical, the Carmichael function `lambda`, the
//! primorial, and prime enumeration (`next_prime`, `prev_prime`, `prime_pi`,
//! `nth_prime`) — and every value is cheaply re-checkable by a caller:
//!
//! - a `mobius` / `is_squarefree` verdict is one look at the factorization;
//! - a `sigma_k(1, n) == 2*n` check is exactly what `is_perfect` reports;
//! - a `radical` or `carmichael_lambda` answer is re-derived from `factorize(n)`;
//! - a Carmichael verdict re-checks Korselt's criterion directly.
//!
//! # Overflow discipline
//!
//! As in [`crate::ntheory`], no routine ever panics. Values whose mathematical
//! result can leave the `i128` range (a divisor power-sum, a radical, a
//! primorial, the next prime past `i128::MAX`) return [`Option`] and yield
//! `None` rather than overflowing. All arithmetic goes through `checked_*`.
//!
//! # Sign and edge conventions
//!
//! The multiplicative functions operate on the *absolute value* of their
//! argument (mathematical factorization is defined on the positive integers).
//! Each function documents its behaviour on `0` and `1`.

use crate::ntheory::{factorize, is_prime, lcm};

// ---------------------------------------------------------------------------
// Internal helpers
// ---------------------------------------------------------------------------

/// Carmichael's function on a single prime power `prime^exponent`.
///
/// For an odd prime this is `prime^(exponent-1) * (prime - 1)` (equal to Euler's
/// totient of the prime power); for `prime == 2` it is `1`, `2`, or `2^(e-2)`
/// according as `exponent` is `1`, `2`, or `>= 3`. Returns `None` on overflow.
fn carmichael_prime_power(prime: i128, exponent: u32) -> Option<i128> {
    if prime == 2 {
        return match exponent {
            0 | 1 => Some(1),
            2 => Some(2),
            _ => 2i128.checked_pow(exponent - 2),
        };
    }
    let power = prime.checked_pow(exponent - 1)?;
    power.checked_mul(prime - 1)
}

// ---------------------------------------------------------------------------
// Public API
// ---------------------------------------------------------------------------

/// The Möbius function `mu(|n|)`.
///
/// Returns `0` when `|n|` is divisible by the square of a prime (squareful),
/// otherwise `(-1)^k` where `k` is the number of distinct prime factors. By the
/// empty-product convention `mu(1) == 1`, and `mu(0) == 0`.
///
/// # Examples
///
/// ```
/// use axeyum_cas::ntheory_more::mobius;
/// assert_eq!(mobius(1), 1);
/// assert_eq!(mobius(2), -1);
/// assert_eq!(mobius(6), 1);   // 6 = 2 * 3, two distinct primes
/// assert_eq!(mobius(12), 0);  // 12 = 2^2 * 3, squareful
/// ```
#[must_use]
pub fn mobius(n: i128) -> i32 {
    if n == 0 {
        return 0;
    }
    let factors = factorize(n);
    if factors.iter().any(|&(_, exponent)| exponent > 1) {
        return 0;
    }
    if factors.len().is_multiple_of(2) {
        1
    } else {
        -1
    }
}

/// The Mertens function `M(n) = sum_{k=1}^{n} mu(k)`.
///
/// The running total of the [`mobius`] values over `1..=n`. Returns `0` for
/// `n < 1` (empty sum). The accumulation is in `i64`, which comfortably holds
/// `M(n)` for any `n` this bounded loop can practically reach.
///
/// # Examples
///
/// ```
/// use axeyum_cas::ntheory_more::mertens;
/// assert_eq!(mertens(1), 1);
/// assert_eq!(mertens(10), -1);
/// ```
#[must_use]
pub fn mertens(n: i128) -> i64 {
    let mut total: i64 = 0;
    for k in 1..=n {
        total += i64::from(mobius(k));
    }
    total
}

/// The divisor power-sum `sigma_k(|n|) = sum_{d | |n|} d^k`, or `None` on
/// overflow.
///
/// With `k == 0` this is the number of divisors (`sigma_0`); with `k == 1` the
/// sum of divisors (`sigma_1`). Computed multiplicatively from the
/// factorization: each prime power `p^e` contributes the geometric sum
/// `1 + p^k + p^{2k} + ... + p^{ek}`. Returns `None` for `n == 0` (undefined)
/// and `Some(1)` for `n` in `{-1, 1}` (empty product).
///
/// # Examples
///
/// ```
/// use axeyum_cas::ntheory_more::sigma_k;
/// assert_eq!(sigma_k(0, 12), Some(6));  // number of divisors of 12
/// assert_eq!(sigma_k(1, 12), Some(28)); // sum of divisors of 12
/// assert_eq!(sigma_k(2, 6), Some(50));  // 1 + 4 + 9 + 36
/// assert_eq!(sigma_k(1, 0), None);
/// ```
pub fn sigma_k(k: u32, n: i128) -> Option<i128> {
    if n == 0 {
        return None;
    }
    let mut result: i128 = 1;
    for (prime, exponent) in factorize(n) {
        let prime_power = prime.checked_pow(k)?;
        // Geometric series 1 + p^k + p^{2k} + ... + p^{ek}.
        let mut term: i128 = 1;
        let mut power: i128 = 1;
        for _ in 0..exponent {
            power = power.checked_mul(prime_power)?;
            term = term.checked_add(power)?;
        }
        result = result.checked_mul(term)?;
    }
    Some(result)
}

/// Whether `n` is a perfect number (`sigma_1(n) == 2 * n`).
///
/// A positive integer equal to the sum of its proper divisors. Non-positive `n`
/// are never perfect, and the check is honest under overflow (either side
/// overflowing yields `false`, never a wrong `true`).
///
/// # Examples
///
/// ```
/// use axeyum_cas::ntheory_more::is_perfect;
/// assert!(is_perfect(6));   // 1 + 2 + 3 = 6
/// assert!(is_perfect(28));  // 1 + 2 + 4 + 7 + 14 = 28
/// assert!(!is_perfect(12));
/// ```
#[must_use]
pub fn is_perfect(n: i128) -> bool {
    if n <= 0 {
        return false;
    }
    matches!((sigma_k(1, n), n.checked_mul(2)), (Some(s), Some(double)) if s == double)
}

/// Whether `|n|` is squarefree (no prime factor with exponent `>= 2`).
///
/// `1` is squarefree (empty factorization), while `0` is **not** (it is
/// divisible by every square).
///
/// # Examples
///
/// ```
/// use axeyum_cas::ntheory_more::is_squarefree;
/// assert!(is_squarefree(1));
/// assert!(is_squarefree(30)); // 2 * 3 * 5
/// assert!(!is_squarefree(12)); // 2^2 * 3
/// assert!(!is_squarefree(0));
/// ```
#[must_use]
pub fn is_squarefree(n: i128) -> bool {
    if n == 0 {
        return false;
    }
    factorize(n).iter().all(|&(_, exponent)| exponent == 1)
}

/// The radical of `|n|`: the product of its distinct prime factors, or `None`
/// on overflow.
///
/// `radical(1) == Some(1)` (empty product); `radical(0) == None` (undefined).
///
/// # Examples
///
/// ```
/// use axeyum_cas::ntheory_more::radical;
/// assert_eq!(radical(1), Some(1));
/// assert_eq!(radical(12), Some(6)); // distinct primes 2, 3
/// assert_eq!(radical(360), Some(30)); // 2 * 3 * 5
/// assert_eq!(radical(0), None);
/// ```
pub fn radical(n: i128) -> Option<i128> {
    if n == 0 {
        return None;
    }
    let mut result: i128 = 1;
    for (prime, _exponent) in factorize(n) {
        result = result.checked_mul(prime)?;
    }
    Some(result)
}

/// The **integer floor `k`-th root** of a non-negative `n`: the largest `r ≥ 0`
/// with `rᵏ ≤ n`. `None` for `k == 0`. `integer_nth_root(27, 3) = 3`,
/// `integer_nth_root(28, 3) = 3`, `integer_nth_root(0, k) = 0`.
///
/// ```
/// use axeyum_cas::ntheory_more::integer_nth_root;
/// assert_eq!(integer_nth_root(1000, 3), Some(10));
/// assert_eq!(integer_nth_root(1001, 3), Some(10));
/// ```
#[must_use]
pub fn integer_nth_root(n: i128, k: u32) -> Option<i128> {
    if k == 0 {
        return None;
    }
    if n < 0 {
        return None; // even/odd roots of negatives are out of scope
    }
    if n <= 1 || k == 1 {
        return Some(n);
    }
    // Binary search for the largest r with rᵏ ≤ n (checked power avoids overflow).
    let pow_le = |base: i128| -> bool {
        let mut acc: i128 = 1;
        for _ in 0..k {
            match acc.checked_mul(base) {
                Some(next) if next <= n => acc = next,
                _ => return false, // overflow or exceeded n ⇒ base^k > n
            }
        }
        true
    };
    let (mut low, mut high) = (1i128, n);
    while low < high {
        let mid = low + (high - low + 1) / 2;
        if pow_le(mid) {
            low = mid;
        } else {
            high = mid - 1;
        }
    }
    Some(low)
}

/// Detect a **perfect power**: if `n = mᵏ` for some integer base `m` and exponent
/// `k ≥ 2`, return `(m, k)` with `k` **maximal** (so `m` is not itself a perfect
/// power) and `m` minimal in magnitude; otherwise `None`. Handles negative `n`
/// (only odd exponents, e.g. `−8 = (−2)³`). `0` and `±1` are not perfect powers here.
///
/// The base re-checks directly: `mᵏ == n`.
///
/// ```
/// use axeyum_cas::ntheory_more::perfect_power;
/// assert_eq!(perfect_power(64), Some((2, 6)));   // 2⁶ (not 8² or 4³)
/// assert_eq!(perfect_power(72), None);
/// assert_eq!(perfect_power(-27), Some((-3, 3))); // (−3)³
/// ```
#[must_use]
pub fn perfect_power(n: i128) -> Option<(i128, u32)> {
    let magnitude = n.checked_abs()?;
    if magnitude <= 1 {
        return None;
    }
    // Try exponents from large to small; the first (largest) prime exponent that
    // works gives the maximal factorization when iterated. Simplest correct route:
    // find the maximal k by testing every k from ⌊log₂ n⌋ down to 2.
    let mut best: Option<(i128, u32)> = None;
    let mut k = 2u32;
    while (1i128 << k.min(126)) <= magnitude {
        if let Some(root) = integer_nth_root(magnitude, k)
            && root.checked_pow(k) == Some(magnitude)
        {
            // Respect the sign: a negative n needs an odd exponent.
            if n < 0 {
                if k % 2 == 1 {
                    best = Some((-root, k)); // largest odd k wins as k grows
                }
            } else {
                best = Some((root, k)); // largest k wins
            }
        }
        k += 1;
    }
    best
}

/// The Carmichael function `lambda(|n|)`, or `None` on overflow.
///
/// The exponent of the unit group `(Z/nZ)^x`: the least `m > 0` with `a^m ≡ 1
/// (mod n)` for every `a` coprime to `n`. Computed as the least common multiple
/// of [`carmichael_prime_power`] over the prime-power factors. `lambda(1) ==
/// Some(1)`; `lambda(0) == None`.
///
/// # Examples
///
/// ```
/// use axeyum_cas::ntheory_more::carmichael_lambda;
/// assert_eq!(carmichael_lambda(1), Some(1));
/// assert_eq!(carmichael_lambda(8), Some(2));  // lambda(2^3)
/// assert_eq!(carmichael_lambda(15), Some(4)); // lcm(lambda(3), lambda(5))
/// assert_eq!(carmichael_lambda(0), None);
/// ```
pub fn carmichael_lambda(n: i128) -> Option<i128> {
    if n == 0 {
        return None;
    }
    let mut result: i128 = 1;
    for (prime, exponent) in factorize(n) {
        let lambda = carmichael_prime_power(prime, exponent)?;
        result = lcm(result, lambda)?;
    }
    Some(result)
}

/// The primorial of `n`: the product of all primes `<= n`, or `None` on
/// overflow.
///
/// Returns `Some(1)` for `n < 2` (empty product). Note this is the primorial of
/// a *bound* `n#`, not the product of the first `n` primes.
///
/// # Examples
///
/// ```
/// use axeyum_cas::ntheory_more::primorial;
/// assert_eq!(primorial(1), Some(1));
/// assert_eq!(primorial(10), Some(210)); // 2 * 3 * 5 * 7
/// assert_eq!(primorial(11), Some(2310));
/// ```
pub fn primorial(n: i128) -> Option<i128> {
    let mut result: i128 = 1;
    for candidate in 2..=n {
        if is_prime(candidate) {
            result = result.checked_mul(candidate)?;
        }
    }
    Some(result)
}

/// The smallest prime strictly greater than `n`, or `None` on overflow.
///
/// For any `n < 2` the answer is `2`. Returns `None` only if the search would
/// have to step past `i128::MAX` without finding a prime.
///
/// # Examples
///
/// ```
/// use axeyum_cas::ntheory_more::next_prime;
/// assert_eq!(next_prime(13), Some(17));
/// assert_eq!(next_prime(0), Some(2));
/// assert_eq!(next_prime(-5), Some(2));
/// ```
pub fn next_prime(n: i128) -> Option<i128> {
    let mut candidate = if n < 2 { 2 } else { n.checked_add(1)? };
    loop {
        if is_prime(candidate) {
            return Some(candidate);
        }
        candidate = candidate.checked_add(1)?;
    }
}

/// The largest prime strictly less than `n`, or `None` when none exists.
///
/// Returns `None` for `n <= 2` (there is no prime below `2`).
///
/// # Examples
///
/// ```
/// use axeyum_cas::ntheory_more::prev_prime;
/// assert_eq!(prev_prime(13), Some(11));
/// assert_eq!(prev_prime(3), Some(2));
/// assert_eq!(prev_prime(2), None);
/// ```
pub fn prev_prime(n: i128) -> Option<i128> {
    if n <= 2 {
        return None;
    }
    let mut candidate = n - 1;
    while candidate >= 2 {
        if is_prime(candidate) {
            return Some(candidate);
        }
        candidate -= 1;
    }
    None
}

/// The prime-counting function `pi(n)`: the number of primes `<= n`.
///
/// A direct bounded sieve-free count via [`is_prime`]; returns `0` for `n < 2`.
///
/// # Examples
///
/// ```
/// use axeyum_cas::ntheory_more::prime_pi;
/// assert_eq!(prime_pi(10), 4);   // 2, 3, 5, 7
/// assert_eq!(prime_pi(100), 25);
/// assert_eq!(prime_pi(1), 0);
/// ```
#[must_use]
pub fn prime_pi(n: i128) -> i64 {
    let mut count: i64 = 0;
    for candidate in 2..=n {
        if is_prime(candidate) {
            count += 1;
        }
    }
    count
}

/// The `k`-th prime, 1-indexed (`nth_prime(1) == 2`), or `None` on overflow.
///
/// Returns `None` for `k == 0` (there is no zeroth prime) and `None` only if the
/// search would have to step past `i128::MAX`.
///
/// # Examples
///
/// ```
/// use axeyum_cas::ntheory_more::nth_prime;
/// assert_eq!(nth_prime(1), Some(2));
/// assert_eq!(nth_prime(6), Some(13)); // 2, 3, 5, 7, 11, 13
/// assert_eq!(nth_prime(0), None);
/// ```
pub fn nth_prime(k: u32) -> Option<i128> {
    if k == 0 {
        return None;
    }
    let mut remaining = k;
    let mut candidate: i128 = 2;
    loop {
        if is_prime(candidate) {
            remaining -= 1;
            if remaining == 0 {
                return Some(candidate);
            }
        }
        candidate = candidate.checked_add(1)?;
    }
}

/// Whether `n` is a Carmichael number, via Korselt's criterion.
///
/// True exactly when `n` is a positive, **composite**, **squarefree** integer
/// such that `p - 1` divides `n - 1` for every prime `p` dividing `n`. Such `n`
/// are Fermat pseudoprimes to every base coprime to `n`. Non-positive, prime,
/// and squareful `n` are all rejected.
///
/// # Examples
///
/// ```
/// use axeyum_cas::ntheory_more::is_carmichael_number;
/// assert!(is_carmichael_number(561));  // 3 * 11 * 17
/// assert!(is_carmichael_number(1105)); // 5 * 13 * 17
/// assert!(!is_carmichael_number(560));
/// assert!(!is_carmichael_number(7));   // prime, not composite
/// ```
#[must_use]
pub fn is_carmichael_number(n: i128) -> bool {
    if n < 2 || is_prime(n) {
        return false;
    }
    let factors = factorize(n);
    // Squarefree: every prime appears to the first power.
    if factors.iter().any(|&(_, exponent)| exponent > 1) {
        return false;
    }
    let n_minus_one = n - 1;
    factors.iter().all(|&(prime, _)| {
        n_minus_one
            .unsigned_abs()
            .is_multiple_of((prime - 1).unsigned_abs())
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ntheory::{divisors, is_prime};

    #[test]
    fn mobius_known_values() {
        assert_eq!(mobius(1), 1);
        assert_eq!(mobius(2), -1);
        assert_eq!(mobius(3), -1);
        assert_eq!(mobius(6), 1);
        assert_eq!(mobius(12), 0);
        assert_eq!(mobius(30), -1); // 2 * 3 * 5, three distinct primes
        assert_eq!(mobius(0), 0);
        // A prime is always -1; a squareful number is always 0.
        for prime in [2i128, 3, 5, 7, 11, 13, 97] {
            assert_eq!(mobius(prime), -1, "mu({prime})");
        }
        for squareful in [4i128, 8, 9, 18, 12, 50, 500] {
            assert_eq!(mobius(squareful), 0, "mu({squareful})");
        }
    }

    #[test]
    fn perfect_powers_and_integer_roots() {
        // Floor k-th roots.
        assert_eq!(integer_nth_root(1000, 3), Some(10));
        assert_eq!(integer_nth_root(1001, 3), Some(10));
        assert_eq!(integer_nth_root(999, 3), Some(9));
        assert_eq!(integer_nth_root(1024, 10), Some(2));
        assert_eq!(integer_nth_root(0, 5), Some(0));
        assert_eq!(integer_nth_root(50, 1), Some(50));
        assert_eq!(integer_nth_root(50, 0), None);
        // Perfect powers with the maximal exponent; the base re-checks (mᵏ = n).
        for (n, base, exp) in [
            (64i128, 2i128, 6u32),
            (27, 3, 3),
            (1024, 2, 10),
            (100, 10, 2),
            (81, 3, 4),
            (256, 2, 8),
            (-27, -3, 3),
            (-8, -2, 3),
        ] {
            assert_eq!(perfect_power(n), Some((base, exp)), "perfect_power({n})");
            assert_eq!(base.checked_pow(exp), Some(n));
        }
        // Non-powers.
        for n in [2i128, 7, 72, 1, 0, -1, -4] {
            assert_eq!(perfect_power(n), None, "perfect_power({n})");
        }
    }

    #[test]
    fn mertens_known_values() {
        assert_eq!(mertens(0), 0);
        assert_eq!(mertens(1), 1);
        assert_eq!(mertens(10), -1);
        // Cross-check the partial sum definition directly.
        let mut running: i64 = 0;
        for k in 1i128..=50 {
            running += i64::from(mobius(k));
            assert_eq!(mertens(k), running, "M({k})");
        }
    }

    #[test]
    fn sigma_k_known_values() {
        assert_eq!(sigma_k(0, 12), Some(6));
        assert_eq!(sigma_k(1, 12), Some(28));
        assert_eq!(sigma_k(2, 6), Some(50));
        assert_eq!(sigma_k(1, 6), Some(12)); // perfect
        assert_eq!(sigma_k(1, 28), Some(56)); // perfect
        assert_eq!(sigma_k(0, 1), Some(1));
        assert_eq!(sigma_k(1, 1), Some(1));
        assert_eq!(sigma_k(1, 0), None);

        // sigma_0(n) equals the length of the divisor list.
        for n in [1i128, 6, 12, 28, 360, 1_000_000] {
            let expected = i128::try_from(divisors(n).len()).unwrap();
            assert_eq!(
                sigma_k(0, n),
                Some(expected),
                "sigma_0({n}) vs divisor count"
            );
        }
        // sigma_1(n) equals the sum of the divisor list.
        for n in [1i128, 6, 12, 28, 496] {
            let expected: i128 = divisors(n).iter().sum();
            assert_eq!(sigma_k(1, n), Some(expected), "sigma_1({n}) vs divisor sum");
        }
    }

    #[test]
    fn is_perfect_known_values() {
        assert!(is_perfect(6));
        assert!(is_perfect(28));
        assert!(is_perfect(496));
        assert!(is_perfect(8128));
        assert!(!is_perfect(12));
        assert!(!is_perfect(1));
        assert!(!is_perfect(0));
        assert!(!is_perfect(-6));
    }

    #[test]
    fn is_squarefree_known_values() {
        assert!(is_squarefree(1));
        assert!(is_squarefree(2));
        assert!(is_squarefree(6));
        assert!(is_squarefree(30));
        assert!(!is_squarefree(12));
        assert!(!is_squarefree(4));
        assert!(!is_squarefree(0));
        // Squarefree iff the Mobius value is non-zero (for positive n).
        for n in 1i128..=100 {
            assert_eq!(
                is_squarefree(n),
                mobius(n) != 0,
                "squarefree/mobius for {n}"
            );
        }
    }

    #[test]
    fn radical_known_values() {
        assert_eq!(radical(1), Some(1));
        assert_eq!(radical(12), Some(6));
        assert_eq!(radical(360), Some(30));
        assert_eq!(radical(7), Some(7));
        assert_eq!(radical(0), None);
        // The radical of a squarefree number is itself.
        for n in [6i128, 30, 105, 2310] {
            assert_eq!(radical(n), Some(n), "radical of squarefree {n}");
        }
    }

    #[test]
    fn carmichael_lambda_known_values() {
        assert_eq!(carmichael_lambda(1), Some(1));
        assert_eq!(carmichael_lambda(8), Some(2));
        assert_eq!(carmichael_lambda(15), Some(4));
        assert_eq!(carmichael_lambda(0), None);
        // A few more: lambda(2)=1, lambda(4)=2, lambda(16)=4, lambda(7)=6.
        assert_eq!(carmichael_lambda(2), Some(1));
        assert_eq!(carmichael_lambda(4), Some(2));
        assert_eq!(carmichael_lambda(16), Some(4));
        assert_eq!(carmichael_lambda(7), Some(6));
        // lambda(n) certifies as an exponent: a^lambda ≡ 1 (mod n) for coprime a.
        for n in [8i128, 15, 16, 21, 100] {
            let lambda = carmichael_lambda(n).unwrap();
            let exponent = u128::try_from(lambda).unwrap();
            for a in 1..n {
                if crate::ntheory::gcd(a, n) == 1 {
                    assert_eq!(
                        crate::ntheory::mod_pow(a, exponent, n),
                        Some(1),
                        "a={a}^lambda({n}) must be 1"
                    );
                }
            }
        }
    }

    #[test]
    fn primorial_known_values() {
        assert_eq!(primorial(1), Some(1));
        assert_eq!(primorial(2), Some(2));
        assert_eq!(primorial(10), Some(210));
        assert_eq!(primorial(11), Some(2310));
        assert_eq!(primorial(-3), Some(1));
        // The primorial is the product of every prime up to the bound.
        let expected: i128 = (2i128..=20).filter(|&p| is_prime(p)).product();
        assert_eq!(primorial(20), Some(expected));
    }

    #[test]
    fn next_and_prev_prime_known_values() {
        assert_eq!(next_prime(13), Some(17));
        assert_eq!(next_prime(0), Some(2));
        assert_eq!(next_prime(-5), Some(2));
        assert_eq!(next_prime(2), Some(3));
        assert_eq!(prev_prime(13), Some(11));
        assert_eq!(prev_prime(3), Some(2));
        assert_eq!(prev_prime(2), None);
        assert_eq!(prev_prime(1), None);
        // Round-trip: the prime after prev_prime(p)+... brackets p tightly.
        for p in [11i128, 13, 17, 97, 101] {
            assert!(is_prime(p));
            assert_eq!(prev_prime(next_prime(p).unwrap()), Some(p));
        }
    }

    #[test]
    fn prime_pi_known_values() {
        assert_eq!(prime_pi(1), 0);
        assert_eq!(prime_pi(2), 1);
        assert_eq!(prime_pi(10), 4);
        assert_eq!(prime_pi(100), 25);
        assert_eq!(prime_pi(0), 0);
        // pi(n) counts exactly the primes in 2..=n.
        let expected = i64::try_from((2i128..=200).filter(|&p| is_prime(p)).count()).unwrap();
        assert_eq!(prime_pi(200), expected);
    }

    #[test]
    fn nth_prime_known_values() {
        assert_eq!(nth_prime(0), None);
        assert_eq!(nth_prime(1), Some(2));
        assert_eq!(nth_prime(2), Some(3));
        assert_eq!(nth_prime(6), Some(13));
        assert_eq!(nth_prime(10), Some(29));
        // nth_prime and prime_pi are inverse: pi(nth_prime(k)) == k.
        for k in 1u32..=25 {
            let p = nth_prime(k).unwrap();
            assert!(is_prime(p));
            assert_eq!(prime_pi(p), i64::from(k), "pi(nth_prime({k}))");
        }
    }

    #[test]
    fn is_carmichael_number_known_values() {
        assert!(is_carmichael_number(561));
        assert!(!is_carmichael_number(560));
        // The first several Carmichael numbers.
        for c in [561i128, 1105, 1729, 2465, 2821, 6601, 8911] {
            assert!(is_carmichael_number(c), "{c} is a Carmichael number");
            // Carmichael numbers are composite but pass the Fermat test.
            assert!(!is_prime(c));
        }
        // Primes and squareful composites are never Carmichael.
        for non in [2i128, 3, 7, 97, 4, 12, 100, 560, 1] {
            assert!(!is_carmichael_number(non), "{non} is not Carmichael");
        }
    }
}
