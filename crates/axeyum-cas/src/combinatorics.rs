//! Classical combinatorial numbers — exact and overflow-safe.
//!
//! A small, dependency-light toolbox of the standard integer sequences that
//! recur throughout combinatorics and the theory of generating functions:
//! Bernoulli and Euler numbers, the two kinds of Stirling numbers, Bell
//! numbers, the integer partition function, Catalan numbers, and the
//! Fibonacci/Lucas pair.
//!
//! # Overflow discipline
//!
//! Every routine is written to **never panic on overflow** and to use no
//! `unsafe`. Each result whose exact value can leave the representable range
//! returns [`Option`]: integer sequences land in `i128` and yield `None` when a
//! partial product or sum would exceed it, while [`bernoulli`] returns an exact
//! [`Rational`] (again `None` on `i128` overflow of a numerator or denominator).
//! The heavy lifting reuses [`crate::ntheory::binomial`], which is itself
//! overflow-safe.
//!
//! # Conventions
//!
//! Bernoulli numbers use the convention `B_1 = -1/2`. The Stirling numbers of
//! the first kind are the **unsigned** `c(n, k)` (counts of permutations of `n`
//! elements with `k` cycles). Indices are `u32`; the exact sequence values are
//! what overflows first, so the `u32` domain is never the binding constraint.

use crate::ntheory::binomial;
use axeyum_ir::Rational;

/// Bernoulli number `B_n` as an exact [`Rational`], or `None` on `i128`
/// overflow.
///
/// Uses the convention `B_1 = -1/2` and the recurrence
/// `sum_{k=0}^{n} C(n+1, k) * B_k = 0`, solved for the top term:
/// `B_n = -1/(n+1) * sum_{k=0}^{n-1} C(n+1, k) * B_k`, seeded with `B_0 = 1`.
///
/// The odd-index Bernoulli numbers vanish for `n >= 3`. Overflow becomes more
/// likely as `n` grows because the numerators and denominators grow super-
/// exponentially; `None` is returned rather than a wrapped value.
///
/// # Examples
///
/// ```
/// use axeyum_cas::combinatorics::bernoulli;
/// use axeyum_ir::Rational;
/// assert_eq!(bernoulli(0), Some(Rational::integer(1)));
/// assert_eq!(bernoulli(1), Some(Rational::new(-1, 2)));
/// assert_eq!(bernoulli(2), Some(Rational::new(1, 6)));
/// assert_eq!(bernoulli(6), Some(Rational::new(1, 42)));
/// ```
pub fn bernoulli(n: u32) -> Option<Rational> {
    let target = usize::try_from(n).ok()?;
    let mut values: Vec<Rational> = Vec::with_capacity(target + 1);
    for m in 0..=target {
        if m == 0 {
            values.push(Rational::integer(1));
            continue;
        }
        let upper = i128::try_from(m).ok()? + 1;
        let mut sum = Rational::zero();
        for (k, &b_k) in values.iter().enumerate() {
            let coeff = binomial(upper, i128::try_from(k).ok()?)?;
            let term = Rational::integer(coeff).checked_mul(b_k)?;
            sum = sum.checked_add(term)?;
        }
        // B_m = -sum / (m + 1).
        let b_m = sum.checked_div(Rational::integer(upper))?.checked_neg()?;
        values.push(b_m);
    }
    values.pop()
}

/// Euler number `E_n`, or `None` on `i128` overflow.
///
/// The Euler numbers satisfy `E_0 = 1`, `E_n = 0` for every odd `n`, and for
/// even `n = 2m` the recurrence
/// `E_{2m} = -sum_{k=0}^{m-1} C(2m, 2k) * E_{2k}`. This gives `E_2 = -1`,
/// `E_4 = 5`, `E_6 = -61`, and so on (the signs alternate).
///
/// # Examples
///
/// ```
/// use axeyum_cas::combinatorics::euler_number;
/// assert_eq!(euler_number(0), Some(1));
/// assert_eq!(euler_number(1), Some(0));
/// assert_eq!(euler_number(2), Some(-1));
/// assert_eq!(euler_number(4), Some(5));
/// assert_eq!(euler_number(6), Some(-61));
/// ```
pub fn euler_number(n: u32) -> Option<i128> {
    if !n.is_multiple_of(2) {
        return Some(0);
    }
    let half = usize::try_from(n / 2).ok()?;
    let mut evens: Vec<i128> = Vec::with_capacity(half + 1);
    for j in 0..=half {
        if j == 0 {
            evens.push(1);
            continue;
        }
        let two_j = i128::try_from(j).ok()?.checked_mul(2)?;
        let mut sum: i128 = 0;
        for (k, &e_k) in evens.iter().enumerate() {
            let two_k = i128::try_from(k).ok()?.checked_mul(2)?;
            let term = binomial(two_j, two_k)?.checked_mul(e_k)?;
            sum = sum.checked_add(term)?;
        }
        evens.push(sum.checked_neg()?);
    }
    evens.pop()
}

/// Unsigned Stirling number of the first kind `c(n, k)`, or `None` on `i128`
/// overflow.
///
/// `c(n, k)` counts the permutations of `n` elements having exactly `k`
/// cycles. Computed from the recurrence
/// `c(n, k) = c(n-1, k-1) + (n-1) * c(n-1, k)` with `c(0, 0) = 1`. Returns
/// `Some(0)` whenever `k > n`.
///
/// # Examples
///
/// ```
/// use axeyum_cas::combinatorics::stirling_first;
/// assert_eq!(stirling_first(0, 0), Some(1));
/// assert_eq!(stirling_first(4, 2), Some(11));
/// assert_eq!(stirling_first(5, 3), Some(35));
/// assert_eq!(stirling_first(4, 5), Some(0));
/// ```
pub fn stirling_first(n: u32, k: u32) -> Option<i128> {
    if k > n {
        return Some(0);
    }
    let columns = usize::try_from(k).ok()?;
    let mut row = vec![0i128; columns + 1];
    row[0] = 1; // c(0, 0) = 1.
    for i in 1..=n {
        let weight = i128::from(i - 1); // the (n - 1) factor with n = i.
        let mut next = vec![0i128; columns + 1];
        for j in 1..=columns {
            let scaled = weight.checked_mul(row[j])?;
            next[j] = row[j - 1].checked_add(scaled)?;
        }
        row = next;
    }
    Some(row[columns])
}

/// Stirling number of the second kind `S(n, k)`, or `None` on `i128` overflow.
///
/// `S(n, k)` counts the partitions of an `n`-element set into exactly `k`
/// non-empty blocks. Computed from the recurrence
/// `S(n, k) = k * S(n-1, k) + S(n-1, k-1)` with `S(0, 0) = 1`. Returns
/// `Some(0)` whenever `k > n`.
///
/// # Examples
///
/// ```
/// use axeyum_cas::combinatorics::stirling_second;
/// assert_eq!(stirling_second(0, 0), Some(1));
/// assert_eq!(stirling_second(4, 2), Some(7));
/// assert_eq!(stirling_second(5, 3), Some(25));
/// assert_eq!(stirling_second(4, 5), Some(0));
/// ```
pub fn stirling_second(n: u32, k: u32) -> Option<i128> {
    if k > n {
        return Some(0);
    }
    let columns = usize::try_from(k).ok()?;
    let mut row = vec![0i128; columns + 1];
    row[0] = 1; // S(0, 0) = 1.
    for _ in 1..=n {
        let mut next = vec![0i128; columns + 1];
        for j in 1..=columns {
            let factor = i128::try_from(j).ok()?;
            let scaled = factor.checked_mul(row[j])?;
            next[j] = row[j - 1].checked_add(scaled)?;
        }
        row = next;
    }
    Some(row[columns])
}

/// Bell number `B_n` — the number of partitions of an `n`-element set — or
/// `None` on `i128` overflow.
///
/// Computed with the Bell triangle: the leftmost entry of each row is the
/// rightmost entry of the previous row, every other entry is the sum of its
/// left neighbour and the entry diagonally above-left, and `B_n` is the
/// leftmost entry of row `n`. Equivalently `B_n = sum_k S(n, k)`.
///
/// # Examples
///
/// ```
/// use axeyum_cas::combinatorics::bell;
/// assert_eq!(bell(0), Some(1));
/// assert_eq!(bell(1), Some(1));
/// assert_eq!(bell(2), Some(2));
/// assert_eq!(bell(3), Some(5));
/// assert_eq!(bell(4), Some(15));
/// assert_eq!(bell(5), Some(52));
/// ```
pub fn bell(n: u32) -> Option<i128> {
    let rows = usize::try_from(n).ok()?;
    let mut row = vec![1i128]; // Bell triangle row 0, whose leftmost entry is B_0.
    for _ in 0..rows {
        let mut next = Vec::with_capacity(row.len() + 1);
        next.push(*row.last()?);
        for &above_left in &row {
            let left = *next.last()?;
            next.push(left.checked_add(above_left)?);
        }
        row = next;
    }
    Some(row[0])
}

/// Integer partition count `p(n)` — the number of ways to write `n` as an
/// unordered sum of positive integers — or `None` on `i128` overflow.
///
/// Uses Euler's pentagonal-number-theorem recurrence
/// `p(n) = sum_{k>=1} (-1)^{k+1} [ p(n - g(k)) + p(n - g(-k)) ]`, where
/// `g(k) = k(3k-1)/2` are the generalized pentagonal numbers and terms with a
/// negative argument are dropped. Seeded with `p(0) = 1`.
///
/// # Examples
///
/// ```
/// use axeyum_cas::combinatorics::partition_count;
/// assert_eq!(partition_count(0), Some(1));
/// assert_eq!(partition_count(1), Some(1));
/// assert_eq!(partition_count(5), Some(7));
/// assert_eq!(partition_count(6), Some(11));
/// assert_eq!(partition_count(10), Some(42));
/// ```
pub fn partition_count(n: u32) -> Option<i128> {
    let target = usize::try_from(n).ok()?;
    let mut partitions = vec![0i128; target + 1];
    partitions[0] = 1;
    for i in 1..=target {
        let bound = i128::try_from(i).ok()?;
        let mut total: i128 = 0;
        let mut k: i128 = 1;
        loop {
            // Generalized pentagonal numbers g(k) and g(-k).
            let pent_low = k.checked_mul(k.checked_mul(3)?.checked_sub(1)?)? / 2;
            if pent_low > bound {
                break;
            }
            let sign: i128 = if k.unsigned_abs().is_multiple_of(2) {
                -1
            } else {
                1
            };
            let index_low = i - usize::try_from(pent_low).ok()?;
            total = total.checked_add(sign.checked_mul(partitions[index_low])?)?;

            let pent_high = k.checked_mul(k.checked_mul(3)?.checked_add(1)?)? / 2;
            if pent_high <= bound {
                let index_high = i - usize::try_from(pent_high).ok()?;
                total = total.checked_add(sign.checked_mul(partitions[index_high])?)?;
            }
            k += 1;
        }
        partitions[i] = total;
    }
    Some(partitions[target])
}

/// Catalan number `C_n = C(2n, n) / (n + 1)`, or `None` on `i128` overflow.
///
/// The division is exact because `n + 1` divides `C(2n, n)`, so the result is a
/// genuine integer. Overflow is detected inside the binomial coefficient.
///
/// # Examples
///
/// ```
/// use axeyum_cas::combinatorics::catalan;
/// assert_eq!(catalan(0), Some(1));
/// assert_eq!(catalan(1), Some(1));
/// assert_eq!(catalan(2), Some(2));
/// assert_eq!(catalan(3), Some(5));
/// assert_eq!(catalan(4), Some(14));
/// ```
pub fn catalan(n: u32) -> Option<i128> {
    let n_i = i128::from(n);
    let central = binomial(n_i.checked_mul(2)?, n_i)?;
    Some(central / (n_i + 1))
}

/// Fibonacci number `F_n` (with `F_0 = 0`, `F_1 = 1`), or `None` on `i128`
/// overflow.
///
/// Computed by exact iteration — no floating-point closed form — so the value
/// is exact up to the point at which `F_n` would exceed `i128` (`n = 185`),
/// where `None` is returned.
///
/// # Examples
///
/// ```
/// use axeyum_cas::combinatorics::fibonacci;
/// assert_eq!(fibonacci(0), Some(0));
/// assert_eq!(fibonacci(1), Some(1));
/// assert_eq!(fibonacci(10), Some(55));
/// ```
pub fn fibonacci(n: u32) -> Option<i128> {
    let mut previous: i128 = 0; // F_0
    let mut current: i128 = 1; // F_1
    for _ in 0..n {
        let next = previous.checked_add(current)?;
        previous = current;
        current = next;
    }
    Some(previous)
}

/// Lucas number `L_n` (with `L_0 = 2`, `L_1 = 1`), or `None` on `i128`
/// overflow.
///
/// Computed by the same exact iteration as [`fibonacci`], only with the Lucas
/// seeds; `None` is returned once `L_n` would exceed `i128`.
///
/// # Examples
///
/// ```
/// use axeyum_cas::combinatorics::lucas;
/// assert_eq!(lucas(0), Some(2));
/// assert_eq!(lucas(1), Some(1));
/// assert_eq!(lucas(5), Some(11));
/// ```
pub fn lucas(n: u32) -> Option<i128> {
    let mut previous: i128 = 2; // L_0
    let mut current: i128 = 1; // L_1
    for _ in 0..n {
        let next = previous.checked_add(current)?;
        previous = current;
        current = next;
    }
    Some(previous)
}

/// The **harmonic number** `Hₙ = Σ_{k=1}^{n} 1/k`, exact ([`Rational`]).
/// `H₀ = 0`, `H₁ = 1`, `H₂ = 3/2`, `H₃ = 11/6`, `H₄ = 25/12`. `None` on `i128`
/// overflow of the running numerator/denominator (the denominators grow as
/// `lcm(1..n)`, so this bounds `n` to a few dozen).
///
/// ```
/// use axeyum_cas::combinatorics::harmonic;
/// use axeyum_ir::Rational;
/// assert_eq!(harmonic(3), Some(Rational::new(11, 6)));
/// ```
#[must_use]
pub fn harmonic(n: u32) -> Option<Rational> {
    generalized_harmonic(n, 1)
}

/// The **generalized harmonic number** `H_n^{(r)} = Σ_{k=1}^{n} 1/kʳ`, exact.
/// `H_n^{(1)}` is the ordinary [`harmonic`] number; `H_n^{(2)} → π²/6` as
/// `n → ∞` (cf. [`crate::special::zeta`]). Requires `r ≥ 1` (`r == 0` is
/// rejected); `None` also on `i128` overflow of `kʳ` or the running sum.
///
/// ```
/// use axeyum_cas::combinatorics::generalized_harmonic;
/// use axeyum_ir::Rational;
/// // H_2^{(2)} = 1 + 1/4 = 5/4.
/// assert_eq!(generalized_harmonic(2, 2), Some(Rational::new(5, 4)));
/// ```
#[must_use]
pub fn generalized_harmonic(n: u32, r: u32) -> Option<Rational> {
    if r == 0 {
        return None;
    }
    let mut sum = Rational::zero();
    for k in 1..=n {
        let base = i128::from(k);
        let mut power = 1_i128;
        for _ in 0..r {
            power = power.checked_mul(base)?;
        }
        sum = sum.checked_add(Rational::checked_new(1, power)?)?;
    }
    Some(sum)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn harmonic_numbers_exact() {
        assert_eq!(harmonic(0), Some(Rational::zero()));
        assert_eq!(harmonic(1), Some(Rational::integer(1)));
        assert_eq!(harmonic(2), Some(Rational::new(3, 2)));
        assert_eq!(harmonic(3), Some(Rational::new(11, 6)));
        assert_eq!(harmonic(4), Some(Rational::new(25, 12)));
        // Generalized: H_2^{(2)} = 1 + 1/4 = 5/4; H_3^{(2)} = 1 + 1/4 + 1/9 = 49/36.
        assert_eq!(generalized_harmonic(2, 2), Some(Rational::new(5, 4)));
        assert_eq!(generalized_harmonic(3, 2), Some(Rational::new(49, 36)));
        assert_eq!(generalized_harmonic(3, 0), None);
    }

    #[test]
    fn bernoulli_known_values() {
        assert_eq!(bernoulli(0), Some(Rational::integer(1)));
        assert_eq!(bernoulli(1), Some(Rational::new(-1, 2)));
        assert_eq!(bernoulli(2), Some(Rational::new(1, 6)));
        assert_eq!(bernoulli(4), Some(Rational::new(-1, 30)));
        assert_eq!(bernoulli(6), Some(Rational::new(1, 42)));
        // Odd-index Bernoulli numbers vanish for n >= 3.
        assert_eq!(bernoulli(3), Some(Rational::zero()));
        assert_eq!(bernoulli(5), Some(Rational::zero()));
    }

    #[test]
    fn euler_known_values() {
        assert_eq!(euler_number(0), Some(1));
        assert_eq!(euler_number(2), Some(-1));
        assert_eq!(euler_number(4), Some(5));
        assert_eq!(euler_number(6), Some(-61));
        // Every odd index is zero.
        for odd in [1u32, 3, 5, 7, 9] {
            assert_eq!(euler_number(odd), Some(0), "E_{odd} should be zero");
        }
    }

    #[test]
    fn stirling_first_known_values() {
        assert_eq!(stirling_first(4, 2), Some(11));
        assert_eq!(stirling_first(0, 0), Some(1));
        assert_eq!(stirling_first(5, 3), Some(35));
        assert_eq!(stirling_first(4, 5), Some(0));
        // Row sum of c(n, k) over k equals n!.
        let sum: i128 = (0..=5).map(|k| stirling_first(5, k).unwrap()).sum();
        assert_eq!(sum, 120);
    }

    #[test]
    fn stirling_second_known_values() {
        assert_eq!(stirling_second(4, 2), Some(7));
        assert_eq!(stirling_second(0, 0), Some(1));
        assert_eq!(stirling_second(5, 3), Some(25));
        assert_eq!(stirling_second(4, 5), Some(0));
    }

    #[test]
    fn bell_known_values() {
        assert_eq!(bell(0), Some(1));
        assert_eq!(bell(1), Some(1));
        assert_eq!(bell(2), Some(2));
        assert_eq!(bell(3), Some(5));
        assert_eq!(bell(4), Some(15));
        assert_eq!(bell(5), Some(52));
    }

    #[test]
    fn bell_equals_stirling_row_sum() {
        // Identity: sum_k S(n, k) = B_n. Checked here for n = 5.
        let row_sum: i128 = (0..=5).map(|k| stirling_second(5, k).unwrap()).sum();
        assert_eq!(row_sum, bell(5).unwrap());
        assert_eq!(row_sum, 52);
    }

    #[test]
    fn partition_known_values() {
        let expected = [1i128, 1, 2, 3, 5, 7, 11];
        for (n, &want) in expected.iter().enumerate() {
            assert_eq!(
                partition_count(u32::try_from(n).unwrap()),
                Some(want),
                "p({n})"
            );
        }
        assert_eq!(partition_count(10), Some(42));
    }

    #[test]
    fn catalan_known_values() {
        let expected = [1i128, 1, 2, 5, 14];
        for (n, &want) in expected.iter().enumerate() {
            assert_eq!(catalan(u32::try_from(n).unwrap()), Some(want), "C_{n}");
        }
    }

    #[test]
    fn fibonacci_and_lucas_known_values() {
        assert_eq!(fibonacci(0), Some(0));
        assert_eq!(fibonacci(1), Some(1));
        assert_eq!(fibonacci(10), Some(55));
        assert_eq!(lucas(0), Some(2));
        assert_eq!(lucas(1), Some(1));
        assert_eq!(lucas(5), Some(11));
        // Identity: L_n = F_{n-1} + F_{n+1}, checked for n = 5.
        assert_eq!(
            lucas(5).unwrap(),
            fibonacci(4).unwrap() + fibonacci(6).unwrap()
        );
    }
}
