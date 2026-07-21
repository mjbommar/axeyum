//! Exact descriptive statistics over rational data.
//!
//! Every summary here is computed with exact [`Rational`] arithmetic, so a
//! returned value is the exact statistic, not a floating-point approximation.
//! Functions decline to `None` on the empty input (where the statistic is
//! undefined) or on `i128` rational overflow, never returning a wrong number.
//!
//! The one irrational statistic — the standard deviation, `√variance` — is
//! surfaced at the crate root as a [`CasExpr`](crate::CasExpr) via
//! [`standard_deviation`](crate::standard_deviation); this module exposes the
//! exact rational [`variance`] it is the root of.

use axeyum_ir::Rational;

/// The arithmetic mean `(Σ xᵢ) / n`. `None` if `data` is empty or on overflow.
#[must_use]
pub fn mean(data: &[Rational]) -> Option<Rational> {
    if data.is_empty() {
        return None;
    }
    let mut sum = Rational::zero();
    for value in data {
        sum = sum.checked_add(*value)?;
    }
    let count = Rational::integer(i128::try_from(data.len()).ok()?);
    sum.checked_div(count)
}

/// The median (middle value of the sorted data, or the mean of the two middle
/// values for an even count). `None` if `data` is empty or on overflow.
#[must_use]
pub fn median(data: &[Rational]) -> Option<Rational> {
    if data.is_empty() {
        return None;
    }
    let mut sorted = data.to_vec();
    sorted.sort_unstable();
    let n = sorted.len();
    if n % 2 == 1 {
        Some(sorted[n / 2])
    } else {
        let lower = sorted[n / 2 - 1];
        let upper = sorted[n / 2];
        lower.checked_add(upper)?.checked_div(Rational::integer(2))
    }
}

/// The mode(s): every value tied for the highest frequency, returned sorted
/// ascending. Empty input yields an empty vector. When all values are distinct,
/// every value is a mode (each occurs once).
#[must_use]
pub fn mode(data: &[Rational]) -> Vec<Rational> {
    let mut sorted = data.to_vec();
    sorted.sort_unstable();
    let mut best_count = 0usize;
    let mut runs: Vec<(Rational, usize)> = Vec::new();
    let mut index = 0;
    while index < sorted.len() {
        let value = sorted[index];
        let mut run = 1;
        while index + run < sorted.len() && sorted[index + run] == value {
            run += 1;
        }
        best_count = best_count.max(run);
        runs.push((value, run));
        index += run;
    }
    runs.into_iter()
        .filter(|&(_, count)| count == best_count)
        .map(|(value, _)| value)
        .collect()
}

/// The **population** variance `(1/n) Σ (xᵢ − mean)²`. `None` if `data` is empty
/// or on overflow.
#[must_use]
pub fn variance(data: &[Rational]) -> Option<Rational> {
    variance_over(data, data.len())
}

/// The **sample** variance `(1/(n−1)) Σ (xᵢ − mean)²` (Bessel-corrected). `None`
/// if `data` has fewer than two points or on overflow.
#[must_use]
pub fn sample_variance(data: &[Rational]) -> Option<Rational> {
    if data.len() < 2 {
        return None;
    }
    variance_over(data, data.len() - 1)
}

/// The sum of squared deviations from the mean, divided by `divisor` — the shared
/// core of the population and sample variances. `None` on empty input, a zero
/// divisor, or overflow.
fn variance_over(data: &[Rational], divisor: usize) -> Option<Rational> {
    let mean_value = mean(data)?;
    let mut sum_squares = Rational::zero();
    for value in data {
        let deviation = value.checked_sub(mean_value)?;
        sum_squares = sum_squares.checked_add(deviation.checked_mul(deviation)?)?;
    }
    let denominator = Rational::integer(i128::try_from(divisor).ok()?);
    sum_squares.checked_div(denominator)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn data() -> Vec<Rational> {
        // 2, 4, 4, 4, 5, 5, 7, 9 — the textbook example (mean 5, pop. variance 4).
        [2, 4, 4, 4, 5, 5, 7, 9]
            .into_iter()
            .map(Rational::integer)
            .collect()
    }

    #[test]
    fn mean_is_exact() {
        assert_eq!(mean(&data()), Some(Rational::integer(5)));
        // Fractional mean stays exact: mean(1,2) = 3/2.
        assert_eq!(
            mean(&[Rational::integer(1), Rational::integer(2)]),
            Some(Rational::new(3, 2))
        );
        assert_eq!(mean(&[]), None);
    }

    #[test]
    fn median_handles_odd_and_even() {
        // Even count (8 values) → mean of the two middle values, 4 and 5 → 9/2.
        assert_eq!(median(&data()), Some(Rational::new(9, 2)));
        // Odd count.
        assert_eq!(
            median(&[Rational::integer(3), Rational::integer(1), Rational::integer(2)]),
            Some(Rational::integer(2))
        );
        // Even count with a fractional midpoint: median(1,2,3,4) = 5/2.
        assert_eq!(
            median(&[1, 2, 3, 4].into_iter().map(Rational::integer).collect::<Vec<_>>()),
            Some(Rational::new(5, 2))
        );
    }

    #[test]
    fn mode_finds_all_ties() {
        assert_eq!(mode(&data()), vec![Rational::integer(4)]);
        // Bimodal: 1,1,2,2,3 → {1,2}.
        assert_eq!(
            mode(&[1, 1, 2, 2, 3].into_iter().map(Rational::integer).collect::<Vec<_>>()),
            vec![Rational::integer(1), Rational::integer(2)]
        );
        assert!(mode(&[]).is_empty());
    }

    #[test]
    fn variances_are_exact() {
        // Population variance of the textbook set is exactly 4.
        assert_eq!(variance(&data()), Some(Rational::integer(4)));
        // Sample variance of {1,2,3} = 1: Σ(dev²)=2, /(3−1)=1.
        let small = [1, 2, 3].into_iter().map(Rational::integer).collect::<Vec<_>>();
        assert_eq!(sample_variance(&small), Some(Rational::integer(1)));
        // Population variance of {1,2,3} = 2/3.
        assert_eq!(variance(&small), Some(Rational::new(2, 3)));
        assert_eq!(sample_variance(&[Rational::integer(1)]), None);
    }
}
