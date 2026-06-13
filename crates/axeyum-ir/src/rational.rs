//! Exact rational numbers for linear real arithmetic (ADR-0015).
//!
//! A [`Rational`] is a normalized `i128` fraction: the denominator is always
//! positive, the fraction is in lowest terms, and zero is `0/1`. Normalization
//! makes the representation canonical, so structural `Eq`/`Hash` coincide with
//! value equality and the type can key the term interner. Arithmetic is exact
//! within the `i128` range; overflow is a usage error (the bounded-arithmetic
//! stance of ADR-0014/0015) and panics with a clear message.

/// An exact rational number `num/den` in lowest terms with `den > 0`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Rational {
    num: i128,
    den: i128,
}

impl Default for Rational {
    /// The default rational is zero.
    fn default() -> Self {
        Self::zero()
    }
}

impl Rational {
    /// Creates `num/den` normalized to lowest terms with a positive denominator.
    ///
    /// # Panics
    ///
    /// Panics if `den` is zero, or on `i128` overflow during normalization.
    pub fn new(num: i128, den: i128) -> Self {
        assert!(den != 0, "rational denominator must be non-zero");
        let mut num = num;
        let mut den = den;
        if den < 0 {
            // Move the sign to the numerator (den stays positive). `checked_neg`
            // guards i128::MIN.
            num = num
                .checked_neg()
                .expect("rational numerator negation in range");
            den = den
                .checked_neg()
                .expect("rational denominator negation in range");
        }
        let g = gcd(num.unsigned_abs(), den.unsigned_abs());
        if g > 1 {
            // g divides both exactly; the casts are exact (g <= |num|,|den|).
            #[allow(clippy::cast_possible_wrap)]
            let g = g as i128;
            num /= g;
            den /= g;
        }
        Self { num, den }
    }

    /// The integer `n` as `n/1`.
    pub fn integer(n: i128) -> Self {
        Self { num: n, den: 1 }
    }

    /// Zero (`0/1`).
    pub fn zero() -> Self {
        Self { num: 0, den: 1 }
    }

    /// The numerator (sign lives here).
    pub fn numerator(self) -> i128 {
        self.num
    }

    /// The denominator (always positive).
    pub fn denominator(self) -> i128 {
        self.den
    }

    /// Returns `true` if this is an integer (denominator one).
    pub fn is_integer(self) -> bool {
        self.den == 1
    }

    /// Returns `true` if this is zero.
    pub fn is_zero(self) -> bool {
        self.num == 0
    }

    /// The multiplicative inverse `den/num`.
    ///
    /// # Panics
    ///
    /// Panics if this is zero, or on `i128` overflow during normalization.
    #[must_use]
    pub fn recip(self) -> Self {
        assert!(self.num != 0, "reciprocal of zero rational");
        Self::new(self.den, self.num)
    }
}

impl core::ops::Div for Rational {
    type Output = Self;

    /// Exact division.
    ///
    /// # Panics
    ///
    /// Panics on division by zero or `i128` overflow.
    #[allow(clippy::suspicious_arithmetic_impl)] // division is multiply-by-reciprocal
    fn div(self, other: Self) -> Self {
        self * other.recip()
    }
}

impl core::ops::Neg for Rational {
    type Output = Self;

    /// Exact negation.
    ///
    /// # Panics
    ///
    /// Panics on `i128` overflow (only `num == i128::MIN`).
    fn neg(self) -> Self {
        Self {
            num: self.num.checked_neg().expect("rational negation in range"),
            den: self.den,
        }
    }
}

impl core::ops::Add for Rational {
    type Output = Self;

    /// Exact addition.
    ///
    /// # Panics
    ///
    /// Panics on `i128` overflow.
    fn add(self, other: Self) -> Self {
        // a/b + c/d = (a*d + c*b) / (b*d)
        let ad = self
            .num
            .checked_mul(other.den)
            .expect("rational add overflow");
        let cb = other
            .num
            .checked_mul(self.den)
            .expect("rational add overflow");
        let num = ad.checked_add(cb).expect("rational add overflow");
        let den = self
            .den
            .checked_mul(other.den)
            .expect("rational add overflow");
        Self::new(num, den)
    }
}

impl core::ops::Sub for Rational {
    type Output = Self;

    /// Exact subtraction.
    ///
    /// # Panics
    ///
    /// Panics on `i128` overflow.
    fn sub(self, other: Self) -> Self {
        self + (-other)
    }
}

impl core::ops::Mul for Rational {
    type Output = Self;

    /// Exact multiplication.
    ///
    /// # Panics
    ///
    /// Panics on `i128` overflow.
    fn mul(self, other: Self) -> Self {
        let num = self
            .num
            .checked_mul(other.num)
            .expect("rational mul overflow");
        let den = self
            .den
            .checked_mul(other.den)
            .expect("rational mul overflow");
        Self::new(num, den)
    }
}

impl PartialOrd for Rational {
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Rational {
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        // Denominators are positive, so compare a/b vs c/d by a*d vs c*b.
        let lhs = self
            .num
            .checked_mul(other.den)
            .expect("rational comparison overflow");
        let rhs = other
            .num
            .checked_mul(self.den)
            .expect("rational comparison overflow");
        lhs.cmp(&rhs)
    }
}

impl core::fmt::Display for Rational {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        if self.den == 1 {
            write!(f, "{}", self.num)
        } else {
            write!(f, "{}/{}", self.num, self.den)
        }
    }
}

/// Greatest common divisor of two unsigned magnitudes (Euclid).
fn gcd(mut a: u128, mut b: u128) -> u128 {
    while b != 0 {
        let t = a % b;
        a = b;
        b = t;
    }
    a
}

#[cfg(test)]
mod tests {
    use super::Rational;

    #[test]
    fn normalizes_sign_and_lowest_terms() {
        let r = Rational::new(2, -4);
        assert_eq!(r.numerator(), -1);
        assert_eq!(r.denominator(), 2);
        assert_eq!(Rational::new(6, 3), Rational::integer(2));
        assert_eq!(Rational::new(0, 5), Rational::zero());
    }

    #[test]
    fn arithmetic_is_exact() {
        let third = Rational::new(1, 3);
        let sixth = Rational::new(1, 6);
        assert_eq!(third + sixth, Rational::new(1, 2));
        assert_eq!(third - sixth, Rational::new(1, 6));
        assert_eq!(third * Rational::new(3, 1), Rational::integer(1));
        assert_eq!(-third, Rational::new(-1, 3));
    }

    #[test]
    fn ordering_uses_cross_multiplication() {
        assert!(Rational::new(1, 3) < Rational::new(1, 2));
        assert!(Rational::new(-1, 2) < Rational::zero());
        assert_eq!(Rational::new(2, 4), Rational::new(1, 2));
        assert!(Rational::new(5, 3) > Rational::integer(1));
    }
}
