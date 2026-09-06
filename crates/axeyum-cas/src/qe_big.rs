//! The exact `BigRational` univariate polynomial engine behind [`crate::qe`].
//!
//! Everything the quantifier-elimination module needs from real algebra lives
//! here, over [`num_rational::BigRational`] throughout: polynomial arithmetic,
//! Sturm chains, real-root counting and isolation, the exact sign of one
//! polynomial at a real algebraic number, and the exact position of such a
//! number relative to a rational.
//!
//! # Why not reuse [`crate::sturm`]
//!
//! [`crate::sturm`] and [`crate::algebraic`] are `i128`-rational throughout and
//! report overflow as `None`. That is sound — an overflow becomes a decline,
//! never a verdict — but it is also a **wall**: the first slice of `qe` could
//! not decide `∃x. x² − 10³⁰ = 0`, because the Sturm chain of `x² − 10³⁰`
//! evaluates near a Cauchy bound of `10³⁰ + 1` and squares it. Nothing here can
//! overflow, so nothing here declines for that reason; the only declines are
//! explicit step budgets, and each one is a named constant.
//!
//! # What is exact and how
//!
//! - **Sign of `p` at a rational** — Horner over `BigRational`. Total.
//! - **Distinct real roots of `p` in `(lo, hi]`** — Sturm's theorem on the
//!   chain of the square-free part: `V(lo) − V(hi)`.
//! - **Isolation** — bisection from a Cauchy bound, each output bracket
//!   Sturm-certified to hold exactly one root. A root that is *rational* is
//!   recognised exactly, by testing the simplest rational in the current
//!   bracket (`simplest_between`); this is what keeps small integer roots
//!   printing as `0`, `±1`, `2` rather than as anonymous algebraic numbers.
//! - **Sign of `g` at an algebraic `α`** — `g(α) = 0` is decided *exactly*, by
//!   asking whether `gcd(f, g)` has a root in `α`'s bracket (`f` being `α`'s
//!   defining polynomial, square-free with `α` its only root there). Only when
//!   the answer is "no" do we refine, and then we refine until `g` has **no**
//!   root in the bracket at all — a matching pair of endpoint signs is *not*
//!   sufficient and is not used, because `g` may dip and return between them.
//!
//! Nothing in this module is a heuristic: every `None` is a step budget, named
//! in the returning function's documentation.

use core::cmp::Ordering;

use axeyum_arith::QPoly;
use num_bigint::{BigInt, BigUint};
use num_rational::BigRational;
use num_traits::{One, Zero};

/// How many bisections [`isolate`] will spend separating the real roots of one
/// polynomial before declining. Each step halves an interval, so this is a
/// bound on `log₂(2B / separation)` for a Cauchy bound `B` — comfortable for a
/// `10⁶⁰` coefficient (which needs about 200) and finite for everything else.
const MAX_ISOLATION_STEPS: usize = 4096;

/// How many bisections `exactify` will spend trying to recognise a *rational*
/// root before settling for an algebraic sample. Recognising `10¹⁵` inside a
/// bracket of width `10³⁰` needs about 100.
const MAX_EXACTIFY_STEPS: usize = 512;

/// The largest denominator `exactify` will chase. If the simplest rational in
/// the bracket already has a denominator above this, then so would any rational
/// root (the simplest rational in an interval containing `p/q` has denominator
/// at most `q`), so the search stops — soundly, because failing to recognise a
/// rational root only means the root is carried as an algebraic sample.
const MAX_EXACTIFY_DENOMINATOR: u64 = 1_000_000_000_000;

/// How many bisections the algebraic-sign and algebraic-comparison routines
/// will spend before declining.
const MAX_REFINE_STEPS: usize = 4096;

// ============================================================================
// Polynomial arithmetic over ℚ. LSB-first: `p[k]` is the coefficient of `xᵏ`.
// ============================================================================

/// Drop trailing zero coefficients, so a polynomial has a unique representation
/// and [`degree`] is well defined.
///
/// **Migrated onto `axeyum_arith::QPoly` (ADR-1710 migration slice 4)**, as is
/// every function in this section and [`SturmChain`] below. The
/// `Vec<BigRational>` shape survives at the boundary because `crate::qe`,
/// `crate::qe_fibre` and `crate::qe_bivariate` spell it at some forty call
/// sites; what moved is the arithmetic underneath. The pre-migration bodies are
/// kept in this module's test block as `legacy_*` and are asserted to agree
/// with the shared layer on this module's own corpus.
#[must_use]
pub(crate) fn trim(p: Vec<BigRational>) -> Vec<BigRational> {
    axeyum_arith::trim_coefficients(p)
}

/// The degree, or `None` for the zero polynomial.
#[must_use]
pub(crate) fn degree(p: &[BigRational]) -> Option<usize> {
    axeyum_arith::slice_degree(p)
}

/// `p(x)` by Horner. Exact; cannot overflow.
#[must_use]
pub(crate) fn eval(p: &[BigRational], x: &BigRational) -> BigRational {
    axeyum_arith::evaluate_slice(p, x)
}

/// `-1`, `0`, `1` — the sign of a rational.
#[must_use]
pub(crate) fn sign_of(value: &BigRational) -> i8 {
    axeyum_arith::sign_of_rational(value)
}

/// The sign of `p` at the rational `x`. Total and exact.
#[must_use]
pub(crate) fn sign_at(p: &[BigRational], x: &BigRational) -> i8 {
    axeyum_arith::sign_at_slice(p, x)
}

// `derivative` and `div_exact` are gone: after the migration nothing in this
// module called them, because the two routines that did — `SturmChain::new` and
// `squarefree_part` — now delegate whole. That is a measured consequence of
// ADR-1710 slice 4, not an unrelated tidy-up, and the differential test still
// compares the shared implementations of both against the bodies deleted here.

/// `a · b`.
#[must_use]
pub(crate) fn mul(a: &[BigRational], b: &[BigRational]) -> Vec<BigRational> {
    QPoly::from_slice(a)
        .mul(&QPoly::from_slice(b))
        .into_coefficients()
}

/// The remainder of `a` on division by `b`, over ℚ. `None` when `b` is the zero
/// polynomial.
#[must_use]
pub(crate) fn rem(a: &[BigRational], b: &[BigRational]) -> Option<Vec<BigRational>> {
    QPoly::from_slice(a)
        .rem(&QPoly::from_slice(b))
        .map(QPoly::into_coefficients)
}

/// The polynomial scaled so its leading coefficient is `1`. The zero polynomial
/// is returned as the empty vector.
#[must_use]
pub(crate) fn monic(p: &[BigRational]) -> Vec<BigRational> {
    QPoly::from_slice(p).monic().into_coefficients()
}

/// `gcd(a, b)`, monic. `gcd(0, 0)` is the zero polynomial.
#[must_use]
pub(crate) fn gcd(a: &[BigRational], b: &[BigRational]) -> Vec<BigRational> {
    QPoly::from_slice(a)
        .gcd(&QPoly::from_slice(b))
        .into_coefficients()
}

/// The square-free part `p / gcd(p, p′)`, monic — the polynomial with the same
/// real roots as `p`, each simple. `None` for the zero polynomial.
#[must_use]
pub(crate) fn squarefree_part(p: &[BigRational]) -> Option<Vec<BigRational>> {
    QPoly::from_slice(p)
        .squarefree_part()
        .map(QPoly::into_coefficients)
}

/// A Cauchy bound `B = 1 + maxₖ |aₖ / aₙ|`: every real root of `p` lies in the
/// **open** interval `(−B, B)`. `None` for the zero polynomial or a constant.
#[must_use]
pub(crate) fn cauchy_bound(p: &[BigRational]) -> Option<BigRational> {
    QPoly::from_slice(p).cauchy_bound()
}

// ============================================================================
// Sturm chains.
// ============================================================================

/// The Sturm chain of a polynomial: `s₀ = p`, `s₁ = p′`, `sₖ = −rem(sₖ₋₂, sₖ₋₁)`.
///
/// Built from the **square-free part**, so `V(lo) − V(hi)` is exactly the number
/// of distinct real roots in `(lo, hi]` — the same convention as
/// [`crate::sturm::count_real_roots_in`], which this replaces.
///
/// **Migrated onto `axeyum_arith::SturmChain` (ADR-1710 slice 4).** The shared
/// chain scales every member to a primitive integer polynomial by a *positive*
/// rational, which this one did not. A positive scale changes no sign
/// variation, so the counts are identical on every interval — that equality is
/// asserted directly against the pre-migration chain in
/// `legacy_and_shared_chains_agree_on_every_interval`, over this module's own
/// corpus plus a coefficient far beyond `i128`.
#[derive(Debug, Clone)]
pub(crate) struct SturmChain {
    inner: axeyum_arith::SturmChain,
}

impl SturmChain {
    /// Build the chain for `p`. `None` for the zero polynomial.
    #[must_use]
    pub(crate) fn new(p: &[BigRational]) -> Option<SturmChain> {
        axeyum_arith::SturmChain::new(&QPoly::from_slice(p)).map(|inner| SturmChain { inner })
    }

    /// The number of **distinct** real roots in the half-open `(lo, hi]`.
    #[must_use]
    pub(crate) fn count_in(&self, lo: &BigRational, hi: &BigRational) -> usize {
        self.inner.count_in(lo, hi)
    }
}

/// The number of distinct real roots of `p` in `(lo, hi]`. `None` only for the
/// zero polynomial.
#[must_use]
pub(crate) fn count_roots_in(
    p: &[BigRational],
    lo: &BigRational,
    hi: &BigRational,
) -> Option<usize> {
    let d = degree(p)?;
    if d == 0 {
        return Some(0);
    }
    Some(SturmChain::new(p)?.count_in(lo, hi))
}

/// The number of distinct real roots of `p` in all of ℝ. `None` for the zero
/// polynomial.
#[must_use]
pub(crate) fn count_real_roots(p: &[BigRational]) -> Option<usize> {
    let d = degree(p)?;
    if d == 0 {
        return Some(0);
    }
    let bound = cauchy_bound(p)?;
    Some(SturmChain::new(p)?.count_in(&-bound.clone(), &bound))
}

// ============================================================================
// Isolation.
// ============================================================================

/// One isolated real root of a polynomial: the bracket `(lo, hi]` holds it and
/// nothing else, and `exact` records whether the root **is** the rational `hi`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct IsolatedRoot {
    /// Exclusive lower endpoint; strictly below the root.
    pub(crate) lo: BigRational,
    /// Inclusive upper endpoint; the root itself when `exact`, strictly above
    /// it otherwise.
    pub(crate) hi: BigRational,
    /// Whether the root is exactly the rational `hi`.
    pub(crate) exact: bool,
}

/// Isolate every distinct real root of `p`, ascending.
///
/// Bisection from a Cauchy bound, with a Sturm count deciding each half. Every
/// returned bracket is certified to hold exactly one root, the brackets are
/// pairwise disjoint (`hiⱼ ≤ loⱼ₊₁`), and a rational root is recognised as such
/// whenever the `exactify` budget reaches it.
///
/// `None` for the zero polynomial or when [`MAX_ISOLATION_STEPS`] is exhausted.
#[must_use]
pub(crate) fn isolate(p: &[BigRational]) -> Option<Vec<IsolatedRoot>> {
    let d = degree(p)?;
    if d == 0 {
        return Some(Vec::new());
    }
    let squarefree = squarefree_part(p)?;
    let chain = SturmChain::new(&squarefree)?;
    let bound = cauchy_bound(&squarefree)?;
    let two = BigRational::from_integer(BigInt::from(2));

    let total = chain.count_in(&-bound.clone(), &bound);
    if total == 0 {
        return Some(Vec::new());
    }
    // A work list rather than recursion: the depth is data-dependent and the
    // step budget must be global, not per branch.
    let mut pending: Vec<(BigRational, BigRational, usize)> = vec![(-bound.clone(), bound, total)];
    let mut found: Vec<IsolatedRoot> = Vec::new();
    let mut steps = 0usize;
    while let Some((lo, hi, count)) = pending.pop() {
        if count == 0 {
            continue;
        }
        if count == 1 {
            found.push(exactify(&squarefree, &chain, lo, hi));
            continue;
        }
        steps += 1;
        if steps > MAX_ISOLATION_STEPS {
            return None;
        }
        let mid = (&lo + &hi) / &two;
        let left = chain.count_in(&lo, &mid);
        pending.push((mid.clone(), hi, count - left));
        pending.push((lo, mid, left));
    }
    found.sort_by(|a, b| a.hi.cmp(&b.hi));
    Some(found)
}

/// Narrow `(lo, hi]` around its single root, recognising a rational root
/// exactly when it can.
///
/// At each step the **simplest rational** strictly inside the bracket is tested
/// against `p`. If it is a root then it *is* the root, because the bracket holds
/// exactly one. The search stops early once that simplest rational's denominator
/// passes [`MAX_EXACTIFY_DENOMINATOR`], since the simplest rational in an
/// interval containing `p/q` has denominator at most `q`; failing to recognise a
/// rational root only costs an algebraic sample instead of a rational one, never
/// soundness.
fn exactify(
    p: &[BigRational],
    chain: &SturmChain,
    mut lo: BigRational,
    mut hi: BigRational,
) -> IsolatedRoot {
    let two = BigRational::from_integer(BigInt::from(2));
    if eval(p, &hi).is_zero() {
        return IsolatedRoot {
            lo,
            hi,
            exact: true,
        };
    }
    let denominator_cap = BigUint::from(MAX_EXACTIFY_DENOMINATOR);
    for _ in 0..MAX_EXACTIFY_STEPS {
        let candidate = simplest_between(&lo, &hi);
        if eval(p, &candidate).is_zero() {
            return IsolatedRoot {
                lo,
                hi: candidate,
                exact: true,
            };
        }
        if candidate.denom().magnitude() > &denominator_cap {
            break;
        }
        let mid = (&lo + &hi) / &two;
        if eval(p, &mid).is_zero() {
            return IsolatedRoot {
                lo,
                hi: mid,
                exact: true,
            };
        }
        if chain.count_in(&lo, &mid) == 1 {
            hi = mid;
        } else {
            lo = mid;
        }
    }
    IsolatedRoot {
        lo,
        hi,
        exact: false,
    }
}

/// The rational of smallest denominator strictly between `lo` and `hi`.
///
/// The Stern–Brocot descent: take the integer `⌊lo⌋ + 1` when it lands strictly
/// inside; otherwise the answer is `⌊lo⌋ + 1/simplest(1/(hi−⌊lo⌋), 1/(lo−⌊lo⌋))`,
/// which is one continued-fraction step. Requires `lo < hi`.
#[must_use]
pub(crate) fn simplest_between(lo: &BigRational, hi: &BigRational) -> BigRational {
    let one = BigRational::one();
    let floor = BigRational::from_integer(lo.floor().to_integer());
    let next = &floor + &one;
    if next < *hi {
        return next;
    }
    // No integer strictly inside, so both endpoints share the integer part
    // `floor` and their fractional parts lie in `[0, 1)`.
    let low_fraction = lo - &floor;
    let high_fraction = hi - &floor;
    if low_fraction.is_zero() {
        // `lo` is the integer `floor`; the simplest rational above it and below
        // `hi` is `floor + 1/k` for the smallest admissible `k`.
        let k = (&one / &high_fraction).floor().to_integer() + BigInt::one();
        return &floor + &one / BigRational::from_integer(k);
    }
    let recip_low = &one / &high_fraction;
    let recip_high = &one / &low_fraction;
    &floor + &one / simplest_between(&recip_low, &recip_high)
}

// ============================================================================
// Real algebraic numbers: sign of a polynomial, position against a rational.
// ============================================================================

/// The exact sign of `g` at the unique root `α` of the square-free `f` in
/// `(lo, hi]`.
///
/// `g(α) = 0` is settled *exactly*: `α` is a root of `g` iff `gcd(f, g)` has a
/// root in the bracket, because any root of the gcd there is a root of `f`
/// there, and `α` is `f`'s only one. When `g(α) ≠ 0` the bracket is bisected —
/// tracking `α` by a Sturm count on `f` — until `g` has **no** root in it, at
/// which point `g`'s sign is constant on the bracket and `sign g(hi)` is the
/// answer.
///
/// `None` for a zero defining polynomial or when [`MAX_REFINE_STEPS`] runs out.
#[must_use]
pub(crate) fn sign_at_algebraic(
    g: &[BigRational],
    f: &[BigRational],
    lo: &BigRational,
    hi: &BigRational,
) -> Option<i8> {
    if degree(g).is_none() {
        return Some(0); // the zero polynomial vanishes everywhere
    }
    let f_chain = SturmChain::new(f)?;
    let common = gcd(f, g);
    if degree(&common).is_some_and(|d| d >= 1) {
        let common_chain = SturmChain::new(&common)?;
        if common_chain.count_in(lo, hi) >= 1 {
            return Some(0);
        }
    }
    if degree(g) == Some(0) {
        return Some(sign_of(&g[0]));
    }
    let g_chain = SturmChain::new(g)?;
    let two = BigRational::from_integer(BigInt::from(2));
    let mut lo = lo.clone();
    let mut hi = hi.clone();
    for _ in 0..MAX_REFINE_STEPS {
        if g_chain.count_in(&lo, &hi) == 0 {
            return Some(sign_at(g, &hi));
        }
        let mid = (&lo + &hi) / &two;
        if f_chain.count_in(&lo, &mid) == 1 {
            hi = mid;
        } else {
            lo = mid;
        }
    }
    None
}

/// Where the unique root `α` of the square-free `f` in `(lo, hi]` sits relative
/// to the rational `x`.
///
/// `α = x` is settled exactly by evaluating `f` at `x` and checking `x` lies in
/// the bracket. Otherwise the bracket is bisected until `x` falls outside it.
///
/// `None` for a zero defining polynomial or when [`MAX_REFINE_STEPS`] runs out.
#[must_use]
pub(crate) fn compare_algebraic_to_rational(
    f: &[BigRational],
    lo: &BigRational,
    hi: &BigRational,
    x: &BigRational,
) -> Option<Ordering> {
    let chain = SturmChain::new(f)?;
    if eval(f, x).is_zero() && lo < x && x <= hi {
        return Some(Ordering::Equal);
    }
    let two = BigRational::from_integer(BigInt::from(2));
    let mut lo = lo.clone();
    let mut hi = hi.clone();
    for _ in 0..MAX_REFINE_STEPS {
        if *x <= lo {
            return Some(Ordering::Greater); // α > lo ≥ x
        }
        if *x > hi {
            return Some(Ordering::Less); // α ≤ hi < x
        }
        let mid = (&lo + &hi) / &two;
        if chain.count_in(&lo, &mid) == 1 {
            hi = mid;
        } else {
            lo = mid;
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;
    use axeyum_arith::UnivariatePoly;
    use num_traits::Signed;

    // -----------------------------------------------------------------------
    // The pre-migration bodies, kept verbatim as the differential oracle for
    // ADR-1710 slice 4. They are `legacy_*` and `#[cfg(test)]`: nothing in the
    // shipped module calls them, and they exist only so the assertions below
    // compare two independent implementations rather than one against itself.
    // -----------------------------------------------------------------------

    /// `derivative` and `div_exact` no longer exist in this module — the
    /// migration removed their last internal caller — so the differential test
    /// compares the SHARED implementations, which is what actually replaced
    /// the deleted bodies.
    fn shared_derivative(p: &[BigRational]) -> Vec<BigRational> {
        UnivariatePoly::derivative(&QPoly::from_slice(p)).into_coefficients()
    }

    fn shared_div_exact(a: &[BigRational], b: &[BigRational]) -> Option<Vec<BigRational>> {
        QPoly::from_slice(a)
            .div_exact(&QPoly::from_slice(b))
            .map(QPoly::into_coefficients)
    }

    fn legacy_trim(mut p: Vec<BigRational>) -> Vec<BigRational> {
        while p.last().is_some_and(Zero::is_zero) {
            p.pop();
        }
        p
    }

    fn legacy_degree(p: &[BigRational]) -> Option<usize> {
        p.iter().rposition(|c| !c.is_zero())
    }

    fn legacy_eval(p: &[BigRational], x: &BigRational) -> BigRational {
        let mut acc = BigRational::zero();
        for coeff in p.iter().rev() {
            acc = acc * x + coeff;
        }
        acc
    }

    fn legacy_derivative(p: &[BigRational]) -> Vec<BigRational> {
        if p.len() <= 1 {
            return Vec::new();
        }
        legacy_trim(
            p.iter()
                .enumerate()
                .skip(1)
                .map(|(k, c)| c * BigRational::from_integer(BigInt::from(k)))
                .collect(),
        )
    }

    fn legacy_mul(a: &[BigRational], b: &[BigRational]) -> Vec<BigRational> {
        if a.is_empty() || b.is_empty() {
            return Vec::new();
        }
        let mut out = vec![BigRational::zero(); a.len() + b.len() - 1];
        for (i, left) in a.iter().enumerate() {
            if left.is_zero() {
                continue;
            }
            for (j, right) in b.iter().enumerate() {
                out[i + j] += left * right;
            }
        }
        legacy_trim(out)
    }

    fn legacy_rem(a: &[BigRational], b: &[BigRational]) -> Option<Vec<BigRational>> {
        let b_degree = legacy_degree(b)?;
        let mut remainder = legacy_trim(a.to_vec());
        let leading = b[b_degree].clone();
        while let Some(r_degree) = legacy_degree(&remainder) {
            if r_degree < b_degree {
                break;
            }
            let factor = &remainder[r_degree] / &leading;
            let shift = r_degree - b_degree;
            for (index, coeff) in b.iter().enumerate().take(b_degree + 1) {
                remainder[index + shift] -= &factor * coeff;
            }
            remainder = legacy_trim(remainder);
        }
        Some(remainder)
    }

    fn legacy_monic(p: &[BigRational]) -> Vec<BigRational> {
        match legacy_degree(p) {
            None => Vec::new(),
            Some(d) => {
                let leading = p[d].clone();
                legacy_trim(p.iter().take(d + 1).map(|c| c / &leading).collect())
            }
        }
    }

    fn legacy_gcd(a: &[BigRational], b: &[BigRational]) -> Vec<BigRational> {
        let mut left = legacy_trim(a.to_vec());
        let mut right = legacy_trim(b.to_vec());
        while legacy_degree(&right).is_some() {
            let Some(next) = legacy_rem(&left, &right) else {
                break;
            };
            left = right;
            right = next;
        }
        legacy_monic(&left)
    }

    fn legacy_div_exact(a: &[BigRational], b: &[BigRational]) -> Option<Vec<BigRational>> {
        let b_degree = legacy_degree(b)?;
        let mut remainder = legacy_trim(a.to_vec());
        let leading = b[b_degree].clone();
        let mut quotient: Vec<BigRational> = Vec::new();
        while let Some(r_degree) = legacy_degree(&remainder) {
            if r_degree < b_degree {
                break;
            }
            let factor = &remainder[r_degree] / &leading;
            let shift = r_degree - b_degree;
            if quotient.len() < shift + 1 {
                quotient.resize(shift + 1, BigRational::zero());
            }
            quotient[shift] = factor.clone();
            for (index, coeff) in b.iter().enumerate().take(b_degree + 1) {
                remainder[index + shift] -= &factor * coeff;
            }
            remainder = legacy_trim(remainder);
        }
        Some(legacy_trim(quotient))
    }

    fn legacy_squarefree_part(p: &[BigRational]) -> Option<Vec<BigRational>> {
        legacy_degree(p)?;
        let common = legacy_gcd(p, &legacy_derivative(p));
        if legacy_degree(&common).is_none_or(|d| d == 0) {
            return Some(legacy_monic(p));
        }
        let quotient = legacy_div_exact(p, &common)?;
        Some(legacy_monic(&quotient))
    }

    fn legacy_cauchy_bound(p: &[BigRational]) -> Option<BigRational> {
        let d = legacy_degree(p)?;
        if d == 0 {
            return None;
        }
        let leading = p[d].clone();
        let mut max_ratio = BigRational::zero();
        for coeff in p.iter().take(d) {
            let ratio = (coeff / &leading).abs();
            if ratio > max_ratio {
                max_ratio = ratio;
            }
        }
        Some(max_ratio + BigRational::one())
    }

    /// The pre-migration Sturm chain: members are NOT scaled to primitive
    /// integer polynomials. That is the normalization difference the design
    /// note calls out as slice 4's headline risk.
    fn legacy_sturm_members(p: &[BigRational]) -> Option<Vec<Vec<BigRational>>> {
        let squarefree = legacy_squarefree_part(p)?;
        let mut members = vec![squarefree];
        let first_derivative = legacy_derivative(&members[0]);
        if legacy_degree(&first_derivative).is_none() {
            return Some(members);
        }
        members.push(first_derivative);
        loop {
            let len = members.len();
            let remainder = legacy_rem(&members[len - 2], &members[len - 1])?;
            if legacy_degree(&remainder).is_none() {
                break;
            }
            members.push(remainder.iter().map(core::ops::Neg::neg).collect());
        }
        Some(members)
    }

    fn legacy_variations(members: &[Vec<BigRational>], x: &BigRational) -> usize {
        let mut variations = 0usize;
        let mut previous: Option<i8> = None;
        for member in members {
            let value = legacy_eval(member, x);
            let sign = if value.is_zero() {
                0
            } else if value.is_negative() {
                -1
            } else {
                1
            };
            if sign == 0 {
                continue;
            }
            if previous.is_some_and(|prev| prev != sign) {
                variations += 1;
            }
            previous = Some(sign);
        }
        variations
    }

    fn legacy_count_in(members: &[Vec<BigRational>], lo: &BigRational, hi: &BigRational) -> usize {
        legacy_variations(members, lo).saturating_sub(legacy_variations(members, hi))
    }

    /// The differential corpus: every polynomial the pre-migration module was
    /// exercised on, plus the degenerate shapes (zero, constant, repeated
    /// roots, no real roots) and a coefficient far beyond `i128` — which is the
    /// wall this module's own header says it exists to clear.
    fn differential_corpus() -> Vec<Vec<BigRational>> {
        let huge = BigRational::from_integer(BigInt::from(10u8).pow(30));
        vec![
            vec![],                 // zero
            ip(&[7]),               // nonzero constant
            ip(&[0, 1]),            // x
            ip(&[-2, 1]),           // x - 2
            ip(&[-2, 0, 1]),        // x^2 - 2, irrational roots
            ip(&[1, 0, 1]),         // x^2 + 1, no real roots
            ip(&[1, -2, 1]),        // (x-1)^2, repeated
            ip(&[-6, 11, -6, 1]),   // (x-1)(x-2)(x-3)
            ip(&[-30, 31, -10, 1]), // (x-2)(x-3)(x-5)
            ip(&[0, -1, 0, 1]),     // x^3 - x
            ip(&[-1, 0, 0, 0, 1]),  // x^4 - 1
            ip(&[6, -5, 1]),        // x^2 - 5x + 6
            ip(&[2, -5, 4, -1]),    // -(x-1)^2(x-2)
            vec![frac(1, 2), frac(-3, 4), frac(5, 6)],
            vec![frac(-7, 3), q(0), frac(2, 9), q(1)],
            vec![-huge.clone(), q(0), q(1)], // x^2 - 10^30
            vec![q(1), huge, q(1)],          // 10^30 x, no real roots
        ]
    }

    /// Every migrated primitive agrees with the body it replaced, on the whole
    /// corpus, pairwise where the operation is binary.
    ///
    /// This is the exit criterion the design note's §8 sets for a slice: a
    /// differential test against the copy it replaces, over that copy's own
    /// test corpus. The corpus is 17 polynomials, so 289 ordered pairs.
    #[test]
    fn legacy_and_shared_polynomial_layers_agree() {
        let corpus = differential_corpus();
        assert_eq!(corpus.len(), 17, "the corpus size this test's name claims");
        let points = [q(0), q(1), q(-1), q(2), frac(1, 3), frac(-7, 2), q(1000)];
        let mut pairs = 0usize;
        for a in &corpus {
            assert_eq!(trim(a.clone()), legacy_trim(a.clone()), "trim");
            assert_eq!(degree(a), legacy_degree(a), "degree");
            assert_eq!(shared_derivative(a), legacy_derivative(a), "derivative");
            assert_eq!(monic(a), legacy_monic(a), "monic");
            assert_eq!(squarefree_part(a), legacy_squarefree_part(a), "squarefree");
            assert_eq!(cauchy_bound(a), legacy_cauchy_bound(a), "cauchy");
            for x in &points {
                assert_eq!(eval(a, x), legacy_eval(a, x), "eval");
                assert_eq!(sign_at(a, x), sign_of(&legacy_eval(a, x)), "sign_at");
            }
            for b in &corpus {
                pairs += 1;
                assert_eq!(mul(a, b), legacy_mul(a, b), "mul");
                assert_eq!(rem(a, b), legacy_rem(a, b), "rem");
                assert_eq!(gcd(a, b), legacy_gcd(a, b), "gcd");
                assert_eq!(shared_div_exact(a, b), legacy_div_exact(a, b), "div_exact");
            }
        }
        assert_eq!(pairs, 289, "every ordered pair was compared");
    }

    /// The chains use **different normalizations** — the shared one scales each
    /// member to a primitive integer polynomial, this module's did not — and
    /// still produce the same root count on every interval either can be asked
    /// about. That equality is the whole justification for one chain replacing
    /// six, so it is asserted directly rather than inferred from the counts
    /// matching on a handful of examples.
    #[test]
    fn legacy_and_shared_chains_agree_on_every_interval() {
        let endpoints = [
            q(-1_000_000),
            q(-10),
            q(-3),
            q(-1),
            frac(-1, 2),
            q(0),
            frac(1, 3),
            q(1),
            frac(3, 2),
            q(2),
            frac(5, 2),
            q(3),
            q(10),
            q(1_000_000),
        ];
        let mut compared = 0usize;
        let mut chains = 0usize;
        for p in differential_corpus() {
            let shared = SturmChain::new(&p);
            let legacy = legacy_sturm_members(&p);
            assert_eq!(
                shared.is_some(),
                legacy.is_some(),
                "the two chains decline on the same inputs"
            );
            let (Some(shared), Some(legacy)) = (shared, legacy) else {
                continue;
            };
            chains += 1;
            for lo in &endpoints {
                for hi in &endpoints {
                    if lo > hi {
                        continue;
                    }
                    compared += 1;
                    assert_eq!(
                        shared.count_in(lo, hi),
                        legacy_count_in(&legacy, lo, hi),
                        "root count on ({lo}, {hi}] for {p:?}"
                    );
                }
            }
        }
        assert_eq!(chains, 16, "every non-zero corpus member built a chain");
        assert_eq!(compared, 1680, "every ordered interval pair was compared");
    }

    /// Every count the migrated chain reports carries a certificate that
    /// re-derives it — the chain rebuilt from its own first member, the sign
    /// variations recounted. Nothing in `verify` reuses what `count_in`
    /// computed.
    #[test]
    fn every_migrated_sturm_count_carries_a_verifiable_certificate() {
        let mut verified = 0usize;
        for p in differential_corpus() {
            let Some(chain) = SturmChain::new(&p) else {
                continue;
            };
            let shared = axeyum_arith::SturmChain::new(&QPoly::from_slice(&p)).unwrap();
            for (lo, hi) in [(q(-10), q(10)), (q(0), q(3)), (frac(-1, 2), frac(5, 2))] {
                let certificate = shared.certificate(&lo, &hi);
                assert_eq!(certificate.root_count, chain.count_in(&lo, &hi));
                assert!(
                    certificate.verify(),
                    "certificate for {p:?} on ({lo}, {hi}]"
                );
                verified += 1;
            }
        }
        assert_eq!(verified, 48, "16 chains x 3 intervals");
    }

    fn q(n: i64) -> BigRational {
        BigRational::from_integer(BigInt::from(n))
    }

    fn frac(n: i64, d: i64) -> BigRational {
        BigRational::new(BigInt::from(n), BigInt::from(d))
    }

    fn ip(coeffs: &[i64]) -> Vec<BigRational> {
        coeffs.iter().copied().map(q).collect()
    }

    #[test]
    fn remainder_and_gcd_agree_with_a_known_factorisation() {
        // x³ − x = x(x−1)(x+1); its gcd with x² − 1 is x² − 1 (monic).
        let cubic = ip(&[0, -1, 0, 1]);
        let quadratic = ip(&[-1, 0, 1]);
        assert_eq!(rem(&cubic, &quadratic), Some(Vec::new()));
        assert_eq!(gcd(&cubic, &quadratic), ip(&[-1, 0, 1]));
    }

    #[test]
    fn squarefree_part_collapses_a_double_root() {
        // (x−1)²(x−2) = x³ − 4x² + 5x − 2 → (x−1)(x−2) = x² − 3x + 2.
        assert_eq!(squarefree_part(&ip(&[-2, 5, -4, 1])), Some(ip(&[2, -3, 1])));
    }

    #[test]
    fn sturm_counts_the_distinct_roots_of_a_cubic() {
        let cubic = ip(&[0, -1, 0, 1]); // roots −1, 0, 1
        assert_eq!(count_real_roots(&cubic), Some(3));
        assert_eq!(count_roots_in(&cubic, &q(-2), &q(0)), Some(2));
        assert_eq!(count_roots_in(&cubic, &q(0), &q(2)), Some(1));
        // A nonzero constant has no roots; the zero polynomial has no count.
        assert_eq!(count_real_roots(&ip(&[7])), Some(0));
        assert_eq!(count_real_roots(&[]), None);
    }

    #[test]
    fn isolation_recognises_integer_roots_exactly() {
        let roots = isolate(&ip(&[0, -1, 0, 1])).expect("isolation");
        assert_eq!(roots.len(), 3);
        assert!(roots.iter().all(|r| r.exact), "−1, 0, 1 are all rational");
        assert_eq!(
            roots.iter().map(|r| r.hi.clone()).collect::<Vec<_>>(),
            vec![q(-1), q(0), q(1)]
        );
    }

    #[test]
    fn isolation_recognises_a_non_dyadic_rational_root() {
        // 3x − 1 has the single root 1/3, which no bisection midpoint ever hits.
        let roots = isolate(&ip(&[-1, 3])).expect("isolation");
        assert_eq!(roots.len(), 1);
        assert!(roots[0].exact);
        assert_eq!(roots[0].hi, frac(1, 3));
    }

    #[test]
    fn isolation_leaves_an_irrational_root_as_a_bracket() {
        let roots = isolate(&ip(&[-2, 0, 1])).expect("isolation"); // ±√2
        assert_eq!(roots.len(), 2);
        assert!(roots.iter().all(|r| !r.exact));
        assert!(
            roots[0].hi <= roots[1].lo,
            "brackets are disjoint and ordered"
        );
    }

    #[test]
    fn isolation_survives_a_coefficient_far_beyond_i128() {
        // x² − 10⁶⁰: the roots are ±10³⁰, both exactly rational.
        let mut huge = ip(&[0, 0, 1]);
        huge[0] = -BigRational::from_integer(BigInt::from(10u32).pow(60));
        let roots = isolate(&huge).expect("isolation must not decline");
        assert_eq!(roots.len(), 2);
        assert!(roots.iter().all(|r| r.exact));
        let ten30 = BigRational::from_integer(BigInt::from(10u32).pow(30));
        assert_eq!(roots[1].hi, ten30);
    }

    #[test]
    fn simplest_between_finds_the_smallest_denominator() {
        assert_eq!(simplest_between(&q(0), &q(5)), q(1));
        assert_eq!(simplest_between(&frac(1, 4), &frac(1, 2)), frac(1, 3));
        assert_eq!(simplest_between(&frac(-1, 2), &frac(1, 2)), q(0));
        // An interval starting exactly on an integer.
        assert_eq!(simplest_between(&q(0), &frac(1, 3)), frac(1, 4));
    }

    #[test]
    fn sign_at_an_algebraic_point_decides_zero_exactly() {
        // α = √2, isolated in (1, 2].
        let f = ip(&[-2, 0, 1]);
        assert_eq!(sign_at_algebraic(&f, &f, &q(1), &q(2)), Some(0));
        // x² − 2 shares its root with 2x² − 4 but not with x² − 3.
        assert_eq!(
            sign_at_algebraic(&ip(&[-4, 0, 2]), &f, &q(1), &q(2)),
            Some(0)
        );
        assert_eq!(
            sign_at_algebraic(&ip(&[-3, 0, 1]), &f, &q(1), &q(2)),
            Some(-1)
        );
        // x − 1 is positive at √2; x − 2 is negative there.
        assert_eq!(sign_at_algebraic(&ip(&[-1, 1]), &f, &q(1), &q(2)), Some(1));
        assert_eq!(sign_at_algebraic(&ip(&[-2, 1]), &f, &q(1), &q(2)), Some(-1));
    }

    #[test]
    fn sign_at_an_algebraic_point_is_not_fooled_by_matching_endpoint_signs() {
        // g = (x − 5/4)(x − 3/2) is positive at both endpoints of (1, 2] and
        // negative at √2 ≈ 1.414, which lies between its roots. A checker that
        // compared endpoint signs would answer `+1`.
        let g = mul(&[frac(-5, 4), q(1)], &[frac(-3, 2), q(1)]);
        let f = ip(&[-2, 0, 1]);
        assert_eq!(sign_at(&g, &q(1)), 1);
        assert_eq!(sign_at(&g, &q(2)), 1);
        assert_eq!(sign_at_algebraic(&g, &f, &q(1), &q(2)), Some(-1));
    }

    #[test]
    fn comparison_of_an_algebraic_number_to_a_rational_is_exact() {
        let f = ip(&[-2, 0, 1]); // √2 in (1, 2]
        assert_eq!(
            compare_algebraic_to_rational(&f, &q(1), &q(2), &frac(3, 2)),
            Some(Ordering::Less)
        );
        assert_eq!(
            compare_algebraic_to_rational(&f, &q(1), &q(2), &frac(7, 5)),
            Some(Ordering::Greater)
        );
        // An exact hit: 0 is the root of x in (−1, 0].
        assert_eq!(
            compare_algebraic_to_rational(&ip(&[0, 1]), &q(-1), &q(0), &q(0)),
            Some(Ordering::Equal)
        );
    }
}
