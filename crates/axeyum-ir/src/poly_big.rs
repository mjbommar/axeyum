//! Arbitrary-precision (bignum) retry path for algebraic-number field arithmetic
//! (nra-cad-nlsat-plan.md, step 2), behind the optional `bignum` feature.
//!
//! This is a **focused duplicate** of the exact-rational resultant + squarefree +
//! Sturm-isolation primitives in the `crate::poly` module, computed over
//! [`num_rational::BigRational`] instead of the `i128`-backed [`Rational`]. It is
//! used **only as a retry** when the `i128` fast path in
//! the `crate::real_algebraic` module declines on intermediate overflow: the algorithm is
//! identical, so a heavy intermediate (e.g. the Sylvester determinant of `√2+√3`)
//! no longer caps out at `i128`, while the *final* defining polynomial and
//! isolating interval — if they fit `i128` — are converted back so the stored
//! [`crate::RealAlgebraic`] representation is unchanged (still `Vec<i128>` + i128
//! [`Rational`]). If the final result does not fit `i128`, the retry declines
//! (`None`): a bignum-backed `RealAlgebraic` is an explicitly-deferred later slice.
//!
//! **Soundness:** the duplication is guarded by a differential test
//! (`real_algebraic_field_bignum.rs`) pinning this module and the `crate::poly`
//! module to the SAME isolating result on small inputs — isolation is soundness-critical.
//! Everything here is exact (no floating point) and bounded (degree/round caps →
//! graceful decline, never OOM/hang).

use core::cmp::Ordering;

use num_bigint::BigInt;
use num_integer::Integer;
use num_rational::BigRational;
use num_traits::{One, Zero};

use crate::rational::Rational;
use crate::real_algebraic::Sign;

/// A bignum-rational univariate polynomial, LSB-first.
type BigVec = Vec<BigRational>;

/// Degree / round guards keeping the bignum retry bounded. Coefficient size is
/// unbounded (that is the whole point), but the Sylvester-matrix DIMENSION, the
/// polynomial degree, and the refinement-round count are capped → graceful
/// decline (never OOM/hang).
///
/// The Sylvester determinant is computed by Leibniz expansion, which is `O(dim!)`
/// in the matrix dimension `dim = deg(p_α) + deg(p_β)`. `BIG_MAX_SYLVESTER_DIM`
/// is therefore a HARD cost cap: beyond it the retry declines *before* building
/// the matrix, so a high-degree combination (e.g. a degree-12 × degree-4 product,
/// `dim = 16`, `16! ≈ 2·10¹³`) declines instantly instead of hanging. A `dim`
/// of 10 (`10! ≈ 3.6·10⁶`) comfortably covers the cases the i128 path can also
/// reach while staying fast. (The i128 path is bounded in practice by its `i128`
/// overflow on those same large dimensions; this is the bignum analogue.)
const BIG_MAX_SYLVESTER_DIM: usize = 10;
const BIG_MAX_DEGREE: usize = BIG_MAX_SYLVESTER_DIM;
const BIG_COMBINE_REFINE_ROUNDS: u32 = 200;
/// Belt-and-suspenders cap on the Euclidean / Sturm-chain iteration count (the
/// result polynomial has degree ≤ `BIG_MAX_SYLVESTER_DIM`).
const BIG_MAX_DEGREE_GUARD: usize = BIG_MAX_SYLVESTER_DIM;

/// How the result interval is derived from the two operand intervals (mirrors
/// `real_algebraic::IntervalCombine`).
#[derive(Clone, Copy)]
pub enum Combine {
    /// `α + β`: `[α.lo+β.lo, α.hi+β.hi]`.
    Sum,
    /// `α · β`: min/max of the four endpoint products.
    Product,
}

/// The outcome of a successful bignum retry: a final defining polynomial and an
/// isolating interval, all in bignum form. The caller converts to `i128` (or
/// declines if it does not fit).
pub struct BigAlgebraic {
    /// LSB-first integer (bignum) defining polynomial.
    pub poly: Vec<BigInt>,
    /// Lower endpoint of the isolating interval (exclusive), bignum-rational.
    pub lo: BigRational,
    /// Upper endpoint of the isolating interval (exclusive), bignum-rational.
    pub hi: BigRational,
}

impl BigAlgebraic {
    /// Convert to the `i128`-backed representation, or `None` if any coefficient or
    /// interval endpoint does not fit `i128`. Never panics.
    #[must_use]
    pub fn to_i128(&self) -> Option<(Vec<i128>, Rational, Rational)> {
        let mut poly = Vec::with_capacity(self.poly.len());
        for c in &self.poly {
            poly.push(bigint_to_i128(c)?);
        }
        let lo = bigrational_to_rational(&self.lo)?;
        let hi = bigrational_to_rational(&self.hi)?;
        Some((poly, lo, hi))
    }
}

/// Lift an `i128` [`Rational`] to a [`BigRational`].
fn rational_to_big(r: Rational) -> BigRational {
    BigRational::new(BigInt::from(r.numerator()), BigInt::from(r.denominator()))
}

/// Lift an LSB-first `i128`-integer polynomial to a bignum-rational polynomial,
/// trailing zeros trimmed.
fn big_from_int(poly: &[i128]) -> BigVec {
    big_trim(
        poly.iter()
            .map(|&c| BigRational::from(BigInt::from(c)))
            .collect(),
    )
}

/// `BigInt` → `i128`, `None` if out of range.
fn bigint_to_i128(b: &BigInt) -> Option<i128> {
    i128::try_from(b.clone()).ok()
}

/// `BigRational` → `i128` [`Rational`], `None` if numerator or denominator is out
/// of `i128` range. The bignum rational is already in lowest terms.
fn bigrational_to_rational(r: &BigRational) -> Option<Rational> {
    let num = bigint_to_i128(r.numer())?;
    let den = bigint_to_i128(r.denom())?;
    Rational::checked_new(num, den)
}

/// Drop trailing zero coefficients.
fn big_trim(mut p: BigVec) -> BigVec {
    while p.last().is_some_and(num_traits::Zero::is_zero) {
        p.pop();
    }
    p
}

/// True degree, `None` for the zero polynomial.
fn big_degree(p: &[BigRational]) -> Option<usize> {
    let mut n = p.len();
    while n > 0 && p[n - 1].is_zero() {
        n -= 1;
    }
    if n == 0 { None } else { Some(n - 1) }
}

/// The sign of a bignum rational.
fn big_sign(r: &BigRational) -> Sign {
    match r.numer().sign() {
        num_bigint::Sign::Minus => Sign::Neg,
        num_bigint::Sign::NoSign => Sign::Zero,
        num_bigint::Sign::Plus => Sign::Pos,
    }
}

/// Formal derivative.
fn big_derivative(p: &[BigRational]) -> BigVec {
    if p.len() <= 1 {
        return Vec::new();
    }
    let mut out = Vec::with_capacity(p.len() - 1);
    for (i, c) in p.iter().enumerate().skip(1) {
        out.push(c * BigRational::from(BigInt::from(i)));
    }
    big_trim(out)
}

/// Exact polynomial remainder `a mod b` (LSB-first), `b ≠ 0`.
fn big_rem(a: &[BigRational], b: &[BigRational]) -> Option<BigVec> {
    let db = big_degree(b)?;
    let lead_b = &b[db];
    let mut r = big_trim(a.to_vec());
    while let Some(dr) = big_degree(&r) {
        if dr < db {
            break;
        }
        let coeff = &r[dr] / lead_b;
        let shift = dr - db;
        for (j, bj) in b[..=db].iter().enumerate() {
            let sub = &coeff * bj;
            r[j + shift] -= sub;
        }
        r = big_trim(r);
        if big_degree(&r).is_some_and(|d| d == dr) {
            return None; // exact arithmetic must cancel the leading term
        }
    }
    Some(r)
}

/// Exact polynomial GCD (monic), bounded by `max_degree` iterations.
fn big_gcd(a: &[BigRational], b: &[BigRational], max_degree: usize) -> Option<BigVec> {
    let mut a = big_trim(a.to_vec());
    let mut b = big_trim(b.to_vec());
    for _ in 0..(max_degree + 4) {
        if big_degree(&b).is_none() {
            return Some(big_make_monic(&a));
        }
        let r = big_rem(&a, &b)?;
        a = b;
        b = r;
    }
    None
}

/// Normalize to monic (bignum division never overflows, so this is total).
fn big_make_monic(p: &[BigRational]) -> BigVec {
    let Some(d) = big_degree(p) else {
        return Vec::new();
    };
    let lead = p[d].clone();
    p[..=d].iter().map(|c| c / &lead).collect()
}

/// Exact division `a / b` assuming `b | a`.
fn big_exact_div(a: &[BigRational], b: &[BigRational]) -> Option<BigVec> {
    let db = big_degree(b)?;
    let lead_b = &b[db];
    let mut r = big_trim(a.to_vec());
    let Some(da) = big_degree(&r) else {
        return Some(Vec::new());
    };
    if da < db {
        return None;
    }
    let mut quot = vec![BigRational::zero(); da - db + 1];
    while let Some(dr) = big_degree(&r) {
        if dr < db {
            break;
        }
        let coeff = &r[dr] / lead_b;
        let shift = dr - db;
        quot[shift] = coeff.clone();
        for (j, bj) in b[..=db].iter().enumerate() {
            let sub = &coeff * bj;
            r[j + shift] -= sub;
        }
        r = big_trim(r);
        if big_degree(&r).is_some_and(|d| d == dr) {
            return None;
        }
    }
    if big_degree(&r).is_some() {
        return None;
    }
    Some(big_trim(quot))
}

/// Squarefree part `p / gcd(p, p')`.
fn big_squarefree_part(p: &[BigRational], max_degree: usize) -> Option<BigVec> {
    let dp = big_degree(p)?;
    if dp == 0 {
        return None;
    }
    let dpoly = big_derivative(p);
    let g = big_gcd(p, &dpoly, max_degree)?;
    match big_degree(&g) {
        Some(0) | None => Some(big_trim(p.to_vec())),
        Some(_) => big_exact_div(p, &g),
    }
}

/// Clear denominators to an LSB-first bignum-integer polynomial (multiply by the
/// LCM of denominators). The multiplier is positive ⇒ real roots unchanged. No
/// coefficient-size cap (the bignum point), but the polynomial must be non-empty.
fn big_to_int_poly(p: &[BigRational]) -> Option<Vec<BigInt>> {
    if p.is_empty() {
        return None;
    }
    let mut lcm = BigInt::one();
    for c in p {
        lcm = lcm.lcm(c.denom());
    }
    let mut out = Vec::with_capacity(p.len());
    for c in p {
        let scaled = c.numer() * &lcm;
        let (q, rem) = scaled.div_rem(c.denom());
        if !rem.is_zero() {
            return None;
        }
        out.push(q);
    }
    while out.len() > 1 && out.last().is_some_and(num_traits::Zero::is_zero) {
        out.pop();
    }
    Some(out)
}

/// Lift an LSB-first bignum-integer polynomial back to bignum-rational.
fn bigint_poly_to_rat(p: &[BigInt]) -> BigVec {
    big_trim(p.iter().map(|c| BigRational::from(c.clone())).collect())
}

/// Exact Horner evaluation of a bignum-rational polynomial at a bignum-rational.
fn big_eval(p: &[BigRational], x: &BigRational) -> BigRational {
    let mut acc = BigRational::zero();
    for c in p.iter().rev() {
        acc = &acc * x + c;
    }
    acc
}

/// Negate a bignum-rational polynomial.
fn big_negate(p: &[BigRational]) -> BigVec {
    p.iter().map(core::ops::Neg::neg).collect()
}

/// Multiply two LSB-first bignum-rational polynomials.
fn big_mul(a: &[BigRational], b: &[BigRational]) -> BigVec {
    if a.is_empty() || b.is_empty() {
        return vec![BigRational::zero()];
    }
    let mut out = vec![BigRational::zero(); a.len() + b.len() - 1];
    for (i, ca) in a.iter().enumerate() {
        if ca.is_zero() {
            continue;
        }
        for (j, cb) in b.iter().enumerate() {
            out[i + j] += ca * cb;
        }
    }
    out
}

/// Add two LSB-first bignum-rational polynomials.
fn big_add(a: &[BigRational], b: &[BigRational]) -> BigVec {
    let n = a.len().max(b.len());
    let mut out = vec![BigRational::zero(); n];
    for (i, slot) in out.iter_mut().enumerate() {
        if let Some(ca) = a.get(i) {
            *slot += ca;
        }
        if let Some(cb) = b.get(i) {
            *slot += cb;
        }
    }
    out
}

/// The Sturm chain `S₀=p, S₁=p', S_{k+1}=−rem(S_{k−1},S_k)` of a squarefree `p`.
fn big_sturm_chain(p: &[BigRational], max_degree: usize) -> Option<Vec<BigVec>> {
    let dp = big_degree(p)?;
    let mut chain: Vec<BigVec> = Vec::with_capacity(dp + 2);
    chain.push(big_trim(p.to_vec()));
    let deriv = big_derivative(p);
    big_degree(&deriv)?; // constant p ⇒ no chain
    chain.push(deriv);
    for _ in 0..(max_degree + 2) {
        let n = chain.len();
        let r = big_rem(&chain[n - 2], &chain[n - 1])?;
        if big_degree(&r).is_none() {
            break;
        }
        chain.push(big_negate(&r));
    }
    Some(chain)
}

/// `V(t)`: sign alternations in the Sturm chain at `t`, dropping zeros.
fn big_sign_changes(chain: &[BigVec], t: &BigRational) -> usize {
    let mut changes = 0usize;
    let mut last: Option<Sign> = None;
    for s in chain {
        let sign = big_sign(&big_eval(s, t));
        if sign == Sign::Zero {
            continue;
        }
        if let Some(prev) = last
            && prev != sign
        {
            changes += 1;
        }
        last = Some(sign);
    }
    changes
}

/// Distinct real roots of squarefree `p` in `(lo, hi]` via `V(lo) − V(hi)`.
fn big_count_roots_in(chain: &[BigVec], lo: &BigRational, hi: &BigRational) -> Option<usize> {
    big_sign_changes(chain, lo).checked_sub(big_sign_changes(chain, hi))
}

// ============================================================================
// Bivariate resultant construction (mirrors `real_algebraic.rs` helpers, in
// bignum). Coefficients (by y-exponent) are LSB-first bignum-rational polys in x.
// ============================================================================

/// Binomial `C(n, k)` as a `BigInt` (exact, never overflows).
fn big_binom(n: usize, k: usize) -> BigInt {
    if k > n {
        return BigInt::zero();
    }
    let k = k.min(n - k);
    let mut num = BigInt::one();
    for i in 0..k {
        num *= BigInt::from(n - i);
        num /= BigInt::from(i + 1);
    }
    num
}

/// `p_α(y)`: coefficients constant in x (each a length-1 vector).
fn big_const_coeffs(poly: &[i128]) -> Vec<BigVec> {
    big_from_int(poly).into_iter().map(|c| vec![c]).collect()
}

/// `p_β(x − y)` as a poly in y whose coefficients are LSB-first polys in x.
fn big_beta_of_x_minus_y(poly: &[i128]) -> Option<Vec<BigVec>> {
    let trimmed = big_from_int(poly);
    let n = big_degree(&trimmed)?;
    if n == 0 || n > BIG_MAX_DEGREE {
        return None;
    }
    let mut out: Vec<BigVec> = vec![Vec::new(); n + 1];
    for (i, slot) in out.iter_mut().enumerate() {
        let mut xcoeffs = vec![BigRational::zero(); n - i + 1];
        let sign = if i % 2 == 0 { 1i32 } else { -1i32 };
        for j in i..=n {
            let bj = &trimmed[j];
            if bj.is_zero() {
                continue;
            }
            let c = big_binom(j, i);
            let term = bj * BigRational::from(c) * BigRational::from(BigInt::from(sign));
            xcoeffs[j - i] += term;
        }
        *slot = xcoeffs;
    }
    Some(out)
}

/// `y^{deg β}·p_β(x / y)` as a poly in y whose coefficients are polys in x.
fn big_beta_homogenized(poly: &[i128]) -> Option<Vec<BigVec>> {
    let trimmed = big_from_int(poly);
    let n = big_degree(&trimmed)?;
    if n == 0 || n > BIG_MAX_DEGREE {
        return None;
    }
    let mut out: Vec<BigVec> = vec![vec![BigRational::zero()]; n + 1];
    for (j, bj) in trimmed.iter().enumerate() {
        if bj.is_zero() {
            continue;
        }
        let k = n - j;
        let mut xcoeffs = vec![BigRational::zero(); j + 1];
        xcoeffs[j] = bj.clone();
        out[k] = xcoeffs;
    }
    Some(out)
}

/// Build the Sylvester matrix (entries are bignum-rational polys in x).
fn big_sylvester_matrix(p_coeffs: &[BigVec], q_coeffs: &[BigVec]) -> Option<Vec<Vec<BigVec>>> {
    let m = p_coeffs.len().checked_sub(1)?;
    let n = q_coeffs.len().checked_sub(1)?;
    if m == 0 || n == 0 {
        return None;
    }
    let dim = m + n;
    let zero_cell = || vec![BigRational::zero()];
    let mut mat: Vec<Vec<BigVec>> = vec![vec![zero_cell(); dim]; dim];
    for (row, slot) in mat.iter_mut().take(n).enumerate() {
        for (j, coeff) in p_coeffs.iter().rev().enumerate() {
            slot[row + j].clone_from(coeff);
        }
    }
    for (i, slot) in mat.iter_mut().skip(n).take(m).enumerate() {
        for (j, coeff) in q_coeffs.iter().rev().enumerate() {
            slot[i + j].clone_from(coeff);
        }
    }
    Some(mat)
}

/// Permutation sign (+1 / −1) by inversion parity.
fn permutation_sign(perm: &[usize]) -> i32 {
    let mut inv = 0usize;
    for i in 0..perm.len() {
        for j in (i + 1)..perm.len() {
            if perm[i] > perm[j] {
                inv += 1;
            }
        }
    }
    if inv % 2 == 0 { 1 } else { -1 }
}

/// Determinant of a polynomial-entry matrix by Leibniz expansion.
fn big_determinant(mat: &[Vec<BigVec>]) -> BigVec {
    let n = mat.len();
    let mut perm: Vec<usize> = (0..n).collect();
    let mut used = vec![false; n];
    let mut acc = vec![BigRational::zero()];
    leibniz(mat, &mut perm, 0, &mut used, &mut acc);
    acc
}

fn leibniz(
    mat: &[Vec<BigVec>],
    perm: &mut [usize],
    col: usize,
    used: &mut [bool],
    acc: &mut BigVec,
) {
    let n = mat.len();
    if col == n {
        let mut prod = vec![BigRational::one()];
        for (i, &c) in perm.iter().enumerate() {
            prod = big_mul(&prod, &mat[i][c]);
        }
        if permutation_sign(perm) < 0 {
            prod = big_negate(&prod);
        }
        *acc = big_add(acc, &prod);
        return;
    }
    for r in 0..n {
        if used[r] {
            continue;
        }
        used[r] = true;
        perm[col] = r;
        leibniz(mat, perm, col + 1, used, acc);
        used[r] = false;
    }
}

/// `Res_y(p_α, p_β')` → squarefree integer (bignum) polynomial. `None` on a
/// degenerate / constant resultant or a guard trip.
fn big_resultant_then_squarefree(pa: &[BigVec], pb: &[BigVec]) -> Option<Vec<BigInt>> {
    let m = pa.len().checked_sub(1)?;
    let n = pb.len().checked_sub(1)?;
    // `dim = m + n` is the Sylvester-matrix dimension and the Leibniz `O(dim!)`
    // cost driver: cap it HARD so a high-degree combination declines fast instead
    // of hanging on a factorial determinant.
    if m == 0 || n == 0 || m + n > BIG_MAX_SYLVESTER_DIM {
        return None;
    }
    let mat = big_sylvester_matrix(pa, pb)?;
    let det = big_determinant(&mat);
    if det.iter().all(num_traits::Zero::is_zero) {
        return None;
    }
    let res_int = big_to_int_poly(&det)?;
    if res_int.len() <= 1 {
        return None;
    }
    let rat = bigint_poly_to_rat(&res_int);
    let sqfree = big_squarefree_part(&rat, BIG_MAX_DEGREE_GUARD)?;
    let q = big_to_int_poly(&sqfree)?;
    if q.len() <= 1 || q.last().is_some_and(num_traits::Zero::is_zero) {
        return None;
    }
    Some(q)
}

// ============================================================================
// Operand-interval refinement (mirrors RealAlgebraic::refine_once in bignum).
// ============================================================================

/// A bignum view of one operand's defining poly + isolating interval, used purely
/// to narrow the interval toward the operand's root.
struct Operand {
    poly: BigVec,
    lo: BigRational,
    hi: BigRational,
}

impl Operand {
    fn new(poly: &[i128], lo: Rational, hi: Rational) -> Operand {
        Operand {
            poly: big_from_int(poly),
            lo: rational_to_big(lo),
            hi: rational_to_big(hi),
        }
    }

    /// One bisection step keeping the half straddling the root. Returns the
    /// midpoint sign; `Sign::Zero` ⇒ the interval collapsed onto an exact root.
    fn refine_once(&mut self) -> Sign {
        let two = BigRational::from(BigInt::from(2));
        let mid = (&self.lo + &self.hi) / two;
        let smid = big_sign(&big_eval(&self.poly, &mid));
        if smid == Sign::Zero {
            self.lo = mid.clone();
            self.hi = mid;
            return Sign::Zero;
        }
        let slo = big_sign(&big_eval(&self.poly, &self.lo));
        if slo == smid {
            self.lo = mid;
        } else {
            self.hi = mid;
        }
        smid
    }
}

/// The candidate result interval for `α ∘ β`.
fn combined_interval(a: &Operand, b: &Operand, how: Combine) -> (BigRational, BigRational) {
    match how {
        Combine::Sum => (&a.lo + &b.lo, &a.hi + &b.hi),
        Combine::Product => {
            let p = [&a.lo * &b.lo, &a.lo * &b.hi, &a.hi * &b.lo, &a.hi * &b.hi];
            let mut lo = p[0].clone();
            let mut hi = p[0].clone();
            for q in &p[1..] {
                if *q < lo {
                    lo = q.clone();
                }
                if *q > hi {
                    hi = q.clone();
                }
            }
            (lo, hi)
        }
    }
}

/// Identify the unique root of squarefree `q` equal to `α ∘ β` and return it (in
/// bignum). Mirrors `real_algebraic::combine_via_interval`.
fn combine(a: &Operand, b: &Operand, q: &[BigInt], how: Combine) -> Option<BigAlgebraic> {
    let qrat = bigint_poly_to_rat(q);
    let chain = big_sturm_chain(&qrat, BIG_MAX_DEGREE_GUARD)?;

    let mut pa = Operand {
        poly: a.poly.clone(),
        lo: a.lo.clone(),
        hi: a.hi.clone(),
    };
    let mut pb = Operand {
        poly: b.poly.clone(),
        lo: b.lo.clone(),
        hi: b.hi.clone(),
    };

    for _ in 0..BIG_COMBINE_REFINE_ROUNDS {
        let (lo, hi) = combined_interval(&pa, &pb, how);
        if lo.cmp(&hi) != Ordering::Less {
            return None;
        }
        let slo = big_sign(&big_eval(&qrat, &lo));
        let shi = big_sign(&big_eval(&qrat, &hi));
        if slo != Sign::Zero && shi != Sign::Zero {
            let count = big_count_roots_in(&chain, &lo, &hi)?;
            if count == 1 && slo != shi {
                return Some(BigAlgebraic {
                    poly: q.to_vec(),
                    lo,
                    hi,
                });
            }
        }
        if pa.refine_once() == Sign::Zero {
            return None;
        }
        if pb.refine_once() == Sign::Zero {
            return None;
        }
    }
    None
}

/// The bignum retry for `α + β` (resp. `α · β`): same algorithm as the `i128`
/// path, in arbitrary precision. Returns the final defining poly + isolating
/// interval in bignum (the caller converts to `i128` or declines).
#[must_use]
pub fn combine_retry(
    a_poly: &[i128],
    a_lo: Rational,
    a_hi: Rational,
    b_poly: &[i128],
    b_lo: Rational,
    b_hi: Rational,
    how: Combine,
) -> Option<BigAlgebraic> {
    let pa = big_const_coeffs(a_poly);
    let pb = match how {
        Combine::Sum => big_beta_of_x_minus_y(b_poly)?,
        Combine::Product => big_beta_homogenized(b_poly)?,
    };
    let q = big_resultant_then_squarefree(&pa, &pb)?;
    let a = Operand::new(a_poly, a_lo, a_hi);
    let b = Operand::new(b_poly, b_lo, b_hi);
    combine(&a, &b, &q, how)
}
