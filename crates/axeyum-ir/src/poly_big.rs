//! Arbitrary-precision (bignum) algebraic-number primitives: the exact-rational
//! resultant + squarefree + Sturm-isolation routines computed over
//! [`num_rational::BigRational`] / [`num_bigint::BigInt`] (ADR-0045 storage
//! widening).
//!
//! Since [`crate::RealAlgebraic`] now stores its defining polynomial and isolating
//! interval in arbitrary precision, **these are THE algebraic field-arithmetic
//! primitives** (no longer an i128 "retry"). Field arithmetic always computes in
//! bignum, so a heavy intermediate (e.g. the Sylvester determinant of `√2+√3`, or
//! a high-degree coupled NRA witness) no longer caps out at `i128`. The
//! single-variable root-isolation primitives over the `i128`-backed
//! [`Rational`](crate::Rational) continue to live in the `crate::poly` module
//! (used by the solver's NRA root
//! isolation, which works in `i128` until it hands a witness to this layer).
//!
//! **Soundness:** these routines are guarded by a differential test
//! (`sylvester_determinant_diff_bignum.rs`) pinning the fast
//! evaluation–interpolation determinant against the reference Leibniz expansion,
//! and (`real_algebraic_field.rs`) pinning the field arithmetic to the known
//! min-polynomials — isolation is soundness-critical. Everything here is exact (no
//! floating point) and bounded (degree/round/dimension caps → graceful decline,
//! never OOM/hang).

use core::cmp::Ordering;

use num_bigint::BigInt;
use num_integer::Integer;
use num_rational::BigRational;
use num_traits::{One, Zero};

use crate::real_algebraic::Sign;

/// A bignum-rational univariate polynomial, LSB-first.
type BigVec = Vec<BigRational>;

/// Degree / round guards keeping the bignum retry bounded. Coefficient size is
/// unbounded (that is the whole point), but the Sylvester-matrix DIMENSION, the
/// polynomial degree, and the refinement-round count are capped → graceful
/// decline (never OOM/hang).
///
/// The Sylvester determinant is now computed by exact evaluation–interpolation
/// (`O(D · dim³)`, `D ≤ Σ row-max degrees`), NOT Leibniz expansion, so the
/// dimension is no longer factorially constrained. `BIG_MAX_SYLVESTER_DIM` remains
/// a HARD bounded-cost cap so a genuinely huge coupled system declines *before*
/// building the matrix (the eval-interpolation cost and the bignum coefficient
/// growth are both polynomial but still grow with `dim`). Raised to 24 (from 10)
/// to reach the higher-degree coupled systems the polynomial-time route now
/// affords — e.g. the dim-16 resultant behind the degree-4 nested-radical
/// coordinates of `x²+y²=4 ∧ x·y=1`. Beyond 24 the retry declines fast instead of
/// risking an OOM/hang on a pathological input.
const BIG_MAX_SYLVESTER_DIM: usize = 24;
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

/// The outcome of a successful field-arithmetic combination: a final defining
/// polynomial and an isolating interval, all in bignum form. This is exactly the
/// representation [`crate::RealAlgebraic`] now stores.
pub struct BigAlgebraic {
    /// LSB-first integer (bignum) defining polynomial.
    pub poly: Vec<BigInt>,
    /// Lower endpoint of the isolating interval (exclusive), bignum-rational.
    pub lo: BigRational,
    /// Upper endpoint of the isolating interval (exclusive), bignum-rational.
    pub hi: BigRational,
}

/// Lift an LSB-first bignum-integer polynomial to a bignum-rational polynomial,
/// trailing zeros trimmed.
fn big_from_bigint(poly: &[BigInt]) -> BigVec {
    big_trim(poly.iter().map(|c| BigRational::from(c.clone())).collect())
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
pub(crate) fn big_sign(r: &BigRational) -> Sign {
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
pub(crate) fn big_eval(p: &[BigRational], x: &BigRational) -> BigRational {
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
fn big_const_coeffs(poly: &[BigInt]) -> Vec<BigVec> {
    big_from_bigint(poly).into_iter().map(|c| vec![c]).collect()
}

/// `p_β(x − y)` as a poly in y whose coefficients are LSB-first polys in x.
fn big_beta_of_x_minus_y(poly: &[BigInt]) -> Option<Vec<BigVec>> {
    let trimmed = big_from_bigint(poly);
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
fn big_beta_homogenized(poly: &[BigInt]) -> Option<Vec<BigVec>> {
    let trimmed = big_from_bigint(poly);
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

/// Determinant of a polynomial-entry matrix by Leibniz expansion (`O(dim!)`).
///
/// Kept as the **reference oracle** for the differential test pinning the fast
/// [`big_determinant`] (evaluation–interpolation) to the same exact coefficient
/// vector. Not on the solver path. Exposed (`pub`) only so that test can call it.
#[doc(hidden)]
#[must_use]
pub fn big_determinant_leibniz(mat: &[Vec<BigVec>]) -> BigVec {
    let n = mat.len();
    let mut perm: Vec<usize> = (0..n).collect();
    let mut used = vec![false; n];
    let mut acc = vec![BigRational::zero()];
    leibniz(mat, &mut perm, 0, &mut used, &mut acc);
    big_trim(acc)
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

/// Determinant of a square matrix of LSB-first bignum-rational polynomials in one
/// variable `x`, returned as the determinant polynomial `R(x)` (LSB-first), by
/// exact evaluation–interpolation (`O(D · dim³)`, `D` bounds `deg R`). Mirrors the
/// `i128`-path [`crate::poly::sylvester_determinant`]. Coefficients are unbounded
/// (the bignum point) so this never overflows; the matrix DIMENSION is the cost
/// driver and is capped by the caller. Exposed (`pub`) for the differential test.
#[doc(hidden)]
#[must_use]
pub fn big_determinant(mat: &[Vec<BigVec>]) -> BigVec {
    let n = mat.len();
    if n == 0 {
        return vec![BigRational::one()];
    }
    // Degree bound D = Σ_i max_j deg(M[i][j]); an all-zero row ⇒ R ≡ 0.
    let mut deg_bound: usize = 0;
    for row in mat {
        let mut row_max: Option<usize> = None;
        for entry in row {
            if let Some(d) = big_degree(entry) {
                row_max = Some(row_max.map_or(d, |m: usize| m.max(d)));
            }
        }
        match row_max {
            None => return vec![BigRational::zero()],
            Some(d) => deg_bound += d,
        }
    }
    let num_points = deg_bound + 1;
    let mut xs: Vec<BigRational> = Vec::with_capacity(num_points);
    let mut ys: Vec<BigRational> = Vec::with_capacity(num_points);
    for k in 0..num_points {
        let x = BigRational::from(BigInt::from(k));
        let scalar = big_eval_poly_matrix(mat, &x);
        let det = big_bareiss_determinant(&scalar);
        xs.push(x);
        ys.push(det);
    }
    big_trim(big_newton_interpolate(&xs, &ys))
}

/// Evaluate every entry of a polynomial-entry matrix at `x` → scalar matrix.
fn big_eval_poly_matrix(mat: &[Vec<BigVec>], x: &BigRational) -> Vec<Vec<BigRational>> {
    mat.iter()
        .map(|row| row.iter().map(|entry| big_eval(entry, x)).collect())
        .collect()
}

/// Exact determinant of a scalar bignum-rational matrix by fraction-free Bareiss
/// elimination with partial pivoting (`O(n³)`, exact). Singular ⇒ zero.
fn big_bareiss_determinant(mat: &[Vec<BigRational>]) -> BigRational {
    let n = mat.len();
    if n == 0 {
        return BigRational::one();
    }
    let mut a: Vec<Vec<BigRational>> = mat.to_vec();
    let mut sign = 1i32;
    let mut prev = BigRational::one();
    for k in 0..n {
        if a[k][k].is_zero() {
            let mut swap_row = None;
            for (i, _) in a.iter().enumerate().skip(k + 1) {
                if !a[i][k].is_zero() {
                    swap_row = Some(i);
                    break;
                }
            }
            match swap_row {
                Some(i) => {
                    a.swap(k, i);
                    sign = -sign;
                }
                None => return BigRational::zero(),
            }
        }
        let pivot = a[k][k].clone();
        for i in (k + 1)..n {
            for j in (k + 1)..n {
                let num = &a[i][j] * &pivot - &a[i][k] * &a[k][j];
                a[i][j] = num / &prev;
            }
            a[i][k] = BigRational::zero();
        }
        prev = pivot;
    }
    let det = a[n - 1][n - 1].clone();
    if sign < 0 { -det } else { det }
}

/// Exact Newton-divided-difference interpolation over bignum rationals: the unique
/// polynomial of degree `< xs.len()` through `(xs[i], ys[i])` (distinct `xs`),
/// LSB-first.
fn big_newton_interpolate(xs: &[BigRational], ys: &[BigRational]) -> BigVec {
    let n = xs.len();
    if n == 0 {
        return vec![BigRational::zero()];
    }
    let mut coeff = ys.to_vec();
    for level in 1..n {
        for i in (level..n).rev() {
            let num = &coeff[i] - &coeff[i - 1];
            let den = &xs[i] - &xs[i - level];
            coeff[i] = num / den;
        }
    }
    let mut result: BigVec = vec![coeff[n - 1].clone()];
    for k in (0..n - 1).rev() {
        let mut next = vec![BigRational::zero(); result.len() + 1];
        for (i, c) in result.iter().enumerate() {
            next[i + 1] += c;
        }
        for (i, c) in result.iter().enumerate() {
            next[i] -= c * &xs[k];
        }
        next[0] += &coeff[k];
        result = next;
    }
    result
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
    fn new(poly: &[BigInt], lo: BigRational, hi: BigRational) -> Operand {
        Operand {
            poly: big_from_bigint(poly),
            lo,
            hi,
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

/// Compute `α + β` (resp. `α · β`) for two algebraic numbers in arbitrary
/// precision: build the resultant, take its squarefree part, and Sturm-isolate the
/// unique result root. Returns the final defining poly + isolating interval in
/// bignum form (exactly [`crate::RealAlgebraic`]'s storage), or `None` on a
/// degree/dimension/round-cap trip (graceful decline, never OOM/hang).
#[must_use]
pub fn combine_retry(
    a_poly: &[BigInt],
    a_lo: &BigRational,
    a_hi: &BigRational,
    b_poly: &[BigInt],
    b_lo: &BigRational,
    b_hi: &BigRational,
    how: Combine,
) -> Option<BigAlgebraic> {
    let pa = big_const_coeffs(a_poly);
    let pb = match how {
        Combine::Sum => big_beta_of_x_minus_y(b_poly)?,
        Combine::Product => big_beta_homogenized(b_poly)?,
    };
    let q = big_resultant_then_squarefree(&pa, &pb)?;
    let a = Operand::new(a_poly, a_lo.clone(), a_hi.clone());
    let b = Operand::new(b_poly, b_lo.clone(), b_hi.clone());
    combine(&a, &b, &q, how)
}

// ============================================================================
// Bignum primitives used directly by the `crate::real_algebraic` value layer
// (sign tests, refinement, divisibility). All exact, no floating point.
// ============================================================================

/// Exact Horner evaluation of an LSB-first **bignum-integer** polynomial at a
/// [`BigRational`]. Always exact (bignum never overflows).
pub(crate) fn big_eval_int_at(poly: &[BigInt], x: &BigRational) -> BigRational {
    let mut acc = BigRational::zero();
    for c in poly.iter().rev() {
        acc = &acc * x + BigRational::from(c.clone());
    }
    acc
}

/// Lift an LSB-first `i128`-integer polynomial to a bignum-integer polynomial.
pub(crate) fn bigint_poly_from_i128(poly: &[i128]) -> Vec<BigInt> {
    poly.iter().map(|&c| BigInt::from(c)).collect()
}

/// Lift an `i128` numerator/denominator pair (a [`crate::Rational`] decomposed)
/// to a [`BigRational`].
pub(crate) fn bigrational_from_i128(num: i128, den: i128) -> BigRational {
    BigRational::new(BigInt::from(num), BigInt::from(den))
}

/// Exact test of whether the LSB-first bignum-integer polynomial `divisor` divides
/// `dividend` over the rationals with zero remainder. `divisor` must be non-zero.
/// Always decides (bignum never overflows).
pub(crate) fn big_poly_divides(divisor: &[BigInt], dividend: &[BigInt]) -> bool {
    let d = big_from_bigint(divisor);
    let n = big_from_bigint(dividend);
    if big_degree(&d).is_none() {
        return false; // zero divisor: treat as "does not divide"
    }
    match big_rem(&n, &d) {
        Some(r) => big_degree(&r).is_none(),
        None => false,
    }
}
