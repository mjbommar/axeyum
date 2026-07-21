//! Full univariate polynomial factorization over the integers and rationals.
//!
//! This module upgrades the crate's linear-factor `factor` to a *complete*
//! factorization into irreducibles over the rationals, including irreducible
//! quadratics and higher (e.g. `x^4 - 1` factors as `(x-1)(x+1)(x^2+1)`, while
//! `x^4 - 10 x^2 + 1` is irreducible over the rationals even though it factors
//! modulo every prime).
//!
//! # Algorithm (Berlekamp–Zassenhaus)
//!
//! The pipeline is the classical Zassenhaus algorithm, as presented in
//! von zur Gathen and Gerhard, *Modern Computer Algebra*, chapters 15 and 16
//! ("Factorization over finite fields" and "Factorization over the rationals"):
//!
//! 1. **Content and primitive part.** Clear denominators and pull out the integer
//!    content, leaving a primitive integer polynomial with a positive leading
//!    coefficient.
//! 2. **Squarefree factorization (Yun).** Split the primitive part into pairwise
//!    coprime squarefree factors, each tagged with its multiplicity, over the
//!    rationals using the exact primitives in `axeyum_ir::poly`.
//! 3. **Factor each squarefree part over the integers:**
//!    - pick a prime `p` that does not divide the leading coefficient and that
//!      keeps the polynomial squarefree modulo `p`;
//!    - factor modulo `p` into monic irreducibles with Berlekamp's deterministic
//!      linear-algebra method (nullspace of the Frobenius map, then splitting by
//!      `gcd` with `h(x) - s` for each field element `s`);
//!    - Hensel-lift the modular factorization to a modulus `p^k` exceeding twice
//!      the Landau–Mignotte coefficient bound, so every true integer factor is
//!      recoverable in the symmetric residue range;
//!    - recombine subsets of the lifted modular factors into true integer factors,
//!      confirmed by exact trial division.
//!
//! # Certification
//!
//! The search steps above (modular factoring, Hensel lifting, recombination) are
//! intricate, but the *answer* is cheaply certified: [`factor_expr`] multiplies the
//! returned factors back together and checks the product against the input with the
//! crate's decidable zero-test [`crate::equal`]. A wrong factorization can never be
//! reported as certified.
//!
//! # Robustness
//!
//! Everything runs in `i128` and is overflow-graceful: every arithmetic step is
//! `checked_*` and every loop is bounded by an explicit iteration cap, so a
//! pathological or too-large input yields `None` (an honest decline) rather than a
//! panic or a hang. No floating point, no randomness, no `unsafe`.

use axeyum_ir::{Rational, poly};

use crate::ntheory::{is_prime, mod_inverse};
use crate::{CasExpr, ZeroTest, equal, normalize};

/// Largest input degree we attempt; above this we decline (recombination is
/// worst-case exponential in the number of modular factors).
const MAX_DEGREE: usize = 32;
/// Largest prime we search when looking for a good reduction prime.
const MAX_PRIME: i128 = 2_000;
/// Largest number of Hensel doubling/increment steps.
const MAX_HENSEL_STEPS: u32 = 256;
/// Largest number of modular factors we will try to recombine.
const MAX_MOD_FACTORS: usize = 20;
/// Cap on the total number of recombination subsets examined.
const MAX_RECOMB_ITERS: u64 = 500_000;
/// Cap on iterations of the Yun squarefree loop.
const MAX_YUN_ITERS: usize = 64;

// ---------------------------------------------------------------------------
// Public API
// ---------------------------------------------------------------------------

/// Factor a univariate polynomial over the rationals into irreducible factors.
///
/// The input is a dense coefficient vector, least-significant coefficient first
/// (index `i` is the coefficient of `x^i`), matching `axeyum_ir::poly`. The result
/// is a list of `(factor, multiplicity)` pairs where each `factor` is a primitive
/// integer polynomial (content one, positive leading coefficient), irreducible over
/// the rationals. Their product raised to the given multiplicities equals the input
/// up to a single rational leading constant (the content and sign, which the caller
/// can recover by comparing leading coefficients).
///
/// Returns `Some(vec![])` for a constant or zero input (no non-constant factors),
/// and `None` on overflow, an input that is too large, or any bounded search
/// declining — never a wrong or partial answer.
pub fn factor_univariate_over_q(poly: &[Rational]) -> Option<Vec<(Vec<Rational>, u32)>> {
    let trimmed = poly::rat_trim(poly.to_vec());
    // The zero polynomial and any nonzero constant have no non-constant factors.
    let degree = match poly::rat_degree(&trimmed) {
        None | Some(0) => return Some(Vec::new()),
        Some(d) => d,
    };
    if degree > MAX_DEGREE {
        return None;
    }
    let squarefree = yun_squarefree(&trimmed)?;
    let mut out: Vec<(Vec<Rational>, u32)> = Vec::new();
    for (factor, multiplicity) in squarefree {
        let multiplicity = u32::try_from(multiplicity).ok()?;
        for irreducible in factor_squarefree_over_z(&factor)? {
            let as_rational: Vec<Rational> =
                irreducible.iter().map(|&c| Rational::integer(c)).collect();
            out.push((as_rational, multiplicity));
        }
    }
    // Deterministic order: by degree, then by coefficient vector.
    out.sort_by(|left, right| {
        left.0
            .len()
            .cmp(&right.0.len())
            .then_with(|| left.0.cmp(&right.0))
    });
    Some(out)
}

/// Fully factor a univariate polynomial expression, returning a factored
/// expression certified equal to the input.
///
/// `expr` must be a univariate polynomial in `var`; any other shape yields `None`.
/// The returned expression is a product of a rational constant and the irreducible
/// factors (each raised to its multiplicity). It is only returned when it is
/// **certified equal** to the input: [`crate::equal`] must report
/// [`ZeroTest::Certified`] with `equal == true` for the re-multiplied product.
/// Returns `None` on overflow, a non-polynomial input, or if certification fails.
pub fn factor_expr(expr: &CasExpr, var: &str) -> Option<CasExpr> {
    let coeffs = poly::rat_trim(normalize(expr)?.to_univariate(var)?);
    let Some(degree) = poly::rat_degree(&coeffs) else {
        return Some(CasExpr::zero());
    };
    let factors = factor_univariate_over_q(&coeffs)?;

    // Reconstruct the product of the irreducible factors and recover the leading
    // rational constant that scales it back to the input.
    let mut product = vec![Rational::integer(1)];
    for (factor, multiplicity) in &factors {
        for _ in 0..*multiplicity {
            product = poly::ratpoly_mul(&product, factor)?;
        }
    }
    let product_degree = poly::rat_degree(&product).unwrap_or(0);
    let constant = coeffs[degree].checked_div(product[product_degree])?;

    let mut expr_factors: Vec<CasExpr> = Vec::new();
    if constant != Rational::integer(1) || factors.is_empty() {
        expr_factors.push(CasExpr::Const(constant));
    }
    for (factor, multiplicity) in &factors {
        let factor_expr = int_rational_slice_to_expr(var, factor)?;
        expr_factors.push(if *multiplicity == 1 {
            factor_expr
        } else {
            factor_expr.pow(*multiplicity)
        });
    }
    let built = match expr_factors.len() {
        0 => CasExpr::one(),
        1 => expr_factors.into_iter().next()?,
        _ => CasExpr::Mul(expr_factors),
    };
    match equal(&built, expr) {
        ZeroTest::Certified { equal: true, .. } => Some(built),
        _ => None,
    }
}

/// Build a canonical polynomial expression `Σ cᵢ · varⁱ` from an integer-valued
/// rational coefficient vector (least-significant first). `None` on degree
/// overflow.
fn int_rational_slice_to_expr(var: &str, coeffs: &[Rational]) -> Option<CasExpr> {
    let mut terms: Vec<CasExpr> = Vec::new();
    for (i, coeff) in coeffs.iter().enumerate() {
        if coeff.is_zero() {
            continue;
        }
        let term = if i == 0 {
            CasExpr::Const(*coeff)
        } else {
            let power = if i == 1 {
                CasExpr::var(var)
            } else {
                CasExpr::var(var).pow(u32::try_from(i).ok()?)
            };
            if *coeff == Rational::integer(1) {
                power
            } else {
                CasExpr::Mul(vec![CasExpr::Const(*coeff), power])
            }
        };
        terms.push(term);
    }
    Some(match terms.len() {
        0 => CasExpr::zero(),
        1 => terms.into_iter().next()?,
        _ => CasExpr::Add(terms),
    })
}

// ---------------------------------------------------------------------------
// Squarefree factorization (Yun's algorithm) over the rationals
// ---------------------------------------------------------------------------

/// Yun's squarefree factorization of a primitive (or arbitrary) rational
/// polynomial `f`: returns pairwise-coprime squarefree factors, each with its
/// multiplicity, such that `f = c · ∏ factorᵢ^{multᵢ}` for a rational constant `c`.
/// `None` on overflow.
fn yun_squarefree(f: &[Rational]) -> Option<Vec<(Vec<Rational>, usize)>> {
    let degree = poly::rat_degree(f)?;
    if degree == 0 {
        return Some(Vec::new());
    }
    let bound = f.len() + 4;
    let derivative = poly::rat_derivative(f)?;
    let common = poly::rat_gcd(f, &derivative, bound)?; // gcd(f, f'), monic
    let mut work = poly::rat_exact_div(f, &common)?; // b₁
    let mut rest = poly::rat_exact_div(&derivative, &common)?; // c₁
    rest = rat_sub(&rest, &poly::rat_derivative(&work)?)?; // d₁ = c₁ − b₁'

    let mut factors: Vec<(Vec<Rational>, usize)> = Vec::new();
    for multiplicity in 1..=MAX_YUN_ITERS {
        let factor = poly::rat_gcd(&work, &rest, bound)?; // aᵢ, monic
        if poly::rat_degree(&factor).unwrap_or(0) >= 1 {
            factors.push((factor.clone(), multiplicity));
        }
        work = poly::rat_exact_div(&work, &factor)?; // bᵢ₊₁
        let quotient = poly::rat_exact_div(&rest, &factor)?; // dᵢ / aᵢ
        rest = rat_sub(&quotient, &poly::rat_derivative(&work)?)?; // dᵢ₊₁
        if poly::rat_degree(&work).unwrap_or(0) == 0 {
            return Some(factors);
        }
    }
    None
}

/// Exact subtraction of two rational polynomials. `None` on overflow.
fn rat_sub(a: &[Rational], b: &[Rational]) -> Option<Vec<Rational>> {
    poly::ratpoly_add(a, &poly::ratpoly_neg(b)?)
}

// ---------------------------------------------------------------------------
// Integer polynomial helpers (least-significant-coefficient first)
// ---------------------------------------------------------------------------

/// Drop trailing zero coefficients so the leading coefficient is nonzero. The
/// zero polynomial becomes the empty vector.
fn ipoly_trim(mut p: Vec<i128>) -> Vec<i128> {
    while p.last() == Some(&0) {
        p.pop();
    }
    p
}

/// The degree of an integer polynomial, or `None` for the zero polynomial.
fn ipoly_degree(p: &[i128]) -> Option<usize> {
    let mut n = p.len();
    while n > 0 && p[n - 1] == 0 {
        n -= 1;
    }
    if n == 0 { None } else { Some(n - 1) }
}

/// The greatest common divisor of two non-negative magnitudes (Euclid).
fn gcd_u128(mut a: u128, mut b: u128) -> u128 {
    while b != 0 {
        let t = a % b;
        a = b;
        b = t;
    }
    a
}

/// Make an integer polynomial primitive: divide out the content (the `gcd` of the
/// coefficient magnitudes) and force a positive leading coefficient. `None` on the
/// zero polynomial or overflow.
fn ipoly_primitive(p: &[i128]) -> Option<Vec<i128>> {
    let trimmed = ipoly_trim(p.to_vec());
    let degree = ipoly_degree(&trimmed)?;
    let mut content: u128 = 0;
    for &c in &trimmed {
        content = gcd_u128(content, c.unsigned_abs());
    }
    if content == 0 {
        return None;
    }
    let content = i128::try_from(content).ok()?;
    let sign = if trimmed[degree] < 0 { -1 } else { 1 };
    let mut out = Vec::with_capacity(trimmed.len());
    for &c in &trimmed {
        out.push(c.checked_div(content)?.checked_mul(sign)?);
    }
    Some(out)
}

/// Convert a rational polynomial to a primitive integer polynomial with a positive
/// leading coefficient. `None` on overflow.
fn rat_to_primitive_int(p: &[Rational]) -> Option<Vec<i128>> {
    let cleared = poly::rat_to_int_poly(p, i128::MAX)?;
    ipoly_primitive(&cleared)
}

/// Exact integer polynomial division `a / b` (both integer polynomials). Returns
/// the quotient when `b` divides `a` exactly over the integers, or `None`
/// otherwise (non-exact division or overflow).
fn ipoly_exact_div(a: &[i128], b: &[i128]) -> Option<Vec<i128>> {
    let db = ipoly_degree(b)?;
    let lead = b[db];
    let mut remainder = ipoly_trim(a.to_vec());
    let Some(da) = ipoly_degree(&remainder) else {
        return Some(Vec::new());
    };
    if da < db {
        return None;
    }
    let mut quotient = vec![0i128; da - db + 1];
    while let Some(dr) = ipoly_degree(&remainder) {
        if dr < db {
            break;
        }
        if remainder[dr] % lead != 0 {
            return None;
        }
        let factor = remainder[dr].checked_div(lead)?;
        let shift = dr - db;
        quotient[shift] = factor;
        for (j, &bj) in b[..=db].iter().enumerate() {
            let sub = factor.checked_mul(bj)?;
            remainder[j + shift] = remainder[j + shift].checked_sub(sub)?;
        }
        remainder = ipoly_trim(remainder);
    }
    if ipoly_degree(&remainder).is_some() {
        return None;
    }
    Some(ipoly_trim(quotient))
}

/// Multiply two integer polynomials modulo `modulus`, with coefficients kept in
/// `0..modulus`. `None` on overflow.
fn poly_mul_mod(a: &[i128], b: &[i128], modulus: i128) -> Option<Vec<i128>> {
    if a.is_empty() || b.is_empty() {
        return Some(Vec::new());
    }
    let mut out = vec![0i128; a.len() + b.len() - 1];
    for (i, &ca) in a.iter().enumerate() {
        if ca == 0 {
            continue;
        }
        for (j, &cb) in b.iter().enumerate() {
            let term = ca.checked_mul(cb)?.rem_euclid(modulus);
            out[i + j] = out[i + j].checked_add(term)?.rem_euclid(modulus);
        }
    }
    Some(reduce_mod(&out, modulus))
}

/// Reduce every coefficient into `0..modulus` and drop trailing zeros.
fn reduce_mod(p: &[i128], modulus: i128) -> Vec<i128> {
    let mut out: Vec<i128> = p.iter().map(|&c| c.rem_euclid(modulus)).collect();
    while out.last() == Some(&0) {
        out.pop();
    }
    out
}

/// Map a coefficient in `0..modulus` to the symmetric range `(-modulus/2,
/// modulus/2]`.
fn symmetric(c: i128, modulus: i128) -> i128 {
    let r = c.rem_euclid(modulus);
    if r > modulus / 2 { r - modulus } else { r }
}

// ---------------------------------------------------------------------------
// Finite-field 𝔽ₚ polynomial arithmetic (coefficients in 0..p)
// ---------------------------------------------------------------------------

/// Subtract `b` from `a` over 𝔽ₚ.
fn fp_sub(a: &[i128], b: &[i128], p: i128) -> Vec<i128> {
    let n = a.len().max(b.len());
    let mut out = vec![0i128; n];
    for (i, slot) in out.iter_mut().enumerate() {
        let ca = a.get(i).copied().unwrap_or(0);
        let cb = b.get(i).copied().unwrap_or(0);
        *slot = (ca - cb).rem_euclid(p);
    }
    reduce_mod(&out, p)
}

/// Multiply two polynomials over 𝔽ₚ. `None` on overflow.
fn fp_mul(a: &[i128], b: &[i128], p: i128) -> Option<Vec<i128>> {
    poly_mul_mod(a, b, p)
}

/// Multiply a polynomial by a scalar over 𝔽ₚ.
fn fp_scale(a: &[i128], scalar: i128, p: i128) -> Vec<i128> {
    let scaled: Vec<i128> = a.iter().map(|&c| (c * scalar).rem_euclid(p)).collect();
    reduce_mod(&scaled, p)
}

/// Make a nonzero polynomial monic over 𝔽ₚ. `None` if it is zero or the leading
/// coefficient is not invertible.
fn fp_make_monic(a: &[i128], p: i128) -> Option<Vec<i128>> {
    let reduced = reduce_mod(a, p);
    let degree = ipoly_degree(&reduced)?;
    let inv = mod_inverse(reduced[degree], p)?;
    Some(fp_scale(&reduced, inv, p))
}

/// Divide `a` by `b` over 𝔽ₚ, returning `(quotient, remainder)`. `None` if `b` is
/// zero or a coefficient is not invertible.
fn fp_divrem(a: &[i128], b: &[i128], p: i128) -> Option<(Vec<i128>, Vec<i128>)> {
    let db = ipoly_degree(b)?;
    let lead_inv = mod_inverse(b[db], p)?;
    let mut remainder = reduce_mod(a, p);
    let Some(da) = ipoly_degree(&remainder) else {
        return Some((Vec::new(), Vec::new()));
    };
    if da < db {
        return Some((Vec::new(), remainder));
    }
    let mut quotient = vec![0i128; da - db + 1];
    while let Some(dr) = ipoly_degree(&remainder) {
        if dr < db {
            break;
        }
        let factor = (remainder[dr] * lead_inv).rem_euclid(p);
        let shift = dr - db;
        quotient[shift] = factor;
        for (j, &bj) in b[..=db].iter().enumerate() {
            let sub = (factor * bj).rem_euclid(p);
            let idx = j + shift;
            remainder[idx] = (remainder[idx] - sub).rem_euclid(p);
        }
        remainder = reduce_mod(&remainder, p);
    }
    Some((reduce_mod(&quotient, p), reduce_mod(&remainder, p)))
}

/// The remainder of `a` divided by `b` over 𝔽ₚ.
fn fp_rem(a: &[i128], b: &[i128], p: i128) -> Option<Vec<i128>> {
    Some(fp_divrem(a, b, p)?.1)
}

/// The monic greatest common divisor of two polynomials over 𝔽ₚ. `None` on
/// overflow or a non-invertible leading coefficient.
fn fp_gcd(left: &[i128], right: &[i128], p: i128) -> Option<Vec<i128>> {
    let mut cur = reduce_mod(left, p);
    let mut next = reduce_mod(right, p);
    let mut guard = 0usize;
    while ipoly_degree(&next).is_some() {
        let rem = fp_rem(&cur, &next, p)?;
        cur = next;
        next = rem;
        guard += 1;
        if guard > MAX_DEGREE + 4 {
            return None;
        }
    }
    if ipoly_degree(&cur).is_none() {
        return Some(Vec::new());
    }
    fp_make_monic(&cur, p)
}

/// `base^exp mod modulus` over 𝔽ₚ, by square-and-multiply. `None` on overflow.
fn fp_pow_mod(base: &[i128], exp: u128, modulus: &[i128], p: i128) -> Option<Vec<i128>> {
    let mut result = vec![1i128];
    let mut factor = fp_rem(base, modulus, p)?;
    let mut remaining = exp;
    while remaining > 0 {
        if remaining & 1 == 1 {
            result = fp_rem(&fp_mul(&result, &factor, p)?, modulus, p)?;
        }
        factor = fp_rem(&fp_mul(&factor, &factor, p)?, modulus, p)?;
        remaining >>= 1;
    }
    Some(reduce_mod(&result, p))
}

/// The formal derivative of a polynomial over 𝔽ₚ.
fn fp_derivative(a: &[i128], p: i128) -> Vec<i128> {
    if a.len() <= 1 {
        return Vec::new();
    }
    let mut out = Vec::with_capacity(a.len() - 1);
    for (i, &c) in a.iter().enumerate().skip(1) {
        let scaled = i128::try_from(i).map_or(0, |k| (c * k).rem_euclid(p));
        out.push(scaled);
    }
    reduce_mod(&out, p)
}

// ---------------------------------------------------------------------------
// Berlekamp factorization over 𝔽ₚ
// ---------------------------------------------------------------------------

/// Factor a monic squarefree polynomial `g` over 𝔽ₚ into its monic irreducible
/// factors, using Berlekamp's deterministic method. `None` on overflow or if a
/// bounded step declines.
fn berlekamp_factor(g: &[i128], p: i128) -> Option<Vec<Vec<i128>>> {
    let g = fp_make_monic(g, p)?;
    let degree = ipoly_degree(&g)?;
    if degree <= 1 {
        return Some(vec![g]);
    }
    // Berlekamp matrix Q: row i holds x^{p·i} mod g = (x^p mod g)^i.
    let x_to_p = fp_pow_mod(&[0, 1], u128::try_from(p).ok()?, &g, p)?;
    let mut rows: Vec<Vec<i128>> = Vec::with_capacity(degree);
    let mut current = vec![1i128];
    for _ in 0..degree {
        rows.push(dense(&current, degree));
        current = fp_rem(&fp_mul(&current, &x_to_p, p)?, &g, p)?;
    }
    // Subtract the identity to form Q − I.
    for (i, row) in rows.iter_mut().enumerate() {
        row[i] = (row[i] - 1).rem_euclid(p);
    }
    // Left nullspace of Q − I = right nullspace of its transpose.
    let transposed = transpose(&rows, degree);
    let basis = fp_right_nullspace(&transposed, degree, p);
    let factor_count = basis.len();
    if factor_count <= 1 {
        return Some(vec![g]);
    }
    if factor_count > MAX_MOD_FACTORS {
        return None;
    }
    berlekamp_split(&g, &basis, factor_count, p)
}

/// Pad a coefficient vector to a dense length-`n` vector.
fn dense(v: &[i128], n: usize) -> Vec<i128> {
    let mut out = vec![0i128; n];
    for (slot, &c) in out.iter_mut().zip(v.iter()) {
        *slot = c;
    }
    out
}

/// Transpose an `n × n` matrix given as rows.
fn transpose(rows: &[Vec<i128>], n: usize) -> Vec<Vec<i128>> {
    let mut out = vec![vec![0i128; n]; n];
    for (i, row) in rows.iter().enumerate() {
        for (j, &value) in row.iter().enumerate() {
            out[j][i] = value;
        }
    }
    out
}

/// A basis for the right nullspace of a square matrix over 𝔽ₚ (Gaussian
/// elimination to reduced row echelon form, then one basis vector per free
/// column).
fn fp_right_nullspace(matrix: &[Vec<i128>], n: usize, p: i128) -> Vec<Vec<i128>> {
    let mut m: Vec<Vec<i128>> = matrix.iter().map(|row| reduce_row(row, n, p)).collect();
    let mut pivot_col_of_row: Vec<Option<usize>> = vec![None; n];
    let mut row = 0usize;
    let mut col = 0usize;
    while row < n && col < n {
        // Find a pivot in this column at or below `row`.
        let mut pivot = None;
        let mut search = row;
        while search < n {
            if m[search][col] != 0 {
                pivot = Some(search);
                break;
            }
            search += 1;
        }
        let Some(pivot) = pivot else {
            col += 1;
            continue;
        };
        m.swap(row, pivot);
        // Normalize the pivot row.
        if let Some(inv) = mod_inverse(m[row][col], p) {
            let mut c = col;
            while c < n {
                m[row][c] = (m[row][c] * inv).rem_euclid(p);
                c += 1;
            }
        }
        // Eliminate the column from all other rows.
        let mut other = 0usize;
        while other < n {
            if other != row && m[other][col] != 0 {
                let factor = m[other][col];
                let mut c = col;
                while c < n {
                    m[other][c] = (m[other][c] - factor * m[row][c]).rem_euclid(p);
                    c += 1;
                }
            }
            other += 1;
        }
        pivot_col_of_row[row] = Some(col);
        row += 1;
        col += 1;
    }
    let pivot_columns: Vec<usize> = pivot_col_of_row.iter().flatten().copied().collect();
    let mut basis: Vec<Vec<i128>> = Vec::new();
    for free in 0..n {
        if pivot_columns.contains(&free) {
            continue;
        }
        let mut vector = vec![0i128; n];
        vector[free] = 1;
        for (r, &pcol) in pivot_col_of_row
            .iter()
            .enumerate()
            .filter_map(|(r, opt)| opt.as_ref().map(|c| (r, c)))
        {
            vector[pcol] = (-m[r][free]).rem_euclid(p);
        }
        basis.push(vector);
    }
    basis
}

/// Reduce a row into `0..p`, padded to length `n`.
fn reduce_row(row: &[i128], n: usize, p: i128) -> Vec<i128> {
    let mut out = vec![0i128; n];
    for (slot, &value) in out.iter_mut().zip(row.iter()) {
        *slot = value.rem_euclid(p);
    }
    out
}

/// Split `g` into `factor_count` monic irreducibles using the Berlekamp
/// subalgebra basis: repeatedly refine the current factor set by `gcd` with
/// `h(x) − s` for every field element `s`.
fn berlekamp_split(
    g: &[i128],
    basis: &[Vec<i128>],
    factor_count: usize,
    p: i128,
) -> Option<Vec<Vec<i128>>> {
    let mut factors: Vec<Vec<i128>> = vec![reduce_mod(g, p)];
    for vector in basis {
        if factors.len() >= factor_count {
            break;
        }
        let h = reduce_mod(vector, p);
        if ipoly_degree(&h).unwrap_or(0) < 1 {
            continue; // constant element: no splitting power
        }
        let mut refined: Vec<Vec<i128>> = Vec::new();
        for factor in &factors {
            if ipoly_degree(factor).unwrap_or(0) <= 1 {
                refined.push(factor.clone());
                continue;
            }
            let mut s = 0i128;
            while s < p {
                let shifted = fp_sub(&h, &[s], p);
                let piece = fp_gcd(factor, &shifted, p)?;
                if ipoly_degree(&piece).unwrap_or(0) >= 1 {
                    refined.push(piece);
                }
                s += 1;
            }
        }
        if !refined.is_empty() {
            factors = refined;
        }
    }
    if factors.len() != factor_count {
        return None;
    }
    let mut monic: Vec<Vec<i128>> = Vec::with_capacity(factors.len());
    for factor in factors {
        monic.push(fp_make_monic(&factor, p)?);
    }
    Some(monic)
}

// ---------------------------------------------------------------------------
// Hensel lifting
// ---------------------------------------------------------------------------

/// Lift a monic factorization `f ≡ ∏ modular_factors (mod p)` of the monic
/// polynomial `f_bar` to modulus `p^k`, returning monic factors modulo `p^k`.
/// `None` on overflow.
fn multifactor_hensel(
    f_bar: &[i128],
    modular_factors: &[Vec<i128>],
    p: i128,
    k: u32,
    big_modulus: i128,
) -> Option<Vec<Vec<i128>>> {
    let mut lifted: Vec<Vec<i128>> = Vec::with_capacity(modular_factors.len());
    let mut running = reduce_mod(f_bar, big_modulus);
    let count = modular_factors.len();
    for (index, target) in modular_factors.iter().enumerate() {
        if index + 1 == count {
            lifted.push(running);
            break;
        }
        // Cofactor modulo p = product of the remaining modular factors = running / target.
        let running_mod_p = reduce_mod(&running, p);
        let (cofactor_mod_p, remainder) = fp_divrem(&running_mod_p, target, p)?;
        if ipoly_degree(&remainder).is_some() {
            return None; // target does not divide the running product mod p
        }
        let (lifted_target, lifted_cofactor) =
            hensel_lift_two(&running, target, &cofactor_mod_p, p, k, big_modulus)?;
        lifted.push(lifted_target);
        running = lifted_cofactor;
    }
    Some(lifted)
}

/// Linear Hensel lifting of a two-factor factorization `f ≡ g·h (mod p)` (with `g`
/// monic and `gcd(g, h) = 1` over 𝔽ₚ) up to modulus `p^k`. Returns `(G, H)` monic
/// modulo `p^k` with `f ≡ G·H`. `None` on overflow or if the factors are not
/// coprime.
fn hensel_lift_two(
    f: &[i128],
    g_mod_p: &[i128],
    h_mod_p: &[i128],
    p: i128,
    k: u32,
    big_modulus: i128,
) -> Option<(Vec<i128>, Vec<i128>)> {
    let g_mod_p = fp_make_monic(g_mod_p, p)?;
    let h_mod_p = fp_make_monic(h_mod_p, p)?;
    let bezout_h = fp_bezout_cofactor(&g_mod_p, &h_mod_p, p)?;

    let mut lifted_g = reduce_mod(&g_mod_p, big_modulus);
    let mut lifted_h = reduce_mod(&h_mod_p, big_modulus);
    let mut modulus = p;
    let mut step = 1u32;
    while step < k {
        if step > MAX_HENSEL_STEPS {
            return None;
        }
        let next_modulus = modulus.checked_mul(p)?;
        let product = poly_mul_mod(&lifted_g, &lifted_h, next_modulus)?;
        let difference = fp_sub(&reduce_mod(f, next_modulus), &product, next_modulus);
        // difference ≡ 0 (mod modulus); the error term is difference / modulus (mod p).
        let error: Vec<i128> = difference
            .iter()
            .map(|&c| c.rem_euclid(next_modulus) / modulus)
            .collect();
        let error = reduce_mod(&error, p);
        // Corrections: u_g = (error · bezout_h) mod g, u_h = (error − u_g·h) / g.
        let u_g = fp_rem(&fp_mul(&error, &bezout_h, p)?, &g_mod_p, p)?;
        let numerator = fp_sub(&error, &fp_mul(&u_g, &h_mod_p, p)?, p);
        let (u_h, check) = fp_divrem(&numerator, &g_mod_p, p)?;
        if ipoly_degree(&check).is_some() {
            return None;
        }
        lifted_g = add_scaled(&lifted_g, &u_g, modulus, next_modulus)?;
        lifted_h = add_scaled(&lifted_h, &u_h, modulus, next_modulus)?;
        modulus = next_modulus;
        step += 1;
    }
    Some((
        reduce_mod(&lifted_g, big_modulus),
        reduce_mod(&lifted_h, big_modulus),
    ))
}

/// The Bezout cofactor `t` of `h` over 𝔽ₚ: a polynomial with `s·g + t·h ≡ 1` for
/// some `s`, computed via the extended Euclidean algorithm and reduced so the
/// derived `s` satisfies `deg s < deg h`. `None` if `g` and `h` are not coprime.
fn fp_bezout_cofactor(g: &[i128], h: &[i128], p: i128) -> Option<Vec<i128>> {
    let (gcd, s, _t) = fp_ext_gcd(g, h, p)?;
    if ipoly_degree(&gcd).unwrap_or(0) != 0 {
        return None; // not coprime
    }
    let inv = mod_inverse(gcd[0], p)?;
    let s_scaled = fp_scale(&s, inv, p);
    // Reduce s modulo h so that deg s < deg h, then recover t = (1 − s·g) / h.
    let s_reduced = fp_rem(&s_scaled, h, p)?;
    let one_minus = fp_sub(&[1], &fp_mul(&s_reduced, g, p)?, p);
    let (t_reduced, remainder) = fp_divrem(&one_minus, h, p)?;
    if ipoly_degree(&remainder).is_some() {
        return None;
    }
    Some(t_reduced)
}

/// Extended Euclidean algorithm over 𝔽ₚ: returns `(gcd, s, t)` with `s·a + t·b =
/// gcd`. `None` on overflow.
fn fp_ext_gcd(left: &[i128], right: &[i128], p: i128) -> Option<(Vec<i128>, Vec<i128>, Vec<i128>)> {
    let mut old_rem = reduce_mod(left, p);
    let mut rem = reduce_mod(right, p);
    let mut old_s = vec![1i128];
    let mut coeff_s: Vec<i128> = Vec::new();
    let mut old_t: Vec<i128> = Vec::new();
    let mut coeff_t = vec![1i128];
    let mut guard = 0usize;
    while ipoly_degree(&rem).is_some() {
        let (quotient, remainder) = fp_divrem(&old_rem, &rem, p)?;
        old_rem = rem;
        rem = remainder;
        let new_s = fp_sub(&old_s, &fp_mul(&quotient, &coeff_s, p)?, p);
        old_s = coeff_s;
        coeff_s = new_s;
        let new_t = fp_sub(&old_t, &fp_mul(&quotient, &coeff_t, p)?, p);
        old_t = coeff_t;
        coeff_t = new_t;
        guard += 1;
        if guard > MAX_DEGREE + 4 {
            return None;
        }
    }
    Some((old_rem, old_s, old_t))
}

/// Compute `base + scale · correction (mod modulus)`, where `correction` has
/// coefficients over 𝔽ₚ. `None` on overflow.
fn add_scaled(base: &[i128], correction: &[i128], scale: i128, modulus: i128) -> Option<Vec<i128>> {
    let n = base.len().max(correction.len());
    let mut out = vec![0i128; n];
    for (i, slot) in out.iter_mut().enumerate() {
        let b = base.get(i).copied().unwrap_or(0);
        let c = correction.get(i).copied().unwrap_or(0);
        let add = c.checked_mul(scale)?.rem_euclid(modulus);
        *slot = b.checked_add(add)?.rem_euclid(modulus);
    }
    Some(reduce_mod(&out, modulus))
}

// ---------------------------------------------------------------------------
// Recombination of lifted modular factors into true integer factors
// ---------------------------------------------------------------------------

/// Recombine lifted modular factors into true irreducible integer factors of the
/// primitive polynomial `f` (with modulus `big_modulus = p^k`). Each candidate
/// subset product, scaled by the current leading coefficient and reduced to the
/// symmetric range, is trial-divided into the remaining polynomial. `None` on
/// overflow or if the iteration cap is exceeded.
fn recombine(lifted: &[Vec<i128>], f: &[i128], big_modulus: i128) -> Option<Vec<Vec<i128>>> {
    let mut pool: Vec<Vec<i128>> = lifted.to_vec();
    let mut remaining = ipoly_primitive(f)?;
    let mut result: Vec<Vec<i128>> = Vec::new();
    let mut iterations: u64 = 0;
    let mut subset_size = 1usize;
    while 2 * subset_size <= pool.len() {
        let mut found = false;
        let mut indices: Vec<usize> = (0..subset_size).collect();
        loop {
            iterations += 1;
            if iterations > MAX_RECOMB_ITERS {
                return None;
            }
            if let Some(candidate) = subset_candidate(&pool, &indices, &remaining, big_modulus)
                && ipoly_degree(&candidate).unwrap_or(0) >= 1
                && let Some(quotient) = ipoly_exact_div(&remaining, &candidate)
            {
                remaining = ipoly_primitive(&quotient).unwrap_or_else(|| vec![1]);
                remove_indices(&mut pool, &indices);
                result.push(candidate);
                found = true;
                break;
            }
            if !next_combination(&mut indices, pool.len()) {
                break;
            }
        }
        if found {
            subset_size = 1;
            if pool.is_empty() {
                break;
            }
        } else {
            subset_size += 1;
        }
    }
    if ipoly_degree(&remaining).unwrap_or(0) >= 1 {
        result.push(ipoly_primitive(&remaining)?);
    }
    Some(result)
}

/// Form the primitive integer candidate for a subset of lifted factors: the monic
/// subset product, scaled by the leading coefficient of the remaining polynomial,
/// reduced to the symmetric residue range, then made primitive. Returns `None`
/// when no candidate can be formed (a degenerate remaining polynomial or an
/// overflow) — the caller simply skips that subset, so the answer stays correct
/// (at worst a coarser, still-certified factorization).
fn subset_candidate(
    pool: &[Vec<i128>],
    indices: &[usize],
    remaining: &[i128],
    big_modulus: i128,
) -> Option<Vec<i128>> {
    let lead = remaining[ipoly_degree(remaining)?];
    let mut product = vec![1i128];
    for &i in indices {
        product = poly_mul_mod(&product, &pool[i], big_modulus)?;
    }
    let lead_mod = lead.rem_euclid(big_modulus);
    let scaled: Vec<i128> = product
        .iter()
        .map(|&c| symmetric((c * lead_mod).rem_euclid(big_modulus), big_modulus))
        .collect();
    ipoly_primitive(&scaled)
}

/// Remove the given (sorted, ascending) indices from `pool`.
fn remove_indices(pool: &mut Vec<Vec<i128>>, indices: &[usize]) {
    for &i in indices.iter().rev() {
        pool.remove(i);
    }
}

/// Advance `indices` to the next `k`-combination of `0..n` in lexicographic order.
/// Returns `false` when the last combination has been passed.
fn next_combination(indices: &mut [usize], n: usize) -> bool {
    let k = indices.len();
    if k == 0 {
        return false;
    }
    let mut i = k - 1;
    loop {
        if indices[i] != i + n - k {
            indices[i] += 1;
            let mut prev = indices[i];
            for slot in &mut indices[i + 1..] {
                prev += 1;
                *slot = prev;
            }
            return true;
        }
        if i == 0 {
            return false;
        }
        i -= 1;
    }
}

// ---------------------------------------------------------------------------
// Driver: factor one squarefree primitive polynomial over ℤ
// ---------------------------------------------------------------------------

/// Factor a squarefree rational polynomial into irreducible primitive integer
/// factors over the integers. `None` on overflow or a bounded decline.
fn factor_squarefree_over_z(squarefree: &[Rational]) -> Option<Vec<Vec<i128>>> {
    let f = rat_to_primitive_int(squarefree)?;
    let degree = ipoly_degree(&f)?;
    if degree == 0 {
        return Some(Vec::new());
    }
    if degree == 1 {
        return Some(vec![f]);
    }
    let lead = f[degree];
    let prime = choose_prime(&f, lead)?;

    // Factor the monic reduction of f modulo p.
    let f_mod_p = fp_make_monic(&reduce_mod(&f, prime), prime)?;
    let modular_factors = berlekamp_factor(&f_mod_p, prime)?;
    if modular_factors.len() == 1 {
        return Some(vec![f]); // irreducible modulo p ⇒ irreducible over ℤ
    }
    if modular_factors.len() > MAX_MOD_FACTORS {
        return None;
    }

    // Choose k so that p^k exceeds twice the Landau–Mignotte bound.
    let (big_modulus, k) = choose_modulus(&f, prime)?;

    // Build the monic image f_bar = lead^{-1} · f (mod p^k) whose modular
    // factorization matches the monic Berlekamp factors.
    let lead_inv = mod_inverse(lead.rem_euclid(big_modulus), big_modulus)?;
    let f_bar: Vec<i128> = f
        .iter()
        .map(|&c| (c.rem_euclid(big_modulus) * lead_inv).rem_euclid(big_modulus))
        .collect();
    let f_bar = reduce_mod(&f_bar, big_modulus);

    let lifted = multifactor_hensel(&f_bar, &modular_factors, prime, k, big_modulus)?;
    recombine(&lifted, &f, big_modulus)
}

/// Pick a prime that does not divide the leading coefficient and keeps `f`
/// squarefree modulo `p`. `None` if none is found below the cap.
fn choose_prime(f: &[i128], lead: i128) -> Option<i128> {
    let mut candidate = 2i128;
    while candidate <= MAX_PRIME {
        if is_prime(candidate) && lead.rem_euclid(candidate) != 0 {
            let reduced = reduce_mod(f, candidate);
            if ipoly_degree(&reduced) == ipoly_degree(f)
                && let Some(monic) = fp_make_monic(&reduced, candidate)
            {
                let derivative = fp_derivative(&monic, candidate);
                if let Some(gcd) = fp_gcd(&monic, &derivative, candidate)
                    && ipoly_degree(&gcd).unwrap_or(0) == 0
                {
                    return Some(candidate);
                }
            }
        }
        candidate += 1;
    }
    None
}

/// Choose `p^k` exceeding twice the Landau–Mignotte coefficient bound for factors
/// of `f`, scaled by the leading coefficient (the leading-coefficient trick).
/// Returns `(p^k, k)`. `None` on overflow.
fn choose_modulus(f: &[i128], p: i128) -> Option<(i128, u32)> {
    let degree = ipoly_degree(f)?;
    let max_norm = f.iter().map(|&c| c.unsigned_abs()).max().unwrap_or(0);
    let lead = f[degree].unsigned_abs();
    // Mignotte: coefficients of a factor are bounded by 2^n · ‖f‖_∞; the
    // leading-coefficient trick multiplies by |lead|. Require p^k > 2 · bound.
    let mut bound: u128 = max_norm;
    for _ in 0..=degree {
        bound = bound.checked_mul(2)?;
    }
    bound = bound.checked_mul(lead.max(1))?;
    let target = bound.checked_mul(2)?.checked_add(1)?;

    let mut modulus: i128 = p;
    let mut k: u32 = 1;
    while (modulus.unsigned_abs()) <= target {
        modulus = modulus.checked_mul(p)?;
        k += 1;
        if k > MAX_HENSEL_STEPS {
            return None;
        }
    }
    // Guard the Hensel multiply: coefficient products stay below modulus².
    modulus.checked_mul(modulus)?;
    Some((modulus, k))
}

/// Bridge a `MultiPoly` univariate view into this module's coefficient world,
/// exercised by the tests to confirm the crate wiring.
#[cfg(test)]
fn multipoly_to_univariate(poly: &crate::MultiPoly, var: &str) -> Option<Vec<Rational>> {
    poly.to_univariate(var)
}

#[cfg(test)]
mod tests {
    use super::*;
    use axeyum_ir::poly;

    /// An integer as a `Rational`.
    fn ri(n: i128) -> Rational {
        Rational::integer(n)
    }

    /// Build a rational coefficient vector from integers (least-significant first).
    fn ints(cs: &[i128]) -> Vec<Rational> {
        cs.iter().map(|&c| ri(c)).collect()
    }

    /// Reconstruct `∏ factorᵢ^{multᵢ}` from a factor list.
    fn product_of(factors: &[(Vec<Rational>, u32)]) -> Vec<Rational> {
        let mut product = vec![ri(1)];
        for (factor, mult) in factors {
            for _ in 0..*mult {
                product = poly::ratpoly_mul(&product, factor).expect("no overflow");
            }
        }
        product
    }

    /// Assert that the factor product equals `input` up to a rational constant.
    fn assert_remultiplies(factors: &[(Vec<Rational>, u32)], input: &[Rational]) {
        let product = product_of(factors);
        let input = poly::rat_trim(input.to_vec());
        let di = poly::rat_degree(&input).expect("nonzero input");
        let dp = poly::rat_degree(&product).expect("nonzero product");
        assert_eq!(di, dp, "degree mismatch: {factors:?}");
        let constant = input[di].checked_div(product[dp]).expect("nonzero lead");
        for i in 0..=di {
            let scaled = product[i].checked_mul(constant).expect("no overflow");
            assert_eq!(scaled, input[i], "coefficient {i} mismatch");
        }
    }

    /// The multiset of factor degrees.
    fn factor_degrees(factors: &[(Vec<Rational>, u32)]) -> Vec<usize> {
        let mut degrees: Vec<usize> = factors
            .iter()
            .map(|(f, _)| poly::rat_degree(f).expect("nonzero factor"))
            .collect();
        degrees.sort_unstable();
        degrees
    }

    #[test]
    fn factors_difference_of_squares() {
        // x² − 1 = (x − 1)(x + 1)
        let input = ints(&[-1, 0, 1]);
        let factors = factor_univariate_over_q(&input).expect("factorable");
        assert_eq!(factors.len(), 2);
        assert_eq!(factor_degrees(&factors), vec![1, 1]);
        assert_remultiplies(&factors, &input);
    }

    #[test]
    fn factors_x4_minus_1() {
        // x⁴ − 1 = (x − 1)(x + 1)(x² + 1)
        let input = ints(&[-1, 0, 0, 0, 1]);
        let factors = factor_univariate_over_q(&input).expect("factorable");
        assert_eq!(factor_degrees(&factors), vec![1, 1, 2]);
        assert_remultiplies(&factors, &input);
    }

    #[test]
    fn factors_into_two_irreducible_quadratics() {
        // x⁴ + 3x² + 2 = (x² + 1)(x² + 2)
        let input = ints(&[2, 0, 3, 0, 1]);
        let factors = factor_univariate_over_q(&input).expect("factorable");
        assert_eq!(factor_degrees(&factors), vec![2, 2]);
        assert_remultiplies(&factors, &input);
        // The two quadratics are exactly x² + 1 and x² + 2.
        let mut present: Vec<Vec<i128>> = factors
            .iter()
            .map(|(f, _)| f.iter().map(|c| c.numerator()).collect())
            .collect();
        present.sort();
        assert_eq!(present, vec![vec![1, 0, 1], vec![2, 0, 1]]);
    }

    #[test]
    fn irreducible_quadratic_stays_intact() {
        // x² − 2 is irreducible over ℚ (no rational roots).
        let input = ints(&[-2, 0, 1]);
        let factors = factor_univariate_over_q(&input).expect("factorable");
        assert_eq!(factors.len(), 1);
        assert_eq!(factor_degrees(&factors), vec![2]);
        assert_remultiplies(&factors, &input);
    }

    #[test]
    fn swinnerton_dyer_quartic_is_irreducible() {
        // x⁴ − 10x² + 1 is irreducible over ℚ (roots ±√2 ± √3) yet reducible modulo
        // every prime — the classic recombination stress test.
        let input = ints(&[1, 0, -10, 0, 1]);
        let factors = factor_univariate_over_q(&input).expect("factorable");
        assert_eq!(factors.len(), 1, "must not split over ℚ");
        assert_eq!(factor_degrees(&factors), vec![4]);
        assert_remultiplies(&factors, &input);
    }

    #[test]
    fn content_is_pulled_out() {
        // 2x² − 4 = 2·(x² − 2); the primitive factor is x² − 2.
        let input = ints(&[-4, 0, 2]);
        let factors = factor_univariate_over_q(&input).expect("factorable");
        assert_eq!(factors.len(), 1);
        assert_eq!(factor_degrees(&factors), vec![2]);
        let (factor, mult) = &factors[0];
        assert_eq!(*mult, 1);
        assert_eq!(
            factor.iter().map(|c| c.numerator()).collect::<Vec<_>>(),
            vec![-2, 0, 1]
        );
        assert_remultiplies(&factors, &input);
    }

    #[test]
    fn repeated_factors_carry_multiplicity() {
        // (x − 1)² (x + 2) = x³ − 3x + 2  →  x³ + 0x² − 3x + 2
        let input = ints(&[2, -3, 0, 1]);
        let factors = factor_univariate_over_q(&input).expect("factorable");
        assert_remultiplies(&factors, &input);
        // Expect a degree-1 factor of multiplicity 2 and another of multiplicity 1.
        let mut mults: Vec<u32> = factors.iter().map(|(_, m)| *m).collect();
        mults.sort_unstable();
        assert_eq!(mults, vec![1, 2]);
    }

    #[test]
    fn factor_expr_is_certified_equal() {
        let x = || CasExpr::var("x");
        // x⁴ − 1
        let f = x().pow(4) - CasExpr::int(1);
        let factored = factor_expr(&f, "x").expect("factorable");
        match equal(&factored, &f) {
            ZeroTest::Certified { equal, .. } => assert!(equal, "not certified equal"),
            ZeroTest::Unknown => panic!("expected a decidable result"),
        }
        // x⁴ + 3x² + 2
        let g = x().pow(4) + CasExpr::int(3) * x().pow(2) + CasExpr::int(2);
        let factored = factor_expr(&g, "x").expect("factorable");
        match equal(&factored, &g) {
            ZeroTest::Certified { equal, .. } => assert!(equal),
            ZeroTest::Unknown => panic!("expected a decidable result"),
        }
    }

    #[test]
    fn factor_expr_handles_content_and_irreducibles() {
        let x = || CasExpr::var("x");
        // 2x² − 4  →  2·(x² − 2), certified.
        let f = CasExpr::int(2) * x().pow(2) - CasExpr::int(4);
        let factored = factor_expr(&f, "x").expect("factorable");
        match equal(&factored, &f) {
            ZeroTest::Certified { equal, .. } => assert!(equal),
            ZeroTest::Unknown => panic!("expected a decidable result"),
        }
        // x⁴ − 10x² + 1 is irreducible; factor_expr must still certify (as itself).
        let g = x().pow(4) - CasExpr::int(10) * x().pow(2) + CasExpr::int(1);
        let factored = factor_expr(&g, "x").expect("factorable");
        match equal(&factored, &g) {
            ZeroTest::Certified { equal, .. } => assert!(equal),
            ZeroTest::Unknown => panic!("expected a decidable result"),
        }
    }

    #[test]
    fn constant_and_zero_inputs() {
        assert_eq!(factor_univariate_over_q(&ints(&[5])), Some(Vec::new()));
        assert_eq!(factor_univariate_over_q(&[]), Some(Vec::new()));
    }

    #[test]
    fn multipoly_bridge_roundtrips() {
        let expr = CasExpr::var("x").pow(2) - CasExpr::int(1);
        let mp = normalize(&expr).expect("polynomial");
        let coeffs = multipoly_to_univariate(&mp, "x").expect("univariate");
        assert_eq!(coeffs, ints(&[-1, 0, 1]));
    }
}
