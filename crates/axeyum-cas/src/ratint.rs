//! Rational-function integration internals — the Horowitz–Ostrogradsky method.
//!
//! Given a proper `A/D` with `gcd(A, D) = 1`, Horowitz's algorithm splits the
//! integral into a **rational part** `B/D₂` (computable by exact linear algebra,
//! no factorization or root-finding) and a **logarithmic part** `∫ C/D₁ dx`:
//!
//! ```text
//! ∫ A/D dx = B/D₂ + ∫ C/D₁ dx ,   D₂ = gcd(D, D'),  D₁ = D/D₂,
//!   deg B < deg D₂,  deg C < deg D₁.
//! ```
//!
//! The identity `A = B'·D₁ − B·H + C·D₂` with `H = D'/D₂ − D₁'` is linear in the
//! unknown coefficients of `B` and `C`, so we solve one exact-rational linear
//! system. When `C = 0` the integral is purely rational (fully certified by the
//! differentiate-and-check zero-test); otherwise a genuine logarithmic part
//! remains (a later slice). Everything here operates on `poly.rs`'s public exact
//! primitives, so the shared IR crate is untouched.
//!
//! Reference: Bronstein, *Symbolic Integration I*, Ch. 2 (the classical
//! Horowitz–Ostrogradsky method).

use axeyum_ir::{Rational, poly};

/// A dense univariate polynomial, LSB-first (matching `axeyum_ir::poly`).
pub(crate) type RatVec = Vec<Rational>;

/// Whether every coefficient is zero (the zero polynomial).
pub(crate) fn is_zero(v: &[Rational]) -> bool {
    v.iter().all(|c| c.is_zero())
}

/// Polynomial division with quotient **and** remainder: `a = q·b + r`,
/// `deg r < deg b`. Built from `rat_rem` + exact division. `None` on overflow.
pub(crate) fn divrem(a: &[Rational], b: &[Rational]) -> Option<(RatVec, RatVec)> {
    let rem = poly::rat_rem(a, b)?;
    let a_minus_rem = poly::ratpoly_add(a, &poly::ratpoly_neg(&rem)?)?;
    let quot = poly::rat_exact_div(&a_minus_rem, b)?;
    Some((poly::rat_trim(quot), poly::rat_trim(rem)))
}

/// Solve the exact-rational linear system `Σⱼ xⱼ · colⱼ = rhs` for a **square**
/// system (`cols.len() == rhs.len()`), by Gauss–Jordan elimination over ℚ.
/// Returns `None` if the system is singular or on overflow. Column `j` supplies
/// the coefficients of unknown `xⱼ`; missing entries are read as zero.
pub(crate) fn solve_linear(cols: &[RatVec], rhs: &[Rational]) -> Option<Vec<Rational>> {
    let n = cols.len();
    let m = rhs.len();
    if n != m {
        return None;
    }
    // Augmented matrix: m rows × (n unknowns + 1 rhs).
    let mut mat: Vec<Vec<Rational>> = (0..m)
        .map(|i| {
            let mut row: Vec<Rational> = (0..n)
                .map(|j| cols[j].get(i).copied().unwrap_or_else(Rational::zero))
                .collect();
            row.push(rhs[i]);
            row
        })
        .collect();

    for col in 0..n {
        // Select a nonzero pivot at or below the diagonal.
        let sel = (col..m).find(|&r| !mat[r][col].is_zero())?;
        mat.swap(col, sel);
        // Normalize the pivot row so mat[col][col] == 1.
        let pivot_inv = Rational::integer(1).checked_div(mat[col][col])?;
        for entry in &mut mat[col][col..=n] {
            *entry = entry.checked_mul(pivot_inv)?;
        }
        // Eliminate this column from every other row.
        let pivot = mat[col][col..=n].to_vec();
        for (r, row) in mat.iter_mut().enumerate() {
            if r != col && !row[col].is_zero() {
                let factor = row[col];
                for (offset, pivot_val) in pivot.iter().enumerate() {
                    let sub = pivot_val.checked_mul(factor)?;
                    let cell = &mut row[col + offset];
                    *cell = cell.checked_sub(sub)?;
                }
            }
        }
    }
    Some((0..n).map(|j| mat[j][n]).collect())
}

/// `x^k` as a dense polynomial.
fn monomial(k: usize) -> RatVec {
    let mut v = vec![Rational::zero(); k + 1];
    v[k] = Rational::integer(1);
    v
}

/// Horowitz–Ostrogradsky reduction of a **proper** fraction `a/d` with
/// `gcd(a, d) = 1`. Returns `(B, D₂, C, D₁)` with `∫ a/d = B/D₂ + ∫ C/D₁`,
/// `deg B < deg D₂`, `deg C < deg D₁`. `None` on overflow or a singular system.
pub(crate) fn horowitz(
    numer: &[Rational],
    denom: &[Rational],
) -> Option<(RatVec, RatVec, RatVec, RatVec)> {
    let denom_deriv = poly::rat_derivative(denom)?;
    let bound = denom.len() + 2;
    let repeated = poly::rat_gcd(denom, &denom_deriv, bound)?; // gcd(D, D'), monic
    let squarefree = poly::rat_exact_div(denom, &repeated)?; // D / D2 (exact)

    // H = D'/D2 − D1'
    let deriv_over_repeated = poly::rat_exact_div(&denom_deriv, &repeated)?;
    let squarefree_deriv = poly::rat_derivative(&squarefree)?;
    let h_poly = poly::ratpoly_add(&deriv_over_repeated, &poly::ratpoly_neg(&squarefree_deriv)?)?;

    let deg_rep = poly::rat_degree(&repeated).unwrap_or(0); // number of B coefficients
    let deg_sqf = poly::rat_degree(&squarefree).unwrap_or(0); // number of C coefficients
    let eqn = deg_rep + deg_sqf; // = deg D
    if eqn == 0 {
        return None;
    }

    let mut cols: Vec<RatVec> = Vec::with_capacity(eqn);
    // B unknowns b_k (k = 0..deg_rep): column = (d/dx x^k)·D1 − x^k·H.
    for idx in 0..deg_rep {
        let term1 = if idx == 0 {
            Vec::new() // derivative of a constant is 0
        } else {
            // d/dx x^k = k·x^{k-1}
            let mut deriv_mono = vec![Rational::zero(); idx];
            deriv_mono[idx - 1] = Rational::integer(i128::try_from(idx).ok()?);
            poly::ratpoly_mul(&deriv_mono, &squarefree)?
        };
        let term2 = poly::ratpoly_mul(&monomial(idx), &h_poly)?;
        cols.push(poly::ratpoly_add(&term1, &poly::ratpoly_neg(&term2)?)?);
    }
    // C unknowns c_k (k = 0..deg_sqf): column = x^k·D2.
    for idx in 0..deg_sqf {
        cols.push(poly::ratpoly_mul(&monomial(idx), &repeated)?);
    }

    // rhs = A, padded to `eqn` coefficients.
    let mut rhs = numer.to_vec();
    rhs.resize(eqn, Rational::zero());

    let sol = solve_linear(&cols, &rhs)?;
    let b_num = poly::rat_trim(sol[0..deg_rep].to_vec());
    let c_num = poly::rat_trim(sol[deg_rep..deg_rep + deg_sqf].to_vec());
    Some((b_num, repeated, c_num, squarefree))
}

/// Rothstein–Trager resultant `R(t) = Res_x(P̄ − t·Q̄', Q̄)`, as a polynomial in
/// `t` (LSB-first). Reuses the in-tree bivariate Sylvester machinery with `t` as
/// the surviving variable. `None` on overflow or a degenerate (deg < 2)
/// denominator.
pub(crate) fn rothstein_trager_resultant(p_bar: &[Rational], q_bar: &[Rational]) -> Option<RatVec> {
    let q_deriv = poly::rat_derivative(q_bar)?;
    let flen = p_bar.len().max(q_deriv.len());
    // f(x) = P̄ − t·Q̄': the x^i coefficient is the length-2 poly [P̄_i, −Q̄'_i] in t.
    let mut p_coeffs: Vec<RatVec> = Vec::with_capacity(flen);
    for i in 0..flen {
        let constant = p_bar.get(i).copied().unwrap_or_else(Rational::zero);
        let linear = q_deriv
            .get(i)
            .copied()
            .unwrap_or_else(Rational::zero)
            .checked_neg()?;
        p_coeffs.push(vec![constant, linear]);
    }
    while p_coeffs.last().is_some_and(|c| is_zero(c)) {
        p_coeffs.pop();
    }
    let q_coeffs: Vec<RatVec> = q_bar.iter().map(|&c| vec![c]).collect();
    let mat = poly::sylvester_matrix(&p_coeffs, &q_coeffs)?;
    poly::sylvester_determinant(&mat)
}

/// All positive divisors of `n` (`n > 0`), or `None` if `n` is too large to
/// factor cheaply (the caller then declines — safe, never wrong).
fn divisors(n: u128) -> Option<Vec<u128>> {
    if n == 0 || n > 1_000_000_000 {
        return None;
    }
    let mut out = Vec::new();
    let mut d = 1u128;
    while d * d <= n {
        if n.is_multiple_of(d) {
            out.push(d);
            if d != n / d {
                out.push(n / d);
            }
        }
        d += 1;
    }
    Some(out)
}

/// All distinct rational roots of `poly_t` (LSB-first) via the rational-root
/// theorem. A constant returns an empty list; `None` on overflow / coefficients
/// too large to factor.
pub(crate) fn rational_roots(poly_t: &[Rational]) -> Option<Vec<Rational>> {
    let mut work = poly::rat_trim(poly_t.to_vec());
    let mut roots: Vec<Rational> = Vec::new();
    // Strip factors of t (the root 0), recorded once.
    let mut had_zero_root = false;
    while work.len() > 1 && work[0].is_zero() {
        had_zero_root = true;
        work.remove(0);
    }
    if had_zero_root {
        roots.push(Rational::zero());
    }
    if work.len() <= 1 {
        return Some(roots); // constant remainder: no further roots
    }
    // Candidates ± p/q with p | a₀, q | aₙ.
    let int_coeffs = poly::rat_to_int_poly(&work, 1_000_000_000)?;
    let a0 = *int_coeffs.first()?;
    let an = *int_coeffs.last()?;
    if a0 == 0 || an == 0 {
        return Some(roots);
    }
    let numer_divs = divisors(a0.unsigned_abs())?;
    let denom_divs = divisors(an.unsigned_abs())?;
    for &p in &numer_divs {
        for &q in &denom_divs {
            for sign in [1i128, -1] {
                let candidate = Rational::checked_new(
                    sign.checked_mul(i128::try_from(p).ok()?)?,
                    i128::try_from(q).ok()?,
                )?;
                if poly::eval_rat_poly(&work, candidate)?.is_zero() && !roots.contains(&candidate) {
                    roots.push(candidate);
                }
            }
        }
    }
    Some(roots)
}

/// The Rothstein–Trager logarithmic part `∫ P̄/Q̄ = Σ cᵢ·ln(vᵢ)` for squarefree
/// `Q̄` with `gcd(P̄, Q̄) = 1`, when the resultant splits over ℚ. Returns the
/// `(cᵢ, vᵢ)` term list (`vᵢ` monic), or `None` if a non-rational root is
/// required (the caller then declines — the certificate never sees a wrong sum).
pub(crate) fn log_terms(p_bar: &[Rational], q_bar: &[Rational]) -> Option<Vec<(Rational, RatVec)>> {
    let resultant = rothstein_trager_resultant(p_bar, q_bar)?;
    let roots = rational_roots(&resultant)?;
    if roots.is_empty() {
        return None;
    }
    let q_deriv = poly::rat_derivative(q_bar)?;
    let bound = q_bar.len() + 2;
    let mut terms = Vec::new();
    for coeff in roots {
        // vᵢ = gcd(P̄ − cᵢ·Q̄', Q̄), monic. When the shift is identically zero
        // (P̄ = cᵢ·Q̄'), gcd(0, Q̄) = Q̄ — the whole denominator is the argument.
        let scaled = poly::ratpoly_mul(&[coeff], &q_deriv)?;
        let shifted = poly::ratpoly_add(p_bar, &poly::ratpoly_neg(&scaled)?)?;
        let v = if is_zero(&shifted) {
            poly::rat_make_monic(q_bar)?
        } else {
            poly::rat_make_monic(&poly::rat_gcd(&shifted, q_bar, bound)?)?
        };
        if poly::rat_degree(&v).unwrap_or(0) >= 1 {
            terms.push((coeff, v));
        }
    }
    if terms.is_empty() {
        return None;
    }
    Some(terms)
}
