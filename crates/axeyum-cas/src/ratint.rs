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
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{ToPrimitive, Zero};

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
    solve_linear_i128(cols, rhs).or_else(|| solve_linear_big(cols, rhs))
}

/// Fast path for [`solve_linear`] over the crate's ordinary `i128` rationals.
fn solve_linear_i128(cols: &[RatVec], rhs: &[Rational]) -> Option<Vec<Rational>> {
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

/// Exact bignum fallback for a small square system. Only final coefficients that
/// fit the public `i128` [`Rational`] representation are returned; otherwise the
/// caller still declines. This keeps coefficient growth out of the soundness
/// path without changing the CAS value model.
fn solve_linear_big(cols: &[RatVec], rhs: &[Rational]) -> Option<Vec<Rational>> {
    const MAX_BIG_LINEAR_DIMENSION: usize = 16;
    let n = cols.len();
    if n != rhs.len() || n > MAX_BIG_LINEAR_DIMENSION {
        return None;
    }
    let lift = |value: Rational| {
        BigRational::new(
            BigInt::from(value.numerator()),
            BigInt::from(value.denominator()),
        )
    };
    let mut matrix: Vec<Vec<BigRational>> = (0..n)
        .map(|row| {
            let mut values: Vec<BigRational> = (0..n)
                .map(|column| {
                    lift(
                        cols[column]
                            .get(row)
                            .copied()
                            .unwrap_or_else(Rational::zero),
                    )
                })
                .collect();
            values.push(lift(rhs[row]));
            values
        })
        .collect();

    for column in 0..n {
        let pivot_row = (column..n).find(|&row| !matrix[row][column].is_zero())?;
        matrix.swap(column, pivot_row);
        let pivot = matrix[column][column].clone();
        for entry in &mut matrix[column][column..=n] {
            *entry /= pivot.clone();
        }
        let pivot_values = matrix[column][column..=n].to_vec();
        for (row_index, row) in matrix.iter_mut().enumerate() {
            if row_index == column || row[column].is_zero() {
                continue;
            }
            let factor = row[column].clone();
            for (offset, pivot_value) in pivot_values.iter().enumerate() {
                row[column + offset] -= factor.clone() * pivot_value;
            }
        }
    }

    (0..n)
        .map(|index| {
            let value = &matrix[index][n];
            Rational::checked_new(value.numer().to_i128()?, value.denom().to_i128()?)
        })
        .collect()
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

/// Independently re-derives and checks a Horowitz–Ostrogradsky split
/// `(B, D2, C, D1)` of `numer/denom`, **without trusting how it was
/// produced** (the caller may pass [`horowitz`]'s own output, or a
/// hand-built candidate).
///
/// This is the module's "differentiate the candidate and compare exactly"
/// checker for the **rational** part of the integral, and it stays entirely
/// in `poly.rs`'s exact-`Rational` polynomial arithmetic — it never goes
/// through the CAS's general `equal`/`CasExpr` derivative route, so it is
/// small and independent in the sense the architecture wants.
///
/// Checks, in order:
/// 1. `D` (`denom`) is a genuine non-constant polynomial — a rational
///    function's denominator can't be a nonzero constant or zero (the
///    producer's own [`horowitz`] declines a constant `D` via `eqn == 0`).
/// 2. Properness: `deg B < deg D2` and `deg C < deg D1`. Without this bound
///    the identity below is satisfiable by infinitely many wrong `(B, C)`
///    pairs — see `wrong_degree_b_is_vacuous_without_the_properness_guard`
///    in the tests, this module's analogue of `taylor.rs`'s flagship fixture:
///    replacing `B` by `B + D2` leaves the identity holding exactly (the
///    added constant differentiates to zero) while producing a wrong
///    antiderivative (`+1`, not `+C`, more precisely a spurious integer-degree
///    shift wherever `D2` is non-constant).
/// 3. `D2 * D1 == D` exactly (the claimed split reconstructs the denominator).
/// 4. `D2` divides `D'` exactly (a precondition for `H = D'/D2 − D1'` to be a
///    polynomial at all).
/// 5. The core identity `numer == B'·D1 − B·H + C·D2`. Worked out in the
///    module doc, this is algebraically **equivalent** — given 3 and 4 — to
///    `d/dx(B/D2) + C/D1 == numer/denom` as rational functions, so checking
///    it here *is* differentiating the candidate antiderivative and
///    comparing to the integrand, exactly, in poly-space.
///
/// There is deliberately no separate "`D2`, `D1` nonzero" guard: given guard
/// 1, both are always caught downstream — `D2 == 0` makes guard 4's exact
/// division fail unconditionally (it requires a nonzero divisor, independent
/// of `denom`), and `D1 == 0` makes guard 3 fail because `D2 * 0` trims to
/// the zero polynomial while `D` has degree ≥ 1 by guard 1. Mutation-tested.
///
/// Returns `Some(false)` on any violation, `Some(true)` only when every
/// guard passes, and `None` only on internal arithmetic overflow (treated by
/// callers as a decline, never as acceptance).
///
/// Not yet wired into `lib.rs`'s `integrate_rational` (out of this module's
/// scope — see `docs/plan/status/163-ratint.md`); exercised directly by this
/// module's own test suite, hence the explicit `dead_code` allow.
#[allow(dead_code)]
pub(crate) fn verify_horowitz(
    numer: &[Rational],
    denom: &[Rational],
    b: &[Rational],
    d2: &[Rational],
    c: &[Rational],
    d1: &[Rational],
) -> Option<bool> {
    let numer = poly::rat_trim(numer.to_vec());
    let denom = poly::rat_trim(denom.to_vec());
    let b = poly::rat_trim(b.to_vec());
    let d2 = poly::rat_trim(d2.to_vec());
    let c = poly::rat_trim(c.to_vec());
    let d1 = poly::rat_trim(d1.to_vec());

    // Guard 1: D must be a genuine non-constant denominator.
    match poly::rat_degree(&denom) {
        Some(deg) if deg >= 1 => {}
        _ => return Some(false),
    }
    let deg_d2 = poly::rat_degree(&d2).unwrap_or(0);
    let deg_d1 = poly::rat_degree(&d1).unwrap_or(0);

    // Guard 2: properness.
    if let Some(deg_b) = poly::rat_degree(&b)
        && deg_b >= deg_d2
    {
        return Some(false);
    }
    if let Some(deg_c) = poly::rat_degree(&c)
        && deg_c >= deg_d1
    {
        return Some(false);
    }

    // Guard 3: the claimed split reconstructs D exactly.
    let product = poly::rat_trim(poly::ratpoly_mul(&d2, &d1)?);
    if product != denom {
        return Some(false);
    }

    // Guard 4: D2 | D' exactly, giving H = D'/D2 − D1'.
    let denom_deriv = poly::rat_derivative(&denom)?;
    let Some(deriv_over_d2) = poly::rat_exact_div(&denom_deriv, &d2) else {
        return Some(false);
    };
    let d1_deriv = poly::rat_derivative(&d1)?;
    let h = poly::ratpoly_add(&deriv_over_d2, &poly::ratpoly_neg(&d1_deriv)?)?;

    // Guard 5: numer == B'D1 - BH + CD2.
    let b_deriv = poly::rat_derivative(&b)?;
    let term1 = poly::ratpoly_mul(&b_deriv, &d1)?;
    let term2 = poly::ratpoly_mul(&b, &h)?;
    let term3 = poly::ratpoly_mul(&c, &d2)?;
    let rhs = poly::ratpoly_add(
        &poly::ratpoly_add(&term1, &poly::ratpoly_neg(&term2)?)?,
        &term3,
    )?;
    if poly::rat_trim(rhs) != numer {
        return Some(false);
    }

    Some(true)
}

/// Independently re-derives and checks a Rothstein–Trager logarithmic
/// decomposition `Σ cᵢ·ln(vᵢ)` of `∫ p_bar/q_bar dx`, **without trusting how
/// it was produced** — purely in `poly.rs` exact-`Rational` arithmetic, never
/// through the CAS's general `equal`/`ln`-derivative route.
///
/// `d/dx Σ cᵢ ln(vᵢ) = Σ cᵢ·vᵢ'/vᵢ`. Clearing denominators against `q_bar`
/// turns "this equals `p_bar/q_bar`" into the polynomial identity
/// `Σ cᵢ·vᵢ'·(q_bar/vᵢ) == p_bar`, checked by exact division (rejecting if any
/// `vᵢ` does not divide `q_bar`) and exact polynomial equality.
///
/// Additionally requires **completeness** — `∏ vᵢ == monic(q_bar)`. The
/// producer (`log_terms`) can decline early on an incomplete resultant
/// factorization, but nothing stops a malformed certificate from omitting a
/// root's contribution while still solving the identity for the roots it
/// *did* keep (in general it will not, but the completeness guard makes that
/// independent of the identity guard rather than an accident of one example
/// — see the tests). There is deliberately no separate "no duplicate `vᵢ`"
/// guard: mutation-tested and found always subsumed by completeness — a
/// repeated `vᵢ` (degree ≥ 1 by guard 1) strictly inflates `∏ vᵢ`'s degree
/// past `deg(monic(q_bar))`, so the two polynomials can never compare equal.
///
/// Returns `Some(false)` on any violation, `Some(true)` only when every
/// guard passes, `None` only on internal overflow (never accepted).
///
/// Not yet wired into `lib.rs`'s `integrate_log_part` (out of this module's
/// scope — see `docs/plan/status/163-ratint.md`); exercised directly by this
/// module's own test suite, hence the explicit `dead_code` allow.
#[allow(dead_code)]
pub(crate) fn verify_log_terms(
    p_bar: &[Rational],
    q_bar: &[Rational],
    terms: &[(Rational, RatVec)],
) -> Option<bool> {
    let p_bar = poly::rat_trim(p_bar.to_vec());
    let q_bar = poly::rat_trim(q_bar.to_vec());
    if poly::rat_degree(&q_bar).is_none() {
        return Some(false); // zero denominator
    }
    if terms.is_empty() {
        return Some(false);
    }

    // Guard 1: every vᵢ is a genuine (degree >= 1), monic factor.
    for (_, v) in terms {
        let Some(deg_v) = poly::rat_degree(v) else {
            return Some(false);
        };
        if deg_v == 0 {
            return Some(false);
        }
        if v[deg_v] != Rational::integer(1) {
            return Some(false);
        }
    }

    // Guard 2: completeness -- prod(vᵢ) == monic(q_bar). (There is no
    // separate "no duplicate vᵢ" guard -- see the module doc: a repeat is
    // always caught here, on degree alone.)
    let mut product = vec![Rational::integer(1)];
    for (_, v) in terms {
        product = poly::ratpoly_mul(&product, v)?;
    }
    let q_monic = poly::rat_make_monic(&q_bar)?;
    if poly::rat_trim(product) != poly::rat_trim(q_monic) {
        return Some(false);
    }

    // Guard 3: Σ cᵢ vᵢ' (q_bar/vᵢ) == p_bar.
    let mut acc: Vec<Rational> = Vec::new();
    for (coeff, v) in terms {
        let v_deriv = poly::rat_derivative(v)?;
        let Some(q_over_v) = poly::rat_exact_div(&q_bar, v) else {
            return Some(false);
        };
        let term = poly::ratpoly_mul(&v_deriv, &q_over_v)?;
        let scaled = poly::ratpoly_mul(&[*coeff], &term)?;
        acc = poly::ratpoly_add(&acc, &scaled)?;
    }
    if poly::rat_trim(acc) != p_bar {
        return Some(false);
    }

    Some(true)
}

#[cfg(test)]
#[allow(clippy::many_single_char_names)] // A, D, B, C, D1, D2, H mirror the module doc's math notation
mod tests {
    use super::*;

    fn poly_from(coeffs: &[i128]) -> Vec<Rational> {
        coeffs.iter().map(|&c| Rational::integer(c)).collect()
    }

    /// Evaluate `d/dx(B/D2) + C/D1` and `A/D` at a rational point `x` (not a
    /// root of `D`, `D1`, or `D2`) and compare, as an evaluation-based
    /// cross-check on `horowitz`'s output that is independent of both the
    /// producer's own algebra AND `verify_horowitz`'s polynomial-identity
    /// route -- used only inside tests, to confirm a fixture is a genuine
    /// identity before trusting a guard to reject a mutated one.
    fn horowitz_identity_holds_at(
        a: &[Rational],
        d: &[Rational],
        b: &[Rational],
        d2: &[Rational],
        c: &[Rational],
        d1: &[Rational],
        x: Rational,
    ) -> bool {
        let ev = |p: &[Rational]| poly::eval_rat_poly(p, x).unwrap();
        let b_deriv = poly::rat_derivative(b).unwrap();
        let d2_deriv = poly::rat_derivative(d2).unwrap();
        let numerator = ev(&b_deriv)
            .checked_mul(ev(d2))
            .unwrap()
            .checked_sub(ev(b).checked_mul(ev(&d2_deriv)).unwrap())
            .unwrap();
        let lhs_rational = numerator
            .checked_div(ev(d2).checked_mul(ev(d2)).unwrap())
            .unwrap();
        let lhs = lhs_rational
            .checked_add(ev(c).checked_div(ev(d1)).unwrap())
            .unwrap();
        let rhs = ev(a).checked_div(ev(d)).unwrap();
        lhs == rhs
    }

    // ---------------------------------------------------------------
    // divrem / solve_linear / rational_roots -- basic producer sanity
    // ---------------------------------------------------------------

    #[test]
    fn divrem_splits_improper_fraction() {
        // (x^2 + 1) / x = x + (1/x remainder 1)
        let a = poly_from(&[1, 0, 1]); // 1 + x^2
        let b = poly_from(&[0, 1]); // x
        let (q, r) = divrem(&a, &b).unwrap();
        assert_eq!(q, poly_from(&[0, 1])); // x
        assert_eq!(r, poly_from(&[1])); // 1
    }

    #[test]
    fn solve_linear_solves_a_simple_system() {
        // [1 1; 0 1] x = [3; 2]  =>  x = [1, 2]
        let cols = vec![poly_from(&[1, 0]), poly_from(&[1, 1])];
        let rhs = poly_from(&[3, 2]);
        let sol = solve_linear(&cols, &rhs).unwrap();
        assert_eq!(sol, vec![Rational::integer(1), Rational::integer(2)]);
    }

    #[test]
    fn solve_linear_declines_on_singular_system() {
        let cols = vec![poly_from(&[1, 2]), poly_from(&[2, 4])];
        let rhs = poly_from(&[1, 1]);
        assert_eq!(solve_linear(&cols, &rhs), None);
    }

    #[test]
    fn rational_roots_finds_all_roots_of_a_cubic() {
        // (x-1)(x-2)(x+3) = x^3 - 7x - ... let's just build it directly.
        let f1 = poly_from(&[-1, 1]); // x - 1
        let f2 = poly_from(&[-2, 1]); // x - 2
        let f3 = poly_from(&[3, 1]); // x + 3
        let q = poly::ratpoly_mul(&poly::ratpoly_mul(&f1, &f2).unwrap(), &f3).unwrap();
        let mut roots = rational_roots(&q).unwrap();
        roots.sort_by_key(|r| r.numerator());
        assert_eq!(
            roots,
            vec![
                Rational::integer(-3),
                Rational::integer(1),
                Rational::integer(2)
            ]
        );
    }

    // ---------------------------------------------------------------
    // horowitz + verify_horowitz -- rung 1 (the rational part)
    // ---------------------------------------------------------------

    #[test]
    fn horowitz_splits_x_over_x_minus_one_squared() {
        // A/D = x / (x-1)^2. gcd(D,D') = (x-1) (up to scale), so D2 = x-1,
        // D1 = x-1, and there's a genuine logarithmic remainder.
        let factor = poly_from(&[-1, 1]); // x - 1
        let d = poly::ratpoly_mul(&factor, &factor).unwrap(); // (x-1)^2
        let a = poly_from(&[0, 1]); // x

        let (b, d2, c, d1) = horowitz(&a, &d).expect("must not decline");
        assert_eq!(verify_horowitz(&a, &d, &b, &d2, &c, &d1), Some(true));
        assert!(!is_zero(&c), "this fixture must have a genuine log part");

        // Independent evaluation cross-check.
        let x = Rational::integer(5);
        assert!(horowitz_identity_holds_at(&a, &d, &b, &d2, &c, &d1, x));
    }

    #[test]
    fn horowitz_declines_when_eqn_is_zero() {
        // Constant denominator: no equations to solve.
        let a = poly_from(&[1]);
        let d = poly_from(&[2]);
        assert_eq!(horowitz(&a, &d), None);
    }

    #[test]
    fn horowitz_purely_rational_case_has_no_log_part() {
        // A/D = 1 / x^2: D2 = gcd(x^2, 2x) = x, D1 = D/D2 = x, and the
        // antiderivative -1/x has no logarithmic remainder, so C must solve
        // to the zero poly even though D1 is non-constant.
        let d = poly_from(&[0, 0, 1]); // x^2
        let a = poly_from(&[1]); // 1
        let (b, d2, c, d1) = horowitz(&a, &d).expect("must not decline");
        assert_eq!(verify_horowitz(&a, &d, &b, &d2, &c, &d1), Some(true));
        assert!(is_zero(&c), "1/x^2 has no logarithmic part");
        assert_eq!(d2, poly_from(&[0, 1])); // x
        assert_eq!(d1, poly_from(&[0, 1])); // x
        assert_eq!(b, poly_from(&[-1])); // B/D2 = -1/x
    }

    #[test]
    fn perturbed_b_coefficient_is_rejected() {
        let factor = poly_from(&[-1, 1]);
        let d = poly::ratpoly_mul(&factor, &factor).unwrap();
        let a = poly_from(&[0, 1]);
        let (mut b, d2, c, d1) = horowitz(&a, &d).unwrap();
        assert_eq!(verify_horowitz(&a, &d, &b, &d2, &c, &d1), Some(true));
        // Bump B's constant term by 1.
        if b.is_empty() {
            b.push(Rational::integer(1));
        } else {
            b[0] = b[0].checked_add(Rational::integer(1)).unwrap();
        }
        assert_eq!(
            verify_horowitz(&a, &d, &b, &d2, &c, &d1),
            Some(false),
            "a perturbed rational-part coefficient must be rejected"
        );
    }

    #[test]
    fn perturbed_c_coefficient_is_rejected() {
        let factor = poly_from(&[-1, 1]);
        let d = poly::ratpoly_mul(&factor, &factor).unwrap();
        let a = poly_from(&[0, 1]);
        let (b, d2, mut c, d1) = horowitz(&a, &d).unwrap();
        assert!(!is_zero(&c));
        if c.is_empty() {
            c.push(Rational::integer(1));
        } else {
            c[0] = c[0].checked_add(Rational::integer(1)).unwrap();
        }
        assert_eq!(
            verify_horowitz(&a, &d, &b, &d2, &c, &d1),
            Some(false),
            "a perturbed logarithmic-part coefficient must be rejected"
        );
    }

    /// The flagship fixture for the properness guard on `B`: because `B`
    /// only enters the identity through its *derivative*, `B + D2` satisfies
    /// the EXACT SAME identity as `B` (the added `D2` differentiates against
    /// `D1` to `D2'D1`, which cancels exactly against the `B*H` term's
    /// increase -- `D2*H = D2'*D1`, worked out in the module doc). So
    /// perturbing `B` by a whole copy of `D2` is invisible to guard 5 and
    /// caught ONLY by the properness bound (guard 2) -- this module's
    /// analogue of `taylor.rs`'s flagship fixture, where a wrong witness
    /// satisfies the identical *value* equation while failing a structural
    /// (interval / degree) bound.
    #[test]
    fn wrong_degree_b_is_vacuous_without_the_properness_guard() {
        let factor = poly_from(&[-1, 1]); // x - 1
        let d = poly::ratpoly_mul(&factor, &factor).unwrap(); // (x-1)^2
        let a = poly_from(&[0, 1]); // x
        let (b, d2, c, d1) = horowitz(&a, &d).unwrap();
        assert_eq!(verify_horowitz(&a, &d, &b, &d2, &c, &d1), Some(true));
        assert_eq!(poly::rat_degree(&d2), Some(1), "fixture needs deg D2 = 1");

        let bumped_b = poly::ratpoly_add(&b, &d2).unwrap(); // B + D2, now deg B == deg D2
        assert_eq!(
            poly::rat_degree(&bumped_b),
            Some(1),
            "the mutant must actually violate deg B < deg D2"
        );

        // Confirm the core identity (guard 5) is untouched by construction.
        let numer_deriv_term1 = {
            let b_deriv = poly::rat_derivative(&bumped_b).unwrap();
            poly::ratpoly_mul(&b_deriv, &d1).unwrap()
        };
        let denom_deriv = poly::rat_derivative(&d).unwrap();
        let h = poly::ratpoly_add(
            &poly::rat_exact_div(&denom_deriv, &d2).unwrap(),
            &poly::ratpoly_neg(&poly::rat_derivative(&d1).unwrap()).unwrap(),
        )
        .unwrap();
        let term2 = poly::ratpoly_mul(&bumped_b, &h).unwrap();
        let term3 = poly::ratpoly_mul(&c, &d2).unwrap();
        let reconstructed = poly::rat_trim(
            poly::ratpoly_add(
                &poly::ratpoly_add(&numer_deriv_term1, &poly::ratpoly_neg(&term2).unwrap())
                    .unwrap(),
                &term3,
            )
            .unwrap(),
        );
        assert_eq!(
            reconstructed,
            poly::rat_trim(a.clone()),
            "fixture must leave the core identity holding exactly"
        );

        assert_eq!(
            verify_horowitz(&a, &d, &bumped_b, &d2, &c, &d1),
            Some(false),
            "B with deg B >= deg D2 must be rejected even though the core \
             identity holds exactly"
        );
    }

    #[test]
    fn mismatched_denominator_split_is_rejected() {
        // D2 * D1 != D.
        let factor = poly_from(&[-1, 1]);
        let d = poly::ratpoly_mul(&factor, &factor).unwrap();
        let a = poly_from(&[0, 1]);
        let (b, d2, c, mut d1) = horowitz(&a, &d).unwrap();
        // Corrupt D1 by adding an unrelated constant.
        d1[0] = d1[0].checked_add(Rational::integer(1)).unwrap();
        assert_eq!(verify_horowitz(&a, &d, &b, &d2, &c, &d1), Some(false));
    }

    /// Isolates guard 4 (`D2 | D'` exactly): a `D2, D1` split that
    /// reconstructs `D` (guard 3 passes) but is NOT the true `gcd(D, D')`
    /// split, paired with a `(B, C)` chosen to satisfy the identity **that
    /// guard 5 would compute if D2's failure to divide D' were silently
    /// tolerated** (i.e. `H` taken as `-D1'` rather than `D'/D2 - D1'`).
    /// `D = (x-1)(x-2)`, `D2 = x-1`, `D1 = x-2`: `D2` does not divide
    /// `D' = 2x-3` (`D'` at `x=1` is `-1 != 0`), so the real Horowitz `H` is
    /// undefined as a polynomial, but `B=1, C=1` solves
    /// `A = B'D1 + B*D1' + C*D2` exactly for `A = x`. This is a genuinely
    /// WRONG certificate -- `(B/D2)' + C/D1` at `x=3` is `-1/4 + 1 = 3/4`,
    /// not `A/D = 3/2` -- caught only by the exact-division guard, never by
    /// the identity guard alone (which a divisibility-blind implementation
    /// would compute the same wrong way).
    #[test]
    fn non_dividing_d2_slips_past_without_the_divisibility_guard() {
        let d = poly_from(&[2, -3, 1]); // (x-1)(x-2)
        let d2 = poly_from(&[-1, 1]); // x - 1
        let d1 = poly_from(&[-2, 1]); // x - 2 (D2*D1 == D, but D2 != gcd(D,D'))
        let b = poly_from(&[1]);
        let c = poly_from(&[1]);
        let a = poly_from(&[0, 1]); // x

        // Confirm the fixture is NOT a genuine rational-function identity.
        let x = Rational::integer(3);
        assert!(
            !horowitz_identity_holds_at(&a, &d, &b, &d2, &c, &d1, x),
            "fixture must be a genuinely wrong certificate"
        );

        assert_eq!(
            verify_horowitz(&a, &d, &b, &d2, &c, &d1),
            Some(false),
            "a D2 that does not divide D' exactly must be rejected even \
             though it solves the (wrongly H-computed) identity"
        );
    }

    #[test]
    fn zero_d2_is_rejected() {
        let a = poly_from(&[1]);
        let d = poly_from(&[-1, 1]);
        assert_eq!(
            verify_horowitz(&a, &d, &[], &[], &poly_from(&[1]), &d),
            Some(false)
        );
    }

    /// Isolates guard 1 (`D` non-constant): the fully degenerate all-zero
    /// certificate `numer=denom=B=C=D1=0, D2` any nonzero constant. Every
    /// OTHER guard is vacuous against it -- properness is skipped for a
    /// zero `B`/`C` (no degree to compare), guard 3's `D2*D1==D` holds
    /// trivially (`D2*0 == 0`), guard 4's exact division of `0` by `D2`
    /// succeeds trivially, and guard 5's identity is `0 == 0`. Only
    /// rejecting a zero/constant `denom` up front catches it.
    #[test]
    fn degenerate_zero_denominator_certificate_is_rejected() {
        let empty: Vec<Rational> = Vec::new();
        let d2 = poly_from(&[1]); // any nonzero constant
        assert_eq!(
            verify_horowitz(&empty, &empty, &empty, &d2, &empty, &empty),
            Some(false),
            "a zero denom must be rejected even though every other guard is vacuous"
        );
    }

    // ---------------------------------------------------------------
    // log_terms + verify_log_terms -- rung 2 (the logarithmic part)
    // ---------------------------------------------------------------

    #[test]
    fn log_terms_for_two_distinct_linear_roots() {
        // p_bar/q_bar = 1 / ((x-1)(x-2)).
        let q = poly_from(&[2, -3, 1]); // (x-1)(x-2)
        let p = poly_from(&[1]);
        let terms = log_terms(&p, &q).expect("must not decline");
        assert_eq!(verify_log_terms(&p, &q, &terms), Some(true));
        assert_eq!(terms.len(), 2);

        // Evaluation cross-check: d/dx sum(c ln v) at x, vs p/q at x.
        let x = Rational::integer(10);
        let mut lhs = Rational::zero();
        for (c, v) in &terms {
            let v_deriv = poly::rat_derivative(v).unwrap();
            let contrib = c
                .checked_mul(poly::eval_rat_poly(&v_deriv, x).unwrap())
                .unwrap()
                .checked_div(poly::eval_rat_poly(v, x).unwrap())
                .unwrap();
            lhs = lhs.checked_add(contrib).unwrap();
        }
        let rhs = poly::eval_rat_poly(&p, x)
            .unwrap()
            .checked_div(poly::eval_rat_poly(&q, x).unwrap())
            .unwrap();
        assert_eq!(lhs, rhs);
    }

    #[test]
    fn log_terms_declines_on_zero_numerator() {
        // p_bar = 0: no logarithmic part.
        let q = poly_from(&[-1, 1]);
        let p: Vec<Rational> = Vec::new();
        assert_eq!(log_terms(&p, &q), None);
    }

    #[test]
    fn perturbed_log_coefficient_is_rejected() {
        let q = poly_from(&[2, -3, 1]); // (x-1)(x-2)
        let p = poly_from(&[1]);
        let mut terms = log_terms(&p, &q).unwrap();
        assert_eq!(verify_log_terms(&p, &q, &terms), Some(true));
        terms[0].0 = terms[0].0.checked_add(Rational::integer(1)).unwrap();
        assert_eq!(
            verify_log_terms(&p, &q, &terms),
            Some(false),
            "a perturbed log-term coefficient must be rejected"
        );
    }

    /// The flagship fixture for the completeness guard: drop one term
    /// entirely. The identity guard (4) is expected to fail too on this
    /// concrete example, so this fixture additionally *isolates*
    /// completeness by checking that even the (structurally valid, single
    /// remaining, correctly-signed) survivor is rejected because it no
    /// longer accounts for the whole denominator -- `∏ vᵢ` is now a proper
    /// factor of `q_bar`, not `q_bar` itself.
    #[test]
    fn dropped_term_breaks_completeness() {
        let q = poly_from(&[2, -3, 1]); // (x-1)(x-2)
        let p = poly_from(&[1]);
        let terms = log_terms(&p, &q).unwrap();
        assert_eq!(terms.len(), 2);
        let incomplete = vec![terms[0].clone()];
        assert_eq!(
            verify_log_terms(&p, &q, &incomplete),
            Some(false),
            "an incomplete log-term set must be rejected"
        );
    }

    /// A duplicate `vᵢ`: split one term's coefficient across two entries
    /// with the SAME `v`. The identity sum is unaffected (splitting one
    /// coefficient into two that add to the same value leaves
    /// `Σ cᵢ vᵢ'(Q/vᵢ)` unchanged), but the completeness product now
    /// double-counts that factor's degree, so completeness alone rejects it.
    /// There is no separate duplicate-`vᵢ` guard in `verify_log_terms` --
    /// mutation testing found one subsumed here on every input (a repeat
    /// necessarily inflates `∏ vᵢ`'s degree past `deg(monic(q_bar))`), so it
    /// was removed rather than kept as decoration, mirroring the
    /// partial-fractions lane's power-set-guard finding.
    #[test]
    fn duplicate_v_is_caught_by_completeness() {
        let q = poly_from(&[2, -3, 1]); // (x-1)(x-2)
        let p = poly_from(&[1]);
        let terms = log_terms(&p, &q).unwrap();
        let (c0, v0) = terms[0].clone();
        let half = c0.checked_div(Rational::integer(2)).unwrap();
        let mut split = vec![(half, v0.clone()), (half, v0)];
        split.push(terms[1].clone());
        assert_eq!(
            verify_log_terms(&p, &q, &split),
            Some(false),
            "duplicate v with split coefficients must still be rejected"
        );
    }

    #[test]
    fn non_monic_v_is_rejected() {
        let q = poly_from(&[2, -3, 1]);
        let p = poly_from(&[1]);
        let mut terms = log_terms(&p, &q).unwrap();
        // Scale one v by 2. Measured: this does NOT isolate the monic-ness
        // guard -- over the rational field, exact division by 2v still
        // succeeds (guard 4 is blind to the scale), but the completeness
        // product now picks up the extra factor of 2 and guard 3 rejects it
        // regardless. Kept as a fixture on the monic guard's SPECIFIED
        // behaviour (it must still reject), with the finding that it is, for
        // this input, subsumed by completeness -- see
        // `spurious_constant_v_with_zero_coefficient_is_rejected` below for
        // the isolating fixture (the "degree >= 1" half of guard 1).
        terms[0].1 = terms[0]
            .1
            .iter()
            .map(|&c| c.checked_mul(Rational::integer(2)).unwrap())
            .collect();
        assert_eq!(verify_log_terms(&p, &q, &terms), Some(false));
    }

    /// Isolates the "degree >= 1" half of guard 1: append a spurious
    /// CONSTANT `v = [1]` (monic, so it does not trip the monic check) with
    /// coefficient `0`. Because the coefficient is zero, it contributes
    /// nothing to guard 4's identity sum; because `v = [1]` is the
    /// multiplicative identity, it leaves guard 3's completeness product
    /// unchanged (`P * 1 == P`); and it is not equal to any real `vᵢ`
    /// (degree 1), so guard 2's duplicate check is vacuous too. Only
    /// rejecting non-constant `v` catches it -- this module's analogue of
    /// `partial_fractions.rs`'s spurious-constant-factor fixture.
    #[test]
    fn spurious_constant_v_with_zero_coefficient_is_rejected() {
        let q = poly_from(&[2, -3, 1]); // (x-1)(x-2)
        let p = poly_from(&[1]);
        let mut terms = log_terms(&p, &q).unwrap();
        assert_eq!(verify_log_terms(&p, &q, &terms), Some(true));
        terms.push((Rational::zero(), poly_from(&[1]))); // c=0, v=1
        assert_eq!(
            verify_log_terms(&p, &q, &terms),
            Some(false),
            "a spurious constant v (even with a zero coefficient) must be rejected"
        );
    }

    #[test]
    fn empty_terms_is_rejected() {
        let q = poly_from(&[-1, 1]);
        let p = poly_from(&[1]);
        assert_eq!(verify_log_terms(&p, &q, &[]), Some(false));
    }
}
