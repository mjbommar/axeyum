//! Gosper's algorithm for indefinite hypergeometric summation (proof-carrying).
//!
//! A term `t(k)` is **hypergeometric** in `k` when the consecutive ratio
//! `t(k+1)/t(k)` is a rational function of `k`. Gosper's algorithm (Gosper 1978;
//! Petkovšek–Wilf–Zeilberger, *A=B*, Ch. 5) decides whether the indefinite sum
//! `∑ t(k)` is itself hypergeometric — **Gosper-summable** — and, when it is,
//! returns a closed form `S(k)` satisfying the telescoping (antidifference)
//! relation
//!
//! ```text
//! S(k+1) − S(k) = t(k).
//! ```
//!
//! It is the discrete analogue of the crate's [`crate::sum_polynomial`] (which
//! solves exactly this relation for *polynomial* `t`) and of [`crate::integrate`]
//! (which returns only differentiate-and-check-certified antiderivatives). As
//! there, the search may be heuristic but the **certificate is a cheap,
//! independent re-check**: the returned `S` is emitted only after the crate's
//! decidable zero-test ([`crate::equal`]) confirms the telescoping identity.
//!
//! # The algorithm
//!
//! Given `t(k)` with reduced ratio `r(k) = t(k+1)/t(k) = a(k)/b(k)`:
//!
//! 1. **Gosper–Petkovšek normal form.** Rewrite `a/b = (p(k+1)/p(k))·(q(k)/r(k))`
//!    with `gcd(q(k), r(k+j)) = 1` for every integer `j ≥ 0`. The candidate
//!    shifts `j` are the non-negative integer roots of the *dispersion*
//!    resultant `Res_k(a(k), b(k+j))` (a polynomial in `j`), stripped one factor
//!    at a time.
//! 2. **Gosper equation.** Solve `q(k)·x(k+1) − r(k−1)·x(k) = p(k)` for a
//!    *polynomial* `x(k)` by bounding `deg x` and solving one exact-rational
//!    linear system. No polynomial solution ⇒ not Gosper-summable ⇒ `None`.
//! 3. **Antidifference.** `S(k) = (r(k−1)/p(k))·x(k)·t(k)`.
//!
//! # Two certifiable fragments (honest scope)
//!
//! What the decidable zero-test can *certify* — not just what the algorithm can
//! compute — bounds the honest scope here:
//!
//! - **Rational-function terms** (`t(k)` a rational function of `k`, e.g.
//!   `∑ k`, `∑ 1/(k(k+1))`). The whole construction lives in the rational
//!   fragment, so `S(k+1) − S(k) − t(k)` is decided *exactly* by
//!   [`crate::equal`]. This is the gold-standard path: `S` is returned only when
//!   `equal(&(S(k+1) − S(k)), t)` is [`ZeroTest::Certified`] with `equal == true`.
//!
//! - **Geometric × polynomial terms** `p(k)·c^k`, with `c^k` represented as
//!   `exp(k·ln c)` (see [`geometric_power`]). Here the *full-expression*
//!   zero-test cannot decide the identity: `equal` treats `exp((k+1)·ln c)` and
//!   `exp(k·ln c)` as independent opaque atoms and never applies the exponent law
//!   `c^{k+1} = c·c^k`, so `equal(&(S(k+1) − S(k)), t)` returns
//!   `Certified{ equal: false }`. The faithful, *decidable* certificate is the
//!   reduced Gosper equation for this shape — the polynomial identity
//!   `c·X(k+1) − X(k) ≡ p(k)` — which [`crate::equal`] certifies exactly and
//!   which is mathematically equivalent to the telescoping relation once the
//!   exact shift law `c^{k+1} = c·c^k` is applied. `S = X(k)·c^k` is returned
//!   only when that polynomial identity certifies.
//!
//! Genuinely factorial/Pochhammer heads (`k!`, binomials) with a symbolic
//! argument are *not representable* in this CAS fragment (powers carry a `u32`
//! exponent, and a `k!` head would be an opaque atom the zero-test cannot relate
//! across a shift), so they are declined (`None`) honestly rather than returned
//! uncertified.

use axeyum_ir::{Rational, poly};

use crate::{CasExpr, UnaryFunc, ZeroTest, binomial_rat, equal, normalize, normalize_rational};

/// A dense univariate rational polynomial, least-significant-coefficient first
/// (index `i` is the coefficient of `var^i`), matching [`axeyum_ir::poly`].
type RatVec = Vec<Rational>;

/// An absolute cap on the degree of the polynomial unknown searched for in the
/// Gosper equation, so a pathological input can neither hang nor blow up the
/// linear system. Well past any degree a real Gosper certificate needs.
const MAX_SOLVE_DEGREE: usize = 64;

/// The indefinite hypergeometric sum `S(var)` of a Gosper-summable term, i.e. an
/// antidifference with `S(var+1) − S(var) = term`, or `None` when the term is not
/// Gosper-summable in this certifiable fragment.
///
/// The `term` must be hypergeometric in `var`. Two shapes are supported:
///
/// - a **rational function** of `var` (the ratio `term(var+1)/term(var)` is a
///   rational function that can be formed directly); the result is certified by
///   the exact zero-test `equal(&(S(var+1) − S(var)), term)`;
/// - a **geometric × polynomial** term `p(var)·c^var`, with `c^var` written as
///   `exp(var·ln c)` (see [`geometric_power`]); certified by the decidable
///   reduced Gosper identity `c·X(var+1) − X(var) ≡ p(var)` (see the module
///   documentation for why the full-expression zero-test is not decidable for
///   this shape).
///
/// Returns `None` — honestly — for any term outside these fragments, when no
/// polynomial solution to the Gosper equation exists (e.g. `∑ 1/k`, which has no
/// hypergeometric closed form), or on exact-arithmetic overflow.
pub fn gosper_sum(term: &CasExpr, var: &str) -> Option<CasExpr> {
    // A term that vanishes identically sums to the zero function.
    if let Some(poly) = normalize(term)
        && poly.is_zero()
    {
        return Some(CasExpr::zero());
    }
    // Primary, fully certified path: rational-function terms.
    if let Some(sum) = rational_gosper(term, var) {
        return Some(sum);
    }
    // Secondary path: geometric × polynomial terms `p(k)·c^k`.
    geometric_gosper(term, var)
}

/// `c^var`, the canonical CAS representation of a geometric factor with rational
/// base `c > 0`, written as `exp(var·ln c)`. This is the representation
/// [`gosper_sum`] recognises for the geometric fragment and the form in which it
/// returns geometric antidifferences.
#[must_use]
pub fn geometric_power(base: Rational, var: &str) -> CasExpr {
    CasExpr::Unary(
        UnaryFunc::Exp,
        Box::new(CasExpr::Mul(vec![
            CasExpr::var(var),
            CasExpr::Unary(UnaryFunc::Ln, Box::new(CasExpr::Const(base))),
        ])),
    )
}

/// Gosper's algorithm on a **rational-function** term, certified by the exact
/// zero-test. Returns `None` if `term` is not a univariate rational function of
/// `var`, if the Gosper equation has no polynomial solution, or on overflow.
fn rational_gosper(term: &CasExpr, var: &str) -> Option<CasExpr> {
    let (ratio_num, ratio_den) = consecutive_ratio(term, var)?;
    let (p_poly, q_poly, r_poly) = gosper_petkovsek(&ratio_num, &ratio_den)?;
    let r_shift = shift_poly(&r_poly, Rational::integer(-1))?; // r(k−1)

    // Try increasing degree bounds for the polynomial unknown x(k); accept the
    // first whose reconstructed antidifference the exact zero-test certifies.
    let deg_p = poly::rat_degree(&p_poly).unwrap_or(0);
    let deg_q = poly::rat_degree(&q_poly).unwrap_or(0);
    let deg_rs = poly::rat_degree(&r_shift).unwrap_or(0);
    let cap = (deg_p + deg_q.max(deg_rs) + 2).min(MAX_SOLVE_DEGREE);
    for bound in 0..=cap {
        let Some(x_coeffs) = solve_gosper_equation(&p_poly, &q_poly, &r_shift, bound) else {
            continue;
        };
        let x_expr = ratvec_to_expr(var, &x_coeffs)?;
        let r_shift_expr = ratvec_to_expr(var, &r_shift)?;
        let p_expr = ratvec_to_expr(var, &p_poly)?;
        // S(k) = (r(k−1)/p(k))·x(k)·t(k).
        let numerator = CasExpr::Mul(vec![r_shift_expr, x_expr, term.clone()]);
        let sum = CasExpr::Div(Box::new(numerator), Box::new(p_expr));
        // Prefer a simplified (lowest-terms) form: the raw quotient often carries
        // a removable `p(k)` singularity, e.g. `(1/k)·x(k)·k` for `∑ k`. Simplify
        // is value-preserving, so certifying the simplified form is sound; the
        // returned expression is always the exact one the certificate accepted.
        let simplified = crate::simplify(&sum);
        if certifies_telescoping(&simplified, term, var) {
            return Some(simplified);
        }
        if certifies_telescoping(&sum, term, var) {
            return Some(sum);
        }
    }
    None
}

/// Gosper's algorithm on a **geometric × polynomial** term `p(var)·c^var`.
/// Returns `None` if `term` is not of that shape (with `c` a positive rational
/// `≠ 1`), if the reduced Gosper equation `c·X(k+1) − X(k) = p(k)` has no
/// polynomial solution, if that identity fails to certify, or on overflow.
fn geometric_gosper(term: &CasExpr, var: &str) -> Option<CasExpr> {
    let (poly_coeffs, base) = split_geometric(term, var)?;
    let x = solve_geometric_equation(&poly_coeffs, base)?;

    // Decidable certificate: the polynomial identity c·X(k+1) − X(k) ≡ p(k).
    let x_expr = ratvec_to_expr(var, &x)?;
    let p_expr = ratvec_to_expr(var, &poly_coeffs)?;
    let x_shift = x_expr.substitute(var, &(CasExpr::var(var) + CasExpr::int(1)));
    let lhs = CasExpr::Const(base) * x_shift - x_expr.clone();
    match equal(&lhs, &p_expr) {
        ZeroTest::Certified { equal: true, .. } => {}
        _ => return None,
    }

    // S(k) = X(k)·c^k.
    Some(CasExpr::Mul(vec![x_expr, geometric_power(base, var)]))
}

/// Whether `sum` is a certified antidifference of `term`: the exact zero-test
/// decides `sum(var+1) − sum(var) − term ≡ 0` as [`ZeroTest::Certified`] with
/// `equal == true`.
fn certifies_telescoping(sum: &CasExpr, term: &CasExpr, var: &str) -> bool {
    let shifted = sum.substitute(var, &(CasExpr::var(var) + CasExpr::int(1)));
    let delta = shifted - sum.clone();
    matches!(
        equal(&delta, term),
        ZeroTest::Certified { equal: true, .. }
    )
}

/// The reduced consecutive ratio `term(var+1)/term(var) = a(var)/b(var)` of a
/// univariate rational-function term, as a pair of coprime polynomials with the
/// denominator's leading coefficient made positive. `None` if `term` is not a
/// univariate rational function of `var` (e.g. it carries an opaque atom such as
/// `exp`), if it vanishes identically, or on overflow.
fn consecutive_ratio(term: &CasExpr, var: &str) -> Option<(RatVec, RatVec)> {
    let shifted = term.substitute(var, &(CasExpr::var(var) + CasExpr::int(1)));
    let ratio = CasExpr::Div(Box::new(shifted), Box::new(term.clone()));
    let rf = normalize_rational(&ratio)?;
    let num = poly::rat_trim(rf.num.to_univariate(var)?);
    let den = poly::rat_trim(rf.den.to_univariate(var)?);
    if num.is_empty() || den.is_empty() {
        return None;
    }
    reduce_fraction(&num, &den)
}

/// Reduce `num/den` to lowest terms via the exact polynomial GCD, normalising the
/// denominator's leading coefficient positive. `None` on overflow.
fn reduce_fraction(num: &[Rational], den: &[Rational]) -> Option<(RatVec, RatVec)> {
    let bound = num.len() + den.len() + 4;
    let g = poly::rat_gcd(num, den, bound)?;
    let mut a = poly::rat_exact_div(num, &g)?;
    let mut b = poly::rat_exact_div(den, &g)?;
    if b.last().is_some_and(|c| c.numerator() < 0) {
        a = poly::rat_negate(&a)?;
        b = poly::rat_negate(&b)?;
    }
    Some((poly::rat_trim(a), poly::rat_trim(b)))
}

/// The Gosper–Petkovšek normal form of `a/b`: polynomials `(p, q, r)` with
/// `a/b = (p(k+1)/p(k))·(q(k)/r(k))` and `gcd(q(k), r(k+j)) = 1` for every
/// integer `j ≥ 0`. Assumes `gcd(a, b) = 1`. `None` on overflow.
fn gosper_petkovsek(a: &[Rational], b: &[Rational]) -> Option<(RatVec, RatVec, RatVec)> {
    let mut q_poly = poly::rat_trim(a.to_vec());
    let mut r_poly = poly::rat_trim(b.to_vec());
    let mut p_poly = vec![Rational::integer(1)];

    for j in nonneg_integer_dispersion(a, b)? {
        // gcd_g(k) = gcd(q(k), r(k+j)); a nontrivial common factor at shift j.
        let r_at_j = shift_poly(&r_poly, Rational::integer(j))?;
        let bound = q_poly.len() + r_at_j.len() + 4;
        let gcd_g = poly::rat_gcd(&q_poly, &r_at_j, bound)?;
        if poly::rat_degree(&gcd_g).is_none_or(|deg| deg == 0) {
            continue; // no nontrivial factor at this shift
        }
        q_poly = poly::rat_exact_div(&q_poly, &gcd_g)?;
        let g_back = shift_poly(&gcd_g, Rational::integer(-j))?; // g(k−j)
        r_poly = poly::rat_exact_div(&r_poly, &g_back)?;
        // p(k) ← p(k)·∏_{i=1}^{j} g(k−i).
        for i in 1..=j {
            let g_shift = shift_poly(&gcd_g, Rational::integer(-i))?;
            p_poly = poly::ratpoly_mul(&p_poly, &g_shift)?;
        }
    }
    Some((
        poly::rat_trim(p_poly),
        poly::rat_trim(q_poly),
        poly::rat_trim(r_poly),
    ))
}

/// The sorted, distinct non-negative integer roots `j` of the dispersion
/// resultant `Res_k(a(k), b(k+j))` — the candidate shifts at which `a` and `b`
/// can share a factor. Empty when either input is constant in `k`. `None` on
/// overflow or coefficients too large to factor.
fn nonneg_integer_dispersion(a: &[Rational], b: &[Rational]) -> Option<Vec<i128>> {
    let (Some(da), Some(db)) = (poly::rat_degree(a), poly::rat_degree(b)) else {
        return Some(Vec::new());
    };
    if da == 0 || db == 0 {
        return Some(Vec::new());
    }
    let resultant = dispersion_resultant(a, b)?;
    let mut roots: Vec<i128> = crate::ratint::rational_roots(&resultant)?
        .into_iter()
        .filter(|value| value.denominator() == 1 && value.numerator() >= 0)
        .map(Rational::numerator)
        .collect();
    roots.sort_unstable();
    roots.dedup();
    Some(roots)
}

/// `Res_k(a(k), b(k+j))` as a polynomial in `j` (LSB-first), built from the
/// bivariate Sylvester machinery in [`axeyum_ir::poly`] with `k` eliminated.
/// `None` on overflow.
fn dispersion_resultant(a: &[Rational], b: &[Rational]) -> Option<RatVec> {
    let a = poly::rat_trim(a.to_vec());
    let b = poly::rat_trim(b.to_vec());
    let da = poly::rat_degree(&a)?;
    let db = poly::rat_degree(&b)?;
    // a(k): each k-coefficient is a constant polynomial in j.
    let a_coeffs: Vec<RatVec> = a[..=da].iter().map(|&c| vec![c]).collect();
    // b(k+j): the coefficient of k^i is Σ_{m≥i} b_m·C(m,i)·j^{m−i}.
    let mut b_coeffs: Vec<RatVec> = Vec::with_capacity(db + 1);
    for i in 0..=db {
        let mut in_j = vec![Rational::zero(); db - i + 1];
        for (m, slot) in in_j.iter_mut().enumerate().map(|(offset, s)| (offset + i, s)) {
            let term = b[m].checked_mul(binomial_rat(m, i)?)?;
            *slot = term;
        }
        b_coeffs.push(poly::rat_trim(in_j));
    }
    let matrix = poly::sylvester_matrix(&a_coeffs, &b_coeffs)?;
    poly::sylvester_determinant(&matrix)
}

/// Solve the Gosper equation `q(k)·x(k+1) − rshift(k)·x(k) = p(k)` for a
/// polynomial `x(k)` of degree `≤ bound`, where `rshift(k) = r(k−1)`. Returns the
/// coefficient vector of `x`, or `None` if no such polynomial exists or on
/// overflow. `x` is recovered as a particular solution (free coefficients set to
/// zero) of one exact-rational linear system.
fn solve_gosper_equation(
    p: &[Rational],
    q: &[Rational],
    rshift: &[Rational],
    bound: usize,
) -> Option<RatVec> {
    let mut columns: Vec<RatVec> = Vec::with_capacity(bound + 1);
    for i in 0..=bound {
        // Contribution of the unknown coefficient xᵢ (basis kⁱ):
        //   q(k)·(k+1)ⁱ − rshift(k)·kⁱ.
        let mono = monomial(i);
        let mono_shift = shift_poly(&mono, Rational::integer(1))?;
        let term1 = poly::ratpoly_mul(q, &mono_shift)?;
        let term2 = poly::ratpoly_mul(rshift, &mono)?;
        columns.push(poly::ratpoly_add(&term1, &poly::ratpoly_neg(&term2)?)?);
    }
    let solution = solve_linear_system(&columns, p)?;
    Some(poly::rat_trim(solution))
}

/// Solve the reduced geometric Gosper equation `c·X(k+1) − X(k) = p(k)` for a
/// polynomial `X(k)` (degree `= deg p`, since `c ≠ 1`). Returns the coefficient
/// vector of `X`, or `None` if no solution exists or on overflow.
fn solve_geometric_equation(p: &[Rational], base: Rational) -> Option<RatVec> {
    let deg_p = poly::rat_degree(p).unwrap_or(0);
    let mut columns: Vec<RatVec> = Vec::with_capacity(deg_p + 1);
    for i in 0..=deg_p {
        // Contribution of Xᵢ (basis kⁱ): c·(k+1)ⁱ − kⁱ.
        let mono = monomial(i);
        let mono_shift = shift_poly(&mono, Rational::integer(1))?;
        let scaled = poly::ratpoly_mul(&[base], &mono_shift)?;
        columns.push(poly::ratpoly_add(&scaled, &poly::ratpoly_neg(&mono)?)?);
    }
    let solution = solve_linear_system(&columns, p)?;
    Some(poly::rat_trim(solution))
}

/// Interpret `term` as `p(var)·c^var` with `c^var = exp(var·ln c)`: return the
/// polynomial coefficients of `p` and the base `c` (a positive rational `≠ 1`).
/// `None` if `term` is not of that shape.
fn split_geometric(term: &CasExpr, var: &str) -> Option<(RatVec, Rational)> {
    let factors = match term {
        CasExpr::Mul(fs) => fs.clone(),
        other => vec![other.clone()],
    };
    let mut base: Option<Rational> = None;
    let mut poly_factors: Vec<CasExpr> = Vec::new();
    for factor in factors {
        if let CasExpr::Unary(UnaryFunc::Exp, arg) = &factor {
            if base.is_some() {
                return None; // more than one geometric factor: out of scope
            }
            base = Some(geometric_base(arg, var)?);
        } else {
            poly_factors.push(factor);
        }
    }
    let base = base?;
    // A real geometric factor needs a positive base; base 1 is the degenerate
    // constant handled by the rational path.
    if base.numerator() <= 0 || base == Rational::integer(1) {
        return None;
    }
    let poly_expr = match poly_factors.len() {
        0 => CasExpr::one(),
        1 => poly_factors.into_iter().next()?,
        _ => CasExpr::Mul(poly_factors),
    };
    let coeffs = poly::rat_trim(normalize(&poly_expr)?.to_univariate(var)?);
    if coeffs.is_empty() {
        return None; // zero polynomial coefficient — nothing to sum
    }
    Some((coeffs, base))
}

/// Extract the base `c` from a geometric exponent `arg = var·ln c`, i.e. the
/// argument of the `exp` head in [`geometric_power`]. `None` if `arg` is not
/// exactly `var` times `ln(c)` for a rational constant `c`.
fn geometric_base(arg: &CasExpr, var: &str) -> Option<Rational> {
    let factors = match arg {
        CasExpr::Mul(fs) => fs.clone(),
        other => vec![other.clone()],
    };
    let mut saw_var = false;
    let mut base: Option<Rational> = None;
    for factor in factors {
        match factor {
            CasExpr::Var(v) if v == var && !saw_var => saw_var = true,
            CasExpr::Unary(UnaryFunc::Ln, inner) if base.is_none() => {
                let CasExpr::Const(value) = *inner else {
                    return None;
                };
                base = Some(value);
            }
            _ => return None,
        }
    }
    if saw_var { base } else { None }
}

/// Solve the exact-rational linear system `Σⱼ xⱼ·columnⱼ = rhs`, where
/// `columnⱼ` is the contribution of unknown `xⱼ` to each equation (equation `i`
/// is the coefficient of `varⁱ`). Handles rectangular (over- or
/// under-determined) systems: returns a particular solution with free unknowns
/// set to zero when the system is consistent, or `None` if it is inconsistent or
/// overflows. Gauss–Jordan elimination over ℚ.
fn solve_linear_system(columns: &[RatVec], rhs: &[Rational]) -> Option<Vec<Rational>> {
    let num_unknowns = columns.len();
    let num_rows = columns
        .iter()
        .map(Vec::len)
        .max()
        .unwrap_or(0)
        .max(rhs.len());
    // Augmented matrix: row i is [column₀[i], …, column_{n−1}[i] | rhs[i]].
    let mut matrix: Vec<Vec<Rational>> = (0..num_rows)
        .map(|i| {
            let mut row: Vec<Rational> = columns
                .iter()
                .map(|col| col.get(i).copied().unwrap_or_else(Rational::zero))
                .collect();
            row.push(rhs.get(i).copied().unwrap_or_else(Rational::zero));
            row
        })
        .collect();

    let mut pivot_columns: Vec<usize> = Vec::new();
    let mut pivot_row = 0usize;
    for col in 0..num_unknowns {
        let Some(sel) = (pivot_row..num_rows).find(|&r| !matrix[r][col].is_zero()) else {
            continue; // free column
        };
        matrix.swap(pivot_row, sel);
        let inverse = Rational::integer(1).checked_div(matrix[pivot_row][col])?;
        for entry in &mut matrix[pivot_row][col..=num_unknowns] {
            *entry = entry.checked_mul(inverse)?;
        }
        let pivot = matrix[pivot_row].clone();
        for (r, row) in matrix.iter_mut().enumerate() {
            if r == pivot_row || row[col].is_zero() {
                continue;
            }
            let factor = row[col];
            for (c, pivot_value) in pivot.iter().enumerate().skip(col) {
                let sub = pivot_value.checked_mul(factor)?;
                row[c] = row[c].checked_sub(sub)?;
            }
        }
        pivot_columns.push(col);
        pivot_row += 1;
        if pivot_row == num_rows {
            break;
        }
    }

    // Consistency: a row that is all-zero in the unknowns but has nonzero rhs has
    // no solution.
    for row in &matrix {
        if row[..num_unknowns].iter().all(|c| c.is_zero()) && !row[num_unknowns].is_zero() {
            return None;
        }
    }

    let mut solution = vec![Rational::zero(); num_unknowns];
    for (row_index, &col) in pivot_columns.iter().enumerate() {
        solution[col] = matrix[row_index][num_unknowns];
    }
    Some(solution)
}

/// The monomial `varⁱ` as a dense coefficient vector.
fn monomial(i: usize) -> RatVec {
    let mut v = vec![Rational::zero(); i + 1];
    v[i] = Rational::integer(1);
    v
}

/// `base` raised to the non-negative integer power `exp`, exact. `None` on
/// overflow.
fn rational_pow(base: Rational, exp: usize) -> Option<Rational> {
    let mut acc = Rational::integer(1);
    for _ in 0..exp {
        acc = acc.checked_mul(base)?;
    }
    Some(acc)
}

/// The shifted polynomial `p(var + c)` (LSB-first), via the binomial expansion
/// `p(var+c) = Σ_i (Σ_{m≥i} p_m·C(m,i)·c^{m−i})·varⁱ`. `None` on overflow.
fn shift_poly(p: &[Rational], c: Rational) -> Option<RatVec> {
    let p = poly::rat_trim(p.to_vec());
    let Some(degree) = poly::rat_degree(&p) else {
        return Some(Vec::new()); // zero polynomial is shift-invariant
    };
    let mut out = vec![Rational::zero(); degree + 1];
    for (m, &coeff) in p.iter().enumerate().take(degree + 1) {
        if coeff.is_zero() {
            continue;
        }
        for (i, slot) in out.iter_mut().enumerate().take(m + 1) {
            let power = rational_pow(c, m - i)?;
            let term = coeff.checked_mul(binomial_rat(m, i)?)?.checked_mul(power)?;
            *slot = slot.checked_add(term)?;
        }
    }
    Some(poly::rat_trim(out))
}

/// Reconstruct a canonical [`CasExpr`] polynomial in `var` from a dense
/// coefficient vector (LSB-first). `None` if a degree does not fit `u32`.
fn ratvec_to_expr(var: &str, coeffs: &[Rational]) -> Option<CasExpr> {
    let mut terms: Vec<CasExpr> = Vec::new();
    for (i, &coeff) in coeffs.iter().enumerate() {
        if coeff.is_zero() {
            continue;
        }
        let mut factors: Vec<CasExpr> = Vec::new();
        if coeff != Rational::integer(1) || i == 0 {
            factors.push(CasExpr::Const(coeff));
        }
        if i >= 1 {
            let base = CasExpr::var(var);
            factors.push(if i == 1 {
                base
            } else {
                base.pow(u32::try_from(i).ok()?)
            });
        }
        terms.push(match factors.len() {
            0 => CasExpr::one(),
            1 => factors.into_iter().next()?,
            _ => CasExpr::Mul(factors),
        });
    }
    Some(match terms.len() {
        0 => CasExpr::zero(),
        1 => terms.into_iter().next()?,
        _ => CasExpr::Add(terms),
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::BTreeMap;

    /// Assert `gosper_sum` returns a closed form whose telescoping identity the
    /// exact zero-test certifies, and return that closed form.
    fn certified_sum(term: &CasExpr, var: &str) -> CasExpr {
        let sum = gosper_sum(term, var).expect("expected a Gosper-summable term");
        let shifted = sum.substitute(var, &(CasExpr::var(var) + CasExpr::int(1)));
        let delta = shifted - sum.clone();
        match equal(&delta, term) {
            ZeroTest::Certified { equal, .. } => {
                assert!(equal, "telescoping identity did not certify: S = {sum}");
            }
            ZeroTest::Unknown => panic!("expected a decidable telescoping check for S = {sum}"),
        }
        sum
    }

    /// Exact numeric partial-sum check: `∑_{k=lo}^{hi} term(k)` must equal
    /// `S(hi+1) − S(lo)` for a rational-valued closed form `S`.
    fn check_partial_sums(term: &CasExpr, sum: &CasExpr, var: &str, lo: i128, hi: i128) {
        let mut running = Rational::zero();
        for k in lo..=hi {
            let mut env = BTreeMap::new();
            env.insert(var.to_owned(), Rational::integer(k));
            let value = term.eval(&env).expect("term evaluates to a rational");
            running = running.checked_add(value).expect("no overflow");

            let mut env_hi = BTreeMap::new();
            env_hi.insert(var.to_owned(), Rational::integer(k + 1));
            let s_hi = sum.eval(&env_hi).expect("S(hi+1) evaluates");
            let mut env_lo = BTreeMap::new();
            env_lo.insert(var.to_owned(), Rational::integer(lo));
            let s_lo = sum.eval(&env_lo).expect("S(lo) evaluates");
            assert_eq!(
                s_hi.checked_sub(s_lo).expect("no overflow"),
                running,
                "partial sum mismatch at k = {k}"
            );
        }
    }

    #[test]
    fn sum_of_k_matches_polynomial_summation() {
        // ∑ k = k(k−1)/2 — must agree with sum_polynomial.
        let term = CasExpr::var("k");
        let sum = certified_sum(&term, "k");
        let expected = crate::sum_polynomial(&term, "k").expect("polynomial sum");
        assert!(matches!(
            equal(&sum, &expected),
            ZeroTest::Certified { equal: true, .. }
        ));
        check_partial_sums(&term, &sum, "k", 0, 12);
    }

    #[test]
    fn sum_of_constant() {
        // ∑ 3 = 3k (up to the S(0)=0 normalisation used by the telescoping check).
        let term = CasExpr::int(3);
        let sum = certified_sum(&term, "k");
        check_partial_sums(&term, &sum, "k", 0, 8);
    }

    #[test]
    fn sum_of_quadratic() {
        // ∑ (k² + 1): a higher-degree polynomial summand.
        let k = CasExpr::var("k");
        let term = k.clone().pow(2) + CasExpr::int(1);
        let sum = certified_sum(&term, "k");
        check_partial_sums(&term, &sum, "k", 0, 9);
    }

    #[test]
    fn telescoping_rational_one_over_k_kplus1() {
        // ∑ 1/(k(k+1)) = −1/k, a telescoping rational sum. Δ[−1/k] = 1/(k(k+1)).
        let k = CasExpr::var("k");
        let term =
            CasExpr::int(1) / (k.clone() * (k.clone() + CasExpr::int(1)));
        let sum = certified_sum(&term, "k");
        // Expect exactly −1/k (up to an additive constant, which the telescoping
        // check absorbs); confirm value-equality with −1/k.
        let expected = -(CasExpr::int(1) / k.clone());
        assert!(matches!(
            equal(&sum, &expected),
            ZeroTest::Certified { equal: true, .. }
        ));
        // Numeric partial sums over a k-range avoiding the pole at 0.
        check_partial_sums(&term, &sum, "k", 1, 10);
    }

    #[test]
    fn telescoping_rational_one_over_k_kplus2() {
        // ∑ 1/(k(k+2)) is Gosper-summable to (a rational function); certify it.
        let k = CasExpr::var("k");
        let term = CasExpr::int(1) / (k.clone() * (k.clone() + CasExpr::int(2)));
        let sum = certified_sum(&term, "k");
        check_partial_sums(&term, &sum, "k", 1, 10);
    }

    #[test]
    fn geometric_times_polynomial_k_two_pow_k() {
        // ∑ k·2^k → (k−2)·2^k. (Note: the antidifference is (k−2)·2^k, since
        // Δ[(k−2)2^k] = (k−1)2^{k+1} − (k−2)2^k = 2^k(2(k−1) − (k−2)) = k·2^k.
        // The often-quoted "(k−1)·2^k" is off by a constant term — its difference
        // is (k+1)·2^k, not k·2^k.)
        let k = CasExpr::var("k");
        let term = CasExpr::Mul(vec![k.clone(), geometric_power(Rational::integer(2), "k")]);
        let sum = gosper_sum(&term, "k").expect("geometric term is Gosper-summable");

        // The closed form is X(k)·2^k with X(k) = k − 2.
        let expected = CasExpr::Mul(vec![
            k.clone() - CasExpr::int(2),
            geometric_power(Rational::integer(2), "k"),
        ]);
        assert!(matches!(
            equal(&sum, &expected),
            ZeroTest::Certified { equal: true, .. }
        ));

        // Independent numeric telescoping check, evaluating 2^k exactly by hand
        // (CasExpr::eval cannot evaluate the exp/ln atoms). With X(k)=k−2:
        //   Δ = X(k+1)·2^{k+1} − X(k)·2^k = (k−1)·2^{k+1} − (k−2)·2^k = k·2^k.
        let x = |k: i128| Rational::integer(k - 2); // X(k) = k − 2
        let pow2 = |k: i128| Rational::integer(1i128 << k);
        for k in 0..=12 {
            let delta = x(k + 1)
                .checked_mul(pow2(k + 1))
                .unwrap()
                .checked_sub(x(k).checked_mul(pow2(k)).unwrap())
                .unwrap();
            let rhs = Rational::integer(k).checked_mul(pow2(k)).unwrap(); // k·2^k
            assert_eq!(delta, rhs, "geometric telescoping mismatch at k = {k}");
        }
    }

    #[test]
    fn geometric_times_quadratic() {
        // ∑ (k²)·3^k is Gosper-summable to a (quadratic)·3^k closed form.
        let base = Rational::integer(3);
        let k = CasExpr::var("k");
        let term = CasExpr::Mul(vec![k.clone().pow(2), geometric_power(base, "k")]);
        assert!(
            gosper_sum(&term, "k").is_some(),
            "geometric·quadratic is Gosper-summable (certified by the reduced identity)"
        );

        // Reconstruct the solution polynomial X(k) of 3·X(k+1) − X(k) = k² and
        // check the exact telescoping X(k+1)·3^{k+1} − X(k)·3^k = k²·3^k over a
        // range of integer points (CasExpr::eval cannot evaluate the 3^k atom).
        let p = vec![Rational::zero(), Rational::zero(), Rational::integer(1)]; // k²
        let x = solve_geometric_equation(&p, base).expect("reduced Gosper equation is solvable");
        let eval_x = |k: i128| poly::eval_rat_poly(&x, Rational::integer(k)).unwrap();
        let pow3 = |k: i128| Rational::integer(3i128.pow(u32::try_from(k).unwrap()));
        for k in 0..=8 {
            let delta = eval_x(k + 1)
                .checked_mul(pow3(k + 1))
                .unwrap()
                .checked_sub(eval_x(k).checked_mul(pow3(k)).unwrap())
                .unwrap();
            let rhs = Rational::integer(k * k).checked_mul(pow3(k)).unwrap();
            assert_eq!(delta, rhs, "geometric·quadratic mismatch at k = {k}");
        }
    }

    #[test]
    fn not_gosper_summable_one_over_k() {
        // ∑ 1/k has no hypergeometric closed form — decline honestly.
        let term = CasExpr::int(1) / CasExpr::var("k");
        assert_eq!(gosper_sum(&term, "k"), None);
    }

    #[test]
    fn not_gosper_summable_harmonic_shift() {
        // ∑ 1/(k+1) is likewise not Gosper-summable.
        let term = CasExpr::int(1) / (CasExpr::var("k") + CasExpr::int(1));
        assert_eq!(gosper_sum(&term, "k"), None);
    }

    #[test]
    fn factorial_head_is_declined() {
        // A genuine factorial head (opaque atom) is out of the certifiable
        // fragment: decline honestly rather than return an uncertified answer.
        let k = CasExpr::var("k");
        // "k!" modelled as an opaque unary atom via ln — not a geometric power.
        let fake_factorial = CasExpr::Unary(UnaryFunc::Ln, Box::new(k.clone()));
        let term = CasExpr::Mul(vec![k, fake_factorial]);
        assert_eq!(gosper_sum(&term, "k"), None);
    }

    #[test]
    fn dispersion_and_shift_helpers() {
        // shift_poly: (k)² shifted by +1 is (k+1)² = k² + 2k + 1.
        let sq = vec![Rational::zero(), Rational::zero(), Rational::integer(1)];
        let shifted = shift_poly(&sq, Rational::integer(1)).unwrap();
        assert_eq!(
            shifted,
            vec![
                Rational::integer(1),
                Rational::integer(2),
                Rational::integer(1)
            ]
        );
        // dispersion of a = k+1, b = k has the single non-negative shift j = 1.
        let a = vec![Rational::integer(1), Rational::integer(1)];
        let b = vec![Rational::zero(), Rational::integer(1)];
        assert_eq!(nonneg_integer_dispersion(&a, &b).unwrap(), vec![1]);
    }
}
