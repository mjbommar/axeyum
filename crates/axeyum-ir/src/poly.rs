//! Exact-rational univariate polynomial + Sturm primitives (arena-free).
//!
//! These are the pure number-theoretic building blocks the real-algebraic
//! *value* layer (`crate::real_algebraic`) and the solver's NRA root-isolation
//! pass both need: exact-`Rational` polynomial arithmetic (LSB-first vectors),
//! the squarefree-part reduction, the Sturm chain and its exact distinct-root
//! count, and the Sylvester-resultant primitive used for algebraic field
//! arithmetic.
//!
//! Everything here is **exact** (no floating point) and **overflow-graceful**:
//! every step is `checked_*` and any `i128`/[`Rational`] overflow returns
//! `None` so the caller declines rather than ever producing a wrong value.
//!
//! Degree / coefficient guards are passed in as parameters (`max_degree`,
//! `max_abs_coeff`) so the same primitive serves callers with different bounds
//! without baking one policy into the leaf crate.

use core::cmp::Ordering;

use crate::rational::Rational;
use crate::real_algebraic::Sign;

/// A polynomial with exact `Rational` coefficients (LSB-first). The Sturm chain
/// remainders have rational coefficients even when `p` is integer, so the chain
/// is computed in this representation throughout.
pub type RatVec = Vec<Rational>;

/// Drop trailing (high-degree) zero coefficients so the leading coefficient is
/// genuinely nonzero. The zero polynomial becomes the empty vector.
#[must_use]
pub fn rat_trim(mut p: RatVec) -> RatVec {
    while p.last().is_some_and(|c| c.is_zero()) {
        p.pop();
    }
    p
}

/// The (true, post-trim) degree, or `None` for the zero polynomial.
#[must_use]
pub fn rat_degree(p: &[Rational]) -> Option<usize> {
    let mut n = p.len();
    while n > 0 && p[n - 1].is_zero() {
        n -= 1;
    }
    if n == 0 { None } else { Some(n - 1) }
}

/// Lift an LSB-first integer polynomial to a trimmed rational polynomial.
#[must_use]
pub fn rat_from_int(poly: &[i128]) -> RatVec {
    rat_trim(poly.iter().map(|&c| Rational::integer(c)).collect())
}

/// The formal derivative `p'` (LSB-first), exact. `None` on overflow.
#[must_use]
pub fn rat_derivative(p: &[Rational]) -> Option<RatVec> {
    if p.len() <= 1 {
        return Some(Vec::new()); // constant ⇒ derivative 0
    }
    let mut out = Vec::with_capacity(p.len() - 1);
    for (i, &c) in p.iter().enumerate().skip(1) {
        out.push(c.checked_mul(Rational::integer(i128::try_from(i).ok()?))?);
    }
    Some(rat_trim(out))
}

/// Exact polynomial remainder `a mod b` (LSB-first), `b ≠ 0`. Long division over
/// `Rational`; `None` on overflow. The result has degree `< deg(b)`.
#[must_use]
pub fn rat_rem(a: &[Rational], b: &[Rational]) -> Option<RatVec> {
    let db = rat_degree(b)?; // b ≠ 0 by contract
    let lead_b = b[db];
    let mut r = rat_trim(a.to_vec());
    // Reduce while deg(r) ≥ deg(b).
    while let Some(dr) = rat_degree(&r) {
        if dr < db {
            break;
        }
        // factor = (lead_r / lead_b) · x^(dr − db)
        let coeff = r[dr].checked_div(lead_b)?;
        let shift = dr - db;
        for (j, &bj) in b[..=db].iter().enumerate() {
            let sub = coeff.checked_mul(bj)?;
            let idx = j + shift;
            r[idx] = r[idx].checked_sub(sub)?;
        }
        // The leading term must cancel exactly; trim it (and any new trailing
        // zeros) so the loop makes progress.
        r = rat_trim(r);
        if rat_degree(&r).is_some_and(|d| d == dr) {
            // Leading term failed to cancel (should be impossible with exact
            // arithmetic); decline rather than loop forever.
            return None;
        }
    }
    Some(r)
}

/// Exact polynomial GCD (monic-normalized result), via the Euclidean algorithm
/// over `Rational`. Returns the zero polynomial only if both inputs are zero;
/// `None` on overflow. Used to extract the squarefree part `p / gcd(p, p')`.
/// `max_degree` bounds the Euclidean iterations so a pathological input cannot
/// spin.
#[must_use]
pub fn rat_gcd(a: &[Rational], b: &[Rational], max_degree: usize) -> Option<RatVec> {
    let mut a = rat_trim(a.to_vec());
    let mut b = rat_trim(b.to_vec());
    for _ in 0..(max_degree + 4) {
        if rat_degree(&b).is_none() {
            // b == 0 ⇒ gcd is a; normalize to monic.
            return rat_make_monic(&a);
        }
        let r = rat_rem(&a, &b)?;
        a = b;
        b = r;
    }
    None
}

/// Normalize a nonzero polynomial to monic (divide by its leading coefficient);
/// the zero polynomial maps to zero. `None` on overflow.
#[must_use]
pub fn rat_make_monic(p: &[Rational]) -> Option<RatVec> {
    let Some(d) = rat_degree(p) else {
        return Some(Vec::new());
    };
    let lead = p[d];
    let mut out = Vec::with_capacity(d + 1);
    for &c in &p[..=d] {
        out.push(c.checked_div(lead)?);
    }
    Some(out)
}

/// Exact polynomial division `a / b` assuming `b` divides `a` EXACTLY (the
/// squarefree-part extraction calls this with `b = gcd(p, p')`). Returns the
/// quotient (LSB-first), or `None` on overflow or a nonzero remainder (a
/// defensive guard — `b | a` should make the remainder vanish).
#[must_use]
pub fn rat_exact_div(a: &[Rational], b: &[Rational]) -> Option<RatVec> {
    let db = rat_degree(b)?;
    let lead_b = b[db];
    let mut r = rat_trim(a.to_vec());
    let Some(da) = rat_degree(&r) else {
        return Some(Vec::new()); // 0 / b = 0
    };
    if da < db {
        return None; // not an exact multiple (nonzero a of lower degree)
    }
    let mut quot = vec![Rational::zero(); da - db + 1];
    while let Some(dr) = rat_degree(&r) {
        if dr < db {
            break;
        }
        let coeff = r[dr].checked_div(lead_b)?;
        let shift = dr - db;
        quot[shift] = coeff;
        for (j, &bj) in b[..=db].iter().enumerate() {
            let sub = coeff.checked_mul(bj)?;
            let idx = j + shift;
            r[idx] = r[idx].checked_sub(sub)?;
        }
        r = rat_trim(r);
        if rat_degree(&r).is_some_and(|d| d == dr) {
            return None;
        }
    }
    // Exact division ⇒ remainder must be zero.
    if rat_degree(&r).is_some() {
        return None;
    }
    Some(rat_trim(quot))
}

/// The squarefree part `p / gcd(p, p')` of `p` (same root SET, every root now
/// simple), as a trimmed rational polynomial. `None` on overflow or a degenerate
/// shape (constant `p`). When `gcd(p, p')` is a nonzero constant, `p` is already
/// squarefree and is returned (trimmed) unchanged.
#[must_use]
pub fn squarefree_part(p: &[Rational], max_degree: usize) -> Option<RatVec> {
    let dp = rat_degree(p)?; // None ⇒ zero poly: caller handles separately
    if dp == 0 {
        return None; // constant: no roots, not our job here
    }
    let dpoly = rat_derivative(p)?;
    let g = rat_gcd(p, &dpoly, max_degree)?;
    match rat_degree(&g) {
        // gcd is a nonzero constant ⇒ already squarefree.
        Some(0) | None => Some(rat_trim(p.to_vec())),
        Some(_) => rat_exact_div(p, &g),
    }
}

/// Clear denominators of a rational polynomial to an integer polynomial
/// (LSB-first), multiplying through by the LCM of all denominators. The
/// multiplier is positive, so the polynomial's real roots are UNCHANGED.
/// Declines (`None`) on overflow or if any cleared coefficient's magnitude is
/// `>= max_abs_coeff`.
#[must_use]
pub fn rat_to_int_poly(p: &[Rational], max_abs_coeff: i128) -> Option<Vec<i128>> {
    if p.is_empty() {
        return None;
    }
    let mut lcm = 1i128;
    for c in p {
        lcm = lcm_i128(lcm, c.denominator())?;
    }
    let mut out = Vec::with_capacity(p.len());
    for c in p {
        let scaled = c.numerator().checked_mul(lcm)?;
        if scaled % c.denominator() != 0 {
            return None;
        }
        let v = scaled / c.denominator();
        if v.checked_abs()? >= max_abs_coeff {
            return None;
        }
        out.push(v);
    }
    while out.len() > 1 && out.last().copied() == Some(0) {
        out.pop();
    }
    Some(out)
}

/// Exact Horner evaluation of a rational polynomial (LSB-first) at `x`. `None` on
/// overflow.
#[must_use]
pub fn eval_rat_poly(p: &[Rational], x: Rational) -> Option<Rational> {
    let mut acc = Rational::zero();
    for &c in p.iter().rev() {
        acc = acc.checked_mul(x)?.checked_add(c)?;
    }
    Some(acc)
}

/// Exact Horner evaluation of an LSB-first **integer** polynomial at a
/// [`Rational`], returning `None` on `i128`/[`Rational`] overflow.
#[must_use]
pub fn eval_int_poly(poly: &[i128], x: Rational) -> Option<Rational> {
    let mut acc = Rational::zero();
    for &c in poly.iter().rev() {
        acc = acc.checked_mul(x)?.checked_add(Rational::integer(c))?;
    }
    Some(acc)
}

/// Exact coefficient-wise negation of a rational polynomial. `None` on overflow.
#[must_use]
pub fn rat_negate(p: &[Rational]) -> Option<RatVec> {
    let mut out = Vec::with_capacity(p.len());
    for &c in p {
        out.push(c.checked_neg()?);
    }
    Some(out)
}

/// The Sturm chain `S₀ = p, S₁ = p', S_{k+1} = −rem(S_{k−1}, S_k)` of a
/// SQUAREFREE polynomial `p`. The chain is returned LSB-first per element; its
/// length is bounded by `deg(p) + 2`. `None` on overflow (⇒ decline). Each step
/// strictly drops the degree, so the chain always terminates; the
/// `max_degree`-derived bound is a belt-and-suspenders guard against any
/// unexpected non-termination.
#[must_use]
pub fn sturm_chain(p: &[Rational], max_degree: usize) -> Option<Vec<RatVec>> {
    let dp = rat_degree(p)?;
    let mut chain: Vec<RatVec> = Vec::with_capacity(dp + 2);
    chain.push(rat_trim(p.to_vec()));
    let deriv = rat_derivative(p)?;
    // p' == 0 ⇒ p is constant; no Sturm chain (handled by the caller).
    rat_degree(&deriv)?;
    chain.push(deriv);
    // After the first two, each S_{k+1} = −rem(S_{k−1}, S_k). Bounded by degree.
    for _ in 0..(max_degree + 2) {
        let n = chain.len();
        let prev2 = &chain[n - 2];
        let prev1 = &chain[n - 1];
        if rat_degree(prev1).is_none() {
            break; // last pushed element was zero (cannot happen: we break before)
        }
        let r = rat_rem(prev2, prev1)?;
        if rat_degree(&r).is_none() {
            break; // remainder zero ⇒ chain complete
        }
        let neg = rat_negate(&r)?;
        chain.push(neg);
    }
    Some(chain)
}

/// `V(t)`: the number of sign alternations in the Sturm chain evaluated at `t`,
/// dropping zeros. `None` on overflow.
#[must_use]
pub fn sturm_sign_changes(chain: &[RatVec], t: Rational) -> Option<usize> {
    let mut changes = 0usize;
    let mut last: Option<Sign> = None;
    for s in chain {
        let v = eval_rat_poly(s, t)?;
        let sign = sign_of_rational(v);
        if sign == Sign::Zero {
            continue; // zeros are ignored
        }
        if let Some(prev) = last
            && prev != sign
        {
            changes += 1;
        }
        last = Some(sign);
    }
    Some(changes)
}

/// `count_roots_in(chain, lo, hi) = V(lo) − V(hi)`: the EXACT number of distinct
/// real roots of the squarefree `p` in the half-open interval `(lo, hi]`.
///
/// `lo` and `hi` must not themselves be roots of `p` (the Cauchy bound endpoints
/// `±B` are safe — `B` strictly exceeds every root magnitude). `None` on
/// overflow, or if `V(lo) < V(hi)` (impossible for a valid Sturm chain — a
/// defensive guard so a bug can never yield a bogus large count).
#[must_use]
pub fn count_roots_in(chain: &[RatVec], lo: Rational, hi: Rational) -> Option<usize> {
    let vlo = sturm_sign_changes(chain, lo)?;
    let vhi = sturm_sign_changes(chain, hi)?;
    vlo.checked_sub(vhi)
}

/// Multiply two LSB-first rational univariate polynomials. `None` on overflow.
#[must_use]
pub fn ratpoly_mul(a: &[Rational], b: &[Rational]) -> Option<Vec<Rational>> {
    if a.is_empty() || b.is_empty() {
        return Some(vec![Rational::zero()]);
    }
    let mut out = vec![Rational::zero(); a.len() + b.len() - 1];
    for (i, &ca) in a.iter().enumerate() {
        if ca.is_zero() {
            continue;
        }
        for (j, &cb) in b.iter().enumerate() {
            let term = ca.checked_mul(cb)?;
            out[i + j] = out[i + j].checked_add(term)?;
        }
    }
    Some(out)
}

/// Add two LSB-first rational univariate polynomials. `None` on overflow.
#[must_use]
pub fn ratpoly_add(a: &[Rational], b: &[Rational]) -> Option<Vec<Rational>> {
    let n = a.len().max(b.len());
    let mut out = vec![Rational::zero(); n];
    for (i, slot) in out.iter_mut().enumerate() {
        let ca = a.get(i).copied().unwrap_or_else(Rational::zero);
        let cb = b.get(i).copied().unwrap_or_else(Rational::zero);
        *slot = ca.checked_add(cb)?;
    }
    Some(out)
}

/// Negate an LSB-first rational univariate polynomial. `None` on overflow.
#[must_use]
pub fn ratpoly_neg(a: &[Rational]) -> Option<Vec<Rational>> {
    let mut out = Vec::with_capacity(a.len());
    for &c in a {
        out.push(c.checked_neg()?);
    }
    Some(out)
}

/// Determinant of a square matrix whose entries are LSB-first rational univariate
/// polynomials, by Leibniz permutation expansion (exact; `O(dim!)`). Returns the
/// determinant polynomial (LSB-first). `None` on overflow.
///
/// This is the **reference oracle** kept for the differential test that pins the
/// fast [`sylvester_determinant`] (evaluation–interpolation) to the same exact
/// coefficient vector. It is NOT on the solver hot path (its factorial cost is the
/// reason for the replacement) — do not call it for production resultants.
#[must_use]
pub fn sylvester_determinant_leibniz(mat: &[Vec<Vec<Rational>>]) -> Option<Vec<Rational>> {
    let n = mat.len();
    let mut perm: Vec<usize> = (0..n).collect();
    let mut acc = vec![Rational::zero()];
    let mut used = vec![false; n];
    leibniz_recurse(mat, &mut perm, 0, &mut used, &mut acc)?;
    Some(rat_trim(acc))
}

/// Determinant of a square matrix whose entries are LSB-first rational univariate
/// polynomials in one variable `x`, returned as the determinant polynomial `R(x)`
/// (LSB-first). Exact, no floating point, `O(D · dim³)` where `D` bounds `deg R`.
///
/// Method (exact evaluation–interpolation):
/// 1. **Degree bound** `D = Σ_i max_j deg(M[i][j])` — a safe upper bound on
///    `deg R` (every Leibniz term is a product of one entry per row, so its degree
///    is `≤ Σ_i max_j deg(M[i][j])`). Over-estimates are harmless (extra,
///    redundant interpolation points). An all-zero / empty row makes `R ≡ 0`.
/// 2. **Evaluate** the polynomial matrix at the `D+1` distinct integer points
///    `x = 0,1,…,D`, giving `D+1` scalar `Rational` matrices.
/// 3. **Scalar determinant** of each via fraction-free Bareiss elimination
///    (exact over ℚ; `O(dim³)`).
/// 4. **Interpolate** `R(x)` from the `D+1` pairs `(k, det_k)` by exact Newton
///    divided differences over ℚ.
///
/// `None` on any `i128`/[`Rational`] overflow (the caller declines) — never a
/// wrong coefficient. The result equals [`sylvester_determinant_leibniz`] exactly
/// (pinned by a differential test).
#[must_use]
pub fn sylvester_determinant(mat: &[Vec<Vec<Rational>>]) -> Option<Vec<Rational>> {
    let n = mat.len();
    if n == 0 {
        // Determinant of the empty matrix is 1 (matches Leibniz: the single empty
        // permutation contributes the empty product).
        return Some(vec![Rational::integer(1)]);
    }
    // Degree bound D = Σ_i max_j deg(M[i][j]). A row of all-zero entries forces a
    // zero determinant (every Leibniz term passes through that row).
    let mut deg_bound: usize = 0;
    for row in mat {
        debug_assert_eq!(row.len(), n);
        let mut row_max: Option<usize> = None;
        for entry in row {
            if let Some(d) = rat_degree(entry) {
                row_max = Some(row_max.map_or(d, |m: usize| m.max(d)));
            }
        }
        match row_max {
            // Whole row is zero ⇒ determinant is identically zero.
            None => return Some(vec![Rational::zero()]),
            Some(d) => deg_bound = deg_bound.checked_add(d)?,
        }
    }
    let num_points = deg_bound.checked_add(1)?;
    let mut xs: Vec<Rational> = Vec::with_capacity(num_points);
    let mut ys: Vec<Rational> = Vec::with_capacity(num_points);
    for k in 0..num_points {
        let x = Rational::integer(i128::try_from(k).ok()?);
        let scalar = eval_poly_matrix(mat, x)?;
        let det = bareiss_determinant(&scalar)?;
        xs.push(x);
        ys.push(det);
    }
    let coeffs = newton_interpolate(&xs, &ys)?;
    Some(rat_trim(coeffs))
}

/// Evaluate every entry of a polynomial-entry matrix at `x`, producing a scalar
/// `Rational` matrix. `None` on overflow.
fn eval_poly_matrix(mat: &[Vec<Vec<Rational>>], x: Rational) -> Option<Vec<Vec<Rational>>> {
    let n = mat.len();
    let mut out = Vec::with_capacity(n);
    for row in mat {
        let mut orow = Vec::with_capacity(n);
        for entry in row {
            orow.push(eval_rat_poly(entry, x)?);
        }
        out.push(orow);
    }
    Some(out)
}

/// Exact determinant of a square scalar `Rational` matrix by fraction-free Bareiss
/// elimination with partial pivoting. `O(n³)`, exact over ℚ (the Bareiss division
/// is exact: each pivot quotient is an integer combination that divides evenly).
/// `None` on overflow. Returns `Rational::zero()` for a singular matrix.
fn bareiss_determinant(mat: &[Vec<Rational>]) -> Option<Rational> {
    let n = mat.len();
    if n == 0 {
        return Some(Rational::integer(1));
    }
    let mut a: Vec<Vec<Rational>> = mat.to_vec();
    let mut sign = 1i32;
    let mut prev = Rational::integer(1); // previous pivot (M[k-1][k-1] after step)
    for k in 0..n {
        // Pivot: if the diagonal is zero, swap in a nonzero row below.
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
                None => return Some(Rational::zero()), // singular
            }
        }
        let pivot = a[k][k];
        for i in (k + 1)..n {
            for j in (k + 1)..n {
                // a[i][j] = (a[i][j]·pivot − a[i][k]·a[k][j]) / prev  (exact).
                let term1 = a[i][j].checked_mul(pivot)?;
                let term2 = a[i][k].checked_mul(a[k][j])?;
                let num = term1.checked_sub(term2)?;
                a[i][j] = num.checked_div(prev)?;
            }
            a[i][k] = Rational::zero();
        }
        prev = pivot;
    }
    let det = a[n - 1][n - 1];
    if sign < 0 {
        det.checked_neg()
    } else {
        Some(det)
    }
}

/// Exact Newton-divided-difference interpolation of the unique polynomial of
/// degree `< xs.len()` through the points `(xs[i], ys[i])` (distinct `xs`),
/// returned as an LSB-first `Rational` coefficient vector. `None` on overflow.
fn newton_interpolate(xs: &[Rational], ys: &[Rational]) -> Option<Vec<Rational>> {
    let n = xs.len();
    if n == 0 {
        return Some(vec![Rational::zero()]);
    }
    // Divided differences: coeff[k] = f[x0,…,xk] computed in place.
    let mut coeff = ys.to_vec();
    for level in 1..n {
        for i in (level..n).rev() {
            // (coeff[i] − coeff[i-1]) / (xs[i] − xs[i-level])
            let num = coeff[i].checked_sub(coeff[i - 1])?;
            let den = xs[i].checked_sub(xs[i - level])?;
            coeff[i] = num.checked_div(den)?;
        }
    }
    // Horner-from-the-top expansion to standard coefficients:
    //   R(x) = ((coeff[n-1])(x−x_{n-2}) + coeff[n-2])(x−x_{n-3}) + …
    // Maintain `result` as an LSB-first coefficient vector.
    let mut result: Vec<Rational> = vec![coeff[n - 1]];
    for k in (0..n - 1).rev() {
        // result = result·(x − xs[k]) + coeff[k]
        // Multiply by x: shift up by one degree.
        let mut next = vec![Rational::zero(); result.len() + 1];
        for (i, &c) in result.iter().enumerate() {
            next[i + 1] = next[i + 1].checked_add(c)?;
        }
        // Subtract xs[k]·result.
        for (i, &c) in result.iter().enumerate() {
            let sub = c.checked_mul(xs[k])?;
            next[i] = next[i].checked_sub(sub)?;
        }
        // Add coeff[k] (constant term).
        next[0] = next[0].checked_add(coeff[k])?;
        result = next;
    }
    Some(result)
}

/// One step of the Leibniz determinant expansion: choose the row for column `col`,
/// recurse, and at a complete permutation accumulate the signed entry product (the
/// sign from inversion parity). `None` on any polynomial-arithmetic overflow.
fn leibniz_recurse(
    mat: &[Vec<Vec<Rational>>],
    perm: &mut [usize],
    col: usize,
    used: &mut [bool],
    acc: &mut Vec<Rational>,
) -> Option<()> {
    let n = mat.len();
    if col == n {
        let mut prod = vec![Rational::integer(1)];
        for (i, &c) in perm.iter().enumerate() {
            prod = ratpoly_mul(&prod, &mat[i][c])?;
        }
        if permutation_sign(perm) < 0 {
            prod = ratpoly_neg(&prod)?;
        }
        *acc = ratpoly_add(acc, &prod)?;
        return Some(());
    }
    for r in 0..n {
        if used[r] {
            continue;
        }
        used[r] = true;
        perm[col] = r;
        leibniz_recurse(mat, perm, col + 1, used, acc)?;
        used[r] = false;
    }
    Some(())
}

/// The sign (+1 / −1) of a permutation given as a slice mapping position → value,
/// by counting inversions.
fn permutation_sign(perm: &[usize]) -> i32 {
    let mut inv = 0usize;
    for i in 0..perm.len() {
        for j in (i + 1)..perm.len() {
            if perm[i] > perm[j] {
                inv += 1;
            }
        }
    }
    if inv.is_multiple_of(2) { 1 } else { -1 }
}

/// `Res_y(p, q)` of two univariate rational polynomials (LSB-first), as a
/// rational scalar — degenerate-resultant special case where both inputs are
/// univariate in the *same* eliminated variable, so the Sylvester entries are
/// scalars. For the algebraic field-arithmetic use the resultant is bivariate
/// (entries are polynomials in the surviving variable) and is built directly by
/// the caller via [`sylvester_determinant`].
///
/// Build the `(deg p + deg q)`-dimensional Sylvester matrix of two LSB-first
/// **rational-coefficient** univariate polynomials whose coefficients are
/// themselves LSB-first rational polynomials in a surviving variable (`p_coeffs`
/// and `q_coeffs` are indexed by the eliminated variable's exponent, each entry a
/// `RatVec` in the surviving variable). Returns the matrix ready for
/// [`sylvester_determinant`], or `None` on a degenerate (degree-0) input.
#[must_use]
pub fn sylvester_matrix(
    p_coeffs: &[RatVec],
    q_coeffs: &[RatVec],
) -> Option<Vec<Vec<Vec<Rational>>>> {
    let m = p_coeffs.len().checked_sub(1)?; // deg_elim(p)
    let n = q_coeffs.len().checked_sub(1)?; // deg_elim(q)
    if m == 0 || n == 0 {
        return None;
    }
    let dim = m + n;
    let zero_cell = || vec![Rational::zero()];
    let mut mat: Vec<Vec<Vec<Rational>>> = vec![vec![zero_cell(); dim]; dim];
    // p's coefficients, MSB(elim)-first: index 0 ↔ elim^m.
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

/// LCM of two `i128` magnitudes, declining on overflow.
#[must_use]
pub fn lcm_i128(a: i128, b: i128) -> Option<i128> {
    if a == 0 || b == 0 {
        return Some(0);
    }
    let g = gcd_i128(a.unsigned_abs(), b.unsigned_abs());
    // a / g * b, with g | a exactly.
    let a_div = a.checked_div(i128::try_from(g).ok()?)?;
    a_div.checked_mul(b)?.checked_abs()
}

/// GCD of two unsigned magnitudes (Euclid).
#[must_use]
pub fn gcd_i128(mut a: u128, mut b: u128) -> u128 {
    while b != 0 {
        let t = a % b;
        a = b;
        b = t;
    }
    a
}

/// The sign of a rational value (`< 0`, `= 0`, `> 0`).
#[must_use]
pub fn sign_of_rational(r: Rational) -> Sign {
    match r.numerator().cmp(&0) {
        Ordering::Less => Sign::Neg,
        Ordering::Equal => Sign::Zero,
        Ordering::Greater => Sign::Pos,
    }
}
