//! Independent verification of a creative-telescoping certificate.
//!
//! This module is the **consumer** of [`crate::telescoping`]'s output and shares
//! no code with it. It re-derives the shift ratios of the term from the
//! specification with its own implementation, re-derives the certificate
//! identity by plain fraction arithmetic rather than by the producer's
//! linear-system layout, and — the part that actually carries the independence —
//! cross-checks both against **direct exact-bignum evaluation of the term at
//! integer points**, which computes real factorials and shares nothing at all
//! with the symbolic route.
//!
//! A bug in the producer can therefore lose a proof but cannot manufacture one.
//! A bug in this module's *symbolic* half is caught by its *concrete* half and
//! vice versa: the two halves agree only if the ratios really are the term's
//! ratios.
//!
//! # What is checked
//!
//! For a certificate `(a_0 … a_J, R = P/Q)` about `F` with summation variable
//! `k` and shift variable `n`:
//!
//! 1. **Shape** — the recurrence is nonempty with a nonzero leading coefficient,
//!    `Q` is not the zero polynomial, `P` and `Q` are free of nothing in
//!    particular but must be genuine polynomials.
//! 2. **The rational identity**
//!    `Σ_j a_j·S_j = R(k+1)·r − R` in `ℚ(vars)`, cleared to a polynomial
//!    identity and compared against zero exactly.
//! 3. **Ratio integrity** — at a grid of integer points, `S_j` and `r` are
//!    confirmed against `F` computed from actual factorials in exact bignum
//!    rationals.
//! 4. **Pointwise telescoping** — at every integer `k` of a scanned window,
//!    `Σ_j a_j(n)·F(n+j,k) = G(n,k+1) − G(n,k)` with `G = R·F`, in exact bignum.
//!    Points where `Q` vanishes are counted and reported, never silently skipped.
//! 5. **Boundary** — `F` and `G` vanish at both ends of the window, so the
//!    telescoped sum really is zero.
//! 6. **The recurrence itself** — `Σ_j a_j(n)·S(n+j) = 0` by exact finite
//!    summation at each sampled `n`.
//!
//! # What is *not* checked, and must be assumed
//!
//! Step 2 is an identity of rational functions; steps 4–6 confirm its integer
//! consequences only at the sampled points. Passing from "holds in `ℚ(n,k)`" to
//! "holds at every integer of the summation range, for every `n`" needs the
//! standard side condition that `G = R·F` has the same natural boundary as `F`
//! and acquires no pole inside the range. That assumption is *named*, not
//! hidden, and steps 4–5 are exactly the evidence that it is not vacuous.

use std::collections::{BTreeMap, BTreeSet};

use axeyum_ir::Rational;
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Zero};

use crate::mvpoly::MvPoly;
use crate::telescoping::{Factor, HyperTerm, LinearForm, TelescopingCertificate};

/// Largest `Γ` argument the concrete evaluator will expand into a factorial.
const MAX_CONCRETE_GAMMA: i64 = 512;

/// Largest absolute exponent the concrete evaluator will raise a base to.
const MAX_CONCRETE_POWER: i64 = 4_096;

/// Largest `Γ` argument displacement this checker will expand symbolically.
const MAX_SYMBOLIC_DISPLACEMENT: i64 = 32;

/// The grid and window one verification runs over.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CheckOptions {
    /// Integer sample values for every variable except the summation variable.
    /// A variable absent from this map contributes no samples, which makes the
    /// concrete layers decline.
    pub samples: BTreeMap<String, Vec<i64>>,
    /// The inclusive `k` window scanned. It must strictly contain the support of
    /// `F(n+j, ·)` for every sampled `n` and every `j`.
    pub window: (i64, i64),
    /// Minimum successful ratio comparisons demanded before the ratio layer
    /// counts as confirmed rather than merely un-refuted.
    pub min_ratio_samples: usize,
    /// Minimum integer `(n, k)` points at which the **pointwise telescoping
    /// identity** must actually be confirmed.
    ///
    /// This is the demand the checker was missing. `confirm_telescoping`
    /// counts a point where `Q` vanishes as a pole and `continue`s past the
    /// pointwise comparison, so a window can be arranged in which the identity
    /// tying `G` to `F` is never once checked -- and the verdict was still
    /// `Verified`, because only the ratio layer and the summed recurrence
    /// carried demands. The committed artifacts confirm between 60 and 260
    /// points against 0 to 40 poles, so this floor is well inside what real
    /// certificates achieve.
    ///
    /// Zero is not "no floor": it is refused outright, because options that
    /// demand nothing of this layer describe a verification that need not run
    /// it.
    pub min_pointwise_samples: usize,
}

impl CheckOptions {
    /// A grid over one shift variable `shift_var` taking the values `points`,
    /// scanning `k` across `window`.
    #[must_use]
    pub fn over(shift_var: &str, points: &[i64], window: (i64, i64)) -> CheckOptions {
        let mut samples = BTreeMap::new();
        samples.insert(shift_var.to_owned(), points.to_vec());
        CheckOptions {
            samples,
            window,
            min_ratio_samples: 8,
            min_pointwise_samples: 8,
        }
    }

    /// The same options with sample values added for a further variable.
    #[must_use]
    pub fn with(mut self, var: &str, points: &[i64]) -> CheckOptions {
        self.samples.insert(var.to_owned(), points.to_vec());
        self
    }
}

/// What a passing verification actually confirmed, in counts rather than
/// adjectives.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct CheckReport {
    /// Successful concrete confirmations of a shift ratio against factorials.
    pub ratio_samples: usize,
    /// Integer `(n, k)` points at which the pointwise telescoping identity was
    /// confirmed in exact bignum arithmetic.
    pub pointwise_samples: usize,
    /// Integer points inside the window where the certificate denominator `Q`
    /// vanishes, so `G` is not directly evaluable there.
    pub certificate_poles_in_window: usize,
    /// Sampled shift-variable values at which the summed recurrence was
    /// confirmed by exact finite summation.
    pub recurrence_samples: usize,
}

/// The outcome of an independent verification.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Verdict {
    /// Every layer passed. The counts say how much was actually exercised.
    Verified(CheckReport),
    /// At least one layer failed or could not be run. Each reason is recorded;
    /// nothing is claimed about the identity.
    Rejected(Vec<String>),
}

impl Verdict {
    /// Whether this verdict is [`Verdict::Verified`].
    #[must_use]
    pub fn is_verified(&self) -> bool {
        matches!(self, Verdict::Verified(_))
    }
}

/// Verify a creative-telescoping certificate from first principles.
#[must_use]
pub fn check_certificate(certificate: &TelescopingCertificate, options: &CheckOptions) -> Verdict {
    let mut reasons: Vec<String> = Vec::new();
    let mut report = CheckReport::default();

    if certificate.recurrence.is_empty() {
        reasons.push("the recurrence is empty".to_owned());
    }
    if certificate.recurrence.iter().all(MvPoly::is_zero) {
        reasons.push("every recurrence coefficient is zero".to_owned());
    }
    if certificate.certificate_denominator.is_zero() {
        reasons.push("the certificate denominator is zero".to_owned());
    }
    // A zero floor is refused HERE, at the options, rather than by catching its
    // consequence downstream. The consequence -- zero pointwise confirmations
    // with every other layer green -- is not reachable in this design, because
    // the edge-vanishing check forces the window to contain the support and the
    // ratio layer then confirms over that same window. A guard on an
    // unreachable state is a guard no fixture can kill, which is the defect
    // this checker is being repaired for.
    if options.min_pointwise_samples == 0 {
        reasons.push(
            "the options demand no pointwise telescoping confirmation, so the layer \
             tying G to F would not have to run at all"
                .to_owned(),
        );
    }
    if certificate
        .recurrence
        .iter()
        .any(|coefficient| coefficient.variables().contains(&certificate.sum_var))
    {
        reasons.push(format!(
            "a recurrence coefficient mentions the summation variable `{}`",
            certificate.sum_var
        ));
    }
    if !reasons.is_empty() {
        return Verdict::Rejected(reasons);
    }

    match symbolic_identity_holds(certificate) {
        Ok(true) => {}
        Ok(false) => {
            reasons.push("the certificate identity is not zero as a rational function".to_owned());
        }
        Err(reason) => reasons.push(reason),
    }

    match confirm_ratios(certificate, options) {
        Ok(count) => {
            report.ratio_samples = count;
            if count < options.min_ratio_samples {
                reasons.push(format!(
                    "only {count} shift-ratio point(s) confirmed against exact factorials, {} demanded",
                    options.min_ratio_samples
                ));
            }
        }
        Err(reason) => reasons.push(reason),
    }

    match confirm_telescoping(certificate, options) {
        Ok((pointwise, poles, recurrences)) => {
            report.pointwise_samples = pointwise;
            report.certificate_poles_in_window = poles;
            report.recurrence_samples = recurrences;
            if recurrences == 0 {
                reasons.push("no shift-variable sample confirmed the summed recurrence".to_owned());
            }
            // The pointwise layer is the one that ties `G` to `F`, and it is
            // the one a certificate pole silently skips.
            if pointwise < options.min_pointwise_samples {
                reasons.push(format!(
                    "only {pointwise} pointwise telescoping confirmation(s), {} demanded \
                     ({poles} point(s) skipped as certificate poles)",
                    options.min_pointwise_samples
                ));
            }
        }
        Err(reason) => reasons.push(reason),
    }

    if reasons.is_empty() {
        Verdict::Verified(report)
    } else {
        Verdict::Rejected(reasons)
    }
}

// ---------------------------------------------------------------------------
// Layer 2: the rational identity, by this module's own route.
// ---------------------------------------------------------------------------

/// `Σ_j a_j·S_j − R(k+1)·r + R ≡ 0` in `ℚ(vars)`.
///
/// Accumulated as ordinary fractions — `p/q + r/s = (ps+rq)/(qs)` — and compared
/// by one cross-multiplication. No lcm, no linear system, no monomial ordering.
fn symbolic_identity_holds(certificate: &TelescopingCertificate) -> Result<bool, String> {
    let current = ratio_of(&certificate.term, &certificate.sum_var, 1)
        .ok_or_else(|| "the summation shift ratio is not computable".to_owned())?;
    let mut left = (MvPoly::zero(), MvPoly::constant(Rational::integer(1)));
    for (offset, coefficient) in certificate.recurrence.iter().enumerate() {
        let outer = ratio_of(
            &certificate.term,
            &certificate.shift_var,
            i64::try_from(offset).map_err(|_| "recurrence order out of range".to_owned())?,
        )
        .ok_or_else(|| format!("shift ratio at offset {offset} is not computable"))?;
        let scaled = (
            coefficient
                .mul(&outer.0)
                .ok_or_else(|| "overflow scaling a shift ratio".to_owned())?,
            outer.1,
        );
        left = add_fractions(&left, &scaled)
            .ok_or_else(|| "overflow summing the left side".to_owned())?;
    }

    let advanced = substitute_shift(&certificate.certificate_numerator, &certificate.sum_var, 1)
        .ok_or_else(|| "overflow shifting the certificate numerator".to_owned())?;
    let advanced_denominator = substitute_shift(
        &certificate.certificate_denominator,
        &certificate.sum_var,
        1,
    )
    .ok_or_else(|| "overflow shifting the certificate denominator".to_owned())?;
    if advanced_denominator.is_zero() {
        return Err("the shifted certificate denominator is zero".to_owned());
    }
    let forward = multiply_fractions(&(advanced, advanced_denominator), &current)
        .ok_or_else(|| "overflow forming R(k+1)·r".to_owned())?;
    let backward = (
        certificate.certificate_numerator.clone(),
        certificate.certificate_denominator.clone(),
    );
    let right = subtract_fractions(&forward, &backward)
        .ok_or_else(|| "overflow forming the right side".to_owned())?;

    let cross_left = left
        .0
        .mul(&right.1)
        .ok_or_else(|| "overflow cross-multiplying".to_owned())?;
    let cross_right = right
        .0
        .mul(&left.1)
        .ok_or_else(|| "overflow cross-multiplying".to_owned())?;
    Ok(cross_left == cross_right)
}

/// `(p/q) + (r/s)`, reduced.
fn add_fractions(left: &(MvPoly, MvPoly), right: &(MvPoly, MvPoly)) -> Option<(MvPoly, MvPoly)> {
    combine(left, right, false)
}

/// `(p/q) − (r/s)`, reduced.
fn subtract_fractions(
    left: &(MvPoly, MvPoly),
    right: &(MvPoly, MvPoly),
) -> Option<(MvPoly, MvPoly)> {
    combine(left, right, true)
}

/// `(p/q) ± (r/s)`, reduced.
///
/// The cross-multiplied form `(ps ± rq)/(qs)` is correct but squares the
/// denominator's size at every step, and a `Σ_j` over a third-order recurrence
/// reaches the point where the reducing GCD overflows `i128`. So when one
/// denominator already divides the other — which is exactly what happens for the
/// shift ratios of a hypergeometric term, whose denominators form a chain — the
/// smaller side is scaled up instead. Same value, same route, no lcm machinery:
/// only the sizes change.
fn combine(
    left: &(MvPoly, MvPoly),
    right: &(MvPoly, MvPoly),
    subtract: bool,
) -> Option<(MvPoly, MvPoly)> {
    let signed = |first: &MvPoly, second: &MvPoly| -> Option<MvPoly> {
        if subtract {
            first.sub(second)
        } else {
            first.add(second)
        }
    };
    if left.1 == right.1 {
        return Some(reduce(signed(&left.0, &right.0)?, left.1.clone()));
    }
    if let Some(quotient) = right.1.exact_div(&left.1) {
        return Some(reduce(
            signed(&left.0.mul(&quotient)?, &right.0)?,
            right.1.clone(),
        ));
    }
    if let Some(quotient) = left.1.exact_div(&right.1) {
        return Some(reduce(
            signed(&left.0, &right.0.mul(&quotient)?)?,
            left.1.clone(),
        ));
    }
    let numerator = signed(&left.0.mul(&right.1)?, &right.0.mul(&left.1)?)?;
    Some(reduce(numerator, left.1.mul(&right.1)?))
}

/// `(p/q)·(r/s)`, reduced.
fn multiply_fractions(
    left: &(MvPoly, MvPoly),
    right: &(MvPoly, MvPoly),
) -> Option<(MvPoly, MvPoly)> {
    Some(reduce(left.0.mul(&right.0)?, left.1.mul(&right.1)?))
}

/// Divide out a common polynomial factor; value-preserving.
///
/// Reduction is an optimization, not a check: an overflowing GCD leaves the pair
/// unreduced rather than failing, because the verdict is decided by an exact
/// cross-multiplication either way. A larger unreduced pair can still overflow
/// *that*, which rejects — it never accepts.
fn reduce(numerator: MvPoly, denominator: MvPoly) -> (MvPoly, MvPoly) {
    if numerator.is_zero() {
        return (MvPoly::zero(), MvPoly::constant(Rational::integer(1)));
    }
    let Some(common) = numerator.gcd(&denominator) else {
        return (numerator, denominator);
    };
    if common.total_degree() == 0 {
        return (numerator, denominator);
    }
    match (numerator.exact_div(&common), denominator.exact_div(&common)) {
        (Some(top), Some(bottom)) => (top, bottom),
        _ => (numerator, denominator),
    }
}

/// This module's own derivation of `term(var → var + delta) / term`, as
/// `(numerator, denominator)`.
///
/// Written as two explicit factor lists multiplied at the end, from the single
/// fact `Γ(x+1) = x·Γ(x)`; deliberately not the producer's construction.
fn ratio_of(term: &HyperTerm, var: &str, delta: i64) -> Option<(MvPoly, MvPoly)> {
    let mut up: Vec<MvPoly> = Vec::new();
    let mut down: Vec<MvPoly> = Vec::new();
    for factor in term.factors() {
        match factor {
            Factor::Gamma { form, exponent } => {
                let moved = form.coefficient(var).checked_mul(delta)?;
                if moved.abs() > MAX_SYMBOLIC_DISPLACEMENT {
                    return None;
                }
                let base = form.to_poly()?;
                // Γ(L+d)/Γ(L) is the product of the d arguments crossed going up,
                // or the reciprocal of the |d| crossed going down.
                let mut crossed: Vec<MvPoly> = Vec::new();
                for step in 1..=moved.abs() {
                    let offset = if moved > 0 { step - 1 } else { -step };
                    crossed
                        .push(base.add(&MvPoly::constant(Rational::integer(i128::from(offset))))?);
                }
                let ascending = moved > 0;
                for polynomial in crossed {
                    let repeats = exponent.unsigned_abs();
                    let raised = polynomial.pow(repeats)?;
                    if ascending == (*exponent > 0) {
                        up.push(raised);
                    } else {
                        down.push(raised);
                    }
                }
            }
            Factor::Power { base, form } => {
                let moved = form.coefficient(var).checked_mul(delta)?;
                let value = concrete_power(*base, moved)?;
                up.push(MvPoly::constant(value));
            }
            Factor::Poly { poly, exponent } => {
                let moved = substitute_shift(poly, var, delta)?;
                let repeats = exponent.unsigned_abs();
                let (top, bottom) = (moved.pow(repeats)?, poly.pow(repeats)?);
                if *exponent >= 0 {
                    up.push(top);
                    down.push(bottom);
                } else {
                    up.push(bottom);
                    down.push(top);
                }
            }
        }
    }
    let fold = |parts: Vec<MvPoly>| -> Option<MvPoly> {
        parts
            .into_iter()
            .try_fold(MvPoly::constant(Rational::integer(1)), |acc, part| {
                acc.mul(&part)
            })
    };
    Some(reduce(fold(up)?, fold(down)?))
}

/// `poly(var → var + delta)`, by expanding each monomial's `var` power.
fn substitute_shift(poly: &MvPoly, var: &str, delta: i64) -> Option<MvPoly> {
    if delta == 0 {
        return Some(poly.clone());
    }
    let replacement =
        MvPoly::var(var).add(&MvPoly::constant(Rational::integer(i128::from(delta))))?;
    let mut total = MvPoly::zero();
    for (mono, coefficient) in poly.terms() {
        let mut product = MvPoly::constant(*coefficient);
        for (name, power) in mono.powers() {
            let piece = if name == var {
                replacement.pow(power)?
            } else {
                MvPoly::var(name).pow(power)?
            };
            product = product.mul(&piece)?;
        }
        total = total.add(&product)?;
    }
    Some(total)
}

/// `base^exponent` for an integer exponent of either sign.
fn concrete_power(base: Rational, exponent: i64) -> Option<Rational> {
    if exponent.abs() > MAX_CONCRETE_POWER {
        return None;
    }
    let mut value = Rational::integer(1);
    for _ in 0..exponent.abs() {
        value = value.checked_mul(base)?;
    }
    if exponent < 0 {
        Rational::integer(1).checked_div(value)
    } else {
        Some(value)
    }
}

// ---------------------------------------------------------------------------
// Layer 3: the ratios, against real factorials.
// ---------------------------------------------------------------------------

/// Confirm every shift ratio used by the identity against direct exact
/// evaluation of the term. Returns the number of successful comparisons.
fn confirm_ratios(
    certificate: &TelescopingCertificate,
    options: &CheckOptions,
) -> Result<usize, String> {
    let mut shifts: Vec<(String, i64)> = vec![(certificate.sum_var.clone(), 1)];
    for offset in 1..certificate.recurrence.len() {
        shifts.push((
            certificate.shift_var.clone(),
            i64::try_from(offset).map_err(|_| "recurrence order out of range".to_owned())?,
        ));
    }
    let grid = full_grid(certificate, options)?;
    let mut confirmed = 0usize;
    for (var, delta) in &shifts {
        let (numerator, denominator) = ratio_of(&certificate.term, var, *delta)
            .ok_or_else(|| format!("shift ratio in `{var}` by {delta} is not computable"))?;
        for point in &grid {
            let Some(here) = evaluate_term(&certificate.term, point) else {
                continue;
            };
            if here.is_zero() {
                continue;
            }
            let mut moved = point.clone();
            let slot = moved.entry(var.clone()).or_insert(0);
            let Some(next) = slot.checked_add(*delta) else {
                continue;
            };
            *slot = next;
            let Some(there) = evaluate_term(&certificate.term, &moved) else {
                continue;
            };
            let (Some(top), Some(bottom)) = (
                evaluate_poly(&numerator, point),
                evaluate_poly(&denominator, point),
            ) else {
                continue;
            };
            if bottom.is_zero() {
                continue;
            }
            if top * here != bottom * there {
                return Err(format!(
                    "shift ratio in `{var}` by {delta} disagrees with exact evaluation at {}",
                    render_point(point)
                ));
            }
            confirmed += 1;
        }
    }
    Ok(confirmed)
}

// ---------------------------------------------------------------------------
// Layers 4-6: telescoping, boundary, and the summed recurrence.
// ---------------------------------------------------------------------------

/// Returns `(pointwise confirmations, poles inside the window, recurrence
/// confirmations)`.
#[allow(clippy::too_many_lines)]
fn confirm_telescoping(
    certificate: &TelescopingCertificate,
    options: &CheckOptions,
) -> Result<(usize, usize, usize), String> {
    let (low, high) = options.window;
    if low >= high {
        return Err("the summation window is empty".to_owned());
    }
    let parameter_grid = parameter_grid(certificate, options)?;
    let mut pointwise = 0usize;
    let mut poles = 0usize;
    let mut recurrences = 0usize;

    for base in &parameter_grid {
        // The certificate must vanish at both ends, or the telescoped sum is not
        // the zero it is claimed to be.
        for edge in [low, high + 1] {
            let point = with_sum_value(base, &certificate.sum_var, edge);
            let Some(value) = evaluate_certificate_product(certificate, &point) else {
                return Err(format!(
                    "G is not evaluable at the window edge {}",
                    render_point(&point)
                ));
            };
            if !value.is_zero() {
                return Err(format!(
                    "G does not vanish at the window edge {}; the window does not contain the support",
                    render_point(&point)
                ));
            }
        }

        let mut totals: Vec<BigRational> = vec![BigRational::zero(); certificate.recurrence.len()];
        for index in low..=high {
            let point = with_sum_value(base, &certificate.sum_var, index);
            // Σ_j a_j(n)·F(n+j,k) accumulated per offset, and checked pointwise
            // against G(n,k+1) − G(n,k).
            let mut combination = BigRational::zero();
            for (offset, coefficient) in certificate.recurrence.iter().enumerate() {
                let shifted = shift_point(&point, &certificate.shift_var, offset)?;
                let Some(value) = evaluate_term(&certificate.term, &shifted) else {
                    return Err(format!("F is not evaluable at {}", render_point(&shifted)));
                };
                let Some(weight) = evaluate_poly(coefficient, base) else {
                    return Err("a recurrence coefficient is not evaluable".to_owned());
                };
                totals[offset] += value.clone();
                combination += weight * value;
            }
            let next = with_sum_value(base, &certificate.sum_var, index + 1);
            let here_denominator = evaluate_poly(&certificate.certificate_denominator, &point);
            let next_denominator = evaluate_poly(&certificate.certificate_denominator, &next);
            if here_denominator.as_ref().is_none_or(BigRational::is_zero)
                || next_denominator.as_ref().is_none_or(BigRational::is_zero)
            {
                poles += 1;
                continue;
            }
            let (Some(here), Some(there)) = (
                evaluate_certificate_product(certificate, &point),
                evaluate_certificate_product(certificate, &next),
            ) else {
                poles += 1;
                continue;
            };
            if combination != there - here {
                return Err(format!(
                    "the pointwise telescoping identity fails at {}",
                    render_point(&point)
                ));
            }
            pointwise += 1;
        }

        // Σ_j a_j(n)·S(n+j) must be exactly zero.
        let mut total = BigRational::zero();
        for (offset, coefficient) in certificate.recurrence.iter().enumerate() {
            let Some(weight) = evaluate_poly(coefficient, base) else {
                return Err("a recurrence coefficient is not evaluable".to_owned());
            };
            total += weight * totals[offset].clone();
        }
        if !total.is_zero() {
            return Err(format!(
                "the summed recurrence is not zero at {}",
                render_point(base)
            ));
        }
        recurrences += 1;
    }
    Ok((pointwise, poles, recurrences))
}

/// `G(point) = R(point)·F(point)`, or `None` when either part is undefined.
fn evaluate_certificate_product(
    certificate: &TelescopingCertificate,
    point: &BTreeMap<String, i64>,
) -> Option<BigRational> {
    let value = evaluate_term(&certificate.term, point)?;
    let numerator = evaluate_poly(&certificate.certificate_numerator, point)?;
    let denominator = evaluate_poly(&certificate.certificate_denominator, point)?;
    if denominator.is_zero() {
        return None;
    }
    Some(numerator / denominator * value)
}

/// `point` with the shift variable advanced by `offset`.
fn shift_point(
    point: &BTreeMap<String, i64>,
    shift_var: &str,
    offset: usize,
) -> Result<BTreeMap<String, i64>, String> {
    let mut moved = point.clone();
    let slot = moved.entry(shift_var.to_owned()).or_insert(0);
    *slot = slot
        .checked_add(i64::try_from(offset).map_err(|_| "offset out of range".to_owned())?)
        .ok_or_else(|| "shift-variable overflow".to_owned())?;
    Ok(moved)
}

/// `base` extended with a value for the summation variable.
fn with_sum_value(
    base: &BTreeMap<String, i64>,
    sum_var: &str,
    value: i64,
) -> BTreeMap<String, i64> {
    let mut point = base.clone();
    point.insert(sum_var.to_owned(), value);
    point
}

/// The Cartesian product of the sample values for every variable except the
/// summation variable.
fn parameter_grid(
    certificate: &TelescopingCertificate,
    options: &CheckOptions,
) -> Result<Vec<BTreeMap<String, i64>>, String> {
    let mut names: BTreeSet<String> = certificate.term.variables();
    names.remove(&certificate.sum_var);
    build_grid(&names, options)
}

/// The Cartesian product over every variable, the summation variable included
/// (its samples come from the window).
fn full_grid(
    certificate: &TelescopingCertificate,
    options: &CheckOptions,
) -> Result<Vec<BTreeMap<String, i64>>, String> {
    let mut names: BTreeSet<String> = certificate.term.variables();
    names.remove(&certificate.sum_var);
    let mut grid = build_grid(&names, options)?;
    let (low, high) = options.window;
    let mut widened = Vec::new();
    for point in grid.drain(..) {
        for index in low..=high {
            widened.push(with_sum_value(&point, &certificate.sum_var, index));
        }
    }
    Ok(widened)
}

/// The Cartesian product of `options.samples` restricted to `names`.
fn build_grid(
    names: &BTreeSet<String>,
    options: &CheckOptions,
) -> Result<Vec<BTreeMap<String, i64>>, String> {
    let mut grid: Vec<BTreeMap<String, i64>> = vec![BTreeMap::new()];
    for name in names {
        let Some(values) = options.samples.get(name) else {
            return Err(format!("no sample values supplied for `{name}`"));
        };
        if values.is_empty() {
            return Err(format!("the sample list for `{name}` is empty"));
        }
        let mut widened = Vec::with_capacity(grid.len() * values.len());
        for point in &grid {
            for value in values {
                let mut extended = point.clone();
                extended.insert(name.clone(), *value);
                widened.push(extended);
            }
        }
        grid = widened;
    }
    Ok(grid)
}

/// A point rendered for a rejection message, in a deterministic order.
fn render_point(point: &BTreeMap<String, i64>) -> String {
    let parts: Vec<String> = point
        .iter()
        .map(|(name, value)| format!("{name}={value}"))
        .collect();
    format!("({})", parts.join(", "))
}

// ---------------------------------------------------------------------------
// Exact concrete evaluation: real factorials, no symbolic algebra at all.
// ---------------------------------------------------------------------------

/// The exact value of a hypergeometric term at an integer point.
///
/// A `Γ` at a non-positive integer is a pole: in a denominator it makes the term
/// zero (this is what gives `C(n,k) = 0` outside `0 ≤ k ≤ n` for free), in a
/// numerator it makes the term undefined. A term that is simultaneously zero and
/// undefined is reported undefined rather than guessed.
#[must_use]
pub fn evaluate_term(term: &HyperTerm, point: &BTreeMap<String, i64>) -> Option<BigRational> {
    let mut value = BigRational::one();
    let mut zeros = 0u32;
    let mut poles = 0u32;
    for factor in term.factors() {
        match factor {
            Factor::Gamma { form, exponent } => {
                let argument = form.evaluate(point)?;
                if argument <= 0 {
                    if *exponent == 0 {
                        continue;
                    }
                    if *exponent < 0 {
                        zeros += 1;
                    } else {
                        poles += 1;
                    }
                    continue;
                }
                if argument > MAX_CONCRETE_GAMMA {
                    return None;
                }
                let factorial = factorial_big(argument - 1);
                value *= integer_power(&BigRational::from_integer(factorial), *exponent)?;
            }
            Factor::Power { base, form } => {
                let exponent = form.evaluate(point)?;
                if exponent.abs() > MAX_CONCRETE_POWER {
                    return None;
                }
                let base = BigRational::new(
                    BigInt::from(base.numerator()),
                    BigInt::from(base.denominator()),
                );
                if base.is_zero() {
                    if exponent > 0 {
                        zeros += 1;
                    } else if exponent < 0 {
                        poles += 1;
                    }
                    continue;
                }
                value *= big_power(&base, exponent)?;
            }
            Factor::Poly { poly, exponent } => {
                let evaluated = evaluate_poly(poly, point)?;
                if evaluated.is_zero() {
                    if *exponent == 0 {
                        continue;
                    }
                    if *exponent > 0 {
                        zeros += 1;
                    } else {
                        poles += 1;
                    }
                    continue;
                }
                value *= integer_power(&evaluated, *exponent)?;
            }
        }
    }
    if poles > 0 {
        return None;
    }
    if zeros > 0 {
        return Some(BigRational::zero());
    }
    Some(value)
}

/// A polynomial's exact value at an integer point, in bignum rationals.
#[must_use]
pub fn evaluate_poly(poly: &MvPoly, point: &BTreeMap<String, i64>) -> Option<BigRational> {
    let mut total = BigRational::zero();
    for (mono, coefficient) in poly.terms() {
        let mut term = BigRational::new(
            BigInt::from(coefficient.numerator()),
            BigInt::from(coefficient.denominator()),
        );
        for (name, power) in mono.powers() {
            let base = BigRational::from_integer(BigInt::from(*point.get(name)?));
            for _ in 0..power {
                term *= base.clone();
            }
        }
        total += term;
    }
    Some(total)
}

/// `value^exponent` for a signed integer exponent; `None` on a zero base with a
/// negative exponent.
fn integer_power(value: &BigRational, exponent: i32) -> Option<BigRational> {
    big_power(value, i64::from(exponent))
}

/// `value^exponent` for a signed integer exponent.
fn big_power(value: &BigRational, exponent: i64) -> Option<BigRational> {
    if exponent < 0 && value.is_zero() {
        return None;
    }
    let mut result = BigRational::one();
    for _ in 0..exponent.abs() {
        result *= value.clone();
    }
    if exponent < 0 {
        Some(BigRational::one() / result)
    } else {
        Some(result)
    }
}

/// `n!` as a big integer.
fn factorial_big(n: i64) -> BigInt {
    let mut value = BigInt::one();
    for factor in 1..=n {
        value *= BigInt::from(factor);
    }
    value
}

// ---------------------------------------------------------------------------
// Symbolic evaluation: integers for some variables, symbols for the rest.
// ---------------------------------------------------------------------------

/// The exact value of a hypergeometric term at a point where only *some*
/// variables are integers.
///
/// It is a rational coefficient times a product of `Γ` powers whose arguments
/// still mention symbolic parameters. The interesting case is the one where
/// `gammas` is **empty**: every symbolic `Γ` has cancelled and the value is an
/// honest rational, valid for every value of the parameters. That is what makes
/// a base case at symbolic `m` and `n` decidable rather than sampled.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SymbolicValue {
    coefficient: BigRational,
    gammas: BTreeMap<LinearForm, i32>,
}

impl SymbolicValue {
    /// The zero value.
    #[must_use]
    pub fn zero() -> SymbolicValue {
        SymbolicValue {
            coefficient: BigRational::zero(),
            gammas: BTreeMap::new(),
        }
    }

    /// Whether this value is exactly zero.
    #[must_use]
    pub fn is_zero(&self) -> bool {
        self.coefficient.is_zero()
    }

    /// The rational coefficient, meaningful on its own only when
    /// [`SymbolicValue::is_rational`] holds.
    #[must_use]
    pub fn coefficient(&self) -> &BigRational {
        &self.coefficient
    }

    /// Whether every symbolic `Γ` power cancelled, so this value is a plain
    /// rational number for **all** values of the remaining parameters.
    #[must_use]
    pub fn is_rational(&self) -> bool {
        self.gammas.is_empty()
    }

    /// The number of uncancelled symbolic `Γ` powers.
    #[must_use]
    pub fn gamma_count(&self) -> usize {
        self.gammas.len()
    }

    /// `self + other`, when the two share the same uncancelled `Γ` part (a zero
    /// value shares every part). `None` otherwise: two different `Γ` monomials
    /// have no common rational form here.
    #[must_use]
    pub fn checked_add(&self, other: &SymbolicValue) -> Option<SymbolicValue> {
        if self.is_zero() {
            return Some(other.clone());
        }
        if other.is_zero() {
            return Some(self.clone());
        }
        if self.gammas != other.gammas {
            return None;
        }
        Some(SymbolicValue {
            coefficient: self.coefficient.clone() + other.coefficient.clone(),
            gammas: self.gammas.clone(),
        })
    }
}

/// The exact value of `term` at a point assigning integers to *some* variables.
///
/// Every `Γ` whose argument becomes a concrete integer is expanded to a real
/// factorial (or recognised as a zero/pole exactly as
/// [`evaluate_term`] does); every `Γ` whose argument still mentions a parameter
/// is accumulated by argument, so that `Γ(m+1)·Γ(m+1)⁻¹` cancels *symbolically*.
///
/// Returns `None` when the value cannot be decided: a `Γ` at a numerator pole, a
/// symbolic exponent on a `Power` factor, or a `Poly` factor that is still
/// symbolic.
///
/// # The assumption this makes, named
///
/// An uncancelled symbolic `Γ` power (see [`SymbolicValue::gamma_count`]) is
/// treated as a nonzero finite value. For a parameter ranging over the integers
/// that is only true away from the poles, so a nonzero count carries the standing
/// side condition that the symbolic arguments avoid the non-positive integers.
/// When the count is zero —
/// the only case the closed-form check accepts — the powers have cancelled
/// pairwise and the value is unconditional except for that same non-pole
/// proviso, which is exactly the axiom
/// `cas.symbolic-gamma-arguments-avoid-poles`.
#[must_use]
pub fn evaluate_term_symbolic(
    term: &HyperTerm,
    point: &BTreeMap<String, i64>,
) -> Option<SymbolicValue> {
    let mut coefficient = BigRational::one();
    let mut gammas: BTreeMap<LinearForm, i32> = BTreeMap::new();
    let mut zeros = 0u32;
    let mut poles = 0u32;
    for factor in term.factors() {
        match factor {
            Factor::Gamma { form, exponent } => {
                if *exponent == 0 {
                    continue;
                }
                let reduced = form.substitute(point)?;
                if !reduced.is_constant() {
                    let slot = gammas.entry(reduced).or_insert(0);
                    *slot = slot.checked_add(*exponent)?;
                    continue;
                }
                let argument = reduced.constant();
                if argument <= 0 {
                    if *exponent < 0 {
                        zeros += 1;
                    } else {
                        poles += 1;
                    }
                    continue;
                }
                if argument > MAX_CONCRETE_GAMMA {
                    return None;
                }
                let factorial = factorial_big(argument - 1);
                coefficient *= integer_power(&BigRational::from_integer(factorial), *exponent)?;
            }
            Factor::Power { base, form } => {
                let reduced = form.substitute(point)?;
                if !reduced.is_constant() {
                    return None;
                }
                let exponent = reduced.constant();
                if exponent.abs() > MAX_CONCRETE_POWER {
                    return None;
                }
                let base = BigRational::new(
                    BigInt::from(base.numerator()),
                    BigInt::from(base.denominator()),
                );
                if base.is_zero() {
                    if exponent > 0 {
                        zeros += 1;
                    } else if exponent < 0 {
                        poles += 1;
                    }
                    continue;
                }
                coefficient *= big_power(&base, exponent)?;
            }
            Factor::Poly { poly, exponent } => {
                if *exponent == 0 {
                    continue;
                }
                let reduced = substitute_integers(poly, point)?;
                if !reduced.variables().is_empty() {
                    return None;
                }
                let value = evaluate_poly(&reduced, &BTreeMap::new())?;
                if value.is_zero() {
                    if *exponent > 0 {
                        zeros += 1;
                    } else {
                        poles += 1;
                    }
                    continue;
                }
                coefficient *= integer_power(&value, *exponent)?;
            }
        }
    }
    gammas.retain(|_, exponent| *exponent != 0);
    if poles > 0 {
        return None;
    }
    if zeros > 0 {
        return Some(SymbolicValue::zero());
    }
    Some(SymbolicValue {
        coefficient,
        gammas,
    })
}

/// `poly` with the assigned variables replaced by their integer values, leaving
/// the rest symbolic.
fn substitute_integers(poly: &MvPoly, point: &BTreeMap<String, i64>) -> Option<MvPoly> {
    let mut total = MvPoly::zero();
    for (mono, coefficient) in poly.terms() {
        let mut product = MvPoly::constant(*coefficient);
        for (name, power) in mono.powers() {
            let piece = match point.get(name) {
                Some(value) => {
                    MvPoly::constant(Rational::integer(i128::from(*value))).pow(power)?
                }
                None => MvPoly::var(name).pow(power)?,
            };
            product = product.mul(&piece)?;
        }
        total = total.add(&product)?;
    }
    Some(total)
}

/// The `k` interval outside which `term` is **forced** to vanish at `point`, read
/// off the `Γ` factors whose argument became parameter-free.
///
/// A `Γ` in the denominator at a non-positive integer makes the term zero, so
/// each such factor `c·k + d` contributes the constraint `c·k + d ≥ 1`. When the
/// constraints bound `k` from both sides the support is a finite explicit set and
/// the sum over all integers is a finite sum — which is exactly the situation a
/// base case needs.
fn forced_support(
    term: &HyperTerm,
    point: &BTreeMap<String, i64>,
    sum_var: &str,
) -> Option<(i64, i64)> {
    let mut low: Option<i64> = None;
    let mut high: Option<i64> = None;
    for factor in term.factors() {
        let Factor::Gamma { form, exponent } = factor else {
            continue;
        };
        if *exponent >= 0 {
            continue;
        }
        let reduced = form.substitute(point)?;
        let slope = reduced.coefficient(sum_var);
        if slope == 0 || reduced.variables().len() != 1 {
            continue;
        }
        // c·k + d ≥ 1.
        let offset = reduced.constant();
        if slope > 0 {
            let bound =
                (1 - offset).div_euclid(slope) + i64::from((1 - offset).rem_euclid(slope) != 0);
            low = Some(low.map_or(bound, |current: i64| current.max(bound)));
        } else {
            let bound = (offset - 1).div_euclid(-slope);
            high = Some(high.map_or(bound, |current: i64| current.min(bound)));
        }
    }
    match (low, high) {
        (Some(low), Some(high)) if low <= high => Some((low, high)),
        _ => None,
    }
}

/// The exact symbolic value of `∑_k term(point, k)`, over a window that must
/// strictly contain the forced support.
///
/// Every window point outside the forced support is *checked* to be zero rather
/// than assumed, which is the symbolic counterpart of the concrete checker's
/// boundary layer. Returns the value together with the number of points
/// confirmed zero.
///
/// # Errors
///
/// When the support is not forced finite, when the window does not strictly
/// contain it, when a summand is not symbolically evaluable, when a point outside
/// the support fails to vanish, or when two summands carry different uncancelled
/// `Γ` parts and therefore cannot be added.
pub fn symbolic_window_sum(
    term: &HyperTerm,
    point: &BTreeMap<String, i64>,
    sum_var: &str,
    window: (i64, i64),
) -> Result<(SymbolicValue, usize), String> {
    let (low, high) = window;
    if low >= high {
        return Err("the summation window is empty".to_owned());
    }
    let Some((support_low, support_high)) = forced_support(term, point, sum_var) else {
        return Err(format!(
            "the summand's support at {} is not forced finite by parameter-free Γ factors",
            render_point(point)
        ));
    };
    if support_low <= low || support_high >= high {
        return Err(format!(
            "the window [{low}, {high}] does not strictly contain the forced support [{support_low}, {support_high}]"
        ));
    }
    let mut total = SymbolicValue::zero();
    let mut confirmed_zero = 0usize;
    for index in low..=high {
        let mut here = point.clone();
        here.insert(sum_var.to_owned(), index);
        let Some(value) = evaluate_term_symbolic(term, &here) else {
            return Err(format!(
                "the summand is not symbolically evaluable at {}",
                render_point(&here)
            ));
        };
        if index < support_low || index > support_high {
            if !value.is_zero() {
                return Err(format!(
                    "the summand does not vanish outside its forced support at {}",
                    render_point(&here)
                ));
            }
            confirmed_zero += 1;
            continue;
        }
        total = total.checked_add(&value).ok_or_else(|| {
            format!(
                "summands at {} carry different uncancelled Γ parts",
                render_point(&here)
            )
        })?;
    }
    Ok((total, confirmed_zero))
}

// ---------------------------------------------------------------------------
// Turning a recurrence into a closed form.
// ---------------------------------------------------------------------------

/// The evidence that a verified recurrence pins `S(n)` to a claimed closed form.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ClosedFormReport {
    /// The base index from which the identity is claimed.
    pub base: i64,
    /// The base cases checked by exact finite summation.
    pub base_cases: usize,
    /// The integers `≥ base` at which the leading recurrence coefficient
    /// vanishes. A nonempty list breaks the induction and rejects the claim.
    pub leading_zeros: Vec<i64>,
}

/// Check that a claimed hypergeometric closed form satisfies the same recurrence
/// and agrees with the sum on enough base cases to force equality for all
/// `n ≥ base`.
///
/// Three things are established: the recurrence annihilates the closed form (a
/// rational-function identity in the closed form's own shift ratio); the sum and
/// the closed form agree on the `J` initial values the recurrence needs; and the
/// leading coefficient `a_J(n)` has no integer zero at or above `base`, so the
/// recurrence can be solved forward. Together with a verified certificate that
/// is what makes `S(n) = T(n)` a theorem rather than a coincidence.
///
/// # Errors
///
/// Returns every reason the claim was not established: the recurrence failing to
/// annihilate the closed form, a base case disagreeing with it, a base case that
/// is not exactly evaluable, or a leading coefficient that vanishes at an integer
/// at or above `base`, which leaves the induction unable to step forward.
pub fn check_closed_form(
    certificate: &TelescopingCertificate,
    closed_form: &HyperTerm,
    base: i64,
    options: &CheckOptions,
) -> Result<ClosedFormReport, Vec<String>> {
    let mut reasons: Vec<String> = Vec::new();
    match annihilates(certificate, closed_form) {
        Ok(true) => {}
        Ok(false) => {
            reasons.push("the recurrence does not annihilate the claimed closed form".to_owned());
        }
        Err(reason) => reasons.push(reason),
    }

    let order = certificate.order();
    let mut base_cases = 0usize;
    let (low, high) = options.window;
    for offset in 0..order.max(1) {
        let index = base + i64::try_from(offset).unwrap_or(i64::MAX);
        let mut total = BigRational::zero();
        let mut summable = true;
        for position in low..=high {
            let mut point: BTreeMap<String, i64> = BTreeMap::new();
            point.insert(certificate.shift_var.clone(), index);
            point.insert(certificate.sum_var.clone(), position);
            match evaluate_term(&certificate.term, &point) {
                Some(value) => total += value,
                None => summable = false,
            }
        }
        if !summable {
            reasons.push(format!("the sum at {index} is not exactly evaluable"));
            continue;
        }
        let mut point: BTreeMap<String, i64> = BTreeMap::new();
        point.insert(certificate.shift_var.clone(), index);
        let Some(claimed) = evaluate_term(closed_form, &point) else {
            reasons.push(format!("the closed form at {index} is not evaluable"));
            continue;
        };
        if total != claimed {
            reasons.push(format!("base case {index} disagrees with the closed form"));
            continue;
        }
        base_cases += 1;
    }

    let leading_zeros = match leading_integer_zeros(certificate, base) {
        Ok(zeros) => zeros,
        Err(reason) => {
            reasons.push(reason);
            Vec::new()
        }
    };
    if !leading_zeros.is_empty() {
        reasons.push(format!(
            "the leading recurrence coefficient vanishes at {leading_zeros:?}, so the recurrence does not run forward"
        ));
    }

    if reasons.is_empty() {
        Ok(ClosedFormReport {
            base,
            base_cases,
            leading_zeros,
        })
    } else {
        Err(reasons)
    }
}

/// The evidence that a verified recurrence pins `S(n)` to a claimed closed form
/// **at symbolic parameters**.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SymbolicClosedFormReport {
    /// The base index from which the identity is claimed.
    pub base: i64,
    /// Base cases established at symbolic parameters by exact finite summation
    /// over a forced-finite support.
    pub base_cases: usize,
    /// The `k` interval outside which the summand at the first base index is
    /// forced to vanish.
    pub forced_support: (i64, i64),
    /// Window points confirmed — not assumed — to vanish outside that support.
    pub confirmed_zero_points: usize,
    /// The integers `≥ base` at which the leading recurrence coefficient
    /// vanishes. A nonempty list breaks the induction and rejects the claim.
    pub leading_zeros: Vec<i64>,
}

/// Check a claimed closed form against a verified certificate **without
/// specializing the remaining parameters**.
///
/// [`check_closed_form`] settles the base cases by exact summation at concrete
/// integers, which is why an identity with a symbolic parameter — Chu–Vandermonde
/// is the standard example — could only ever be filed as its recurrence. This
/// closes that gap. The base case is evaluated with only the *shift* variable
/// bound: the summation collapses to the finitely many `k` where a parameter-free
/// `Γ` in the denominator has not already forced the summand to zero, and each
/// surviving term is evaluated by cancelling symbolic `Γ` powers against each
/// other. Nothing is sampled.
///
/// Three things are established, exactly as in the concrete case: the recurrence
/// annihilates the closed form; the `J` initial values agree; and the leading
/// coefficient has no integer zero at or above `base`.
///
/// # Errors
///
/// Returns every reason the claim was not established, including the ones
/// specific to the symbolic route: a support that is not forced finite, a window
/// that does not strictly contain it, a summand or closed form that does not
/// evaluate symbolically, and a base value that is not a plain rational (some
/// symbolic `Γ` power failed to cancel, so the two sides are not comparable).
pub fn check_closed_form_symbolic(
    certificate: &TelescopingCertificate,
    closed_form: &HyperTerm,
    base: i64,
    options: &CheckOptions,
) -> Result<SymbolicClosedFormReport, Vec<String>> {
    let mut reasons: Vec<String> = Vec::new();
    match annihilates(certificate, closed_form) {
        Ok(true) => {}
        Ok(false) => {
            reasons.push("the recurrence does not annihilate the claimed closed form".to_owned());
        }
        Err(reason) => reasons.push(reason),
    }

    let order = certificate.order();
    let mut base_cases = 0usize;
    let mut support = (0i64, 0i64);
    let mut confirmed_zero_points = 0usize;
    for offset in 0..order.max(1) {
        let index = base + i64::try_from(offset).unwrap_or(i64::MAX);
        let mut point: BTreeMap<String, i64> = BTreeMap::new();
        point.insert(certificate.shift_var.clone(), index);
        if let Some(found) = forced_support(&certificate.term, &point, &certificate.sum_var)
            && offset == 0
        {
            support = found;
        }
        let summed = symbolic_window_sum(
            &certificate.term,
            &point,
            &certificate.sum_var,
            options.window,
        );
        let (total, zeros) = match summed {
            Ok(value) => value,
            Err(reason) => {
                reasons.push(reason);
                continue;
            }
        };
        confirmed_zero_points += zeros;
        let Some(claimed) = evaluate_term_symbolic(closed_form, &point) else {
            reasons.push(format!(
                "the closed form is not symbolically evaluable at {index}"
            ));
            continue;
        };
        if !total.is_rational() || !claimed.is_rational() {
            reasons.push(format!(
                "base case {index} leaves {} uncancelled Γ power(s) on the sum and {} on the closed form, so the two are not comparable as rationals",
                total.gamma_count(),
                claimed.gamma_count()
            ));
            continue;
        }
        if total != claimed {
            reasons.push(format!(
                "base case {index} disagrees with the closed form at symbolic parameters"
            ));
            continue;
        }
        base_cases += 1;
    }

    let leading_zeros = match leading_integer_zeros(certificate, base) {
        Ok(zeros) => zeros,
        Err(reason) => {
            reasons.push(reason);
            Vec::new()
        }
    };
    if !leading_zeros.is_empty() {
        reasons.push(format!(
            "the leading recurrence coefficient vanishes at {leading_zeros:?}, so the recurrence does not run forward"
        ));
    }

    if reasons.is_empty() {
        Ok(SymbolicClosedFormReport {
            base,
            base_cases,
            forced_support: support,
            confirmed_zero_points,
            leading_zeros,
        })
    } else {
        Err(reasons)
    }
}

/// `Σ_j a_j(n)·∏_{i<j} ρ(n+i) ≡ 0` where `ρ = T(n+1)/T(n)`: the recurrence
/// annihilates `T`, as an identity of rational functions.
fn annihilates(
    certificate: &TelescopingCertificate,
    closed_form: &HyperTerm,
) -> Result<bool, String> {
    let mut total = (MvPoly::zero(), MvPoly::constant(Rational::integer(1)));
    for (offset, coefficient) in certificate.recurrence.iter().enumerate() {
        let step = ratio_of(
            closed_form,
            &certificate.shift_var,
            i64::try_from(offset).map_err(|_| "recurrence order out of range".to_owned())?,
        )
        .ok_or_else(|| format!("the closed form has no computable shift ratio at {offset}"))?;
        let scaled = (
            coefficient
                .mul(&step.0)
                .ok_or_else(|| "overflow scaling the closed-form ratio".to_owned())?,
            step.1,
        );
        total = add_fractions(&total, &scaled)
            .ok_or_else(|| "overflow accumulating the annihilation check".to_owned())?;
    }
    Ok(total.0.is_zero())
}

/// Every integer `≥ base` at which the leading recurrence coefficient vanishes.
///
/// Decidable, not sampled: the coefficient is cleared to integer coefficients,
/// factors of the shift variable are stripped (each contributing the root `0`),
/// and the rational-root theorem bounds the remaining integer roots to the
/// divisors of the constant term.
fn leading_integer_zeros(
    certificate: &TelescopingCertificate,
    base: i64,
) -> Result<Vec<i64>, String> {
    let leading = certificate
        .recurrence
        .last()
        .ok_or_else(|| "the recurrence is empty".to_owned())?;
    let variables = leading.variables();
    if variables.is_empty() {
        return Ok(Vec::new());
    }
    if variables.len() > 1 || !variables.contains(&certificate.shift_var) {
        return Err(format!(
            "the leading recurrence coefficient depends on {variables:?}, so forward solvability is not decided here"
        ));
    }
    let degree = leading.degree_in(&certificate.shift_var);
    let mut coefficients: Vec<i128> = vec![0; degree as usize + 1];
    let mut denominators: i128 = 1;
    for (mono, coefficient) in leading.terms() {
        denominators = lcm_i128(denominators, coefficient.denominator())
            .ok_or_else(|| "overflow clearing denominators".to_owned())?;
        let _ = mono;
    }
    for (mono, coefficient) in leading.terms() {
        let power = mono.exponent_of(&certificate.shift_var) as usize;
        let scaled = coefficient
            .numerator()
            .checked_mul(denominators / coefficient.denominator())
            .ok_or_else(|| "overflow clearing denominators".to_owned())?;
        coefficients[power] = scaled;
    }
    let mut zeros: Vec<i64> = Vec::new();
    let mut lowest = 0usize;
    while lowest < coefficients.len() && coefficients[lowest] == 0 {
        lowest += 1;
    }
    if lowest > 0 && base <= 0 {
        zeros.push(0);
    }
    let tail = &coefficients[lowest..];
    let Some(constant) = tail.first().copied() else {
        return Err("the leading recurrence coefficient is identically zero".to_owned());
    };
    for candidate in divisors_of(constant) {
        if candidate < base || zeros.contains(&candidate) {
            continue;
        }
        let mut value: i128 = 0;
        for coefficient in tail.iter().rev() {
            value = value
                .checked_mul(i128::from(candidate))
                .and_then(|scaled| scaled.checked_add(*coefficient))
                .ok_or_else(|| "overflow evaluating the leading coefficient".to_owned())?;
        }
        if value == 0 {
            zeros.push(candidate);
        }
    }
    zeros.sort_unstable();
    Ok(zeros)
}

/// Every integer whose absolute value divides `value`, both signs, as `i64`.
/// An input of zero yields the empty list — the caller has already stripped the
/// zero root in that case.
fn divisors_of(value: i128) -> Vec<i64> {
    if value == 0 {
        return Vec::new();
    }
    let magnitude = value.unsigned_abs();
    let mut result: Vec<i64> = Vec::new();
    let mut candidate: u128 = 1;
    while candidate.saturating_mul(candidate) <= magnitude {
        if magnitude.is_multiple_of(candidate) {
            for divisor in [candidate, magnitude / candidate] {
                if let Ok(narrow) = i64::try_from(divisor) {
                    result.push(narrow);
                    result.push(-narrow);
                }
            }
        }
        candidate += 1;
    }
    result.sort_unstable();
    result.dedup();
    result
}

/// Least common multiple of two positive `i128` values.
fn lcm_i128(left: i128, right: i128) -> Option<i128> {
    if left == 0 || right == 0 {
        return Some(0);
    }
    let mut current = left.unsigned_abs();
    let mut next = right.unsigned_abs();
    while next != 0 {
        let remainder = current % next;
        current = next;
        next = remainder;
    }
    let gcd = i128::try_from(current).ok()?;
    (left / gcd).checked_mul(right).map(i128::abs)
}

/// A [`LinearForm`] convenience re-export point for callers building terms next
/// to their checks.
pub type Form = LinearForm;
