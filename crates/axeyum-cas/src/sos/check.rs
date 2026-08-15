//! The independent checker.
//!
//! Nothing here consults the search that produced a certificate, and nothing
//! here trusts a quantity the artifact states when it can recompute it instead.
//! Concretely:
//!
//! * the Lie derivative `V-dot` is **never read from the file**; it is formed
//!   from the vector field and the candidate by [`MvPoly::derivative_in`] and
//!   [`MvPoly::mul`]. So a tampered vector field breaks the decrease identity
//!   even though no field in the artifact mentions a derivative;
//! * `|x|^2` is built from the declared variable list, not read, so a file
//!   cannot declare a degenerate "norm" that makes its own sandwich vacuous;
//! * the moment matrix of a dual functional is assembled from the functional and
//!   a checker-built monomial basis, so the file cannot supply a matrix that is
//!   PSD but is not the moment matrix of the functional it also supplies;
//! * every set a theorem quantifies over is required to be **nonempty**, by a
//!   committed point that the checker evaluates the generators at. An empty
//!   initial set satisfies every barrier certificate ever written.
//!
//! Each identity is discharged twice, by two different code paths: once
//! symbolically (expand the squares as polynomials and compare canonical forms)
//! and once numerically (evaluate each square at an exact rational point,
//! square and weight the *rational*, and compare against the target evaluated at
//! the same point). The second pass shares no arithmetic with the first.

use std::collections::BTreeMap;

use axeyum_ir::Rational;

use crate::mvpoly::{Monomial, MvPoly};
use crate::sos::psd::{Psd, is_psd};
use crate::sos::{
    BarrierCertificate, BarrierProblem, CheckReport, LyapunovCertificate, LyapunovProblem,
    PsdNotSosCertificate, PsdNotSosProblem, SosArtifact, SosSum, VectorField, is_negative,
    is_positive, scale, show, sum_of_variable_squares,
};

/// How many deterministic rational points every identity is replayed at.
pub const REPLAY_POINTS: usize = 16;

/// Check one artifact, whatever its kind.
///
/// # Errors
///
/// Returns a message naming the first obligation that failed.
pub fn check_artifact(artifact: &SosArtifact) -> Result<CheckReport, String> {
    match artifact {
        SosArtifact::Lyapunov(problem, certificate) => check_lyapunov(problem, certificate),
        SosArtifact::Barrier(problem, certificate) => check_barrier(problem, certificate),
        SosArtifact::PsdNotSos(problem, certificate) => check_psd_not_sos(problem, certificate),
    }
}

// ---------------------------------------------------------------------------
// Lyapunov
// ---------------------------------------------------------------------------

/// Check a stability certificate.
///
/// # Errors
///
/// Returns a message naming the first obligation that failed.
#[allow(clippy::too_many_lines)]
pub fn check_lyapunov(
    problem: &LyapunovProblem,
    certificate: &LyapunovCertificate,
) -> Result<CheckReport, String> {
    let mut report = CheckReport::new();
    check_system(&problem.system, &mut report)?;

    if problem.v.is_zero() {
        return Err("the candidate Lyapunov function is the zero polynomial".into());
    }
    if !problem
        .v
        .variables()
        .iter()
        .all(|used| problem.system.variables.contains(used))
    {
        return Err("the candidate Lyapunov function mentions an undeclared variable".into());
    }

    for (label, constant) in [
        ("lower", problem.lower),
        ("upper", problem.upper),
        ("decay", problem.decay),
    ] {
        if !is_positive(constant) {
            return Err(format!(
                "the `{label}` constant is {}, but a Lyapunov sandwich needs it strictly positive",
                show(constant)
            ));
        }
    }
    if problem.upper.checked_cmp(&problem.lower) == Some(core::cmp::Ordering::Less) {
        return Err(format!(
            "the sandwich is inconsistent: upper {} is below lower {}",
            show(problem.upper),
            show(problem.lower)
        ));
    }
    report.record(
        "sandwich-constants-positive",
        format!(
            "lower {}, upper {}, decay {}, all > 0 and lower <= upper",
            show(problem.lower),
            show(problem.upper),
            show(problem.decay)
        ),
    );

    let norm = sum_of_variable_squares(&problem.system.variables)?;

    // V - lower * |x|^2 is a sum of squares.
    let lower_target = problem
        .v
        .sub(&scale(&norm, problem.lower)?)
        .ok_or("forming V - lower * |x|^2 overflowed the exact coefficient range".to_string())?;
    discharge(
        "v-bounded-below",
        &certificate.lower_gap,
        &lower_target,
        &problem.system.variables,
        &mut report,
        &format!(
            "V - {} * |x|^2 is a sum of {} squares, so V >= {} * |x|^2 everywhere",
            show(problem.lower),
            certificate.lower_gap.len(),
            show(problem.lower)
        ),
    )?;

    // upper * |x|^2 - V is a sum of squares.
    let upper_target = scale(&norm, problem.upper)?
        .sub(&problem.v)
        .ok_or("forming upper * |x|^2 - V overflowed the exact coefficient range".to_string())?;
    discharge(
        "v-bounded-above",
        &certificate.upper_gap,
        &upper_target,
        &problem.system.variables,
        &mut report,
        &format!(
            "{} * |x|^2 - V is a sum of {} squares, so V <= {} * |x|^2 everywhere",
            show(problem.upper),
            certificate.upper_gap.len(),
            show(problem.upper)
        ),
    )?;

    // The checker forms V-dot itself. This is the obligation the artifact
    // cannot influence except through the vector field it declares.
    let v_dot = problem.system.lie_derivative(&problem.v)?;
    let decrease_target = v_dot
        .neg()
        .ok_or("negating V-dot overflowed".to_string())?
        .sub(&scale(&norm, problem.decay)?)
        .ok_or("forming -V-dot - decay * |x|^2 overflowed".to_string())?;
    discharge(
        "v-dot-bounded-above",
        &certificate.decrease,
        &decrease_target,
        &problem.system.variables,
        &mut report,
        &format!(
            "-V-dot - {} * |x|^2 is a sum of {} squares, with V-dot re-derived here from the \
             vector field ({} terms) rather than read from the artifact",
            show(problem.decay),
            certificate.decrease.len(),
            v_dot.term_count()
        ),
    )?;

    // V(0) = 0. Implied by the sandwich, recorded because a reader scans for it.
    let origin: BTreeMap<String, Rational> = problem
        .system
        .variables
        .iter()
        .map(|name| (name.clone(), Rational::zero()))
        .collect();
    let at_origin = problem
        .v
        .evaluate(&origin)
        .ok_or("evaluating V at the origin failed")?;
    if !at_origin.is_zero() {
        return Err(format!(
            "V(0) = {}, but a Lyapunov function must vanish at the equilibrium",
            show(at_origin)
        ));
    }
    for (index, component) in problem.system.field.iter().enumerate() {
        let value = component
            .evaluate(&origin)
            .ok_or("evaluating the vector field at the origin failed")?;
        if !value.is_zero() {
            return Err(format!(
                "component {index} of the vector field is {} at the origin, which is therefore not \
                 an equilibrium",
                show(value)
            ));
        }
    }
    report.record(
        "origin-is-an-equilibrium",
        format!(
            "V(0) = 0 and every one of the {} field components vanishes at the origin",
            problem.system.field.len()
        ),
    );

    // The naive candidate |x|^2 must genuinely fail, or this certificate is
    // evidence of nothing.
    let naive_dot = problem.system.lie_derivative(&norm)?;
    for name in &problem.system.variables {
        if !problem.naive_failure.contains_key(name) {
            return Err(format!(
                "the naive-failure point leaves `{name}` unbound, so it is not a point of the state \
                 space"
            ));
        }
    }
    let naive_value = naive_dot
        .evaluate(&problem.naive_failure)
        .ok_or("evaluating the naive candidate's Lie derivative failed")?;
    if !is_positive(naive_value) {
        return Err(format!(
            "the naive candidate |x|^2 has Lie derivative {} at the committed point, which is not \
             positive -- so the artifact does not show that the obvious guess fails, and a \
             certificate for a problem the obvious guess already solves is not evidence that \
             anything was searched for",
            show(naive_value)
        ));
    }
    report.record(
        "naive-candidate-fails",
        format!(
            "the Lie derivative of |x|^2 is {} > 0 at the committed point, so |x|^2 is NOT a \
             Lyapunov function for this system and the certified V is doing real work",
            show(naive_value)
        ),
    );

    let rate = problem
        .decay
        .checked_div(problem.upper)
        .ok_or("forming the decay rate decay / upper overflowed")?;
    let overshoot = problem
        .upper
        .checked_div(problem.lower)
        .ok_or("forming the overshoot upper / lower overflowed")?;
    report.record(
        "exponential-rate",
        format!(
            "V-dot <= -{} * |x|^2 and V <= {} * |x|^2, so V-dot <= -{} * V. Every solution \
             therefore satisfies |x(t)|^2 <= {} * |x(0)|^2 * exp(-{} * t): an exactly rational \
             certified decay rate {} and overshoot {}, with the passage from these three \
             polynomial inequalities to that bound on solutions being Lyapunov's direct method \
             plus a Gronwall comparison, which is analysis and is NOT certified here",
            show(problem.decay),
            show(problem.upper),
            show(rate),
            show(overshoot),
            show(rate),
            show(rate),
            show(overshoot)
        ),
    );
    report.rate = Some(rate);
    Ok(report)
}

// ---------------------------------------------------------------------------
// Barrier
// ---------------------------------------------------------------------------

/// Check a barrier certificate.
///
/// # Errors
///
/// Returns a message naming the first obligation that failed.
#[allow(clippy::too_many_lines)]
pub fn check_barrier(
    problem: &BarrierProblem,
    certificate: &BarrierCertificate,
) -> Result<CheckReport, String> {
    let mut report = CheckReport::new();
    check_system(&problem.system, &mut report)?;

    if problem.initial.is_empty() {
        return Err("the initial set has no generators, so it is all of state space".into());
    }
    if problem.unsafe_region.is_empty() {
        return Err("the unsafe set has no generators, so it is all of state space".into());
    }

    // Non-vacuity. This is first because everything after it is worthless
    // without it: a barrier certificate over an empty initial set checks out
    // and proves nothing.
    witness_in_set(
        &problem.initial,
        &problem.initial_witness,
        &problem.system.variables,
        "initial",
    )?;
    witness_in_set(
        &problem.unsafe_region,
        &problem.unsafe_witness,
        &problem.system.variables,
        "unsafe",
    )?;
    report.record(
        "both-sets-nonempty",
        format!(
            "a committed point satisfies all {} initial generators and another satisfies all {} \
             unsafe generators, so neither set is empty and the separation is not vacuous",
            problem.initial.len(),
            problem.unsafe_region.len()
        ),
    );

    for (label, margin) in [
        ("initial", certificate.initial_margin),
        ("unsafe", certificate.unsafe_margin),
    ] {
        if !is_positive(margin) {
            return Err(format!(
                "the {label} margin is {}, but the separation needs it strictly positive",
                show(margin)
            ));
        }
    }

    // -B - initial_margin - sum sigma_i g_i is a sum of squares.
    let initial_target = positivstellensatz_target(
        &problem
            .barrier
            .neg()
            .ok_or("negating the barrier overflowed".to_string())?,
        certificate.initial_margin,
        &certificate.initial_multipliers,
        &problem.initial,
        "initial",
    )?;
    discharge(
        "barrier-below-on-the-initial-set",
        &certificate.initial_gap,
        &initial_target,
        &problem.system.variables,
        &mut report,
        &format!(
            "-B - {} - sum of {} SOS multiples of the initial generators is a sum of {} squares, so \
             B <= -{} on the whole initial set",
            show(certificate.initial_margin),
            certificate.initial_multipliers.len(),
            certificate.initial_gap.len(),
            show(certificate.initial_margin)
        ),
    )?;

    // B - unsafe_margin - sum tau_j h_j is a sum of squares.
    let unsafe_target = positivstellensatz_target(
        &problem.barrier,
        certificate.unsafe_margin,
        &certificate.unsafe_multipliers,
        &problem.unsafe_region,
        "unsafe",
    )?;
    discharge(
        "barrier-above-on-the-unsafe-set",
        &certificate.unsafe_gap,
        &unsafe_target,
        &problem.system.variables,
        &mut report,
        &format!(
            "B - {} - sum of {} SOS multiples of the unsafe generators is a sum of {} squares, so \
             B >= {} on the whole unsafe set",
            show(certificate.unsafe_margin),
            certificate.unsafe_multipliers.len(),
            certificate.unsafe_gap.len(),
            show(certificate.unsafe_margin)
        ),
    )?;

    // -B-dot is a sum of squares, with B-dot re-derived here.
    let b_dot = problem.system.lie_derivative(&problem.barrier)?;
    let decrease_target = b_dot.neg().ok_or("negating B-dot overflowed".to_string())?;
    discharge(
        "barrier-non-increasing-along-the-flow",
        &certificate.decrease,
        &decrease_target,
        &problem.system.variables,
        &mut report,
        &format!(
            "-B-dot is a sum of {} squares, with B-dot re-derived here from the vector field ({} \
             terms) rather than read from the artifact, so B never increases along any solution",
            certificate.decrease.len(),
            b_dot.term_count()
        ),
    )?;

    // The two committed points must land on the correct sides. This is not
    // implied by the identities above; it is a second, concrete confirmation
    // that the separation is oriented the way the prose says.
    let at_initial = problem
        .barrier
        .evaluate(&problem.initial_witness)
        .ok_or("evaluating the barrier at the initial witness failed")?;
    let at_unsafe = problem
        .barrier
        .evaluate(&problem.unsafe_witness)
        .ok_or("evaluating the barrier at the unsafe witness failed")?;
    if at_initial.checked_cmp(&Rational::zero()) != Some(core::cmp::Ordering::Less) {
        return Err(format!(
            "the barrier is {} at the initial witness; it must be negative there",
            show(at_initial)
        ));
    }
    if !is_positive(at_unsafe) {
        return Err(format!(
            "the barrier is {} at the unsafe witness; it must be positive there",
            show(at_unsafe)
        ));
    }
    report.record(
        "separation-is-oriented",
        format!(
            "B = {} at the initial witness and {} at the unsafe witness, so the two sets are \
             disjoint and no solution from the initial set ever reaches the unsafe set, at any \
             time, with no horizon bound",
            show(at_initial),
            show(at_unsafe)
        ),
    );
    Ok(report)
}

// ---------------------------------------------------------------------------
// PSD but not SOS
// ---------------------------------------------------------------------------

/// Check a "nonnegative but not a sum of squares" certificate.
///
/// # Errors
///
/// Returns a message naming the first obligation that failed.
#[allow(clippy::too_many_lines)]
pub fn check_psd_not_sos(
    problem: &PsdNotSosProblem,
    certificate: &PsdNotSosCertificate,
) -> Result<CheckReport, String> {
    let mut report = CheckReport::new();

    if problem.variables.is_empty() {
        return Err("the problem declares no variables".into());
    }
    if problem.half_degree == 0 {
        return Err("half_degree must be positive; a degree-zero form is a constant".into());
    }
    let full_degree = u64::from(problem.half_degree) * 2;

    // The form must be homogeneous of degree 2 * half_degree, and mention only
    // declared variables. Homogeneity is what makes the degree-`half_degree`
    // monomial basis the complete basis for a hypothetical SOS representation.
    if problem.form.is_zero() {
        return Err("the form is the zero polynomial".into());
    }
    for (monomial, _) in problem.form.terms() {
        if monomial.total_degree() != full_degree {
            return Err(format!(
                "the form carries a monomial of degree {} in a claimed degree-{full_degree} form; \
                 the dual argument here is only valid for a homogeneous form",
                monomial.total_degree()
            ));
        }
    }
    for used in problem.form.variables() {
        if !problem.variables.contains(&used) {
            return Err(format!(
                "the form mentions the undeclared variable `{used}`"
            ));
        }
    }
    report.record(
        "form-is-homogeneous",
        format!(
            "the form has {} terms, every one of degree {full_degree}, over {} declared variables",
            problem.form.term_count(),
            problem.variables.len()
        ),
    );

    // The multiplier must be exactly the sum of the squares of the declared
    // variables. That is the only property under which "multiplier * form is
    // SOS" gives "form >= 0": it must be strictly positive off the origin. A
    // file that supplied its own multiplier could pick one vanishing on a whole
    // hyperplane and prove nothing there.
    let expected_multiplier = sum_of_variable_squares(&problem.variables)?;
    if problem.multiplier != expected_multiplier {
        return Err(
            "the multiplier is not the sum of the squares of the declared variables; only that \
             multiplier is strictly positive off the origin, so only that multiplier lets an SOS \
             product certify nonnegativity of the form"
                .into(),
        );
    }
    report.record(
        "multiplier-is-positive-off-the-origin",
        format!(
            "the multiplier is |x|^2 over the {} declared variables, rebuilt here rather than read",
            problem.variables.len()
        ),
    );

    let multiplied_target = problem
        .multiplier
        .mul(&problem.form)
        .ok_or("forming multiplier * form overflowed".to_string())?;
    discharge(
        "multiplied-form-is-a-sum-of-squares",
        &certificate.multiplied,
        &multiplied_target,
        &problem.variables,
        &mut report,
        &format!(
            "|x|^2 * form is a sum of {} squares ({} terms expanded), so form >= 0 at every point \
             of every ordered field, the origin included by homogeneity",
            certificate.multiplied.len(),
            multiplied_target.term_count()
        ),
    )?;

    // The dual half. The basis is built here; the moment matrix is assembled
    // here from the functional the artifact supplies.
    let basis = monomials_of_degree(&problem.variables, problem.half_degree);
    if basis.is_empty() {
        return Err("the monomial basis is empty".into());
    }
    for monomial in certificate.dual.keys() {
        if monomial.total_degree() != full_degree {
            return Err(format!(
                "the dual functional assigns a value to a monomial of degree {}, but it is a \
                 functional on degree-{full_degree} forms; a value off that degree is read by no \
                 moment-matrix entry and would be an unchecked free parameter",
                monomial.total_degree()
            ));
        }
        for (name, _) in monomial.powers() {
            if !problem.variables.contains(&name.to_string()) {
                return Err(format!(
                    "the dual functional mentions the undeclared variable `{name}`"
                ));
            }
        }
    }

    let mut moment = Vec::with_capacity(basis.len());
    for row in &basis {
        let mut entries = Vec::with_capacity(basis.len());
        for column in &basis {
            let product = MvPoly::from_terms([(row.clone(), Rational::integer(1))])
                .ok_or("building a basis monomial failed".to_string())?
                .mul(
                    &MvPoly::from_terms([(column.clone(), Rational::integer(1))])
                        .ok_or("building a basis monomial failed".to_string())?,
                )
                .ok_or("multiplying two basis monomials overflowed".to_string())?;
            let (key, _) = product
                .terms()
                .next()
                .ok_or("a product of two monomials is not a monomial".to_string())?;
            entries.push(
                certificate
                    .dual
                    .get(key)
                    .copied()
                    .unwrap_or_else(Rational::zero),
            );
        }
        moment.push(entries);
    }

    match is_psd(&moment) {
        Psd::Yes {
            ref pivots,
            zero_pivots,
        } => report.record(
            "moment-matrix-is-psd",
            format!(
                "the {0}-by-{0} moment matrix assembled here from the dual functional and a \
                 checker-built basis of the {0} degree-{1} monomials is positive semidefinite by \
                 exact rational LDL^T: {2} positive pivots, {zero_pivots} zero. So the functional \
                 is nonnegative on every square of a degree-{1} form.",
                basis.len(),
                problem.half_degree,
                pivots.len()
            ),
        ),
        Psd::No(reason) => {
            return Err(format!(
                "the moment matrix of the dual functional is not positive semidefinite: {reason}"
            ));
        }
        Psd::Overflow => {
            return Err(
                "the exact PSD test overflowed; this is a decline, and nothing is claimed \
                 about the matrix"
                    .into(),
            );
        }
    }

    let mut functional_value = Rational::zero();
    for (monomial, coefficient) in problem.form.terms() {
        let value = certificate
            .dual
            .get(monomial)
            .copied()
            .unwrap_or_else(Rational::zero);
        let contribution = coefficient
            .checked_mul(value)
            .ok_or("applying the dual functional overflowed")?;
        functional_value = functional_value
            .checked_add(contribution)
            .ok_or("applying the dual functional overflowed")?;
    }
    if !is_negative(functional_value) {
        return Err(format!(
            "the dual functional takes the value {} on the form; to refute SOS-ness it must be \
             strictly negative, since it is nonnegative on every square",
            show(functional_value)
        ));
    }
    report.record(
        "dual-is-negative-on-the-form",
        format!(
            "the functional takes the value {} on the form while being nonnegative on every \
             square of a degree-{} form, so the form is NOT a sum of squares -- of forms by the \
             moment argument, and hence not of polynomials",
            show(functional_value),
            problem.half_degree
        ),
    );
    Ok(report)
}

// ---------------------------------------------------------------------------
// shared obligations
// ---------------------------------------------------------------------------

fn check_system(system: &VectorField, report: &mut CheckReport) -> Result<(), String> {
    if system.variables.is_empty() {
        return Err("the system declares no state variables".into());
    }
    if system.variables.len() != system.field.len() {
        return Err(format!(
            "the vector field has {} components for {} state variables",
            system.field.len(),
            system.variables.len()
        ));
    }
    let mut seen = std::collections::BTreeSet::new();
    for name in &system.variables {
        if !seen.insert(name.clone()) {
            return Err(format!("the state variable `{name}` is declared twice"));
        }
    }
    if !system.is_closed() {
        return Err(
            "the vector field mentions a variable that is not a declared state variable, so the \
             system is not autonomous in the declared state"
                .into(),
        );
    }
    let degree = system
        .field
        .iter()
        .map(MvPoly::total_degree)
        .max()
        .unwrap_or(0);
    report.record(
        "system-is-well-formed",
        format!(
            "{} state variables, {} field components, closed in the declared state, degree {degree}",
            system.variables.len(),
            system.field.len()
        ),
    );
    Ok(())
}

/// Discharge one SOS identity twice: symbolically and numerically.
fn discharge(
    name: &str,
    sum: &SosSum,
    target: &MvPoly,
    variables: &[String],
    report: &mut CheckReport,
    detail: &str,
) -> Result<(), String> {
    if sum.is_empty() && !target.is_zero() {
        return Err(format!(
            "`{name}`: the certificate offers no squares at all for a nonzero target"
        ));
    }
    for (weight, square) in sum.squares() {
        if is_negative(*weight) {
            return Err(format!(
                "`{name}`: a summand carries the negative weight {}",
                show(*weight)
            ));
        }
        for used in square.variables() {
            if !variables.contains(&used) {
                return Err(format!(
                    "`{name}`: a summand mentions the undeclared variable `{used}`"
                ));
            }
        }
    }

    let expanded = sum
        .expand()
        .map_err(|message| format!("`{name}`: {message}"))?;
    if expanded != *target {
        let difference = expanded
            .sub(target)
            .ok_or_else(|| format!("`{name}`: the identity fails and the residue overflowed"))?;
        return Err(format!(
            "`{name}`: the squares expand to a polynomial differing from the target in {} \
             monomial(s); the certificate does not prove what it claims",
            difference.term_count()
        ));
    }

    for point_index in 0..REPLAY_POINTS {
        let point = replay_point(variables, point_index);
        let from_squares = evaluate_sos(sum, &point).ok_or_else(|| {
            format!("`{name}`: evaluating the squares at replay point {point_index} failed")
        })?;
        let from_target = target.evaluate(&point).ok_or_else(|| {
            format!("`{name}`: evaluating the target at replay point {point_index} failed")
        })?;
        if from_squares != from_target {
            return Err(format!(
                "`{name}`: at replay point {point_index} the squares give {} and the target gives \
                 {}",
                show(from_squares),
                show(from_target)
            ));
        }
        if is_negative(from_squares) {
            return Err(format!(
                "`{name}`: the sum of squares evaluates to the negative value {} at replay point \
                 {point_index}, which is impossible for nonnegative weights and means the weights \
                 were not checked",
                show(from_squares)
            ));
        }
    }

    report.record(
        name,
        format!("{detail}; re-derived symbolically and at {REPLAY_POINTS} exact rational points"),
    );
    Ok(())
}

/// Evaluate a sum of weighted squares by rational arithmetic alone -- squaring
/// the *value* of each summand rather than expanding any polynomial. This is the
/// second, independent code path behind every identity.
fn evaluate_sos(sum: &SosSum, point: &BTreeMap<String, Rational>) -> Option<Rational> {
    let mut total = Rational::zero();
    for (weight, square) in sum.squares() {
        let value = square.evaluate(point)?;
        let squared = value.checked_mul(value)?;
        let weighted = weight.checked_mul(squared)?;
        total = total.checked_add(weighted)?;
    }
    Some(total)
}

/// A deterministic rational point. Small numerators and denominators keep the
/// exact arithmetic in range while still separating polynomials that agree on
/// the integers.
fn replay_point(variables: &[String], index: usize) -> BTreeMap<String, Rational> {
    let mut point = BTreeMap::new();
    for (slot, name) in variables.iter().enumerate() {
        let seed = index * 7 + slot * 13 + 3;
        let numerator = i128::try_from(seed % 11).unwrap_or(0) - 5;
        let denominator = i128::try_from((index + slot) % 3).unwrap_or(0) + 1;
        point.insert(name.clone(), Rational::new(numerator, denominator));
    }
    point
}

fn witness_in_set(
    generators: &[MvPoly],
    witness: &BTreeMap<String, Rational>,
    variables: &[String],
    label: &str,
) -> Result<(), String> {
    for name in variables {
        if !witness.contains_key(name) {
            return Err(format!(
                "the {label}-set witness leaves `{name}` unbound, so it is not a point of the state \
                 space"
            ));
        }
    }
    for (index, generator) in generators.iter().enumerate() {
        let value = generator
            .evaluate(witness)
            .ok_or_else(|| format!("evaluating {label} generator {index} at its witness failed"))?;
        if is_negative(value) {
            return Err(format!(
                "the {label}-set witness gives generator {index} the value {}, so the committed \
                 point is NOT in the set and the set may be empty -- an empty set satisfies every \
                 separation certificate and proves nothing",
                show(value)
            ));
        }
    }
    Ok(())
}

fn positivstellensatz_target(
    head: &MvPoly,
    margin: Rational,
    multipliers: &[SosSum],
    generators: &[MvPoly],
    label: &str,
) -> Result<MvPoly, String> {
    if multipliers.len() != generators.len() {
        return Err(format!(
            "the certificate offers {} multipliers for the {} {label}-set generators",
            multipliers.len(),
            generators.len()
        ));
    }
    let mut target = head
        .sub(&MvPoly::constant(margin))
        .ok_or_else(|| format!("subtracting the {label} margin overflowed"))?;
    for (multiplier, generator) in multipliers.iter().zip(generators.iter()) {
        let sigma = multiplier
            .expand()
            .map_err(|message| format!("{label} multiplier: {message}"))?;
        let product = sigma
            .mul(generator)
            .ok_or_else(|| format!("forming a {label} Positivstellensatz product overflowed"))?;
        target = target.sub(&product).ok_or_else(|| {
            format!("accumulating the {label} Positivstellensatz target overflowed")
        })?;
    }
    Ok(target)
}

/// Every monomial of exactly the given total degree over the given variables,
/// in a deterministic order.
fn monomials_of_degree(variables: &[String], degree: u32) -> Vec<Monomial> {
    let mut out = Vec::new();
    let mut exponents = vec![0u32; variables.len()];
    fill(variables, degree, 0, &mut exponents, &mut out);
    out
}

fn fill(
    variables: &[String],
    remaining: u32,
    slot: usize,
    exponents: &mut Vec<u32>,
    out: &mut Vec<Monomial>,
) {
    if slot + 1 == variables.len() {
        exponents[slot] = remaining;
        let factors: Vec<(&str, u32)> = variables
            .iter()
            .zip(exponents.iter())
            .filter(|(_, exponent)| **exponent > 0)
            .map(|(name, exponent)| (name.as_str(), *exponent))
            .collect();
        out.push(Monomial::from_powers(&factors));
        return;
    }
    for taken in 0..=remaining {
        exponents[slot] = taken;
        fill(variables, remaining - taken, slot + 1, exponents, out);
    }
}

#[cfg(test)]
mod tests {
    use super::{monomials_of_degree, replay_point};

    #[test]
    fn the_degree_three_basis_in_three_variables_has_ten_monomials() {
        let variables = vec!["x".to_string(), "y".to_string(), "z".to_string()];
        let basis = monomials_of_degree(&variables, 3);
        assert_eq!(basis.len(), 10);
        for monomial in &basis {
            assert_eq!(monomial.total_degree(), 3);
        }
        let mut sorted = basis.clone();
        sorted.sort();
        sorted.dedup();
        assert_eq!(sorted.len(), 10, "the basis must have no repeats");
    }

    #[test]
    fn replay_points_are_distinct_and_deterministic() {
        let variables = vec!["x".to_string(), "y".to_string()];
        let first: Vec<_> = (0..8).map(|i| replay_point(&variables, i)).collect();
        let again: Vec<_> = (0..8).map(|i| replay_point(&variables, i)).collect();
        assert_eq!(first, again);
        let mut seen = std::collections::BTreeSet::new();
        for point in &first {
            let key: Vec<_> = point
                .iter()
                .map(|(name, value)| (name.clone(), value.numerator(), value.denominator()))
                .collect();
            assert!(seen.insert(key), "replay points must not repeat");
        }
    }
}
