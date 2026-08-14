//! Creative telescoping (Zeilberger's algorithm) for **definite** hypergeometric
//! sums, emitting a certificate that is checkable by polynomial algebra alone.
//!
//! [`gosper_sum`](crate::gosper_sum) settles the *indefinite* question: is
//! `∑ t(k)` itself hypergeometric? The definite question — what does
//! `S(n) = ∑_k F(n,k)` equal — is answered instead by a **recurrence in `n`**,
//! and the object that establishes the recurrence is a single rational function.
//!
//! # The certificate
//!
//! Given a hypergeometric term `F(n,k)`, a certificate is a pair
//!
//! ```text
//! (a_0(n), …, a_J(n))   — polynomials, not all zero
//! R(n,k) = P(n,k)/Q(n,k) — a rational function
//! ```
//!
//! subject to one identity, in which every `F` has already cancelled:
//!
//! ```text
//! Σ_j a_j(n)·S_j(n,k)  =  R(n,k+1)·r(n,k)  −  R(n,k)          (★)
//!
//!   S_j(n,k) = F(n+j,k)/F(n,k)     r(n,k) = F(n,k+1)/F(n,k)
//! ```
//!
//! `S_j` and `r` are rational functions read straight off the term's shape, so
//! (★) is an identity in `ℚ(n,k)` — cross-multiply and expand and it is either
//! exactly zero or it is not. Multiplying (★) through by `F(n,k)` gives
//!
//! ```text
//! Σ_j a_j(n)·F(n+j,k) = G(n,k+1) − G(n,k),   G = R·F
//! ```
//!
//! and summing over the (finite) support of `F` collapses the right side, so
//! `Σ_j a_j(n)·S(n+j) = 0`. That is the whole proof, and its only algebraic
//! content is a polynomial identity.
//!
//! # What is searched and what is trusted
//!
//! Nothing here is trusted. The search below is an ansatz: fix a denominator
//! `Q` from a small ladder of candidates, bound the degrees of `a_j` and `P`,
//! and read (★) as one homogeneous linear system over ℚ whose unknowns are those
//! coefficients. A nullspace vector *is* a certificate. A wrong ansatz, a wrong
//! degree bound, an overflow, or an outright bug in the linear algebra loses a
//! certificate; it cannot manufacture one, because the consumer
//! ([`crate::telescoping_check`]) re-derives (★) from the term specification with
//! its own code and additionally cross-checks the shift ratios against direct
//! exact-bignum evaluation of the term at integer points.
//!
//! # Scope
//!
//! A [`HyperTerm`] is a product of `Γ(linear form)^e`, `c^(linear form)` and
//! `polynomial^e` factors. That covers factorials, binomial coefficients to
//! integer powers, geometric factors, falling/rising factorials with integer
//! shifts, and polynomial weights — the classical binomial-identity fragment. It
//! does **not** cover `q`-analogues, terms whose parameters enter non-linearly,
//! or non-hypergeometric summands.

use std::collections::{BTreeMap, BTreeSet};

use axeyum_ir::Rational;
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};

use crate::mvpoly::{Monomial, MvPoly};

/// Largest `Γ` argument displacement expanded into an explicit rising/falling
/// product when forming a shift ratio. Beyond this the ratio's degree makes the
/// linear system pointless, so the search declines rather than allocating.
const MAX_GAMMA_DISPLACEMENT: u64 = 32;

/// Largest absolute integer exponent accepted on a `Γ` or polynomial factor.
const MAX_FACTOR_EXPONENT: i32 = 16;

/// An integer-coefficient linear form `Σ cᵥ·v + c` over named variables.
///
/// Hypergeometric terms in the classical fragment have `Γ` arguments that are
/// exactly of this shape (`n+1`, `k+1`, `n−k+1`, `2n+1`, …), and restricting to
/// it is what makes every shift ratio computable in closed form.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LinearForm {
    coefficients: BTreeMap<String, i64>,
    constant: i64,
}

impl LinearForm {
    /// Build `Σ coefficient·variable + constant`. Repeated variables sum; zero
    /// coefficients are dropped.
    #[must_use]
    pub fn new(terms: &[(&str, i64)], constant: i64) -> LinearForm {
        let mut coefficients: BTreeMap<String, i64> = BTreeMap::new();
        for (name, value) in terms {
            let slot = coefficients.entry((*name).to_owned()).or_insert(0);
            *slot = slot.saturating_add(*value);
        }
        coefficients.retain(|_, value| *value != 0);
        LinearForm {
            coefficients,
            constant,
        }
    }

    /// The coefficient of `var` (zero when absent).
    #[must_use]
    pub fn coefficient(&self, var: &str) -> i64 {
        self.coefficients.get(var).copied().unwrap_or(0)
    }

    /// The variables occurring with a nonzero coefficient.
    #[must_use]
    pub fn variables(&self) -> BTreeSet<String> {
        self.coefficients.keys().cloned().collect()
    }

    /// This form as a degree-one polynomial, or `None` on coefficient overflow.
    #[must_use]
    pub fn to_poly(&self) -> Option<MvPoly> {
        let mut poly = MvPoly::constant(Rational::integer(i128::from(self.constant)));
        for (name, value) in &self.coefficients {
            let piece =
                MvPoly::var(name).mul(&MvPoly::constant(Rational::integer(i128::from(*value))))?;
            poly = poly.add(&piece)?;
        }
        Some(poly)
    }

    /// The exact integer value of this form under an integer assignment, or
    /// `None` if a variable is unassigned or the arithmetic overflows.
    #[must_use]
    pub fn evaluate(&self, assignment: &BTreeMap<String, i64>) -> Option<i64> {
        let mut total = self.constant;
        for (name, value) in &self.coefficients {
            let point = *assignment.get(name)?;
            total = total.checked_add(value.checked_mul(point)?)?;
        }
        Some(total)
    }
}

/// One factor of a hypergeometric term.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Factor {
    /// `Γ(form)^exponent`. Factorials are `Γ(x+1)`; a binomial coefficient
    /// `C(n,k)` is `Γ(n+1)·Γ(k+1)⁻¹·Γ(n−k+1)⁻¹`.
    Gamma {
        /// The `Γ` argument.
        form: LinearForm,
        /// The integer power the `Γ` factor is raised to (negative = denominator).
        exponent: i32,
    },
    /// `base^form` with a rational `base` — the geometric factors `2ⁿ`, `(−1)ᵏ`,
    /// `2^{-n}`.
    Power {
        /// The (nonzero) rational base.
        base: Rational,
        /// The exponent as a linear form in the variables.
        form: LinearForm,
    },
    /// `poly^exponent` — a polynomial weight such as `k`, `k²` or `2k+1`.
    Poly {
        /// The polynomial factor.
        poly: MvPoly,
        /// The integer power it is raised to (negative = denominator).
        exponent: i32,
    },
}

/// A product of [`Factor`]s: the hypergeometric term a certificate is about.
///
/// The specification, not an expression tree, is the input to both the producer
/// and the checker — it is what makes the shift ratios recomputable and what
/// makes concrete evaluation at integer points possible.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HyperTerm {
    factors: Vec<Factor>,
}

/// A rational function held as an explicit numerator/denominator pair.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RationalFunction {
    /// The numerator.
    pub numerator: MvPoly,
    /// The denominator; never the zero polynomial in a well-formed value.
    pub denominator: MvPoly,
}

impl RationalFunction {
    /// This fraction with a common polynomial factor removed, or `None` on
    /// overflow. Value-preserving.
    #[must_use]
    pub fn reduced(&self) -> Option<RationalFunction> {
        if self.numerator.is_zero() {
            return Some(RationalFunction {
                numerator: MvPoly::zero(),
                denominator: MvPoly::constant(Rational::integer(1)),
            });
        }
        let common = self.numerator.gcd(&self.denominator)?;
        if common.total_degree() == 0 {
            return Some(self.clone());
        }
        Some(RationalFunction {
            numerator: self.numerator.exact_div(&common)?,
            denominator: self.denominator.exact_div(&common)?,
        })
    }
}

impl HyperTerm {
    /// A term from its factors.
    #[must_use]
    pub fn new(factors: Vec<Factor>) -> HyperTerm {
        HyperTerm { factors }
    }

    /// The factors, in the order supplied.
    #[must_use]
    pub fn factors(&self) -> &[Factor] {
        &self.factors
    }

    /// Every variable the term mentions.
    #[must_use]
    pub fn variables(&self) -> BTreeSet<String> {
        let mut vars = BTreeSet::new();
        for factor in &self.factors {
            match factor {
                Factor::Gamma { form, .. } | Factor::Power { form, .. } => {
                    vars.extend(form.variables());
                }
                Factor::Poly { poly, .. } => vars.extend(poly.variables()),
            }
        }
        vars
    }

    /// The shift ratio `term(var → var + delta) / term`, as a rational function.
    ///
    /// Every `Γ` factor contributes an explicit rising or falling product, every
    /// power factor a rational constant, and every polynomial factor a shifted
    /// quotient. Returns `None` when a displacement exceeds
    /// the internal displacement ceiling, an exponent exceeds the factor-exponent
    /// ceiling, or exact arithmetic overflows — never a guessed ratio.
    #[must_use]
    pub fn shift_ratio(&self, var: &str, delta: i64) -> Option<RationalFunction> {
        let one = MvPoly::constant(Rational::integer(1));
        let mut numerator = one.clone();
        let mut denominator = one.clone();
        for factor in &self.factors {
            let (piece_num, piece_den) = match factor {
                Factor::Gamma { form, exponent } => {
                    let displacement = form.coefficient(var).checked_mul(delta)?;
                    let (base_num, base_den) = gamma_displacement_ratio(form, displacement)?;
                    fraction_power(&base_num, &base_den, *exponent)?
                }
                Factor::Power { base, form } => {
                    let displacement = form.coefficient(var).checked_mul(delta)?;
                    (
                        MvPoly::constant(rational_power(*base, displacement)?),
                        one.clone(),
                    )
                }
                Factor::Poly { poly, exponent } => {
                    let shifted = shift_variable(poly, var, delta)?;
                    fraction_power(&shifted, poly, *exponent)?
                }
            };
            numerator = numerator.mul(&piece_num)?;
            denominator = denominator.mul(&piece_den)?;
        }
        RationalFunction {
            numerator,
            denominator,
        }
        .reduced()
    }
}

/// `Γ(L + displacement) / Γ(L)` as `(numerator, denominator)`.
///
/// `Γ(L+d)/Γ(L) = L(L+1)···(L+d−1)` for `d > 0` and `1/((L−1)···(L−|d|))` for
/// `d < 0`; both follow from `Γ(x+1) = x·Γ(x)` alone.
fn gamma_displacement_ratio(form: &LinearForm, displacement: i64) -> Option<(MvPoly, MvPoly)> {
    let one = MvPoly::constant(Rational::integer(1));
    if displacement == 0 {
        return Some((one.clone(), one));
    }
    if displacement.unsigned_abs() > MAX_GAMMA_DISPLACEMENT {
        return None;
    }
    let base = form.to_poly()?;
    let step = |offset: i64| -> Option<MvPoly> {
        base.add(&MvPoly::constant(Rational::integer(i128::from(offset))))
    };
    if displacement > 0 {
        let mut numerator = one.clone();
        for offset in 0..displacement {
            numerator = numerator.mul(&step(offset)?)?;
        }
        Some((numerator, one))
    } else {
        let mut denominator = one.clone();
        for offset in 1..=displacement.unsigned_abs() {
            denominator = denominator.mul(&step(-i64::try_from(offset).ok()?)?)?;
        }
        Some((one, denominator))
    }
}

/// `(numerator/denominator)^exponent`, flipping the fraction for a negative
/// exponent. `None` when the exponent exceeds [`MAX_FACTOR_EXPONENT`].
fn fraction_power(
    numerator: &MvPoly,
    denominator: &MvPoly,
    exponent: i32,
) -> Option<(MvPoly, MvPoly)> {
    if exponent.abs() > MAX_FACTOR_EXPONENT {
        return None;
    }
    let power = exponent.unsigned_abs();
    if exponent >= 0 {
        Some((numerator.pow(power)?, denominator.pow(power)?))
    } else {
        Some((denominator.pow(power)?, numerator.pow(power)?))
    }
}

/// `base^exponent` for a possibly negative integer exponent, exactly.
fn rational_power(base: Rational, exponent: i64) -> Option<Rational> {
    if base.is_zero() {
        return (exponent == 0).then(|| Rational::integer(1));
    }
    let magnitude = u32::try_from(exponent.unsigned_abs()).ok()?;
    if u64::from(magnitude) > MAX_GAMMA_DISPLACEMENT * 8 {
        return None;
    }
    let mut value = Rational::integer(1);
    for _ in 0..magnitude {
        value = value.checked_mul(base)?;
    }
    if exponent < 0 {
        Rational::integer(1).checked_div(value)
    } else {
        Some(value)
    }
}

/// `poly(var → var + delta)`, expanded. `None` on overflow.
#[must_use]
pub fn shift_variable(poly: &MvPoly, var: &str, delta: i64) -> Option<MvPoly> {
    if delta == 0 || !poly.variables().contains(var) {
        return Some(poly.clone());
    }
    let shifted_var =
        MvPoly::var(var).add(&MvPoly::constant(Rational::integer(i128::from(delta))))?;
    let mut result = MvPoly::zero();
    for (mono, coeff) in poly.terms() {
        let mut piece = MvPoly::constant(*coeff);
        for (name, exponent) in mono.powers() {
            let factor = if name == var {
                shifted_var.pow(exponent)?
            } else {
                MvPoly::var(name).pow(exponent)?
            };
            piece = piece.mul(&factor)?;
        }
        result = result.add(&piece)?;
    }
    Some(result)
}

/// A creative-telescoping certificate for `S(n) = ∑_k F(n,k)`.
///
/// It asserts exactly the rational identity (★) of the module documentation.
/// Everything a checker needs is here: the term specification, which variable is
/// summed, which is shifted, the recurrence coefficients, and `R = P/Q`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TelescopingCertificate {
    /// The summand `F`.
    pub term: HyperTerm,
    /// The variable the recurrence is in (`n`).
    pub shift_var: String,
    /// The variable summed over (`k`).
    pub sum_var: String,
    /// `a_0 … a_J`, polynomials free of [`Self::sum_var`]; `a_J` is nonzero.
    pub recurrence: Vec<MvPoly>,
    /// The numerator `P` of the certificate `R = P/Q`.
    pub certificate_numerator: MvPoly,
    /// The denominator `Q` of the certificate `R = P/Q`; never zero.
    pub certificate_denominator: MvPoly,
}

impl TelescopingCertificate {
    /// The order `J` of the recurrence this certificate establishes.
    #[must_use]
    pub fn order(&self) -> usize {
        self.recurrence.len().saturating_sub(1)
    }
}

/// Deterministic ceilings for one creative-telescoping search.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Limits {
    /// Largest recurrence order `J` attempted.
    pub max_order: usize,
    /// Largest total degree of the recurrence coefficients `a_j`.
    pub max_recurrence_degree: u32,
    /// Largest total degree of the certificate numerator `P`.
    pub max_certificate_degree: u32,
    /// Largest number of unknowns in one linear system.
    pub max_unknowns: usize,
    /// Largest number of stored monomials in any intermediate polynomial.
    pub max_poly_terms: usize,
}

impl Limits {
    /// Ceilings sized for the classical binomial identities: order up to two,
    /// linear-in-`n` recurrence coefficients, and a certificate numerator of
    /// total degree up to five.
    #[must_use]
    pub fn classical() -> Limits {
        Limits {
            max_order: 2,
            max_recurrence_degree: 2,
            max_certificate_degree: 5,
            max_unknowns: 400,
            max_poly_terms: 4_000,
        }
    }
}

impl Default for Limits {
    fn default() -> Limits {
        Limits::classical()
    }
}

/// The outcome of a creative-telescoping search.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TelescopingOutcome {
    /// A certificate was found. It is **not** verified — run
    /// [`crate::telescoping_check::check_certificate`] before believing it.
    Found(Box<TelescopingCertificate>),
    /// No certificate was found inside the ceilings. Nothing is claimed.
    Declined,
}

/// Search for a creative-telescoping certificate for `∑_k F(n,k)`, smallest
/// recurrence order first.
///
/// The result is the output of an unchecked search. Soundness lives entirely in
/// the independent checker.
#[must_use]
pub fn zeilberger(
    term: &HyperTerm,
    shift_var: &str,
    sum_var: &str,
    limits: &Limits,
) -> TelescopingOutcome {
    let Some(current) = term.shift_ratio(sum_var, 1) else {
        return TelescopingOutcome::Declined;
    };
    let parameters: Vec<String> = term
        .variables()
        .into_iter()
        .filter(|name| name != sum_var)
        .collect();
    if !parameters.iter().any(|name| name == shift_var) {
        return TelescopingOutcome::Declined;
    }
    let all_variables: Vec<String> = term.variables().into_iter().collect();

    let mut outer: Vec<RationalFunction> = Vec::new();
    for order in 0..=limits.max_order {
        let Some(next) = term.shift_ratio(shift_var, i64::try_from(order).unwrap_or(i64::MAX))
        else {
            return TelescopingOutcome::Declined;
        };
        outer.push(next);
        let Some(denominators) = lcm_of_denominators(&outer) else {
            continue;
        };
        for denominator_choice in denominator_ladder(&denominators, &current) {
            for certificate_degree in 0..=limits.max_certificate_degree {
                for recurrence_degree in 0..=limits.max_recurrence_degree {
                    let attempt = solve_ansatz(
                        &outer,
                        &current,
                        &denominators,
                        &denominator_choice,
                        &parameters,
                        &all_variables,
                        sum_var,
                        recurrence_degree,
                        certificate_degree,
                        limits,
                    );
                    if let Some((coefficients, numerator)) = attempt {
                        return finish(
                            term,
                            shift_var,
                            sum_var,
                            coefficients,
                            numerator,
                            denominator_choice,
                        );
                    }
                }
            }
        }
    }
    TelescopingOutcome::Declined
}

/// Assemble a certificate from a raw solution: drop trailing zero recurrence
/// coefficients and reduce `P/Q`.
fn finish(
    term: &HyperTerm,
    shift_var: &str,
    sum_var: &str,
    mut coefficients: Vec<MvPoly>,
    numerator: MvPoly,
    denominator: MvPoly,
) -> TelescopingOutcome {
    while coefficients.len() > 1 && coefficients.last().is_some_and(MvPoly::is_zero) {
        coefficients.pop();
    }
    if coefficients.iter().all(MvPoly::is_zero) {
        return TelescopingOutcome::Declined;
    }
    let Some(reduced) = (RationalFunction {
        numerator,
        denominator,
    })
    .reduced() else {
        return TelescopingOutcome::Declined;
    };
    TelescopingOutcome::Found(Box::new(TelescopingCertificate {
        term: term.clone(),
        shift_var: shift_var.to_owned(),
        sum_var: sum_var.to_owned(),
        recurrence: coefficients,
        certificate_numerator: reduced.numerator,
        certificate_denominator: reduced.denominator,
    }))
}

/// The least common multiple of the shift-ratio denominators seen so far.
fn lcm_of_denominators(ratios: &[RationalFunction]) -> Option<MvPoly> {
    let mut lcm = MvPoly::constant(Rational::integer(1));
    for ratio in ratios {
        let common = lcm.gcd(&ratio.denominator)?;
        lcm = lcm.mul(&ratio.denominator)?.exact_div(&common)?;
    }
    Some(lcm)
}

/// Candidate denominators `Q` for the certificate `R = P/Q`, in the order tried.
///
/// Enlarging `Q` never loses a certificate (a smaller true denominator is
/// absorbed into `P`), it only demands a larger degree bound on `P`; and any
/// factor depending on the shift variable alone is absorbed by the recurrence
/// coefficients, which is why the bare `1` is worth trying first.
fn denominator_ladder(denominators: &MvPoly, current: &RationalFunction) -> Vec<MvPoly> {
    let one = MvPoly::constant(Rational::integer(1));
    let mut ladder = vec![one.clone(), denominators.clone()];
    if let Some(with_current) = denominators.mul(&current.denominator) {
        ladder.push(with_current);
    }
    if let Some(squared) = denominators.pow(2) {
        ladder.push(squared);
    }
    ladder.dedup();
    ladder
}

/// Set up and solve one ansatz. Returns `(recurrence coefficients, P)`.
#[allow(clippy::too_many_arguments)]
fn solve_ansatz(
    outer: &[RationalFunction],
    current: &RationalFunction,
    denominators: &MvPoly,
    choice: &MvPoly,
    parameters: &[String],
    all_variables: &[String],
    sum_var: &str,
    recurrence_degree: u32,
    certificate_degree: u32,
    limits: &Limits,
) -> Option<(Vec<MvPoly>, MvPoly)> {
    let recurrence_monomials = monomials_up_to(parameters, recurrence_degree);
    let certificate_monomials = monomials_up_to(all_variables, certificate_degree);
    let unknowns = recurrence_monomials.len() * outer.len() + certificate_monomials.len();
    if unknowns == 0 || unknowns > limits.max_unknowns {
        return None;
    }

    let shifted_choice = shift_variable(choice, sum_var, 1)?;
    // Common multiplier clearing every denominator in (★).
    let recurrence_prefix = choice.mul(&shifted_choice)?.mul(&current.denominator)?;
    let capped = |poly: MvPoly| -> Option<MvPoly> {
        (poly.term_count() <= limits.max_poly_terms).then_some(poly)
    };

    let mut columns: Vec<MvPoly> = Vec::with_capacity(unknowns);
    for ratio in outer {
        let spread = denominators.exact_div(&ratio.denominator)?;
        let block = ratio
            .numerator
            .mul(&spread)?
            .mul(&recurrence_prefix)
            .and_then(capped)?;
        for mono in &recurrence_monomials {
            columns.push(capped(monomial_poly(mono).mul(&block)?)?);
        }
    }
    let advance_factor = current.numerator.mul(choice)?.mul(denominators)?;
    let retreat_factor = shifted_choice
        .mul(&current.denominator)?
        .mul(denominators)?;
    for mono in &certificate_monomials {
        let base = monomial_poly(mono);
        let advanced = shift_variable(&base, sum_var, 1)?.mul(&advance_factor)?;
        let column = base.mul(&retreat_factor)?.sub(&advanced)?;
        columns.push(capped(column)?);
    }

    let solution = solve_homogeneous(&columns, recurrence_monomials.len() * outer.len())?;
    let (recurrence_part, certificate_part) =
        solution.split_at(recurrence_monomials.len() * outer.len());
    let mut coefficients = Vec::with_capacity(outer.len());
    for block in recurrence_part.chunks(recurrence_monomials.len()) {
        coefficients.push(assemble(&recurrence_monomials, block)?);
    }
    let numerator = assemble(&certificate_monomials, certificate_part)?;
    Some((coefficients, numerator))
}

/// `Σ coefficient·monomial`.
fn assemble(monomials: &[Monomial], coefficients: &[Rational]) -> Option<MvPoly> {
    let mut poly = MvPoly::zero();
    for (mono, coeff) in monomials.iter().zip(coefficients.iter()) {
        poly = poly.add(&MvPoly::from_terms([(mono.clone(), *coeff)])?)?;
    }
    Some(poly)
}

/// A single monomial as a polynomial with coefficient one.
fn monomial_poly(mono: &Monomial) -> MvPoly {
    MvPoly::from_terms([(mono.clone(), Rational::integer(1))]).unwrap_or_else(MvPoly::zero)
}

/// Every monomial in `vars` of total degree at most `degree`, deterministically
/// ordered.
fn monomials_up_to(vars: &[String], degree: u32) -> Vec<Monomial> {
    let mut result: Vec<Monomial> = Vec::new();
    for exponents in exponent_vectors(vars.len(), degree) {
        let factors: Vec<(&str, u32)> = vars
            .iter()
            .map(String::as_str)
            .zip(exponents.iter().copied())
            .collect();
        result.push(Monomial::from_powers(&factors));
    }
    result.sort();
    result.dedup();
    result
}

/// Every length-`count` exponent vector with total degree at most `degree`.
fn exponent_vectors(count: usize, degree: u32) -> Vec<Vec<u32>> {
    if count == 0 {
        return vec![Vec::new()];
    }
    let mut result = Vec::new();
    for head in 0..=degree {
        for mut tail in exponent_vectors(count - 1, degree - head) {
            let mut row = Vec::with_capacity(count);
            row.push(head);
            row.append(&mut tail);
            result.push(row);
        }
    }
    result
}

/// Find a nontrivial `u` with `Σ uᵢ·columns[i] ≡ 0` whose first
/// `recurrence_width` entries are not all zero.
///
/// Every column is a polynomial; requiring the combination to vanish gives one
/// linear equation per monomial appearing anywhere. The system is solved in
/// exact bignum rationals — the coefficients of a Zeilberger ansatz outgrow
/// `i128` well before the certificate does — and the answer is scaled back to a
/// primitive integer vector.
fn solve_homogeneous(columns: &[MvPoly], recurrence_width: usize) -> Option<Vec<Rational>> {
    let mut monomials: BTreeSet<Monomial> = BTreeSet::new();
    for column in columns {
        for (mono, _) in column.terms() {
            monomials.insert(mono.clone());
        }
    }
    let index: BTreeMap<&Monomial, usize> = monomials.iter().zip(0..).collect();
    let mut matrix: Vec<Vec<BigRational>> =
        vec![vec![BigRational::zero(); columns.len()]; monomials.len()];
    for (position, column) in columns.iter().enumerate() {
        for (mono, coeff) in column.terms() {
            let Some(row) = index.get(mono) else { continue };
            matrix[*row][position] = to_big(*coeff);
        }
    }
    for vector in nullspace(&matrix, columns.len()) {
        if vector[..recurrence_width].iter().all(BigRational::is_zero) {
            continue;
        }
        if let Some(scaled) = primitive_integer_vector(&vector) {
            return Some(scaled);
        }
    }
    None
}

/// `BigRational` view of an exact `i128` rational.
fn to_big(value: Rational) -> BigRational {
    BigRational::new(
        BigInt::from(value.numerator()),
        BigInt::from(value.denominator()),
    )
}

/// A basis of the null space of `matrix` (rows are equations, `columns`
/// unknowns), by exact Gauss–Jordan elimination.
fn nullspace(matrix: &[Vec<BigRational>], columns: usize) -> Vec<Vec<BigRational>> {
    let mut rows: Vec<Vec<BigRational>> = matrix.to_vec();
    let mut pivot_row_of_column: Vec<Option<usize>> = vec![None; columns];
    let mut rank = 0usize;
    for column in 0..columns {
        let Some(found) = (rank..rows.len()).find(|index| !rows[*index][column].is_zero()) else {
            continue;
        };
        rows.swap(rank, found);
        let inverse = rows[rank][column].recip();
        for entry in &mut rows[rank] {
            *entry = entry.clone() * inverse.clone();
        }
        for index in 0..rows.len() {
            if index == rank || rows[index][column].is_zero() {
                continue;
            }
            let factor = rows[index][column].clone();
            let pivot = rows[rank].clone();
            for (entry, above) in rows[index].iter_mut().zip(pivot.iter()).take(columns) {
                *entry = entry.clone() - above.clone() * factor.clone();
            }
        }
        pivot_row_of_column[column] = Some(rank);
        rank += 1;
        if rank == rows.len() {
            break;
        }
    }
    let mut basis = Vec::new();
    for free in 0..columns {
        if pivot_row_of_column[free].is_some() {
            continue;
        }
        let mut vector = vec![BigRational::zero(); columns];
        vector[free] = BigRational::one();
        for (bound, pivot) in pivot_row_of_column.iter().enumerate() {
            if let Some(row) = pivot {
                vector[bound] = -rows[*row][free].clone();
            }
        }
        basis.push(vector);
    }
    basis
}

/// Rescale an exact rational vector to primitive integers that fit `i128`.
fn primitive_integer_vector(vector: &[BigRational]) -> Option<Vec<Rational>> {
    let mut scale = BigInt::from(1);
    for entry in vector {
        let denominator = entry.denom().clone();
        let common = big_gcd(&scale, &denominator);
        scale = scale / common * denominator;
    }
    let scaled: Vec<BigInt> = vector
        .iter()
        .map(|entry| (entry * BigRational::from_integer(scale.clone())).to_integer())
        .collect();
    let mut content = BigInt::zero();
    for entry in &scaled {
        content = big_gcd(&content, entry);
    }
    if content.is_zero() {
        return None;
    }
    let leading = scaled.iter().find(|entry| !entry.is_zero())?;
    let sign = if leading.is_negative() {
        -BigInt::one()
    } else {
        BigInt::one()
    };
    scaled
        .iter()
        .map(|entry| {
            i128::try_from(entry / &content * &sign)
                .ok()
                .map(Rational::integer)
        })
        .collect()
}

/// Greatest common divisor of two big integers, as a non-negative value.
fn big_gcd(left: &BigInt, right: &BigInt) -> BigInt {
    let mut current = left.abs();
    let mut next = right.abs();
    while !next.is_zero() {
        let remainder = &current % &next;
        current = next;
        next = remainder;
    }
    current
}

/// `Γ(x+1)`, i.e. `x!`, as a factor with the given integer power.
#[must_use]
pub fn factorial_factor(form: LinearForm, exponent: i32) -> Factor {
    let shifted = LinearForm {
        constant: form.constant.saturating_add(1),
        coefficients: form.coefficients,
    };
    Factor::Gamma {
        form: shifted,
        exponent,
    }
}

/// The binomial coefficient `C(upper, lower)` as the three `Γ` factors
/// `Γ(u+1)·Γ(l+1)⁻¹·Γ(u−l+1)⁻¹`, each raised to `power`.
#[must_use]
pub fn binomial_factors(upper: &LinearForm, lower: &LinearForm, power: i32) -> Vec<Factor> {
    let mut difference: BTreeMap<String, i64> = upper.coefficients.clone();
    for (name, value) in &lower.coefficients {
        let slot = difference.entry(name.clone()).or_insert(0);
        *slot = slot.saturating_sub(*value);
    }
    difference.retain(|_, value| *value != 0);
    let difference = LinearForm {
        coefficients: difference,
        constant: upper.constant.saturating_sub(lower.constant),
    };
    vec![
        factorial_factor(upper.clone(), power),
        factorial_factor(lower.clone(), -power),
        factorial_factor(difference, -power),
    ]
}

#[cfg(test)]
mod tests {
    use super::{
        Factor, HyperTerm, Limits, LinearForm, TelescopingOutcome, binomial_factors,
        shift_variable, zeilberger,
    };
    use crate::mvpoly::MvPoly;
    use axeyum_ir::Rational;

    fn linear(terms: &[(&str, i64)], constant: i64) -> LinearForm {
        LinearForm::new(terms, constant)
    }

    /// `C(n,k)` as a term.
    fn binomial_n_k(power: i32) -> Vec<Factor> {
        binomial_factors(&linear(&[("n", 1)], 0), &linear(&[("k", 1)], 0), power)
    }

    #[test]
    fn binomial_shift_ratios_match_hand_computation() {
        let term = HyperTerm::new(binomial_n_k(1));
        // C(n,k+1)/C(n,k) = (n−k)/(k+1).
        let current = term.shift_ratio("k", 1).expect("ratio");
        let expected_num = MvPoly::var("n").sub(&MvPoly::var("k")).unwrap();
        let expected_den = MvPoly::var("k")
            .add(&MvPoly::constant(Rational::integer(1)))
            .unwrap();
        assert_eq!(current.numerator, expected_num);
        assert_eq!(current.denominator, expected_den);
        // C(n+1,k)/C(n,k) = (n+1)/(n−k+1).
        let outer = term.shift_ratio("n", 1).expect("ratio");
        assert_eq!(
            outer.numerator,
            MvPoly::var("n")
                .add(&MvPoly::constant(Rational::integer(1)))
                .unwrap()
        );
        assert_eq!(
            outer.denominator,
            MvPoly::var("n")
                .sub(&MvPoly::var("k"))
                .unwrap()
                .add(&MvPoly::constant(Rational::integer(1)))
                .unwrap()
        );
    }

    #[test]
    fn shift_variable_expands_a_binomial() {
        // (k² ) with k → k+1 is k² + 2k + 1.
        let poly = MvPoly::var("k").pow(2).unwrap();
        let shifted = shift_variable(&poly, "k", 1).unwrap();
        let expected = MvPoly::var("k")
            .add(&MvPoly::constant(Rational::integer(1)))
            .unwrap()
            .pow(2)
            .unwrap();
        assert_eq!(shifted, expected);
    }

    #[test]
    fn central_binomial_sum_gets_an_order_one_recurrence() {
        let term = HyperTerm::new(binomial_n_k(1));
        let TelescopingOutcome::Found(certificate) =
            zeilberger(&term, "n", "k", &Limits::classical())
        else {
            panic!("no certificate for the binomial row sum");
        };
        assert_eq!(certificate.order(), 1);
    }

    #[test]
    fn a_starved_order_ceiling_declines() {
        let term = HyperTerm::new(binomial_n_k(2));
        let starved = Limits {
            max_certificate_degree: 0,
            max_recurrence_degree: 0,
            ..Limits::classical()
        };
        assert_eq!(
            zeilberger(&term, "n", "k", &starved),
            TelescopingOutcome::Declined
        );
    }
}
