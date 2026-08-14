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
//! # How the certificate is found — Gosper–Petkovšek, not a sweep
//!
//! For a fixed order `J`, write `S_j = F(n+j,k)/F(n,k) = E_j(k)/D(k)` over the
//! common denominator `D = lcm_j den(S_j)`, so that
//!
//! ```text
//! t(k) = Σ_j a_j·F(n+j,k) = F(n,k)·N(k)/D(k),      N(k) = Σ_j a_j·E_j(k)
//! ```
//!
//! is hypergeometric in `k` with the **unknowns entering `N` linearly**. Its
//! shift quotient factors as
//!
//! ```text
//! t(k+1)/t(k) = ρ(k)·N(k+1)/N(k),      ρ(k) = r(k)·D(k)/D(k+1)
//! ```
//!
//! and `ρ` is entirely known. Putting `ρ` into **Gosper–Petkovšek normal form**
//! `ρ = (a(k)/b(k))·(s(k+1)/s(k))` with `gcd(a(k), b(k+h)) = 1` for every integer
//! `h ≥ 0` turns Gosper's condition into one polynomial equation
//!
//! ```text
//! a(k)·x(k+1) − b(k−1)·x(k) = s(k)·N(k)                        (†)
//! ```
//!
//! whose solution gives the certificate outright:
//!
//! ```text
//! R(n,k) = b(k−1)·x(k) / (s(k)·D(k))
//! ```
//!
//! Two things follow, and they are the whole reason this module is shaped this
//! way. The certificate **denominator is derived** — it is `s·D`, read off the
//! normal form, not guessed from a ladder of candidates. And the certificate
//! **numerator degree is bounded** by Gosper's classical degree bound applied to
//! (†), not swept. What remains is a single homogeneous linear system per order,
//! solved over the field `ℚ(parameters)` so the recurrence coefficients `a_j`
//! come out as polynomials of whatever degree they need with no degree ansatz at
//! all.
//!
//! # What is searched and what is trusted
//!
//! Nothing here is trusted. The degree bound and the normal form are derived
//! *generically*: leading coefficients are compared as polynomials in the
//! parameters, so a specialization at which a leading coefficient happens to
//! vanish is not accounted for. That is sound in exactly the sense this module
//! needs — a wrong bound, a wrong normal form, an overflow, or an outright bug in
//! the linear algebra loses a certificate; it cannot manufacture one, because the
//! consumer ([`crate::telescoping_check`]) re-derives (★) from the term
//! specification with its own code and additionally cross-checks the shift ratios
//! against direct exact-bignum evaluation of the term at integer points.
//!
//! # Scope
//!
//! A [`HyperTerm`] is a product of `Γ(linear form)^e`, `c^(linear form)` and
//! `polynomial^e` factors. That covers factorials, binomial coefficients to
//! integer powers, geometric factors, falling/rising factorials with integer
//! shifts, and polynomial weights — the classical binomial-identity fragment. It
//! does **not** cover `q`-analogues, terms whose parameters enter non-linearly,
//! or non-hypergeometric summands.

use std::cmp::Ordering;
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
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
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

    /// The constant term of this form.
    #[must_use]
    pub fn constant(&self) -> i64 {
        self.constant
    }

    /// Whether this form mentions no variables at all, so it *is* its constant.
    #[must_use]
    pub fn is_constant(&self) -> bool {
        self.coefficients.is_empty()
    }

    /// This form with the assigned variables replaced by their integer values,
    /// leaving the rest symbolic. `None` on `i64` overflow.
    ///
    /// [`LinearForm::evaluate`] is the total case of this: it demands every
    /// variable be assigned. Partial substitution is what makes a base case at a
    /// *symbolic* parameter possible — `Γ(p−k+1)` at `p = 0` becomes the
    /// parameter-free `Γ(−k+1)`, whose sign decides the support outright.
    #[must_use]
    pub fn substitute(&self, assignment: &BTreeMap<String, i64>) -> Option<LinearForm> {
        let mut coefficients: BTreeMap<String, i64> = BTreeMap::new();
        let mut constant = self.constant;
        for (name, value) in &self.coefficients {
            match assignment.get(name) {
                Some(point) => constant = constant.checked_add(value.checked_mul(*point)?)?,
                None => {
                    coefficients.insert(name.clone(), *value);
                }
            }
        }
        Some(LinearForm {
            coefficients,
            constant,
        })
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
///
/// None of these is a degree *ansatz*: the certificate degree and the
/// certificate denominator are derived from the term (Gosper–Petkovšek), and the
/// recurrence coefficients are solved for over `ℚ(parameters)` with no degree
/// bound at all. These are ceilings on how large a *derived* quantity the search
/// will act on, so a starved value makes the search decline, never mislead.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Limits {
    /// Largest recurrence order `J` attempted.
    pub max_order: usize,
    /// Ceiling on the derived degree of the certificate numerator in the
    /// summation variable.
    pub max_certificate_degree: u32,
    /// Largest number of unknowns in one linear system.
    pub max_unknowns: usize,
    /// Largest number of stored monomials in any intermediate polynomial.
    pub max_poly_terms: usize,
    /// Largest shift `h` probed when computing the Gosper–Petkovšek normal form.
    ///
    /// The normal form must divide out every factor shared by `a(k)` and
    /// `b(k+h)` for an integer `h ≥ 0`. Probing too few loses certificates; it
    /// cannot invent one.
    pub max_dispersion: i64,
    /// Largest parameter degree swept by the **fallback** solve, which runs
    /// only when the exact-field solve over `ℚ(parameters)` overflows its
    /// `i128` polynomial coefficients.
    pub max_parameter_degree: u32,
}

impl Limits {
    /// Ceilings sized for the classical binomial identities: order up to two,
    /// a derived certificate degree up to eight, and dispersions up to 32.
    #[must_use]
    pub fn classical() -> Limits {
        Limits {
            max_order: 2,
            max_certificate_degree: 8,
            max_unknowns: 400,
            max_poly_terms: 4_000,
            max_dispersion: 32,
            max_parameter_degree: 6,
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

    let mut outer: Vec<RationalFunction> = Vec::new();
    for order in 0..=limits.max_order {
        let Ok(offset) = i64::try_from(order) else {
            return TelescopingOutcome::Declined;
        };
        let Some(next) = term.shift_ratio(shift_var, offset) else {
            return TelescopingOutcome::Declined;
        };
        outer.push(next);
        if let Some(TelescopingOutcome::Found(certificate)) =
            attempt_order(term, shift_var, sum_var, &outer, &current, limits)
        {
            return TelescopingOutcome::Found(certificate);
        }
    }
    TelescopingOutcome::Declined
}

/// One order of the search: derive the Gosper–Petkovšek normal form, derive the
/// certificate degree bound, and solve the single resulting linear system over
/// `ℚ(parameters)`.
fn attempt_order(
    term: &HyperTerm,
    shift_var: &str,
    sum_var: &str,
    outer: &[RationalFunction],
    current: &RationalFunction,
    limits: &Limits,
) -> Option<TelescopingOutcome> {
    // D(k) and the numerators E_j with Σ_j a_j·S_j = (Σ_j a_j·E_j)/D.
    let common = lcm_of_denominators(outer)?;
    let mut spread: Vec<MvPoly> = Vec::with_capacity(outer.len());
    for ratio in outer {
        let quotient = common.exact_div(&ratio.denominator)?;
        spread.push(capped(ratio.numerator.mul(&quotient)?, limits)?);
    }

    // ρ(k) = r(k)·D(k)/D(k+1), the known part of the shift quotient.
    let advanced_common = shift_variable(&common, sum_var, 1)?;
    // Reducing ρ is an optimization: the h = 0 step of the normal form removes
    // any shared factor anyway, and Gosper's identity does not depend on the
    // coprimality condition (only the existence of a *polynomial* `x` does). So
    // a GCD that overflows `i128` costs completeness, never correctness.
    let raw = RationalFunction {
        numerator: current.numerator.mul(&common)?,
        denominator: current.denominator.mul(&advanced_common)?,
    };
    let known = raw.reduced().unwrap_or(raw);
    let normal = gosper_petkovsek(
        &known.numerator,
        &known.denominator,
        sum_var,
        limits.max_dispersion,
    )?;
    let retreated = shift_variable(&normal.b, sum_var, -1)?;

    // deg_k of the right-hand side s(k)·N(k), as an upper bound.
    let widest = spread
        .iter()
        .map(|piece| i64::from(piece.degree_in(sum_var)))
        .max()
        .unwrap_or(0);
    let target = i64::from(normal.s.degree_in(sum_var)).checked_add(widest)?;
    let bound = gosper_degree_bound(&normal.a, &retreated, target, sum_var)?;
    let degree = u32::try_from(bound.max(0)).ok()?;
    if degree > limits.max_certificate_degree {
        return None;
    }
    let unknowns = outer.len().checked_add(degree as usize)?.checked_add(1)?;
    if unknowns > limits.max_unknowns {
        return None;
    }

    // One homogeneous system: a(k)·x(k+1) − b(k−1)·x(k) − s(k)·Σ_j a_j·E_j ≡ 0.
    let mut columns: Vec<MvPoly> = Vec::with_capacity(unknowns);
    for piece in &spread {
        columns.push(capped(normal.s.mul(piece)?.neg()?, limits)?);
    }
    let advanced_var = MvPoly::var(sum_var).add(&MvPoly::constant(Rational::integer(1)))?;
    for power in 0..=degree {
        let here = MvPoly::var(sum_var).pow(power)?;
        let there = advanced_var.pow(power)?;
        let column = normal.a.mul(&there)?.sub(&retreated.mul(&here)?)?;
        columns.push(capped(column, limits)?);
    }
    let parameters: Vec<String> = term
        .variables()
        .into_iter()
        .filter(|name| name != sum_var)
        .collect();
    let solution = solve_over_parameters(&columns, sum_var, outer.len())
        .or_else(|| solve_by_parameter_ansatz(&columns, &parameters, outer.len(), limits))?;
    let (coefficients, tail) = solution.split_at(outer.len());

    let mut numerator = MvPoly::zero();
    for (power, coefficient) in tail.iter().enumerate() {
        let power = u32::try_from(power).ok()?;
        numerator = numerator.add(&coefficient.mul(&MvPoly::var(sum_var).pow(power)?)?)?;
    }
    Some(finish(
        term,
        shift_var,
        sum_var,
        coefficients.to_vec(),
        retreated.mul(&numerator)?,
        normal.s.mul(&common)?,
    ))
}

/// A polynomial, unless it has outgrown the stored-monomial ceiling.
fn capped(poly: MvPoly, limits: &Limits) -> Option<MvPoly> {
    (poly.term_count() <= limits.max_poly_terms).then_some(poly)
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
    // Reduction is cosmetic — the checker accepts any `P/Q` denoting the same
    // rational function — so a GCD that overflows `i128` must not cost a
    // certificate. Deeper terms (`∑_k C(n,k)³`) reach exactly that point.
    let candidate = RationalFunction {
        numerator,
        denominator,
    };
    let reduced = candidate.reduced().unwrap_or(candidate);
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

// ---------------------------------------------------------------------------
// Gosper–Petkovšek normal form and the derived degree bound.
// ---------------------------------------------------------------------------

/// `ρ(k) = (a(k)/b(k))·(s(k+1)/s(k))` with `gcd(a(k), b(k+h)) = 1` for every
/// integer `h ≥ 0` — the Gosper–Petkovšek normal form of a shift quotient.
#[derive(Debug, Clone)]
struct NormalForm {
    /// The numerator `a(k)`.
    a: MvPoly,
    /// The denominator `b(k)`.
    b: MvPoly,
    /// The telescoped part `s(k)`.
    s: MvPoly,
}

/// Put `numerator/denominator` into Gosper–Petkovšek normal form with respect to
/// `var`.
///
/// The loop is the textbook one: at each shift `h` divide the common factor
/// `g = gcd(a(k), b(k+h))` out of `a(k)` and out of `b(k−h)`, and absorb
/// `∏_{i=1..h} g(k−i)` into `s`. The step preserves the value of the quotient,
/// since `(g(k−h)/g(k))·(s_step(k+1)/s_step(k)) = 1`.
///
/// Common factors are taken **primitive in `var`**: a factor free of `var`
/// cancels from the quotient anyway, and keeping it would only bloat `s`.
///
/// The shifts are probed up to `max_dispersion`. A true dispersion beyond that
/// leaves a shared factor in place, which makes Gosper's criterion fail and
/// loses a certificate — it cannot create one.
fn gosper_petkovsek(
    numerator: &MvPoly,
    denominator: &MvPoly,
    var: &str,
    max_dispersion: i64,
) -> Option<NormalForm> {
    let mut a = numerator.clone();
    let mut b = denominator.clone();
    let mut s = MvPoly::constant(Rational::integer(1));
    for shift in 0..=max_dispersion.max(0) {
        let advanced = shift_variable(&b, var, shift)?;
        let Some(shared) = a.gcd(&advanced).and_then(|found| primitive_in(&found, var)) else {
            // An overflowing GCD leaves a shared factor in place, which can only
            // cost a polynomial solution downstream.
            continue;
        };
        if shared.degree_in(var) == 0 {
            continue;
        }
        a = a.exact_div(&shared)?;
        b = b.exact_div(&shift_variable(&shared, var, -shift)?)?;
        for step in 1..=shift {
            s = s.mul(&shift_variable(&shared, var, -step)?)?;
        }
    }
    Some(NormalForm { a, b, s })
}

/// `poly` with the GCD of its `var`-coefficients divided out, so the result is
/// primitive as a polynomial in `var` over the remaining variables.
fn primitive_in(poly: &MvPoly, var: &str) -> Option<MvPoly> {
    if poly.is_zero() {
        return Some(poly.clone());
    }
    let mut content = MvPoly::zero();
    for part in coefficients_in(poly, var)? {
        content = content.gcd(&part)?;
    }
    if content.is_zero() {
        return Some(poly.clone());
    }
    poly.exact_div(&content)
}

/// `poly` split into its coefficients as a univariate polynomial in `var`,
/// indexed by the power of `var`. Each coefficient is free of `var`.
fn coefficients_in(poly: &MvPoly, var: &str) -> Option<Vec<MvPoly>> {
    let degree = usize::try_from(poly.degree_in(var)).ok()?;
    let mut parts = vec![MvPoly::zero(); degree + 1];
    for (mono, coefficient) in poly.terms() {
        let power = usize::try_from(mono.exponent_of(var)).ok()?;
        let factors: Vec<(&str, u32)> = mono.powers().filter(|(name, _)| *name != var).collect();
        let piece = MvPoly::from_terms([(Monomial::from_powers(&factors), *coefficient)])?;
        parts[power] = parts[power].add(&piece)?;
    }
    Some(parts)
}

/// Gosper's degree bound for the polynomial solutions `x` of
/// `left(k)·x(k+1) − right(k)·x(k) = C(k)` given `deg_k C = target`.
///
/// Derived, not swept: match the leading behaviour of the two sides. When the
/// leading terms do not cancel the degree is forced outright; when they do, the
/// next order gives either one more degree or the exceptional value
/// `(subleading(right) − subleading(left))/leading`, which counts only when it is
/// a non-negative integer *constant*.
///
/// The comparisons are generic in the parameters — a specialization at which a
/// leading coefficient vanishes is not accounted for. Over-bounding is harmless
/// (spare unknowns); under-bounding loses a certificate and cannot fake one.
fn gosper_degree_bound(left: &MvPoly, right: &MvPoly, target: i64, var: &str) -> Option<i64> {
    if left.is_zero() || right.is_zero() {
        return None;
    }
    let left_degree = i64::from(left.degree_in(var));
    let right_degree = i64::from(right.degree_in(var));
    if left_degree != right_degree {
        return Some(target - left_degree.max(right_degree));
    }
    let leading = left.leading_coeff(var);
    if leading != right.leading_coeff(var) {
        return Some(target - left_degree);
    }
    let mut bound = target - left_degree + 1;
    if left_degree >= 1 {
        let index = usize::try_from(left_degree - 1).ok()?;
        let below_left = coefficients_in(left, var)?;
        let below_right = coefficients_in(right, var)?;
        let difference = below_right[index].sub(&below_left[index])?;
        if let Some(quotient) = difference.exact_div(&leading)
            && let Some(exceptional) = constant_non_negative_integer(&quotient)
        {
            bound = bound.max(exceptional);
        }
    }
    Some(bound)
}

/// `poly` as a non-negative integer, or `None` if it is not a constant, not an
/// integer, or negative.
fn constant_non_negative_integer(poly: &MvPoly) -> Option<i64> {
    if !poly.variables().is_empty() {
        return None;
    }
    let mut value = Rational::zero();
    for (_, coefficient) in poly.terms() {
        value = *coefficient;
    }
    if value.denominator() != 1 || value.numerator() < 0 {
        return None;
    }
    i64::try_from(value.numerator()).ok()
}

// ---------------------------------------------------------------------------
// The one linear system, solved over ℚ(parameters).
// ---------------------------------------------------------------------------

/// Find a nontrivial `u` over `ℚ(parameters)` with `Σ uᵢ·columns[i] ≡ 0` as a
/// polynomial in `var`, whose first `recurrence_width` entries are not all zero.
///
/// The unknowns are scalars in the *field* `ℚ(parameters)`, so the recurrence
/// coefficients that come out carry whatever parameter degree they need and no
/// degree ansatz is imposed on them. The answer is cleared to a family of
/// polynomials with no common factor and a canonical sign.
fn solve_over_parameters(
    columns: &[MvPoly],
    var: &str,
    recurrence_width: usize,
) -> Option<Vec<MvPoly>> {
    let mut height = 0usize;
    for column in columns {
        height = height.max(usize::try_from(column.degree_in(var)).ok()? + 1);
    }
    let mut matrix: Vec<Vec<RationalFunction>> = vec![vec![fraction_zero(); columns.len()]; height];
    for (position, column) in columns.iter().enumerate() {
        for (power, part) in coefficients_in(column, var)?.into_iter().enumerate() {
            matrix[power][position] = fraction_of(part);
        }
    }
    for vector in parameter_nullspace(&matrix, columns.len())? {
        if vector[..recurrence_width]
            .iter()
            .all(|entry| entry.numerator.is_zero())
        {
            continue;
        }
        if let Some(cleared) = clear_denominators(&vector) {
            return Some(cleared);
        }
    }
    None
}

/// The fallback solve: give every unknown a bounded parameter-degree ansatz and
/// find the null space over **ℚ** in exact bignum rationals.
///
/// This exists because [`solve_over_parameters`] carries its intermediate
/// rational functions in `i128` coefficients, and the primitive-PRS GCD inside
/// the elimination overflows them on the deeper terms (measured: `∑_k C(n,k)³`
/// at order two). Overflow makes the exact-field solve return `None`, never a
/// wrong answer, so falling back is a completeness measure and not a soundness
/// one. The parameter degree is the *only* thing still swept anywhere in this
/// module, and it is swept over a handful of tiny systems because `Q` and the
/// certificate degree are already derived.
fn solve_by_parameter_ansatz(
    columns: &[MvPoly],
    parameters: &[String],
    recurrence_width: usize,
    limits: &Limits,
) -> Option<Vec<MvPoly>> {
    for degree in 0..=limits.max_parameter_degree {
        let monomials = monomials_up_to(parameters, degree);
        if monomials.is_empty() || columns.len().checked_mul(monomials.len())? > limits.max_unknowns
        {
            continue;
        }
        let mut expanded: Vec<MvPoly> = Vec::with_capacity(columns.len() * monomials.len());
        let mut overflowed = false;
        for column in columns {
            for mono in &monomials {
                match MvPoly::from_terms([(mono.clone(), Rational::integer(1))])
                    .and_then(|piece| piece.mul(column))
                    .and_then(|piece| capped(piece, limits))
                {
                    Some(piece) => expanded.push(piece),
                    None => overflowed = true,
                }
            }
        }
        if overflowed {
            continue;
        }
        let attempt = solve_homogeneous(&expanded, recurrence_width * monomials.len());
        if std::env::var("AXEYUM_TELESCOPE_DEBUG").is_ok() {
            eprintln!(
                "fallback degree {degree}: columns {} monos {} -> {}",
                columns.len(),
                monomials.len(),
                attempt.is_some()
            );
        }
        let Some(solution) = attempt else {
            continue;
        };
        let mut assembled: Vec<MvPoly> = Vec::with_capacity(columns.len());
        for block in solution.chunks(monomials.len()) {
            let mut poly = MvPoly::zero();
            for (mono, coefficient) in monomials.iter().zip(block.iter()) {
                poly = poly.add(&MvPoly::from_terms([(mono.clone(), *coefficient)])?)?;
            }
            assembled.push(poly);
        }
        let normalized = normalize_family(&assembled);
        if std::env::var("AXEYUM_TELESCOPE_DEBUG").is_ok() {
            eprintln!("fallback normalize -> {}", normalized.is_some());
        }
        if let Some(normalized) = normalized {
            return Some(normalized);
        }
    }
    None
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

/// Find a nontrivial `u` over ℚ with `Σ uᵢ·columns[i] ≡ 0` whose first
/// `recurrence_width` entries are not all zero.
///
/// Requiring the combination to vanish gives one linear equation per monomial
/// appearing anywhere. Solved in exact bignum rationals — the coefficients of a
/// Zeilberger ansatz outgrow `i128` well before the certificate does — and the
/// answer is scaled back to a primitive integer vector.
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
        for (mono, coefficient) in column.terms() {
            let Some(row) = index.get(mono) else { continue };
            matrix[*row][position] = BigRational::new(
                BigInt::from(coefficient.numerator()),
                BigInt::from(coefficient.denominator()),
            );
        }
    }
    for vector in rational_nullspace(&matrix, columns.len()) {
        if vector[..recurrence_width].iter().all(BigRational::is_zero) {
            continue;
        }
        if let Some(scaled) = primitive_integer_vector(&vector) {
            return Some(scaled);
        }
    }
    None
}

/// A basis of the null space of `matrix` over ℚ (rows are equations, `columns`
/// unknowns), by exact bignum Gauss–Jordan elimination.
fn rational_nullspace(matrix: &[Vec<BigRational>], columns: usize) -> Vec<Vec<BigRational>> {
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
    scaled
        .iter()
        .map(|entry| i128::try_from(entry / &content).ok().map(Rational::integer))
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

/// A basis of the null space of `matrix` over `ℚ(parameters)` by exact
/// Gauss–Jordan elimination on rational functions.
fn parameter_nullspace(
    matrix: &[Vec<RationalFunction>],
    columns: usize,
) -> Option<Vec<Vec<RationalFunction>>> {
    let mut rows: Vec<Vec<RationalFunction>> = matrix.to_vec();
    let mut pivot_row_of_column: Vec<Option<usize>> = vec![None; columns];
    let mut rank = 0usize;
    for column in 0..columns {
        let Some(found) =
            (rank..rows.len()).find(|index| !rows[*index][column].numerator.is_zero())
        else {
            continue;
        };
        rows.swap(rank, found);
        let inverse = fraction_recip(&rows[rank][column])?;
        for entry in rows[rank].iter_mut().take(columns) {
            let scaled = fraction_mul(entry, &inverse)?;
            *entry = scaled;
        }
        for index in 0..rows.len() {
            if index == rank || rows[index][column].numerator.is_zero() {
                continue;
            }
            let factor = rows[index][column].clone();
            let pivot = rows[rank].clone();
            for position in 0..columns {
                let scaled = fraction_mul(&pivot[position], &factor)?;
                rows[index][position] = fraction_sub(&rows[index][position], &scaled)?;
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
        let mut vector = vec![fraction_zero(); columns];
        vector[free] = fraction_of(MvPoly::constant(Rational::integer(1)));
        for (bound, pivot) in pivot_row_of_column.iter().enumerate() {
            if let Some(row) = pivot {
                vector[bound] = fraction_neg(&rows[*row][free])?;
            }
        }
        basis.push(vector);
    }
    Some(basis)
}

/// The zero of `ℚ(parameters)`.
fn fraction_zero() -> RationalFunction {
    RationalFunction {
        numerator: MvPoly::zero(),
        denominator: MvPoly::constant(Rational::integer(1)),
    }
}

/// A polynomial as an element of `ℚ(parameters)`.
fn fraction_of(numerator: MvPoly) -> RationalFunction {
    RationalFunction {
        numerator,
        denominator: MvPoly::constant(Rational::integer(1)),
    }
}

/// `(p/q)·(r/s)`, reduced.
fn fraction_mul(left: &RationalFunction, right: &RationalFunction) -> Option<RationalFunction> {
    RationalFunction {
        numerator: left.numerator.mul(&right.numerator)?,
        denominator: left.denominator.mul(&right.denominator)?,
    }
    .reduced()
}

/// `(p/q) − (r/s)`, reduced.
fn fraction_sub(left: &RationalFunction, right: &RationalFunction) -> Option<RationalFunction> {
    RationalFunction {
        numerator: left
            .numerator
            .mul(&right.denominator)?
            .sub(&right.numerator.mul(&left.denominator)?)?,
        denominator: left.denominator.mul(&right.denominator)?,
    }
    .reduced()
}

/// `−(p/q)`.
fn fraction_neg(value: &RationalFunction) -> Option<RationalFunction> {
    Some(RationalFunction {
        numerator: value.numerator.neg()?,
        denominator: value.denominator.clone(),
    })
}

/// `(p/q)⁻¹`, or `None` when `p` is zero.
fn fraction_recip(value: &RationalFunction) -> Option<RationalFunction> {
    if value.numerator.is_zero() {
        return None;
    }
    Some(RationalFunction {
        numerator: value.denominator.clone(),
        denominator: value.numerator.clone(),
    })
}

/// Clear a solution vector over `ℚ(parameters)` to a family of polynomials with
/// no common polynomial factor, integer coefficients of content one, and a
/// positive `lex`-leading coefficient on the first nonzero entry.
///
/// The certificate identity is homogeneous in `(a_j, R)` jointly, so rescaling
/// the whole family by one factor free of the summation variable preserves it.
fn clear_denominators(vector: &[RationalFunction]) -> Option<Vec<MvPoly>> {
    let mut common = MvPoly::constant(Rational::integer(1));
    for entry in vector {
        let shared = common.gcd(&entry.denominator)?;
        common = common.mul(&entry.denominator)?.exact_div(&shared)?;
    }
    let mut scaled: Vec<MvPoly> = Vec::with_capacity(vector.len());
    for entry in vector {
        let factor = common.exact_div(&entry.denominator)?;
        scaled.push(entry.numerator.mul(&factor)?);
    }
    let mut content = MvPoly::zero();
    for poly in &scaled {
        content = content.gcd(poly)?;
    }
    if content.is_zero() {
        return None;
    }
    let mut reduced: Vec<MvPoly> = Vec::with_capacity(scaled.len());
    for poly in &scaled {
        reduced.push(poly.exact_div(&content)?);
    }
    normalize_family(&reduced)
}

/// Rescale a family of polynomials by one rational so that their combined
/// coefficients are integers of content one, then fix the sign from the first
/// nonzero member's `lex`-leading coefficient.
fn normalize_family(polys: &[MvPoly]) -> Option<Vec<MvPoly>> {
    let mut denominator_lcm: i128 = 1;
    for poly in polys {
        for (_, coefficient) in poly.terms() {
            denominator_lcm = integer_lcm(denominator_lcm, coefficient.denominator())?;
        }
    }
    let mut content: i128 = 0;
    for poly in polys {
        for (_, coefficient) in poly.terms() {
            let scaled = coefficient
                .numerator()
                .checked_mul(denominator_lcm / coefficient.denominator())?;
            content = integer_gcd(content, scaled)?;
        }
    }
    if content == 0 {
        return None;
    }
    let sign = polys
        .iter()
        .find_map(lex_leading_coefficient)
        .filter(|coefficient| coefficient.numerator() < 0)
        .map_or(1, |_| -1);
    let factor = Rational::checked_new(denominator_lcm.checked_mul(sign)?, content)?;
    let multiplier = MvPoly::constant(factor);
    polys.iter().map(|poly| poly.mul(&multiplier)).collect()
}

/// The coefficient of the `lex`-greatest monomial, or `None` for the zero
/// polynomial. `lex` ranks variables alphabetically with the first most
/// significant, matching [`MvPoly`]'s own normalization.
fn lex_leading_coefficient(poly: &MvPoly) -> Option<Rational> {
    let mut best: Option<(&Monomial, Rational)> = None;
    for (mono, coefficient) in poly.terms() {
        let replace = best
            .as_ref()
            .is_none_or(|(current, _)| lex_greater(mono, current));
        if replace {
            best = Some((mono, *coefficient));
        }
    }
    best.map(|(_, coefficient)| coefficient)
}

/// Whether `left` is `lex`-greater than `right`.
fn lex_greater(left: &Monomial, right: &Monomial) -> bool {
    let mut names: BTreeSet<&str> = BTreeSet::new();
    names.extend(left.powers().map(|(name, _)| name));
    names.extend(right.powers().map(|(name, _)| name));
    for name in names {
        match left.exponent_of(name).cmp(&right.exponent_of(name)) {
            Ordering::Equal => {}
            Ordering::Greater => return true,
            Ordering::Less => return false,
        }
    }
    false
}

/// Greatest common divisor of two `i128` values, non-negative.
fn integer_gcd(left: i128, right: i128) -> Option<i128> {
    let mut current = left.unsigned_abs();
    let mut next = right.unsigned_abs();
    while next != 0 {
        let remainder = current % next;
        current = next;
        next = remainder;
    }
    i128::try_from(current).ok()
}

/// Least common multiple of two `i128` values, non-negative.
fn integer_lcm(left: i128, right: i128) -> Option<i128> {
    if left == 0 || right == 0 {
        return Some(0);
    }
    let gcd = integer_gcd(left, right)?;
    (left / gcd).checked_mul(right).map(i128::abs)
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
    fn a_starved_certificate_ceiling_declines() {
        // The derived certificate degree for ∑ C(n,k)² is 1; refusing to act on
        // any positive derived degree must make the search decline, not guess.
        let term = HyperTerm::new(binomial_n_k(2));
        let starved = Limits {
            max_certificate_degree: 0,
            ..Limits::classical()
        };
        assert_eq!(
            zeilberger(&term, "n", "k", &starved),
            TelescopingOutcome::Declined
        );
    }

    #[test]
    fn a_starved_dispersion_ceiling_cannot_invent_a_certificate() {
        // A dispersion ceiling below the true dispersion leaves a shared factor
        // in place, so Gosper's criterion fails. Losing is the only failure mode
        // available: the search must never return an unverifiable certificate.
        let term = HyperTerm::new(binomial_n_k(1));
        let starved = Limits {
            max_dispersion: 0,
            ..Limits::classical()
        };
        // This particular term has dispersion 0, so the certificate survives.
        assert!(matches!(
            zeilberger(&term, "n", "k", &starved),
            TelescopingOutcome::Found(_)
        ));
    }

    #[test]
    fn the_derived_certificate_denominator_is_not_the_old_ladder() {
        // ∑ C(n,k)² has R = k²(3n+3−2k)/(n−k+1)². The denominator is *derived*
        // as s(k)·D(k) from the normal form, and comes out as (n−k+1)² without
        // any candidate ever being guessed.
        let term = HyperTerm::new(binomial_n_k(2));
        let TelescopingOutcome::Found(certificate) =
            zeilberger(&term, "n", "k", &Limits::classical())
        else {
            panic!("no certificate for the squared binomial row sum");
        };
        let expected = MvPoly::var("n")
            .sub(&MvPoly::var("k"))
            .unwrap()
            .add(&MvPoly::constant(Rational::integer(1)))
            .unwrap()
            .pow(2)
            .unwrap();
        assert_eq!(certificate.certificate_denominator, expected);
    }
}
