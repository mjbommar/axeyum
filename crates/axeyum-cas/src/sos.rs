//! Sum-of-squares certificates for polynomial dynamical systems and for
//! polynomial nonnegativity, carried as **exact rational** artifacts.
//!
//! # Why this exists
//!
//! The project's owner asked for the stack to be pointed at useful computation,
//! and named "general numerical approximation / ode / pde systems" as one of
//! four domains. This module is the entry point for that domain, and it takes
//! the position that the useful thing to compute about a differential equation
//! is not a *trajectory* but a **certificate**: an algebraic object, found by an
//! untrusted search (here, by hand), that a small program re-derives exactly.
//!
//! Three question types are modelled, deliberately different in kind:
//!
//! * [`LyapunovProblem`] — does every solution decay, and how fast? The
//!   certificate is a Lyapunov function `V` sandwiched between two multiples of
//!   `|x|^2`, with `-V-dot` bounded below by a third. Three SOS identities, and
//!   the quotient of two of their constants is a **certified exponential decay
//!   rate**.
//! * [`BarrierProblem`] — can the system, starting anywhere in `X0`, ever reach
//!   `Xu`? The certificate is a barrier function separating the two sets and
//!   non-increasing along the flow. The horizon is **unbounded**, which is what
//!   distinguishes this from the bounded-step transition-system reachability the
//!   `artifacts/examples/math/bounded-dynamics-v0` pack already covers.
//! * [`PsdNotSosProblem`] — a nonnegative polynomial the SOS route **cannot**
//!   certify directly. Two certificates in opposite directions: a primal SOS
//!   decomposition of `(sum of squares of the variables) * f` establishing
//!   `f >= 0`, and a **dual** PSD moment functional establishing `f` is not
//!   itself a sum of squares. This is the route's own incompleteness, measured
//!   rather than argued.
//!
//! # What a certificate here proves, and over which field
//!
//! Every identity in this module has **rational** coefficients, so it holds in
//! every ordered field. That is the point, and it is a stronger and cleaner
//! statement than a floating-point evaluation on a grid could ever be:
//! `p = sum w_i q_i^2` with `w_i >= 0` gives `p >= 0` at every point of every
//! ordered field extension of the rationals, not merely at the points a sampler
//! visited, and not merely up to a tolerance.
//!
//! What the certificate does **not** do is take the last step to a statement
//! about trajectories. "`V-dot <= -c|x|^2` pointwise" is algebra; "therefore
//! `|x(t)| -> 0` exponentially" is Lyapunov's direct method plus a Gronwall
//! comparison, which is real analysis over a complete ordered field and is not
//! certified here. The facts this module supports state the algebra as proved
//! and name the analytic bridge in their axiom footprint. Blurring the two is
//! exactly the overstatement ADR-0453 exists to prevent.
//!
//! # Independence of the checker
//!
//! [`check()`] never trusts a stated derivative. Given the vector field and the
//! candidate function it forms `V-dot = sum_i (dV/dx_i) * f_i` itself with
//! [`MvPoly::derivative_in`] and [`MvPoly::mul`], and compares that against what
//! the certificate's squares expand to. A tampered vector field therefore breaks
//! the decrease identity even though nothing in the file mentions a derivative;
//! `scripts/check-sos-negative-controls.sh` pins that.
//!
//! # Prior art
//!
//! Lyapunov (1892) for the direct method; Parrilo (2000) and Lasserre (2001) for
//! the SOS/moment relaxations that made the search tractable; Stengle (1974) for
//! the Positivstellensatz the barrier multipliers instantiate; Prajna and
//! Jadbabaie (2004) for barrier certificates; Motzkin (1967) for the first
//! explicit nonnegative non-SOS form. See the fact ledger entries for the
//! attributions and how each was obtained.

use std::collections::BTreeMap;

use axeyum_ir::Rational;

use crate::mvpoly::{Monomial, MvPoly};

pub mod check;
pub mod corpus;
pub mod json;
pub mod psd;

/// A sum of weighted squares, `sum_i weight_i * square_i^2`, with every weight
/// required nonnegative.
///
/// The weights are carried separately from the squares rather than folded in,
/// because folding a weight `w` into its square costs a square root and this
/// format admits none: `2 * x^2` is representable and `(sqrt(2) x)^2` is not.
/// Keeping the weight rational is what makes the whole artifact exact.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SosSum {
    squares: Vec<(Rational, MvPoly)>,
}

impl SosSum {
    /// Build a sum of weighted squares.
    ///
    /// # Errors
    ///
    /// Returns a message if any weight is negative -- a "sum of squares" with a
    /// negative weight certifies nothing, and accepting one silently is the
    /// single cheapest way to forge every certificate in this module.
    pub fn new(squares: Vec<(Rational, MvPoly)>) -> Result<Self, String> {
        for (weight, _) in &squares {
            if is_negative(*weight) {
                return Err(format!(
                    "a sum-of-squares summand carries the negative weight {}/{}",
                    weight.numerator(),
                    weight.denominator()
                ));
            }
        }
        Ok(Self { squares })
    }

    /// The weighted squares, in the order the certificate lists them.
    #[must_use]
    pub fn squares(&self) -> &[(Rational, MvPoly)] {
        &self.squares
    }

    /// How many squares the sum has. Reported so a certificate that quietly
    /// shrinks to the empty sum is visible rather than merely true.
    #[must_use]
    pub fn len(&self) -> usize {
        self.squares.len()
    }

    /// Whether the sum has no squares at all, i.e. denotes the zero polynomial.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.squares.is_empty()
    }

    /// Expand to the polynomial the sum denotes.
    ///
    /// # Errors
    ///
    /// Returns a message on exact-arithmetic overflow. This is a decline, never
    /// a verdict: an overflowed expansion says nothing about the identity.
    pub fn expand(&self) -> Result<MvPoly, String> {
        let mut total = MvPoly::zero();
        for (weight, square) in &self.squares {
            let raised = square
                .mul(square)
                .ok_or("squaring a summand overflowed the exact coefficient range")?;
            let scaled = raised
                .mul(&MvPoly::constant(*weight))
                .ok_or("scaling a summand overflowed the exact coefficient range")?;
            total = total
                .add(&scaled)
                .ok_or("accumulating the summands overflowed the exact coefficient range")?;
        }
        Ok(total)
    }
}

/// A polynomial vector field `x-dot_i = field[i]` over the named variables.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VectorField {
    /// The state variables, in the order the field components correspond to.
    pub variables: Vec<String>,
    /// One polynomial per variable.
    pub field: Vec<MvPoly>,
}

impl VectorField {
    /// The Lie derivative `sum_i (d p / d x_i) * field_i` of `p` along the field.
    ///
    /// This is the function that makes the checker independent of the artifact:
    /// nothing in a certificate file states a derivative, so nothing in a
    /// certificate file can lie about one.
    ///
    /// # Errors
    ///
    /// Returns a message on a length mismatch or on exact-arithmetic overflow.
    pub fn lie_derivative(&self, p: &MvPoly) -> Result<MvPoly, String> {
        if self.variables.len() != self.field.len() {
            return Err(format!(
                "the vector field has {} components for {} variables",
                self.field.len(),
                self.variables.len()
            ));
        }
        let mut total = MvPoly::zero();
        for (variable, component) in self.variables.iter().zip(self.field.iter()) {
            let partial = p
                .derivative_in(variable)
                .ok_or("differentiating overflowed the exact coefficient range")?;
            let product = partial
                .mul(component)
                .ok_or("forming a Lie-derivative product overflowed")?;
            total = total
                .add(&product)
                .ok_or("accumulating the Lie derivative overflowed")?;
        }
        Ok(total)
    }

    /// Whether the field mentions only the declared variables.
    #[must_use]
    pub fn is_closed(&self) -> bool {
        self.field.iter().all(|component| {
            component
                .variables()
                .iter()
                .all(|used| self.variables.contains(used))
        })
    }
}

/// A global-stability question about a polynomial vector field.
///
/// The three rational constants are the whole quantitative content: `lower` and
/// `upper` sandwich `V` between two multiples of `|x|^2`, `decay` lower-bounds
/// `-V-dot`, and `decay / upper` is the certified exponential rate.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LyapunovProblem {
    /// Stable identifier, matching the artifact file stem.
    pub id: String,
    /// Prose statement of the question, for a human reading the artifact.
    pub description: String,
    /// The dynamics.
    pub system: VectorField,
    /// The candidate Lyapunov function.
    pub v: MvPoly,
    /// `lower > 0` with `V - lower * |x|^2` a sum of squares.
    pub lower: Rational,
    /// `upper > 0` with `upper * |x|^2 - V` a sum of squares.
    pub upper: Rational,
    /// `decay > 0` with `-V-dot - decay * |x|^2` a sum of squares.
    pub decay: Rational,
    /// A point at which the naive candidate `|x|^2` has a *positive* Lie
    /// derivative, so the certificate is not certifying something the obvious
    /// guess already gives. A certificate whose problem could be solved by
    /// `|x|^2` is not wrong, but it is not evidence that the search did
    /// anything, and this field is what makes the difference checkable.
    pub naive_failure: BTreeMap<String, Rational>,
}

/// The three SOS identities that settle a [`LyapunovProblem`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LyapunovCertificate {
    /// Expands to `V - lower * |x|^2`.
    pub lower_gap: SosSum,
    /// Expands to `upper * |x|^2 - V`.
    pub upper_gap: SosSum,
    /// Expands to `-V-dot - decay * |x|^2`.
    pub decrease: SosSum,
}

/// An unbounded-horizon safety question: can a trajectory started anywhere in
/// `initial` ever reach `unsafe_region`?
///
/// Both sets are basic semialgebraic, given as lists of generators `g` with the
/// set being `{ x : g(x) >= 0 for every g }`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BarrierProblem {
    /// Stable identifier, matching the artifact file stem.
    pub id: String,
    /// Prose statement of the question, for a human reading the artifact.
    pub description: String,
    /// The dynamics.
    pub system: VectorField,
    /// Generators of the initial set.
    pub initial: Vec<MvPoly>,
    /// Generators of the unsafe set.
    pub unsafe_region: Vec<MvPoly>,
    /// The barrier function.
    pub barrier: MvPoly,
    /// A point of the initial set, so the claim is not vacuously true of an
    /// empty set. An empty `X0` makes every barrier certificate check out and
    /// proves nothing at all.
    pub initial_witness: BTreeMap<String, Rational>,
    /// A point of the unsafe set, for the same reason in the other direction.
    pub unsafe_witness: BTreeMap<String, Rational>,
}

/// The Positivstellensatz-shaped certificate that settles a [`BarrierProblem`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BarrierCertificate {
    /// One SOS multiplier per initial-set generator.
    pub initial_multipliers: Vec<SosSum>,
    /// `B <= -initial_margin` on the initial set; must be positive.
    pub initial_margin: Rational,
    /// Expands to `-B - initial_margin - sum_i sigma_i * g_i`.
    pub initial_gap: SosSum,
    /// One SOS multiplier per unsafe-set generator.
    pub unsafe_multipliers: Vec<SosSum>,
    /// `B >= unsafe_margin` on the unsafe set; must be positive.
    pub unsafe_margin: Rational,
    /// Expands to `B - unsafe_margin - sum_j tau_j * h_j`.
    pub unsafe_gap: SosSum,
    /// Expands to `-B-dot`.
    pub decrease: SosSum,
}

/// A form that is nonnegative on the reals but is **not** a sum of squares.
///
/// The `multiplier` is required by the checker to be exactly the sum of the
/// squares of the declared variables, which is the only assumption under which
/// "`multiplier * form` is SOS" yields "`form >= 0`": the multiplier must be
/// strictly positive off the origin.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PsdNotSosProblem {
    /// Stable identifier, matching the artifact file stem.
    pub id: String,
    /// Prose statement of the question, for a human reading the artifact.
    pub description: String,
    /// The variables, in a fixed order.
    pub variables: Vec<String>,
    /// The form, homogeneous of degree `2 * half_degree`.
    pub form: MvPoly,
    /// The strictly-positive-off-the-origin multiplier.
    pub multiplier: MvPoly,
    /// Half the degree of `form`; the moment basis is the monomials of exactly
    /// this degree.
    pub half_degree: u32,
}

/// The two opposing certificates that settle a [`PsdNotSosProblem`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PsdNotSosCertificate {
    /// Expands to `multiplier * form`, so `form >= 0` off the origin.
    pub multiplied: SosSum,
    /// A linear functional on the degree-`2 * half_degree` monomials whose
    /// moment matrix over the degree-`half_degree` monomials is PSD and which is
    /// *negative* on `form`. Monomials absent from the map take the value zero.
    pub dual: BTreeMap<Monomial, Rational>,
}

/// One certificate artifact: a question together with what settles it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SosArtifact {
    /// A stability question and its three SOS identities.
    Lyapunov(LyapunovProblem, LyapunovCertificate),
    /// A safety question and its Positivstellensatz certificate.
    Barrier(BarrierProblem, BarrierCertificate),
    /// A nonnegativity question and the dual refutation of its SOS-ness.
    PsdNotSos(PsdNotSosProblem, PsdNotSosCertificate),
}

impl SosArtifact {
    /// The artifact's stable identifier.
    #[must_use]
    pub fn id(&self) -> &str {
        match self {
            SosArtifact::Lyapunov(problem, _) => &problem.id,
            SosArtifact::Barrier(problem, _) => &problem.id,
            SosArtifact::PsdNotSos(problem, _) => &problem.id,
        }
    }

    /// The artifact's kind tag, as it appears in the JSON file and on the
    /// command line.
    #[must_use]
    pub fn kind(&self) -> &'static str {
        match self {
            SosArtifact::Lyapunov(..) => "lyapunov",
            SosArtifact::Barrier(..) => "barrier",
            SosArtifact::PsdNotSos(..) => "psd-not-sos",
        }
    }
}

/// One discharged proof obligation, named so a run reports *what* it checked
/// rather than only that it finished.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Obligation {
    /// A short stable name for the obligation.
    pub name: String,
    /// What was actually re-derived, with the numbers.
    pub detail: String,
}

/// The result of checking one artifact.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CheckReport {
    /// Every obligation discharged, in the order the checker ran them.
    pub obligations: Vec<Obligation>,
    /// For a Lyapunov artifact, the certified exponential rate `decay / upper`.
    pub rate: Option<Rational>,
}

impl CheckReport {
    pub(crate) fn new() -> Self {
        Self {
            obligations: Vec::new(),
            rate: None,
        }
    }

    pub(crate) fn record(&mut self, name: &str, detail: String) {
        self.obligations.push(Obligation {
            name: name.to_string(),
            detail,
        });
    }

    /// How many obligations were discharged.
    #[must_use]
    pub fn len(&self) -> usize {
        self.obligations.len()
    }

    /// Whether nothing was checked at all. A checker that discharges no
    /// obligation and exits zero is indistinguishable from one that passed.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.obligations.is_empty()
    }
}

/// Check any artifact.
///
/// # Errors
///
/// Returns a message naming the first obligation that failed.
pub fn check(artifact: &SosArtifact) -> Result<CheckReport, String> {
    check::check_artifact(artifact)
}

/// The sum of the squares of the named variables, `sum_i x_i^2`.
///
/// The checker builds this itself rather than reading it from the artifact,
/// which is what stops a file from declaring a degenerate "norm" that makes its
/// own sandwich vacuous.
///
/// # Errors
///
/// Returns a message on exact-arithmetic overflow.
pub fn sum_of_variable_squares(variables: &[String]) -> Result<MvPoly, String> {
    let mut total = MvPoly::zero();
    for variable in variables {
        let square = MvPoly::var(variable)
            .pow(2)
            .ok_or("squaring a variable overflowed")?;
        total = total.add(&square).ok_or("accumulating |x|^2 overflowed")?;
    }
    Ok(total)
}

pub(crate) fn is_negative(value: Rational) -> bool {
    value.numerator() < 0
}

pub(crate) fn is_positive(value: Rational) -> bool {
    value.numerator() > 0
}

pub(crate) fn show(value: Rational) -> String {
    if value.denominator() == 1 {
        format!("{}", value.numerator())
    } else {
        format!("{}/{}", value.numerator(), value.denominator())
    }
}

pub(crate) fn scale(poly: &MvPoly, factor: Rational) -> Result<MvPoly, String> {
    poly.mul(&MvPoly::constant(factor))
        .ok_or_else(|| "scaling a polynomial overflowed the exact coefficient range".to_string())
}
