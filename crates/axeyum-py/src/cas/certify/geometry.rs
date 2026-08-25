//! `axeyum.cas.certify.geometry` — the most complete producer / checker /
//! serializer triple in the crate.
//!
//! `certify_any_route` is the front door and returns a **three-way** outcome.
//! `NotInSaturatedIdeal` is not a decline and `RefutedByOwnWitness` means the
//! theorem as stated is *false*; collapsing either into "declined" would erase
//! the distinction the producer made, which is exactly the defect this route's
//! design exists to prevent.

use std::collections::BTreeMap;

use axeyum_cas::geometry_certify::{
    self, Condition as CasCondition, Constraint as CasConstraint,
    DegenerateWitness as CasDegenerateWitness, GenericWitness as CasGenericWitness,
    GeometryCertificate as CasGeometryCertificate, GeometryDecline as CasGeometryDecline,
    GeometryProblem as CasGeometryProblem, ProofOutcome as CasProofOutcome, Pt as CasPt,
};
use axeyum_cas::geometry_check::{
    CheckOptions as CasCheckOptions, GeometryVerdict as CasGeometryVerdict, check_certificate,
};
use axeyum_cas::geometry_corpus;
use axeyum_cas::geometry_json;
use pyo3::prelude::*;
use pyo3::types::{PyAny, PyDict, PyModule};

use crate::cas::certify::groebner::{DeclineReason, Limits};
use crate::cas::expr::rational_env;
use crate::cas::poly::MvPoly;
use crate::cas::rational;

/// A point with polynomial coordinates.
#[pyclass(frozen, from_py_object, module = "axeyum", name = "Pt")]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Pt {
    inner: CasPt,
}

impl Pt {
    /// Wraps a Rust point.
    fn wrap(inner: CasPt) -> Self {
        Self { inner }
    }
}

#[pymethods]
impl Pt {
    /// A free point `(name_x, name_y)`, its coordinates fresh variables.
    #[staticmethod]
    fn free(name: &str) -> Pt {
        Pt::wrap(CasPt::free(name))
    }

    /// A point at fixed rational coordinates.
    ///
    /// # Errors
    ///
    /// Raises `ValueError` when a coordinate is not an exact rational.
    #[staticmethod]
    fn fixed(x: &Bound<'_, PyAny>, y: &Bound<'_, PyAny>) -> PyResult<Pt> {
        Ok(Pt::wrap(CasPt::fixed(
            rational::from_py(x)?,
            rational::from_py(y)?,
        )))
    }

    /// The `x` coordinate.
    #[getter]
    fn x(&self) -> MvPoly {
        MvPoly::wrap(self.inner.x.clone())
    }

    /// The `y` coordinate.
    #[getter]
    fn y(&self) -> MvPoly {
        MvPoly::wrap(self.inner.y.clone())
    }

    /// `self - other`, or `None` on overflow.
    fn sub(&self, other: &Pt) -> Option<Pt> {
        self.inner.sub(&other.inner).map(Pt::wrap)
    }

    /// `self + other`, or `None` on overflow.
    fn add(&self, other: &Pt) -> Option<Pt> {
        self.inner.add(&other.inner).map(Pt::wrap)
    }

    /// `factor * self`, or `None` on overflow.
    ///
    /// # Errors
    ///
    /// Raises `ValueError` when `factor` is not an exact rational.
    fn scale(&self, factor: &Bound<'_, PyAny>) -> PyResult<Option<Pt>> {
        Ok(self.inner.scale(rational::from_py(factor)?).map(Pt::wrap))
    }

    fn __repr__(&self) -> String {
        "Pt(...)".to_owned()
    }
}

/// Binds a `fn(&Pt, &Pt) -> Option<MvPoly>` predicate.
macro_rules! two_point {
    ($name:ident, $doc:literal) => {
        #[doc = $doc]
        #[pyfunction]
        fn $name(first: &Pt, second: &Pt) -> Option<MvPoly> {
            MvPoly::wrap_option(geometry_certify::$name(&first.inner, &second.inner))
        }
    };
}

/// Binds a `fn(&Pt, &Pt, &Pt, &Pt) -> Option<MvPoly>` predicate.
macro_rules! four_point {
    ($name:ident, $doc:literal) => {
        #[doc = $doc]
        #[pyfunction]
        fn $name(from: &Pt, to: &Pt, other_from: &Pt, other_to: &Pt) -> Option<MvPoly> {
            MvPoly::wrap_option(geometry_certify::$name(
                &from.inner,
                &to.inner,
                &other_from.inner,
                &other_to.inner,
            ))
        }
    };
}

two_point!(det, "The determinant of the two coordinate vectors.");
two_point!(dot, "The dot product of the two coordinate vectors.");
two_point!(dist_sq, "The squared distance between two points.");

four_point!(
    parallel,
    "`from->to` is parallel to `other_from->other_to`."
);
four_point!(
    perpendicular,
    "`from->to` is perpendicular to `other_from->other_to`."
);
four_point!(
    equidistant,
    "`|from - to|` equals `|other_from - other_to|`."
);

/// Three points are collinear.
#[pyfunction]
fn collinear(first: &Pt, second: &Pt, third: &Pt) -> Option<MvPoly> {
    MvPoly::wrap_option(geometry_certify::collinear(
        &first.inner,
        &second.inner,
        &third.inner,
    ))
}

/// Four points lie on a common circle.
#[pyfunction]
fn concyclic(first: &Pt, second: &Pt, third: &Pt, fourth: &Pt) -> Option<MvPoly> {
    MvPoly::wrap_option(geometry_certify::concyclic(
        &first.inner,
        &second.inner,
        &third.inner,
        &fourth.inner,
    ))
}

/// The midpoint of two points.
#[pyfunction]
fn midpoint(from: &Pt, to: &Pt) -> Option<Pt> {
    geometry_certify::midpoint(&from.inner, &to.inner).map(Pt::wrap)
}

/// The centroid of three points.
#[pyfunction]
fn centroid(first: &Pt, second: &Pt, third: &Pt) -> Option<Pt> {
    geometry_certify::centroid(&first.inner, &second.inner, &third.inner).map(Pt::wrap)
}

/// The two coordinate equations saying that two points coincide.
#[pyfunction]
fn same_point(first: &Pt, second: &Pt) -> Option<Vec<MvPoly>> {
    geometry_certify::same_point(&first.inner, &second.inner)
        .map(|pair| pair.into_iter().map(MvPoly::wrap).collect())
}

/// A hypothesis or conclusion: an identified polynomial equation `poly == 0`.
#[pyclass(frozen, from_py_object, module = "axeyum", name = "Constraint")]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Constraint {
    inner: CasConstraint,
}

#[pymethods]
impl Constraint {
    /// A constraint `poly == 0` with a stable identifier and a gloss.
    #[new]
    fn new(id: &str, description: &str, poly: &MvPoly) -> Constraint {
        Constraint {
            inner: CasConstraint::new(id, description, poly.inner().clone()),
        }
    }

    /// The stable identifier.
    #[getter]
    fn id(&self) -> &str {
        &self.inner.id
    }

    /// The human-readable gloss.
    #[getter]
    fn description(&self) -> &str {
        &self.inner.description
    }

    /// The polynomial that must vanish.
    #[getter]
    fn poly(&self) -> MvPoly {
        MvPoly::wrap(self.inner.poly.clone())
    }

    fn __repr__(&self) -> String {
        format!("Constraint({:?})", self.inner.id)
    }
}

/// A non-degeneracy condition: an identified polynomial that must **not** vanish.
#[pyclass(frozen, from_py_object, module = "axeyum", name = "Condition")]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Condition {
    inner: CasCondition,
}

#[pymethods]
impl Condition {
    /// A condition `poly != 0` with a stable identifier and a gloss.
    #[new]
    fn new(id: &str, description: &str, poly: &MvPoly) -> Condition {
        Condition {
            inner: CasCondition::new(id, description, poly.inner().clone()),
        }
    }

    /// The stable identifier.
    #[getter]
    fn id(&self) -> &str {
        &self.inner.id
    }

    /// The human-readable gloss.
    #[getter]
    fn description(&self) -> &str {
        &self.inner.description
    }

    /// The polynomial that must not vanish.
    #[getter]
    fn poly(&self) -> MvPoly {
        MvPoly::wrap(self.inner.poly.clone())
    }

    fn __repr__(&self) -> String {
        format!("Condition({:?})", self.inner.id)
    }
}

/// A configuration on a degeneracy locus that genuinely breaks the theorem.
///
/// This is the certificate's **negative control**: a stated witness that does
/// not in fact break the theorem makes the producer decline
/// (`UnverifiedWitness`) rather than ship a decorative one.
#[pyclass(frozen, from_py_object, module = "axeyum", name = "DegenerateWitness")]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DegenerateWitness {
    inner: CasDegenerateWitness,
}

#[pymethods]
impl DegenerateWitness {
    /// A purely rational witness for the named condition.
    ///
    /// # Errors
    ///
    /// Raises `ValueError` when a coordinate is not an exact rational.
    #[staticmethod]
    fn rational(
        condition_id: &str,
        description: &str,
        assignment: &Bound<'_, PyDict>,
    ) -> PyResult<DegenerateWitness> {
        Ok(DegenerateWitness {
            inner: CasDegenerateWitness::rational(
                condition_id,
                description,
                rational_env(assignment)?,
            ),
        })
    }

    /// The condition this witness breaks.
    #[getter]
    fn condition_id(&self) -> &str {
        &self.inner.condition_id
    }

    /// The human-readable gloss.
    #[getter]
    fn description(&self) -> &str {
        &self.inner.description
    }

    /// The real part of the assignment.
    ///
    /// # Errors
    ///
    /// Propagates any Python error raised while building the fractions.
    #[getter]
    fn assignment<'py>(&self, py: Python<'py>) -> PyResult<Bound<'py, PyDict>> {
        rational_dict(py, &self.inner.assignment)
    }

    /// Whether any coordinate has a nonzero imaginary part.
    fn is_gaussian(&self) -> bool {
        self.inner.is_gaussian()
    }

    fn __repr__(&self) -> String {
        format!("DegenerateWitness({:?})", self.inner.condition_id)
    }
}

/// A generic configuration at which the theorem's identity is replayed.
#[pyclass(frozen, from_py_object, module = "axeyum", name = "GenericWitness")]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GenericWitness {
    inner: CasGenericWitness,
}

#[pymethods]
impl GenericWitness {
    /// A generic configuration.
    ///
    /// # Errors
    ///
    /// Raises `ValueError` when a coordinate is not an exact rational.
    #[new]
    fn new(description: &str, assignment: &Bound<'_, PyDict>) -> PyResult<GenericWitness> {
        Ok(GenericWitness {
            inner: CasGenericWitness {
                description: description.to_owned(),
                assignment: rational_env(assignment)?,
            },
        })
    }

    /// The human-readable gloss.
    #[getter]
    fn description(&self) -> &str {
        &self.inner.description
    }

    /// The assignment.
    ///
    /// # Errors
    ///
    /// Propagates any Python error raised while building the fractions.
    #[getter]
    fn assignment<'py>(&self, py: Python<'py>) -> PyResult<Bound<'py, PyDict>> {
        rational_dict(py, &self.inner.assignment)
    }

    fn __repr__(&self) -> String {
        format!("GenericWitness({:?})", self.inner.description)
    }
}

/// `{name: Fraction}` for a rational assignment.
fn rational_dict<'py>(
    py: Python<'py>,
    assignment: &BTreeMap<String, axeyum_ir::Rational>,
) -> PyResult<Bound<'py, PyDict>> {
    let dict = PyDict::new(py);
    for (name, value) in assignment {
        dict.set_item(name, rational::fraction(py, *value)?)?;
    }
    Ok(dict)
}

/// A geometry theorem, stated in coordinates.
#[pyclass(frozen, from_py_object, module = "axeyum", name = "GeometryProblem")]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GeometryProblem {
    inner: CasGeometryProblem,
}

impl GeometryProblem {
    /// Wraps a Rust problem.
    fn wrap(inner: CasGeometryProblem) -> Self {
        Self { inner }
    }
}

#[pymethods]
impl GeometryProblem {
    /// States a theorem from its hypotheses, non-degeneracy conditions,
    /// conclusions and witnesses.
    #[new]
    #[pyo3(signature = (
        id,
        title,
        statement,
        hypotheses,
        conclusions,
        nondegeneracy = Vec::new(),
        coordinate_gloss = Vec::new(),
        degenerate_witnesses = Vec::new(),
        generic_witnesses = Vec::new(),
    ))]
    #[allow(clippy::too_many_arguments)]
    fn new(
        id: &str,
        title: &str,
        statement: &str,
        hypotheses: Vec<Constraint>,
        conclusions: Vec<Constraint>,
        nondegeneracy: Vec<Condition>,
        coordinate_gloss: Vec<(String, String)>,
        degenerate_witnesses: Vec<DegenerateWitness>,
        generic_witnesses: Vec<GenericWitness>,
    ) -> GeometryProblem {
        GeometryProblem::wrap(CasGeometryProblem {
            id: id.to_owned(),
            title: title.to_owned(),
            statement: statement.to_owned(),
            coordinate_gloss,
            hypotheses: hypotheses.into_iter().map(|item| item.inner).collect(),
            nondegeneracy: nondegeneracy.into_iter().map(|item| item.inner).collect(),
            conclusions: conclusions.into_iter().map(|item| item.inner).collect(),
            degenerate_witnesses: degenerate_witnesses
                .into_iter()
                .map(|item| item.inner)
                .collect(),
            generic_witnesses: generic_witnesses
                .into_iter()
                .map(|item| item.inner)
                .collect(),
        })
    }

    /// The stable identifier.
    #[getter]
    fn id(&self) -> &str {
        &self.inner.id
    }

    /// The theorem's title.
    #[getter]
    fn title(&self) -> &str {
        &self.inner.title
    }

    /// The theorem's prose statement.
    #[getter]
    fn statement(&self) -> &str {
        &self.inner.statement
    }

    /// The hypotheses.
    #[getter]
    fn hypotheses(&self) -> Vec<Constraint> {
        self.inner
            .hypotheses
            .iter()
            .cloned()
            .map(|inner| Constraint { inner })
            .collect()
    }

    /// The non-degeneracy conditions.
    #[getter]
    fn nondegeneracy(&self) -> Vec<Condition> {
        self.inner
            .nondegeneracy
            .iter()
            .cloned()
            .map(|inner| Condition { inner })
            .collect()
    }

    /// The conclusions.
    #[getter]
    fn conclusions(&self) -> Vec<Constraint> {
        self.inner
            .conclusions
            .iter()
            .cloned()
            .map(|inner| Constraint { inner })
            .collect()
    }

    /// The degenerate witnesses (the negative controls).
    #[getter]
    fn degenerate_witnesses(&self) -> Vec<DegenerateWitness> {
        self.inner
            .degenerate_witnesses
            .iter()
            .cloned()
            .map(|inner| DegenerateWitness { inner })
            .collect()
    }

    /// The generic witnesses.
    #[getter]
    fn generic_witnesses(&self) -> Vec<GenericWitness> {
        self.inner
            .generic_witnesses
            .iter()
            .cloned()
            .map(|inner| GenericWitness { inner })
            .collect()
    }

    fn __repr__(&self) -> String {
        format!("GeometryProblem({:?})", self.inner.id)
    }
}

/// A checkable geometry certificate.
#[pyclass(
    frozen,
    from_py_object,
    module = "axeyum",
    name = "GeometryCertificate"
)]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GeometryCertificate {
    inner: CasGeometryCertificate,
}

impl GeometryCertificate {
    /// Wraps a Rust certificate.
    fn wrap(inner: CasGeometryCertificate) -> Self {
        Self { inner }
    }
}

#[pymethods]
impl GeometryCertificate {
    /// The theorem's identifier.
    #[getter]
    fn id(&self) -> &str {
        &self.inner.id
    }

    /// The theorem's title.
    #[getter]
    fn title(&self) -> &str {
        &self.inner.title
    }

    /// The theorem's prose statement.
    #[getter]
    fn statement(&self) -> &str {
        &self.inner.statement
    }

    /// The coordinate names, in order.
    #[getter]
    fn coordinates(&self) -> &[String] {
        &self.inner.coordinates
    }

    /// The generator list the identity is stated over.
    #[getter]
    fn generators(&self) -> Vec<MvPoly> {
        MvPoly::wrap_vec(&self.inner.generators)
    }

    /// The identifiers of the conditions this proof saturated by.
    #[getter]
    fn saturation_condition_ids(&self) -> Vec<String> {
        self.inner
            .saturations
            .iter()
            .map(|saturation| saturation.condition_id.clone())
            .collect()
    }

    /// `[(conclusion_id, [cofactor, ...]), ...]`.
    #[getter]
    fn conclusion_cofactors(&self) -> Vec<(String, Vec<MvPoly>)> {
        self.inner
            .conclusions
            .iter()
            .map(|conclusion| {
                (
                    conclusion.id.clone(),
                    MvPoly::wrap_vec(&conclusion.cofactors),
                )
            })
            .collect()
    }

    /// Independently re-derives this certificate.
    ///
    /// Returns a [`GeometryVerdict`] carrying the five `GeometryReport` counts,
    /// not a bool: the counts are what make a `Verified` falsifiable, and a
    /// checker that discharges nothing must be visible as such.
    #[pyo3(signature = (options = None))]
    fn check(&self, py: Python<'_>, options: Option<&CheckOptions>) -> GeometryVerdict {
        let options = options.map_or_else(CasCheckOptions::default, |options| options.inner);
        let certificate = self.inner.clone();
        GeometryVerdict {
            inner: py.detach(|| check_certificate(&certificate, &options)),
        }
    }

    /// The deterministic JSON rendering.
    fn to_json(&self) -> String {
        geometry_json::to_json(&self.inner)
    }

    /// Parses a certificate from its deterministic JSON rendering.
    ///
    /// # Errors
    ///
    /// Raises `CasError` when the text is not a well-formed certificate.
    #[staticmethod]
    fn from_json(text: &str) -> PyResult<GeometryCertificate> {
        geometry_json::from_json(text)
            .map(GeometryCertificate::wrap)
            .map_err(crate::cas::CasError::new_err)
    }

    fn __eq__(&self, other: &Bound<'_, PyAny>) -> bool {
        // `cast` + `get`, never `extract`: `extract` on a `#[pyclass]` CLONES the
        // whole wrapped value -- an entire expression tree or certificate -- to
        // compare it and then drops it, and builds a `TypeError` object for the
        // ordinary `NotImplemented` case. `frozen` makes `Bound::get` a borrow
        // with no runtime borrow check at all.
        other
            .cast::<GeometryCertificate>()
            .is_ok_and(|other| other.get().inner == self.inner)
    }

    fn __repr__(&self) -> String {
        format!(
            "GeometryCertificate({:?}, conclusions={})",
            self.inner.id,
            self.inner.conclusions.len()
        )
    }
}

/// Why the geometry producer emitted no certificate.
#[pyclass(frozen, from_py_object, module = "axeyum", name = "GeometryDecline")]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct GeometryDecline {
    inner: CasGeometryDecline,
}

#[pymethods]
impl GeometryDecline {
    /// The variant name: one of `Reduction`, `TooManyConditions`,
    /// `UnverifiedWitness`, `UndividableMultiplier`, `RefutedByOwnWitness`.
    #[getter]
    fn name(&self) -> &'static str {
        match self.inner {
            CasGeometryDecline::Reduction(_) => "Reduction",
            CasGeometryDecline::TooManyConditions => "TooManyConditions",
            CasGeometryDecline::UnverifiedWitness => "UnverifiedWitness",
            CasGeometryDecline::UndividableMultiplier => "UndividableMultiplier",
            CasGeometryDecline::RefutedByOwnWitness => "RefutedByOwnWitness",
        }
    }

    /// The inner cofactor-reduction reason, when the decline was a reduction.
    #[getter]
    fn reduction_reason(&self) -> Option<DeclineReason> {
        match self.inner {
            CasGeometryDecline::Reduction(reason) => Some(DeclineReason::wrap(reason)),
            _ => None,
        }
    }

    /// Whether the producer's own negative control refuted the statement.
    ///
    /// `True` means **the theorem as stated is false** — not a resource limit,
    /// and never to be reported as "declined".
    fn is_refuted_by_own_witness(&self) -> bool {
        matches!(self.inner, CasGeometryDecline::RefutedByOwnWitness)
    }

    /// Whether a larger [`Limits`] could change the answer.
    ///
    /// Only a reduction decline can be a ceiling; every other variant is a
    /// statement about the theorem, not the budget.
    fn is_ceiling(&self) -> bool {
        match self.inner {
            CasGeometryDecline::Reduction(reason) => reason.is_ceiling(),
            _ => false,
        }
    }

    fn __repr__(&self) -> String {
        format!("GeometryDecline({})", self.name())
    }
}

/// The three-way result of attempting to certify a [`GeometryProblem`].
#[pyclass(frozen, from_py_object, module = "axeyum", name = "ProofOutcome")]
#[derive(Debug, Clone)]
pub struct ProofOutcome {
    inner: CasProofOutcome,
}

#[pymethods]
impl ProofOutcome {
    /// `"Certified"`, `"NotInSaturatedIdeal"`, or `"Declined"`.
    #[getter]
    fn kind(&self) -> &'static str {
        match self.inner {
            CasProofOutcome::Certified(_) => "Certified",
            CasProofOutcome::NotInSaturatedIdeal { .. } => "NotInSaturatedIdeal",
            CasProofOutcome::Declined(_) => "Declined",
        }
    }

    /// The certificate, when one was produced.
    #[getter]
    fn certificate(&self) -> Option<GeometryCertificate> {
        match &self.inner {
            CasProofOutcome::Certified(certificate) => {
                Some(GeometryCertificate::wrap((**certificate).clone()))
            }
            _ => None,
        }
    }

    /// The identifier of a conclusion that did not reduce to zero.
    ///
    /// Present only on `NotInSaturatedIdeal`, which claims **nothing**: the
    /// theorem may need a condition nobody stated, or may be false.
    #[getter]
    fn conclusion_id(&self) -> Option<&str> {
        match &self.inner {
            CasProofOutcome::NotInSaturatedIdeal { conclusion_id, .. } => Some(conclusion_id),
            _ => None,
        }
    }

    /// The nonzero remainder, on `NotInSaturatedIdeal`.
    #[getter]
    fn remainder(&self) -> Option<MvPoly> {
        match &self.inner {
            CasProofOutcome::NotInSaturatedIdeal { remainder, .. } => {
                Some(MvPoly::wrap(remainder.clone()))
            }
            _ => None,
        }
    }

    /// The decline reason, on `Declined`.
    #[getter]
    fn decline(&self) -> Option<GeometryDecline> {
        match self.inner {
            CasProofOutcome::Declined(decline) => Some(GeometryDecline { inner: decline }),
            _ => None,
        }
    }

    fn __repr__(&self) -> String {
        match &self.inner {
            CasProofOutcome::Certified(certificate) => {
                format!("ProofOutcome(Certified, id={:?})", certificate.id)
            }
            CasProofOutcome::NotInSaturatedIdeal { conclusion_id, .. } => {
                format!("ProofOutcome(NotInSaturatedIdeal, conclusion_id={conclusion_id:?})")
            }
            CasProofOutcome::Declined(decline) => {
                format!(
                    "ProofOutcome(Declined, {})",
                    GeometryDecline { inner: *decline }.name()
                )
            }
        }
    }
}

/// The counts an accepted certificate discharged.
///
/// Every one of these is exposed because a zero is the fail signal: a checker
/// that verified nothing and a checker that verified everything must not look
/// alike from Python.
#[pyclass(frozen, from_py_object, module = "axeyum", name = "GeometryReport")]
#[derive(Debug, Clone)]
pub struct GeometryReport {
    conclusions_checked: usize,
    degenerate_witnesses_checked: usize,
    generic_witnesses_checked: usize,
    numeric_points_checked: usize,
    conditions_used: Vec<String>,
}

#[pymethods]
impl GeometryReport {
    /// Conclusions whose cofactor identity was re-expanded.
    #[getter]
    fn conclusions_checked(&self) -> usize {
        self.conclusions_checked
    }

    /// Degenerate witnesses replayed.
    #[getter]
    fn degenerate_witnesses_checked(&self) -> usize {
        self.degenerate_witnesses_checked
    }

    /// Generic witnesses replayed.
    #[getter]
    fn generic_witnesses_checked(&self) -> usize {
        self.generic_witnesses_checked
    }

    /// Integer points at which the identity was re-evaluated.
    #[getter]
    fn numeric_points_checked(&self) -> usize {
        self.numeric_points_checked
    }

    /// The non-degeneracy conditions the proof actually used.
    #[getter]
    fn conditions_used(&self) -> &[String] {
        &self.conditions_used
    }

    fn __repr__(&self) -> String {
        format!(
            "GeometryReport(conclusions={}, degenerate={}, generic={}, numeric_points={}, \
             conditions_used={:?})",
            self.conclusions_checked,
            self.degenerate_witnesses_checked,
            self.generic_witnesses_checked,
            self.numeric_points_checked,
            self.conditions_used
        )
    }
}

/// The verdict of the independent geometry checker.
#[pyclass(frozen, from_py_object, module = "axeyum", name = "GeometryVerdict")]
#[derive(Debug, Clone)]
pub struct GeometryVerdict {
    inner: CasGeometryVerdict,
}

#[pymethods]
impl GeometryVerdict {
    /// `"Verified"` or `"Rejected"`.
    #[getter]
    fn kind(&self) -> &'static str {
        match self.inner {
            CasGeometryVerdict::Verified(_) => "Verified",
            CasGeometryVerdict::Rejected(_) => "Rejected",
        }
    }

    /// Whether the certificate re-derived.
    fn is_verified(&self) -> bool {
        self.inner.is_verified()
    }

    /// The counts, on `Verified`.
    #[getter]
    fn report(&self) -> Option<GeometryReport> {
        match &self.inner {
            CasGeometryVerdict::Verified(report) => Some(GeometryReport {
                conclusions_checked: report.conclusions_checked,
                degenerate_witnesses_checked: report.degenerate_witnesses_checked,
                generic_witnesses_checked: report.generic_witnesses_checked,
                numeric_points_checked: report.numeric_points_checked,
                conditions_used: report.conditions_used.clone(),
            }),
            CasGeometryVerdict::Rejected(_) => None,
        }
    }

    /// The rejection reason, on `Rejected`.
    #[getter]
    fn reason(&self) -> Option<&str> {
        match &self.inner {
            CasGeometryVerdict::Verified(_) => None,
            CasGeometryVerdict::Rejected(reason) => Some(reason),
        }
    }

    fn __repr__(&self) -> String {
        match &self.inner {
            CasGeometryVerdict::Verified(report) => format!(
                "GeometryVerdict(Verified, conclusions={}, numeric_points={})",
                report.conclusions_checked, report.numeric_points_checked
            ),
            CasGeometryVerdict::Rejected(reason) => {
                format!("GeometryVerdict(Rejected, {reason:?})")
            }
        }
    }
}

/// How hard the numeric cross-check works. Defaults: `numeric_points=24`,
/// `half_range=6`.
#[pyclass(frozen, from_py_object, module = "axeyum", name = "CheckOptions")]
#[derive(Debug, Clone, Copy)]
pub struct CheckOptions {
    inner: CasCheckOptions,
}

#[pymethods]
impl CheckOptions {
    /// Options, defaulting to the Rust `CheckOptions::default()`.
    #[new]
    #[pyo3(signature = (numeric_points = 24, half_range = 6))]
    fn new(numeric_points: usize, half_range: i128) -> CheckOptions {
        CheckOptions {
            inner: CasCheckOptions {
                numeric_points,
                half_range,
            },
        }
    }

    /// Integer points per conclusion at which to re-evaluate the identity.
    #[getter]
    fn numeric_points(&self) -> usize {
        self.inner.numeric_points
    }

    /// Points are drawn from `-half_range ..= half_range`.
    #[getter]
    fn half_range(&self) -> i128 {
        self.inner.half_range
    }

    fn __repr__(&self) -> String {
        format!(
            "CheckOptions(numeric_points={}, half_range={})",
            self.inner.numeric_points, self.inner.half_range
        )
    }
}

/// The ceilings calibrated to the committed geometry corpus.
#[pyfunction]
fn geometry_limits() -> Limits {
    Limits::wrap(geometry_certify::geometry_limits())
}

/// The front door: tries every route and returns the three-way outcome.
#[pyfunction]
#[pyo3(signature = (problem, limits = None))]
fn certify_any_route(
    py: Python<'_>,
    problem: &GeometryProblem,
    limits: Option<&Limits>,
) -> ProofOutcome {
    let limits = limits.map_or_else(geometry_certify::geometry_limits, |limits| limits.inner());
    let problem = problem.inner.clone();
    ProofOutcome {
        inner: py.detach(|| geometry_certify::certify_any_route(&problem, limits)),
    }
}

/// The Groebner-saturation route only.
#[pyfunction]
#[pyo3(signature = (problem, limits = None))]
fn certify(py: Python<'_>, problem: &GeometryProblem, limits: Option<&Limits>) -> ProofOutcome {
    let limits = limits.map_or_else(geometry_certify::geometry_limits, |limits| limits.inner());
    let problem = problem.inner.clone();
    ProofOutcome {
        inner: py.detach(|| geometry_certify::certify(&problem, limits)),
    }
}

/// The linear-elimination route, with an optional Groebner handover.
#[pyfunction]
#[pyo3(signature = (problem, handover = None))]
fn certify_by_linear_elimination(
    py: Python<'_>,
    problem: &GeometryProblem,
    handover: Option<&Limits>,
) -> ProofOutcome {
    let handover = handover.map(|limits| limits.inner());
    let problem = problem.inner.clone();
    ProofOutcome {
        inner: py.detach(|| geometry_certify::certify_by_linear_elimination(&problem, handover)),
    }
}

/// The committed corpus of geometry theorems.
#[pyfunction]
fn corpus() -> Vec<GeometryProblem> {
    geometry_corpus::corpus()
        .into_iter()
        .map(GeometryProblem::wrap)
        .collect()
}

/// The frontier: theorems the producer does not yet certify.
#[pyfunction]
fn frontier() -> Vec<GeometryProblem> {
    geometry_corpus::frontier()
        .into_iter()
        .map(GeometryProblem::wrap)
        .collect()
}

/// Registers the `geometry` route on `parent`.
///
/// # Errors
///
/// Propagates any Python error raised while creating or populating the module.
pub(crate) fn register(parent: &Bound<'_, PyModule>) -> PyResult<()> {
    let module = PyModule::new(parent.py(), "axeyum._native.cas.certify.geometry")?;
    module.add_class::<Pt>()?;
    module.add_class::<Constraint>()?;
    module.add_class::<Condition>()?;
    module.add_class::<DegenerateWitness>()?;
    module.add_class::<GenericWitness>()?;
    module.add_class::<GeometryProblem>()?;
    module.add_class::<GeometryCertificate>()?;
    module.add_class::<GeometryDecline>()?;
    module.add_class::<ProofOutcome>()?;
    module.add_class::<GeometryReport>()?;
    module.add_class::<GeometryVerdict>()?;
    module.add_class::<CheckOptions>()?;
    module.add(
        "INVERSE_PREFIX",
        axeyum_cas::geometry_certify::INVERSE_PREFIX,
    )?;
    module.add("FORMAT", geometry_json::FORMAT)?;
    module.add("VERSION", geometry_json::VERSION)?;
    macro_rules! add {
        ($($name:ident),* $(,)?) => {
            $(module.add_function(wrap_pyfunction!($name, &module)?)?;)*
        };
    }
    add!(
        det,
        dot,
        dist_sq,
        collinear,
        parallel,
        perpendicular,
        equidistant,
        concyclic,
        midpoint,
        centroid,
        same_point,
        geometry_limits,
        certify_any_route,
        certify,
        certify_by_linear_elimination,
        corpus,
        frontier,
    );
    parent.add("geometry", &module)?;
    Ok(())
}
