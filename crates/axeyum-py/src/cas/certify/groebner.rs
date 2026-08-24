//! `axeyum.cas.certify.groebner` — cofactor-tracked ideal membership.
//!
//! The crate has **no standalone checker function** for this route: the check is
//! arithmetic the caller performs, `sum(cofactor[i] * generator[i]) + remainder
//! == target`. So this binding ships it, in Rust, from `MvPoly` primitives —
//! and the answer depends on the comparison, not on the producer having
//! returned. Nothing about ideal membership is claimed on a `Declined`.

use axeyum_cas::groebner::MonomialOrder;
use axeyum_cas::groebner_cert::{
    CofactorOutcome as CasCofactorOutcome, DeclineReason as CasDeclineReason, Limits as CasLimits,
    ReductionStats as CasReductionStats, reduce_many_with_cofactors_traced,
    reduce_with_cofactors as cas_reduce_with_cofactors, unit_ideal_cofactors as cas_unit_ideal,
};
use axeyum_cas::mvpoly::MvPoly as CasMvPoly;
use pyo3::exceptions::PyValueError;
use pyo3::prelude::*;
use pyo3::types::{PyAny, PyModule};

use crate::cas::poly::MvPoly;

/// Reads a monomial-order name.
///
/// # Errors
///
/// Raises `ValueError` for an unrecognized name.
pub(crate) fn monomial_order(name: &str) -> PyResult<MonomialOrder> {
    match name {
        "lex" => Ok(MonomialOrder::Lex),
        "degrevlex" => Ok(MonomialOrder::DegRevLex),
        other => Err(PyValueError::new_err(format!(
            "unknown monomial order {other:?}; expected \"lex\" or \"degrevlex\""
        ))),
    }
}

/// The name of a monomial order.
pub(crate) fn monomial_order_name(order: MonomialOrder) -> &'static str {
    match order {
        MonomialOrder::Lex => "lex",
        MonomialOrder::DegRevLex => "degrevlex",
    }
}

/// Deterministic step ceilings for one cofactor-tracked computation.
///
/// The defaults are `Limits::fast()` verbatim: `reduction_steps=20_000`,
/// `pair_iterations=4_000`, `basis_size=64`, `poly_terms=512`, `order="lex"`.
/// These are step *counts*, not durations — termination is already guaranteed by
/// Dickson's lemma, and these exist so a latency-sensitive caller can bound the
/// work without a wall clock. A ceiling cannot change a verdict, only whether
/// one is reached.
#[pyclass(frozen, from_py_object, module = "axeyum", name = "Limits")]
#[derive(Debug, Clone, Copy)]
pub struct Limits {
    inner: CasLimits,
}

impl Limits {
    /// The wrapped Rust limits.
    pub(crate) fn inner(self) -> CasLimits {
        self.inner
    }

    /// Wraps Rust limits.
    pub(crate) fn wrap(inner: CasLimits) -> Self {
        Self { inner }
    }
}

#[pymethods]
impl Limits {
    /// Limits with the `Limits::fast()` defaults, overridable per field.
    ///
    /// # Errors
    ///
    /// Raises `ValueError` for an unrecognized `order`.
    #[new]
    #[pyo3(signature = (
        reduction_steps = 20_000,
        pair_iterations = 4_000,
        basis_size = 64,
        poly_terms = 512,
        order = "lex",
    ))]
    fn new(
        reduction_steps: u64,
        pair_iterations: u64,
        basis_size: usize,
        poly_terms: usize,
        order: &str,
    ) -> PyResult<Limits> {
        Ok(Limits {
            inner: CasLimits {
                reduction_steps,
                pair_iterations,
                basis_size,
                poly_terms,
                order: monomial_order(order)?,
            },
        })
    }

    /// The interactive-dispatch ceilings, exactly as `Limits::fast()` sets them.
    #[staticmethod]
    fn fast() -> Limits {
        Limits {
            inner: CasLimits::fast(),
        }
    }

    /// Maximum term-cancelling steps across all reductions in one call.
    #[getter]
    fn reduction_steps(&self) -> u64 {
        self.inner.reduction_steps
    }

    /// Maximum S-pairs processed by the Buchberger loop.
    #[getter]
    fn pair_iterations(&self) -> u64 {
        self.inner.pair_iterations
    }

    /// Maximum size the intermediate basis may reach.
    #[getter]
    fn basis_size(&self) -> usize {
        self.inner.basis_size
    }

    /// Maximum monomials in any single intermediate polynomial or cofactor.
    #[getter]
    fn poly_terms(&self) -> usize {
        self.inner.poly_terms
    }

    /// The monomial order, `"lex"` or `"degrevlex"`.
    #[getter]
    fn order(&self) -> &'static str {
        monomial_order_name(self.inner.order)
    }

    fn __repr__(&self) -> String {
        format!(
            "Limits(reduction_steps={}, pair_iterations={}, basis_size={}, poly_terms={}, order={:?})",
            self.inner.reduction_steps,
            self.inner.pair_iterations,
            self.inner.basis_size,
            self.inner.poly_terms,
            self.order()
        )
    }
}

/// Why a cofactor-tracked computation stopped without an answer.
///
/// `is_ceiling()` is the distinction that matters: a tripped budget is worth
/// retrying with larger [`Limits`]; an `i128` overflow is not. A decline that
/// does not say which is uninterpretable.
#[pyclass(frozen, from_py_object, module = "axeyum", name = "DeclineReason")]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DeclineReason {
    inner: CasDeclineReason,
}

impl DeclineReason {
    /// Wraps a Rust decline reason.
    pub(crate) fn wrap(inner: CasDeclineReason) -> Self {
        Self { inner }
    }

    /// The variant name.
    pub(crate) fn tag(inner: CasDeclineReason) -> &'static str {
        match inner {
            CasDeclineReason::ReductionSteps => "ReductionSteps",
            CasDeclineReason::PairIterations => "PairIterations",
            CasDeclineReason::BasisSize => "BasisSize",
            CasDeclineReason::PolyTerms => "PolyTerms",
            CasDeclineReason::Overflow => "Overflow",
        }
    }
}

#[pymethods]
impl DeclineReason {
    /// The variant name.
    #[getter]
    fn name(&self) -> &'static str {
        DeclineReason::tag(self.inner)
    }

    /// Whether a larger [`Limits`] could change the answer.
    fn is_ceiling(&self) -> bool {
        self.inner.is_ceiling()
    }

    fn __eq__(&self, other: &Bound<'_, PyAny>) -> bool {
        other
            .extract::<DeclineReason>()
            .is_ok_and(|other| other.inner == self.inner)
    }

    fn __repr__(&self) -> String {
        format!(
            "DeclineReason({}, is_ceiling={})",
            self.name(),
            self.inner.is_ceiling()
        )
    }
}

/// What one cofactor-tracked computation actually did, whatever it concluded.
///
/// Advisory only: nothing in a certificate depends on these, and they are
/// recorded on the success path too so a run that certifies can be compared
/// against one that does not.
#[pyclass(frozen, from_py_object, module = "axeyum", name = "ReductionStats")]
#[derive(Debug, Clone, Copy)]
pub struct ReductionStats {
    inner: CasReductionStats,
}

#[pymethods]
impl ReductionStats {
    /// S-pairs taken off the queue.
    #[getter]
    fn pairs_processed(&self) -> u64 {
        self.inner.pairs_processed
    }

    /// S-pairs ever put on the queue.
    #[getter]
    fn pairs_queued(&self) -> u64 {
        self.inner.pairs_queued
    }

    /// S-pairs whose remainder was nonzero, so the basis grew.
    #[getter]
    fn basis_extensions(&self) -> u64 {
        self.inner.basis_extensions
    }

    /// Processed pairs whose leading monomials were coprime.
    #[getter]
    fn pairs_coprime_lead(&self) -> u64 {
        self.inner.pairs_coprime_lead
    }

    /// The largest the intermediate basis got.
    #[getter]
    fn max_basis_len(&self) -> usize {
        self.inner.max_basis_len
    }

    /// The most monomials seen in any single intermediate polynomial.
    #[getter]
    fn max_poly_terms(&self) -> usize {
        self.inner.max_poly_terms
    }

    /// Term-cancelling steps spent.
    #[getter]
    fn reduction_steps_spent(&self) -> u64 {
        self.inner.reduction_steps_spent
    }

    fn __repr__(&self) -> String {
        format!(
            "ReductionStats(pairs_processed={}, pairs_queued={}, basis_extensions={}, \
             max_basis_len={}, max_poly_terms={}, reduction_steps_spent={})",
            self.inner.pairs_processed,
            self.inner.pairs_queued,
            self.inner.basis_extensions,
            self.inner.max_basis_len,
            self.inner.max_poly_terms,
            self.inner.reduction_steps_spent
        )
    }
}

/// The outcome of a cofactor-tracked reduction: `Reduced` or `Declined`.
#[pyclass(frozen, from_py_object, module = "axeyum", name = "CofactorOutcome")]
#[derive(Debug, Clone)]
pub struct CofactorOutcome {
    inner: CasCofactorOutcome,
}

impl CofactorOutcome {
    /// Wraps a Rust outcome.
    fn wrap(inner: CasCofactorOutcome) -> Self {
        Self { inner }
    }
}

#[pymethods]
impl CofactorOutcome {
    /// `"Reduced"` or `"Declined"`.
    #[getter]
    fn kind(&self) -> &'static str {
        match self.inner {
            CasCofactorOutcome::Reduced { .. } => "Reduced",
            CasCofactorOutcome::Declined(_) => "Declined",
        }
    }

    /// Whether the reduction produced cofactors at all.
    fn is_reduced(&self) -> bool {
        matches!(self.inner, CasCofactorOutcome::Reduced { .. })
    }

    /// One cofactor per generator, positionally aligned with the input; `None`
    /// on a decline.
    #[getter]
    fn cofactors(&self) -> Option<Vec<MvPoly>> {
        match &self.inner {
            CasCofactorOutcome::Reduced { cofactors, .. } => Some(MvPoly::wrap_vec(cofactors)),
            CasCofactorOutcome::Declined(_) => None,
        }
    }

    /// The normal form of the target modulo the basis; zero exactly when the
    /// target lies in the ideal. `None` on a decline.
    #[getter]
    fn remainder(&self) -> Option<MvPoly> {
        match &self.inner {
            CasCofactorOutcome::Reduced { remainder, .. } => Some(MvPoly::wrap(remainder.clone())),
            CasCofactorOutcome::Declined(_) => None,
        }
    }

    /// Why the computation stopped; `None` when it did not.
    #[getter]
    fn reason(&self) -> Option<DeclineReason> {
        match self.inner {
            CasCofactorOutcome::Reduced { .. } => None,
            CasCofactorOutcome::Declined(reason) => Some(DeclineReason::wrap(reason)),
        }
    }

    /// Whether the target lies in the ideal, per this outcome; `None` when
    /// nothing was decided.
    ///
    /// A `Declined` outcome claims **nothing** about membership in either
    /// direction, so it is `None` here rather than `False`.
    fn in_ideal(&self) -> Option<bool> {
        match &self.inner {
            CasCofactorOutcome::Reduced { remainder, .. } => Some(remainder.is_zero()),
            CasCofactorOutcome::Declined(_) => None,
        }
    }

    /// Re-derives the identity from the outside:
    /// `sum(cofactors[i] * generators[i]) + remainder == target`.
    ///
    /// `False` on a decline, on an arity mismatch, and on any overflow while
    /// re-expanding — none of which is a claim that the producer was wrong, only
    /// that this check did not establish the identity.
    ///
    /// # Errors
    ///
    /// Propagates the per-element extraction error for `generators`.
    fn check(&self, generators: &Bound<'_, PyAny>, target: &MvPoly) -> PyResult<bool> {
        let generators = MvPoly::vec_from_py(generators)?;
        let CasCofactorOutcome::Reduced {
            cofactors,
            remainder,
        } = &self.inner
        else {
            return Ok(false);
        };
        Ok(reexpand(cofactors, remainder, &generators, target.inner()))
    }

    fn __repr__(&self) -> String {
        match &self.inner {
            CasCofactorOutcome::Reduced {
                cofactors,
                remainder,
            } => format!(
                "CofactorOutcome(Reduced, cofactors={}, remainder_zero={})",
                cofactors.len(),
                remainder.is_zero()
            ),
            CasCofactorOutcome::Declined(reason) => {
                format!("CofactorOutcome(Declined, {})", DeclineReason::tag(*reason))
            }
        }
    }
}

/// The identity check, in Rust, over `MvPoly` primitives.
fn reexpand(
    cofactors: &[CasMvPoly],
    remainder: &CasMvPoly,
    generators: &[CasMvPoly],
    target: &CasMvPoly,
) -> bool {
    if cofactors.len() != generators.len() {
        return false;
    }
    let mut total = remainder.clone();
    for (cofactor, generator) in cofactors.iter().zip(generators) {
        let Some(product) = cofactor.mul(generator) else {
            return false;
        };
        let Some(sum) = total.add(&product) else {
            return false;
        };
        total = sum;
    }
    let Some(difference) = total.sub(target) else {
        return false;
    };
    difference.is_zero()
}

/// The standalone identity check, so a caller can hand it a **tampered**
/// cofactor list and watch it fail.
///
/// This is the falsifiability control for the whole route: an accepting checker
/// that has never been shown to reject is indistinguishable from one that
/// returns `True`.
///
/// # Errors
///
/// Propagates the per-element extraction error.
#[pyfunction]
fn check_identity(
    cofactors: &Bound<'_, PyAny>,
    remainder: &MvPoly,
    generators: &Bound<'_, PyAny>,
    target: &MvPoly,
) -> PyResult<bool> {
    let cofactors = MvPoly::vec_from_py(cofactors)?;
    let generators = MvPoly::vec_from_py(generators)?;
    Ok(reexpand(
        &cofactors,
        remainder.inner(),
        &generators,
        target.inner(),
    ))
}

/// Reduces `target` modulo the ideal generated by `generators`, tracking
/// cofactors.
///
/// # Errors
///
/// Propagates the per-element extraction error.
#[pyfunction]
#[pyo3(signature = (generators, target, limits = None))]
fn reduce_with_cofactors(
    py: Python<'_>,
    generators: &Bound<'_, PyAny>,
    target: &MvPoly,
    limits: Option<&Limits>,
) -> PyResult<CofactorOutcome> {
    let generators = MvPoly::vec_from_py(generators)?;
    let limits = limits.map_or_else(CasLimits::fast, |limits| limits.inner());
    let target = target.inner().clone();
    Ok(CofactorOutcome::wrap(py.detach(|| {
        cas_reduce_with_cofactors(&generators, &target, limits)
    })))
}

/// Weak-Nullstellensatz cofactors: writes `1` in terms of the generators, when
/// the ideal is the unit ideal.
///
/// # Errors
///
/// Propagates the per-element extraction error.
#[pyfunction]
#[pyo3(signature = (generators, limits = None))]
fn unit_ideal_cofactors(
    py: Python<'_>,
    generators: &Bound<'_, PyAny>,
    limits: Option<&Limits>,
) -> PyResult<CofactorOutcome> {
    let generators = MvPoly::vec_from_py(generators)?;
    let limits = limits.map_or_else(CasLimits::fast, |limits| limits.inner());
    Ok(CofactorOutcome::wrap(
        py.detach(|| cas_unit_ideal(&generators, limits)),
    ))
}

/// Reduces several targets against one basis, returning the outcomes and the
/// shared [`ReductionStats`].
///
/// # Errors
///
/// Propagates the per-element extraction error.
#[pyfunction]
#[pyo3(signature = (generators, targets, limits = None))]
fn reduce_many_with_cofactors(
    py: Python<'_>,
    generators: &Bound<'_, PyAny>,
    targets: &Bound<'_, PyAny>,
    limits: Option<&Limits>,
) -> PyResult<(Vec<CofactorOutcome>, ReductionStats)> {
    let generators = MvPoly::vec_from_py(generators)?;
    let targets = MvPoly::vec_from_py(targets)?;
    let limits = limits.map_or_else(CasLimits::fast, |limits| limits.inner());
    let (outcomes, stats) =
        py.detach(|| reduce_many_with_cofactors_traced(&generators, &targets, limits));
    Ok((
        outcomes.into_iter().map(CofactorOutcome::wrap).collect(),
        ReductionStats { inner: stats },
    ))
}

/// Registers the `groebner` route on `parent`.
///
/// # Errors
///
/// Propagates any Python error raised while creating or populating the module.
pub(crate) fn register(parent: &Bound<'_, PyModule>) -> PyResult<()> {
    let module = PyModule::new(parent.py(), "axeyum._native.cas.certify.groebner")?;
    module.add_class::<Limits>()?;
    module.add_class::<DeclineReason>()?;
    module.add_class::<ReductionStats>()?;
    module.add_class::<CofactorOutcome>()?;
    module.add_function(wrap_pyfunction!(reduce_with_cofactors, &module)?)?;
    module.add_function(wrap_pyfunction!(unit_ideal_cofactors, &module)?)?;
    module.add_function(wrap_pyfunction!(reduce_many_with_cofactors, &module)?)?;
    module.add_function(wrap_pyfunction!(check_identity, &module)?)?;
    parent.add("groebner", &module)?;
    Ok(())
}
