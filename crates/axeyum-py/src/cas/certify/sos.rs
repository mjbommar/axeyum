//! `axeyum.cas.certify.sos` — sum-of-squares / Positivstellensatz artifacts.
//!
//! There is **no search producer** in the crate for this route: artifacts are
//! authored by hand or by an external SDP and re-derived here. So the Python
//! tier is checker-first.
//!
//! `check` refuses a report with an **empty obligation list**. The crate says why
//! in as many words: a checker that discharges no obligation and exits zero is
//! indistinguishable from one that passed. Raising there is the whole point of
//! the wrapper.

use axeyum_cas::mvpoly::Monomial as CasMonomial;
use axeyum_cas::sos::psd::{Psd as CasPsd, is_psd as cas_is_psd};
use axeyum_cas::sos::{
    self, CheckReport as CasCheckReport, SosArtifact as CasSosArtifact, SosSum as CasSosSum,
    corpus as sos_corpus, json as sos_json,
};
use axeyum_ir::Rational as IrRational;
use pyo3::exceptions::PyValueError;
use pyo3::prelude::*;
use pyo3::types::{PyAny, PyModule};

use crate::cas::CasError;
use crate::cas::poly::{Monomial, MvPoly};
use crate::cas::rational;

/// A weighted sum of squares `sum(coefficient * square ** 2)`.
#[pyclass(frozen, from_py_object, module = "axeyum", name = "SosSum")]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SosSum {
    inner: CasSosSum,
}

#[pymethods]
impl SosSum {
    /// A sum from `[(coefficient, polynomial), ...]`.
    ///
    /// # Errors
    ///
    /// Raises `ValueError` when a coefficient is not an exact rational or the
    /// crate rejects the list (a negative weight, say).
    #[new]
    fn new(squares: &Bound<'_, PyAny>) -> PyResult<SosSum> {
        let mut collected: Vec<(IrRational, _)> = Vec::new();
        for item in squares.try_iter()? {
            let (coefficient, poly): (Py<PyAny>, MvPoly) = item?.extract()?;
            collected.push((
                rational::from_py(coefficient.bind(squares.py()))?,
                poly.inner().clone(),
            ));
        }
        CasSosSum::new(collected)
            .map(|inner| SosSum { inner })
            .map_err(PyValueError::new_err)
    }

    /// The number of squares.
    fn __len__(&self) -> usize {
        self.inner.len()
    }

    /// Whether the sum has no squares.
    fn is_empty(&self) -> bool {
        self.inner.is_empty()
    }

    /// `[(Fraction, MvPoly), ...]`.
    ///
    /// # Errors
    ///
    /// Propagates any Python error raised while building the fractions.
    fn squares<'py>(&self, py: Python<'py>) -> PyResult<Vec<(Bound<'py, PyAny>, MvPoly)>> {
        self.inner
            .squares()
            .iter()
            .map(|(coefficient, poly)| {
                Ok((
                    rational::fraction(py, *coefficient)?,
                    MvPoly::wrap(poly.clone()),
                ))
            })
            .collect()
    }

    /// The expanded polynomial the sum denotes.
    ///
    /// # Errors
    ///
    /// Raises `CasError` when the expansion overflows.
    fn expand(&self) -> PyResult<MvPoly> {
        self.inner
            .expand()
            .map(MvPoly::wrap)
            .map_err(CasError::new_err)
    }

    fn __repr__(&self) -> String {
        format!("SosSum(squares={})", self.inner.len())
    }
}

/// One discharged proof obligation.
#[pyclass(frozen, from_py_object, module = "axeyum", name = "Obligation")]
#[derive(Debug, Clone)]
pub struct Obligation {
    name: String,
    detail: String,
}

#[pymethods]
impl Obligation {
    /// The obligation's name.
    #[getter]
    fn name(&self) -> &str {
        &self.name
    }

    /// What was established.
    #[getter]
    fn detail(&self) -> &str {
        &self.detail
    }

    fn __repr__(&self) -> String {
        format!("Obligation({:?}, {:?})", self.name, self.detail)
    }
}

/// What the SOS checker actually discharged.
#[pyclass(frozen, from_py_object, module = "axeyum", name = "CheckReport")]
#[derive(Debug, Clone)]
pub struct CheckReport {
    inner: CasCheckReport,
}

#[pymethods]
impl CheckReport {
    /// The obligations, in the order the checker discharged them.
    #[getter]
    fn obligations(&self) -> Vec<Obligation> {
        self.inner
            .obligations
            .iter()
            .map(|obligation| Obligation {
                name: obligation.name.clone(),
                detail: obligation.detail.clone(),
            })
            .collect()
    }

    /// The certified exponential decay rate, for a Lyapunov artifact.
    ///
    /// # Errors
    ///
    /// Propagates any Python error raised while building the fraction.
    #[getter]
    fn rate<'py>(&self, py: Python<'py>) -> PyResult<Option<Bound<'py, PyAny>>> {
        rational::optional_fraction(py, self.inner.rate)
    }

    /// The number of obligations discharged.
    fn __len__(&self) -> usize {
        self.inner.len()
    }

    /// Whether nothing was discharged — the fail signal this route names
    /// explicitly.
    fn is_empty(&self) -> bool {
        self.inner.is_empty()
    }

    fn __repr__(&self) -> String {
        format!("CheckReport(obligations={})", self.inner.len())
    }
}

/// A sum-of-squares artifact: a problem paired with its certificate.
#[pyclass(frozen, from_py_object, module = "axeyum", name = "SosArtifact")]
#[derive(Debug, Clone)]
pub struct SosArtifact {
    inner: CasSosArtifact,
}

impl SosArtifact {
    /// Wraps a Rust artifact.
    fn wrap(inner: CasSosArtifact) -> Self {
        Self { inner }
    }
}

#[pymethods]
impl SosArtifact {
    /// The artifact identifier.
    #[getter]
    fn id(&self) -> &str {
        self.inner.id()
    }

    /// `"lyapunov"`, `"barrier"` or `"psd-not-sos"`.
    #[getter]
    fn kind(&self) -> &'static str {
        self.inner.kind()
    }

    /// The deterministic JSON rendering.
    fn to_json(&self) -> String {
        sos_json::to_json(&self.inner)
    }

    /// Parses an artifact from its deterministic JSON rendering.
    ///
    /// # Errors
    ///
    /// Raises `CasError` when the text is not a well-formed artifact.
    #[staticmethod]
    fn from_json(text: &str) -> PyResult<SosArtifact> {
        sos_json::from_json(text)
            .map(SosArtifact::wrap)
            .map_err(CasError::new_err)
    }

    fn __repr__(&self) -> String {
        format!(
            "SosArtifact({:?}, kind={:?})",
            self.inner.id(),
            self.inner.kind()
        )
    }
}

/// Re-derives an SOS artifact, returning what it discharged.
///
/// # Errors
///
/// Raises `CasError` when the checker rejects the artifact, **and also when the
/// report is empty**: a checker that discharged no obligation established
/// nothing, and returning that as a pass is the failure mode this route is
/// documented against.
#[pyfunction]
fn check(py: Python<'_>, artifact: &SosArtifact) -> PyResult<CheckReport> {
    let owned = artifact.inner.clone();
    let report = py.detach(|| sos::check(&owned)).map_err(|reason| {
        CasError::new_err(format!("sos check rejected the artifact: {reason}"))
    })?;
    if report.is_empty() {
        return Err(CasError::new_err(format!(
            "sos check on {:?} discharged no obligation; an empty obligation list is \
             indistinguishable from a checker that did nothing",
            artifact.inner.id()
        )));
    }
    Ok(CheckReport { inner: report })
}

/// The same check without the empty-report guard, so a caller can see the count
/// the guard is about.
///
/// # Errors
///
/// Raises `CasError` when the checker rejects the artifact.
#[pyfunction]
fn check_unguarded(py: Python<'_>, artifact: &SosArtifact) -> PyResult<CheckReport> {
    let owned = artifact.inner.clone();
    py.detach(|| sos::check(&owned))
        .map(|inner| CheckReport { inner })
        .map_err(|reason| CasError::new_err(format!("sos check rejected the artifact: {reason}")))
}

/// The committed SOS corpus.
#[pyfunction]
fn corpus() -> Vec<SosArtifact> {
    sos_corpus::all()
        .into_iter()
        .map(SosArtifact::wrap)
        .collect()
}

/// One corpus artifact by identifier.
#[pyfunction]
fn by_id(id: &str) -> Option<SosArtifact> {
    sos_corpus::by_id(id).map(SosArtifact::wrap)
}

/// `sum(v ** 2 for v in variables)`, the norm the checker builds for itself.
///
/// # Errors
///
/// Raises `CasError` when the construction overflows.
#[pyfunction]
fn sum_of_variable_squares(variables: Vec<String>) -> PyResult<MvPoly> {
    sos::sum_of_variable_squares(&variables)
        .map(MvPoly::wrap)
        .map_err(CasError::new_err)
}

/// The outcome of the exact rational PSD test.
#[pyclass(frozen, from_py_object, module = "axeyum", name = "PsdResult")]
#[derive(Debug, Clone)]
pub struct PsdResult {
    inner: CasPsd,
}

#[pymethods]
impl PsdResult {
    /// `"Yes"`, `"No"`, or `"Overflow"`.
    ///
    /// `Overflow` claims **nothing**; it is not a `No`.
    #[getter]
    fn kind(&self) -> &'static str {
        match self.inner {
            CasPsd::Yes { .. } => "Yes",
            CasPsd::No(_) => "No",
            CasPsd::Overflow => "Overflow",
        }
    }

    /// Whether the matrix was decided positive semidefinite.
    fn is_psd(&self) -> bool {
        matches!(self.inner, CasPsd::Yes { .. })
    }

    /// The nonzero pivots, in elimination order.
    ///
    /// # Errors
    ///
    /// Propagates any Python error raised while building the fractions.
    #[getter]
    fn pivots<'py>(&self, py: Python<'py>) -> PyResult<Option<Vec<Bound<'py, PyAny>>>> {
        match &self.inner {
            CasPsd::Yes { pivots, .. } => pivots
                .iter()
                .map(|pivot| rational::fraction(py, *pivot))
                .collect::<PyResult<Vec<_>>>()
                .map(Some),
            _ => Ok(None),
        }
    }

    /// How many pivots were exactly zero (the corank).
    #[getter]
    fn zero_pivots(&self) -> Option<usize> {
        match self.inner {
            CasPsd::Yes { zero_pivots, .. } => Some(zero_pivots),
            _ => None,
        }
    }

    /// Why the matrix is not positive semidefinite.
    #[getter]
    fn reason(&self) -> Option<&str> {
        match &self.inner {
            CasPsd::No(reason) => Some(reason),
            _ => None,
        }
    }

    fn __repr__(&self) -> String {
        format!("PsdResult({})", self.kind())
    }
}

/// The exact rational PSD test on a symmetric matrix of rationals.
///
/// # Errors
///
/// Raises `ValueError` when an entry is not an exact rational.
#[pyfunction]
fn is_psd(matrix: &Bound<'_, PyAny>) -> PyResult<PsdResult> {
    let mut rows: Vec<Vec<IrRational>> = Vec::new();
    for row in matrix.try_iter()? {
        rows.push(rational::vec_from_py(&row?)?);
    }
    Ok(PsdResult {
        inner: cas_is_psd(&rows),
    })
}

/// The dual monomial certificate of a `psd-not-sos` artifact, as
/// `[(Monomial, Fraction), ...]`.
///
/// Exposed because a dual that is not itself checkable is decoration.
///
/// # Errors
///
/// Propagates any Python error raised while building the fractions.
#[pyfunction]
fn psd_not_sos_dual<'py>(
    py: Python<'py>,
    artifact: &SosArtifact,
) -> PyResult<Option<Vec<(Monomial, Bound<'py, PyAny>)>>> {
    let CasSosArtifact::PsdNotSos(_, certificate) = &artifact.inner else {
        return Ok(None);
    };
    let entries: &std::collections::BTreeMap<CasMonomial, IrRational> = &certificate.dual;
    entries
        .iter()
        .map(|(monomial, value)| {
            Ok((
                Monomial::wrap(monomial.clone()),
                rational::fraction(py, *value)?,
            ))
        })
        .collect::<PyResult<Vec<_>>>()
        .map(Some)
}

/// Registers the `sos` route on `parent`.
///
/// # Errors
///
/// Propagates any Python error raised while creating or populating the module.
pub(crate) fn register(parent: &Bound<'_, PyModule>) -> PyResult<()> {
    let module = PyModule::new(parent.py(), "axeyum._native.cas.certify.sos")?;
    module.add_class::<SosSum>()?;
    module.add_class::<Obligation>()?;
    module.add_class::<CheckReport>()?;
    module.add_class::<SosArtifact>()?;
    module.add_class::<PsdResult>()?;
    module.add("REPLAY_POINTS", axeyum_cas::sos::check::REPLAY_POINTS)?;
    module.add_function(wrap_pyfunction!(check, &module)?)?;
    module.add_function(wrap_pyfunction!(check_unguarded, &module)?)?;
    module.add_function(wrap_pyfunction!(corpus, &module)?)?;
    module.add_function(wrap_pyfunction!(by_id, &module)?)?;
    module.add_function(wrap_pyfunction!(sum_of_variable_squares, &module)?)?;
    module.add_function(wrap_pyfunction!(is_psd, &module)?)?;
    module.add_function(wrap_pyfunction!(psd_not_sos_dual, &module)?)?;
    parent.add("sos", &module)?;
    Ok(())
}
