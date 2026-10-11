//! Exact Pi enclosure transport and structured replay counts.
use super::{expr::Expr, rational};
use crate::{error::BudgetExceeded, stub_types::PyFraction};
use axeyum_cas::{
    expression_wire::WireError,
    pi_certificate::{PiEnclosureCertificate as Certificate, PiEnclosureReport as Report},
};
use axeyum_ir::Rational;
use pyo3::{exceptions::PyValueError, prelude::*, types::PyModule};
fn error(e: WireError) -> PyErr {
    match e {
        WireError::Invalid(s) => PyValueError::new_err(s),
        WireError::ResourceLimit(s) => BudgetExceeded::new_err(s),
    }
}
/// Exact source-bound Pi enclosure. Its bounds are claims until check accepts.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyclass(module = "axeyum._native.cas")
)]
#[pyclass(frozen, from_py_object, module = "axeyum", name = "PiEnclosure")]
#[derive(Debug, Clone)]
pub struct PiEnclosure {
    inner: Certificate,
}
#[cfg_attr(feature = "stub-gen", pyo3_stub_gen::derive::gen_stub_pymethods)]
#[pymethods]
impl PiEnclosure {
    /// Serialize canonical exact certificate bytes as version1 JSON text.
    fn to_json(&self) -> PyResult<String> {
        self.inner.to_json().map_err(error)
    }
    /// Parse bounded evidence; parsing alone does not verify it.
    #[staticmethod]
    fn from_json(encoded: &str) -> PyResult<Self> {
        Certificate::from_json(encoded)
            .map(|inner| Self { inner })
            .map_err(error)
    }
    /// Claimed precision in bits.
    #[getter]
    fn precision(&self) -> u32 {
        self.inner.precision()
    }
    /// Claimed exact lower endpoint; use check before trusting it.
    #[getter]
    fn lower<'py>(&self, py: Python<'py>) -> PyResult<PyFraction<'py>> {
        let value = self.inner.lower().map_err(error)?;
        rational::fraction(
            py,
            Rational::from_big_rational(&value)
                .ok_or_else(|| BudgetExceeded::new_err("rational carrier"))?,
        )
    }
    /// Claimed exact upper endpoint; use check before trusting it.
    #[getter]
    fn upper<'py>(&self, py: Python<'py>) -> PyResult<PyFraction<'py>> {
        let value = self.inner.upper().map_err(error)?;
        rational::fraction(
            py,
            Rational::from_big_rational(&value)
                .ok_or_else(|| BudgetExceeded::new_err("rational carrier"))?,
        )
    }
    /// Replay against the original distinguished Pi expression, without search.
    fn check(&self, subject: &Expr) -> PiEnclosureReport {
        PiEnclosureReport {
            inner: self.inner.check(subject.inner()),
        }
    }
}
/// Acceptance, actual examined/discharged steps and any failed obligation.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyclass(module = "axeyum._native.cas")
)]
#[pyclass(frozen, from_py_object, module = "axeyum", name = "PiEnclosureReport")]
#[derive(Debug, Clone)]
pub struct PiEnclosureReport {
    inner: Report,
}
#[cfg_attr(feature = "stub-gen", pyo3_stub_gen::derive::gen_stub_pymethods)]
#[pymethods]
impl PiEnclosureReport {
    /// Whether replay discharged the certificate.
    #[getter]
    fn accepted(&self) -> bool {
        self.inner.accepted
    }
    /// Number of steps examined.
    #[getter]
    fn examined(&self) -> usize {
        self.inner.examined
    }
    /// Number of steps discharged; zero is never success.
    #[getter]
    fn discharged(&self) -> usize {
        self.inner.discharged
    }
    /// Failed obligation, or None for acceptance.
    #[getter]
    fn reason(&self) -> Option<String> {
        self.inner.reason.clone()
    }
}
/// Produce self-checked exact Machin bounds, up to 256 bits of precision.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.cas")
)]
#[pyfunction]
#[pyo3(signature=(precision=32))]
fn enclose_pi(precision: u32) -> PyResult<PiEnclosure> {
    axeyum_cas::pi_certificate::enclose_pi(precision)
        .map(|inner| PiEnclosure { inner })
        .map_err(error)
}
pub(crate) fn register(module: &Bound<'_, PyModule>) -> PyResult<()> {
    module.add_class::<PiEnclosure>()?;
    module.add_class::<PiEnclosureReport>()?;
    module.add_function(wrap_pyfunction!(enclose_pi, module)?)?;
    Ok(())
}
