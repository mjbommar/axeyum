//! `axeyum.cas.certify.telescoping` — Zeilberger's creative telescoping.
//!
//! The producer's own documentation says its result is **not verified**;
//! soundness lives entirely in `telescoping_check`, which re-derives the shift
//! ratios with its own implementation and shares no code with the search. That
//! is why `zeilberger` and `check` are separate calls here and never one
//! `prove()` returning a bool.

use std::collections::BTreeMap;

use axeyum_cas::telescoping::{
    Factor as CasFactor, HyperTerm as CasHyperTerm, Limits as CasLimits,
    LinearForm as CasLinearForm, TelescopingCertificate as CasTelescopingCertificate,
    TelescopingOutcome as CasTelescopingOutcome, binomial_factors as cas_binomial_factors,
    factorial_factor as cas_factorial_factor, zeilberger as cas_zeilberger,
};
use axeyum_cas::telescoping_check::{
    CheckOptions as CasCheckOptions, CheckReport as CasCheckReport, Verdict as CasVerdict,
    check_certificate, check_closed_form as cas_check_closed_form,
    check_closed_form_symbolic as cas_check_closed_form_symbolic,
};
use axeyum_cas::telescoping_json::{
    self, CertificateDocument as CasCertificateDocument, ClosedFormClaim as CasClosedFormClaim,
};
use pyo3::prelude::*;
use pyo3::types::{PyAny, PyModule};

use crate::cas::CasError;
use crate::cas::poly::MvPoly;
use crate::cas::rational;
use crate::cas::rational::RationalLike;
use crate::stub_types::PyBorrowedList;

/// An integer-linear form `sum(coefficient * variable) + constant`.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyclass(module = "axeyum._native.cas.certify.telescoping")
)]
#[pyclass(frozen, from_py_object, module = "axeyum", name = "LinearForm")]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LinearForm {
    inner: CasLinearForm,
}

#[cfg_attr(feature = "stub-gen", pyo3_stub_gen::derive::gen_stub_pymethods)]
#[pymethods]
impl LinearForm {
    /// A form from `[(variable, coefficient), ...]` and a constant.
    #[new]
    #[pyo3(signature = (terms, constant = 0))]
    fn new(terms: Vec<(String, i64)>, constant: i64) -> LinearForm {
        let borrowed: Vec<(&str, i64)> = terms
            .iter()
            .map(|(name, coefficient)| (name.as_str(), *coefficient))
            .collect();
        LinearForm {
            inner: CasLinearForm::new(&borrowed, constant),
        }
    }

    /// The coefficient of `var`, or `0`.
    fn coefficient(&self, var: &str) -> i64 {
        self.inner.coefficient(var)
    }

    /// The additive constant.
    #[getter]
    fn constant(&self) -> i64 {
        self.inner.constant()
    }

    /// The variables this form mentions, sorted.
    fn variables(&self) -> Vec<String> {
        self.inner.variables().into_iter().collect()
    }

    /// The same form as a polynomial, or `None` on overflow.
    fn to_poly(&self) -> Option<MvPoly> {
        MvPoly::wrap_option(self.inner.to_poly())
    }

    fn __repr__(&self) -> String {
        format!("LinearForm(constant={})", self.inner.constant())
    }
}

/// One factor of a hypergeometric term.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyclass(module = "axeyum._native.cas.certify.telescoping")
)]
#[pyclass(frozen, from_py_object, module = "axeyum", name = "Factor")]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Factor {
    inner: CasFactor,
}

#[cfg_attr(feature = "stub-gen", pyo3_stub_gen::derive::gen_stub_pymethods)]
#[pymethods]
impl Factor {
    /// `Gamma(form) ** exponent`. A negative exponent is a denominator.
    #[staticmethod]
    fn gamma(form: &LinearForm, exponent: i32) -> Factor {
        Factor {
            inner: CasFactor::Gamma {
                form: form.inner.clone(),
                exponent,
            },
        }
    }

    /// `base ** form` for a nonzero rational `base`.
    ///
    /// # Errors
    ///
    /// Raises `ValueError` when `base` is not an exact rational.
    #[staticmethod]
    fn power(base: RationalLike<'_>, form: &LinearForm) -> PyResult<Factor> {
        Ok(Factor {
            inner: CasFactor::Power {
                base: rational::from_py(base.as_any())?,
                form: form.inner.clone(),
            },
        })
    }

    /// `poly ** exponent`. A negative exponent is a denominator.
    #[staticmethod]
    fn poly(poly: &MvPoly, exponent: i32) -> Factor {
        Factor {
            inner: CasFactor::Poly {
                poly: poly.inner().clone(),
                exponent,
            },
        }
    }

    /// `"Gamma"`, `"Power"`, or `"Poly"`.
    #[getter]
    fn kind(&self) -> &'static str {
        match self.inner {
            CasFactor::Gamma { .. } => "Gamma",
            CasFactor::Power { .. } => "Power",
            CasFactor::Poly { .. } => "Poly",
        }
    }

    fn __repr__(&self) -> String {
        format!("Factor({})", self.kind())
    }
}

/// `(form)! ** exponent`, i.e. `Gamma(form + 1) ** exponent`.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.cas.certify.telescoping")
)]
#[pyfunction]
fn factorial_factor(form: &LinearForm, exponent: i32) -> Factor {
    Factor {
        inner: cas_factorial_factor(form.inner.clone(), exponent),
    }
}

/// The three gamma factors of `binomial(upper, lower) ** power`.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.cas.certify.telescoping")
)]
#[pyfunction]
fn binomial_factors(upper: &LinearForm, lower: &LinearForm, power: i32) -> Vec<Factor> {
    cas_binomial_factors(&upper.inner, &lower.inner, power)
        .into_iter()
        .map(|inner| Factor { inner })
        .collect()
}

/// A product of [`Factor`]s: the hypergeometric summand.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyclass(module = "axeyum._native.cas.certify.telescoping")
)]
#[pyclass(frozen, from_py_object, module = "axeyum", name = "HyperTerm")]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HyperTerm {
    inner: CasHyperTerm,
}

#[cfg_attr(feature = "stub-gen", pyo3_stub_gen::derive::gen_stub_pymethods)]
#[pymethods]
impl HyperTerm {
    /// A term from its factors, in the order supplied.
    #[new]
    fn new(factors: Vec<Factor>) -> HyperTerm {
        HyperTerm {
            inner: CasHyperTerm::new(factors.into_iter().map(|factor| factor.inner).collect()),
        }
    }

    /// The factors.
    #[getter]
    fn factors(&self) -> Vec<Factor> {
        self.inner
            .factors()
            .iter()
            .cloned()
            .map(|inner| Factor { inner })
            .collect()
    }

    /// Every variable the term mentions, sorted.
    fn variables(&self) -> Vec<String> {
        self.inner.variables().into_iter().collect()
    }

    fn __repr__(&self) -> String {
        format!("HyperTerm(factors={})", self.inner.factors().len())
    }
}

/// Search ceilings. Defaults are `Limits::classical()` verbatim:
/// `max_order=2`, `max_certificate_degree=8`, `max_unknowns=400`,
/// `max_poly_terms=4_000`, `max_dispersion=32`, `max_parameter_degree=6`.
///
/// None of these is a degree *ansatz*: starving one makes the search **decline**,
/// never mislead.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyclass(module = "axeyum._native.cas.certify.telescoping")
)]
#[pyclass(frozen, from_py_object, module = "axeyum", name = "Limits")]
#[derive(Debug, Clone, Copy)]
pub struct Limits {
    inner: CasLimits,
}

#[cfg_attr(feature = "stub-gen", pyo3_stub_gen::derive::gen_stub_pymethods)]
#[pymethods]
impl Limits {
    /// Ceilings, defaulting to `Limits::classical()`.
    #[new]
    #[pyo3(signature = (
        max_order = 2,
        max_certificate_degree = 8,
        max_unknowns = 400,
        max_poly_terms = 4_000,
        max_dispersion = 32,
        max_parameter_degree = 6,
    ))]
    fn new(
        max_order: usize,
        max_certificate_degree: u32,
        max_unknowns: usize,
        max_poly_terms: usize,
        max_dispersion: i64,
        max_parameter_degree: u32,
    ) -> Limits {
        Limits {
            inner: CasLimits {
                max_order,
                max_certificate_degree,
                max_unknowns,
                max_poly_terms,
                max_dispersion,
                max_parameter_degree,
            },
        }
    }

    /// The classical binomial-identity ceilings.
    #[staticmethod]
    fn classical() -> Limits {
        Limits {
            inner: CasLimits::classical(),
        }
    }

    /// The largest recurrence order searched.
    #[getter]
    fn max_order(&self) -> usize {
        self.inner.max_order
    }

    /// The largest derived certificate degree searched.
    #[getter]
    fn max_certificate_degree(&self) -> u32 {
        self.inner.max_certificate_degree
    }

    /// The largest linear system solved.
    #[getter]
    fn max_unknowns(&self) -> usize {
        self.inner.max_unknowns
    }

    /// The largest intermediate polynomial admitted.
    #[getter]
    fn max_poly_terms(&self) -> usize {
        self.inner.max_poly_terms
    }

    /// The largest dispersion admitted.
    #[getter]
    fn max_dispersion(&self) -> i64 {
        self.inner.max_dispersion
    }

    /// The largest parameter degree admitted.
    #[getter]
    fn max_parameter_degree(&self) -> u32 {
        self.inner.max_parameter_degree
    }

    fn __repr__(&self) -> String {
        format!(
            "Limits(max_order={}, max_certificate_degree={}, max_unknowns={}, \
             max_poly_terms={}, max_dispersion={}, max_parameter_degree={})",
            self.inner.max_order,
            self.inner.max_certificate_degree,
            self.inner.max_unknowns,
            self.inner.max_poly_terms,
            self.inner.max_dispersion,
            self.inner.max_parameter_degree
        )
    }
}

/// The counts an accepted telescoping certificate discharged.
///
/// A zero count is the fail signal: this is exactly the report a checker that
/// did nothing would produce, and it must be visible from Python.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyclass(module = "axeyum._native.cas.certify.telescoping")
)]
#[pyclass(frozen, from_py_object, module = "axeyum", name = "CheckReport")]
#[derive(Debug, Clone, Copy)]
pub struct CheckReport {
    inner: CasCheckReport,
}

#[cfg_attr(feature = "stub-gen", pyo3_stub_gen::derive::gen_stub_pymethods)]
#[pymethods]
impl CheckReport {
    /// Shift-ratio identities re-derived.
    #[getter]
    fn ratio_samples(&self) -> usize {
        self.inner.ratio_samples
    }

    /// Pointwise evaluations of the telescoping identity.
    #[getter]
    fn pointwise_samples(&self) -> usize {
        self.inner.pointwise_samples
    }

    /// Certificate poles found inside the replay window.
    #[getter]
    fn certificate_poles_in_window(&self) -> usize {
        self.inner.certificate_poles_in_window
    }

    /// Recurrence evaluations.
    #[getter]
    fn recurrence_samples(&self) -> usize {
        self.inner.recurrence_samples
    }

    fn __repr__(&self) -> String {
        format!(
            "CheckReport(ratio_samples={}, pointwise_samples={}, \
             certificate_poles_in_window={}, recurrence_samples={})",
            self.inner.ratio_samples,
            self.inner.pointwise_samples,
            self.inner.certificate_poles_in_window,
            self.inner.recurrence_samples
        )
    }
}

/// The verdict of the independent telescoping checker.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyclass(module = "axeyum._native.cas.certify.telescoping")
)]
#[pyclass(frozen, from_py_object, module = "axeyum", name = "Verdict")]
#[derive(Debug, Clone)]
pub struct Verdict {
    inner: CasVerdict,
}

#[cfg_attr(feature = "stub-gen", pyo3_stub_gen::derive::gen_stub_pymethods)]
#[pymethods]
impl Verdict {
    /// `"Verified"` or `"Rejected"`.
    #[getter]
    fn kind(&self) -> &'static str {
        match self.inner {
            CasVerdict::Verified(_) => "Verified",
            CasVerdict::Rejected(_) => "Rejected",
        }
    }

    /// Whether the certificate re-derived.
    fn is_verified(&self) -> bool {
        self.inner.is_verified()
    }

    /// The counts, on `Verified`.
    #[getter]
    fn report(&self) -> Option<CheckReport> {
        match self.inner {
            CasVerdict::Verified(report) => Some(CheckReport { inner: report }),
            CasVerdict::Rejected(_) => None,
        }
    }

    /// Every reason the certificate was rejected.
    #[getter]
    fn reasons(&self) -> Option<Vec<String>> {
        match &self.inner {
            CasVerdict::Verified(_) => None,
            CasVerdict::Rejected(reasons) => Some(reasons.clone()),
        }
    }

    fn __repr__(&self) -> String {
        match &self.inner {
            CasVerdict::Verified(report) => format!(
                "Verdict(Verified, ratio_samples={}, recurrence_samples={})",
                report.ratio_samples, report.recurrence_samples
            ),
            CasVerdict::Rejected(reasons) => format!("Verdict(Rejected, reasons={reasons:?})"),
        }
    }
}

/// The sample points and window the checker replays over.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyclass(module = "axeyum._native.cas.certify.telescoping")
)]
#[pyclass(frozen, from_py_object, module = "axeyum", name = "CheckOptions")]
#[derive(Debug, Clone)]
pub struct CheckOptions {
    inner: CasCheckOptions,
}

#[cfg_attr(feature = "stub-gen", pyo3_stub_gen::derive::gen_stub_pymethods)]
#[pymethods]
impl CheckOptions {
    /// Options over `shift_var` sampled at `points`, replayed on `window`.
    #[staticmethod]
    fn over(shift_var: &str, points: Vec<i64>, window: (i64, i64)) -> CheckOptions {
        CheckOptions {
            inner: CasCheckOptions::over(shift_var, &points, window),
        }
    }

    /// These options with `var` additionally sampled at `points`.
    ///
    /// Spelled `with_` because `with` is a Python keyword; the Rust method is
    /// `CheckOptions::with`.
    fn with_(&self, var: &str, points: Vec<i64>) -> CheckOptions {
        CheckOptions {
            inner: self.inner.clone().with(var, &points),
        }
    }

    /// The replay window `(low, high)`.
    #[getter]
    fn window(&self) -> (i64, i64) {
        self.inner.window
    }

    /// The minimum number of shift-ratio samples the checker demands.
    #[getter]
    fn min_ratio_samples(&self) -> usize {
        self.inner.min_ratio_samples
    }

    /// `{variable: [point, ...]}`.
    #[getter]
    fn samples(&self) -> &BTreeMap<String, Vec<i64>> {
        &self.inner.samples
    }

    fn __repr__(&self) -> String {
        format!(
            "CheckOptions(window={:?}, min_ratio_samples={}, variables={:?})",
            self.inner.window,
            self.inner.min_ratio_samples,
            self.inner.samples.keys().collect::<Vec<_>>()
        )
    }
}

/// The evidence that a verified recurrence pins the sum to a claimed closed
/// form.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyclass(module = "axeyum._native.cas.certify.telescoping")
)]
#[pyclass(frozen, from_py_object, module = "axeyum", name = "ClosedFormReport")]
#[derive(Debug, Clone)]
pub struct ClosedFormReport {
    base: i64,
    base_cases: usize,
    leading_zeros: Vec<i64>,
}

#[cfg_attr(feature = "stub-gen", pyo3_stub_gen::derive::gen_stub_pymethods)]
#[pymethods]
impl ClosedFormReport {
    /// The base index the identity is claimed from.
    #[getter]
    fn base(&self) -> i64 {
        self.base
    }

    /// Base cases checked by exact finite summation.
    #[getter]
    fn base_cases(&self) -> usize {
        self.base_cases
    }

    /// Integers at or above `base` where the leading coefficient vanishes.
    ///
    /// A nonempty list breaks the induction; the checker rejects rather than
    /// reports it, so a verified report always has this empty.
    #[getter]
    fn leading_zeros(&self) -> PyBorrowedList<'_, i64> {
        PyBorrowedList(&self.leading_zeros)
    }

    fn __repr__(&self) -> String {
        format!(
            "ClosedFormReport(base={}, base_cases={}, leading_zeros={:?})",
            self.base, self.base_cases, self.leading_zeros
        )
    }
}

/// What the **symbolic** closed-form checker established.
///
/// Two counts the concrete report does not have, and both are load-bearing:
/// `forced_support` is the interval outside which the summand is *proved* to
/// vanish, and `confirmed_zero_points` is how many window points were **checked**
/// to vanish rather than assumed. A symbolic base case over an unbounded
/// summation is only as good as that bound, so dropping either number would
/// leave a report that cannot be falsified.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyclass(module = "axeyum._native.cas.certify.telescoping")
)]
#[pyclass(
    frozen,
    from_py_object,
    module = "axeyum",
    name = "SymbolicClosedFormReport"
)]
#[derive(Debug, Clone)]
pub struct SymbolicClosedFormReport {
    base: i64,
    base_cases: usize,
    forced_support: (i64, i64),
    confirmed_zero_points: usize,
    leading_zeros: Vec<i64>,
}

#[cfg_attr(feature = "stub-gen", pyo3_stub_gen::derive::gen_stub_pymethods)]
#[pymethods]
impl SymbolicClosedFormReport {
    /// The base index the identity is claimed from.
    #[getter]
    fn base(&self) -> i64 {
        self.base
    }

    /// Base cases established at symbolic parameters by exact finite summation.
    #[getter]
    fn base_cases(&self) -> usize {
        self.base_cases
    }

    /// The `k` interval outside which the summand at the first base index is
    /// *forced* to vanish.
    #[getter]
    fn forced_support(&self) -> (i64, i64) {
        self.forced_support
    }

    /// Window points confirmed -- not assumed -- to vanish outside that support.
    #[getter]
    fn confirmed_zero_points(&self) -> usize {
        self.confirmed_zero_points
    }

    /// Integers at or above `base` where the leading coefficient vanishes.
    ///
    /// A nonempty list breaks the induction; the checker rejects rather than
    /// reports it, so a verified report always has this empty.
    #[getter]
    fn leading_zeros(&self) -> Vec<i64> {
        self.leading_zeros.clone()
    }

    fn __repr__(&self) -> String {
        format!(
            "SymbolicClosedFormReport(base={}, base_cases={}, forced_support={:?}, \
             confirmed_zero_points={}, leading_zeros={:?})",
            self.base,
            self.base_cases,
            self.forced_support,
            self.confirmed_zero_points,
            self.leading_zeros
        )
    }
}

/// A creative-telescoping certificate.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyclass(module = "axeyum._native.cas.certify.telescoping")
)]
#[pyclass(
    frozen,
    from_py_object,
    module = "axeyum",
    name = "TelescopingCertificate"
)]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TelescopingCertificate {
    inner: CasTelescopingCertificate,
}

impl TelescopingCertificate {
    /// Wraps a Rust certificate.
    fn wrap(inner: CasTelescopingCertificate) -> Self {
        Self { inner }
    }
}

#[cfg_attr(feature = "stub-gen", pyo3_stub_gen::derive::gen_stub_pymethods)]
#[pymethods]
impl TelescopingCertificate {
    /// The recurrence order.
    fn order(&self) -> usize {
        self.inner.order()
    }

    /// The summand.
    #[getter]
    fn term(&self) -> HyperTerm {
        HyperTerm {
            inner: self.inner.term.clone(),
        }
    }

    /// The parameter the recurrence is in.
    #[getter]
    fn shift_var(&self) -> &str {
        &self.inner.shift_var
    }

    /// The summation variable.
    #[getter]
    fn sum_var(&self) -> &str {
        &self.inner.sum_var
    }

    /// The recurrence coefficients, lowest shift first.
    #[getter]
    fn recurrence(&self) -> Vec<MvPoly> {
        MvPoly::wrap_vec(&self.inner.recurrence)
    }

    /// The certificate's rational-function numerator.
    #[getter]
    fn certificate_numerator(&self) -> MvPoly {
        MvPoly::wrap(self.inner.certificate_numerator.clone())
    }

    /// The certificate's rational-function denominator.
    #[getter]
    fn certificate_denominator(&self) -> MvPoly {
        MvPoly::wrap(self.inner.certificate_denominator.clone())
    }

    /// Independently re-derives this certificate, returning the verdict **with**
    /// its four report counts.
    fn check(&self, py: Python<'_>, options: &CheckOptions) -> Verdict {
        let certificate = self.inner.clone();
        let options = options.inner.clone();
        Verdict {
            inner: py.detach(|| check_certificate(&certificate, &options)),
        }
    }

    /// Checks a claimed closed form against this certificate's recurrence.
    ///
    /// # Errors
    ///
    /// Raises `CasError` carrying every reason the claim was not established.
    fn check_closed_form(
        &self,
        py: Python<'_>,
        closed_form: &HyperTerm,
        base: i64,
        options: &CheckOptions,
    ) -> PyResult<ClosedFormReport> {
        let certificate = self.inner.clone();
        let term = closed_form.inner.clone();
        let options = options.inner.clone();
        py.detach(|| cas_check_closed_form(&certificate, &term, base, &options))
            .map(|report| ClosedFormReport {
                base: report.base,
                base_cases: report.base_cases,
                leading_zeros: report.leading_zeros,
            })
            .map_err(|reasons| CasError::new_err(reasons.join("; ")))
    }

    /// Checks a claimed closed form **without specializing the remaining
    /// parameters**.
    ///
    /// This is the route for an identity with a symbolic parameter -- the
    /// Chu-Vandermonde shape -- where the concrete checker cannot settle the
    /// base cases at integers. Nothing is sampled: the summation collapses to
    /// the finitely many `k` a parameter-free Gamma forces, and the report says
    /// how many window points were *confirmed* zero rather than assumed.
    ///
    /// # Errors
    ///
    /// Raises `CasError` carrying every reason the claim was not established.
    fn check_closed_form_symbolic(
        &self,
        py: Python<'_>,
        closed_form: &HyperTerm,
        base: i64,
        options: &CheckOptions,
    ) -> PyResult<SymbolicClosedFormReport> {
        let certificate = self.inner.clone();
        let term = closed_form.inner.clone();
        let options = options.inner.clone();
        py.detach(|| cas_check_closed_form_symbolic(&certificate, &term, base, &options))
            .map(|report| SymbolicClosedFormReport {
                base: report.base,
                base_cases: report.base_cases,
                forced_support: report.forced_support,
                confirmed_zero_points: report.confirmed_zero_points,
                leading_zeros: report.leading_zeros,
            })
            .map_err(|reasons| CasError::new_err(reasons.join("; ")))
    }

    fn __eq__(&self, other: &Bound<'_, PyAny>) -> bool {
        // `cast` + `get`, never `extract`: `extract` on a `#[pyclass]` CLONES the
        // whole wrapped value -- an entire expression tree or certificate -- to
        // compare it and then drops it, and builds a `TypeError` object for the
        // ordinary `NotImplemented` case. `frozen` makes `Bound::get` a borrow
        // with no runtime borrow check at all.
        other
            .cast::<TelescopingCertificate>()
            .is_ok_and(|other| other.get().inner == self.inner)
    }

    fn __repr__(&self) -> String {
        format!(
            "TelescopingCertificate(order={}, shift_var={:?}, sum_var={:?})",
            self.inner.order(),
            self.inner.shift_var,
            self.inner.sum_var
        )
    }
}

/// The outcome of a creative-telescoping search: `Found` or `Declined`.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyclass(module = "axeyum._native.cas.certify.telescoping")
)]
#[pyclass(frozen, from_py_object, module = "axeyum", name = "TelescopingOutcome")]
#[derive(Debug, Clone)]
pub struct TelescopingOutcome {
    inner: CasTelescopingOutcome,
}

#[cfg_attr(feature = "stub-gen", pyo3_stub_gen::derive::gen_stub_pymethods)]
#[pymethods]
impl TelescopingOutcome {
    /// `"Found"` or `"Declined"`.
    #[getter]
    fn kind(&self) -> &'static str {
        match self.inner {
            CasTelescopingOutcome::Found(_) => "Found",
            CasTelescopingOutcome::Declined => "Declined",
        }
    }

    /// The certificate, when the search found one.
    ///
    /// It is **not** verified: run `check` before believing it.
    #[getter]
    fn certificate(&self) -> Option<TelescopingCertificate> {
        match &self.inner {
            CasTelescopingOutcome::Found(certificate) => {
                Some(TelescopingCertificate::wrap((**certificate).clone()))
            }
            CasTelescopingOutcome::Declined => None,
        }
    }

    fn __repr__(&self) -> String {
        format!("TelescopingOutcome({})", self.kind())
    }
}

/// Searches for a creative-telescoping certificate, smallest order first.
///
/// The result is an **unchecked** search output; soundness lives in `check`.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.cas.certify.telescoping")
)]
#[pyfunction]
#[pyo3(signature = (term, shift_var, sum_var, limits = None))]
fn zeilberger(
    py: Python<'_>,
    term: &HyperTerm,
    shift_var: &str,
    sum_var: &str,
    limits: Option<&Limits>,
) -> TelescopingOutcome {
    let limits = limits.map_or_else(CasLimits::classical, |limits| limits.inner);
    let term = term.inner.clone();
    let shift_var = shift_var.to_owned();
    let sum_var = sum_var.to_owned();
    TelescopingOutcome {
        inner: py.detach(|| cas_zeilberger(&term, &shift_var, &sum_var, &limits)),
    }
}

/// A certificate together with the options and closed-form claim it ships with.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyclass(module = "axeyum._native.cas.certify.telescoping")
)]
#[pyclass(
    frozen,
    from_py_object,
    module = "axeyum",
    name = "CertificateDocument"
)]
#[derive(Debug, Clone)]
pub struct CertificateDocument {
    inner: CasCertificateDocument,
}

#[cfg_attr(feature = "stub-gen", pyo3_stub_gen::derive::gen_stub_pymethods)]
#[pymethods]
impl CertificateDocument {
    /// A document from its parts.
    #[new]
    #[pyo3(signature = (id, title, certificate, options, closed_form = None, base = 0, symbolic = false))]
    fn new(
        id: &str,
        title: &str,
        certificate: &TelescopingCertificate,
        options: &CheckOptions,
        closed_form: Option<&HyperTerm>,
        base: i64,
        symbolic: bool,
    ) -> CertificateDocument {
        CertificateDocument {
            inner: CasCertificateDocument {
                id: id.to_owned(),
                title: title.to_owned(),
                certificate: certificate.inner.clone(),
                options: options.inner.clone(),
                closed_form: closed_form.map(|term| CasClosedFormClaim {
                    term: term.inner.clone(),
                    base,
                    symbolic,
                }),
            },
        }
    }

    /// The document identifier.
    #[getter]
    fn id(&self) -> &str {
        &self.inner.id
    }

    /// The document title.
    #[getter]
    fn title(&self) -> &str {
        &self.inner.title
    }

    /// The certificate.
    #[getter]
    fn certificate(&self) -> TelescopingCertificate {
        TelescopingCertificate::wrap(self.inner.certificate.clone())
    }

    /// The check options the document pins.
    #[getter]
    fn options(&self) -> CheckOptions {
        CheckOptions {
            inner: self.inner.options.clone(),
        }
    }

    /// The claimed closed form, when the document carries one.
    #[getter]
    fn closed_form(&self) -> Option<HyperTerm> {
        self.inner.closed_form.as_ref().map(|claim| HyperTerm {
            inner: claim.term.clone(),
        })
    }

    /// The deterministic JSON rendering.
    fn to_json(&self) -> String {
        telescoping_json::to_json(&self.inner)
    }

    /// Parses a document from its deterministic JSON rendering.
    ///
    /// # Errors
    ///
    /// Raises `CasError` when the text is not a well-formed document.
    #[staticmethod]
    fn from_json(text: &str) -> PyResult<CertificateDocument> {
        telescoping_json::from_json(text)
            .map(|inner| CertificateDocument { inner })
            .map_err(CasError::new_err)
    }

    fn __repr__(&self) -> String {
        format!("CertificateDocument({:?})", self.inner.id)
    }
}

/// Registers the `telescoping` route on `parent`.
///
/// # Errors
///
/// Propagates any Python error raised while creating or populating the module.
pub(crate) fn register(parent: &Bound<'_, PyModule>) -> PyResult<()> {
    let module = PyModule::new(parent.py(), "axeyum._native.cas.certify.telescoping")?;
    module.add_class::<LinearForm>()?;
    module.add_class::<Factor>()?;
    module.add_class::<HyperTerm>()?;
    module.add_class::<Limits>()?;
    module.add_class::<CheckOptions>()?;
    module.add_class::<CheckReport>()?;
    module.add_class::<Verdict>()?;
    module.add_class::<ClosedFormReport>()?;
    module.add_class::<SymbolicClosedFormReport>()?;
    module.add_class::<TelescopingCertificate>()?;
    module.add_class::<TelescopingOutcome>()?;
    module.add_class::<CertificateDocument>()?;
    module.add("FORMAT", telescoping_json::FORMAT)?;
    module.add("VERSION", telescoping_json::VERSION)?;
    module.add_function(wrap_pyfunction!(factorial_factor, &module)?)?;
    module.add_function(wrap_pyfunction!(binomial_factors, &module)?)?;
    module.add_function(wrap_pyfunction!(zeilberger, &module)?)?;
    parent.add("telescoping", &module)?;
    Ok(())
}

// Module-level constants reach Python through `module.add("NAME", value)`, a
// RUNTIME call with no item for a `#[gen_stub_*]` macro to sit on -- so without
// these submissions they exist in the extension and in no stub, and a checked
// consumer reading one gets an unresolved attribute. The type is named; the
// VALUE deliberately is not, so a constant cannot drift from its stub.
#[cfg(feature = "stub-gen")]
mod stub_variables {
    pyo3_stub_gen::module_variable!("axeyum._native.cas.certify.telescoping", "FORMAT", String);
    pyo3_stub_gen::module_variable!("axeyum._native.cas.certify.telescoping", "VERSION", u32);
}
