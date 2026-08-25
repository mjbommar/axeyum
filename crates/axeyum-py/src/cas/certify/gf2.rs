//! `axeyum.cas.certify.gf2` — Rabin irreducibility over GF(2).
//!
//! The one route in this crate with **two independent checkers**: a packed-word
//! one and a dense re-implementation that shares no code with it. Both are
//! bound, and `check_both` requires both, because one checker agreeing with its
//! own producer establishes less than it looks like.
//!
//! Three answers are kept apart, and conflating any two of them would be the
//! defect: a **reducible** polynomial is `None` (decided); a **rejected**
//! certificate is a verdict with a reason; a **budget or shape** refusal is a
//! `Gf2Error`.

use axeyum_cas::gf2::{
    self, FrobeniusReduction as CasFrobeniusReduction, Gf2Error as CasGf2Error,
    Gf2Limits as CasGf2Limits, Gf2Poly as CasGf2Poly,
    IrreducibilityCertificate as CasIrreducibilityCertificate, RabinBezout as CasRabinBezout,
};
use axeyum_cas::gf2_artifact::{
    self, ArtifactError as CasArtifactError, ArtifactLimits as CasArtifactLimits,
    HalfDegreeArtifact as CasHalfDegreeArtifact,
};
use axeyum_cas::gf2_independent::{
    IndependentCheckLimits as CasIndependentCheckLimits, check_irreducible_certificate_independent,
};
use pyo3::prelude::*;
use pyo3::types::{PyAny, PyModule};

use crate::cas::Gf2Error;

/// Maps a Rust GF(2) error onto the Python exception.
fn map_error(error: &CasGf2Error) -> PyErr {
    Gf2Error::new_err(error.to_string())
}

/// Whether an error is a *rejection of the certificate* rather than a refusal to
/// look at it.
///
/// `InvalidCertificate` is a verdict about the artifact; every other variant is a
/// budget or a shape the checker declined to spend on. Reporting a tripped
/// ceiling as "the certificate is wrong" would be the more dangerous of the two
/// mistakes, so they are kept apart here.
fn is_rejection(error: &CasGf2Error) -> bool {
    matches!(error, CasGf2Error::InvalidCertificate(_))
}

/// Resource ceilings for the packed-word GF(2) arithmetic.
///
/// Defaults are `Gf2Limits::default()` verbatim: `max_input_degree=4_096`,
/// `max_intermediate_degree=8_192`, `max_frobenius_steps=4_096`,
/// `max_word_ops=50_000_000`.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyclass(module = "axeyum._native.cas.certify.gf2")
)]
#[pyclass(frozen, from_py_object, module = "axeyum", name = "Gf2Limits")]
#[derive(Debug, Clone, Copy)]
pub struct Gf2Limits {
    inner: CasGf2Limits,
}

#[cfg_attr(feature = "stub-gen", pyo3_stub_gen::derive::gen_stub_pymethods)]
#[pymethods]
impl Gf2Limits {
    /// Ceilings, defaulting to the Rust `Gf2Limits::default()`.
    #[new]
    #[pyo3(signature = (
        max_input_degree = 4_096,
        max_intermediate_degree = 8_192,
        max_frobenius_steps = 4_096,
        max_word_ops = 50_000_000,
    ))]
    fn new(
        max_input_degree: usize,
        max_intermediate_degree: usize,
        max_frobenius_steps: usize,
        max_word_ops: u64,
    ) -> Gf2Limits {
        Gf2Limits {
            inner: CasGf2Limits {
                max_input_degree,
                max_intermediate_degree,
                max_frobenius_steps,
                max_word_ops,
            },
        }
    }

    /// Maximum degree of a candidate presented for checking.
    #[getter]
    fn max_input_degree(&self) -> usize {
        self.inner.max_input_degree
    }

    /// Maximum degree of an intermediate polynomial.
    #[getter]
    fn max_intermediate_degree(&self) -> usize {
        self.inner.max_intermediate_degree
    }

    /// Maximum Frobenius squarings in one certificate.
    #[getter]
    fn max_frobenius_steps(&self) -> usize {
        self.inner.max_frobenius_steps
    }

    /// Approximate word-level work ceiling.
    #[getter]
    fn max_word_ops(&self) -> u64 {
        self.inner.max_word_ops
    }

    fn __repr__(&self) -> String {
        format!(
            "Gf2Limits(max_input_degree={}, max_intermediate_degree={}, \
             max_frobenius_steps={}, max_word_ops={})",
            self.inner.max_input_degree,
            self.inner.max_intermediate_degree,
            self.inner.max_frobenius_steps,
            self.inner.max_word_ops
        )
    }
}

/// Resource ceilings for the dense independent checker.
///
/// Defaults: `max_degree=4_096`, `max_coefficient_ops=500_000_000`.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyclass(module = "axeyum._native.cas.certify.gf2")
)]
#[pyclass(
    frozen,
    from_py_object,
    module = "axeyum",
    name = "IndependentCheckLimits"
)]
#[derive(Debug, Clone, Copy)]
pub struct IndependentCheckLimits {
    inner: CasIndependentCheckLimits,
}

#[cfg_attr(feature = "stub-gen", pyo3_stub_gen::derive::gen_stub_pymethods)]
#[pymethods]
impl IndependentCheckLimits {
    /// Ceilings, defaulting to the Rust `IndependentCheckLimits::default()`.
    #[new]
    #[pyo3(signature = (max_degree = 4_096, max_coefficient_ops = 500_000_000))]
    fn new(max_degree: usize, max_coefficient_ops: u64) -> IndependentCheckLimits {
        IndependentCheckLimits {
            inner: CasIndependentCheckLimits {
                max_degree,
                max_coefficient_ops,
            },
        }
    }

    /// Maximum candidate degree.
    #[getter]
    fn max_degree(&self) -> usize {
        self.inner.max_degree
    }

    /// Maximum coefficient reads and XORs.
    #[getter]
    fn max_coefficient_ops(&self) -> u64 {
        self.inner.max_coefficient_ops
    }

    fn __repr__(&self) -> String {
        format!(
            "IndependentCheckLimits(max_degree={}, max_coefficient_ops={})",
            self.inner.max_degree, self.inner.max_coefficient_ops
        )
    }
}

/// A polynomial over GF(2), held as packed 64-bit words.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyclass(module = "axeyum._native.cas.certify.gf2")
)]
#[pyclass(frozen, from_py_object, module = "axeyum", name = "Gf2Poly")]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Gf2Poly {
    inner: CasGf2Poly,
}

impl Gf2Poly {
    /// Wraps a Rust polynomial.
    fn wrap(inner: CasGf2Poly) -> Self {
        Self { inner }
    }
}

#[cfg_attr(feature = "stub-gen", pyo3_stub_gen::derive::gen_stub_pymethods)]
#[pymethods]
impl Gf2Poly {
    /// A polynomial from the exponents whose coefficients are `1`.
    ///
    /// # Errors
    ///
    /// Raises `Gf2Error` when an exponent exceeds the degree ceiling.
    #[staticmethod]
    #[pyo3(signature = (exponents, limits = None))]
    fn from_exponents(exponents: Vec<usize>, limits: Option<&Gf2Limits>) -> PyResult<Gf2Poly> {
        let limits = limits.map_or_else(CasGf2Limits::default, |limits| limits.inner);
        CasGf2Poly::from_exponents(&exponents, limits)
            .map(Gf2Poly::wrap)
            .map_err(|error| map_error(&error))
    }

    /// A polynomial from its packed 64-bit words, least significant first.
    #[staticmethod]
    fn from_words(words: Vec<u64>) -> Gf2Poly {
        Gf2Poly::wrap(CasGf2Poly::from_words(words))
    }

    /// The zero polynomial.
    #[staticmethod]
    fn zero() -> Gf2Poly {
        Gf2Poly::wrap(CasGf2Poly::from_words(Vec::new()))
    }

    /// The constant `1`.
    #[staticmethod]
    fn one() -> Gf2Poly {
        Gf2Poly::wrap(CasGf2Poly::one())
    }

    /// The polynomial `x`.
    #[staticmethod]
    fn x() -> Gf2Poly {
        Gf2Poly::wrap(CasGf2Poly::x())
    }

    /// The degree, or `None` for the zero polynomial.
    fn degree(&self) -> Option<usize> {
        self.inner.degree()
    }

    /// Whether this is the zero polynomial.
    fn is_zero(&self) -> bool {
        self.inner.is_zero()
    }

    /// The coefficient of `x ** exponent`.
    fn coefficient(&self, exponent: usize) -> bool {
        self.inner.coefficient(exponent)
    }

    /// The exponents with coefficient `1`, ascending.
    fn exponents(&self) -> Vec<usize> {
        self.inner.exponents()
    }

    /// The packed words.
    fn words(&self) -> Vec<u64> {
        self.inner.words().to_vec()
    }

    /// Whether `f - x ** n` has degree at most `floor(n / 2)`.
    fn is_half_degree_shaped(&self) -> bool {
        self.inner.is_half_degree_shaped()
    }

    fn __eq__(&self, other: &Bound<'_, PyAny>) -> bool {
        // `cast` + `get`, never `extract`: `extract` on a `#[pyclass]` CLONES the
        // whole wrapped value -- an entire expression tree or certificate -- to
        // compare it and then drops it, and builds a `TypeError` object for the
        // ordinary `NotImplemented` case. `frozen` makes `Bound::get` a borrow
        // with no runtime borrow check at all.
        other
            .cast::<Gf2Poly>()
            .is_ok_and(|other| other.get().inner == self.inner)
    }

    fn __repr__(&self) -> String {
        format!("Gf2Poly(exponents={:?})", self.inner.exponents())
    }
}

/// One checker's answer about a certificate.
///
/// `accepted` is paired with the obligation counts the certificate carries, so a
/// caller can tell a checker that re-derived a 100-step Frobenius chain from one
/// that re-derived nothing.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyclass(module = "axeyum._native.cas.certify.gf2")
)]
#[pyclass(frozen, from_py_object, module = "axeyum", name = "Gf2Verdict")]
#[derive(Debug, Clone)]
pub struct Gf2Verdict {
    checker: &'static str,
    accepted: bool,
    reason: Option<String>,
    frobenius_steps: usize,
    bezout_obligations: usize,
}

#[cfg_attr(feature = "stub-gen", pyo3_stub_gen::derive::gen_stub_pymethods)]
#[pymethods]
impl Gf2Verdict {
    /// `"packed"` or `"independent"` — which implementation answered.
    #[getter]
    fn checker(&self) -> &'static str {
        self.checker
    }

    /// Whether this checker accepted the certificate.
    #[getter]
    fn accepted(&self) -> bool {
        self.accepted
    }

    /// Why it did not, when it did not.
    #[getter]
    fn reason(&self) -> Option<&str> {
        self.reason.as_deref()
    }

    /// Frobenius reductions the certificate carries, and this checker re-derived.
    #[getter]
    fn frobenius_steps(&self) -> usize {
        self.frobenius_steps
    }

    /// Bezout identities the certificate carries, one per distinct prime divisor
    /// of the degree.
    #[getter]
    fn bezout_obligations(&self) -> usize {
        self.bezout_obligations
    }

    fn __repr__(&self) -> String {
        format!(
            "Gf2Verdict({}, accepted={}, frobenius_steps={}, bezout_obligations={}, reason={:?})",
            self.checker, self.accepted, self.frobenius_steps, self.bezout_obligations, self.reason
        )
    }
}

/// Both checkers' answers about one certificate.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyclass(module = "axeyum._native.cas.certify.gf2")
)]
#[pyclass(frozen, from_py_object, module = "axeyum", name = "Gf2BothVerdict")]
#[derive(Debug, Clone)]
pub struct Gf2BothVerdict {
    primary: Gf2Verdict,
    independent: Gf2Verdict,
}

#[cfg_attr(feature = "stub-gen", pyo3_stub_gen::derive::gen_stub_pymethods)]
#[pymethods]
impl Gf2BothVerdict {
    /// The packed-word checker's answer.
    #[getter]
    fn primary(&self) -> Gf2Verdict {
        self.primary.clone()
    }

    /// The dense independent checker's answer.
    #[getter]
    fn independent(&self) -> Gf2Verdict {
        self.independent.clone()
    }

    /// Whether **both** checkers accepted.
    #[getter]
    fn accepted(&self) -> bool {
        self.primary.accepted && self.independent.accepted
    }

    fn __repr__(&self) -> String {
        format!(
            "Gf2BothVerdict(accepted={}, primary={}, independent={})",
            self.accepted(),
            self.primary.accepted,
            self.independent.accepted
        )
    }
}

/// One step of the Frobenius chain: `x ** (2 ** i) = quotient * f + remainder`.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyclass(module = "axeyum._native.cas.certify.gf2")
)]
#[pyclass(frozen, from_py_object, module = "axeyum", name = "FrobeniusReduction")]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FrobeniusReduction {
    inner: CasFrobeniusReduction,
}

#[cfg_attr(feature = "stub-gen", pyo3_stub_gen::derive::gen_stub_pymethods)]
#[pymethods]
impl FrobeniusReduction {
    /// A reduction from its quotient and remainder.
    #[new]
    fn new(quotient: &Gf2Poly, remainder: &Gf2Poly) -> FrobeniusReduction {
        FrobeniusReduction {
            inner: CasFrobeniusReduction {
                quotient: quotient.inner.clone(),
                remainder: remainder.inner.clone(),
            },
        }
    }

    /// The quotient multiplying the candidate polynomial.
    #[getter]
    fn quotient(&self) -> Gf2Poly {
        Gf2Poly::wrap(self.inner.quotient.clone())
    }

    /// The reduced residue.
    #[getter]
    fn remainder(&self) -> Gf2Poly {
        Gf2Poly::wrap(self.inner.remainder.clone())
    }

    fn __repr__(&self) -> String {
        format!(
            "FrobeniusReduction(remainder_degree={:?})",
            self.inner.remainder.degree()
        )
    }
}

/// Bezout evidence for one distinct prime divisor of the candidate degree.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyclass(module = "axeyum._native.cas.certify.gf2")
)]
#[pyclass(frozen, from_py_object, module = "axeyum", name = "RabinBezout")]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RabinBezout {
    inner: CasRabinBezout,
}

#[cfg_attr(feature = "stub-gen", pyo3_stub_gen::derive::gen_stub_pymethods)]
#[pymethods]
impl RabinBezout {
    /// An identity from its prime divisor and the two coefficients.
    #[new]
    fn new(
        prime_divisor: usize,
        polynomial_coefficient: &Gf2Poly,
        frobenius_coefficient: &Gf2Poly,
    ) -> RabinBezout {
        RabinBezout {
            inner: CasRabinBezout {
                prime_divisor,
                polynomial_coefficient: polynomial_coefficient.inner.clone(),
                frobenius_coefficient: frobenius_coefficient.inner.clone(),
            },
        }
    }

    /// The distinct prime divisor of the candidate degree.
    #[getter]
    fn prime_divisor(&self) -> usize {
        self.inner.prime_divisor
    }

    /// The coefficient of the candidate polynomial.
    #[getter]
    fn polynomial_coefficient(&self) -> Gf2Poly {
        Gf2Poly::wrap(self.inner.polynomial_coefficient.clone())
    }

    /// The coefficient of `r_(n/p) + x`.
    #[getter]
    fn frobenius_coefficient(&self) -> Gf2Poly {
        Gf2Poly::wrap(self.inner.frobenius_coefficient.clone())
    }

    fn __repr__(&self) -> String {
        format!("RabinBezout(prime_divisor={})", self.inner.prime_divisor)
    }
}

/// A portable Rabin irreducibility certificate.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyclass(module = "axeyum._native.cas.certify.gf2")
)]
#[pyclass(
    frozen,
    from_py_object,
    module = "axeyum",
    name = "IrreducibilityCertificate"
)]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IrreducibilityCertificate {
    inner: CasIrreducibilityCertificate,
}

impl IrreducibilityCertificate {
    /// Wraps a Rust certificate.
    fn wrap(inner: CasIrreducibilityCertificate) -> Self {
        Self { inner }
    }

    /// A verdict from one checker's result.
    fn verdict(
        &self,
        checker: &'static str,
        result: Result<(), CasGf2Error>,
    ) -> PyResult<Gf2Verdict> {
        let (accepted, reason) = match result {
            Ok(()) => (true, None),
            Err(error) if is_rejection(&error) => (false, Some(error.to_string())),
            Err(error) => return Err(map_error(&error)),
        };
        Ok(Gf2Verdict {
            checker,
            accepted,
            reason,
            frobenius_steps: self.inner.frobenius.len(),
            bezout_obligations: self.inner.bezout.len(),
        })
    }
}

#[cfg_attr(feature = "stub-gen", pyo3_stub_gen::derive::gen_stub_pymethods)]
#[pymethods]
impl IrreducibilityCertificate {
    /// A certificate from its parts.
    ///
    /// The certificate is *portable data* — it is meant to arrive from an
    /// untrusted producer over a wire — so reconstructing one from its parts is
    /// part of the surface, not a back door. It is also what makes the two
    /// checkers falsifiable from Python: hand them an edited chain and watch
    /// both reject it.
    #[new]
    fn new(
        polynomial: &Gf2Poly,
        frobenius: Vec<FrobeniusReduction>,
        bezout: Vec<RabinBezout>,
    ) -> IrreducibilityCertificate {
        IrreducibilityCertificate {
            inner: CasIrreducibilityCertificate {
                polynomial: polynomial.inner.clone(),
                frobenius: frobenius.into_iter().map(|item| item.inner).collect(),
                bezout: bezout.into_iter().map(|item| item.inner).collect(),
            },
        }
    }

    /// The Frobenius chain, in order.
    #[getter]
    fn frobenius(&self) -> Vec<FrobeniusReduction> {
        self.inner
            .frobenius
            .iter()
            .cloned()
            .map(|inner| FrobeniusReduction { inner })
            .collect()
    }

    /// The Bezout identities, one per distinct prime divisor of the degree.
    #[getter]
    fn bezout(&self) -> Vec<RabinBezout> {
        self.inner
            .bezout
            .iter()
            .cloned()
            .map(|inner| RabinBezout { inner })
            .collect()
    }

    /// The polynomial whose irreducibility is witnessed.
    #[getter]
    fn polynomial(&self) -> Gf2Poly {
        Gf2Poly::wrap(self.inner.polynomial.clone())
    }

    /// The number of Frobenius reductions carried.
    #[getter]
    fn frobenius_steps(&self) -> usize {
        self.inner.frobenius.len()
    }

    /// The distinct prime divisors of the degree the certificate covers.
    #[getter]
    fn bezout_prime_divisors(&self) -> Vec<usize> {
        self.inner
            .bezout
            .iter()
            .map(|identity| identity.prime_divisor)
            .collect()
    }

    /// The packed-word checker's answer.
    ///
    /// # Errors
    ///
    /// Raises `Gf2Error` on a budget or shape refusal. A *rejected* certificate
    /// is not an error: it comes back as `accepted == False` with a reason.
    #[pyo3(signature = (limits = None))]
    fn check_primary(&self, py: Python<'_>, limits: Option<&Gf2Limits>) -> PyResult<Gf2Verdict> {
        let limits = limits.map_or_else(CasGf2Limits::default, |limits| limits.inner);
        let certificate = self.inner.clone();
        let result = py.detach(|| gf2::check_irreducible_certificate(&certificate, limits));
        self.verdict("packed", result)
    }

    /// The dense independent checker's answer.
    ///
    /// # Errors
    ///
    /// Raises `Gf2Error` on a budget or shape refusal.
    #[pyo3(signature = (limits = None))]
    fn check_independent(
        &self,
        py: Python<'_>,
        limits: Option<&IndependentCheckLimits>,
    ) -> PyResult<Gf2Verdict> {
        let limits = limits.map_or_else(CasIndependentCheckLimits::default, |limits| limits.inner);
        let certificate = self.inner.clone();
        let result = py.detach(|| check_irreducible_certificate_independent(&certificate, limits));
        self.verdict("independent", result)
    }

    /// Both checkers. `accepted` is true only when **both** accept.
    ///
    /// # Errors
    ///
    /// Raises `Gf2Error` on a budget or shape refusal from either checker.
    #[pyo3(signature = (limits = None, independent_limits = None))]
    fn check_both(
        &self,
        py: Python<'_>,
        limits: Option<&Gf2Limits>,
        independent_limits: Option<&IndependentCheckLimits>,
    ) -> PyResult<Gf2BothVerdict> {
        Ok(Gf2BothVerdict {
            primary: self.check_primary(py, limits)?,
            independent: self.check_independent(py, independent_limits)?,
        })
    }

    fn __eq__(&self, other: &Bound<'_, PyAny>) -> bool {
        // `cast` + `get`, never `extract`: `extract` on a `#[pyclass]` CLONES the
        // whole wrapped value -- an entire expression tree or certificate -- to
        // compare it and then drops it, and builds a `TypeError` object for the
        // ordinary `NotImplemented` case. `frozen` makes `Bound::get` a borrow
        // with no runtime borrow check at all.
        other
            .cast::<IrreducibilityCertificate>()
            .is_ok_and(|other| other.get().inner == self.inner)
    }

    fn __repr__(&self) -> String {
        format!(
            "IrreducibilityCertificate(degree={:?}, frobenius_steps={}, bezout={})",
            self.inner.polynomial.degree(),
            self.inner.frobenius.len(),
            self.inner.bezout.len()
        )
    }
}

/// Produces an irreducibility certificate, or `None` for a **reducible**
/// polynomial.
///
/// `None` is a decided answer, not a decline.
///
/// # Errors
///
/// Raises `Gf2Error` for a zero or constant input and for typed degree,
/// Frobenius-step, or work-limit refusals.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.cas.certify.gf2")
)]
#[pyfunction]
#[pyo3(signature = (polynomial, limits = None))]
fn certify_irreducible(
    py: Python<'_>,
    polynomial: &Gf2Poly,
    limits: Option<&Gf2Limits>,
) -> PyResult<Option<IrreducibilityCertificate>> {
    let limits = limits.map_or_else(CasGf2Limits::default, |limits| limits.inner);
    let owned = polynomial.inner.clone();
    py.detach(|| gf2::certify_irreducible(&owned, limits))
        .map(|certificate| certificate.map(IrreducibilityCertificate::wrap))
        .map_err(|error| map_error(&error))
}

/// Ceilings for parsing and validating an on-disk artifact.
///
/// Defaults: `max_bytes=32 MiB`, `max_id_bytes=256`, `max_producer_bytes=256`,
/// with the two checkers' own defaults.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyclass(module = "axeyum._native.cas.certify.gf2")
)]
#[pyclass(frozen, from_py_object, module = "axeyum", name = "ArtifactLimits")]
#[derive(Debug, Clone, Copy)]
pub struct ArtifactLimits {
    inner: CasArtifactLimits,
}

#[cfg_attr(feature = "stub-gen", pyo3_stub_gen::derive::gen_stub_pymethods)]
#[pymethods]
impl ArtifactLimits {
    /// Ceilings, defaulting to the Rust `ArtifactLimits::default()`.
    #[new]
    #[pyo3(signature = (
        max_bytes = 32 * 1024 * 1024,
        max_id_bytes = 256,
        max_producer_bytes = 256,
        primary = None,
        independent = None,
    ))]
    fn new(
        max_bytes: usize,
        max_id_bytes: usize,
        max_producer_bytes: usize,
        primary: Option<&Gf2Limits>,
        independent: Option<&IndependentCheckLimits>,
    ) -> ArtifactLimits {
        ArtifactLimits {
            inner: CasArtifactLimits {
                max_bytes,
                max_id_bytes,
                max_producer_bytes,
                primary: primary.map_or_else(CasGf2Limits::default, |limits| limits.inner),
                independent: independent
                    .map_or_else(CasIndependentCheckLimits::default, |limits| limits.inner),
            },
        }
    }

    /// Maximum serialized input size, in bytes.
    #[getter]
    fn max_bytes(&self) -> usize {
        self.inner.max_bytes
    }

    /// Maximum identifier length, in bytes.
    #[getter]
    fn max_id_bytes(&self) -> usize {
        self.inner.max_id_bytes
    }

    /// Maximum producer-identity length, in bytes.
    #[getter]
    fn max_producer_bytes(&self) -> usize {
        self.inner.max_producer_bytes
    }

    fn __repr__(&self) -> String {
        format!(
            "ArtifactLimits(max_bytes={}, max_id_bytes={}, max_producer_bytes={})",
            self.inner.max_bytes, self.inner.max_id_bytes, self.inner.max_producer_bytes
        )
    }
}

/// A checked bounded witness together with the identity of the **untrusted**
/// producer that made it.
///
/// `producer` is the tier boundary made data: it records who to distrust, and it
/// is part of the canonical bytes.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyclass(module = "axeyum._native.cas.certify.gf2")
)]
#[pyclass(frozen, from_py_object, module = "axeyum", name = "HalfDegreeArtifact")]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HalfDegreeArtifact {
    inner: CasHalfDegreeArtifact,
}

/// Maps an artifact error onto the Python exception.
fn map_artifact_error(error: &CasArtifactError) -> PyErr {
    Gf2Error::new_err(error.to_string())
}

#[cfg_attr(feature = "stub-gen", pyo3_stub_gen::derive::gen_stub_pymethods)]
#[pymethods]
impl HalfDegreeArtifact {
    /// An artifact from an identifier, a producer identity, and a certificate.
    #[new]
    fn new(
        id: &str,
        producer: &str,
        certificate: &IrreducibilityCertificate,
    ) -> HalfDegreeArtifact {
        HalfDegreeArtifact {
            inner: CasHalfDegreeArtifact {
                id: id.to_owned(),
                producer: producer.to_owned(),
                certificate: certificate.inner.clone(),
            },
        }
    }

    /// The artifact identifier.
    #[getter]
    fn id(&self) -> &str {
        &self.inner.id
    }

    /// The untrusted producer's identity.
    #[getter]
    fn producer(&self) -> &str {
        &self.inner.producer
    }

    /// The certificate.
    #[getter]
    fn certificate(&self) -> IrreducibilityCertificate {
        IrreducibilityCertificate::wrap(self.inner.certificate.clone())
    }

    /// The canonical JSON bytes. Validates before serializing: fail-closed.
    ///
    /// # Errors
    ///
    /// Raises `Gf2Error` when the artifact does not validate.
    #[pyo3(signature = (limits = None))]
    fn to_canonical_json(
        &self,
        py: Python<'_>,
        limits: Option<&ArtifactLimits>,
    ) -> PyResult<String> {
        let limits = limits.map_or_else(CasArtifactLimits::default, |limits| limits.inner);
        let owned = self.inner.clone();
        py.detach(|| gf2_artifact::to_canonical_json(&owned, limits))
            .map_err(|error| map_artifact_error(&error))
    }

    /// Parses and fully validates canonical JSON.
    ///
    /// # Errors
    ///
    /// Raises `Gf2Error` for oversized input, malformed JSON, a broken format
    /// invariant, or a certificate either checker rejects.
    #[staticmethod]
    #[pyo3(signature = (text, limits = None))]
    fn from_canonical_json(
        py: Python<'_>,
        text: &str,
        limits: Option<&ArtifactLimits>,
    ) -> PyResult<HalfDegreeArtifact> {
        let limits = limits.map_or_else(CasArtifactLimits::default, |limits| limits.inner);
        let owned = text.to_owned();
        py.detach(|| gf2_artifact::from_canonical_json(&owned, limits))
            .map(|inner| HalfDegreeArtifact { inner })
            .map_err(|error| map_artifact_error(&error))
    }

    /// Re-validates this artifact, fail-closed.
    ///
    /// # Errors
    ///
    /// Raises `Gf2Error` with the first invariant that failed.
    #[pyo3(signature = (limits = None))]
    fn validate(&self, py: Python<'_>, limits: Option<&ArtifactLimits>) -> PyResult<()> {
        let limits = limits.map_or_else(CasArtifactLimits::default, |limits| limits.inner);
        let owned = self.inner.clone();
        py.detach(|| gf2_artifact::validate(&owned, limits))
            .map_err(|error| map_artifact_error(&error))
    }

    fn __eq__(&self, other: &Bound<'_, PyAny>) -> bool {
        // `cast` + `get`, never `extract`: `extract` on a `#[pyclass]` CLONES the
        // whole wrapped value -- an entire expression tree or certificate -- to
        // compare it and then drops it, and builds a `TypeError` object for the
        // ordinary `NotImplemented` case. `frozen` makes `Bound::get` a borrow
        // with no runtime borrow check at all.
        other
            .cast::<HalfDegreeArtifact>()
            .is_ok_and(|other| other.get().inner == self.inner)
    }

    fn __repr__(&self) -> String {
        format!(
            "HalfDegreeArtifact({:?}, producer={:?})",
            self.inner.id, self.inner.producer
        )
    }
}

/// Registers the `gf2` route on `parent`.
///
/// # Errors
///
/// Propagates any Python error raised while creating or populating the module.
pub(crate) fn register(parent: &Bound<'_, PyModule>) -> PyResult<()> {
    let module = PyModule::new(parent.py(), "axeyum._native.cas.certify.gf2")?;
    module.add_class::<Gf2Limits>()?;
    module.add_class::<IndependentCheckLimits>()?;
    module.add_class::<Gf2Poly>()?;
    module.add_class::<FrobeniusReduction>()?;
    module.add_class::<RabinBezout>()?;
    module.add_class::<Gf2Verdict>()?;
    module.add_class::<Gf2BothVerdict>()?;
    module.add_class::<IrreducibilityCertificate>()?;
    module.add_class::<ArtifactLimits>()?;
    module.add_class::<HalfDegreeArtifact>()?;
    module.add("FORMAT", gf2_artifact::FORMAT)?;
    module.add("VERSION", gf2_artifact::VERSION)?;
    module.add("STATEMENT", gf2_artifact::STATEMENT)?;
    module.add_function(wrap_pyfunction!(certify_irreducible, &module)?)?;
    parent.add("gf2", &module)?;
    Ok(())
}

// Module-level constants reach Python through `module.add("NAME", value)`, a
// RUNTIME call with no item for a `#[gen_stub_*]` macro to sit on -- so without
// these submissions they exist in the extension and in no stub, and a checked
// consumer reading one gets an unresolved attribute. The type is named; the
// VALUE deliberately is not, so a constant cannot drift from its stub.
#[cfg(feature = "stub-gen")]
mod stub_variables {
    pyo3_stub_gen::module_variable!("axeyum._native.cas.certify.gf2", "FORMAT", String);
    pyo3_stub_gen::module_variable!("axeyum._native.cas.certify.gf2", "STATEMENT", String);
    pyo3_stub_gen::module_variable!("axeyum._native.cas.certify.gf2", "VERSION", u32);
}
