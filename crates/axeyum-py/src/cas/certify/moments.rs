//! `axeyum.cas.certify.moments` — Wilf-Zeilberger certificates for binomial
//! moment identities.
//!
//! The route ships the shape every route here ships, and the split is the point:
//!
//! * a **producer** — `prove_squared_binomial_falling_moment`,
//!   `prove_squared_binomial_moment`, `prove_wz_sum` — which is untrusted and
//!   returns a typed certificate object, never a `bool`;
//! * a **certificate** carrying every distinction the producer made, so an
//!   independent caller can re-derive the identity. That is why `prove_wz_sum`
//!   binds a record of `(summand, n, k, rhs, base, k_lo, k_hi, multiplier)` and
//!   not the bare multiplier: the multiplier alone does not say *which* identity
//!   it certifies, and a checker handed only that cannot fail on the wrong one;
//! * a **checker** — `check()` — returning a report **with its counts**. A zero
//!   count is the fail signal.
//!
//! Both moment provers are bounded, and the bounds are constants here:
//! `MAX_PROVED_SQUARED_BINOMIAL_FALLING_MOMENT` (255) and
//! `MAX_PROVED_SQUARED_BINOMIAL_MOMENT` (35). Above them the producer returns
//! `None` *before any proof work*, which is a budget decision and not a claim
//! that the identity fails.

use axeyum_cas::{
    CasExpr, CertifiedSquaredBinomialFallingMoment as CasFallingMoment,
    CertifiedSquaredBinomialMoment as CasRawMoment, ZeroTest as CasZeroTest,
};
use pyo3::prelude::*;
use pyo3::types::{PyAny, PyModule};

use crate::cas::CasError;
use crate::cas::expr::Expr;

/// One discharged (or refused) proof obligation.
///
/// A checker that only returns `True`/`False` cannot say *what it looked at*.
/// This is what makes the report falsifiable: a caller counts obligations and a
/// zero count is a failure, not a pass.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyclass(module = "axeyum._native.cas.certify.moments")
)]
#[pyclass(frozen, from_py_object, module = "axeyum", name = "MomentObligation")]
#[derive(Debug, Clone)]
pub struct MomentObligation {
    name: String,
    detail: String,
    discharged: bool,
}

#[cfg_attr(feature = "stub-gen", pyo3_stub_gen::derive::gen_stub_pymethods)]
#[pymethods]
impl MomentObligation {
    /// The obligation's name.
    #[getter]
    fn name(&self) -> &str {
        &self.name
    }

    /// What was established, or why it was not.
    #[getter]
    fn detail(&self) -> &str {
        &self.detail
    }

    /// Whether this obligation was discharged.
    #[getter]
    fn discharged(&self) -> bool {
        self.discharged
    }

    fn __repr__(&self) -> String {
        format!(
            "MomentObligation({:?}, discharged={})",
            self.name, self.discharged
        )
    }
}

/// What a moment checker actually discharged.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyclass(module = "axeyum._native.cas.certify.moments")
)]
#[pyclass(frozen, from_py_object, module = "axeyum", name = "MomentCheckReport")]
#[derive(Debug, Clone)]
pub struct MomentCheckReport {
    obligations: Vec<MomentObligation>,
}

#[cfg_attr(feature = "stub-gen", pyo3_stub_gen::derive::gen_stub_pymethods)]
#[pymethods]
impl MomentCheckReport {
    /// The obligations, in the order the checker looked at them.
    #[getter]
    fn obligations(&self) -> Vec<MomentObligation> {
        self.obligations.clone()
    }

    /// How many obligations were discharged.
    #[getter]
    fn discharged(&self) -> usize {
        self.obligations
            .iter()
            .filter(|obligation| obligation.discharged)
            .count()
    }

    /// Whether every obligation was discharged **and** there was at least one.
    ///
    /// The second half is not decoration: an empty obligation list vacuously
    /// satisfies "every obligation held", and a checker that can pass without
    /// looking at anything is worse than no checker.
    fn accepted(&self) -> bool {
        !self.obligations.is_empty()
            && self
                .obligations
                .iter()
                .all(|obligation| obligation.discharged)
    }

    /// The number of obligations examined.
    fn __len__(&self) -> usize {
        self.obligations.len()
    }

    /// Whether nothing was examined — the fail signal.
    fn is_empty(&self) -> bool {
        self.obligations.is_empty()
    }

    fn __repr__(&self) -> String {
        format!(
            "MomentCheckReport(examined={}, discharged={}, accepted={})",
            self.obligations.len(),
            self.discharged(),
            self.accepted()
        )
    }
}

/// Builds a one-obligation report from a `bool` and its description.
fn one(name: &str, detail: &str, discharged: bool) -> MomentCheckReport {
    MomentCheckReport {
        obligations: vec![MomentObligation {
            name: name.to_owned(),
            detail: detail.to_owned(),
            discharged,
        }],
    }
}

/// A proved falling-factorial squared-binomial moment
/// `sum_k (k)_order * C(n, k) ** 2 == closed_form`, with its rational WZ
/// multiplier.
///
/// Tier C — certificate. Constructible from parts on purpose: a certificate is
/// portable data that may arrive from an untrusted producer, and rebuilding an
/// **edited** one is how a caller shows the checker can fail.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyclass(module = "axeyum._native.cas.certify.moments")
)]
#[pyclass(
    frozen,
    from_py_object,
    module = "axeyum",
    name = "CertifiedSquaredBinomialFallingMoment"
)]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CertifiedSquaredBinomialFallingMoment {
    inner: CasFallingMoment,
}

impl CertifiedSquaredBinomialFallingMoment {
    /// Wraps a Rust certificate.
    fn wrap(inner: CasFallingMoment) -> Self {
        Self { inner }
    }
}

#[cfg_attr(feature = "stub-gen", pyo3_stub_gen::derive::gen_stub_pymethods)]
#[pymethods]
impl CertifiedSquaredBinomialFallingMoment {
    /// A certificate from its parts.
    #[new]
    fn new(order: u32, closed_form: &Expr, certificate: &Expr) -> Self {
        Self {
            inner: CasFallingMoment {
                order,
                closed_form: closed_form.inner().clone(),
                certificate: certificate.inner().clone(),
            },
        }
    }

    /// The nonnegative falling-factorial order.
    #[getter]
    fn order(&self) -> u32 {
        self.inner.order
    }

    /// The exact closed form, as an expression in `n`.
    #[getter]
    fn closed_form(&self) -> Expr {
        Expr::wrap(self.inner.closed_form.clone())
    }

    /// The rational Wilf-Zeilberger multiplier `R(n, k)`.
    #[getter]
    fn certificate(&self) -> Expr {
        Expr::wrap(self.inner.certificate.clone())
    }

    /// Re-derives the WZ identity and the exact finite base case, returning the
    /// report.
    ///
    /// This is the *independent* half of the route: it reads only the stored
    /// order, closed form and multiplier, so a tampered certificate is rejected
    /// here rather than trusted because a producer once returned it.
    fn check(&self, py: Python<'_>) -> MomentCheckReport {
        let certified = py.detach(|| self.inner.is_certified());
        one(
            "wz-falling-moment",
            "symbolic WZ telescoping plus the exact finite base case, re-derived \
             from the stored order, closed form and multiplier",
            certified,
        )
    }

    /// Whether the certificate re-checks. Prefer [`Self::check`], which says
    /// what it looked at.
    fn is_certified(&self, py: Python<'_>) -> bool {
        py.detach(|| self.inner.is_certified())
    }

    fn __eq__(&self, other: &Bound<'_, PyAny>) -> bool {
        // `cast` + `get`, never `extract`: `extract` on a `#[pyclass]` CLONES the
        // whole wrapped value to compare it and then drops it.
        other
            .cast::<CertifiedSquaredBinomialFallingMoment>()
            .is_ok_and(|other| other.get().inner == self.inner)
    }

    fn __repr__(&self) -> String {
        format!(
            "CertifiedSquaredBinomialFallingMoment(order={})",
            self.inner.order
        )
    }
}

/// A proved squared-binomial raw moment `sum_k k ** moment * C(n, k) ** 2`,
/// carrying the WZ-certified falling-factorial components of its Stirling
/// expansion.
///
/// Tier C — certificate.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyclass(module = "axeyum._native.cas.certify.moments")
)]
#[pyclass(
    frozen,
    from_py_object,
    module = "axeyum",
    name = "CertifiedSquaredBinomialMoment"
)]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CertifiedSquaredBinomialMoment {
    inner: CasRawMoment,
}

#[cfg_attr(feature = "stub-gen", pyo3_stub_gen::derive::gen_stub_pymethods)]
#[pymethods]
impl CertifiedSquaredBinomialMoment {
    /// A certificate from its parts.
    #[new]
    fn new(
        moment: u32,
        closed_form: &Expr,
        components: Vec<CertifiedSquaredBinomialFallingMoment>,
    ) -> Self {
        Self {
            inner: CasRawMoment {
                moment,
                closed_form: closed_form.inner().clone(),
                components: components
                    .into_iter()
                    .map(|component| component.inner)
                    .collect(),
            },
        }
    }

    /// The nonnegative raw-moment order.
    #[getter]
    fn moment(&self) -> u32 {
        self.inner.moment
    }

    /// The exact closed form, as an expression in `n`.
    #[getter]
    fn closed_form(&self) -> Expr {
        Expr::wrap(self.inner.closed_form.clone())
    }

    /// The independently certified falling-factorial components, ascending.
    #[getter]
    fn components(&self) -> Vec<CertifiedSquaredBinomialFallingMoment> {
        self.inner
            .components
            .iter()
            .cloned()
            .map(CertifiedSquaredBinomialFallingMoment::wrap)
            .collect()
    }

    /// Re-derives every component WZ proof, the Stirling expansion and the
    /// reconstructed closed form, returning the report.
    ///
    /// The report carries one obligation per component **plus** the composite,
    /// so the count is the number of independent WZ proofs the acceptance rests
    /// on — a composite that rests on nothing is visible as a count of one.
    fn check(&self, py: Python<'_>) -> MomentCheckReport {
        let (composite, components): (bool, Vec<(u32, bool)>) = py.detach(|| {
            (
                self.inner.is_certified(),
                self.inner
                    .components
                    .iter()
                    .map(|component| (component.order, component.is_certified()))
                    .collect(),
            )
        });
        let mut obligations: Vec<MomentObligation> = components
            .into_iter()
            .map(|(order, discharged)| MomentObligation {
                name: format!("wz-falling-moment-{order}"),
                detail: "component WZ telescoping and base case".to_owned(),
                discharged,
            })
            .collect();
        obligations.push(MomentObligation {
            name: "stirling-composition".to_owned(),
            detail: "exact Stirling power expansion, per-component central-binomial \
                     quotient, and the independently reconstructed closed form"
                .to_owned(),
            discharged: composite,
        });
        MomentCheckReport { obligations }
    }

    /// Whether the certificate re-checks. Prefer [`Self::check`].
    fn is_certified(&self, py: Python<'_>) -> bool {
        py.detach(|| self.inner.is_certified())
    }

    fn __eq__(&self, other: &Bound<'_, PyAny>) -> bool {
        // `cast` + `get`, never `extract`: see the note in the falling-moment
        // certificate above.
        other
            .cast::<CertifiedSquaredBinomialMoment>()
            .is_ok_and(|other| other.get().inner == self.inner)
    }

    fn __repr__(&self) -> String {
        format!(
            "CertifiedSquaredBinomialMoment(moment={}, components={})",
            self.inner.moment,
            self.inner.components.len()
        )
    }
}

/// A Wilf-Zeilberger certificate for `sum_(k=k_lo)^(k_hi) F(n, k) == rhs(n)`.
///
/// Tier C — certificate. The Rust producer returns only the multiplier
/// `R(n, k)`; this record adds the seven inputs that say **which identity** the
/// multiplier certifies. Without them a checker cannot fail on the wrong
/// identity, which is the certificate defect this repository has already
/// measured once (`nra_monomial_bound_cert`).
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyclass(module = "axeyum._native.cas.certify.moments")
)]
#[pyclass(frozen, from_py_object, module = "axeyum", name = "WzCertificate")]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct WzCertificate {
    summand: CasExpr,
    n: String,
    k: String,
    rhs: CasExpr,
    base: i128,
    k_lo: i128,
    k_hi: i128,
    multiplier: CasExpr,
}

#[cfg_attr(feature = "stub-gen", pyo3_stub_gen::derive::gen_stub_pymethods)]
#[pymethods]
impl WzCertificate {
    /// A certificate from its parts, so an edited one can be handed to
    /// [`Self::check`].
    ///
    /// Eight arguments, and every one of them is load-bearing: they are exactly
    /// the identity the multiplier certifies. Grouping them into a struct would
    /// only move the arity, and dropping any of them is the certificate defect
    /// this module's header describes.
    #[new]
    #[allow(clippy::too_many_arguments)]
    fn new(
        summand: &Expr,
        n: &str,
        k: &str,
        rhs: &Expr,
        base: i128,
        k_lo: i128,
        k_hi: i128,
        multiplier: &Expr,
    ) -> Self {
        Self {
            summand: summand.inner().clone(),
            n: n.to_owned(),
            k: k.to_owned(),
            rhs: rhs.inner().clone(),
            base,
            k_lo,
            k_hi,
            multiplier: multiplier.inner().clone(),
        }
    }

    /// The summand `F(n, k)`.
    #[getter]
    fn summand(&self) -> Expr {
        Expr::wrap(self.summand.clone())
    }

    /// The outer summation variable's name.
    #[getter]
    fn n(&self) -> &str {
        &self.n
    }

    /// The inner summation variable's name.
    #[getter]
    fn k(&self) -> &str {
        &self.k
    }

    /// The claimed closed form `rhs(n)`.
    #[getter]
    fn rhs(&self) -> Expr {
        Expr::wrap(self.rhs.clone())
    }

    /// The concrete `n` at which the base case is pinned.
    #[getter]
    fn base(&self) -> i128 {
        self.base
    }

    /// The inclusive lower limit of the base-case summation.
    #[getter]
    fn k_lo(&self) -> i128 {
        self.k_lo
    }

    /// The inclusive upper limit of the base-case summation.
    #[getter]
    fn k_hi(&self) -> i128 {
        self.k_hi
    }

    /// The rational WZ multiplier `R(n, k)`.
    #[getter]
    fn multiplier(&self) -> Expr {
        Expr::wrap(self.multiplier.clone())
    }

    /// Re-derives the telescoping identity and the base case from the stored
    /// parts, returning the report.
    ///
    /// Two obligations, both re-derived through the public decidable zero test
    /// and neither reading anything the producer computed:
    ///
    /// * `wz-telescoping` — with `f = F / rhs` and `G = R * f`,
    ///   `G(n, k+1) - G(n, k) == f(n+1, k) - f(n, k)`;
    /// * `base-case` — `sum_(k=k_lo)^(k_hi) F(base, k) == rhs(base)` by exact
    ///   finite summation.
    ///
    /// An obligation the zero test leaves `Unknown` is **not discharged**: an
    /// undecided check is not a passing one.
    fn check(&self, py: Python<'_>) -> MomentCheckReport {
        let (telescoping, base_case) = py.detach(|| (self.telescoping(), self.base_case()));
        MomentCheckReport {
            obligations: vec![
                MomentObligation {
                    name: "wz-telescoping".to_owned(),
                    detail: "G(n, k+1) - G(n, k) == f(n+1, k) - f(n, k) for G = R * f, \
                             f = F / rhs, both variables symbolic"
                        .to_owned(),
                    discharged: telescoping,
                },
                MomentObligation {
                    name: "base-case".to_owned(),
                    detail: "sum over the stored k range of F(base, k) equals rhs(base), \
                             by exact finite summation"
                        .to_owned(),
                    discharged: base_case,
                },
            ],
        }
    }

    fn __eq__(&self, other: &Bound<'_, PyAny>) -> bool {
        // `cast` + `get`, never `extract`: see the note above.
        other.cast::<WzCertificate>().is_ok_and(|other| {
            let other = other.get();
            other.summand == self.summand
                && other.n == self.n
                && other.k == self.k
                && other.rhs == self.rhs
                && other.base == self.base
                && other.k_lo == self.k_lo
                && other.k_hi == self.k_hi
                && other.multiplier == self.multiplier
        })
    }

    fn __repr__(&self) -> String {
        format!(
            "WzCertificate(n={:?}, k={:?}, base={}, k_lo={}, k_hi={})",
            self.n, self.k, self.base, self.k_lo, self.k_hi
        )
    }
}

impl WzCertificate {
    /// `f = F / rhs`.
    fn normalized(&self) -> CasExpr {
        axeyum_cas::simplify(&CasExpr::Div(
            Box::new(self.summand.clone()),
            Box::new(self.rhs.clone()),
        ))
    }

    /// The symbolic telescoping obligation.
    fn telescoping(&self) -> bool {
        let f = self.normalized();
        let n_plus_one = CasExpr::var(&self.n) + CasExpr::int(1);
        let k_plus_one = CasExpr::var(&self.k) + CasExpr::int(1);
        let f_next_n = axeyum_cas::simplify(&f.substitute(&self.n, &n_plus_one));
        let g = axeyum_cas::simplify(&(self.multiplier.clone() * f.clone()));
        let g_next_k = axeyum_cas::simplify(&g.substitute(&self.k, &k_plus_one));
        let left = axeyum_cas::simplify(&(g_next_k - g));
        let right = axeyum_cas::simplify(&(f_next_n - f));
        matches!(
            axeyum_cas::equal(&left, &right),
            CasZeroTest::Certified { equal: true, .. }
        )
    }

    /// The exact finite base case.
    fn base_case(&self) -> bool {
        if self.k_hi < self.k_lo {
            return false;
        }
        let base = CasExpr::int(self.base);
        let mut total = CasExpr::int(0);
        let mut index = self.k_lo;
        while index <= self.k_hi {
            let term = self
                .summand
                .substitute(&self.n, &base)
                .substitute(&self.k, &CasExpr::int(index));
            total = axeyum_cas::simplify(&(total + term));
            index += 1;
        }
        let claimed = axeyum_cas::simplify(&self.rhs.substitute(&self.n, &base));
        matches!(
            axeyum_cas::equal(&total, &claimed),
            CasZeroTest::Certified { equal: true, .. }
        )
    }
}

/// Proves `sum_k (k)_order * C(n, k) ** 2 == (n)_order * C(2n-order, n-order)`.
///
/// Tier C — producer. `None` above
/// `MAX_PROVED_SQUARED_BINOMIAL_FALLING_MOMENT` is the budget refusing
/// *before* any proof work, not a failed proof.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.cas.certify.moments")
)]
#[pyfunction]
fn prove_squared_binomial_falling_moment(
    py: Python<'_>,
    order: u32,
) -> Option<CertifiedSquaredBinomialFallingMoment> {
    py.detach(|| axeyum_cas::prove_squared_binomial_falling_moment(order))
        .map(CertifiedSquaredBinomialFallingMoment::wrap)
}

/// Proves `sum_k k ** moment * C(n, k) ** 2 == closed_form`.
///
/// Tier C — producer. `None` above `MAX_PROVED_SQUARED_BINOMIAL_MOMENT` is the
/// budget refusing before any proof work.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.cas.certify.moments")
)]
#[pyfunction]
fn prove_squared_binomial_moment(
    py: Python<'_>,
    moment: u32,
) -> Option<CertifiedSquaredBinomialMoment> {
    py.detach(|| axeyum_cas::prove_squared_binomial_moment(moment))
        .map(|inner| CertifiedSquaredBinomialMoment { inner })
}

/// Discovers and symbolically verifies a WZ certificate for
/// `sum_(k=k_lo)^(k_hi) F(n, k) == rhs(n)`.
///
/// Tier C — producer. `None` means the discovery or the symbolic verification
/// declined, or the base case failed; the multiplier is never returned
/// unverified.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.cas.certify.moments")
)]
#[pyfunction]
#[allow(clippy::too_many_arguments)] // the seven inputs ARE the identity being proved
fn prove_wz_sum(
    py: Python<'_>,
    summand: &Expr,
    n: &str,
    k: &str,
    rhs: &Expr,
    base: i128,
    k_lo: i128,
    k_hi: i128,
) -> Option<WzCertificate> {
    let multiplier = py.detach(|| {
        axeyum_cas::prove_wz_sum(summand.inner(), n, k, rhs.inner(), base, k_lo, k_hi)
    })?;
    Some(WzCertificate {
        summand: summand.inner().clone(),
        n: n.to_owned(),
        k: k.to_owned(),
        rhs: rhs.inner().clone(),
        base,
        k_lo,
        k_hi,
        multiplier,
    })
}

/// `C(n, k)` as a symbolic expression, the shape the WZ route summands are
/// built from.
///
/// Tier R: a total builder.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.cas.certify.moments")
)]
#[pyfunction]
fn binomial_coefficient(n: &Expr, k: &Expr) -> Expr {
    Expr::wrap(axeyum_cas::binomial_coefficient(n.inner(), k.inner()))
}

/// Re-derives a checked closed-form claim symbolically, raising when nothing
/// was discharged.
///
/// Tier C — checker. Mirrors the `sos::check` guard: a report that examined no
/// obligation established nothing, and returning it as a pass is the failure
/// mode this whole module tree is documented against.
///
/// # Errors
///
/// Raises `CasError` when the report is empty.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.cas.certify.moments")
)]
#[pyfunction]
fn require_nonempty(report: &MomentCheckReport) -> PyResult<MomentCheckReport> {
    if report.obligations.is_empty() {
        return Err(CasError::new_err(
            "moment check discharged no obligation; an empty obligation list is \
             indistinguishable from a checker that did nothing",
        ));
    }
    Ok(report.clone())
}

/// Registers the `moments` route on `parent`.
///
/// # Errors
///
/// Propagates any Python error raised while creating or populating the module.
pub(crate) fn register(parent: &Bound<'_, PyModule>) -> PyResult<()> {
    let module = PyModule::new(parent.py(), "axeyum._native.cas.certify.moments")?;
    module.add_class::<MomentObligation>()?;
    module.add_class::<MomentCheckReport>()?;
    module.add_class::<CertifiedSquaredBinomialFallingMoment>()?;
    module.add_class::<CertifiedSquaredBinomialMoment>()?;
    module.add_class::<WzCertificate>()?;
    module.add(
        "MAX_PROVED_SQUARED_BINOMIAL_FALLING_MOMENT",
        axeyum_cas::MAX_PROVED_SQUARED_BINOMIAL_FALLING_MOMENT,
    )?;
    module.add(
        "MAX_PROVED_SQUARED_BINOMIAL_MOMENT",
        axeyum_cas::MAX_PROVED_SQUARED_BINOMIAL_MOMENT,
    )?;
    #[cfg(feature = "stub-gen")]
    pyo3_stub_gen::module_variable!(
        "axeyum._native.cas.certify.moments",
        "MAX_PROVED_SQUARED_BINOMIAL_FALLING_MOMENT",
        usize
    );
    #[cfg(feature = "stub-gen")]
    pyo3_stub_gen::module_variable!(
        "axeyum._native.cas.certify.moments",
        "MAX_PROVED_SQUARED_BINOMIAL_MOMENT",
        usize
    );
    module.add_function(wrap_pyfunction!(
        prove_squared_binomial_falling_moment,
        &module
    )?)?;
    module.add_function(wrap_pyfunction!(prove_squared_binomial_moment, &module)?)?;
    module.add_function(wrap_pyfunction!(prove_wz_sum, &module)?)?;
    module.add_function(wrap_pyfunction!(binomial_coefficient, &module)?)?;
    module.add_function(wrap_pyfunction!(require_nonempty, &module)?)?;
    parent.add("moments", &module)?;
    Ok(())
}
