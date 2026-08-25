//! `axeyum.cas` — finite-field arithmetic: `GF(p)[x]`, the GF(2) sparse search,
//! and the binary-extension trace reports.
//!
//! Three tiers live here and are named on every item.
//!
//! * **`gfp_*` (tier R)** — dense polynomial arithmetic mod a prime, coefficients
//!   ascending. Pure functions with no budget.
//! * **`search_sparse_half_degree` (tier P)** — a *producer*. It enumerates
//!   candidates under an explicit budget and returns a typed outcome carrying
//!   the counts, so `Exhausted` (every candidate was reducible) and
//!   `CandidateLimit` (the budget stopped the search) are different answers and
//!   neither is silently a failure. Its `Found` certificate is the same
//!   `cas.certify.gf2.IrreducibilityCertificate` the two independent checkers
//!   there accept or reject.
//! * **`binary_extension_*` (tier P)** — exact bounded enumerations whose reports
//!   are `Debug`-only in Rust. Every field is bound, none is summarised: a
//!   report that drops a field cannot be re-checked against the identity it
//!   claims, and these reports exist precisely to be re-checked.

use axeyum_cas::gf2_extension::{
    BinaryExtensionTraceError, BinaryExtensionTraceLimits as CasTraceLimits,
};
use axeyum_cas::gf2_search::{
    SparseSearchError, SparseSearchLimits as CasSparseSearchLimits,
    SparseSearchOutcome as CasSparseSearchOutcome,
};
use pyo3::prelude::*;
use pyo3::types::{PyAny, PyModule};

use crate::cas::Gf2Error;
use crate::cas::certify::gf2::{Gf2Limits, IrreducibilityCertificate};

/// A `BigInt`/`BigUint` as a Python `int`, exactly.
///
/// Rendered through the decimal string so no precision is lost — these values
/// routinely exceed `u128`, and a lossy conversion in a report that exists to be
/// re-checked would be worse than not binding it.
///
/// # Errors
///
/// Propagates any Python error raised while importing `builtins`.
fn big<'py>(py: Python<'py>, value: &impl std::fmt::Display) -> PyResult<Bound<'py, PyAny>> {
    PyModule::import(py, "builtins")?
        .getattr("int")?
        .call1((value.to_string(),))
}

// ------------------------------------------------------------------- GF(p)[x]

/// Binds `fn(&[i128], &[i128], i128) -> Vec<i128>`.
macro_rules! gfp_binary {
    ($py_name:ident, $name:ident, $doc:literal) => {
        #[doc = $doc]
        ///
        /// Tier R: a pure function. Coefficients are dense and ascending
        /// (index `i` is the coefficient of `x ** i`); `p` must be prime.
        #[cfg_attr(
            feature = "stub-gen",
            pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.cas")
        )]
        #[pyfunction]
        fn $py_name(a: Vec<i128>, b: Vec<i128>, p: i128) -> Vec<i128> {
            axeyum_cas::gfp::$name(&a, &b, p)
        }
    };
}

gfp_binary!(gfp_add, add, "Sum of two polynomials over `GF(p)`.");
gfp_binary!(gfp_sub, sub, "Difference of two polynomials over `GF(p)`.");
gfp_binary!(gfp_mul, mul, "Product of two polynomials over `GF(p)`.");
gfp_binary!(
    gfp_gcd,
    gcd,
    "Monic gcd of two polynomials over `GF(p)`; the zero polynomial for two zeros."
);

/// `c * a` over `GF(p)`.
///
/// Tier R: a pure function.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.cas")
)]
#[pyfunction]
fn gfp_scale(a: Vec<i128>, c: i128, p: i128) -> Vec<i128> {
    axeyum_cas::gfp::scale(&a, c, p)
}

/// `-a` over `GF(p)`.
///
/// Tier R: a pure function.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.cas")
)]
#[pyfunction]
fn gfp_neg(a: Vec<i128>, p: i128) -> Vec<i128> {
    axeyum_cas::gfp::neg(&a, p)
}

/// `(quotient, remainder)` of `a / b` over `GF(p)`, or `None` when `b` is zero.
///
/// Tier R: a pure function. Division by the **zero polynomial** is the
/// degenerate argument for this operator and is `None` — a decided answer, not
/// an exception and not a convention.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.cas")
)]
#[pyfunction]
fn gfp_div_rem(a: Vec<i128>, b: Vec<i128>, p: i128) -> Option<(Vec<i128>, Vec<i128>)> {
    axeyum_cas::gfp::div_rem(&a, &b, p)
}

/// `a ** e mod modulus` over `GF(p)`, or `None` for a zero modulus or overflow.
///
/// Tier R: a pure function.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.cas")
)]
#[pyfunction]
fn gfp_pow_mod(a: Vec<i128>, e: u64, modulus: Vec<i128>, p: i128) -> Option<Vec<i128>> {
    axeyum_cas::gfp::pow_mod(&a, e, &modulus, p)
}

/// Whether `a` is irreducible over `GF(p)`; `None` when undecided.
///
/// Tier R: a pure function.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.cas")
)]
#[pyfunction]
fn gfp_is_irreducible(a: Vec<i128>, p: i128) -> Option<bool> {
    axeyum_cas::gfp::is_irreducible(&a, p)
}

/// The Berlekamp factorization as `[(factor, multiplicity), ...]`, or `None`.
///
/// Tier R: a pure function. The factors are the witness: multiplying them back
/// together is how a caller checks this without trusting it.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.cas")
)]
#[pyfunction]
fn gfp_factor_berlekamp(a: Vec<i128>, p: i128) -> Option<Vec<(Vec<i128>, u32)>> {
    axeyum_cas::gfp::factor_berlekamp(&a, p)
}

/// The roots of `a` in `GF(p)`, ascending.
///
/// Tier R: a pure function.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.cas")
)]
#[pyfunction]
fn gfp_roots(a: Vec<i128>, p: i128) -> Vec<i128> {
    axeyum_cas::gfp::roots(&a, p)
}

// --------------------------------------------------------- GF(2) sparse search

/// Explicit ceilings for one degree's sparse GF(2) search.
///
/// Tier P. Defaults are the Rust `SparseSearchLimits::default()` verbatim:
/// `max_tail_terms=4`, `max_candidates=2_000_000`, and `Gf2Limits::default()`
/// arithmetic.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyclass(module = "axeyum._native.cas")
)]
#[pyclass(frozen, from_py_object, module = "axeyum", name = "SparseSearchLimits")]
#[derive(Debug, Clone, Copy)]
pub struct SparseSearchLimits {
    inner: CasSparseSearchLimits,
}

#[cfg_attr(feature = "stub-gen", pyo3_stub_gen::derive::gen_stub_pymethods)]
#[pymethods]
impl SparseSearchLimits {
    /// Ceilings, defaulting to the Rust `SparseSearchLimits::default()`.
    #[new]
    #[pyo3(signature = (max_tail_terms = 4, max_candidates = 2_000_000, arithmetic = None))]
    fn new(
        max_tail_terms: usize,
        max_candidates: u64,
        arithmetic: Option<Gf2Limits>,
    ) -> SparseSearchLimits {
        SparseSearchLimits {
            inner: CasSparseSearchLimits {
                max_tail_terms,
                max_candidates,
                arithmetic: arithmetic.map_or_else(Default::default, Gf2Limits::into_inner),
            },
        }
    }

    /// Largest even number of nonleading terms enumerated.
    #[getter]
    fn max_tail_terms(&self) -> usize {
        self.inner.max_tail_terms
    }

    /// Maximum candidates tested for this degree.
    #[getter]
    fn max_candidates(&self) -> u64 {
        self.inner.max_candidates
    }

    /// The per-candidate arithmetic and certificate ceilings.
    #[getter]
    fn arithmetic(&self) -> Gf2Limits {
        Gf2Limits::from_inner(self.inner.arithmetic)
    }

    fn __repr__(&self) -> String {
        format!(
            "SparseSearchLimits(max_tail_terms={}, max_candidates={})",
            self.inner.max_tail_terms, self.inner.max_candidates
        )
    }
}

/// One deterministic sparse-search result, with its counts.
///
/// Tier P. `kind` is `"Found"`, `"Exhausted"` or `"CandidateLimit"`, and the
/// three are **different answers**: `Exhausted` says every candidate through
/// `max_tail_terms` was reducible, `CandidateLimit` says the budget stopped the
/// enumeration and claims nothing about the remaining candidates.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyclass(module = "axeyum._native.cas")
)]
#[pyclass(
    frozen,
    from_py_object,
    module = "axeyum",
    name = "SparseSearchOutcome"
)]
#[derive(Debug, Clone)]
pub struct SparseSearchOutcome {
    inner: CasSparseSearchOutcome,
}

#[cfg_attr(feature = "stub-gen", pyo3_stub_gen::derive::gen_stub_pymethods)]
#[pymethods]
impl SparseSearchOutcome {
    /// `"Found"`, `"Exhausted"` or `"CandidateLimit"`.
    #[getter]
    fn kind(&self) -> &'static str {
        match self.inner {
            CasSparseSearchOutcome::Found { .. } => "Found",
            CasSparseSearchOutcome::Exhausted { .. } => "Exhausted",
            CasSparseSearchOutcome::CandidateLimit { .. } => "CandidateLimit",
        }
    }

    /// The certificate of the polynomial that was found, or `None`.
    ///
    /// Hand it to `cas.certify.gf2.check_certificate` /
    /// `check_certificate_independent`: the producer here is untrusted, and the
    /// certificate is what makes it checkable.
    #[getter]
    fn certificate(&self) -> Option<IrreducibilityCertificate> {
        match &self.inner {
            CasSparseSearchOutcome::Found { certificate, .. } => {
                Some(IrreducibilityCertificate::wrap(certificate.clone()))
            }
            _ => None,
        }
    }

    /// How many candidates were tested, in every outcome.
    #[getter]
    fn candidates_tested(&self) -> u64 {
        match self.inner {
            CasSparseSearchOutcome::Found {
                candidates_tested, ..
            }
            | CasSparseSearchOutcome::Exhausted { candidates_tested }
            | CasSparseSearchOutcome::CandidateLimit {
                candidates_tested, ..
            } => candidates_tested,
        }
    }

    /// The number of nonleading terms in the successful polynomial, or `None`.
    #[getter]
    fn tail_terms(&self) -> Option<usize> {
        match self.inner {
            CasSparseSearchOutcome::Found { tail_terms, .. } => Some(tail_terms),
            _ => None,
        }
    }

    /// The configured candidate ceiling that stopped the search, or `None`.
    #[getter]
    fn limit(&self) -> Option<u64> {
        match self.inner {
            CasSparseSearchOutcome::CandidateLimit { limit, .. } => Some(limit),
            _ => None,
        }
    }

    fn __repr__(&self) -> String {
        format!(
            "SparseSearchOutcome({}, candidates_tested={})",
            self.kind(),
            self.candidates_tested()
        )
    }
}

/// Enumerates sparse `GF(2)` candidates of `degree` in a stable order and
/// returns the first one with a dual-checkable irreducibility certificate.
///
/// Tier P: a *producer* under an explicit budget. It never claims a polynomial
/// does not exist beyond the searched sparse layers — that is what the
/// `Exhausted` / `CandidateLimit` distinction is for.
///
/// # Errors
///
/// Raises `Gf2Error` for a malformed policy (`max_tail_terms` must be a
/// positive even number) or a typed arithmetic/resource decline.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.cas")
)]
#[pyfunction]
#[pyo3(signature = (degree, limits = None))]
fn search_sparse_half_degree(
    py: Python<'_>,
    degree: usize,
    limits: Option<SparseSearchLimits>,
) -> PyResult<SparseSearchOutcome> {
    let limits = limits.map_or_else(CasSparseSearchLimits::default, |limits| limits.inner);
    py.detach(|| axeyum_cas::gf2_search::search_sparse_half_degree(degree, limits))
        .map(|inner| SparseSearchOutcome { inner })
        .map_err(|error: SparseSearchError| Gf2Error::new_err(error.to_string()))
}

// --------------------------------------------------- binary-extension traces

/// Deterministic limits for one extension-field interval trace.
///
/// Tier P. Defaults are the Rust `BinaryExtensionTraceLimits::default()`
/// verbatim: `max_field_degree=8`, `max_polynomial_degree=16`,
/// `max_candidates=1_000_000`.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyclass(module = "axeyum._native.cas")
)]
#[pyclass(
    frozen,
    from_py_object,
    module = "axeyum",
    name = "BinaryExtensionTraceLimits"
)]
#[derive(Debug, Clone, Copy)]
pub struct BinaryExtensionTraceLimits {
    inner: CasTraceLimits,
}

#[cfg_attr(feature = "stub-gen", pyo3_stub_gen::derive::gen_stub_pymethods)]
#[pymethods]
impl BinaryExtensionTraceLimits {
    /// Ceilings, defaulting to the Rust `BinaryExtensionTraceLimits::default()`.
    #[new]
    #[pyo3(signature = (
        max_field_degree = 8,
        max_polynomial_degree = 16,
        max_candidates = 1_000_000,
    ))]
    fn new(
        max_field_degree: usize,
        max_polynomial_degree: usize,
        max_candidates: u64,
    ) -> BinaryExtensionTraceLimits {
        BinaryExtensionTraceLimits {
            inner: CasTraceLimits {
                max_field_degree,
                max_polynomial_degree,
                max_candidates,
            },
        }
    }

    /// Largest admitted extension degree `r` in `GF(2 ** r)`.
    #[getter]
    fn max_field_degree(&self) -> usize {
        self.inner.max_field_degree
    }

    /// Largest admitted polynomial degree.
    #[getter]
    fn max_polynomial_degree(&self) -> usize {
        self.inner.max_polynomial_degree
    }

    /// Largest admitted interval population.
    #[getter]
    fn max_candidates(&self) -> u64 {
        self.inner.max_candidates
    }

    fn __repr__(&self) -> String {
        format!(
            "BinaryExtensionTraceLimits(max_field_degree={}, max_polynomial_degree={}, \
             max_candidates={})",
            self.inner.max_field_degree,
            self.inner.max_polynomial_degree,
            self.inner.max_candidates
        )
    }
}

/// Maps a typed trace decline onto `Gf2Error`, preserving the reason.
fn trace_error(error: &BinaryExtensionTraceError) -> PyErr {
    Gf2Error::new_err(error.to_string())
}

/// Declares a frozen record over a `Debug`-only Rust report.
///
/// Every field of the Rust struct appears; nothing is summarised. `plain`
/// fields cross as their own Python type, `big` fields as exact Python `int`
/// through their decimal rendering.
macro_rules! trace_report {
    (
        $wrapper:ident, $inner:ty, $pyname:literal, $doc:literal,
        $( plain $pf:ident : $pt:ty , $pd:literal ; )*
        $( big $bf:ident , $bd:literal ; )*
    ) => {
        #[doc = $doc]
        ///
        /// Tier P: a frozen record of an exact bounded enumeration. Every field
        /// of the Rust report is present.
        #[cfg_attr(feature = "stub-gen", pyo3_stub_gen::derive::gen_stub_pyclass(module = "axeyum._native.cas"))]
        #[pyclass(frozen, from_py_object, module = "axeyum", name = $pyname)]
        #[derive(Debug, Clone)]
        pub struct $wrapper {
            inner: $inner,
        }

        #[cfg_attr(feature = "stub-gen", pyo3_stub_gen::derive::gen_stub_pymethods)]
        #[pymethods]
        impl $wrapper {
            $(
                #[doc = $pd]
                #[getter]
                fn $pf(&self) -> $pt {
                    self.inner.$pf
                }
            )*
            $(
                #[doc = $bd]
                ///
                /// # Errors
                ///
                /// Propagates any Python error raised while building the `int`.
                #[getter]
                fn $bf<'py>(&self, py: Python<'py>) -> PyResult<Bound<'py, PyAny>> {
                    big(py, &self.inner.$bf)
                }
            )*

            fn __repr__(&self) -> String {
                concat!($pyname, "(...)").to_owned()
            }
        }
    };
}

trace_report!(
    BinaryExtensionLongCycleTraceReport,
    axeyum_cas::gf2_extension::BinaryExtensionLongCycleTraceReport,
    "BinaryExtensionLongCycleTraceReport",
    "Exact fixed-degree long-cycle trace over one binary extension field.",
    plain field_modulus: u64, "Packed monic irreducible modulus defining the field.";
    plain field_degree: usize, "Extension degree `r`.";
    plain field_order: u64, "Field order `2 ** r`.";
    plain polynomial_degree: usize, "Degree of every monic polynomial in the interval.";
    plain fixed_leading_coefficients: usize, "Prescribed zero next-to-leading coefficients.";
    plain free_coefficients: usize, "Free low coefficients.";
    plain candidate_count: u64, "Exact interval population.";
    plain mangoldt_sum: u128, "Exact orbit-weighted Mangoldt sum.";
    plain error: i128, "The signed long-cycle diagnostic.";
);

trace_report!(
    BinaryExtensionConnectedAdamsTraceReport,
    axeyum_cas::gf2_extension::BinaryExtensionConnectedAdamsTraceReport,
    "BinaryExtensionConnectedAdamsTraceReport",
    "Exact connected endpoint trace over one binary extension field.",
    plain field_modulus: u64, "Packed monic irreducible modulus defining the field.";
    plain field_degree: usize, "Extension degree `r`.";
    plain field_order: u64, "Field order `2 ** r`.";
    plain ell: usize, "Number of constrained next-to-leading coefficients.";
    plain polynomial_degree: usize, "Degree of every monic polynomial counted.";
    plain class_count: u64, "Number of coefficient classes.";
    plain candidate_count: u64, "Exact total population.";
    plain uniform_mean: u64, "The uniform per-class population.";
    plain identity_class_mangoldt_sum: u128, "Mangoldt mass of the identity class.";
    plain satisfies_candidate_bound: bool, "Whether the stopping test held.";
    big centered_second_moment, "Exact `M_2`.";
    big centered_fourth_moment, "Exact `M_4`.";
    big fourth_cumulant_numerator, "Exact `q ** ell * M_4 - 3 * M_2 ** 2`.";
    big connected_adams_trace, "Exact `T_r`.";
    big candidate_absolute_bound, "The absolute stopping bound.";
    big minimum_normalized_betti_ceiling, "Least normalized Betti ceiling.";
);

trace_report!(
    BinaryExtensionWittShiftedLayerTrace,
    axeyum_cas::gf2_extension::BinaryExtensionWittShiftedLayerTrace,
    "BinaryExtensionWittShiftedLayerTrace",
    "One signed low-twist layer of a Witt-shifted trace.",
    plain layer: usize, "The layer index.";
    plain average_contraction_holds: bool, "Whether the average contraction identity held.";
    big identity_aggregate_mass, "Aggregate mass on the identity path.";
    big parent_aggregate_mass, "Aggregate mass on the parent path.";
    big signed_spatial_layer, "The signed spatial layer value.";
    big signed_high_character_trace, "The signed high-character trace.";
);

trace_report!(
    BinaryExtensionEllTwoDegreeFiveClosedForm,
    axeyum_cas::gf2_extension::BinaryExtensionEllTwoDegreeFiveClosedForm,
    "BinaryExtensionEllTwoDegreeFiveClosedForm",
    "Closed form of the `ell = 2`, degree-five connected Adams trace.",
    plain field_degree: usize, "Extension degree `r` in `q = 2 ** r`.";
    plain connected_trace_q_degree: usize, "Leading `q`-degree of the connected trace.";
    plain adams_weight_q_degree: usize, "`q`-degree of the Adams weight.";
    plain normalized_connected_q_degree: usize, "`q`-degree after normalization.";
    plain proposed_normalized_q_degree: usize, "The proposed universal cutoff.";
    plain normalized_q_degree_excess: usize, "How far the closed form exceeds it.";
    big field_order, "Field order `q`.";
    big zero_subtrace_population, "Population with zero subtrace.";
    big nonzero_subtrace_population, "Population with nonzero subtrace.";
    big centered_second_moment, "Exact `M_2`.";
    big centered_fourth_moment, "Exact `M_4`.";
    big fourth_cumulant_numerator, "Exact fourth-cumulant numerator.";
    big connected_adams_trace, "Exact `T_r`.";
);

trace_report!(
    BinaryExtensionEllThreeDegreeSevenClosedForm,
    axeyum_cas::gf2_extension::BinaryExtensionEllThreeDegreeSevenClosedForm,
    "BinaryExtensionEllThreeDegreeSevenClosedForm",
    "Closed form of the `ell = 3`, degree-seven connected Adams trace.",
    plain field_degree: usize, "Extension degree `r` in `q = 2 ** r`.";
    plain connected_trace_q_degree: usize, "Leading `q`-degree of the connected trace.";
    plain adams_weight_q_degree: usize, "`q`-degree of the Adams weight.";
    plain normalized_connected_q_degree: usize, "`q`-degree after normalization.";
    plain proposed_normalized_q_degree: usize, "The proposed universal cutoff.";
    plain one_extra_q_normalized_degree: usize, "The cutoff with one extra `q`.";
    plain normalized_q_degree_excess: usize, "How far the closed form exceeds it.";
    big field_order, "Field order `q`.";
    big special_class_count, "Number of special classes.";
    big ordinary_class_count, "Number of ordinary classes.";
    big special_class_population, "Population of a special class.";
    big ordinary_class_population, "Population of an ordinary class.";
    big centered_second_moment, "Exact `M_2`.";
    big centered_fourth_moment, "Exact `M_4`.";
    big fourth_cumulant_numerator, "Exact fourth-cumulant numerator.";
    big connected_adams_trace, "Exact `T_r`.";
);

trace_report!(
    BinaryExtensionEllThreeDegreeSevenWittShiftedClosedForm,
    axeyum_cas::gf2_extension::BinaryExtensionEllThreeDegreeSevenWittShiftedClosedForm,
    "BinaryExtensionEllThreeDegreeSevenWittShiftedClosedForm",
    "Closed form of the `ell = 3`, degree-seven Witt-shifted high-character trace.",
    plain field_degree: usize, "Extension degree `r` in `q = 2 ** r`.";
    plain conductor_two_trace_q_degree: usize, "Leading `q`-degree of the conductor-two trace.";
    plain formal_top_q_degree: usize, "Formal top `q`-degree before cancellation.";
    plain q_degree_drop: usize, "Full `q`-degrees removed in the closed form.";
    big field_order, "Field order `q`.";
    big supported_coarse_mass, "The common nonzero coarse covariance mass.";
    big conductor_one_high_character_trace, "Exact conductor-one high-character trace.";
    big conductor_two_high_character_trace, "Exact conductor-two high-character trace.";
);

trace_report!(
    ExtensionTraceHankelMinor,
    axeyum_cas::gf2_extension::ExtensionTraceHankelMinor,
    "ExtensionTraceHankelMinor",
    "An exact Hankel minor of a bounded extension-trace sequence.",
    plain first_power: usize, "The power the sequence starts at.";
    plain tested_maximum_recurrence_order: usize, "The recurrence order tested.";
    big determinant, "The exact Bareiss determinant.";
);

/// The complete signed low-twist layer sequence over one extension field.
///
/// Tier P: a frozen record of an exact bounded enumeration. Every field of the
/// Rust report is present, including the per-layer traces.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyclass(module = "axeyum._native.cas")
)]
#[pyclass(
    frozen,
    from_py_object,
    module = "axeyum",
    name = "BinaryExtensionWittShiftedTraceReport"
)]
#[derive(Debug, Clone)]
pub struct BinaryExtensionWittShiftedTraceReport {
    inner: axeyum_cas::gf2_extension::BinaryExtensionWittShiftedTraceReport,
}

#[cfg_attr(feature = "stub-gen", pyo3_stub_gen::derive::gen_stub_pymethods)]
#[pymethods]
impl BinaryExtensionWittShiftedTraceReport {
    /// Packed monic irreducible modulus defining the field.
    #[getter]
    fn field_modulus(&self) -> u64 {
        self.inner.field_modulus
    }

    /// Extension degree `r`.
    #[getter]
    fn field_degree(&self) -> usize {
        self.inner.field_degree
    }

    /// Field order `2 ** r`.
    #[getter]
    fn field_order(&self) -> u64 {
        self.inner.field_order
    }

    /// Number of constrained next-to-leading coefficients.
    #[getter]
    fn ell(&self) -> usize {
        self.inner.ell
    }

    /// Degree of every monic polynomial counted.
    #[getter]
    fn polynomial_degree(&self) -> usize {
        self.inner.polynomial_degree
    }

    /// The coarse level the descendants are taken over.
    #[getter]
    fn coarse_level(&self) -> usize {
        self.inner.coarse_level
    }

    /// The number of descendants.
    #[getter]
    fn descendant_count(&self) -> u64 {
        self.inner.descendant_count
    }

    /// The aggregate global mass.
    ///
    /// # Errors
    ///
    /// Propagates any Python error raised while building the `int`.
    #[getter]
    fn aggregate_global_mass<'py>(&self, py: Python<'py>) -> PyResult<Bound<'py, PyAny>> {
        big(py, &self.inner.aggregate_global_mass)
    }

    /// The per-layer traces, in layer order.
    #[getter]
    fn layers(&self) -> Vec<BinaryExtensionWittShiftedLayerTrace> {
        self.inner
            .layers
            .iter()
            .cloned()
            .map(|inner| BinaryExtensionWittShiftedLayerTrace { inner })
            .collect()
    }

    fn __repr__(&self) -> String {
        format!(
            "BinaryExtensionWittShiftedTraceReport(layers={})",
            self.inner.layers.len()
        )
    }
}

/// The exact fixed-degree long-cycle trace over `GF(2 ** r)`.
///
/// Tier P: a bounded exact enumeration behind an explicit budget.
///
/// # Errors
///
/// Raises `Gf2Error` for a reducible field modulus, a malformed interval, a
/// configured degree or population excess, or a failed exact invariant.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.cas")
)]
#[pyfunction]
#[pyo3(signature = (field_modulus, polynomial_degree, fixed_leading_coefficients, limits = None))]
fn binary_extension_long_cycle_trace(
    py: Python<'_>,
    field_modulus: u64,
    polynomial_degree: usize,
    fixed_leading_coefficients: usize,
    limits: Option<BinaryExtensionTraceLimits>,
) -> PyResult<BinaryExtensionLongCycleTraceReport> {
    let limits = limits.map_or_else(CasTraceLimits::default, |limits| limits.inner);
    py.detach(|| {
        axeyum_cas::gf2_extension::binary_extension_long_cycle_trace(
            field_modulus,
            polynomial_degree,
            fixed_leading_coefficients,
            limits,
        )
    })
    .map(|inner| BinaryExtensionLongCycleTraceReport { inner })
    .map_err(|error| trace_error(&error))
}

/// The exact connected endpoint trace over `GF(2 ** r)`.
///
/// Tier P: a bounded exact enumeration behind an explicit budget.
///
/// # Errors
///
/// Raises `Gf2Error` for a non-endpoint degree, an inadmissible field or
/// population, host-size overflow, or a failed Mangoldt conservation identity.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.cas")
)]
#[pyfunction]
#[pyo3(signature = (field_modulus, ell, polynomial_degree, limits = None))]
fn binary_extension_connected_adams_trace(
    py: Python<'_>,
    field_modulus: u64,
    ell: usize,
    polynomial_degree: usize,
    limits: Option<BinaryExtensionTraceLimits>,
) -> PyResult<BinaryExtensionConnectedAdamsTraceReport> {
    let limits = limits.map_or_else(CasTraceLimits::default, |limits| limits.inner);
    py.detach(|| {
        axeyum_cas::gf2_extension::binary_extension_connected_adams_trace(
            field_modulus,
            ell,
            polynomial_degree,
            limits,
        )
    })
    .map(|inner| BinaryExtensionConnectedAdamsTraceReport { inner })
    .map_err(|error| trace_error(&error))
}

/// The complete signed low-twist layer sequence over one extension field.
///
/// Tier P: a bounded exact enumeration behind an explicit budget.
///
/// # Errors
///
/// Raises `Gf2Error` for a non-endpoint degree, a `coarse_level` outside
/// `1..ell`, an inadmissible field or population, or a failed invariant.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.cas")
)]
#[pyfunction]
#[pyo3(signature = (field_modulus, ell, polynomial_degree, coarse_level, limits = None))]
fn binary_extension_witt_shifted_trace(
    py: Python<'_>,
    field_modulus: u64,
    ell: usize,
    polynomial_degree: usize,
    coarse_level: usize,
    limits: Option<BinaryExtensionTraceLimits>,
) -> PyResult<BinaryExtensionWittShiftedTraceReport> {
    let limits = limits.map_or_else(CasTraceLimits::default, |limits| limits.inner);
    py.detach(|| {
        axeyum_cas::gf2_extension::binary_extension_witt_shifted_trace(
            field_modulus,
            ell,
            polynomial_degree,
            coarse_level,
            limits,
        )
    })
    .map(|inner| BinaryExtensionWittShiftedTraceReport { inner })
    .map_err(|error| trace_error(&error))
}

/// Binds a closed-form producer `fn(usize, Limits) -> Result<Report, _>`.
macro_rules! closed_form {
    ($name:ident, $wrapper:ident, $doc:literal) => {
        #[doc = $doc]
        ///
        /// Tier P: an exact closed form under an explicit degree ceiling.
        ///
        /// # Errors
        ///
        /// Raises `Gf2Error` for a zero extension degree or a degree above the
        /// configured bound.
        #[cfg_attr(
            feature = "stub-gen",
            pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.cas")
        )]
        #[pyfunction]
        #[pyo3(signature = (field_degree, limits = None))]
        fn $name(
            py: Python<'_>,
            field_degree: usize,
            limits: Option<BinaryExtensionTraceLimits>,
        ) -> PyResult<$wrapper> {
            let limits = limits.map_or_else(CasTraceLimits::default, |limits| limits.inner);
            py.detach(|| axeyum_cas::gf2_extension::$name(field_degree, limits))
                .map(|inner| $wrapper { inner })
                .map_err(|error| trace_error(&error))
        }
    };
}

closed_form!(
    binary_extension_ell_two_degree_five_closed_form,
    BinaryExtensionEllTwoDegreeFiveClosedForm,
    "The closed form of the `ell = 2`, degree-five connected Adams trace."
);
closed_form!(
    binary_extension_ell_three_degree_seven_closed_form,
    BinaryExtensionEllThreeDegreeSevenClosedForm,
    "The closed form of the `ell = 3`, degree-seven connected Adams trace."
);
closed_form!(
    binary_extension_ell_three_degree_seven_witt_shifted_closed_form,
    BinaryExtensionEllThreeDegreeSevenWittShiftedClosedForm,
    "The closed form of the `ell = 3`, degree-seven Witt-shifted trace."
);

/// The exact Hankel minor of a bounded extension-trace sequence.
///
/// Tier P: an exact Bareiss determinant. A **nonzero** minor refutes a
/// recurrence of order below `tested_maximum_recurrence_order`; it never infers
/// a recurrence from finite data.
///
/// # Errors
///
/// Raises `Gf2Error` for order zero, a power-label overflow, too few traces, or
/// a failed exact Bareiss-division invariant.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.cas")
)]
#[pyfunction]
fn extension_trace_hankel_minor(
    traces: Vec<i128>,
    first_power: usize,
    tested_maximum_recurrence_order: usize,
) -> PyResult<ExtensionTraceHankelMinor> {
    axeyum_cas::gf2_extension::extension_trace_hankel_minor(
        &traces,
        first_power,
        tested_maximum_recurrence_order,
    )
    .map(|inner| ExtensionTraceHankelMinor { inner })
    .map_err(|error| trace_error(&error))
}

/// Registers the finite-field surface on `module`.
///
/// # Errors
///
/// Propagates any Python error raised while setting the module attributes.
pub(crate) fn register(module: &Bound<'_, PyModule>) -> PyResult<()> {
    module.add_class::<SparseSearchLimits>()?;
    module.add_class::<SparseSearchOutcome>()?;
    module.add_class::<BinaryExtensionTraceLimits>()?;
    module.add_class::<BinaryExtensionLongCycleTraceReport>()?;
    module.add_class::<BinaryExtensionConnectedAdamsTraceReport>()?;
    module.add_class::<BinaryExtensionWittShiftedLayerTrace>()?;
    module.add_class::<BinaryExtensionWittShiftedTraceReport>()?;
    module.add_class::<BinaryExtensionEllTwoDegreeFiveClosedForm>()?;
    module.add_class::<BinaryExtensionEllThreeDegreeSevenClosedForm>()?;
    module.add_class::<BinaryExtensionEllThreeDegreeSevenWittShiftedClosedForm>()?;
    module.add_class::<ExtensionTraceHankelMinor>()?;
    macro_rules! add {
        ($($name:ident),* $(,)?) => {
            $(module.add_function(wrap_pyfunction!($name, module)?)?;)*
        };
    }
    add!(
        gfp_add,
        gfp_sub,
        gfp_mul,
        gfp_scale,
        gfp_neg,
        gfp_div_rem,
        gfp_gcd,
        gfp_pow_mod,
        gfp_is_irreducible,
        gfp_factor_berlekamp,
        gfp_roots,
        search_sparse_half_degree,
        binary_extension_long_cycle_trace,
        binary_extension_connected_adams_trace,
        binary_extension_witt_shifted_trace,
        binary_extension_ell_two_degree_five_closed_form,
        binary_extension_ell_three_degree_seven_closed_form,
        binary_extension_ell_three_degree_seven_witt_shifted_closed_form,
        extension_trace_hankel_minor,
    );
    Ok(())
}
