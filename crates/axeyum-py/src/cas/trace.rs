//! Structured production/replay outcomes for source-bound CAS step traces.
use super::expr::Expr;
use axeyum_cas::rewrite_trace::{
    PolynomialExpr, RewriteTrace as CasTrace, TraceError, TraceLimits, check_trace,
    normalize_with_trace, replay_json,
};
use pyo3::{exceptions::PyValueError, prelude::*, types::PyModule};

fn limits(max_steps: usize, max_work: u64) -> TraceLimits {
    TraceLimits {
        steps: max_steps,
        work: max_work,
        ..TraceLimits::default()
    }
}

/// A full polynomial equality log; kernel admission remains separate.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyclass(module = "axeyum._native.cas")
)]
#[pyclass(frozen, from_py_object, module = "axeyum", name = "RewriteTrace")]
#[derive(Debug, Clone)]
pub struct RewriteTrace {
    inner: CasTrace,
}

#[cfg_attr(feature = "stub-gen", pyo3_stub_gen::derive::gen_stub_pymethods)]
#[pymethods]
impl RewriteTrace {
    /// Original typed expression.
    #[getter]
    fn input(&self) -> PyResult<Expr> {
        self.inner
            .input
            .to_cas(TraceLimits::default())
            .map(Expr::wrap)
            .map_err(|e| PyValueError::new_err(format!("{e:?}")))
    }
    /// Claimed final typed expression.
    #[getter]
    fn result(&self) -> PyResult<Expr> {
        self.inner
            .result
            .to_cas(TraceLimits::default())
            .map(Expr::wrap)
            .map_err(|e| PyValueError::new_err(format!("{e:?}")))
    }
    /// Number of actual local rewrites, including their certificates.
    #[getter]
    fn step_count(&self) -> usize {
        self.inner.steps.len()
    }
    /// Deterministic complete evidence JSON, suitable for a separate process.
    fn to_json(&self) -> PyResult<String> {
        self.inner
            .to_json(TraceLimits::default())
            .map_err(|e| PyValueError::new_err(format!("{e:?}")))
    }
    /// Check this log against separately supplied original/final expressions.
    #[pyo3(signature = (input, result, *, max_steps = 128, max_work = 1_000_000))]
    fn replay(&self, input: Expr, result: Expr, max_steps: usize, max_work: u64) -> TraceOutcome {
        let policy = limits(max_steps, max_work);
        let checked = (|| {
            let input = PolynomialExpr::from_cas(input.inner(), policy)?;
            let result = PolynomialExpr::from_cas(result.inner(), policy)?;
            check_trace(&self.inner, &input, &result, policy)
        })();
        match checked {
            Ok(()) => TraceOutcome::success("checked", self.inner.clone()),
            Err(error) => TraceOutcome::failure(error),
        }
    }
}

/// Production/checking status; refusal never becomes a success-shaped value.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyclass(module = "axeyum._native.cas")
)]
#[pyclass(frozen, from_py_object, module = "axeyum", name = "TraceOutcome")]
#[derive(Debug, Clone)]
pub struct TraceOutcome {
    /// produced, checked, rejected, unsupported, or `resource_limited`.
    #[pyo3(get)]
    status: String,
    /// Completed evidence only on successful production or replay.
    #[pyo3(get)]
    trace: Option<RewriteTrace>,
    /// Failing step index when the checker identifies a local obligation.
    #[pyo3(get)]
    failing_step: Option<usize>,
    /// Concrete decline/rejection reason; empty on success.
    #[pyo3(get)]
    detail: String,
}
impl TraceOutcome {
    fn success(status: &str, trace: CasTrace) -> Self {
        Self {
            status: status.to_owned(),
            trace: Some(RewriteTrace { inner: trace }),
            failing_step: None,
            detail: String::new(),
        }
    }
    fn failure(error: TraceError) -> Self {
        let (status, failing_step, detail) = match error {
            TraceError::Rejected { step, reason } => ("rejected", step, reason),
            TraceError::Unsupported(reason) => ("unsupported", None, reason),
            TraceError::ResourceLimit(reason) => ("resource_limited", None, reason),
        };
        Self {
            status: status.to_owned(),
            trace: None,
            failing_step,
            detail,
        }
    }
}

/// Produce an opt-in polynomial step trace with explicit refusal status.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.cas")
)]
#[pyfunction]
#[pyo3(signature = (expr, *, max_steps = 128, max_work = 1_000_000))]
pub(crate) fn normalize_trace(
    py: Python<'_>,
    expr: Expr,
    max_steps: usize,
    max_work: u64,
) -> TraceOutcome {
    py.detach(
        move || match normalize_with_trace(expr.inner(), limits(max_steps, max_work)) {
            Ok(trace) => TraceOutcome::success("produced", trace),
            Err(error) => TraceOutcome::failure(error),
        },
    )
}

/// Replay exported JSON against an explicit expected equality statement.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.cas")
)]
#[pyfunction]
#[pyo3(signature = (json, input, result, *, max_steps = 128, max_work = 1_000_000))]
pub(crate) fn replay_trace(
    py: Python<'_>,
    json: &str,
    input: Expr,
    result: Expr,
    max_steps: usize,
    max_work: u64,
) -> TraceOutcome {
    py.detach(move || {
        let policy = limits(max_steps, max_work);
        let checked = (|| {
            let input = PolynomialExpr::from_cas(input.inner(), policy)?;
            let result = PolynomialExpr::from_cas(result.inner(), policy)?;
            replay_json(json.as_bytes(), &input, &result, policy)
        })();
        match checked {
            Ok(trace) => TraceOutcome::success("checked", trace),
            Err(error) => TraceOutcome::failure(error),
        }
    })
}

/// Conditional quotient equality and explicit nonzero assumptions.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyclass(module = "axeyum._native.cas")
)]
#[pyclass(
    frozen,
    from_py_object,
    module = "axeyum",
    name = "GuardedRewriteTrace"
)]
#[derive(Debug, Clone)]
pub struct GuardedRewriteTrace {
    inner: axeyum_cas::guarded_trace::GuardedQuotientTrace,
}
#[cfg_attr(feature = "stub-gen", pyo3_stub_gen::derive::gen_stub_pymethods)]
#[pymethods]
impl GuardedRewriteTrace {
    /// Claimed polynomial quotient; its validity depends on the carried context.
    #[getter]
    fn result(&self) -> PyResult<Expr> {
        self.inner
            .result
            .to_cas(TraceLimits::default())
            .map(Expr::wrap)
            .map_err(|e| PyValueError::new_err(format!("{e:?}")))
    }
    /// Each expression is assumed nonzero, never inferred nonzero by the producer.
    #[getter]
    fn nonzero_assumptions(&self) -> PyResult<Vec<Expr>> {
        self.inner
            .nonzero_assumptions
            .iter()
            .map(|expr| {
                expr.to_cas(TraceLimits::default())
                    .map(Expr::wrap)
                    .map_err(|e| PyValueError::new_err(format!("{e:?}")))
            })
            .collect()
    }
    /// One cancellation step plus the actual local polynomial witness steps.
    #[getter]
    fn step_count(&self) -> usize {
        1 + self.inner.numerator_identity.steps.len() + self.inner.product_identity.steps.len()
    }
    /// Deterministic evidence; byte replay must bind an external subject and context.
    fn to_json(&self) -> PyResult<String> {
        self.inner
            .to_json(TraceLimits::default())
            .map_err(|e| PyValueError::new_err(format!("{e:?}")))
    }
}
/// Conditional production/replay outcome; failures carry no completed trace.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyclass(module = "axeyum._native.cas")
)]
#[pyclass(
    frozen,
    from_py_object,
    module = "axeyum",
    name = "GuardedTraceOutcome"
)]
#[derive(Debug, Clone)]
pub struct GuardedTraceOutcome {
    /// produced, checked, rejected, unsupported or `resource_limited`.
    #[pyo3(get)]
    status: String,
    /// Evidence only after complete successful production or checking.
    #[pyo3(get)]
    trace: Option<GuardedRewriteTrace>,
    /// Local step identified on rejection, otherwise None.
    #[pyo3(get)]
    failing_step: Option<usize>,
    /// Explicit failure/decline reason, empty on success.
    #[pyo3(get)]
    detail: String,
}
impl GuardedTraceOutcome {
    fn success(status: &str, inner: axeyum_cas::guarded_trace::GuardedQuotientTrace) -> Self {
        Self {
            status: status.into(),
            trace: Some(GuardedRewriteTrace { inner }),
            failing_step: None,
            detail: String::new(),
        }
    }
    fn failure(error: TraceError) -> Self {
        let outcome = TraceOutcome::failure(error);
        Self {
            status: outcome.status,
            trace: None,
            failing_step: outcome.failing_step,
            detail: outcome.detail,
        }
    }
}
fn guarded_subject(
    numerator: &Expr,
    denominator: &Expr,
    nonzero: &[Expr],
    policy: TraceLimits,
) -> Result<
    (
        axeyum_cas::guarded_trace::QuotientSubject,
        Vec<PolynomialExpr>,
    ),
    TraceError,
> {
    if nonzero.len() > policy.nodes {
        return Err(TraceError::ResourceLimit("assumption count".into()));
    }
    Ok((
        axeyum_cas::guarded_trace::QuotientSubject {
            numerator: PolynomialExpr::from_cas(numerator.inner(), policy)?,
            denominator: PolynomialExpr::from_cas(denominator.inner(), policy)?,
        },
        nonzero
            .iter()
            .map(|expr| PolynomialExpr::from_cas(expr.inner(), policy))
            .collect::<Result<_, _>>()?,
    ))
}
/// Cancel a denominator factor under caller-supplied nonzero assumptions.
/// Missing assumptions explicitly reject; this never produces an unconditional identity.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.cas")
)]
#[pyfunction]
#[pyo3(signature = (numerator, denominator, *, nonzero, max_steps = 128, max_work = 1_000_000))]
pub(crate) fn cancel_trace(
    py: Python<'_>,
    numerator: Expr,
    denominator: Expr,
    nonzero: Vec<Expr>,
    max_steps: usize,
    max_work: u64,
) -> GuardedTraceOutcome {
    py.detach(move || {
        let policy = limits(max_steps, max_work);
        let produced = (|| {
            let (subject, context) = guarded_subject(&numerator, &denominator, &nonzero, policy)?;
            axeyum_cas::guarded_trace::cancel_factor_with_trace(&subject, &context, policy)
        })();
        match produced {
            Ok(trace) => GuardedTraceOutcome::success("produced", trace),
            Err(error) => GuardedTraceOutcome::failure(error),
        }
    })
}
/// Replay guarded bytes against the exact original quotient, result and context.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.cas")
)]
#[pyfunction]
#[pyo3(signature = (json, numerator, denominator, result, *, nonzero, max_steps = 128, max_work = 1_000_000))]
#[allow(clippy::too_many_arguments)]
pub(crate) fn replay_guarded_trace(
    py: Python<'_>,
    json: &str,
    numerator: Expr,
    denominator: Expr,
    result: Expr,
    nonzero: Vec<Expr>,
    max_steps: usize,
    max_work: u64,
) -> GuardedTraceOutcome {
    py.detach(move || {
        let policy = limits(max_steps, max_work);
        let checked = (|| {
            let (subject, context) = guarded_subject(&numerator, &denominator, &nonzero, policy)?;
            let result = PolynomialExpr::from_cas(result.inner(), policy)?;
            axeyum_cas::guarded_trace::replay_guarded_json(
                json.as_bytes(),
                &subject,
                &result,
                &context,
                policy,
            )
        })();
        match checked {
            Ok(trace) => GuardedTraceOutcome::success("checked", trace),
            Err(error) => GuardedTraceOutcome::failure(error),
        }
    })
}

pub(crate) fn register(module: &Bound<'_, PyModule>) -> PyResult<()> {
    module.add_class::<RewriteTrace>()?;
    module.add_class::<GuardedRewriteTrace>()?;
    module.add_class::<GuardedTraceOutcome>()?;
    module.add_function(wrap_pyfunction!(cancel_trace, module)?)?;
    module.add_function(wrap_pyfunction!(replay_guarded_trace, module)?)?;
    module.add_class::<TraceOutcome>()?;
    module.add_function(wrap_pyfunction!(normalize_trace, module)?)?;
    module.add_function(wrap_pyfunction!(replay_trace, module)?)?;
    Ok(())
}
