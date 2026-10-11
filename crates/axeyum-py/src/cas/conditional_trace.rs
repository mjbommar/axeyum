//! Python transport for nested conditional cancellation certificates.
use super::expr::Expr;
use axeyum_cas::CasExpr;
use axeyum_cas::conditional_trace::{
    ConditionalTrace, cancel_nested_with_trace, replay_conditional_json,
};
use axeyum_cas::rewrite_trace::{PolynomialExpr, TraceError, TraceLimits};
use pyo3::{prelude::*, types::PyModule};

fn encode(expr: &CasExpr, limits: TraceLimits) -> Result<PolynomialExpr, TraceError> {
    fn walk(
        expr: &CasExpr,
        depth: usize,
        nodes: &mut usize,
        limits: TraceLimits,
    ) -> Result<PolynomialExpr, TraceError> {
        *nodes += 1;
        if depth > limits.depth || *nodes > limits.nodes {
            return Err(TraceError::ResourceLimit(
                "conditional Python expression shape".into(),
            ));
        }
        let mut child = |x: &CasExpr| walk(x, depth + 1, nodes, limits);
        Ok(match expr {
            CasExpr::Const(_) | CasExpr::Var(_) => PolynomialExpr::from_cas_wide(expr, limits)?,
            CasExpr::Add(xs) => {
                PolynomialExpr::Add(xs.iter().map(child).collect::<Result<_, _>>()?)
            }
            CasExpr::Mul(xs) => {
                PolynomialExpr::Mul(xs.iter().map(child).collect::<Result<_, _>>()?)
            }
            CasExpr::Neg(x) => PolynomialExpr::Neg(Box::new(child(x)?)),
            CasExpr::Pow(x, exponent) => PolynomialExpr::Pow {
                base: Box::new(child(x)?),
                exponent: *exponent,
            },
            CasExpr::Div(n, d) => PolynomialExpr::Div {
                numerator: Box::new(child(n)?),
                denominator: Box::new(child(d)?),
            },
            _ => {
                return Err(TraceError::Unsupported(
                    "nonrational conditional expression".into(),
                ));
            }
        })
    }
    walk(expr, 0, &mut 0, limits)
}
fn decode(expr: &PolynomialExpr) -> Result<CasExpr, TraceError> {
    Ok(match expr {
        PolynomialExpr::Const { .. } | PolynomialExpr::Var(_) => {
            expr.to_cas_wide(TraceLimits::default())?
        }
        PolynomialExpr::Add(xs) => CasExpr::Add(xs.iter().map(decode).collect::<Result<_, _>>()?),
        PolynomialExpr::Mul(xs) => CasExpr::Mul(xs.iter().map(decode).collect::<Result<_, _>>()?),
        PolynomialExpr::Neg(x) => CasExpr::Neg(Box::new(decode(x)?)),
        PolynomialExpr::Pow { base, exponent } => CasExpr::Pow(Box::new(decode(base)?), *exponent),
        PolynomialExpr::Div {
            numerator,
            denominator,
        } => CasExpr::Div(Box::new(decode(numerator)?), Box::new(decode(denominator)?)),
    })
}
/// Production/replay result for a complete source-bound conditional trace.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyclass(module = "axeyum._native.cas")
)]
#[pyclass(
    frozen,
    from_py_object,
    module = "axeyum",
    name = "ConditionalTraceOutcome"
)]
#[derive(Debug, Clone)]
pub struct ConditionalTraceOutcome {
    /// produced, checked, rejected, unsupported, or resource_limited.
    #[pyo3(get)]
    status: String,
    /// Complete serialized evidence, absent on refusal.
    #[pyo3(get)]
    json: Option<String>,
    /// Typed final expression, absent on refusal.
    #[pyo3(get)]
    result: Option<Expr>,
    /// Actual conditional steps; zero on refusal.
    #[pyo3(get)]
    step_count: usize,
    /// Failing step when the checker identifies one.
    #[pyo3(get)]
    failing_step: Option<usize>,
    /// Concrete refusal reason.
    #[pyo3(get)]
    detail: String,
}
impl ConditionalTraceOutcome {
    fn failure(error: TraceError) -> Self {
        let (status, failing_step, detail) = match error {
            TraceError::Rejected { step, reason } => ("rejected", step, reason),
            TraceError::Unsupported(reason) => ("unsupported", None, reason),
            TraceError::ResourceLimit(reason) => ("resource_limited", None, reason),
        };
        Self {
            status: status.into(),
            json: None,
            result: None,
            step_count: 0,
            failing_step,
            detail,
        }
    }
    fn success(status: &str, trace: ConditionalTrace) -> Self {
        let result = match decode(&trace.result) {
            Ok(expr) => Expr::wrap(expr),
            Err(error) => return Self::failure(error),
        };
        match serde_json::to_string(&trace) {
            Ok(json) => Self {
                status: status.into(),
                json: Some(json),
                result: Some(result),
                step_count: trace.steps.len(),
                failing_step: None,
                detail: String::new(),
            },
            Err(_) => Self::failure(TraceError::Rejected {
                step: None,
                reason: "conditional JSON serialization".into(),
            }),
        }
    }
}
fn context(nonzero: &[Expr], limits: TraceLimits) -> Result<Vec<PolynomialExpr>, TraceError> {
    if nonzero.len() > limits.nodes {
        return Err(TraceError::ResourceLimit(
            "conditional assumption count".into(),
        ));
    }
    nonzero
        .iter()
        .map(|expr| PolynomialExpr::from_cas_wide(expr.inner(), limits))
        .collect()
}
/// Cancel nested quotient factors under explicit nonzero assumptions.
/// Certificates preserve partial definedness; they do not admit kernel theorems.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.cas")
)]
#[pyfunction]
#[pyo3(signature=(input, *, nonzero, max_steps=128, max_work=1_000_000))]
fn cancel_nested_trace(
    py: Python<'_>,
    input: Expr,
    nonzero: Vec<Expr>,
    max_steps: usize,
    max_work: u64,
) -> ConditionalTraceOutcome {
    py.detach(move || {
        let limits = TraceLimits {
            steps: max_steps,
            work: max_work,
            ..TraceLimits::default()
        };
        let produced = (|| {
            cancel_nested_with_trace(
                &encode(input.inner(), limits)?,
                &context(&nonzero, limits)?,
                limits,
            )
        })();
        match produced {
            Ok(trace) => ConditionalTraceOutcome::success("produced", trace),
            Err(error) => ConditionalTraceOutcome::failure(error),
        }
    })
}
/// Check saved conditional bytes against original subject, endpoint and context.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.cas")
)]
#[pyfunction]
#[pyo3(signature=(json, input, result, *, nonzero, max_steps=128, max_work=1_000_000))]
#[allow(clippy::too_many_arguments)]
fn replay_conditional_trace(
    py: Python<'_>,
    json: &str,
    input: Expr,
    result: Expr,
    nonzero: Vec<Expr>,
    max_steps: usize,
    max_work: u64,
) -> ConditionalTraceOutcome {
    py.detach(move || {
        let limits = TraceLimits {
            steps: max_steps,
            work: max_work,
            ..TraceLimits::default()
        };
        let checked = (|| {
            replay_conditional_json(
                json.as_bytes(),
                &encode(input.inner(), limits)?,
                &encode(result.inner(), limits)?,
                &context(&nonzero, limits)?,
                limits,
            )
        })();
        match checked {
            Ok(trace) => ConditionalTraceOutcome::success("checked", trace),
            Err(error) => ConditionalTraceOutcome::failure(error),
        }
    })
}
pub(crate) fn register(module: &Bound<'_, PyModule>) -> PyResult<()> {
    module.add_class::<ConditionalTraceOutcome>()?;
    module.add_function(wrap_pyfunction!(cancel_nested_trace, module)?)?;
    module.add_function(wrap_pyfunction!(replay_conditional_trace, module)?)?;
    Ok(())
}
