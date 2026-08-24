//! `axeyum.smt` — decide an SMT-LIB script, and replay the model yourself.
//!
//! One function, [`solve`], over the Rust text front door
//! [`axeyum_solver::smtlib::solve_smtlib`] (ADR-0052). The Python surface adds
//! nothing the Rust API lacks: no logic selection the Rust call cannot make, no
//! access to the declared `:status` on the solving path, and no way to turn an
//! `unknown` into anything other than an `unknown`.

use std::time::Duration;

use axeyum_ir::{Sort, SymbolId, TermArena, TermId, Value};
use axeyum_smtlib::{Script, ScriptCommand, decode_packed_string, parse_script};
use axeyum_solver::smtlib::solve_smtlib;
use axeyum_solver::{CheckResult, Model, SolverConfig, SolverError, check_model};
use pyo3::prelude::*;
use pyo3::types::{PyDict, PyModule};

use crate::convert::model_dict;
use crate::error::{AxeyumError, SmtLibParseError};

/// Everything needed to re-check a `sat` model without solving again.
///
/// Kept inside the [`Outcome`] so `replay()` is self-contained: the canonical
/// check ([`axeyum_solver::check_model`]) evaluates the ORIGINAL assertions, so
/// it needs the arena those terms live in.
struct ReplayState {
    arena: TermArena,
    assertions: Vec<TermId>,
    model: Model,
}

/// The result of deciding one SMT-LIB script.
///
/// `status` is `"sat"`, `"unsat"` or `"unknown"`. **`unknown` is a value**, not
/// an exception (CLAUDE.md hard rule): a budget-exhausted or incomplete run
/// returns an `Outcome` whose `detail` says why.
#[pyclass(frozen, module = "axeyum", name = "Outcome")]
pub struct Outcome {
    status: &'static str,
    logic: Option<String>,
    expected_status: Option<String>,
    detail: String,
    model: Py<PyDict>,
    replay: Option<ReplayState>,
}

#[pymethods]
impl Outcome {
    /// `"sat"`, `"unsat"`, or `"unknown"`.
    #[getter]
    fn status(&self) -> &'static str {
        self.status
    }

    /// The script's `(set-logic ...)`, when it declared one.
    #[getter]
    fn logic(&self) -> Option<&str> {
        self.logic.as_deref()
    }

    /// The script's own `(set-info :status ...)`, echoed for cross-checking.
    ///
    /// This is ground truth *about* the benchmark and is never consulted while
    /// solving; the binding cannot pass it to the solver because
    /// `solve_smtlib` does not take it.
    #[getter]
    fn expected_status(&self) -> Option<&str> {
        self.expected_status.as_deref()
    }

    /// The classified `unknown` reason, rendered; empty for a decided query.
    #[getter]
    fn detail(&self) -> &str {
        &self.detail
    }

    /// The satisfying assignment, `{declared name: value}`, in declaration
    /// order. Empty unless `status == "sat"`.
    ///
    /// # Errors
    ///
    /// Propagates any Python error raised while copying the dictionary.
    #[getter]
    fn model<'py>(&self, py: Python<'py>) -> PyResult<Bound<'py, PyDict>> {
        self.model.bind(py).copy()
    }

    /// Re-checks the model against the original assertions, in Rust.
    ///
    /// This is [`axeyum_solver::check_model`] — the canonical replay, the same
    /// one the solver applies to itself. `True` means the returned model
    /// genuinely satisfies the script's active assertions.
    ///
    /// `False` is **not** a claim that the model is wrong: it is also what an
    /// `unsat`/`unknown` outcome returns, and what a `sat` returns when no
    /// replay state could be built. That last case is real — the front door
    /// reaches routes that `axeyum_solver::solve` alone does not, so the
    /// re-derivation this object carries can come back undecided on a query the
    /// front door decided. Measured 2026-08-24 over the 45 committed
    /// `corpus/regression` files: 16 `sat` verdicts, of which **1** (a
    /// quantified `LIA` negation, `uflia_induction/unguarded_int_nonneg.smt2`)
    /// had no replay state.
    /// TODO(plan 02): distinguish "replayed and disagreed" from "no replay
    /// available" — they are the same `False` today, and only the first is a
    /// soundness signal.
    ///
    /// # Errors
    ///
    /// Raises `AxeyumError` if the evaluator fails on a term it cannot
    /// interpret; a model that simply does not satisfy the assertions is
    /// `False`, not an error.
    fn replay(&self, py: Python<'_>) -> PyResult<bool> {
        let Some(state) = self.replay.as_ref() else {
            return Ok(false);
        };
        py.detach(|| check_model(&state.arena, &state.assertions, &state.model))
            .map_err(map_solver_error)
    }

    fn __repr__(&self) -> String {
        format!(
            "Outcome(status={:?}, logic={}, expected_status={})",
            self.status,
            optional_repr(self.logic.as_deref()),
            optional_repr(self.expected_status.as_deref()),
        )
    }
}

/// `repr()` of an optional string, the way Python spells it.
fn optional_repr(value: Option<&str>) -> String {
    value.map_or_else(|| "None".to_owned(), |text| format!("{text:?}"))
}

/// Decides an SMT-LIB 2 script.
///
/// `timeout_ms` is the wall-clock budget handed to the solver. Exhausting it
/// yields `status == "unknown"`, never an exception.
///
/// # Errors
///
/// Raises `SmtLibParseError` when the text is malformed or uses a construct
/// outside the supported fragment, and `AxeyumError` for any other solver
/// failure.
#[pyfunction]
#[pyo3(signature = (script, *, timeout_ms = 10_000))]
fn solve(py: Python<'_>, script: &str, timeout_ms: u64) -> PyResult<Outcome> {
    let config = SolverConfig::new().with_timeout(Duration::from_millis(timeout_ms));
    let outcome = py
        .detach(|| solve_smtlib(script, &config))
        .map_err(map_solver_error)?;

    let (status, detail) = match &outcome.result {
        CheckResult::Sat(_) => ("sat", String::new()),
        CheckResult::Unsat => ("unsat", String::new()),
        CheckResult::Unknown(reason) => ("unknown", format!("{reason:?}")),
    };

    // The front door returns a verdict, not an arena — and the canonical replay
    // needs the arena the original terms live in. So on `sat` we re-derive the
    // model through the same public `solve` the front door dispatches to,
    // keeping the parsed script alive inside the `Outcome`.
    // TODO(plan 02): this costs a second solve on `sat`. Removing it needs a
    // Rust entry point that returns the arena, the active assertions and the
    // model together; `solve_smtlib_model` does not (it re-parses and re-solves
    // too, and returns names without the arena).
    let (replay, named) = if status == "sat" {
        match py.detach(|| build_replay_state(script, &config)) {
            Some((state, named)) => (Some(state), named),
            None => (None, Vec::new()),
        }
    } else {
        (None, Vec::new())
    };

    Ok(Outcome {
        status,
        logic: outcome.logic,
        expected_status: outcome.expected_status,
        detail,
        model: model_dict(py, &named)?.unbind(),
        replay,
    })
}

/// Re-solves `input` through [`axeyum_solver::solve`] to recover the arena, the
/// active assertion stack, and the model.
///
/// Returns `None` when the script is not a single-query script, fails to parse,
/// or does not come back `sat` on this route — all of which leave the caller
/// with an empty model and a `replay()` of `False` rather than a wrong answer.
fn build_replay_state(
    input: &str,
    config: &SolverConfig,
) -> Option<(ReplayState, Vec<(String, Value)>)> {
    let mut script = parse_script(input).ok()?;
    if script.check_sats > 1 {
        return None;
    }
    let assertions = active_assertions(&script);
    let result = axeyum_solver::solve(&mut script.arena, &assertions, config).ok()?;
    let CheckResult::Sat(model) = result else {
        return None;
    };
    let named = named_constants(&script, &model);
    let arena = std::mem::take(&mut script.arena);
    Some((
        ReplayState {
            arena,
            assertions,
            model,
        },
        named,
    ))
}

/// The assertion stack active at the script's `check-sat`, honoring
/// `push`/`pop`, `check-sat-assuming` and `reset-assertions`.
///
/// This mirrors the solver's own private `smtlib_single_query`. A script with no
/// `check-sat` decides its whole flat stack, matching the front door.
fn active_assertions(script: &Script) -> Vec<TermId> {
    let mut stack: Vec<TermId> = Vec::new();
    let mut scopes: Vec<usize> = Vec::new();
    let mut queried: Option<Vec<TermId>> = None;
    for command in &script.commands {
        match command {
            ScriptCommand::Assert(term) => stack.push(*term),
            ScriptCommand::Push(n) => {
                for _ in 0..*n {
                    scopes.push(stack.len());
                }
            }
            ScriptCommand::Pop(n) => {
                for _ in 0..*n {
                    if let Some(depth) = scopes.pop() {
                        stack.truncate(depth);
                    }
                }
            }
            ScriptCommand::CheckSat => queried = Some(stack.clone()),
            ScriptCommand::CheckSatAssuming(assumptions) => {
                let mut with_assumptions = stack.clone();
                with_assumptions.extend(assumptions.iter().copied());
                queried = Some(with_assumptions);
            }
            ScriptCommand::ResetAssertions => {
                stack.clear();
                scopes.clear();
            }
            // Output/metadata commands do not move the assertion stack.
            _ => {}
        }
    }
    queried.unwrap_or(stack)
}

/// The user-declared constants of `script` with their model values, in
/// declaration order.
///
/// Symbols the model leaves unconstrained are omitted rather than defaulted:
/// the completion the Rust `(get-model)` path performs lives in a private
/// helper, and inventing a value here would be a claim the solver did not make.
fn named_constants(script: &Script, model: &Model) -> Vec<(String, Value)> {
    script
        .model_symbols
        .iter()
        .filter_map(|&symbol| {
            let value = model.get(symbol)?;
            let (name, _sort) = script.arena.symbol(symbol);
            Some((
                name.to_owned(),
                render_declared_string(script, symbol, value),
            ))
        })
        .collect()
}

/// Renders a declared `String`'s packed bit-vector value as a sequence value.
///
/// ADR-0029 gives a declared `String` the IR sort `(_ BitVec string_total(m))`,
/// so without this a `String` variable comes back as a bit-vector. Keyed on
/// `Script::declared_strings`, never on the width: decoding a genuine
/// `(_ BitVec 100)` would be a WRONG model rather than merely an unreadable one.
/// A packing the decoder rejects is left as the raw bit-vector for the same
/// reason.
fn render_declared_string(script: &Script, symbol: SymbolId, value: Value) -> Value {
    let Value::Bv { width, value: bits } = value else {
        return value;
    };
    if !script.declared_strings.iter().any(|&(s, _)| s == symbol) {
        return Value::Bv { width, value: bits };
    }
    match decode_packed_string(width, bits) {
        Some(bytes) => Value::Seq(
            bytes
                .iter()
                .map(|&b| Value::Bv {
                    width: Sort::STRING_ELEM_WIDTH,
                    value: u128::from(b),
                })
                .collect(),
        ),
        None => Value::Bv { width, value: bits },
    }
}

/// Maps a Rust solver error onto the Python exception hierarchy.
fn map_solver_error(error: SolverError) -> PyErr {
    match error {
        SolverError::Parse(what) => SmtLibParseError::new_err(what),
        other => AxeyumError::new_err(other.to_string()),
    }
}

/// Builds the `smt` submodule.
///
/// # Errors
///
/// Propagates any Python error raised while creating or populating the module.
pub(crate) fn register<'py>(parent: &Bound<'py, PyModule>) -> PyResult<Bound<'py, PyModule>> {
    let py = parent.py();
    // The FULL dotted name, so `repr(axeyum.smt)` and every traceback name the
    // module the way an import statement spells it. The parent attribute is set
    // explicitly for the same reason -- `add_submodule` would use the full name
    // as the attribute name.
    let module = PyModule::new(py, "axeyum._native.smt")?;
    module.add_class::<Outcome>()?;
    module.add_function(wrap_pyfunction!(solve, &module)?)?;
    parent.add("smt", &module)?;
    Ok(module)
}
