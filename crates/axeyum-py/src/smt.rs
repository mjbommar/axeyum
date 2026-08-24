//! `axeyum.smt` — decide an SMT-LIB script, and replay the model yourself.
//!
//! One function, [`solve`], over the Rust text front door
//! [`axeyum_solver::smtlib::solve_smtlib`] (ADR-0052). The Python surface adds
//! nothing the Rust API lacks: no logic selection the Rust call cannot make, no
//! access to the declared `:status` on the solving path, and no way to turn an
//! `unknown` into anything other than an `unknown`.
#![allow(
    // PyO3's calling convention hands `PyRef` guards and owned `Vec` arguments
    // in by value; there is no by-reference form.
    clippy::needless_pass_by_value,
    clippy::trivially_copy_pass_by_ref
)]

use std::time::Duration;

use std::sync::atomic::{AtomicU64, Ordering};

use axeyum_ir::{Sort, SymbolId, TermArena, TermId, Value};
use axeyum_smtlib::{
    Script, ScriptCommand, SmtError, decode_packed_string, parse_script, parse_script_within,
};
use axeyum_solver::smtlib::{
    solve_smtlib, solve_smtlib_get_assignment, solve_smtlib_get_proof, solve_smtlib_get_value,
    solve_smtlib_incremental, solve_smtlib_unsat_core,
};
use axeyum_solver::{
    BitLoweringMode, CheckResult, Model, SmtLibResponse, SolverConfig, SolverError, check_model,
    solve_smtlib_session,
};
use pyo3::prelude::*;
use pyo3::types::{PyDict, PyList, PyModule};

use crate::convert::{model_dict, value_to_py};
use crate::error::{AxeyumError, BudgetExceeded, SmtLibParseError};
use crate::ir::types::check_epoch;

/// Script epochs come from a range disjoint from `Arena`'s, so a `Term` and a
/// `ScriptTerm` can never be silently interchanged even by hand-built handles.
static NEXT_SCRIPT_EPOCH: AtomicU64 = AtomicU64::new(1 << 32);

/// Hands out the next script epoch.
fn next_script_epoch() -> u64 {
    NEXT_SCRIPT_EPOCH.fetch_add(1, Ordering::Relaxed)
}

/// A term inside a parsed [`Script`](axeyum.smt.Script).
///
/// Distinct from [`ir.Term`](axeyum.ir.Term) on purpose: a script owns its own
/// arena, so its terms are not usable against an `ir.Arena` and vice versa.
#[pyclass(frozen, from_py_object, module = "axeyum", name = "ScriptTerm")]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ScriptTerm {
    epoch: u64,
    id: TermId,
}

impl ScriptTerm {
    fn new(epoch: u64, id: TermId) -> Self {
        Self { epoch, id }
    }

    fn resolve(self, epoch: u64) -> PyResult<TermId> {
        check_epoch(epoch, self.epoch, "ScriptTerm")?;
        Ok(self.id)
    }
}

#[pymethods]
impl ScriptTerm {
    /// The epoch of the script that minted this handle.
    #[getter]
    fn epoch(&self) -> u64 {
        self.epoch
    }

    /// The dense index inside the owning script's arena.
    #[getter]
    fn raw(&self) -> u32 {
        u32::try_from(self.id.index()).unwrap_or(u32::MAX)
    }

    fn __repr__(&self) -> String {
        format!("ScriptTerm(epoch={}, raw={})", self.epoch, self.id.index())
    }

    fn __eq__(&self, other: &Bound<'_, PyAny>) -> bool {
        other
            .cast::<Self>()
            .is_ok_and(|other| *self == *other.get())
    }

    fn __hash__(&self) -> u64 {
        (self.epoch << 16) ^ (self.id.index() as u64)
    }
}

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
/// Every budget is a **value contract**: exhausting one yields
/// `status == "unknown"` with a `detail`, never an exception. The two `mpsc`
/// progress sinks of the Rust `SolverConfig` are not bound.
///
/// # Errors
///
/// Raises `SmtLibParseError` when the text is malformed or uses a construct
/// outside the supported fragment, and `AxeyumError` for any other solver
/// failure.
#[pyfunction]
#[pyo3(signature = (
    script,
    *,
    timeout_ms = 10_000,
    resource_limit = None,
    memory_limit_mb = None,
    node_budget = None,
    cnf_variable_budget = None,
    cnf_clause_budget = None,
    prove_unsat = false,
    preprocess = true,
))]
#[allow(clippy::fn_params_excessive_bools, clippy::too_many_arguments)]
fn solve(
    py: Python<'_>,
    script: &str,
    timeout_ms: u64,
    resource_limit: Option<u64>,
    memory_limit_mb: Option<u64>,
    node_budget: Option<u64>,
    cnf_variable_budget: Option<u64>,
    cnf_clause_budget: Option<u64>,
    prove_unsat: bool,
    preprocess: bool,
) -> PyResult<Outcome> {
    let config = script_config(
        timeout_ms,
        resource_limit,
        memory_limit_mb,
        node_budget,
        cnf_variable_budget,
        cnf_clause_budget,
        prove_unsat,
        preprocess,
    );
    let outcome = py
        .detach(|| solve_smtlib(script, &config))
        .map_err(map_solver_error)?;

    let (status, detail) = match &outcome.result {
        CheckResult::Sat(_) => ("sat", String::new()),
        CheckResult::Unsat => ("unsat", String::new()),
        CheckResult::Unknown(reason) => ("unknown", format!("{reason:?}")),
    };

    // The front door returns a verdict, not an arena -- and the canonical replay
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

/// Builds the front-door configuration from the shared keyword set.
#[allow(clippy::fn_params_excessive_bools, clippy::too_many_arguments)]
fn script_config(
    timeout_ms: u64,
    resource_limit: Option<u64>,
    memory_limit_mb: Option<u64>,
    node_budget: Option<u64>,
    cnf_variable_budget: Option<u64>,
    cnf_clause_budget: Option<u64>,
    prove_unsat: bool,
    preprocess: bool,
) -> SolverConfig {
    let mut config = SolverConfig::new().with_timeout(Duration::from_millis(timeout_ms));
    config.resource_limit = resource_limit;
    config.memory_limit_mb = memory_limit_mb;
    config.node_budget = node_budget;
    config.cnf_variable_budget = cnf_variable_budget;
    config.cnf_clause_budget = cnf_clause_budget;
    config.prove_unsat = prove_unsat;
    config.preprocess = preprocess;
    config.bit_lowering_mode = BitLoweringMode::Eager;
    config
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

/// The default single-query budget the `_smtlib` helpers share.
fn default_config(timeout_ms: u64) -> SolverConfig {
    SolverConfig::new().with_timeout(Duration::from_millis(timeout_ms))
}

/// One response to one SMT-LIB output command.
///
/// `Unsupported` and `Error` stay distinct: the first says the command is
/// outside the implemented surface, the second that it was illegal in the
/// state the script had reached. Collapsing them loses the difference between
/// "we do not do that" and "that script is wrong".
#[pyclass(frozen, module = "axeyum", name = "Response")]
pub struct Response {
    kind: &'static str,
    text: Option<String>,
    status: Option<&'static str>,
    values: Option<Py<PyList>>,
    command: Option<String>,
}

#[pymethods]
impl Response {
    /// `"check-sat"`, `"model"`, `"values"`, `"unsat-core"`, `"proof"`,
    /// `"echo"`, `"assertions"`, `"unsupported"`, `"error"` or `"success"`.
    #[getter]
    fn kind(&self) -> &'static str {
        self.kind
    }

    /// The verdict, for a `"check-sat"` response.
    #[getter]
    fn status(&self) -> Option<&'static str> {
        self.status
    }

    /// The response payload as text, when it has one.
    #[getter]
    fn text(&self) -> Option<&str> {
        self.text.as_deref()
    }

    /// The command this response answers, for `"unsupported"` / `"error"`.
    #[getter]
    fn command(&self) -> Option<&str> {
        self.command.as_deref()
    }

    /// The list payload, for `"values"`, `"unsat-core"` and `"assertions"`.
    #[getter]
    fn values<'py>(&self, py: Python<'py>) -> Option<Bound<'py, PyList>> {
        self.values.as_ref().map(|values| values.bind(py).clone())
    }

    fn __repr__(&self) -> String {
        format!(
            "Response(kind={:?}, status={:?}, command={:?})",
            self.kind, self.status, self.command
        )
    }
}

/// The verdict text of a `CheckResult`.
fn verdict_name(result: &CheckResult) -> &'static str {
    match result {
        CheckResult::Sat(_) => "sat",
        CheckResult::Unsat => "unsat",
        CheckResult::Unknown(_) => "unknown",
    }
}

/// Runs a multi-`check-sat` script and returns one response per output command.
///
/// This is the only non-doc-hidden front door in the Rust crate, and the one a
/// `axeyum_cli script.smt2` run reaches. An unimplemented command answers
/// `unsupported` -- never silently nothing.
///
/// # Errors
///
/// Raises `SmtLibParseError` for malformed text; an illegal-in-state command
/// is an `error` RESPONSE, not an exception.
#[pyfunction]
#[pyo3(signature = (script, *, timeout_ms = 10_000))]
fn session(py: Python<'_>, script: &str, timeout_ms: u64) -> PyResult<Vec<Response>> {
    let config = default_config(timeout_ms);
    let responses = py
        .detach(|| solve_smtlib_session(script, &config))
        .map_err(map_solver_error)?;
    responses
        .into_iter()
        .map(|response| {
            Ok(match response {
                SmtLibResponse::CheckSat(result) => Response {
                    kind: "check-sat",
                    text: None,
                    status: Some(verdict_name(&result)),
                    values: None,
                    command: None,
                },
                SmtLibResponse::Model(text) => Response {
                    kind: "model",
                    text: Some(text),
                    status: None,
                    values: None,
                    command: None,
                },
                SmtLibResponse::Values(pairs) => Response {
                    kind: "values",
                    text: None,
                    status: None,
                    values: Some(PyList::new(py, pairs)?.unbind()),
                    command: None,
                },
                SmtLibResponse::UnsatCore(names) => Response {
                    kind: "unsat-core",
                    text: None,
                    status: None,
                    values: Some(PyList::new(py, names)?.unbind()),
                    command: None,
                },
                SmtLibResponse::Proof(text) => Response {
                    kind: "proof",
                    text: Some(text),
                    status: None,
                    values: None,
                    command: None,
                },
                SmtLibResponse::Echo(text) => Response {
                    kind: "echo",
                    text: Some(text),
                    status: None,
                    values: None,
                    command: None,
                },
                SmtLibResponse::Assertions(texts) => Response {
                    kind: "assertions",
                    text: None,
                    status: None,
                    values: Some(PyList::new(py, texts)?.unbind()),
                    command: None,
                },
                SmtLibResponse::Unsupported { command, detail } => Response {
                    kind: "unsupported",
                    text: Some(detail),
                    status: None,
                    values: None,
                    command: Some(command),
                },
                SmtLibResponse::Error { command, message } => Response {
                    kind: "error",
                    text: Some(message),
                    status: None,
                    values: None,
                    command: Some(command),
                },
                SmtLibResponse::Success => Response {
                    kind: "success",
                    text: None,
                    status: None,
                    values: None,
                    command: None,
                },
            })
        })
        .collect()
}

/// Runs a multi-`check-sat` script and returns just the verdicts, in order.
///
/// Delegates to the same session walk, so the two cannot disagree.
#[pyfunction]
#[pyo3(signature = (script, *, timeout_ms = 10_000))]
fn incremental(py: Python<'_>, script: &str, timeout_ms: u64) -> PyResult<Vec<&'static str>> {
    let config = default_config(timeout_ms);
    let results = py
        .detach(|| solve_smtlib_incremental(script, &config))
        .map_err(map_solver_error)?;
    Ok(results.iter().map(verdict_name).collect())
}

/// The values of the script's `(get-value ...)` terms under the model.
///
/// `None` when the script is not `sat`, or asks for no values. The values are
/// read from the **replay-checked** model through the ground evaluator.
#[pyfunction]
#[pyo3(signature = (script, *, timeout_ms = 10_000))]
fn get_value<'py>(
    py: Python<'py>,
    script: &str,
    timeout_ms: u64,
) -> PyResult<Option<Vec<Bound<'py, PyAny>>>> {
    let config = default_config(timeout_ms);
    let values = py
        .detach(|| solve_smtlib_get_value(script, &config))
        .map_err(map_solver_error)?;
    values
        .map(|values| {
            values
                .iter()
                .map(|value| value_to_py(py, value))
                .collect::<PyResult<Vec<_>>>()
        })
        .transpose()
}

/// The truth value of each `:named` Boolean assertion under the model.
///
/// `None` when the script is not `sat`.
#[pyfunction]
#[pyo3(signature = (script, *, timeout_ms = 10_000))]
fn get_assignment(
    py: Python<'_>,
    script: &str,
    timeout_ms: u64,
) -> PyResult<Option<Vec<(String, bool)>>> {
    let config = default_config(timeout_ms);
    py.detach(|| solve_smtlib_get_assignment(script, &config))
        .map_err(map_solver_error)
}

/// A deletion-minimized unsatisfiable core as `:named` labels.
///
/// Every returned name is genuinely needed. `None` when the script is not
/// `unsat`; a bounded-string `unsat` is gate-confirmed before a core is built.
#[pyfunction]
#[pyo3(signature = (script, *, timeout_ms = 10_000))]
fn unsat_core(py: Python<'_>, script: &str, timeout_ms: u64) -> PyResult<Option<Vec<String>>> {
    let config = default_config(timeout_ms);
    py.detach(|| solve_smtlib_unsat_core(script, &config))
        .map_err(map_solver_error)
}

/// A textual Alethe proof of an `unsat`, or `None`.
///
/// `None` means **no emitter covers this refutation**, not that the script is
/// satisfiable. Three fragments also pass external Carcara; the `QF_LIA` one
/// is internal-only, so it is tried last.
#[pyfunction]
#[pyo3(signature = (script, *, timeout_ms = 10_000))]
fn get_proof(py: Python<'_>, script: &str, timeout_ms: u64) -> PyResult<Option<String>> {
    let config = default_config(timeout_ms);
    py.detach(|| solve_smtlib_get_proof(script, &config))
        .map_err(map_solver_error)
}

/// A parsed SMT-LIB script, together with the arena it owns.
///
/// `parse_script` creates and gives away a `TermArena`, so a `Script` IS the
/// arena for its terms; the handles it hands out carry its own epoch and are
/// not interchangeable with an [`Arena`](axeyum.ir.Arena)'s.
#[pyclass(module = "axeyum", name = "Script")]
pub struct PyScript {
    script: Script,
    epoch: u64,
}

#[pymethods]
impl PyScript {
    /// The script's `(set-logic ...)`, when it declared one.
    #[getter]
    fn logic(&self) -> Option<&str> {
        self.script.logic.as_deref()
    }

    /// The script's `(set-info :status ...)` — benchmark ground truth, echoed
    /// for cross-checking and never consulted while solving.
    #[getter]
    fn expected_status(&self) -> Option<&str> {
        self.script.status.as_deref()
    }

    /// Number of `check-sat` commands.
    #[getter]
    fn check_sats(&self) -> u32 {
        self.script.check_sats
    }

    /// Whether the script used the bounded string/sequence encoding.
    ///
    /// When `True`, an `unsat` of the LOWERED query is only `unsat` within the
    /// encoding bound until the string gate confirms it.
    #[getter]
    fn uses_bounded_strings(&self) -> bool {
        self.script.uses_bounded_strings
    }

    /// The ordered `assert`/`push`/`pop`/`check-sat` sequence, as tagged dicts.
    #[getter]
    fn commands<'py>(&self, py: Python<'py>) -> PyResult<Bound<'py, PyList>> {
        let list = PyList::empty(py);
        for command in &self.script.commands {
            let entry = PyDict::new(py);
            match command {
                ScriptCommand::Assert(term) => {
                    entry.set_item("kind", "assert")?;
                    entry.set_item("term", ScriptTerm::new(self.epoch, *term))?;
                }
                ScriptCommand::Push(n) => {
                    entry.set_item("kind", "push")?;
                    entry.set_item("levels", n)?;
                }
                ScriptCommand::Pop(n) => {
                    entry.set_item("kind", "pop")?;
                    entry.set_item("levels", n)?;
                }
                ScriptCommand::CheckSat => entry.set_item("kind", "check-sat")?,
                ScriptCommand::CheckSatAssuming(terms) => {
                    entry.set_item("kind", "check-sat-assuming")?;
                    entry.set_item(
                        "terms",
                        terms
                            .iter()
                            .map(|&term| ScriptTerm::new(self.epoch, term))
                            .collect::<Vec<_>>(),
                    )?;
                }
                ScriptCommand::ResetAssertions => entry.set_item("kind", "reset-assertions")?,
                ScriptCommand::GetAssertions => entry.set_item("kind", "get-assertions")?,
                ScriptCommand::SetLogic(logic) => {
                    entry.set_item("kind", "set-logic")?;
                    entry.set_item("logic", logic)?;
                }
                ScriptCommand::SetOption { key, value } => {
                    entry.set_item("kind", "set-option")?;
                    entry.set_item("key", key)?;
                    entry.set_item("value", value)?;
                }
                ScriptCommand::GetModel => entry.set_item("kind", "get-model")?,
                ScriptCommand::GetValue(pairs) => {
                    entry.set_item("kind", "get-value")?;
                    entry.set_item(
                        "terms",
                        pairs
                            .iter()
                            .map(|(text, term)| (text.clone(), ScriptTerm::new(self.epoch, *term)))
                            .collect::<Vec<_>>(),
                    )?;
                }
                ScriptCommand::GetUnsatCore => entry.set_item("kind", "get-unsat-core")?,
                ScriptCommand::GetProof => entry.set_item("kind", "get-proof")?,
                ScriptCommand::Echo(text) => {
                    entry.set_item("kind", "echo")?;
                    entry.set_item("text", text)?;
                }
                ScriptCommand::UnansweredOutput(text) => {
                    entry.set_item("kind", "unanswered-output")?;
                    entry.set_item("text", text)?;
                }
            }
            list.append(entry)?;
        }
        Ok(list)
    }

    /// The flat assertion list a solver may soundly decide, or `None`.
    ///
    /// This binds `solvable_flat_view`, **not** `checked_flat_view`. `None` is
    /// returned for a word-first-fallback parse, whose `assertions` are empty
    /// because only the source-level side channels were populated: solving that
    /// empty view would be a vacuous `sat`, which is a shipped P0. The
    /// `checked_` sibling `debug_assert!`s instead of answering `None`, so it
    /// panics in debug and is silently wrong in release; it is deliberately
    /// not bound.
    fn flat_view(&self) -> Option<Vec<ScriptTerm>> {
        self.script.solvable_flat_view().map(|terms| {
            terms
                .iter()
                .map(|&t| ScriptTerm::new(self.epoch, t))
                .collect()
        })
    }

    /// The original bounded-parse error, when the script came through the
    /// word-first fallback (which is exactly when `flat_view()` is `None`).
    #[getter]
    fn word_only_fallback(&self) -> Option<&str> {
        self.script.word_only_fallback.as_deref()
    }

    /// Renders one of this script's terms as SMT-LIB-flavoured text.
    fn render(&self, term: ScriptTerm) -> PyResult<String> {
        let id = term.resolve(self.epoch)?;
        Ok(axeyum_ir::render(&self.script.arena, id))
    }

    /// The declared model constants, in declaration order.
    #[getter]
    fn model_symbols(&self) -> Vec<String> {
        self.script
            .model_symbols
            .iter()
            .map(|&symbol| self.script.arena.symbol(symbol).0.to_owned())
            .collect()
    }

    fn __repr__(&self) -> String {
        format!(
            "Script(logic={}, commands={}, check_sats={})",
            optional_repr(self.script.logic.as_deref()),
            self.script.commands.len(),
            self.script.check_sats
        )
    }
}

/// Parses an SMT-LIB 2 script without solving it.
///
/// `timeout_ms` bounds INGEST. A deadline or resource miss is an `unknown`
/// about the budget, not a statement about the script, so it raises
/// `BudgetExceeded` rather than `SmtLibParseError`.
///
/// # Errors
///
/// Raises `SmtLibParseError` for malformed or out-of-fragment text, and
/// `BudgetExceeded` when ingest ran out of budget.
#[pyfunction]
#[pyo3(signature = (script, *, timeout_ms = None))]
fn parse(py: Python<'_>, script: &str, timeout_ms: Option<u64>) -> PyResult<PyScript> {
    let deadline =
        timeout_ms.and_then(|ms| std::time::Instant::now().checked_add(Duration::from_millis(ms)));
    let parsed = py
        .detach(|| parse_script_within(script, deadline))
        .map_err(|error| match error {
            SmtError::DeadlineExceeded(what) | SmtError::ResourceLimit(what) => {
                BudgetExceeded::new_err(format!(
                    "ingest budget exhausted ({what}); this says nothing about the script"
                ))
            }
            other => SmtLibParseError::new_err(other.to_string()),
        })?;
    Ok(PyScript {
        script: parsed,
        epoch: next_script_epoch(),
    })
}

/// Writes `assertions` from an [`Arena`](axeyum.ir.Arena) as an SMT-LIB script.
///
/// Sharing-preserving: nodes with fan-in above one are hoisted to 0-ary
/// `define-fun`s, so the output is linear in the DAG rather than in the tree.
///
/// # Errors
///
/// Raises `EpochError` when an assertion belongs to another arena. The Rust
/// writer PANICS on a foreign term, which is why this is checked here.
#[pyfunction]
fn write_script(
    arena: PyRef<'_, crate::ir::arena::Arena>,
    assertions: Vec<crate::ir::types::Term>,
) -> PyResult<String> {
    let ids = arena.resolve_terms(&assertions)?;
    Ok(axeyum_smtlib::write_script(&arena.arena, &ids))
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
    module.add(
        "__doc__",
        "tier P + C -- decide an SMT-LIB 2 script through the text front door, and \
         replay the model yourself.",
    )?;
    module.add_class::<Outcome>()?;
    module.add_class::<Response>()?;
    module.add_class::<PyScript>()?;
    module.add_class::<ScriptTerm>()?;
    module.add_function(wrap_pyfunction!(solve, &module)?)?;
    module.add_function(wrap_pyfunction!(session, &module)?)?;
    module.add_function(wrap_pyfunction!(incremental, &module)?)?;
    module.add_function(wrap_pyfunction!(get_value, &module)?)?;
    module.add_function(wrap_pyfunction!(get_assignment, &module)?)?;
    module.add_function(wrap_pyfunction!(unsat_core, &module)?)?;
    module.add_function(wrap_pyfunction!(get_proof, &module)?)?;
    module.add_function(wrap_pyfunction!(parse, &module)?)?;
    module.add_function(wrap_pyfunction!(write_script, &module)?)?;
    parent.add("smt", &module)?;
    Ok(module)
}
