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
    Script, ScriptCommand, SmtError, decode_packed_string, packed_string_max_len, parse_script,
    parse_script_within,
};
use axeyum_solver::smtlib::{
    solve_smtlib, solve_smtlib_get_assertions, solve_smtlib_get_assignment, solve_smtlib_get_info,
    solve_smtlib_get_option, solve_smtlib_get_proof, solve_smtlib_get_value,
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
    replay_unavailable: Option<String>,
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
    /// `False` has exactly one meaning: the model was replayed and does NOT
    /// satisfy the assertions -- a soundness signal. When there is nothing to
    /// replay (`unsat`/`unknown`, or that one quantified route) this RAISES
    /// [`ReplayUnavailable`]; `replay_available` says so without raising.
    ///
    /// # Errors
    ///
    /// Raises `ReplayUnavailable` when no replay state exists, and
    /// `AxeyumError` if the evaluator fails on a term it cannot interpret.
    fn replay(&self, py: Python<'_>) -> PyResult<bool> {
        let Some(state) = self.replay.as_ref() else {
            return Err(crate::error::ReplayUnavailable::new_err(
                self.replay_unavailable.clone().unwrap_or_else(|| {
                    "no replay state; check `replay_available` first".to_owned()
                }),
            ));
        };
        py.detach(|| check_model(&state.arena, &state.assertions, &state.model))
            .map_err(map_solver_error)
    }

    /// Whether `replay()` has a model and arena to re-check.
    #[getter]
    fn replay_available(&self) -> bool {
        self.replay.is_some()
    }

    /// Why `replay()` would raise, or `None` when it is available.
    #[getter]
    fn replay_unavailable_reason(&self) -> Option<String> {
        self.replay_unavailable.clone()
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
    // needs the arena the original terms live in. So on `sat` the front door's
    // own model lift (`solve_smtlib_model`, the same route) is run once more and
    // laid onto the parsed script's arena, kept alive inside the `Outcome`. It
    // costs a second front-door call on `sat`; removing that needs a Rust entry
    // point returning verdict, arena, assertions and model together.
    let (replay, replay_unavailable, named) = if status == "sat" {
        match py.detach(|| build_replay_state(script, &config)) {
            Ok((state, named)) => (Some(state), None, named),
            Err(reason) => (None, Some(reason), Vec::new()),
        }
    } else {
        (
            None,
            Some(format!("no model to replay for a {status:?} outcome")),
            Vec::new(),
        )
    };

    Ok(Outcome {
        status,
        logic: outcome.logic,
        expected_status: outcome.expected_status,
        detail,
        model: model_dict(py, &named)?.unbind(),
        replay,
        replay_unavailable,
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
) -> Result<(ReplayState, Vec<(String, Value)>), String> {
    let mut script = parse_script(input).map_err(|error| format!("re-parse failed: {error}"))?;
    // A WORD-ONLY FALLBACK PARSE BUILDS NO FLAT ASSERTIONS, so `check_model`
    // over its (empty) assertion stack returns `true` having checked nothing.
    //
    // `parse_script` retries a bounded-encoder decline -- a string literal past
    // the ADR-0029 byte model, a `str.++` over the bound -- as a source-only
    // parse and records the reason in `word_only_fallback`. The front door then
    // decides the query on independently checked source routes, which is sound;
    // but the arena it hands back here has an empty assertion list, and a
    // checker whose input is empty cannot fail.
    //
    // Measured 2026-08-24 before this guard:
    //     (set-logic QF_S)(declare-fun s () String)
    //     (assert (= s "\u{100}"))(check-sat)
    // came back `sat` with `model == {}` and `replay() is True` -- a vacuous
    // certification. `axeyum_solver`'s own `solvable_flat_view` refuses exactly
    // this shape (it returns `None` rather than solving an empty assertion list
    // as a vacuous `sat`, a shipped P0); this is the same refusal on the replay
    // side, which was missing.
    if let Some(reason) = script.word_only_fallback.as_deref() {
        return Err(format!(
            "the replay re-parse fell back to a word-only parse ({reason}), which builds no flat \
             assertions; `check_model` over an empty assertion stack would accept any model, so \
             there is nothing here that could fail"
        ));
    }
    if script.check_sats > 1 {
        return Err(
            "multi-`check-sat` scripts are not replayed through `Outcome`; use `session`".into(),
        );
    }
    let assertions = active_assertions(&script);
    if let Some(term) = assertions
        .iter()
        .copied()
        .find(|&term| contains_quantifier(&script.arena, term))
    {
        return Err(format!(
            "assertion {} is quantified; the ground evaluator cannot decide a quantifier, so a `sat` here is not replayable through `check_model`",
            axeyum_ir::render(&script.arena, term)
        ));
    }
    // The SAME route the verdict came from (`solve_smtlib_model` is the front
    // door plus a model lift), not `axeyum_solver::solve`, which can decide a
    // different way -- measured 2026-08-24: a quantified `LIA` query was `sat`
    // by both routes, and `solve`'s model, replayed, said `False` for a reason
    // that had nothing to do with soundness.
    let lifted = axeyum_solver::smtlib::solve_smtlib_model(input, config)
        .map_err(|error| format!("front-door model lift failed: {error}"))?
        .ok_or_else(|| "the front door produced no liftable model for this `sat`".to_owned())?;
    let mut model = Model::new();
    for (name, value) in &lifted.constants {
        let Some(symbol) = script.arena.find_symbol(name) else {
            return Err(format!(
                "front-door model names `{name}`, which the parsed script does not declare"
            ));
        };
        let value = lift_onto_arena(&script, symbol, value.clone())?;
        model.set(symbol, value);
    }
    for (name, func) in &lifted.functions {
        let Some(id) = script.arena.find_function(name) else {
            return Err(format!(
                "front-door model names function `{name}`, which the parsed script does not declare"
            ));
        };
        model.set_function(id, func.clone());
    }
    // Symbols the front door left unconstrained get the same well-founded
    // default the solver's own completion uses, so `check_model` sees a total
    // assignment. A symbol with no well-founded default is left unassigned and
    // `check_model` reports it, rather than this code inventing a value.
    let unassigned: Vec<(SymbolId, Sort)> = script
        .arena
        .symbols()
        .filter(|(symbol, _, _)| model.get(*symbol).is_none())
        .map(|(symbol, _, sort)| (symbol, sort))
        .collect();
    for (symbol, sort) in unassigned {
        if let Some(value) = axeyum_ir::well_founded_default(&script.arena, sort) {
            model.set(symbol, value);
        }
    }
    let named = named_constants(&script, &model);
    let arena = std::mem::take(&mut script.arena);
    Ok((
        ReplayState {
            arena,
            assertions,
            model,
        },
        named,
    ))
}

/// Converts a front-door model value into the representation the parsed
/// script's arena uses for `symbol`.
///
/// The parser lowers a declared `String` to a packed bit-vector (length field
/// in the low bits, then little-endian bytes), while the front door lifts the
/// same symbol back to a `Seq` of code points. `check_model` evaluates the
/// ARENA's terms, so the value must be packed again. The packing is checked
/// against the public `decode_packed_string` before it is trusted: an encoder
/// that disagreed with the decoder would replay the wrong string, and that is
/// refused rather than replayed.
fn lift_onto_arena(script: &Script, symbol: SymbolId, value: Value) -> Result<Value, String> {
    let is_declared_string = script.declared_strings.iter().any(|&(s, _)| s == symbol);
    let (name, sort) = script.arena.symbol(symbol);
    match (is_declared_string, &value, sort) {
        (true, Value::Seq(elements), Sort::BitVec(width)) => {
            let mut bytes = Vec::with_capacity(elements.len());
            for element in elements {
                match element {
                    Value::Bv { value: code, .. } if *code <= 0xff => {
                        bytes.push(u8::try_from(*code).map_err(|e| e.to_string())?);
                    }
                    other => {
                        return Err(format!(
                            "string `{name}` carries code point {other:?}, outside the packed encoding"
                        ));
                    }
                }
            }
            let packed = encode_packed_string(width, &bytes).ok_or_else(|| {
                format!(
                    "string `{name}` ({} bytes) does not fit its packed width {width}",
                    bytes.len()
                )
            })?;
            if decode_packed_string(width, packed).as_deref() != Some(bytes.as_slice()) {
                return Err(format!(
                    "packed encoding of string `{name}` did not round-trip through the decoder"
                ));
            }
            Ok(Value::Bv {
                width,
                value: packed,
            })
        }
        _ => Ok(value),
    }
}

/// Inverse of `decode_packed_string` for the parser's layout: `len_width`
/// low bits hold the length, bytes follow little-endian, 8 bits each.
fn encode_packed_string(width: u32, bytes: &[u8]) -> Option<u128> {
    let max_len = packed_string_max_len(width)?;
    let len = u32::try_from(bytes.len()).ok()?;
    if len > max_len {
        return None;
    }
    let lw = 32 - max_len.leading_zeros();
    let mut content: u128 = 0;
    for (i, &b) in bytes.iter().enumerate() {
        content |= u128::from(b) << (8 * i);
    }
    Some((content << lw) | u128::from(len))
}

/// Whether `term`'s DAG contains a `forall`/`exists` node.
fn contains_quantifier(arena: &TermArena, term: TermId) -> bool {
    let mut stack = vec![term];
    let mut seen = std::collections::HashSet::new();
    while let Some(current) = stack.pop() {
        if !seen.insert(current) {
            continue;
        }
        if let axeyum_ir::TermNode::App { op, args } = arena.node(current) {
            if matches!(op, axeyum_ir::Op::Forall(_) | axeyum_ir::Op::Exists(_)) {
                return true;
            }
            stack.extend(args.iter().copied());
        }
    }
    false
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

/// The assertion-stack snapshots the script's `(get-assertions)` commands ask
/// for, one list of SMT-LIB texts per command, in script order.
///
/// Tier **R** — pure. The Rust function ignores the config and never solves;
/// the snapshot is taken at the exact command point, after honoring prior
/// `assert`/`push`/`pop`/`reset-assertions`. One-shot `check-sat-assuming`
/// assumptions are deliberately NOT in the stack, so a snapshot is the
/// assertion set and not the last query.
///
/// `None` means the script requested no snapshots — not that it has no
/// assertions.
#[pyfunction]
#[pyo3(signature = (script,))]
fn get_assertions(py: Python<'_>, script: &str) -> PyResult<Option<Vec<Vec<String>>>> {
    // The Rust signature takes a config and ignores it (`_config`), so this
    // binding offers no budget: a timeout that cannot bite is worse than none.
    let config = SolverConfig::new();
    py.detach(|| solve_smtlib_get_assertions(script, &config))
        .map_err(map_solver_error)
}

/// The `(get-info ...)` answers, as `(key, value)` pairs in script order.
///
/// Tier **R/P**. Pure for every key EXCEPT `:reason-unknown`, which solves the
/// single active query — so this one takes a budget. An unrecognized key comes
/// back as `"unsupported"` rather than being dropped: a missing pair and an
/// unsupported one are different answers.
///
/// `:reason-unknown` is the empty SMT-LIB string literal `""` when the query
/// was decided; the classified reason is returned only for an actual
/// `unknown`. `None` when the script asks for no info.
#[pyfunction]
#[pyo3(signature = (script, *, timeout_ms = 10_000))]
fn get_info(
    py: Python<'_>,
    script: &str,
    timeout_ms: u64,
) -> PyResult<Option<Vec<(String, String)>>> {
    let config = default_config(timeout_ms);
    py.detach(|| solve_smtlib_get_info(script, &config))
        .map_err(map_solver_error)
}

/// The `(get-option ...)` answers, as `(key, value)` pairs in script order.
///
/// Tier **R** — pure; nothing is solved. A key the script set is echoed
/// verbatim, an unset standard key gets its SMT-LIB default, and anything else
/// is `"unsupported"`. This is the option state a driver would observe, which
/// is not the same as "the solver honors it".
///
/// `None` when the script asks for no options.
#[pyfunction]
#[pyo3(signature = (script,))]
fn get_option(py: Python<'_>, script: &str) -> PyResult<Option<Vec<(String, String)>>> {
    // `_config` upstream: no budget is offered, because none would apply.
    let config = SolverConfig::new();
    py.detach(|| solve_smtlib_get_option(script, &config))
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
    module.add_function(wrap_pyfunction!(get_assertions, &module)?)?;
    module.add_function(wrap_pyfunction!(get_info, &module)?)?;
    module.add_function(wrap_pyfunction!(get_option, &module)?)?;
    module.add_function(wrap_pyfunction!(parse, &module)?)?;
    module.add_function(wrap_pyfunction!(write_script, &module)?)?;
    parent.add("smt", &module)?;
    Ok(module)
}

#[cfg(test)]
mod tests {
    use axeyum_ir::{Sort, TermArena, Value};
    use axeyum_smtlib::{decode_packed_string, packed_string_max_len, parse_script};

    use super::{
        build_replay_state, contains_quantifier, encode_packed_string, lift_onto_arena,
        next_script_epoch, script_config,
    };

    /// The widths for which the parser's packed-string layout is defined.
    ///
    /// `packed_string_max_len` answers `Some` only for widths that are exactly
    /// the total of some maximum length, so the widths are DERIVED here rather
    /// than written down: a hard-coded width that stopped being a legal packed
    /// width would make this suite skip everything while staying green.
    fn packed_widths(count: usize) -> Vec<(u32, u32)> {
        let widths: Vec<(u32, u32)> = (1..=512)
            .filter_map(|width| packed_string_max_len(width).map(|max| (width, max)))
            .filter(|&(_, max)| max >= 1)
            .take(count)
            .collect();
        assert_eq!(
            widths.len(),
            count,
            "fewer than {count} packed string widths exist; the layout changed"
        );
        widths
    }

    /// The encoder is the inverse of the public decoder at every length.
    ///
    /// `lift_onto_arena` trusts `encode_packed_string` to reproduce the layout
    /// `decode_packed_string` reads. If the two ever disagreed, a replayed
    /// model would carry a DIFFERENT string than the solver found -- and the
    /// replay would then be checking a claim nobody made.
    #[test]
    fn packed_string_encoder_round_trips_at_every_length() {
        let mut checked = 0usize;
        for (width, max_len) in packed_widths(3) {
            for len in 0..=max_len {
                let bytes: Vec<u8> = (0..len)
                    .map(|i| u8::try_from(i % 251).unwrap_or(7))
                    .collect();
                let packed = encode_packed_string(width, &bytes)
                    .unwrap_or_else(|| panic!("width {width} refused a {len}-byte string"));
                assert_eq!(
                    decode_packed_string(width, packed).as_deref(),
                    Some(bytes.as_slice()),
                    "width {width}, length {len} did not round-trip"
                );
                checked += 1;
            }
            // One past the maximum must be refused, not silently truncated.
            let too_long: Vec<u8> = vec![b'x'; (max_len + 1) as usize];
            assert!(
                encode_packed_string(width, &too_long).is_none(),
                "width {width} accepted a string one byte over its maximum"
            );
        }
        assert!(checked >= 3, "only {checked} lengths were exercised");
    }

    /// A quantified assertion is detected; an equally deep ground one is not.
    #[test]
    fn contains_quantifier_finds_a_binder_and_only_a_binder() {
        let mut arena = TermArena::new();
        let symbol = arena.declare("p", Sort::Bool).expect("declare p");
        let p = arena.var(symbol);
        let ground = arena.and(p, p).expect("and");
        assert!(!contains_quantifier(&arena, ground));

        let quantified = arena.forall(symbol, ground).expect("forall");
        assert!(contains_quantifier(&arena, quantified));

        // Nested below another node, so the walk -- not just the root check --
        // is what is under test.
        let nested = arena.and(ground, quantified).expect("and");
        assert!(contains_quantifier(&arena, nested));
    }

    /// A code point outside the packed byte model is refused, not truncated.
    ///
    /// Truncating it would replay a DIFFERENT string than the solver found and
    /// report `True`; the refusal is what makes `replay()` unavailable instead.
    #[test]
    fn lift_onto_arena_refuses_an_out_of_range_code_point() {
        let script = parse_script(
            "(set-logic QF_S)(declare-fun s () String)(assert (= s \"ab\"))(check-sat)",
        )
        .expect("parse");
        let symbol = script.arena.find_symbol("s").expect("declared symbol s");

        let wide = Value::Seq(vec![Value::Bv {
            width: 16,
            value: 0x100,
        }]);
        let error = lift_onto_arena(&script, symbol, wide).expect_err("U+0100 must be refused");
        assert!(
            error.contains("outside the packed encoding"),
            "unexpected refusal: {error}"
        );

        // Positive control: an in-range value lifts, and lands as a packed
        // bit-vector rather than staying a sequence.
        let in_range = Value::Seq(vec![
            Value::Bv {
                width: 16,
                value: u128::from(b'a'),
            },
            Value::Bv {
                width: 16,
                value: u128::from(b'b'),
            },
        ]);
        let lifted = lift_onto_arena(&script, symbol, in_range).expect("in-range value lifts");
        assert!(matches!(lifted, Value::Bv { .. }), "{lifted:?}");
    }

    /// Script epochs strictly increase, so two scripts never share one.
    ///
    /// A repeated epoch would make one script's `ScriptTerm` resolve against
    /// another script's arena -- an index into the wrong table, which is a
    /// wrong term rather than an error.
    #[test]
    fn script_epochs_are_monotone() {
        let first = next_script_epoch();
        let second = next_script_epoch();
        let third = next_script_epoch();
        assert!(first < second && second < third, "{first} {second} {third}");
        // Disjoint from the `ir::Arena` range, which starts at 1.
        assert!(
            first >= 1 << 32,
            "script epochs must not collide with arenas"
        );
    }

    /// A word-only fallback parse yields NO replay state.
    ///
    /// The fallback builds no flat assertions, so `check_model` over its
    /// assertion stack returns `true` having checked nothing. Before the guard
    /// in `build_replay_state`, this script came back `sat` with an empty model
    /// and `replay() == True` -- a certification of nothing.
    #[test]
    fn a_word_only_fallback_parse_has_no_replay_state() {
        let script =
            "(set-logic QF_S)(declare-fun s () String)(assert (= s \"\\u{100}\"))(check-sat)";
        let parsed = parse_script(script).expect("the fallback parse succeeds");
        assert!(
            parsed.word_only_fallback.is_some(),
            "this fixture no longer exercises the fallback"
        );
        assert!(
            super::active_assertions(&parsed).is_empty(),
            "the fallback parse must have no flat assertions -- that is the hazard"
        );

        let config = script_config(10_000, None, None, None, None, None, false, true);
        let error = build_replay_state(script, &config)
            .err()
            .expect("no replay state for a word-only fallback parse");
        assert!(error.contains("word-only"), "unexpected reason: {error}");
    }
}
