//! The SMT-LIB text front door (ADR-0018).
//!
//! [`solve_smtlib`] is the entry point a real SMT consumer reaches for: it takes
//! a script as *text* — a file, an editor buffer, output from another tool —
//! parses it with [`axeyum_smtlib`], and decides it with [`crate::solve`]. The
//! whole path is text in, a checked `sat`/`unsat`/`unknown` out.
//!
//! The script's declared `(set-info :status ...)` is passed through unchanged in
//! [`SmtLibOutcome::expected_status`]; it is *not* consulted when solving, so a
//! caller can cross-check the decision against the benchmark's own ground truth.
//! The trust anchor stays exactly where it is in [`crate::solve`]: a `sat` model
//! is replayed against the original term through the ground evaluator.

use axeyum_cnf::{check_alethe, write_alethe};
use std::collections::{BTreeMap, VecDeque};

use axeyum_ir::{Sort, TermArena, TermId};
use axeyum_smtlib::{Script, ScriptCommand, parse_script};

use crate::auto::{solve, unsat_core};
use crate::backend::{CheckResult, SolverConfig, SolverError};
use crate::optimize::{OptOutcome, maximize_bv, maximize_lia, minimize_bv, minimize_lia};

/// The result of deciding an SMT-LIB script, with the script's own declarations.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct SmtLibOutcome {
    /// The decision for the conjunction of the script's assertions.
    pub result: CheckResult,
    /// The `set-logic` value, if the script declared one.
    pub logic: Option<String>,
    /// The declared `(set-info :status ...)` (`"sat"`/`"unsat"`/`"unknown"`), if
    /// present. Ground truth for cross-checking; never consulted when solving.
    pub expected_status: Option<String>,
}

#[derive(Debug, Clone)]
struct SmtLibSingleQuery {
    assertions: Vec<TermId>,
    assertion_names: Vec<Option<String>>,
}

fn smtlib_single_query(script: &Script) -> Result<SmtLibSingleQuery, SolverError> {
    if script.check_sats > 1 {
        return Err(SolverError::Unsupported(
            "single-result SMT-LIB helper received multiple check-sat commands; use \
             solve_smtlib_incremental to get one result per query"
                .to_owned(),
        ));
    }

    let mut names_by_term = BTreeMap::<TermId, VecDeque<Option<String>>>::new();
    for (&assertion, name) in script.assertions.iter().zip(&script.assertion_names) {
        names_by_term
            .entry(assertion)
            .or_default()
            .push_back(name.clone());
    }

    let mut stack = Vec::<(TermId, Option<String>)>::new();
    let mut scopes = Vec::<usize>::new();
    let mut queried_stack = None;
    for command in &script.commands {
        match command {
            ScriptCommand::Assert(term) => {
                let name = names_by_term
                    .get_mut(term)
                    .and_then(VecDeque::pop_front)
                    .unwrap_or(None);
                stack.push((*term, name));
            }
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
            ScriptCommand::CheckSat => {
                queried_stack = Some(stack.clone());
            }
            ScriptCommand::CheckSatAssuming(assumptions) => {
                let mut with_assumptions = stack.clone();
                with_assumptions.extend(assumptions.iter().copied().map(|term| (term, None)));
                queried_stack = Some(with_assumptions);
            }
            ScriptCommand::ResetAssertions => {
                stack.clear();
                scopes.clear();
            }
        }
    }

    let active = queried_stack.unwrap_or(stack);
    let (assertions, assertion_names) = active.into_iter().unzip();
    Ok(SmtLibSingleQuery {
        assertions,
        assertion_names,
    })
}

/// Parses an SMT-LIB 2 script and decides it — the text front door.
///
/// For a script with zero or one `check-sat`/`check-sat-assuming`, the active
/// assertion stack at that query is decided by [`crate::solve`], honoring
/// `push`/`pop`, `check-sat-assuming`, and `reset-assertions` semantics. Scripts
/// with multiple queries should use [`solve_smtlib_incremental`], because this
/// helper has a single-result return type. The returned
/// [`SmtLibOutcome::expected_status`] reflects the script's own declared
/// `:status` and is left for the caller to compare against
/// [`SmtLibOutcome::result`].
///
/// # Errors
///
/// - [`SolverError::Parse`] when the text is malformed or uses an SMT-LIB
///   construct outside the supported fragment.
/// - any [`SolverError`] from [`crate::solve`] (e.g. a non-Boolean assertion or
///   an internal backend failure).
pub fn solve_smtlib(input: &str, config: &SolverConfig) -> Result<SmtLibOutcome, SolverError> {
    let mut script = parse_script(input).map_err(|error| SolverError::Parse(error.to_string()))?;
    let query = smtlib_single_query(&script)?;
    let result = solve(&mut script.arena, &query.assertions, config)?;
    Ok(SmtLibOutcome {
        result,
        logic: script.logic,
        expected_status: script.status,
    })
}

/// Solves an **optimization** (OMT) SMT-LIB script: each `(maximize t)` /
/// `(minimize t)` objective is optimized subject to the script's assertions,
/// returning one [`OptOutcome`] per objective in script order (the boxed /
/// independent interpretation). The objective sort selects the engine — `Int`
/// uses the simplex-bounded integer optimizer, `BitVec` the unsigned bit-vector
/// optimizer — and each `Optimal` value is anchored by the underlying optimizer's
/// model checks (ADR-0020 / the optimize module).
///
/// # Errors
///
/// [`SolverError::Parse`] for malformed/unsupported text, [`SolverError::Unsupported`]
/// for an objective outside the supported (`Int`/`BitVec`) optimization
/// fragment, or any [`SolverError`] from the optimizer.
pub fn optimize_smtlib(input: &str, config: &SolverConfig) -> Result<Vec<OptOutcome>, SolverError> {
    let _ = config;
    let mut script = parse_script(input).map_err(|error| SolverError::Parse(error.to_string()))?;
    let query = smtlib_single_query(&script)?;
    let objectives = std::mem::take(&mut script.objectives);
    let mut outcomes = Vec::with_capacity(objectives.len());
    for (objective, is_max) in objectives {
        outcomes.push(optimize_one(
            &mut script.arena,
            &query.assertions,
            objective,
            is_max,
        )?);
    }
    Ok(outcomes)
}

/// Lexicographic (priority-order) multi-objective optimization: each objective is
/// optimized subject to the previous ones being **fixed at their optima**. The
/// first objective is optimized over the assertions; if it has an exact optimum,
/// the constraint `objective = optimum` is added before optimizing the next, and
/// so on. Returns the optima in priority (declaration) order. (Z3's `lex` mode;
/// [`optimize_smtlib`] gives the independent/`box` interpretation.)
///
/// # Errors
///
/// As [`optimize_smtlib`]; additionally [`SolverError::Backend`] if a fixing
/// constraint cannot be built.
pub fn optimize_smtlib_lexicographic(
    input: &str,
    config: &SolverConfig,
) -> Result<Vec<OptOutcome>, SolverError> {
    let _ = config;
    let mut script = parse_script(input).map_err(|error| SolverError::Parse(error.to_string()))?;
    let query = smtlib_single_query(&script)?;
    let objectives = std::mem::take(&mut script.objectives);
    let mut assertions = query.assertions;
    let mut outcomes = Vec::with_capacity(objectives.len());
    for (objective, is_max) in objectives {
        let outcome = optimize_one(&mut script.arena, &assertions, objective, is_max)?;
        // Pin this objective at its optimum for the lower-priority ones.
        if let OptOutcome::Optimal(value) = outcome {
            let pin = match script.arena.sort_of(objective) {
                Sort::Int => script.arena.int_const(value),
                Sort::BitVec(width) => {
                    let mask = if width >= 128 {
                        u128::MAX
                    } else {
                        (1u128 << width) - 1
                    };
                    #[allow(clippy::cast_sign_loss)] // two's-complement reinterpret into the BV
                    let bits = (value as u128) & mask;
                    script
                        .arena
                        .bv_const(width, bits)
                        .map_err(|e| SolverError::Backend(e.to_string()))?
                }
                _ => unreachable!("optimize_one rejects non-Int/BitVec objectives"),
            };
            let eq = script
                .arena
                .eq(objective, pin)
                .map_err(|e| SolverError::Backend(e.to_string()))?;
            assertions.push(eq);
        }
        outcomes.push(outcome);
    }
    Ok(outcomes)
}

/// Optimizes one objective subject to `assertions`, dispatching by sort (`Int` /
/// `BitVec`, unsigned) and direction.
fn optimize_one(
    arena: &mut TermArena,
    assertions: &[axeyum_ir::TermId],
    objective: axeyum_ir::TermId,
    is_max: bool,
) -> Result<OptOutcome, SolverError> {
    match (arena.sort_of(objective), is_max) {
        (Sort::Int, true) => maximize_lia(arena, assertions, objective),
        (Sort::Int, false) => minimize_lia(arena, assertions, objective),
        (Sort::BitVec(_), true) => maximize_bv(arena, assertions, objective),
        (Sort::BitVec(_), false) => minimize_bv(arena, assertions, objective),
        (other, _) => Err(SolverError::Unsupported(format!(
            "optimization objective of sort {other:?} (only Int and BitVec are supported)"
        ))),
    }
}

/// Evaluates the `(get-value (t …))` terms of an SMT-LIB script against a `sat`
/// model. The conjunction of all assertions is decided; on `sat` each requested
/// term is evaluated through the ground evaluator under the model, returning the
/// values in script order. Returns `Ok(None)` when the script is `unsat`/
/// `unknown` (no model) or requested no values.
///
/// This is the model-query companion to [`solve_smtlib`]: the same trusted `sat`
/// model that is replay-checked is what the values are read from.
///
/// # Errors
///
/// [`SolverError::Parse`] for malformed/unsupported text, any [`SolverError`]
/// from [`crate::solve`], or [`SolverError::Backend`] if a requested term fails
/// to evaluate under the model.
pub fn solve_smtlib_get_value(
    input: &str,
    config: &SolverConfig,
) -> Result<Option<Vec<axeyum_ir::Value>>, SolverError> {
    let mut script = parse_script(input).map_err(|error| SolverError::Parse(error.to_string()))?;
    let query = smtlib_single_query(&script)?;
    if script.get_value_terms.is_empty() {
        return Ok(None);
    }
    let CheckResult::Sat(model) = solve(&mut script.arena, &query.assertions, config)? else {
        return Ok(None);
    };
    let assignment = model.to_assignment();
    let mut values = Vec::with_capacity(script.get_value_terms.len());
    for &term in &script.get_value_terms {
        let value = axeyum_ir::eval(&script.arena, term, &assignment)
            .map_err(|e| SolverError::Backend(format!("get-value evaluation failed: {e}")))?;
        values.push(value);
    }
    Ok(Some(values))
}

/// Extracts an **unsat core** from an SMT-LIB script (`get-unsat-core`): the
/// conjunction of all its assertions is decided, and if it is `unsat`, a minimal
/// unsatisfiable subset is returned, reported as the assertions' `:named` labels
/// where present (and `assertion #i` otherwise, in script order). Returns
/// `Ok(None)` when the script is `sat`/`unknown` (no core exists).
///
/// The core is the deletion-minimized subset from [`crate::unsat_core`], so every
/// returned name is genuinely needed for unsatisfiability.
///
/// # Errors
///
/// [`SolverError::Parse`] for malformed/unsupported text, or any [`SolverError`]
/// from the underlying [`crate::unsat_core`] solving.
pub fn solve_smtlib_unsat_core(
    input: &str,
    config: &SolverConfig,
) -> Result<Option<Vec<String>>, SolverError> {
    let mut script = parse_script(input).map_err(|error| SolverError::Parse(error.to_string()))?;
    let query = smtlib_single_query(&script)?;
    let Some(core) = unsat_core(&mut script.arena, &query.assertions, config)? else {
        return Ok(None);
    };
    let names = core
        .into_iter()
        .map(|i| {
            query
                .assertion_names
                .get(i)
                .and_then(Clone::clone)
                .unwrap_or_else(|| format!("assertion #{i}"))
        })
        .collect();
    Ok(Some(names))
}

/// Produces a checkable **Alethe proof** for an SMT-LIB script (`get-proof`):
/// when the conjunction of its assertions is `unsat` and falls within a supported
/// proof fragment, returns the textual Alethe proof, re-validated by the in-tree
/// checker before it is returned. Four fragments are tried, in order:
///
/// - **`QF_BV`**: a complete `bitblast_*` → CNF-introduction → resolution
///   refutation deriving `(cl)` (re-checked by [`check_alethe`]).
/// - **`QF_UF`** (EUF) / **`QF_ABV`**: a congruence/transitivity refutation
///   (re-checked by [`check_alethe`]) — also proves array extensionality
///   (`select`/`store` as UF) and the array read-over-write-same disequality (the
///   latter via the internal-only `read_over_write_same` rule).
/// - **`QF_LRA`**: a Farkas `la_generic` + resolution refutation (re-checked by
///   [`crate::check_alethe_lra`], which decides the `la_generic` coefficients).
/// - **`QF_LIA`**: an integer `lia_generic` refutation (re-checked by
///   [`crate::check_alethe_lra`], which honors integrality).
///
/// Each emitter is self-validating (it returns a proof only when it checks), and
/// this re-validates again as defense in depth. The first three fragments' proofs
/// are also accepted by the external Carcara checker (see
/// `crates/axeyum-solver/tests/carcara_crosscheck.rs`); the **`QF_LIA`** proof is
/// checkable only *internally* — Carcara has no `lia_generic` rule and treats it as
/// a hole — so it is tried LAST, after the Carcara-valid routes.
///
/// Returns `Ok(None)` when no Alethe proof is available — the script is
/// `sat`/`unknown`, or its `unsat` is outside all supported fragments (e.g. `QF_BV`
/// with shifts/division/remainder, or a theory with no Alethe emitter yet).
///
/// # Errors
///
/// [`SolverError::Parse`] for malformed/unsupported text.
pub fn solve_smtlib_get_proof(
    input: &str,
    _config: &SolverConfig,
) -> Result<Option<String>, SolverError> {
    let script = parse_script(input).map_err(|error| SolverError::Parse(error.to_string()))?;
    let query = smtlib_single_query(&script)?;
    let arena = &script.arena;
    let assertions = &query.assertions;

    // QF_BV: the bitblast→CNF→resolution driver (re-checked by check_alethe).
    if let Some(proof) = crate::prove_qf_bv_unsat_alethe(arena, assertions)
        && matches!(check_alethe(&proof), Ok(true))
    {
        return Ok(Some(write_alethe(&proof)));
    }
    // QF_UF (EUF) and QF_ABV: the array emitter handles a read-over-write-same
    // disequality and otherwise falls back to the EUF congruence/transitivity
    // emitter (which also proves array extensionality, `select`/`store` as UF). All
    // re-checked by check_alethe. NOTE: a pure-EUF proof is Carcara-valid, but the
    // `read_over_write_same` step (array path) is checkable only *internally*
    // (Carcara has no array rules — see the array-proof design note).
    if let Some(proof) = crate::prove_qf_abv_unsat_alethe(arena, assertions)
        && matches!(check_alethe(&proof), Ok(true))
    {
        return Ok(Some(write_alethe(&proof)));
    }
    // QF_LRA: a Farkas la_generic refutation (re-checked by check_alethe_lra, which
    // owns the arithmetic la_generic decision the plain check_alethe lacks).
    if let Some(proof) = crate::prove_lra_unsat_alethe(arena, assertions)
        && matches!(crate::check_alethe_lra(&proof), Ok(true))
    {
        return Ok(Some(write_alethe(&proof)));
    }
    // QF_LIA: an integer `lia_generic` refutation, re-checked by check_alethe_lra
    // (which honors integrality). NOTE: unlike the other three fragments, this proof
    // is checkable only *internally* — Carcara has no `lia_generic` rule, so it
    // treats the step as a hole. Tried last so a problem also expressible over the
    // reals takes the Carcara-valid LRA route first.
    if let Some(proof) = crate::prove_lia_unsat_alethe(arena, assertions)
        && matches!(crate::check_alethe_lra(&proof), Ok(true))
    {
        return Ok(Some(write_alethe(&proof)));
    }
    Ok(None)
}

/// Decides an **incremental** SMT-LIB script, returning one result per
/// `check-sat` in order (ADR-0009 lifecycle, ADR-0018 front door).
///
/// `push`/`pop` scope the assertion stack: `(push n)` opens `n` nested scopes,
/// `(pop n)` drops the assertions made within the `n` innermost ones, and each
/// `check-sat` decides the conjunction of the currently-active assertions.
/// `(check-sat-assuming (l …))` decides the active assertions together with the
/// assumption literals `l`, *without* retaining them past that query. The
/// decision at each `check-sat` is by [`crate::solve`] over that assertion set —
/// re-solved from scratch, which is *semantically equivalent* to incremental
/// solving (the warm-restart backends, ADR-0009, are a performance path, not a
/// soundness one). Declarations are global (the shared arena keeps them), which
/// is sound for deciding the assertion sets even across `pop`.
///
/// # Errors
///
/// [`SolverError::Parse`] for malformed/unsupported text, or any
/// [`SolverError`] from a per-`check-sat` [`crate::solve`].
pub fn solve_smtlib_incremental(
    input: &str,
    config: &SolverConfig,
) -> Result<Vec<CheckResult>, SolverError> {
    let mut script = parse_script(input).map_err(|error| SolverError::Parse(error.to_string()))?;
    let mut stack: Vec<axeyum_ir::TermId> = Vec::new();
    let mut scopes: Vec<usize> = Vec::new(); // assertion-stack depth at each open push
    let mut results = Vec::new();
    for command in &script.commands {
        match command {
            ScriptCommand::Assert(t) => stack.push(*t),
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
            ScriptCommand::CheckSat => {
                results.push(solve(&mut script.arena, &stack, config)?);
            }
            ScriptCommand::CheckSatAssuming(assumptions) => {
                // Decide the active assertions together with the assumptions, but
                // do not retain them: solve a temporary stack, then discard.
                let mut with = stack.clone();
                with.extend_from_slice(assumptions);
                results.push(solve(&mut script.arena, &with, config)?);
            }
            ScriptCommand::ResetAssertions => {
                // Remove all assertions and open scopes (declarations stay interned
                // in the arena). Subsequent `check-sat`s see only assertions made
                // after the reset — the SMT-LIB `reset-assertions` semantics.
                stack.clear();
                scopes.clear();
            }
        }
    }
    Ok(results)
}
