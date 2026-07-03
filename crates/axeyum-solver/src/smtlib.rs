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
use std::collections::{BTreeMap, HashMap, VecDeque};

use axeyum_ir::{
    FuncValue, Op, Sort, TermArena, TermId, TermNode, Value, render, well_founded_default,
};
use axeyum_smtlib::{Script, ScriptCommand, parse_script};
use axeyum_strings::{SearchBudget, SearchOutcome, solve_word_equations};

use crate::auto::{solve, unsat_core};
use crate::backend::{CheckResult, SolverConfig, SolverError, UnknownKind, UnknownReason};
use crate::model::Model;
use crate::optimize::{OptOutcome, maximize_bv, maximize_lia, minimize_bv, minimize_lia};

/// The branch-node budget the word-equation route (ADR-0053, T-B.4b) spends per
/// front-door query. The search additionally honors an absolute deadline derived
/// from [`SolverConfig::timeout`]; this node cap is the sole termination guard
/// when no timeout is set (and under `wasm32`, where the deadline is absent). It
/// is deliberately generous — the search prunes hard via T-B.3 inference and the
/// per-path Skolem cap — while bounding the pathological loop shape to a fast,
/// first-class `unknown`.
const WORD_ROUTE_MAX_NODES: u64 = 200_000;

/// The word-equation second-chance route (ADR-0053, T-B.4b).
///
/// Runs **strictly after** the ADR-0029 bounded pre-check and the ADR-0052
/// [`StringGate`], and only when the current verdict is `unknown` (the bounded
/// path declined or the gate downgraded) *and* the parser accumulated a
/// [`WordProblem`](axeyum_smtlib::WordProblem) side channel. It may only ever
/// **add** `sat`: on a replay-checked [`SearchOutcome::Sat`] it returns `sat`,
/// and on [`SearchOutcome::Unknown`] it preserves the prior `unknown` (recording
/// the decline in the reason detail — the "unknown-ends-in-declined" telemetry
/// invariant). The word search has no `unsat` capability by construction, so this
/// can never introduce an `unsat`, and its `sat` is soundness-anchored by the
/// mandatory ground-evaluator replay inside `axeyum-strings`.
fn apply_word_route(
    script: &mut Script,
    config: &SolverConfig,
    result: CheckResult,
) -> CheckResult {
    let CheckResult::Unknown(reason) = result else {
        return result;
    };
    // Clone the (Copy-element) problem so the immutable borrow of `word_problem`
    // ends before the `&mut arena` search call; leaves the side channel in place
    // for the incremental path's later queries.
    let Some((eqs, diseqs, syms)) = script.word_problem.as_ref().map(|wp| {
        (
            wp.equalities.clone(),
            wp.disequalities.clone(),
            wp.seq_symbols.clone(),
        )
    }) else {
        return CheckResult::Unknown(reason);
    };

    let budget = word_route_budget(config);
    match solve_word_equations(&mut script.arena, &eqs, &diseqs, &budget) {
        // A model that has already replayed against every equality/disequality
        // through the ground evaluator inside `axeyum-strings` (the trust anchor).
        SearchOutcome::Sat(assignment) => {
            let mut model = Model::new();
            for &sym in &syms {
                if let Some(value) = assignment.get(sym) {
                    model.set(sym, value);
                }
            }
            CheckResult::Sat(model)
        }
        // First-class `unknown`: keep the prior verdict, record the decline.
        SearchOutcome::Unknown { reason: word } => {
            let detail = if reason.detail.is_empty() {
                format!("word-equation route declined ({word})")
            } else {
                format!("{}; word-equation route declined ({word})", reason.detail)
            };
            CheckResult::Unknown(UnknownReason {
                kind: reason.kind,
                detail,
            })
        }
    }
}

/// The word-route [`SearchBudget`]: an absolute deadline from `config.timeout`
/// (native targets) plus the [`WORD_ROUTE_MAX_NODES`] node cap.
fn word_route_budget(config: &SolverConfig) -> SearchBudget {
    #[cfg(not(target_arch = "wasm32"))]
    {
        if let Some(t) = config.timeout
            && let Some(deadline) = std::time::Instant::now().checked_add(t)
        {
            return SearchBudget::with_deadline(WORD_ROUTE_MAX_NODES, deadline);
        }
        SearchBudget::new(WORD_ROUTE_MAX_NODES)
    }
    #[cfg(target_arch = "wasm32")]
    {
        let _ = config;
        SearchBudget::new(WORD_ROUTE_MAX_NODES)
    }
}

/// Decides a **word-first-fallback** [`Script`] (T-B.4d) by the word route alone.
///
/// The bounded ADR-0029 encoder declined this script *at parse* (a literal over
/// the length cap, a `str.++` over the width cap, …), so
/// [`Script::word_only_fallback`] is set and the flat assertion view is **empty**.
/// The empty view must never be handed to [`crate::solve`] — that would answer a
/// vacuous `sat` unrelated to the word problem. Instead the sat-only, replay-
/// checked [`apply_word_route`] is the sole decider, seeded from a synthetic
/// `unknown`. On a word-route decline the **original** bounded parse error is
/// reproduced as [`SolverError::Parse`], so a script that was `unsupported` before
/// this fallback existed never silently becomes a bare `unknown`/`sat`.
fn decide_word_only(
    script: &mut Script,
    config: &SolverConfig,
) -> Result<CheckResult, SolverError> {
    let base = CheckResult::Unknown(UnknownReason {
        kind: UnknownKind::Incomplete,
        detail: "word-first fallback: bounded string encoder declined at parse; deciding via \
                 the word-equation route (T-B.4d)"
            .to_owned(),
    });
    match apply_word_route(script, config, base) {
        result @ CheckResult::Sat(_) => Ok(result),
        // Decline (word route returned `unknown`, or has no `unsat` capability):
        // reproduce the original bounded parse error verbatim.
        _ => Err(SolverError::Parse(
            script.word_only_fallback.clone().unwrap_or_default(),
        )),
    }
}

/// Harness-parity surface (T-B.4d): decides a **word-first-fallback**
/// [`Script`] exactly as the `solve_smtlib` front door does — the sat-only,
/// replay-checked word route is the sole decider (the flat assertion view is
/// empty and must never be solved), and a decline reproduces the original
/// bounded parse error as [`SolverError::Parse`]. Exposed for `axeyum-bench`,
/// which otherwise classifies these scripts `unsupported` without ever
/// consulting the solver.
///
/// # Errors
///
/// Returns [`SolverError::Parse`] carrying the original bounded parse error
/// whenever the word route declines — the caller sees exactly what it would
/// have seen before the fallback existed.
pub fn decide_word_only_script(
    script: &mut Script,
    config: &SolverConfig,
) -> Result<CheckResult, SolverError> {
    decide_word_only(script, config)
}

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

/// A Rust-facing result for SMT-LIB `(get-model)`.
///
/// Constants and functions are reported in user declaration order. Values are
/// Axeyum IR values, not textual SMT-LIB terms; this avoids pretending the
/// front-end can already render every lowered theory value back into canonical
/// SMT-LIB syntax. Textual command-session rendering is a later P4.4 step.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct SmtLibModel {
    /// User-declared 0-ary constants and their model values.
    pub constants: Vec<(String, Value)>,
    /// User-declared n-ary uninterpreted functions and their finite
    /// interpretations.
    pub functions: Vec<(String, FuncValue)>,
}

#[derive(Debug, Clone)]
struct SmtLibSingleQuery {
    assertions: Vec<TermId>,
    assertion_names: Vec<Option<String>>,
}

/// The bounded-string `unsat` gate (P2.7 A.2), extracted from a parsed
/// [`Script`] so it can be applied per `check-sat` alongside a disjoint
/// `&mut script.arena` borrow.
///
/// ADR-0029's contract is "strings up to `max_len` decide soundly; longer ones
/// are `Unsupported`, never wrong" — but an `unsat` of the *lowered* query is a
/// priori only `unsat` **within the encoding bound**: the packed representation
/// asserts `len(s) ≤ max_len` as an encoding artifact, while in the real
/// (unbounded) string theory a longer witness may exist (e.g. `(= (str.len s)
/// 9)` with `STRING_MAX_LEN = 8` is `sat`). [`StringGate::confirm`] keeps an
/// `unsat` only when it is provably bound-independent.
struct StringGate {
    /// The script used the bounded string/sequence encoding at all.
    active: bool,
    /// `original → abstraction` rewrite pairs ([`Script::len_abstraction_map`]).
    map: HashMap<TermId, TermId>,
    /// Universally-true abstraction side facts ([`Script::len_abstraction_facts`]).
    facts: Vec<TermId>,
    /// Encoding-bound facts ([`Script::len_abstraction_bounds`]) — bite-detector
    /// input only, never part of the sound abstraction.
    bounds: Vec<TermId>,
    /// A coarsely-abstracted atom (`str.<`/`str.<=`/`str.in_re`) is present:
    /// the length abstraction may miss a bound bite, so only a step-1-confirmed
    /// `unsat` may pass ([`Script::len_abstraction_coarse`]).
    coarse: bool,
}

impl StringGate {
    fn from_script(script: &Script) -> Self {
        StringGate {
            active: script.uses_bounded_strings,
            map: script.len_abstraction_map.iter().copied().collect(),
            facts: script.len_abstraction_facts.clone(),
            bounds: script.len_abstraction_bounds.clone(),
            coarse: script.len_abstraction_coarse,
        }
    }

    /// Decides `assertions`, downgrading a bound-suspect `unsat` to `unknown`:
    ///
    /// 1. **Unbounded length abstraction**: rewrite the active assertions
    ///    through the abstraction map (string atoms → `fresh_bool ∧ implied
    ///    length fact`; `str.len`-bridges → shared unbounded length variables)
    ///    plus the side facts, and re-decide. The rewritten query carries *no*
    ///    encoding bound and is a relaxation of the real string semantics, so
    ///    its `unsat` transfers — the bounded `unsat` is confirmed.
    /// 2. **Content-driven check**: relax every integer atom crossing the BV→Int
    ///    bridge (`bv2nat`) to a fresh Boolean and re-decide. Still-`unsat`
    ///    means the refutation never needed the bound-suspect integer channel —
    ///    the verdict surface predating the `bv2nat` blast (whose residual
    ///    pure-BV bound-bite class is tracked separately as the ADR-0029
    ///    contract-repair follow-up).
    /// 3. Otherwise the refutation leaned on the integer channel in a way the
    ///    unbounded abstraction cannot confirm — report an honest `unknown`.
    fn confirm(
        &self,
        arena: &mut TermArena,
        assertions: &[TermId],
        config: &SolverConfig,
        result: CheckResult,
    ) -> Result<CheckResult, SolverError> {
        if !self.active || !matches!(result, CheckResult::Unsat) {
            return Ok(result);
        }
        // Quantifier guard: the abstraction map replaces *atoms*, and an atom
        // inside a quantifier body may depend on the bound variable — a single
        // fresh Boolean cannot represent it for every instantiation, so the
        // rewritten query would not be a relaxation. Skip the abstraction-based
        // steps (1/1.5) and fall through to the wholesale atom relaxation of
        // step 2, which never descends into a quantifier.
        let has_quantifier = {
            let mut seen: std::collections::HashSet<TermId> = std::collections::HashSet::new();
            let mut stack: Vec<TermId> = assertions.to_vec();
            let mut found = false;
            while let Some(t) = stack.pop() {
                if !seen.insert(t) {
                    continue;
                }
                if let TermNode::App { op, args } = arena.node(t) {
                    if matches!(op, Op::Forall(_) | Op::Exists(_)) {
                        found = true;
                        break;
                    }
                    stack.extend(args.iter().copied());
                }
            }
            found
        };
        // Step 1 — the unbounded length abstraction refutes?
        if !has_quantifier && !self.map.is_empty() {
            let mut memo: HashMap<TermId, TermId> = HashMap::new();
            let mut abstracted_assertions = Vec::with_capacity(assertions.len());
            for &a in assertions {
                abstracted_assertions.push(
                    axeyum_rewrite::replace_subterms(arena, a, &self.map, &mut memo)
                        .map_err(|e| SolverError::Backend(e.to_string()))?,
                );
            }
            let mut abstracted = Vec::with_capacity(abstracted_assertions.len() + self.facts.len());
            abstracted.extend(abstracted_assertions.iter().copied());
            abstracted.extend(self.facts.iter().copied());
            let full = solve(arena, &abstracted, config)?;
            if matches!(full, CheckResult::Unsat) {
                return Ok(CheckResult::Unsat);
            }
            // Step 1a — the LIA length **projection**. The bounded encoding emits
            // per-string-variable well-formedness constraints (padding above the
            // length field is zero) that pass through the abstraction as pure
            // bit-vectors; mixed with the length facts' `Int` atoms they defeat the
            // exact refuters (a free `BitVec` forces the sat-only bounded-integer
            // path, which returns `unknown` rather than the true `unsat` — e.g.
            // `xx = xx ++ yy ∧ len(yy) > len(xx)`). Dropping every abstracted
            // assertion that carries no `Int` subterm is a **sound weakening**:
            // removing constraints only *adds* models, so an `unsat` of the subset
            // still implies the full abstraction (hence the real theory) is
            // `unsat`. The kept subset is pure Bool+LIA, which the length refuters
            // decide. Only worth trying when the full solve was undecided (a `sat`
            // full abstraction can never yield an `unsat` subset).
            if matches!(full, CheckResult::Unknown(_)) {
                let mut projected: Vec<TermId> = abstracted_assertions
                    .iter()
                    .copied()
                    .filter(|&a| mentions_int_sort(arena, a))
                    .collect();
                if projected.len() < abstracted_assertions.len() {
                    projected.extend(self.facts.iter().copied());
                    if matches!(solve(arena, &projected, config)?, CheckResult::Unsat) {
                        return Ok(CheckResult::Unsat);
                    }
                }
            }
            // Step 1.5 — bound-bite detector: the same length system WITH the
            // encoding bounds (`len(v) ≤ max_len`) being unsatisfiable — while
            // step 1 could not refute it unbounded — proves the recorded length
            // facts force some length past the encoding bound. The bounded
            // `unsat` is then an artifact of the encoding (a real model may use
            // longer strings), so downgrade. A downgrade is always sound.
            if !self.bounds.is_empty() {
                let mut with_bounds = abstracted;
                with_bounds.extend(self.bounds.iter().copied());
                if matches!(solve(arena, &with_bounds, config)?, CheckResult::Unsat) {
                    return Ok(CheckResult::Unknown(UnknownReason {
                        kind: UnknownKind::Incomplete,
                        detail: "bounded-string unsat is an encoding-bound artifact: the                                  recorded length facts force a length past the bound                                  (P2.7 A.2 bite detector)"
                            .to_owned(),
                    }));
                }
            }
        }
        // A coarsely-abstracted atom (`str.<`, `str.in_re`) means the length
        // abstraction can miss a bound bite (a real model may exist only past
        // the bound while every recorded fact fits within it — e.g.
        // `"aaaaaaaa" < s < "aaaaaaab"` needs `len(s) ≥ 9` with no length fact
        // saying so). Only the step-1 confirmation is sound then.
        if self.coarse {
            return Ok(CheckResult::Unknown(UnknownReason {
                kind: UnknownKind::Incomplete,
                detail: "bounded-string unsat with a coarsely-abstracted atom \
                         (str.</str.<=/str.in_re); not confirmed bound-independent \
                         (P2.7 A.2)"
                    .to_owned(),
            }));
        }
        // Step 2 — content-driven (no integer channel needed)?
        match relax_bridge_atoms(arena, assertions)? {
            None => Ok(CheckResult::Unsat),
            Some(relaxed) => {
                if matches!(solve(arena, &relaxed, config)?, CheckResult::Unsat) {
                    return Ok(CheckResult::Unsat);
                }
                Ok(CheckResult::Unknown(UnknownReason {
                    kind: UnknownKind::Incomplete,
                    detail: "bounded-string unsat within the encoding bound; not confirmed \
                             bound-independent by the unbounded length abstraction (P2.7 A.2)"
                        .to_owned(),
                }))
            }
        }
    }
}

/// Applies the bounded-string `unsat` gate (P2.7 A.2 / ADR-0052) to a verdict
/// obtained by solving a parsed [`Script`]'s (possibly rewritten) assertions
/// directly — for harnesses (e.g. `axeyum-bench`) that bypass [`solve_smtlib`]
/// and call [`crate::solve`] on `script.arena` themselves. A non-`unsat`
/// verdict and a string-free script pass through unchanged; a bounded-string
/// `unsat` is confirmed bound-independent or downgraded to an honest
/// `unknown`, exactly as at the [`solve_smtlib`] front door.
///
/// # Errors
///
/// Any [`SolverError`] from the confirmation solves.
pub fn confirm_bounded_string_verdict(
    script: &mut Script,
    assertions: &[TermId],
    config: &SolverConfig,
    result: CheckResult,
) -> Result<CheckResult, SolverError> {
    let gate = StringGate::from_script(script);
    let confirmed = gate.confirm(&mut script.arena, assertions, config, result)?;
    // Word-equation second-chance route (ADR-0053, T-B.4b), same as the
    // `solve_smtlib` front door: adds `sat` only where the verdict is `unknown`.
    Ok(apply_word_route(script, config, confirmed))
}

/// Whether `t` has any `Int`-sorted subterm — used by the step-1a LIA
/// projection to keep only length-relevant abstracted assertions (the pure
/// bit-vector well-formedness constraints, which carry no `Int`, are dropped;
/// see the projection comment for the soundness argument).
fn mentions_int_sort(arena: &TermArena, t: TermId) -> bool {
    fn go(arena: &TermArena, t: TermId, memo: &mut HashMap<TermId, bool>) -> bool {
        if let Some(&b) = memo.get(&t) {
            return b;
        }
        let b = arena.sort_of(t) == Sort::Int
            || match arena.node(t) {
                TermNode::App { args, .. } => {
                    let args = args.clone();
                    args.iter().any(|&a| go(arena, a, memo))
                }
                _ => false,
            };
        memo.insert(t, b);
        b
    }
    go(arena, t, &mut HashMap::new())
}

/// Replaces every Boolean atom whose subtree crosses the BV→Int bridge
/// (`bv2nat`) with a fresh Boolean variable, recursing only through the pure
/// propositional connectives. Returns `Ok(None)` when no assertion contains a
/// bridge (nothing to relax). The result is a **relaxation**: a model of the
/// original extends by assigning each fresh Boolean its atom's truth value, so
/// `unsat` of the relaxed query implies `unsat` of the original.
fn relax_bridge_atoms(
    arena: &mut TermArena,
    assertions: &[TermId],
) -> Result<Option<Vec<TermId>>, SolverError> {
    fn has_bridge(arena: &TermArena, t: TermId, memo: &mut HashMap<TermId, bool>) -> bool {
        if let Some(&b) = memo.get(&t) {
            return b;
        }
        let b = match arena.node(t) {
            TermNode::App { op, args } => {
                matches!(op, Op::Bv2Nat) || {
                    let args = args.clone();
                    args.iter().any(|&a| has_bridge(arena, a, memo))
                }
            }
            _ => false,
        };
        memo.insert(t, b);
        b
    }

    fn relax(
        arena: &mut TermArena,
        t: TermId,
        bridge_memo: &mut HashMap<TermId, bool>,
        memo: &mut HashMap<TermId, TermId>,
        fresh: &mut u32,
        changed: &mut bool,
    ) -> Result<TermId, SolverError> {
        if let Some(&r) = memo.get(&t) {
            return Ok(r);
        }
        if !has_bridge(arena, t, bridge_memo) {
            memo.insert(t, t);
            return Ok(t);
        }
        let err = |e: axeyum_ir::IrError| SolverError::Backend(e.to_string());
        let node = arena.node(t).clone();
        let out = match node {
            TermNode::App { op, args }
                if matches!(
                    op,
                    Op::BoolNot | Op::BoolAnd | Op::BoolOr | Op::BoolXor | Op::BoolImplies
                ) || (matches!(op, Op::Ite | Op::Eq)
                    && arena.sort_of(args[args.len() - 1]) == Sort::Bool) =>
            {
                let mut new_args = Vec::with_capacity(args.len());
                for &a in &args {
                    new_args.push(relax(arena, a, bridge_memo, memo, fresh, changed)?);
                }
                axeyum_rewrite::build_app(arena, op, &new_args).map_err(err)?
            }
            // Any other Boolean node containing a bridge (an Int comparison,
            // a quantifier, …) becomes a fresh, unconstrained Boolean.
            _ => {
                let n = *fresh;
                *fresh += 1;
                let sym = arena
                    .declare(&format!("!strgate.{n}"), Sort::Bool)
                    .map_err(err)?;
                *changed = true;
                arena.var(sym)
            }
        };
        memo.insert(t, out);
        Ok(out)
    }

    let mut bridge_memo = HashMap::new();
    if !assertions
        .iter()
        .any(|&a| has_bridge(arena, a, &mut bridge_memo))
    {
        return Ok(None);
    }
    let mut memo = HashMap::new();
    let mut fresh = 0u32;
    let mut changed = false;
    let mut out = Vec::with_capacity(assertions.len());
    for &a in assertions {
        out.push(relax(
            arena,
            a,
            &mut bridge_memo,
            &mut memo,
            &mut fresh,
            &mut changed,
        )?);
    }
    Ok(Some(out))
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
            ScriptCommand::GetAssertions => {}
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
    // Word-first parse fallback (T-B.4d): the bounded encoder declined this script
    // at parse, so decide it by the word route alone — never solve its (empty) flat
    // assertion view.
    if script.word_only_fallback.is_some() {
        let result = decide_word_only(&mut script, config)?;
        return Ok(SmtLibOutcome {
            result,
            logic: script.logic,
            expected_status: script.status,
        });
    }
    let query = smtlib_single_query(&script)?;
    let gate = StringGate::from_script(&script);
    let result = solve(&mut script.arena, &query.assertions, config)?;
    let result = gate.confirm(&mut script.arena, &query.assertions, config, result)?;
    // Word-equation second-chance route (ADR-0053, T-B.4b): may only add `sat`
    // where the bounded path + gate left an `unknown`.
    let result = apply_word_route(&mut script, config, result);
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

/// Evaluates active top-level `:named` assertions for an SMT-LIB
/// `(get-assignment)` query.
///
/// For a `sat` single-query script, this returns `(name, value)` pairs for the
/// active top-level assertions annotated as `(! t :named name)`, in active
/// assertion order after honoring `push`/`pop`, `check-sat-assuming`, and
/// `reset-assertions`. Popped names are not reported. Returns `Ok(None)` when
/// the script is `unsat`/`unknown` or has no active named assertions. Nested
/// named subterms are currently aliases for parsing; this helper reports the
/// top-level assertion assignments used by common SMT-LIB drivers.
///
/// # Errors
///
/// [`SolverError::Parse`] for malformed/unsupported text, any [`SolverError`]
/// from [`crate::solve`], or [`SolverError::Backend`] if a named assertion fails
/// to evaluate under a returned model.
pub fn solve_smtlib_get_assignment(
    input: &str,
    config: &SolverConfig,
) -> Result<Option<Vec<(String, bool)>>, SolverError> {
    let mut script = parse_script(input).map_err(|error| SolverError::Parse(error.to_string()))?;
    let query = smtlib_single_query(&script)?;
    let CheckResult::Sat(model) = solve(&mut script.arena, &query.assertions, config)? else {
        return Ok(None);
    };
    let assignment = model.to_assignment();
    let mut values = Vec::new();
    for (&term, name) in query.assertions.iter().zip(&query.assertion_names) {
        let Some(name) = name else {
            continue;
        };
        let value = axeyum_ir::eval(&script.arena, term, &assignment)
            .map_err(|e| SolverError::Backend(format!("get-assignment evaluation failed: {e}")))?;
        match value {
            Value::Bool(value) => values.push((name.clone(), value)),
            other => {
                return Err(SolverError::Backend(format!(
                    "get-assignment named assertion `{name}` evaluated to non-Bool value {other:?}"
                )));
            }
        }
    }
    if values.is_empty() {
        Ok(None)
    } else {
        Ok(Some(values))
    }
}

/// Returns scoped assertion-stack snapshots requested by SMT-LIB
/// `(get-assertions)` commands.
///
/// Each snapshot is rendered in SMT-LIB-style text at the exact command point,
/// after honoring prior `assert`, `push`, `pop`, and `reset-assertions`
/// commands. One-shot `check-sat-assuming` assumptions are intentionally not
/// retained in the assertion stack. Returns `Ok(None)` when the script requested
/// no assertion snapshots.
///
/// # Errors
///
/// [`SolverError::Parse`] for malformed/unsupported text.
pub fn solve_smtlib_get_assertions(
    input: &str,
    _config: &SolverConfig,
) -> Result<Option<Vec<Vec<String>>>, SolverError> {
    let script = parse_script(input).map_err(|error| SolverError::Parse(error.to_string()))?;
    let mut stack = Vec::<TermId>::new();
    let mut scopes = Vec::<usize>::new();
    let mut snapshots = Vec::new();
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
            ScriptCommand::ResetAssertions => {
                stack.clear();
                scopes.clear();
            }
            ScriptCommand::CheckSat | ScriptCommand::CheckSatAssuming(_) => {}
            ScriptCommand::GetAssertions => {
                snapshots.push(
                    stack
                        .iter()
                        .map(|&term| render(&script.arena, term))
                        .collect(),
                );
            }
        }
    }
    if snapshots.is_empty() {
        Ok(None)
    } else {
        Ok(Some(snapshots))
    }
}

/// Answers recorded SMT-LIB `(get-info :key)` queries.
///
/// The parser preserves `(set-info :key value)` metadata and requested
/// `(get-info :key)` commands. This helper returns one `(key, value)` row per
/// request, in script order. Recorded `set-info` values are returned verbatim;
/// `:name` and `:version` have axeyum defaults when the script did not set them.
/// `:reason-unknown` is computed only when requested: the single active query is
/// solved, and the backend's unknown reason is returned if the result is
/// `unknown`; otherwise it returns the empty SMT-LIB string literal. Unknown
/// info keys return `unsupported` rather than being silently dropped.
///
/// # Errors
///
/// [`SolverError::Parse`] for malformed/unsupported text, or any [`SolverError`]
/// from solving the active query for `:reason-unknown`.
pub fn solve_smtlib_get_info(
    input: &str,
    config: &SolverConfig,
) -> Result<Option<Vec<(String, String)>>, SolverError> {
    let mut script = parse_script(input).map_err(|error| SolverError::Parse(error.to_string()))?;
    if script.get_info_keys.is_empty() {
        return Ok(None);
    }

    let mut reason_unknown = None;
    if script
        .get_info_keys
        .iter()
        .any(|key| key == ":reason-unknown")
    {
        let query = smtlib_single_query(&script)?;
        let gate = StringGate::from_script(&script);
        let solved = solve(&mut script.arena, &query.assertions, config)?;
        let solved = gate.confirm(&mut script.arena, &query.assertions, config, solved)?;
        let solved = apply_word_route(&mut script, config, solved);
        reason_unknown = Some(match solved {
            CheckResult::Unknown(reason) if reason.detail.is_empty() => {
                format!("{:?}", reason.kind)
            }
            CheckResult::Unknown(reason) => reason.detail,
            CheckResult::Sat(_) | CheckResult::Unsat => "\"\"".to_owned(),
        });
    }

    let values = script
        .get_info_keys
        .iter()
        .map(|key| {
            let value = match key.as_str() {
                ":name" => script
                    .infos
                    .get(key)
                    .cloned()
                    .unwrap_or_else(|| "\"axeyum\"".to_owned()),
                ":version" => script
                    .infos
                    .get(key)
                    .cloned()
                    .unwrap_or_else(|| format!("\"{}\"", env!("CARGO_PKG_VERSION"))),
                ":reason-unknown" => reason_unknown.clone().unwrap_or_else(|| "\"\"".to_owned()),
                _ => script
                    .infos
                    .get(key)
                    .cloned()
                    .unwrap_or_else(|| "unsupported".to_owned()),
            };
            (key.clone(), value)
        })
        .collect();
    Ok(Some(values))
}

/// Answers recorded SMT-LIB `(get-option :key)` queries.
///
/// The parser preserves `(set-option :key value)` updates and requested
/// `(get-option :key)` commands. This helper returns one `(key, value)` row per
/// request, in script order. Explicitly set options are returned verbatim; common
/// SMT-LIB options have conservative defaults when the script did not set them.
/// Unknown options return `unsupported` rather than being silently dropped.
///
/// This is a command-surface helper only: not every standard option has full
/// semantic impact on the solver yet. For example, proof/model-producing helpers
/// are still explicit Rust APIs, while this function exposes the option state a
/// driver would observe.
///
/// # Errors
///
/// [`SolverError::Parse`] for malformed/unsupported text.
pub fn solve_smtlib_get_option(
    input: &str,
    _config: &SolverConfig,
) -> Result<Option<Vec<(String, String)>>, SolverError> {
    let script = parse_script(input).map_err(|error| SolverError::Parse(error.to_string()))?;
    if script.get_option_keys.is_empty() {
        return Ok(None);
    }

    let values = script
        .get_option_keys
        .iter()
        .map(|key| {
            let value = script
                .options
                .get(key)
                .cloned()
                .or_else(|| smtlib_option_default(key).map(str::to_owned))
                .unwrap_or_else(|| "unsupported".to_owned());
            (key.clone(), value)
        })
        .collect();
    Ok(Some(values))
}

fn smtlib_option_default(key: &str) -> Option<&'static str> {
    match key {
        ":diagnostic-output-channel" => Some("\"stderr\""),
        ":global-declarations"
        | ":print-success"
        | ":produce-assignments"
        | ":produce-models"
        | ":produce-proofs"
        | ":produce-unsat-assumptions"
        | ":produce-unsat-cores" => Some("false"),
        ":random-seed" | ":reproducible-resource-limit" | ":verbosity" => Some("0"),
        ":regular-output-channel" => Some("\"stdout\""),
        _ => None,
    }
}

/// Returns the model requested by an SMT-LIB `(get-model)` command.
///
/// For a `sat` single-query script that requested `(get-model)`, this returns
/// user-declared constants and interpreted functions in declaration order.
/// Quantifier locals, definitions/macros, and parser-internal lowering details
/// are not reported. Returns `Ok(None)` when no model was requested or the query
/// is `unsat`/`unknown`.
///
/// The helper returns [`Value`]s and [`FuncValue`]s rather than SMT-LIB text; a
/// full interactive command renderer is tracked separately under P4.4.
///
/// # Errors
///
/// [`SolverError::Parse`] for malformed/unsupported text, any [`SolverError`]
/// from [`crate::solve`], or [`SolverError::Backend`] if a sat model omits a
/// declared constant whose sort has no well-founded default.
pub fn solve_smtlib_get_model(
    input: &str,
    config: &SolverConfig,
) -> Result<Option<SmtLibModel>, SolverError> {
    let mut script = parse_script(input).map_err(|error| SolverError::Parse(error.to_string()))?;
    if !script.get_model {
        return Ok(None);
    }
    let query = smtlib_single_query(&script)?;
    let CheckResult::Sat(model) = solve(&mut script.arena, &query.assertions, config)? else {
        return Ok(None);
    };

    let constants = script
        .model_symbols
        .iter()
        .map(|&symbol| {
            let (name, sort) = script.arena.symbol(symbol);
            let value = model
                .get(symbol)
                .or_else(|| well_founded_default(&script.arena, sort));
            let Some(value) = value else {
                return Err(SolverError::Backend(format!(
                    "get-model could not complete symbol `{name}` of sort {sort:?}"
                )));
            };
            Ok((name.to_owned(), value))
        })
        .collect::<Result<Vec<_>, SolverError>>()?;
    let functions = script
        .model_functions
        .iter()
        .filter_map(|&func| {
            model.function(func).map(|value| {
                let (name, _params, _result) = script.arena.function(func);
                (name.to_owned(), value.clone())
            })
        })
        .collect();
    Ok(Some(SmtLibModel {
        constants,
        functions,
    }))
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
    // Bounded-string gate (P2.7 A.2): a core is only meaningful for a
    // bound-independent `unsat`, so confirm the verdict first.
    let gate = StringGate::from_script(&script);
    if gate.active {
        let result = solve(&mut script.arena, &query.assertions, config)?;
        if !matches!(
            gate.confirm(&mut script.arena, &query.assertions, config, result)?,
            CheckResult::Unsat
        ) {
            return Ok(None);
        }
    }
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
    config: &SolverConfig,
) -> Result<Option<String>, SolverError> {
    let mut script = parse_script(input).map_err(|error| SolverError::Parse(error.to_string()))?;
    let query = smtlib_single_query(&script)?;
    // Bounded-string gate (P2.7 A.2): a proof of the *lowered* (bounded) query
    // is not a proof for the script unless the `unsat` is bound-independent —
    // confirm before emitting (e.g. a bit-blast refutation of `len(s) = 9`
    // against the encoding bound proves nothing about the real string theory).
    let gate = StringGate::from_script(&script);
    if gate.active {
        let result = solve(&mut script.arena, &query.assertions, config)?;
        if !matches!(
            gate.confirm(&mut script.arena, &query.assertions, config, result)?,
            CheckResult::Unsat
        ) {
            return Ok(None);
        }
    }
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
    // Word-first parse fallback (T-B.4d): a word-only script is non-incremental by
    // construction (`build_word_problem` declines push/pop/check-sat-assuming), so
    // it has exactly one implicit `check-sat`. Decide it by the word route alone.
    if script.word_only_fallback.is_some() {
        return Ok(vec![decide_word_only(&mut script, config)?]);
    }
    let gate = StringGate::from_script(&script);
    let mut stack: Vec<axeyum_ir::TermId> = Vec::new();
    let mut scopes: Vec<usize> = Vec::new(); // assertion-stack depth at each open push
    let mut results = Vec::new();
    // Clone the command stream so the per-`check-sat` word route can take
    // `&mut script` (arena + word-problem side channel) without holding a borrow
    // of `script.commands` across the loop body.
    let commands = script.commands.clone();
    for command in &commands {
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
                let result = solve(&mut script.arena, &stack, config)?;
                let result = gate.confirm(&mut script.arena, &stack, config, result)?;
                results.push(apply_word_route(&mut script, config, result));
            }
            ScriptCommand::CheckSatAssuming(assumptions) => {
                // Decide the active assertions together with the assumptions, but
                // do not retain them: solve a temporary stack, then discard.
                let mut with = stack.clone();
                with.extend_from_slice(assumptions);
                let result = solve(&mut script.arena, &with, config)?;
                let result = gate.confirm(&mut script.arena, &with, config, result)?;
                // The word-problem side channel is `None` whenever the script
                // uses `check-sat-assuming` (see `build_word_problem`), so this is
                // a plain pass-through here; kept uniform with the other queries.
                results.push(apply_word_route(&mut script, config, result));
            }
            ScriptCommand::ResetAssertions => {
                // Remove all assertions and open scopes (declarations stay interned
                // in the arena). Subsequent `check-sat`s see only assertions made
                // after the reset — the SMT-LIB `reset-assertions` semantics.
                stack.clear();
                scopes.clear();
            }
            ScriptCommand::GetAssertions => {}
        }
    }
    Ok(results)
}
