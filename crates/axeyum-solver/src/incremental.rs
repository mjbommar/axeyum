//! End-to-end incremental bit-vector solver (ADR-0009 stage 2).
//!
//! [`IncrementalBvSolver`] is the symbolic-execution-shaped front end the
//! `Solver` façade pointed at: `assert` / `push` / `pop` / `check` /
//! `check_assuming` over a *warm* engine. Each asserted term is bit-blasted into
//! a persistent AIG ([`axeyum_bv::IncrementalLowering`]) and Tseitin-encoded
//! into a persistent CNF over a warm SAT solver
//! ([`axeyum_cnf::IncrementalCnf`]); shared subterms across queries are lowered
//! once and the SAT solver keeps its learned clauses. Scopes are compiled to
//! selector (assumption) literals, so `pop` deactivates a frame's assertions
//! without rebuilding anything.
//!
//! Soundness is preserved exactly as in the one-shot backend: a `sat`
//! assignment is lifted (CNF → AIG node values → Axeyum symbols) through the
//! same shared reconstruction, then **replayed against the original asserted
//! terms** with the ground evaluator before being returned.

use axeyum_bv::{BitLowerError, IncrementalLowering, first_unsupported_op};
use axeyum_cnf::{CnfVar, IncrementalCnf, SatError, SatResult};
use axeyum_ir::{
    Assignment, IrError, Sort, SymbolId, TermArena, TermId, Value, eval, well_founded_default,
};

use crate::backend::{CheckResult, SolverConfig, SolverError, UnknownKind, UnknownReason};
use crate::model::Model;

/// Outcome of [`IncrementalBvSolver::check_assuming_core`]: like a
/// [`CheckResult`], but the `unsat` case carries the **assumption core**.
#[derive(Debug, Clone)]
pub enum AssumptionOutcome {
    /// Satisfiable, with a replay-checked model.
    Sat(Model),
    /// Unsatisfiable. `core` is the subset of the passed assumptions already
    /// jointly inconsistent with the active assertions (a sound, often minimal,
    /// blocking set; its negation is a sound conflict clause for path pruning).
    Unsat {
        /// The inconsistent assumption subset.
        core: Vec<TermId>,
    },
    /// Undecided, with the classified reason.
    Unknown(UnknownReason),
}

/// One push/pop frame: its activation selector (none for the permanent base
/// frame) and the terms asserted while it was the top frame.
#[derive(Debug)]
struct Frame {
    selector: Option<CnfVar>,
    assertions: Vec<TermId>,
}

/// A warm, incremental pure-Rust bit-vector solver.
///
/// Bound to a single [`TermArena`] over its lifetime (term IDs are arena-stable
/// and the persistent lowering reuses them). One-shot in spirit it is not: state
/// accumulates across [`IncrementalBvSolver::check`] calls.
#[derive(Debug)]
pub struct IncrementalBvSolver {
    lowering: IncrementalLowering,
    cnf: IncrementalCnf,
    config: SolverConfig,
    frames: Vec<Frame>,
}

impl Default for IncrementalBvSolver {
    fn default() -> Self {
        Self::new()
    }
}

impl IncrementalBvSolver {
    /// Creates an empty incremental solver with the default configuration.
    pub fn new() -> Self {
        Self::with_config(SolverConfig::default())
    }

    /// Creates an empty incremental solver with an explicit configuration.
    ///
    /// Only the `timeout` field is consulted by this solver today; admission
    /// budgets are a one-shot-backend concern.
    pub fn with_config(config: SolverConfig) -> Self {
        Self {
            lowering: IncrementalLowering::new(),
            cnf: IncrementalCnf::new(),
            config,
            frames: vec![Frame {
                selector: None,
                assertions: Vec::new(),
            }],
        }
    }

    /// The number of currently open push scopes (excluding the base frame).
    pub fn scope_depth(&self) -> usize {
        self.frames.len() - 1
    }

    /// Total CNF clauses encoded so far across all queries on this warm solver.
    ///
    /// Because shared subterms bit-blast and encode exactly once, this grows far
    /// more slowly across related path queries than re-encoding each query from a
    /// cold solver would — the measurable incrementality win for the
    /// symbolic-execution consumer.
    pub fn encoded_clause_count(&self) -> usize {
        self.cnf.clause_count()
    }

    /// Total CNF variables (AIG nodes plus scope selectors) encoded so far.
    pub fn encoded_variable_count(&self) -> usize {
        self.cnf.variable_count()
    }

    /// Bit-blasts `term` and adds it to the current scope.
    ///
    /// The assertion is enforced while the current scope (and all enclosing
    /// scopes) remain open, and is dropped by the matching [`Self::pop`].
    ///
    /// # Errors
    ///
    /// Returns [`SolverError::NonBooleanAssertion`] if `term` is not Boolean,
    /// [`SolverError::Unsupported`] for constructs outside the lowering subset,
    /// or [`SolverError::Backend`] for an internal lowering/encoding failure.
    ///
    /// # Panics
    ///
    /// Does not panic in practice: the base frame is an invariant, so the
    /// current-frame lookups always succeed.
    pub fn assert(&mut self, arena: &TermArena, term: TermId) -> Result<(), SolverError> {
        if arena.sort_of(term) != Sort::Bool {
            return Err(SolverError::NonBooleanAssertion(term));
        }
        if let Some((unsupported, op)) = first_unsupported_op(arena, &[term]) {
            return Err(SolverError::Unsupported(format!(
                "term #{} uses unsupported pure-Rust BV operator {op:?}",
                unsupported.index()
            )));
        }
        let lowered = self.lowering.lower(arena, term).map_err(map_lower_error)?;
        let root = lowered.bits()[0];
        let selector = self
            .frames
            .last()
            .expect("base frame always present")
            .selector;
        self.cnf
            .assert_root(self.lowering.aig(), root, selector)
            .map_err(|error| map_sat_error(&error))?;
        self.frames
            .last_mut()
            .expect("base frame always present")
            .assertions
            .push(term);
        Ok(())
    }

    /// Opens a new scope; assertions added afterwards are removed by the
    /// matching [`Self::pop`].
    ///
    /// # Errors
    ///
    /// Returns [`SolverError::Backend`] if a selector variable cannot be
    /// allocated.
    pub fn push(&mut self) -> Result<(), SolverError> {
        let selector = self
            .cnf
            .fresh_selector()
            .map_err(|error| map_sat_error(&error))?;
        self.frames.push(Frame {
            selector: Some(selector),
            assertions: Vec::new(),
        });
        Ok(())
    }

    /// Closes the most recent scope. Returns `false` if only the base frame
    /// remained (nothing to pop).
    pub fn pop(&mut self) -> bool {
        if self.frames.len() > 1 {
            self.frames.pop();
            true
        } else {
            false
        }
    }

    /// Checks satisfiability of the currently active assertions.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError::Backend`] for an adapter or lift failure.
    pub fn check(&mut self, arena: &TermArena) -> Result<CheckResult, SolverError> {
        Ok(self.solve_with_extra(arena, &[])?.0)
    }

    /// Checks the active assertions together with one-shot `assumptions`, which
    /// hold only for this check (SMT-LIB `check-sat-assuming`).
    ///
    /// # Errors
    ///
    /// Returns the same errors as [`Self::assert`] (for the assumptions) and
    /// [`Self::check`].
    pub fn check_assuming(
        &mut self,
        arena: &TermArena,
        assumptions: &[TermId],
    ) -> Result<CheckResult, SolverError> {
        Ok(self.solve_with_extra(arena, assumptions)?.0)
    }

    /// Like [`Self::check_assuming`], but on `unsat` also returns the
    /// **assumption core**: the subset of `assumptions` already jointly
    /// inconsistent with the active assertions. The rest of the assumptions are
    /// irrelevant to the contradiction.
    ///
    /// This is the path-pruning primitive for **symbolic execution and
    /// reachability**: feed candidate branch conditions as `assumptions`; an
    /// `Unsat { core }` says the conditions in `core` cannot co-occur on this
    /// path prefix, so the whole sub-tree under that combination is infeasible
    /// and can be pruned (and the negated core is a sound blocking clause).
    ///
    /// The core is sound by construction (the SAT solver's final conflict is
    /// entailed); when the adapter returns none, the full assumption set — always
    /// a sound core — is returned instead.
    ///
    /// # Errors
    ///
    /// Returns the same errors as [`Self::check_assuming`].
    pub fn check_assuming_core(
        &mut self,
        arena: &TermArena,
        assumptions: &[TermId],
    ) -> Result<AssumptionOutcome, SolverError> {
        let (result, core) = self.solve_with_extra(arena, assumptions)?;
        Ok(match result {
            CheckResult::Sat(model) => AssumptionOutcome::Sat(model),
            CheckResult::Unsat => AssumptionOutcome::Unsat { core },
            CheckResult::Unknown(reason) => AssumptionOutcome::Unknown(reason),
        })
    }

    /// Asserts a **blocking clause** excluding `model`'s assignment to `symbols`
    /// from future solutions: `⋁_s (s ≠ model[s])`. This is the
    /// **reachable-state / all-SAT enumeration** primitive for reachability
    /// analysis: repeatedly `check`, record the model, `block_model` it, and
    /// re-`check` until `unsat` — each iteration yields a *distinct* assignment
    /// over `symbols` (the set of reachable states/inputs, projected to
    /// `symbols`). Sound: the clause is a valid consequence asserted as a normal
    /// constraint, so models stay replay-checked.
    ///
    /// Symbols absent from the model are skipped; an empty effective clause (no
    /// listed symbol has a value) blocks everything (asserts `false`), ending
    /// enumeration.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError::Unsupported`] if a listed symbol's value is not a
    /// `Bool`/`BitVec` (the incremental engine's sorts), or [`SolverError`] from
    /// the builders / [`Self::assert`].
    pub fn block_model(
        &mut self,
        arena: &mut TermArena,
        model: &Model,
        symbols: &[SymbolId],
    ) -> Result<(), SolverError> {
        let mut disjuncts = Vec::new();
        for &symbol in symbols {
            let Some(value) = model.get(symbol) else {
                continue;
            };
            let var = arena.var(symbol);
            let literal = match value {
                Value::Bv { width, value } => {
                    let constant = arena.bv_const(width, value)?;
                    let equal = arena.eq(var, constant)?;
                    arena.not(equal)?
                }
                Value::Bool(b) => {
                    if b {
                        arena.not(var)?
                    } else {
                        var
                    }
                }
                other => {
                    return Err(SolverError::Unsupported(format!(
                        "block_model: symbol value {other:?} is not a Bool/BitVec"
                    )));
                }
            };
            disjuncts.push(literal);
        }
        let clause = match disjuncts.split_first() {
            None => arena.bool_const(false),
            Some((&first, rest)) => {
                let mut acc = first;
                for &disjunct in rest {
                    acc = arena.or(acc, disjunct)?;
                }
                acc
            }
        };
        self.assert(arena, clause)
    }

    /// Core solve. Returns the [`CheckResult`] and, on an `unsat` under
    /// assumptions, the subset of `assumptions` (as `TermId`s) the solver found
    /// sufficient for the contradiction — its final-conflict core, the
    /// path-pruning primitive. The core is empty for `sat`/`unknown` and for an
    /// assumption-free solve.
    fn solve_with_extra(
        &mut self,
        arena: &TermArena,
        assumptions: &[TermId],
    ) -> Result<(CheckResult, Vec<TermId>), SolverError> {
        // Encode each one-shot assumption guarded by an ephemeral selector that
        // is assumed only for this solve, so it does not persist as a hard
        // constraint after the check returns.
        let mut ephemeral = Vec::with_capacity(assumptions.len());
        for &term in assumptions {
            if arena.sort_of(term) != Sort::Bool {
                return Err(SolverError::NonBooleanAssertion(term));
            }
            if let Some((unsupported, op)) = first_unsupported_op(arena, &[term]) {
                return Err(SolverError::Unsupported(format!(
                    "term #{} uses unsupported pure-Rust BV operator {op:?}",
                    unsupported.index()
                )));
            }
            let lowered = self.lowering.lower(arena, term).map_err(map_lower_error)?;
            let root = lowered.bits()[0];
            let selector = self
                .cnf
                .fresh_selector()
                .map_err(|error| map_sat_error(&error))?;
            self.cnf
                .assert_root(self.lowering.aig(), root, Some(selector))
                .map_err(|error| map_sat_error(&error))?;
            ephemeral.push(selector);
        }

        let mut active = self
            .frames
            .iter()
            .filter_map(|frame| frame.selector)
            .collect::<Vec<_>>();
        active.extend_from_slice(&ephemeral);

        let result = self
            .cnf
            .solve(&active, self.config.timeout)
            .map_err(|error| map_sat_error(&error))?;

        match result {
            SatResult::Sat(cnf_assignment) => {
                let node_values = self
                    .cnf
                    .aig_node_values(self.lowering.aig(), &cnf_assignment);
                let reconstructed = self
                    .lowering
                    .assignment_from_aig_values(&node_values)
                    .map_err(map_lower_error)?;
                let model = complete_model(arena, &reconstructed);
                self.replay(arena, assumptions, &model)?;
                Ok((CheckResult::Sat(model), Vec::new()))
            }
            SatResult::Unsat(evidence) => {
                // Map the solver's failed-assumption selector literals back to the
                // source assumption terms (ephemeral[i] is the selector for
                // assumptions[i]). An empty core (e.g. unsat without assumptions,
                // or an adapter that returns none) is reported as the full set,
                // which is always a sound core.
                let mut core = Vec::new();
                for lit in &evidence.failed_assumptions {
                    if let Some(i) = ephemeral.iter().position(|&sel| sel == lit.var()) {
                        core.push(assumptions[i]);
                    }
                }
                if core.is_empty() && !assumptions.is_empty() {
                    core.extend_from_slice(assumptions);
                }
                Ok((CheckResult::Unsat, core))
            }
            SatResult::Unknown(reason) => {
                let kind = if reason.detail.contains("timeout") {
                    UnknownKind::Timeout
                } else {
                    UnknownKind::Other
                };
                Ok((
                    CheckResult::Unknown(UnknownReason {
                        kind,
                        detail: reason.detail,
                    }),
                    Vec::new(),
                ))
            }
        }
    }

    /// Replays the model against every active assertion plus the one-shot
    /// assumptions, the level-1 evidence check; a failure is a soundness bug.
    fn replay(
        &self,
        arena: &TermArena,
        assumptions: &[TermId],
        model: &Model,
    ) -> Result<(), SolverError> {
        let assignment = model.to_assignment();
        let active = self
            .frames
            .iter()
            .flat_map(|frame| frame.assertions.iter().copied());
        for term in active.chain(assumptions.iter().copied()) {
            match eval(arena, term, &assignment) {
                Ok(Value::Bool(true)) => {}
                Ok(Value::Bool(false)) => {
                    return Err(SolverError::Backend(format!(
                        "incremental sat model replay failed: term #{} evaluated to false",
                        term.index()
                    )));
                }
                Ok(value) => {
                    return Err(SolverError::Backend(format!(
                        "incremental sat model replay failed: term #{} evaluated to non-Boolean {value}",
                        term.index()
                    )));
                }
                Err(error) => {
                    return Err(SolverError::Backend(format!(
                        "incremental sat model replay failed: term #{} failed evaluation: {error}",
                        term.index()
                    )));
                }
            }
        }
        Ok(())
    }
}

fn complete_model(arena: &TermArena, assignment: &Assignment) -> Model {
    let mut model = Model::new();
    for (symbol, _name, sort) in arena.symbols() {
        // Unconstrained symbols get their sort's well-founded default; an
        // uninhabited datatype gets no entry (see the sat-bv backend's twin).
        let value = assignment
            .get(symbol)
            .or_else(|| well_founded_default(arena, sort));
        if let Some(value) = value {
            model.set(symbol, value);
        }
    }
    model
}

fn map_lower_error(error: BitLowerError) -> SolverError {
    match error {
        BitLowerError::UnsupportedOp { term, op } => SolverError::Unsupported(format!(
            "term #{} uses unsupported pure-Rust BV operator {op:?}",
            term.index()
        )),
        BitLowerError::Ir(IrError::InvalidWidth(width)) => SolverError::Unsupported(format!(
            "unsupported bit-vector width {width} in pure-Rust BV backend"
        )),
        other => SolverError::Backend(other.to_string()),
    }
}

fn map_sat_error(error: &SatError) -> SolverError {
    SolverError::Backend(error.to_string())
}
