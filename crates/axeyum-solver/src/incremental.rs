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
    Assignment, IrError, Op, Sort, SymbolId, TermArena, TermId, TermNode, Value, eval,
    well_founded_default,
};

use std::collections::{HashMap, HashSet};

use crate::backend::{CheckResult, SolverConfig, SolverError, UnknownKind, UnknownReason};
use crate::model::Model;

/// Whether `term` needs the deferred theory path instead of the warm
/// bit-blaster: arrays (`select`/`store`/array values) or uninterpreted function
/// applications. Such assertions are kept scoped in the incremental frames and
/// decided by [`IncrementalBvSolver::check_with_memory`] through the full
/// pure-Rust dispatcher.
fn needs_deferred_theory(arena: &TermArena, term: TermId) -> bool {
    let mut stack = vec![term];
    let mut seen = HashSet::new();
    while let Some(t) = stack.pop() {
        if !seen.insert(t) {
            continue;
        }
        if matches!(arena.sort_of(t), Sort::Array { .. }) {
            return true;
        }
        if let TermNode::App { op, args, .. } = arena.node(t) {
            if matches!(op, Op::Apply(_)) {
                return true;
            }
            stack.extend(args.iter().copied());
        }
    }
    false
}

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
    /// Array-free assertions, bit-blasted into the warm CNF.
    assertions: Vec<TermId>,
    /// Assertions involving arrays or uninterpreted functions. The warm
    /// bit-blaster does not encode these theory constructs, so they are scoped
    /// here and decided by [`IncrementalBvSolver::check_with_memory`] via the
    /// full dispatcher. Warm lazy theory incrementality is ADR-0030 future work.
    deferred_assertions: Vec<TermId>,
}

#[derive(Debug, Clone, Copy)]
struct OneShotAssumption {
    original: TermId,
    encoded: TermId,
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
                deferred_assertions: Vec::new(),
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

    /// Whether `term` contains array or uninterpreted-function structure that
    /// the warm BV bit-blaster intentionally defers to the full dispatcher.
    #[must_use]
    pub fn term_needs_deferred_theory(arena: &TermArena, term: TermId) -> bool {
        needs_deferred_theory(arena, term)
    }

    /// Whether any currently active assertion is being held for the deferred
    /// array/UF theory path.
    #[must_use]
    pub fn has_deferred_theory_assertions(&self) -> bool {
        self.frames
            .iter()
            .any(|frame| !frame.deferred_assertions.is_empty())
    }

    /// Simplifies the small memory fragment that is safe to encode on the warm
    /// BV path today.
    ///
    /// This is deliberately narrow: it folds syntactic read-over-write
    /// identities of the form `select(store(a, i, v), i)` to `v`, skips a store
    /// at a literal-distinct index (`select(store(a, c1, v), c2)` to
    /// `select(a, c2)` when `c1 != c2` is known from constants), and collapses
    /// reads from constant arrays to their default value. It recurses through
    /// ordinary wrappers, but does not instantiate symbolic distinct-index
    /// read-over-write cases, array extensionality, or UF lemmas.
    #[must_use]
    pub fn simplify_memory_for_warm_assertion(arena: &mut TermArena, term: TermId) -> TermId {
        let mut memo = HashMap::new();
        simplify_memory_for_warm_assertion_inner(arena, term, &mut memo)
    }

    /// Asserts `term`, first applying the small warm-safe memory simplifier.
    ///
    /// When simplification removes all array/UF structure, the simplified term
    /// is encoded into the warm BV solver while the original term is retained
    /// for replay. If unsupported array/UF structure remains, the original term
    /// is scoped as a deferred theory assertion exactly like [`Self::assert`].
    ///
    /// Returns the term actually presented to the warm/deferred classifier.
    ///
    /// # Errors
    ///
    /// Returns the same errors as [`Self::assert`].
    pub fn assert_simplifying_memory(
        &mut self,
        arena: &mut TermArena,
        term: TermId,
    ) -> Result<TermId, SolverError> {
        if arena.sort_of(term) != Sort::Bool {
            return Err(SolverError::NonBooleanAssertion(term));
        }
        let encoded = Self::simplify_memory_for_warm_assertion(arena, term);
        self.assert_encoded(arena, term, encoded)?;
        Ok(encoded)
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
        self.assert_encoded(arena, term, term)
    }

    fn assert_encoded(
        &mut self,
        arena: &TermArena,
        original: TermId,
        encoded: TermId,
    ) -> Result<(), SolverError> {
        if arena.sort_of(original) != Sort::Bool {
            return Err(SolverError::NonBooleanAssertion(original));
        }
        if arena.sort_of(encoded) != Sort::Bool {
            return Err(SolverError::Backend(format!(
                "memory simplification changed Boolean assertion #{} to non-Boolean term #{}",
                original.index(),
                encoded.index()
            )));
        }
        if needs_deferred_theory(arena, encoded) {
            // The warm bit-blaster does not encode arrays or UFs; defer this
            // assertion to `check_with_memory`, which decides it with all active
            // assertions through the full dispatcher. Scope is honored: it is
            // dropped by the matching `pop` with the rest of the frame.
            self.frames
                .last_mut()
                .expect("base frame always present")
                .deferred_assertions
                .push(original);
            return Ok(());
        }
        if let Some((unsupported, op)) = first_unsupported_op(arena, &[encoded]) {
            return Err(SolverError::Unsupported(format!(
                "term #{} uses unsupported pure-Rust BV operator {op:?}",
                unsupported.index()
            )));
        }
        let lowered = self
            .lowering
            .lower(arena, encoded)
            .map_err(map_lower_error)?;
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
            .push(original);
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
            deferred_assertions: Vec::new(),
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

    /// Decides the active assertions **including array/memory** (`select`/`store`)
    /// and uninterpreted-function applications — the symbolic-memory and
    /// keccak-as-UF capability symbolic execution needs. The first slice of
    /// ADR-0030: it re-solves all active assertions one-shot via the full
    /// pure-Rust dispatcher, so it does not yet reuse the warm CNF for deferred
    /// theory constructs (warm lazy arrays/UF are the follow-up). Requires
    /// `&mut` arena because theory reductions may introduce terms.
    ///
    /// Use this instead of [`Self::check`] whenever array or UF assertions are
    /// present (the warm `check` refuses them rather than ignore them). For
    /// array/UF-free queries it agrees with `check`, modulo the one-shot route.
    ///
    /// Soundness is unchanged: a `sat` model is replay-checked against the
    /// original `select`/`store` assertions by the ground evaluator.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError`] from the selected dispatcher route.
    pub fn check_with_memory(&mut self, arena: &mut TermArena) -> Result<CheckResult, SolverError> {
        let active = self.active_assertions();
        crate::check_auto(arena, &active, &self.config)
    }

    /// Checks the active assertions together with one-shot assumptions through
    /// the memory/theory-aware dispatcher. This is the branch-feasibility query
    /// for symbolic executors whose branch condition mentions arrays or UFs.
    ///
    /// Assumptions hold only for this call and are not retained.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError::NonBooleanAssertion`] if any assumption is not
    /// Boolean, or propagates a dispatcher error.
    pub fn check_assuming_with_memory(
        &mut self,
        arena: &mut TermArena,
        assumptions: &[TermId],
    ) -> Result<CheckResult, SolverError> {
        let active = self.active_assertions_with_assumptions(arena, assumptions)?;
        crate::check_auto(arena, &active, &self.config)
    }

    /// Like [`Self::check_assuming_with_memory`], but returns a sound assumption
    /// core on `unsat`.
    ///
    /// The one-shot dispatcher does not expose a final-conflict core, so the
    /// reported core is the full assumption set. This is intentionally coarse but
    /// sound: active assertions plus all listed assumptions are already
    /// inconsistent.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError::NonBooleanAssertion`] if any assumption is not
    /// Boolean, or propagates a dispatcher error.
    pub fn check_assuming_core_with_memory(
        &mut self,
        arena: &mut TermArena,
        assumptions: &[TermId],
    ) -> Result<AssumptionOutcome, SolverError> {
        let result = self.check_assuming_with_memory(arena, assumptions)?;
        Ok(match result {
            CheckResult::Sat(model) => AssumptionOutcome::Sat(model),
            CheckResult::Unsat => AssumptionOutcome::Unsat {
                core: assumptions.to_vec(),
            },
            CheckResult::Unknown(reason) => AssumptionOutcome::Unknown(reason),
        })
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

    /// Checks one-shot assumptions after applying the same narrow warm-safe
    /// memory simplification used by [`Self::assert_simplifying_memory`].
    ///
    /// This lets branch/fork queries over the narrow warm read-over-write slice
    /// stay on the warm BV path. The original assumptions are still replayed
    /// against any returned model and reported in any assumption core.
    ///
    /// # Errors
    ///
    /// Returns the same errors as [`Self::check_assuming`].
    pub fn check_assuming_simplifying_memory(
        &mut self,
        arena: &mut TermArena,
        assumptions: &[TermId],
    ) -> Result<CheckResult, SolverError> {
        let assumptions = Self::simplified_one_shot_assumptions(arena, assumptions)?;
        Ok(self.solve_with_encoded_extra(arena, &assumptions)?.0)
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

    /// Like [`Self::check_assuming_simplifying_memory`], but on `unsat` returns
    /// a core in terms of the original, unsimplified assumptions.
    ///
    /// # Errors
    ///
    /// Returns the same errors as [`Self::check_assuming_core`].
    pub fn check_assuming_core_simplifying_memory(
        &mut self,
        arena: &mut TermArena,
        assumptions: &[TermId],
    ) -> Result<AssumptionOutcome, SolverError> {
        let assumptions = Self::simplified_one_shot_assumptions(arena, assumptions)?;
        let (result, core) = self.solve_with_encoded_extra(arena, &assumptions)?;
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

    fn simplified_one_shot_assumptions(
        arena: &mut TermArena,
        assumptions: &[TermId],
    ) -> Result<Vec<OneShotAssumption>, SolverError> {
        assumptions
            .iter()
            .map(|&term| {
                if arena.sort_of(term) != Sort::Bool {
                    return Err(SolverError::NonBooleanAssertion(term));
                }
                Ok(OneShotAssumption {
                    original: term,
                    encoded: Self::simplify_memory_for_warm_assertion(arena, term),
                })
            })
            .collect()
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
        let assumptions = assumptions
            .iter()
            .map(|&term| OneShotAssumption {
                original: term,
                encoded: term,
            })
            .collect::<Vec<_>>();
        self.solve_with_encoded_extra(arena, &assumptions)
    }

    fn solve_with_encoded_extra(
        &mut self,
        arena: &TermArena,
        assumptions: &[OneShotAssumption],
    ) -> Result<(CheckResult, Vec<TermId>), SolverError> {
        // The warm path does not bit-blast arrays or UFs; if any deferred theory
        // assertion is active, refuse rather than silently ignore it (which would
        // risk a wrong result). Callers use `check_with_memory` for those
        // queries.
        if self.has_deferred_theory_assertions() {
            return Err(SolverError::Unsupported(
                "active array/UF theory assertions: use check_with_memory (the warm path does \
                 not bit-blast deferred theories)"
                    .to_owned(),
            ));
        }
        // Encode each one-shot assumption guarded by an ephemeral selector that
        // is assumed only for this solve, so it does not persist as a hard
        // constraint after the check returns.
        let mut ephemeral = Vec::with_capacity(assumptions.len());
        for assumption in assumptions {
            if arena.sort_of(assumption.original) != Sort::Bool {
                return Err(SolverError::NonBooleanAssertion(assumption.original));
            }
            if arena.sort_of(assumption.encoded) != Sort::Bool {
                return Err(SolverError::Backend(format!(
                    "memory simplification changed Boolean assumption #{} to non-Boolean term #{}",
                    assumption.original.index(),
                    assumption.encoded.index()
                )));
            }
            if needs_deferred_theory(arena, assumption.encoded) {
                return Err(SolverError::Unsupported(
                    "array/UF assumption: use check_assuming_with_memory (the warm path does not \
                     bit-blast deferred theories)"
                        .to_owned(),
                ));
            }
            if let Some((unsupported, op)) = first_unsupported_op(arena, &[assumption.encoded]) {
                return Err(SolverError::Unsupported(format!(
                    "term #{} uses unsupported pure-Rust BV operator {op:?}",
                    unsupported.index()
                )));
            }
            let lowered = self
                .lowering
                .lower(arena, assumption.encoded)
                .map_err(map_lower_error)?;
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
                // Replay is the soundness gate. If the trust-anchor evaluator
                // cannot evaluate a term (e.g. an arithmetic overflow), the model
                // is unverifiable: degrade to a graceful `Unknown` rather than
                // accepting an unchecked sat or crashing.
                let original_assumptions = original_assumptions(assumptions);
                if let Some(reason) = self.replay(arena, &original_assumptions, &model)? {
                    return Ok((CheckResult::Unknown(reason), Vec::new()));
                }
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
                        core.push(assumptions[i].original);
                    }
                }
                if core.is_empty() && !assumptions.is_empty() {
                    core.extend(original_assumptions(assumptions));
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
    /// assumptions, the level-1 evidence check.
    ///
    /// Returns `Ok(None)` when verified. Returns `Ok(Some(reason))` when a term
    /// could not be *evaluated* (an [`IrError`] such as an arithmetic overflow in
    /// the trust-anchor evaluator): the model is conservatively not accepted and
    /// the caller degrades to `Unknown`. Returns `Err(..)` only for a genuine
    /// soundness violation (a term evaluating to `false`/non-Boolean).
    fn replay(
        &self,
        arena: &TermArena,
        assumptions: &[TermId],
        model: &Model,
    ) -> Result<Option<UnknownReason>, SolverError> {
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
                    return Ok(Some(UnknownReason {
                        kind: UnknownKind::Other,
                        detail: format!(
                            "incremental sat model could not be verified: term #{} failed \
                             evaluation: {error} (model conservatively not accepted)",
                            term.index()
                        ),
                    }));
                }
            }
        }
        Ok(None)
    }

    fn active_assertions(&self) -> Vec<TermId> {
        self.frames
            .iter()
            .flat_map(|frame| {
                frame
                    .assertions
                    .iter()
                    .chain(frame.deferred_assertions.iter())
                    .copied()
            })
            .collect()
    }

    fn active_assertions_with_assumptions(
        &self,
        arena: &TermArena,
        assumptions: &[TermId],
    ) -> Result<Vec<TermId>, SolverError> {
        let mut active = self.active_assertions();
        active.reserve(assumptions.len());
        for &assumption in assumptions {
            if arena.sort_of(assumption) != Sort::Bool {
                return Err(SolverError::NonBooleanAssertion(assumption));
            }
            active.push(assumption);
        }
        Ok(active)
    }
}

fn simplify_memory_for_warm_assertion_inner(
    arena: &mut TermArena,
    term: TermId,
    memo: &mut HashMap<TermId, TermId>,
) -> TermId {
    if let Some(&simplified) = memo.get(&term) {
        return simplified;
    }

    let original_args = if let TermNode::App { args, .. } = arena.node(term) {
        args.to_vec()
    } else {
        memo.insert(term, term);
        return term;
    };
    let simplified_args = original_args
        .iter()
        .map(|&arg| simplify_memory_for_warm_assertion_inner(arena, arg, memo))
        .collect::<Vec<_>>();
    let rebuilt = if simplified_args == original_args {
        term
    } else {
        arena.rebuild_with_args(term, &simplified_args)
    };
    let simplified = match collapse_read_over_write(arena, rebuilt) {
        Some(collapsed) if collapsed != rebuilt => {
            simplify_memory_for_warm_assertion_inner(arena, collapsed, memo)
        }
        _ => rebuilt,
    };
    memo.insert(term, simplified);
    simplified
}

fn collapse_read_over_write(arena: &mut TermArena, term: TermId) -> Option<TermId> {
    let (array, read_index) = match arena.node(term) {
        TermNode::App {
            op: Op::Select,
            args,
            ..
        } => {
            let [array, read_index] = args.as_ref() else {
                return None;
            };
            (*array, *read_index)
        }
        _ => return None,
    };
    if let Some(value) = const_array_default(arena, array) {
        return Some(value);
    }
    let (base, write_index, value) = match arena.node(array) {
        TermNode::App {
            op: Op::Store,
            args,
            ..
        } => {
            let [base, write_index, value] = args.as_ref() else {
                return None;
            };
            (*base, *write_index, *value)
        }
        _ => return None,
    };
    if write_index == read_index {
        return Some(value);
    }
    if known_literal_distinct(arena, write_index, read_index) {
        return arena.select(base, read_index).ok();
    }
    None
}

fn const_array_default(arena: &TermArena, term: TermId) -> Option<TermId> {
    let TermNode::App {
        op: Op::ConstArray { .. },
        args,
        ..
    } = arena.node(term)
    else {
        return None;
    };
    let [value] = args.as_ref() else {
        return None;
    };
    Some(*value)
}

fn known_literal_distinct(arena: &TermArena, left: TermId, right: TermId) -> bool {
    if arena.sort_of(left) != arena.sort_of(right) {
        return false;
    }
    match (arena.node(left), arena.node(right)) {
        (TermNode::BoolConst(a), TermNode::BoolConst(b)) => a != b,
        (
            TermNode::BvConst {
                width: left_width,
                value: left_value,
            },
            TermNode::BvConst {
                width: right_width,
                value: right_value,
            },
        ) => left_width == right_width && left_value != right_value,
        (TermNode::WideBvConst(a), TermNode::WideBvConst(b)) => a != b,
        (TermNode::IntConst(a), TermNode::IntConst(b)) => a != b,
        (TermNode::RealConst(a), TermNode::RealConst(b)) => a != b,
        _ => false,
    }
}

fn original_assumptions(assumptions: &[OneShotAssumption]) -> Vec<TermId> {
    assumptions
        .iter()
        .map(|assumption| assumption.original)
        .collect()
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
