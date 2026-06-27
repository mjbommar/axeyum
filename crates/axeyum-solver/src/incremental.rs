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
    ArraySortKey, ArrayValue, Assignment, FuncId, FuncValue, GenericArrayValue, IrError, Op, Sort,
    SymbolId, TermArena, TermId, TermNode, Value, WideUint, eval, well_founded_default,
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
    /// Array reads abstracted into warm scalar symbols for this frame's encoded
    /// assertions. These drive model projection before original-term replay.
    warm_array_selects: Vec<TermId>,
    /// Uninterpreted-function applications abstracted into warm scalar symbols.
    /// These drive function-model projection before original-term replay.
    warm_uf_apps: Vec<TermId>,
}

#[derive(Debug, Clone)]
struct OneShotAssumption {
    original: TermId,
    encoded: TermId,
    warm_array_selects: Vec<TermId>,
    warm_uf_apps: Vec<TermId>,
    congruence_lemmas: Vec<TermId>,
}

#[derive(Debug, Clone, Copy)]
struct WarmArraySelect {
    array_symbol: SymbolId,
    index: TermId,
    value_symbol: SymbolId,
    value_term: TermId,
    index_width: u32,
    element: ArraySortKey,
    element_sort: Sort,
}

#[derive(Debug)]
struct WarmArrayEncoding {
    term: TermId,
    select_terms: Vec<TermId>,
    uf_app_terms: Vec<TermId>,
    congruence_lemmas: Vec<TermId>,
}

#[derive(Debug, Clone)]
struct WarmUfApp {
    func: FuncId,
    args: Vec<TermId>,
    value_symbol: Option<SymbolId>,
    value_term: TermId,
    result_sort: Sort,
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
    warm_array_selects: HashMap<TermId, WarmArraySelect>,
    warm_uf_apps: HashMap<TermId, WarmUfApp>,
    internal_symbols: HashSet<SymbolId>,
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
                warm_array_selects: Vec::new(),
                warm_uf_apps: Vec::new(),
            }],
            warm_array_selects: HashMap::new(),
            warm_uf_apps: HashMap::new(),
            internal_symbols: HashSet::new(),
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

    /// Whether a term that has already gone through
    /// [`Self::simplify_memory_for_warm_assertion`] can stay on the warm BV path
    /// after the retained select/UF abstraction pass.
    ///
    /// This is a pure preflight for branch routing. The real encoding still goes
    /// through [`Self::check_assuming_simplifying_memory`] /
    /// [`Self::assert_simplifying_memory`], which creates the internal symbols,
    /// scoped congruence lemmas, and replay projection maps.
    #[must_use]
    pub fn term_supported_by_warm_abstraction(arena: &TermArena, term: TermId) -> bool {
        let mut memo = HashMap::new();
        warm_abstraction_covers_term(arena, term, &mut memo)
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
    /// `select(a, c2)` when `c1 != c2` is known from constants), collapses reads
    /// from constant arrays to their default value, and distributes reads over
    /// array-valued `ite`. When neither index case is syntactically decided, it
    /// expands read-over-write to a scalar conditional and keeps simplifying the
    /// else branch; this only stays warm when the resulting term is array-free
    /// or reducible by the later retained select/UF abstraction pass. It
    /// recurses through ordinary wrappers, but does not instantiate array
    /// extensionality or general UF lemmas.
    #[must_use]
    pub fn simplify_memory_for_warm_assertion(arena: &mut TermArena, term: TermId) -> TermId {
        let mut memo = HashMap::new();
        simplify_memory_for_warm_assertion_inner(arena, term, &mut memo)
    }

    /// Asserts `term`, first applying the small warm-safe memory simplifier and
    /// retained scalar select/UF abstraction.
    ///
    /// When simplification/abstraction removes all array/UF structure, the pure
    /// BV term is encoded into the warm BV solver while the original term is
    /// retained for replay. If unsupported array/UF structure remains, the
    /// original term is scoped as a deferred theory assertion exactly like
    /// [`Self::assert`].
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
        self.assert_encoded_with_warm_array_selects(arena, term, encoded)
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

    fn assert_encoded_with_warm_array_selects(
        &mut self,
        arena: &mut TermArena,
        original: TermId,
        encoded: TermId,
    ) -> Result<TermId, SolverError> {
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

        let existing_selects = self.active_warm_array_select_terms();
        let existing_uf_apps = self.active_warm_uf_app_terms();
        let encoded =
            self.abstract_warm_array_selects(arena, encoded, &existing_selects, &existing_uf_apps)?;
        if needs_deferred_theory(arena, encoded.term) {
            self.frames
                .last_mut()
                .expect("base frame always present")
                .deferred_assertions
                .push(original);
            return Ok(encoded.term);
        }

        let selector = self
            .frames
            .last()
            .expect("base frame always present")
            .selector;
        for &lemma in &encoded.congruence_lemmas {
            self.encode_warm_root(arena, lemma, selector)?;
        }
        self.encode_warm_root(arena, encoded.term, selector)?;
        let frame = self.frames.last_mut().expect("base frame always present");
        frame.assertions.push(original);
        frame.warm_array_selects.extend(encoded.select_terms);
        frame.warm_uf_apps.extend(encoded.uf_app_terms);
        Ok(encoded.term)
    }

    fn encode_warm_root(
        &mut self,
        arena: &TermArena,
        term: TermId,
        selector: Option<CnfVar>,
    ) -> Result<(), SolverError> {
        if let Some((unsupported, op)) = first_unsupported_op(arena, &[term]) {
            return Err(SolverError::Unsupported(format!(
                "term #{} uses unsupported pure-Rust BV operator {op:?}",
                unsupported.index()
            )));
        }
        let lowered = self.lowering.lower(arena, term).map_err(map_lower_error)?;
        let root = lowered.bits()[0];
        self.cnf
            .assert_root(self.lowering.aig(), root, selector)
            .map_err(|error| map_sat_error(&error))
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
            warm_array_selects: Vec::new(),
            warm_uf_apps: Vec::new(),
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
    /// This lets branch/fork queries over the narrow warm memory slice stay on
    /// the warm BV path. The original assumptions are still replayed against
    /// any returned model and reported in any assumption core.
    ///
    /// # Errors
    ///
    /// Returns the same errors as [`Self::check_assuming`].
    pub fn check_assuming_simplifying_memory(
        &mut self,
        arena: &mut TermArena,
        assumptions: &[TermId],
    ) -> Result<CheckResult, SolverError> {
        let assumptions = self.simplified_one_shot_assumptions(arena, assumptions)?;
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
        let assumptions = self.simplified_one_shot_assumptions(arena, assumptions)?;
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

    fn active_warm_array_select_terms(&self) -> Vec<TermId> {
        self.frames
            .iter()
            .flat_map(|frame| frame.warm_array_selects.iter().copied())
            .collect()
    }

    fn active_warm_uf_app_terms(&self) -> Vec<TermId> {
        self.frames
            .iter()
            .flat_map(|frame| frame.warm_uf_apps.iter().copied())
            .collect()
    }

    fn abstract_warm_array_selects(
        &mut self,
        arena: &mut TermArena,
        term: TermId,
        existing_selects: &[TermId],
        existing_uf_apps: &[TermId],
    ) -> Result<WarmArrayEncoding, SolverError> {
        let mut memo = HashMap::new();
        let mut select_terms = Vec::new();
        let mut uf_app_terms = Vec::new();
        let term = self.abstract_warm_array_selects_inner(
            arena,
            term,
            &mut memo,
            &mut select_terms,
            &mut uf_app_terms,
        )?;
        let mut congruence_lemmas = Vec::new();
        let mut prior = existing_selects.to_vec();
        for &select in &select_terms {
            for &other in &prior {
                if let Some(lemma) = self.warm_array_congruence_lemma(arena, other, select)? {
                    congruence_lemmas.push(lemma);
                }
            }
            prior.push(select);
        }
        let mut prior = existing_uf_apps.to_vec();
        for &app in &uf_app_terms {
            for &other in &prior {
                if let Some(lemma) = self.warm_uf_congruence_lemma(arena, other, app)? {
                    congruence_lemmas.push(lemma);
                }
            }
            prior.push(app);
        }
        Ok(WarmArrayEncoding {
            term,
            select_terms,
            uf_app_terms,
            congruence_lemmas,
        })
    }

    fn abstract_warm_array_selects_inner(
        &mut self,
        arena: &mut TermArena,
        term: TermId,
        memo: &mut HashMap<TermId, TermId>,
        select_terms: &mut Vec<TermId>,
        uf_app_terms: &mut Vec<TermId>,
    ) -> Result<TermId, SolverError> {
        if let Some(&abstracted) = memo.get(&term) {
            return Ok(abstracted);
        }

        if let Some(select) = Self::supported_warm_array_select(arena, term)
            && !needs_deferred_theory(arena, select.index)
        {
            let abstracted = self.get_or_create_warm_array_select(arena, term, select)?;
            if !select_terms.contains(&term) {
                select_terms.push(term);
            }
            memo.insert(term, abstracted.value_term);
            return Ok(abstracted.value_term);
        }

        if let Some(app) = Self::supported_warm_uf_app(arena, term)
            && app
                .args
                .iter()
                .all(|&arg| !needs_deferred_theory(arena, arg))
        {
            let abstracted = self.get_or_create_warm_uf_app(arena, term, app)?;
            if !uf_app_terms.contains(&term) {
                uf_app_terms.push(term);
            }
            memo.insert(term, abstracted.value_term);
            return Ok(abstracted.value_term);
        }

        let original_args = if let TermNode::App { args, .. } = arena.node(term) {
            args.to_vec()
        } else {
            memo.insert(term, term);
            return Ok(term);
        };
        let mut changed = false;
        let mut abstracted_args = Vec::with_capacity(original_args.len());
        for &arg in &original_args {
            let abstracted = self.abstract_warm_array_selects_inner(
                arena,
                arg,
                memo,
                select_terms,
                uf_app_terms,
            )?;
            changed |= abstracted != arg;
            abstracted_args.push(abstracted);
        }
        let rebuilt = if changed {
            arena.rebuild_with_args(term, &abstracted_args)
        } else {
            term
        };
        let abstracted = if let Some(select) = Self::supported_warm_array_select(arena, rebuilt)
            && !needs_deferred_theory(arena, select.index)
        {
            let abstracted = self.get_or_create_warm_array_select(arena, rebuilt, select)?;
            if !select_terms.contains(&rebuilt) {
                select_terms.push(rebuilt);
            }
            abstracted.value_term
        } else if let Some(app) = Self::supported_warm_uf_app(arena, rebuilt)
            && app
                .args
                .iter()
                .all(|&arg| !needs_deferred_theory(arena, arg))
        {
            let abstracted = self.get_or_create_warm_uf_app(arena, rebuilt, app)?;
            if !uf_app_terms.contains(&rebuilt) {
                uf_app_terms.push(rebuilt);
            }
            abstracted.value_term
        } else {
            rebuilt
        };
        memo.insert(term, abstracted);
        Ok(abstracted)
    }

    fn supported_warm_array_select(arena: &TermArena, term: TermId) -> Option<WarmArraySelect> {
        let TermNode::App {
            op: Op::Select,
            args,
            ..
        } = arena.node(term)
        else {
            return None;
        };
        let [array, index] = args.as_ref() else {
            return None;
        };
        let TermNode::Symbol(array_symbol) = arena.node(*array) else {
            return None;
        };
        let Sort::Array {
            index: ArraySortKey::BitVec(index_width),
            element,
        } = arena.sort_of(*array)
        else {
            return None;
        };
        if !is_warm_array_element_sort(element) {
            return None;
        }
        let element_sort = element.to_sort();
        if arena.sort_of(*index) != Sort::BitVec(index_width) || arena.sort_of(term) != element_sort
        {
            return None;
        }
        Some(WarmArraySelect {
            array_symbol: *array_symbol,
            index: *index,
            value_symbol: *array_symbol,
            value_term: term,
            index_width,
            element,
            element_sort,
        })
    }

    fn get_or_create_warm_array_select(
        &mut self,
        arena: &mut TermArena,
        term: TermId,
        mut select: WarmArraySelect,
    ) -> Result<WarmArraySelect, SolverError> {
        if let Some(existing) = self.warm_array_selects.get(&term).copied() {
            return Ok(existing);
        }
        let base_name = format!("!axeyum_warm_select_{}", term.index());
        let name = fresh_internal_symbol_name(arena, &base_name);
        let value_symbol = arena
            .declare(&name, select.element_sort)
            .map_err(|error| map_ir_error(&error))?;
        let value_term = arena.var(value_symbol);
        self.internal_symbols.insert(value_symbol);
        select.value_symbol = value_symbol;
        select.value_term = value_term;
        self.warm_array_selects.insert(term, select);
        Ok(select)
    }

    fn warm_array_congruence_lemma(
        &self,
        arena: &mut TermArena,
        left: TermId,
        right: TermId,
    ) -> Result<Option<TermId>, SolverError> {
        if left == right {
            return Ok(None);
        }
        let Some(left) = self.warm_array_selects.get(&left).copied() else {
            return Ok(None);
        };
        let Some(right) = self.warm_array_selects.get(&right).copied() else {
            return Ok(None);
        };
        if left.array_symbol != right.array_symbol {
            return Ok(None);
        }
        let same_index = arena
            .eq(left.index, right.index)
            .map_err(|error| map_ir_error(&error))?;
        let same_value = arena
            .eq(left.value_term, right.value_term)
            .map_err(|error| map_ir_error(&error))?;
        let distinct_index = arena
            .not(same_index)
            .map_err(|error| map_ir_error(&error))?;
        arena
            .or(distinct_index, same_value)
            .map(Some)
            .map_err(|error| map_ir_error(&error))
    }

    fn supported_warm_uf_app(arena: &TermArena, term: TermId) -> Option<WarmUfApp> {
        let TermNode::App {
            op: Op::Apply(func),
            args,
            ..
        } = arena.node(term)
        else {
            return None;
        };
        let (_name, params, result_sort) = arena.function(*func);
        if !is_warm_scalar_sort(result_sort)
            || args.len() != params.len()
            || !params.iter().copied().all(is_warm_scalar_sort)
            || args
                .iter()
                .zip(params)
                .any(|(&arg, &sort)| arena.sort_of(arg) != sort)
        {
            return None;
        }
        Some(WarmUfApp {
            func: *func,
            args: args.to_vec(),
            value_symbol: None,
            value_term: term,
            result_sort,
        })
    }

    fn get_or_create_warm_uf_app(
        &mut self,
        arena: &mut TermArena,
        term: TermId,
        mut app: WarmUfApp,
    ) -> Result<WarmUfApp, SolverError> {
        if let Some(existing) = self.warm_uf_apps.get(&term).cloned() {
            return Ok(existing);
        }
        let base_name = format!("!axeyum_warm_uf_{}", term.index());
        let name = fresh_internal_symbol_name(arena, &base_name);
        let value_symbol = arena
            .declare(&name, app.result_sort)
            .map_err(|error| map_ir_error(&error))?;
        let value_term = arena.var(value_symbol);
        self.internal_symbols.insert(value_symbol);
        app.value_symbol = Some(value_symbol);
        app.value_term = value_term;
        self.warm_uf_apps.insert(term, app.clone());
        Ok(app)
    }

    fn warm_uf_congruence_lemma(
        &self,
        arena: &mut TermArena,
        left: TermId,
        right: TermId,
    ) -> Result<Option<TermId>, SolverError> {
        if left == right {
            return Ok(None);
        }
        let Some(left) = self.warm_uf_apps.get(&left) else {
            return Ok(None);
        };
        let Some(right) = self.warm_uf_apps.get(&right) else {
            return Ok(None);
        };
        if left.func != right.func || left.args.len() != right.args.len() {
            return Ok(None);
        }

        let same_value = arena
            .eq(left.value_term, right.value_term)
            .map_err(|error| map_ir_error(&error))?;
        let Some(same_args) = conjunction_of_equalities(arena, &left.args, &right.args)? else {
            return Ok(Some(same_value));
        };
        let distinct_args = arena.not(same_args).map_err(|error| map_ir_error(&error))?;
        arena
            .or(distinct_args, same_value)
            .map(Some)
            .map_err(|error| map_ir_error(&error))
    }

    fn simplified_one_shot_assumptions(
        &mut self,
        arena: &mut TermArena,
        assumptions: &[TermId],
    ) -> Result<Vec<OneShotAssumption>, SolverError> {
        let mut active_selects = self.active_warm_array_select_terms();
        let mut active_uf_apps = self.active_warm_uf_app_terms();
        let mut simplified = Vec::with_capacity(assumptions.len());
        for &term in assumptions {
            if arena.sort_of(term) != Sort::Bool {
                return Err(SolverError::NonBooleanAssertion(term));
            }
            let encoded = Self::simplify_memory_for_warm_assertion(arena, term);
            let encoded =
                self.abstract_warm_array_selects(arena, encoded, &active_selects, &active_uf_apps)?;
            active_selects.extend(encoded.select_terms.iter().copied());
            active_uf_apps.extend(encoded.uf_app_terms.iter().copied());
            simplified.push(OneShotAssumption {
                original: term,
                encoded: encoded.term,
                warm_array_selects: encoded.select_terms,
                warm_uf_apps: encoded.uf_app_terms,
                congruence_lemmas: encoded.congruence_lemmas,
            });
        }
        Ok(simplified)
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
                warm_array_selects: Vec::new(),
                warm_uf_apps: Vec::new(),
                congruence_lemmas: Vec::new(),
            })
            .collect::<Vec<_>>();
        self.solve_with_encoded_extra(arena, &assumptions)
    }

    fn encode_one_shot_assumptions(
        &mut self,
        arena: &TermArena,
        assumptions: &[OneShotAssumption],
    ) -> Result<(Vec<CnfVar>, Vec<CnfVar>), SolverError> {
        let lemma_count = assumptions
            .iter()
            .map(|assumption| assumption.congruence_lemmas.len())
            .sum::<usize>();
        let mut ephemeral = Vec::with_capacity(assumptions.len() + lemma_count);
        let mut assumption_selectors = Vec::with_capacity(assumptions.len());

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
            for &lemma in &assumption.congruence_lemmas {
                if needs_deferred_theory(arena, lemma) {
                    return Err(SolverError::Unsupported(
                        "array/UF assumption congruence lemma still mentions deferred theory"
                            .to_owned(),
                    ));
                }
                let selector = self
                    .cnf
                    .fresh_selector()
                    .map_err(|error| map_sat_error(&error))?;
                self.encode_warm_root(arena, lemma, Some(selector))?;
                ephemeral.push(selector);
            }
            let selector = self
                .cnf
                .fresh_selector()
                .map_err(|error| map_sat_error(&error))?;
            self.encode_warm_root(arena, assumption.encoded, Some(selector))?;
            ephemeral.push(selector);
            assumption_selectors.push(selector);
        }

        Ok((ephemeral, assumption_selectors))
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
        let (ephemeral, assumption_selectors) =
            self.encode_one_shot_assumptions(arena, assumptions)?;

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
                let one_shot_selects = assumptions
                    .iter()
                    .flat_map(|assumption| assumption.warm_array_selects.iter().copied())
                    .collect::<Vec<_>>();
                let one_shot_uf_apps = assumptions
                    .iter()
                    .flat_map(|assumption| assumption.warm_uf_apps.iter().copied())
                    .collect::<Vec<_>>();
                let model = match self.complete_model_with_warm_theories(
                    arena,
                    &reconstructed,
                    &one_shot_selects,
                    &one_shot_uf_apps,
                ) {
                    Ok(model) => model,
                    Err(reason) => return Ok((CheckResult::Unknown(reason), Vec::new())),
                };
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
                    if let Some(i) = assumption_selectors
                        .iter()
                        .position(|&sel| sel == lit.var())
                    {
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

    fn complete_model_with_warm_theories(
        &self,
        arena: &TermArena,
        assignment: &Assignment,
        one_shot_selects: &[TermId],
        one_shot_uf_apps: &[TermId],
    ) -> Result<Model, UnknownReason> {
        let mut model = complete_model_filtered(arena, assignment, &self.internal_symbols);
        self.project_warm_array_selects(arena, assignment, one_shot_selects, &mut model)?;
        self.project_warm_uf_apps(arena, assignment, one_shot_uf_apps, &mut model)?;
        Ok(model)
    }

    fn project_warm_array_selects(
        &self,
        arena: &TermArena,
        assignment: &Assignment,
        one_shot_selects: &[TermId],
        model: &mut Model,
    ) -> Result<(), UnknownReason> {
        let mut select_terms = self.active_warm_array_select_terms();
        select_terms.extend_from_slice(one_shot_selects);
        select_terms.sort_by_key(|term| term.index());
        select_terms.dedup();

        for select_term in select_terms {
            let Some(select) = self.warm_array_selects.get(&select_term).copied() else {
                continue;
            };
            let select_value =
                warm_array_select_abstraction_value(arena, assignment, select_term, select)?;
            let model_assignment =
                assignment_with_internal(arena, model, assignment, &self.internal_symbols);
            let index_value = warm_array_select_index_value(arena, &model_assignment, select)?;
            let array_value = warm_array_select_projected_array(
                select_term,
                select,
                &select_value,
                &index_value,
                model,
            )?;
            model.set(select.array_symbol, array_value);
        }
        Ok(())
    }

    fn project_warm_uf_apps(
        &self,
        arena: &TermArena,
        assignment: &Assignment,
        one_shot_uf_apps: &[TermId],
        model: &mut Model,
    ) -> Result<(), UnknownReason> {
        let mut app_terms = self.active_warm_uf_app_terms();
        app_terms.extend_from_slice(one_shot_uf_apps);
        app_terms.sort_by_key(|term| term.index());
        app_terms.dedup();

        for app_term in app_terms {
            let Some(app) = self.warm_uf_apps.get(&app_term) else {
                continue;
            };
            let Some(value_symbol) = app.value_symbol else {
                return Err(UnknownReason {
                    kind: UnknownKind::Other,
                    detail: format!(
                        "warm UF abstraction #{} had no internal value symbol",
                        app_term.index()
                    ),
                });
            };
            let result = assignment
                .get(value_symbol)
                .or_else(|| well_founded_default(arena, app.result_sort))
                .ok_or_else(|| UnknownReason {
                    kind: UnknownKind::Other,
                    detail: format!(
                        "warm UF abstraction #{} had no default value",
                        app_term.index()
                    ),
                })?;
            let result = normalize_bitvec_value(result);
            if result.sort() != app.result_sort {
                return Err(UnknownReason {
                    kind: UnknownKind::Other,
                    detail: format!(
                        "warm UF abstraction #{} had result value {result} of wrong sort",
                        app_term.index()
                    ),
                });
            }

            let (_name, params, result_sort) = arena.function(app.func);
            let model_assignment =
                assignment_with_internal(arena, model, assignment, &self.internal_symbols);
            let mut arg_values = Vec::with_capacity(app.args.len());
            for (&arg, &sort) in app.args.iter().zip(params) {
                let value = eval(arena, arg, &model_assignment).map_err(|error| UnknownReason {
                    kind: UnknownKind::Other,
                    detail: format!(
                        "warm UF argument #{} for app #{} could not be evaluated: {error}",
                        arg.index(),
                        app_term.index()
                    ),
                })?;
                let value = normalize_bitvec_value(value);
                if value.sort() != sort {
                    return Err(UnknownReason {
                        kind: UnknownKind::Other,
                        detail: format!(
                            "warm UF argument #{} for app #{} evaluated to {value} of wrong sort",
                            arg.index(),
                            app_term.index()
                        ),
                    });
                }
                arg_values.push(value);
            }

            let use_value_storage = FuncValue::uses_value_storage_for(params, result_sort);
            let interpretation = match model.function(app.func).cloned() {
                Some(existing) if existing.uses_value_storage() == use_value_storage => existing,
                _ if use_value_storage => {
                    let default = well_founded_default(arena, result_sort)
                        .map(normalize_bitvec_value)
                        .ok_or_else(|| UnknownReason {
                            kind: UnknownKind::Other,
                            detail: format!(
                                "warm UF abstraction #{} had no default function result",
                                app_term.index()
                            ),
                        })?;
                    FuncValue::constant_value(params.to_vec(), result_sort, default)
                }
                _ => FuncValue::constant(params.to_vec(), result_sort, 0),
            };
            let interpretation = if use_value_storage {
                interpretation.define_value(&arg_values, result)
            } else {
                let arg_codes: Vec<u128> = arg_values.iter().map(Value::scalar_code).collect();
                interpretation.define(&arg_codes, result.scalar_code())
            };
            model.set_function(app.func, interpretation);
        }
        Ok(())
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
    let simplified = match collapse_trivial_warm_term(arena, rebuilt)
        .or_else(|| collapse_read_over_write(arena, rebuilt))
    {
        Some(collapsed) if collapsed != rebuilt => {
            simplify_memory_for_warm_assertion_inner(arena, collapsed, memo)
        }
        _ => rebuilt,
    };
    memo.insert(term, simplified);
    simplified
}

fn collapse_trivial_warm_term(arena: &mut TermArena, term: TermId) -> Option<TermId> {
    let (op, args) = match arena.node(term) {
        TermNode::App { op, args } => (*op, args.to_vec()),
        _ => return None,
    };
    match op {
        Op::Ite => {
            let [condition, then_term, else_term] = args.as_slice() else {
                return None;
            };
            match arena.node(*condition) {
                TermNode::BoolConst(true) => return Some(*then_term),
                TermNode::BoolConst(false) => return Some(*else_term),
                _ => {}
            }
            (*then_term == *else_term).then_some(*then_term)
        }
        Op::Eq => {
            let [left, right] = args.as_slice() else {
                return None;
            };
            (left == right).then(|| arena.bool_const(true))
        }
        Op::BoolNot => {
            let [arg] = args.as_slice() else {
                return None;
            };
            match arena.node(*arg) {
                TermNode::BoolConst(value) => Some(arena.bool_const(!value)),
                _ => None,
            }
        }
        _ => None,
    }
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
    if let Some(distributed) = distribute_select_over_array_ite(arena, array, read_index) {
        return Some(distributed);
    }
    if let Some(distributed) = distribute_select_over_index_ite(arena, array, read_index) {
        return Some(distributed);
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
    let base = drop_shadowed_stores_at_index(arena, base, write_index);
    if write_index == read_index {
        return Some(value);
    }
    if known_literal_distinct(arena, write_index, read_index) {
        return arena.select(base, read_index).ok();
    }
    let same_index = arena.eq(write_index, read_index).ok()?;
    let base_read = arena.select(base, read_index).ok()?;
    arena.ite(same_index, value, base_read).ok()
}

fn distribute_select_over_index_ite(
    arena: &mut TermArena,
    array: TermId,
    read_index: TermId,
) -> Option<TermId> {
    let (condition, then_index, else_index) = match arena.node(read_index) {
        TermNode::App {
            op: Op::Ite, args, ..
        } => {
            let [condition, then_index, else_index] = args.as_ref() else {
                return None;
            };
            (*condition, *then_index, *else_index)
        }
        _ => return None,
    };
    let then_read = arena.select(array, then_index).ok()?;
    let else_read = arena.select(array, else_index).ok()?;
    arena.ite(condition, then_read, else_read).ok()
}

fn drop_shadowed_stores_at_index(
    arena: &mut TermArena,
    term: TermId,
    shadowing_index: TermId,
) -> TermId {
    let Some((base, index, value)) = store_parts(arena, term) else {
        return term;
    };
    let pruned_base = drop_shadowed_stores_at_index(arena, base, shadowing_index);
    if index == shadowing_index {
        return pruned_base;
    }
    if pruned_base == base {
        return term;
    }
    arena.store(pruned_base, index, value).unwrap_or(term)
}

fn store_parts(arena: &TermArena, term: TermId) -> Option<(TermId, TermId, TermId)> {
    let TermNode::App {
        op: Op::Store,
        args,
        ..
    } = arena.node(term)
    else {
        return None;
    };
    let [base, index, value] = args.as_ref() else {
        return None;
    };
    Some((*base, *index, *value))
}

fn distribute_select_over_array_ite(
    arena: &mut TermArena,
    array: TermId,
    read_index: TermId,
) -> Option<TermId> {
    let (condition, then_array, else_array) = match arena.node(array) {
        TermNode::App {
            op: Op::Ite, args, ..
        } => {
            let [condition, then_array, else_array] = args.as_ref() else {
                return None;
            };
            (*condition, *then_array, *else_array)
        }
        _ => return None,
    };
    let then_read = arena.select(then_array, read_index).ok()?;
    let else_read = arena.select(else_array, read_index).ok()?;
    arena.ite(condition, then_read, else_read).ok()
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

pub(crate) fn known_literal_distinct(arena: &TermArena, left: TermId, right: TermId) -> bool {
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

fn is_warm_scalar_sort(sort: Sort) -> bool {
    matches!(sort, Sort::Bool | Sort::BitVec(_))
}

fn is_warm_array_element_sort(sort: ArraySortKey) -> bool {
    matches!(sort, ArraySortKey::Bool | ArraySortKey::BitVec(_))
}

fn warm_abstraction_covers_term(
    arena: &TermArena,
    term: TermId,
    memo: &mut HashMap<TermId, bool>,
) -> bool {
    if let Some(&covered) = memo.get(&term) {
        return covered;
    }
    let covered = warm_abstraction_covers_term_uncached(arena, term, memo);
    memo.insert(term, covered);
    covered
}

fn warm_abstraction_covers_term_uncached(
    arena: &TermArena,
    term: TermId,
    memo: &mut HashMap<TermId, bool>,
) -> bool {
    if supported_warm_array_select_shape(arena, term) {
        match arena.node(term) {
            TermNode::App { args, .. } => {
                let [_array, index] = args.as_ref() else {
                    return false;
                };
                return warm_abstraction_covers_term(arena, *index, memo);
            }
            _ => return false,
        }
    }

    if supported_warm_uf_app_shape(arena, term) {
        match arena.node(term) {
            TermNode::App { args, .. } => {
                return args
                    .iter()
                    .copied()
                    .all(|arg| warm_abstraction_covers_term(arena, arg, memo));
            }
            _ => return false,
        }
    }

    if matches!(arena.sort_of(term), Sort::Array { .. }) {
        return false;
    }

    match arena.node(term) {
        TermNode::App { op, args } => {
            if matches!(
                op,
                Op::Select | Op::Store | Op::ConstArray { .. } | Op::Apply(_)
            ) {
                return false;
            }
            args.iter()
                .copied()
                .all(|arg| warm_abstraction_covers_term(arena, arg, memo))
        }
        _ => true,
    }
}

fn supported_warm_array_select_shape(arena: &TermArena, term: TermId) -> bool {
    let TermNode::App {
        op: Op::Select,
        args,
        ..
    } = arena.node(term)
    else {
        return false;
    };
    let [array, index] = args.as_ref() else {
        return false;
    };
    let TermNode::Symbol(_array_symbol) = arena.node(*array) else {
        return false;
    };
    let Sort::Array {
        index: ArraySortKey::BitVec(index_width),
        element,
    } = arena.sort_of(*array)
    else {
        return false;
    };
    is_warm_array_element_sort(element)
        && arena.sort_of(*index) == Sort::BitVec(index_width)
        && arena.sort_of(term) == element.to_sort()
}

fn supported_warm_uf_app_shape(arena: &TermArena, term: TermId) -> bool {
    let TermNode::App {
        op: Op::Apply(func),
        args,
        ..
    } = arena.node(term)
    else {
        return false;
    };
    let (_name, params, result_sort) = arena.function(*func);
    is_warm_scalar_sort(result_sort)
        && args.len() == params.len()
        && params.iter().copied().all(is_warm_scalar_sort)
        && args
            .iter()
            .zip(params)
            .all(|(&arg, &sort)| arena.sort_of(arg) == sort)
}

fn fresh_internal_symbol_name(arena: &TermArena, base_name: &str) -> String {
    let mut name = base_name.to_owned();
    let mut suffix = 0usize;
    while arena
        .symbols()
        .any(|(_symbol, existing, _sort)| existing == name)
    {
        suffix += 1;
        name = format!("{base_name}_{suffix}");
    }
    name
}

fn conjunction_of_equalities(
    arena: &mut TermArena,
    left: &[TermId],
    right: &[TermId],
) -> Result<Option<TermId>, SolverError> {
    if left.len() != right.len() {
        return Err(SolverError::Backend(format!(
            "cannot build congruence over mismatched arities {} and {}",
            left.len(),
            right.len()
        )));
    }
    let mut conjunct = None;
    for (&left, &right) in left.iter().zip(right) {
        let eq = arena
            .eq(left, right)
            .map_err(|error| map_ir_error(&error))?;
        conjunct = Some(match conjunct {
            None => eq,
            Some(acc) => arena.and(acc, eq).map_err(|error| map_ir_error(&error))?,
        });
    }
    Ok(conjunct)
}

fn warm_array_select_abstraction_value(
    arena: &TermArena,
    assignment: &Assignment,
    select_term: TermId,
    select: WarmArraySelect,
) -> Result<Value, UnknownReason> {
    let value = assignment
        .get(select.value_symbol)
        .or_else(|| well_founded_default(arena, select.element_sort))
        .ok_or_else(|| UnknownReason {
            kind: UnknownKind::Other,
            detail: format!(
                "warm array select abstraction #{} had no default value",
                select_term.index()
            ),
        })?;
    if value.sort() != select.element_sort {
        return Err(UnknownReason {
            kind: UnknownKind::Other,
            detail: format!(
                "warm array select abstraction #{} had value sort {}, expected {}",
                select_term.index(),
                value.sort(),
                select.element_sort
            ),
        });
    }
    Ok(normalize_bitvec_value(value))
}

fn warm_array_select_index_value(
    arena: &TermArena,
    assignment: &Assignment,
    select: WarmArraySelect,
) -> Result<Value, UnknownReason> {
    match eval(arena, select.index, assignment) {
        Ok(value) if value.sort() == Sort::BitVec(select.index_width) => {
            Ok(normalize_bitvec_value(value))
        }
        Ok(value) => Err(UnknownReason {
            kind: UnknownKind::Other,
            detail: format!(
                "warm array select index #{} evaluated to non-matching value {value}",
                select.index.index()
            ),
        }),
        Err(error) => Err(UnknownReason {
            kind: UnknownKind::Other,
            detail: format!(
                "warm array select index #{} could not be evaluated: {error}",
                select.index.index()
            ),
        }),
    }
}

fn warm_array_select_projected_array(
    select_term: TermId,
    select: WarmArraySelect,
    select_value: &Value,
    index_value: &Value,
    model: &Model,
) -> Result<Value, UnknownReason> {
    match select.element {
        ArraySortKey::BitVec(_) => {
            project_warm_bv_array_select(select_term, select, select_value, index_value, model)
        }
        ArraySortKey::Bool => {
            project_warm_bool_array_select(select_term, select, select_value, index_value, model)
        }
        other => Err(UnknownReason {
            kind: UnknownKind::Other,
            detail: format!("unsupported warm array element sort {other}"),
        }),
    }
}

fn project_warm_bv_array_select(
    select_term: TermId,
    select: WarmArraySelect,
    select_value: &Value,
    index_value: &Value,
    model: &Model,
) -> Result<Value, UnknownReason> {
    let ArraySortKey::BitVec(element_width) = select.element else {
        unreachable!("caller checked BV element sort")
    };
    let select_value = normalize_bitvec_value(select_value.clone());
    if select_value.sort() != Sort::BitVec(element_width) {
        return Err(UnknownReason {
            kind: UnknownKind::Other,
            detail: format!(
                "warm BV-array select abstraction #{} had value sort {}, expected (_ BitVec {element_width})",
                select_term.index(),
                select_value.sort()
            ),
        });
    }
    if select.index_width <= 128
        && element_width <= 128
        && let Value::Bv {
            value: index_bits, ..
        } = index_value
        && let Value::Bv { value, .. } = select_value
    {
        let array = match model.get(select.array_symbol) {
            Some(Value::Array(array))
                if array.index_width() == select.index_width
                    && array.element_width() == element_width =>
            {
                array
            }
            _ => ArrayValue::constant(select.index_width, element_width, 0),
        };
        return Ok(Value::Array(array.store(*index_bits, value)));
    }
    if index_value.sort() != Sort::BitVec(select.index_width) {
        return Err(UnknownReason {
            kind: UnknownKind::Other,
            detail: format!(
                "warm BV-array select index #{} had value sort {}, expected (_ BitVec {})",
                select.index.index(),
                index_value.sort(),
                select.index_width
            ),
        });
    }
    let array = match model.get(select.array_symbol) {
        Some(Value::GenericArray(array))
            if array.index_sort() == ArraySortKey::BitVec(select.index_width)
                && array.element_sort() == ArraySortKey::BitVec(element_width) =>
        {
            array
        }
        _ => GenericArrayValue::constant(
            ArraySortKey::BitVec(select.index_width),
            ArraySortKey::BitVec(element_width),
            zero_bitvec_value(element_width),
        ),
    };
    Ok(Value::GenericArray(
        array.store(index_value.clone(), select_value),
    ))
}

fn project_warm_bool_array_select(
    select_term: TermId,
    select: WarmArraySelect,
    select_value: &Value,
    index_value: &Value,
    model: &Model,
) -> Result<Value, UnknownReason> {
    if !matches!(select_value, Value::Bool(_)) {
        return Err(UnknownReason {
            kind: UnknownKind::Other,
            detail: format!(
                "warm Bool-array select abstraction #{} had non-Bool value",
                select_term.index()
            ),
        });
    }
    if index_value.sort() != Sort::BitVec(select.index_width) {
        return Err(UnknownReason {
            kind: UnknownKind::Other,
            detail: format!(
                "warm Bool-array select index #{} had value sort {}, expected (_ BitVec {})",
                select.index.index(),
                index_value.sort(),
                select.index_width
            ),
        });
    }
    let array = match model.get(select.array_symbol) {
        Some(Value::GenericArray(array))
            if array.index_sort() == ArraySortKey::BitVec(select.index_width)
                && array.element_sort() == ArraySortKey::Bool =>
        {
            array
        }
        _ => GenericArrayValue::constant(
            ArraySortKey::BitVec(select.index_width),
            ArraySortKey::Bool,
            Value::Bool(false),
        ),
    };
    Ok(Value::GenericArray(
        array.store(index_value.clone(), select_value.clone()),
    ))
}

fn zero_bitvec_value(width: u32) -> Value {
    if width > 128 {
        Value::WideBv(WideUint::zero(width))
    } else {
        Value::Bv { width, value: 0 }
    }
}

fn normalize_bitvec_value(value: Value) -> Value {
    match value {
        Value::Bv { width, value } if width > 128 => {
            Value::WideBv(WideUint::from_u128(value, width))
        }
        Value::WideBv(value) if value.width() <= 128 => Value::Bv {
            width: value.width(),
            value: value.to_u128(),
        },
        other => other,
    }
}

fn assignment_with_internal(
    arena: &TermArena,
    model: &Model,
    assignment: &Assignment,
    internal_symbols: &HashSet<SymbolId>,
) -> Assignment {
    let mut merged = model.to_assignment();
    for &symbol in internal_symbols {
        let (_name, sort) = arena.symbol(symbol);
        if let Some(value) = assignment
            .get(symbol)
            .or_else(|| well_founded_default(arena, sort))
        {
            merged.set(symbol, value);
        }
    }
    merged
}

fn original_assumptions(assumptions: &[OneShotAssumption]) -> Vec<TermId> {
    assumptions
        .iter()
        .map(|assumption| assumption.original)
        .collect()
}

fn complete_model_filtered(
    arena: &TermArena,
    assignment: &Assignment,
    hidden_symbols: &HashSet<SymbolId>,
) -> Model {
    let mut model = Model::new();
    for (symbol, _name, sort) in arena.symbols() {
        if hidden_symbols.contains(&symbol) {
            continue;
        }
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

fn map_ir_error(error: &IrError) -> SolverError {
    SolverError::Backend(error.to_string())
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
