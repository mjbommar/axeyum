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
use axeyum_cnf::{CnfVar, IncrementalCnf, SatError, SatResult, SatUnsatEvidence};
use axeyum_ir::{
    ArraySortKey, ArrayValue, Assignment, FuncId, FuncValue, GenericArrayValue, IrError, Op, Sort,
    SymbolId, TermArena, TermId, TermNode, Value, WideUint, eval, well_founded_default,
};

use std::collections::{BTreeMap, HashMap, HashSet};
use std::time::Duration;

#[cfg(not(target_arch = "wasm32"))]
use std::time::Instant;
#[cfg(target_arch = "wasm32")]
use web_time::Instant;

use crate::backend::{CheckResult, SolverConfig, SolverError, UnknownKind, UnknownReason};
use crate::model::Model;

const MAX_WARM_STRUCTURAL_ARRAY_NODES: usize = 512;
const MAX_WARM_STRUCTURAL_ARRAY_DEPTH: usize = 256;
const MAX_WARM_STRUCTURAL_REFINEMENT_ROUNDS: usize = MAX_WARM_STRUCTURAL_ARRAY_NODES;
const MAX_WARM_ARRAY_UF_APPS_PER_ROOT: usize = 64;

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

struct IncrementalSolveOutcome {
    result: CheckResult,
    assumption_core: Vec<TermId>,
    active_assertion_core: Vec<TermId>,
}

impl IncrementalSolveOutcome {
    fn sat(model: Model) -> Self {
        Self {
            result: CheckResult::Sat(model),
            assumption_core: Vec::new(),
            active_assertion_core: Vec::new(),
        }
    }

    fn unknown(reason: UnknownReason) -> Self {
        Self {
            result: CheckResult::Unknown(reason),
            assumption_core: Vec::new(),
            active_assertion_core: Vec::new(),
        }
    }
}

pub(crate) enum WarmRefutationProbe {
    Refuted { active_core: Vec<TermId> },
    Satisfiable,
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
    /// Array-valued UF applications retained as active projection owners even
    /// when an assertion compares their whole results without reading them.
    warm_array_uf_apps: Vec<TermId>,
    /// Direct equalities between supported array symbols retained as scoped
    /// warm theory facts. They generate select-congruence clauses and drive
    /// equal-array model projection before replay.
    warm_array_equalities: Vec<WarmArrayEquality>,
    /// Boolean flags that stand for array equality atoms nested inside scalar
    /// Boolean structure. Their true branch contributes guarded equality
    /// observations; their false branch contributes a guarded diff witness.
    warm_array_relation_flags: Vec<WarmArrayRelationFlag>,
}

#[derive(Debug, Clone)]
struct OneShotAssumption {
    original: TermId,
    encoded: TermId,
    warm_array_selects: Vec<TermId>,
    warm_uf_apps: Vec<TermId>,
    warm_array_uf_apps: Vec<TermId>,
    warm_array_equalities: Vec<WarmArrayEquality>,
    warm_array_relation_flags: Vec<WarmArrayRelationFlag>,
    congruence_lemmas: Vec<TermId>,
}

#[derive(Debug, Clone, Copy)]
struct WarmArraySelect {
    array_parent: TermId,
    projection_symbol: Option<SymbolId>,
    array_uf_app: Option<TermId>,
    index: TermId,
    encoded_index: TermId,
    value_symbol: Option<SymbolId>,
    value_term: TermId,
    index_width: u32,
    element: ArraySortKey,
    element_sort: Sort,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct WarmArrayEquality {
    left: SymbolId,
    right: SymbolId,
    left_parent: TermId,
    right_parent: TermId,
    left_structural: Option<TermId>,
    right_structural: Option<TermId>,
}

impl WarmArrayEquality {
    fn has_structural_side(self) -> bool {
        self.left_structural.is_some() || self.right_structural.is_some()
    }
}

#[derive(Debug, Clone, Copy)]
struct WarmArrayEqualityOperand {
    owner: SymbolId,
    parent: TermId,
    structural: Option<TermId>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct WarmArrayRelationFlag {
    flag: SymbolId,
    equality: WarmArrayEquality,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum WarmArrayRelationPolarity {
    Equal,
    Distinct,
}

#[derive(Debug, Clone, Copy)]
struct WarmArrayRelation {
    literal: TermId,
    left: TermId,
    right: TermId,
    polarity: WarmArrayRelationPolarity,
    index_width: u32,
}

#[derive(Debug)]
struct WarmArrayEncoding {
    term: TermId,
    select_terms: Vec<TermId>,
    uf_app_terms: Vec<TermId>,
    array_uf_app_terms: Vec<TermId>,
    array_relation_flags: Vec<WarmArrayRelationFlag>,
    congruence_lemmas: Vec<TermId>,
    structural_semantics: Vec<WarmArraySemantic>,
}

#[derive(Debug, Default)]
struct WarmAbstractionWork {
    memo: HashMap<TermId, TermId>,
    select_terms: Vec<TermId>,
    uf_app_terms: Vec<TermId>,
    array_uf_app_terms: Vec<TermId>,
    array_relation_flags: Vec<WarmArrayRelationFlag>,
    congruence_lemmas: Vec<TermId>,
    structural_semantics: Vec<WarmArraySemantic>,
}

#[derive(Debug, Clone)]
struct WarmArraySemantic {
    select_term: TermId,
    definition: TermId,
    dependencies: Vec<TermId>,
}

struct WarmOneShotTerms {
    selects: Vec<TermId>,
    uf_apps: Vec<TermId>,
    array_uf_apps: Vec<TermId>,
    array_equalities: Vec<WarmArrayEquality>,
    array_relation_flags: Vec<WarmArrayRelationFlag>,
}

enum WarmCandidateCheck {
    Refine(Vec<WarmArraySemantic>),
    Sat(Model),
    Unknown(UnknownReason),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum WarmStructuralRealization {
    Unchanged,
    Changed,
    Incompatible,
}

#[derive(Debug, Clone)]
struct WarmUfApp {
    func: FuncId,
    args: Vec<TermId>,
    value_symbol: Option<SymbolId>,
    value_term: TermId,
    result_sort: Sort,
}

#[derive(Debug, Clone)]
struct WarmArrayUfApp {
    func: FuncId,
    args: Vec<TermId>,
    encoded_args: Vec<TermId>,
    projection_symbol: SymbolId,
    result_sort: Sort,
}

#[derive(Debug, Clone)]
struct WarmStructuralArrayOwner {
    projection_symbol: SymbolId,
    rewritten_term: TermId,
    select_terms: Vec<TermId>,
    uf_app_terms: Vec<TermId>,
    array_uf_app_terms: Vec<TermId>,
}

struct WarmArrayUfProjectionGroup {
    func: FuncId,
    args: Vec<Value>,
    projection_symbols: Vec<SymbolId>,
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
    warm_array_semantics: HashMap<TermId, WarmArraySemantic>,
    warm_array_semantics_encoded: HashSet<TermId>,
    warm_array_refinement_rounds: usize,
    warm_uf_apps: HashMap<TermId, WarmUfApp>,
    warm_array_uf_apps: HashMap<TermId, WarmArrayUfApp>,
    warm_structural_array_owners: HashMap<TermId, WarmStructuralArrayOwner>,
    warm_array_equality_probe_symbols: HashMap<TermId, SymbolId>,
    warm_array_diff_symbols: HashMap<TermId, SymbolId>,
    warm_array_relation_flag_symbols: HashMap<TermId, SymbolId>,
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
                warm_array_uf_apps: Vec::new(),
                warm_array_equalities: Vec::new(),
                warm_array_relation_flags: Vec::new(),
            }],
            warm_array_selects: HashMap::new(),
            warm_array_semantics: HashMap::new(),
            warm_array_semantics_encoded: HashSet::new(),
            warm_array_refinement_rounds: 0,
            warm_uf_apps: HashMap::new(),
            warm_array_uf_apps: HashMap::new(),
            warm_structural_array_owners: HashMap::new(),
            warm_array_equality_probe_symbols: HashMap::new(),
            warm_array_diff_symbols: HashMap::new(),
            warm_array_relation_flag_symbols: HashMap::new(),
            internal_symbols: HashSet::new(),
        }
    }

    /// Replaces the wall-clock allowance used by the next warm SAT check.
    ///
    /// Internal online-theory adapters use this to pass an absolute query
    /// deadline as a shrinking per-check timeout instead of accidentally granting
    /// the full user budget to every trail assignment.
    pub(crate) fn set_timeout(&mut self, timeout: Option<Duration>) {
        self.config.timeout = timeout;
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

    /// Number of unique observed array reads represented by retained warm
    /// scalar owners, including direct symbol reads and structural parents.
    #[must_use]
    pub fn retained_warm_array_read_count(&self) -> usize {
        self.warm_array_selects.len()
    }

    /// Number of retained reads whose parent is a store, constant array, or
    /// array-valued ITE rather than a directly projected array symbol.
    #[must_use]
    pub fn retained_warm_structural_read_count(&self) -> usize {
        self.warm_array_selects
            .keys()
            .filter(|select_term| self.warm_array_semantics.contains_key(select_term))
            .count()
    }

    /// Number of exact store/constant/ITE read definitions already installed
    /// in the persistent CNF. Reusing a structural read does not increase it.
    #[must_use]
    pub fn retained_warm_structural_definition_count(&self) -> usize {
        self.warm_array_semantics_encoded.len()
    }

    /// Number of exact structural-read equations retained as candidate-check
    /// metadata, whether dormant or already installed in CNF.
    #[must_use]
    pub fn retained_warm_structural_equation_count(&self) -> usize {
        self.warm_array_semantics.len()
    }

    /// Number of candidate-activation rounds completed over this solver's
    /// lifetime. A round may install several violated definitions as one batch.
    #[must_use]
    pub fn retained_warm_structural_refinement_round_count(&self) -> usize {
        self.warm_array_refinement_rounds
    }

    /// Number of retained finite-scalar array-valued UF application parents.
    #[must_use]
    pub fn retained_warm_array_uf_app_count(&self) -> usize {
        self.warm_array_uf_apps.len()
    }

    /// Number of private total-array owners retained for structural parents
    /// that have participated in positive warm equality.
    #[must_use]
    pub fn retained_warm_structural_array_owner_count(&self) -> usize {
        self.warm_structural_array_owners.len()
    }

    /// Number of private shared-index probes retained for positive structural
    /// equality. Probe metadata may harmlessly outlive a popped scope.
    #[must_use]
    pub fn retained_warm_array_equality_probe_count(&self) -> usize {
        self.warm_array_equality_probe_symbols.len()
    }

    /// Number of private extensional diff-index witnesses retained by relation
    /// literal. Witness metadata may harmlessly outlive a popped scope.
    #[must_use]
    pub fn retained_warm_array_diff_witness_count(&self) -> usize {
        self.warm_array_diff_symbols.len()
    }

    /// Number of private Boolean flags retained for array equality atoms that
    /// appear under scalar Boolean structure.
    #[must_use]
    pub fn retained_warm_array_relation_flag_count(&self) -> usize {
        self.warm_array_relation_flag_symbols.len()
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
        let covered = match warm_array_relation_literal(arena, term) {
            Some(relation) => warm_array_relation_covers(arena, relation, &mut memo),
            None => warm_abstraction_covers_term(arena, term, &mut memo),
        };
        covered && warm_structural_array_limits_hold(arena, term)
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
        simplify_memory_for_warm_assertion_inner(
            arena,
            term,
            &mut memo,
            WarmSimplificationMode::ExpandStructuralReads,
        )
    }

    pub(crate) fn simplify_memory_for_retained_warm_assertion(
        arena: &mut TermArena,
        term: TermId,
    ) -> TermId {
        let mut memo = HashMap::new();
        simplify_memory_for_warm_assertion_inner(
            arena,
            term,
            &mut memo,
            WarmSimplificationMode::RetainStructuralReads,
        )
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
        let encoded = Self::simplify_memory_for_retained_warm_assertion(arena, term);
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

    /// Asserts `term` while honoring an absolute lowering deadline.
    ///
    /// Returns `false` only when bit-vector lowering reaches `deadline`; no CNF
    /// root or frame assertion is installed for the interrupted term. This is
    /// crate-private because online theory combinations translate the outcome
    /// into their shared query's [`UnknownKind::Timeout`].
    pub(crate) fn assert_with_deadline(
        &mut self,
        arena: &TermArena,
        term: TermId,
        deadline: Option<Instant>,
    ) -> Result<bool, SolverError> {
        self.assert_encoded_with_deadline(arena, term, term, deadline)
    }

    fn assert_encoded(
        &mut self,
        arena: &TermArena,
        original: TermId,
        encoded: TermId,
    ) -> Result<(), SolverError> {
        let asserted = self.assert_encoded_with_deadline(arena, original, encoded, None)?;
        debug_assert!(asserted, "deadline-free assertion cannot be interrupted");
        Ok(())
    }

    fn assert_encoded_with_deadline(
        &mut self,
        arena: &TermArena,
        original: TermId,
        encoded: TermId,
        deadline: Option<Instant>,
    ) -> Result<bool, SolverError> {
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
            return Ok(true);
        }
        if let Some((unsupported, op)) = first_unsupported_op(arena, &[encoded]) {
            return Err(SolverError::Unsupported(format!(
                "term #{} uses unsupported pure-Rust BV operator {op:?}",
                unsupported.index()
            )));
        }
        let lowered = match self.lowering.lower_with_deadline(arena, encoded, deadline) {
            Ok(lowered) => lowered,
            Err(BitLowerError::DeadlineExceeded) => return Ok(false),
            Err(error) => return Err(map_lower_error(error)),
        };
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
        Ok(true)
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
        let existing_equalities = self.active_warm_array_equalities();
        let existing_relation_flags = self.active_warm_array_relation_flags();
        if !Self::term_supported_by_warm_abstraction(arena, encoded) {
            self.frames
                .last_mut()
                .expect("base frame always present")
                .deferred_assertions
                .push(original);
            return Ok(encoded);
        }
        let relation = warm_array_relation_literal(arena, encoded);
        if !self.warm_array_equality_observation_budget_holds(
            arena,
            encoded,
            relation,
            &existing_selects,
            &existing_equalities,
        ) {
            self.frames
                .last_mut()
                .expect("base frame always present")
                .deferred_assertions
                .push(original);
            return Ok(encoded);
        }
        if relation.is_some_and(|relation| relation.polarity == WarmArrayRelationPolarity::Equal) {
            return self.assert_warm_array_equality(
                arena,
                original,
                relation.expect("checked as positive relation"),
                &existing_selects,
                &existing_uf_apps,
                &existing_equalities,
                &existing_relation_flags,
            );
        }
        let mut encoded = match relation {
            Some(relation) => self.abstract_warm_array_disequality(
                arena,
                relation,
                &existing_selects,
                &existing_uf_apps,
                &existing_equalities,
            )?,
            None => self.abstract_warm_array_selects(
                arena,
                encoded,
                &existing_selects,
                &existing_uf_apps,
                &existing_equalities,
            )?,
        };
        self.add_warm_array_relation_flag_observation_closure(
            arena,
            &existing_relation_flags,
            &existing_selects,
            &mut encoded,
        )?;
        if needs_deferred_theory(arena, encoded.term) {
            self.frames
                .last_mut()
                .expect("base frame always present")
                .deferred_assertions
                .push(original);
            return Ok(encoded.term);
        }

        self.retain_warm_semantics(&encoded.structural_semantics)?;

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
        frame.warm_array_uf_apps.extend(encoded.array_uf_app_terms);
        frame
            .warm_array_relation_flags
            .extend(encoded.array_relation_flags);
        Ok(encoded.term)
    }

    #[allow(clippy::too_many_arguments)]
    fn assert_warm_array_equality(
        &mut self,
        arena: &mut TermArena,
        original: TermId,
        relation: WarmArrayRelation,
        existing_selects: &[TermId],
        existing_uf_apps: &[TermId],
        existing_equalities: &[WarmArrayEquality],
        existing_relation_flags: &[WarmArrayRelationFlag],
    ) -> Result<TermId, SolverError> {
        let (equality, mut prepared) = self.prepare_warm_array_equality(
            arena,
            relation,
            existing_selects,
            existing_uf_apps,
            existing_equalities,
        )?;
        self.add_warm_array_relation_flag_observation_closure(
            arena,
            existing_relation_flags,
            existing_selects,
            &mut prepared,
        )?;
        self.retain_warm_semantics(&prepared.structural_semantics)?;
        let selector = self
            .frames
            .last()
            .expect("base frame always present")
            .selector;
        for &lemma in &prepared.congruence_lemmas {
            self.encode_warm_root(arena, lemma, selector)?;
        }
        let frame = self.frames.last_mut().expect("base frame always present");
        frame.assertions.push(original);
        frame.warm_array_selects.extend(prepared.select_terms);
        frame.warm_uf_apps.extend(prepared.uf_app_terms);
        frame.warm_array_uf_apps.extend(prepared.array_uf_app_terms);
        frame.warm_array_equalities.push(equality);
        frame
            .warm_array_relation_flags
            .extend(prepared.array_relation_flags);
        Ok(relation.literal)
    }

    fn encode_warm_root(
        &mut self,
        arena: &TermArena,
        term: TermId,
        selector: Option<CnfVar>,
    ) -> Result<(), SolverError> {
        let encoded = self.encode_warm_root_with_deadline(arena, term, selector, None)?;
        debug_assert!(encoded, "deadline-free warm root cannot be interrupted");
        Ok(())
    }

    fn warm_array_equality_observation_budget_holds(
        &self,
        arena: &TermArena,
        root: TermId,
        relation: Option<WarmArrayRelation>,
        existing_selects: &[TermId],
        existing_equalities: &[WarmArrayEquality],
    ) -> bool {
        let mut new_indices = Vec::new();
        collect_warm_select_indices(arena, root, &mut new_indices);
        let generated_diff_index = relation
            .is_some_and(|relation| relation.polarity == WarmArrayRelationPolarity::Distinct);
        let new_index_count = new_indices
            .len()
            .saturating_add(usize::from(generated_diff_index));
        let active_structural = existing_equalities
            .iter()
            .filter(|equality| equality.has_structural_side())
            .count();
        let mut prospective_reads = active_structural
            .saturating_mul(new_index_count)
            .saturating_mul(2);

        if let Some(relation) = relation
            && relation.polarity == WarmArrayRelationPolarity::Equal
            && warm_array_relation_has_structural_parent(arena, relation)
        {
            let mut relation_indices = self.warm_array_select_indices(existing_selects);
            extend_unique_terms(&mut relation_indices, &new_indices);
            let index_sort = Sort::BitVec(relation.index_width);
            collect_warm_store_indices(arena, relation.left, index_sort, &mut relation_indices);
            collect_warm_store_indices(arena, relation.right, index_sort, &mut relation_indices);
            prospective_reads = prospective_reads
                .saturating_add(relation_indices.len().saturating_add(1).saturating_mul(2));
        }
        prospective_reads <= MAX_WARM_STRUCTURAL_ARRAY_NODES
    }

    fn encode_warm_root_with_deadline(
        &mut self,
        arena: &TermArena,
        term: TermId,
        selector: Option<CnfVar>,
        deadline: Option<Instant>,
    ) -> Result<bool, SolverError> {
        if let Some((unsupported, op)) = first_unsupported_op(arena, &[term]) {
            return Err(SolverError::Unsupported(format!(
                "term #{} uses unsupported pure-Rust BV operator {op:?}",
                unsupported.index()
            )));
        }
        let lowered = match self.lowering.lower_with_deadline(arena, term, deadline) {
            Ok(lowered) => lowered,
            Err(BitLowerError::DeadlineExceeded) => return Ok(false),
            Err(error) => return Err(map_lower_error(error)),
        };
        let root = lowered.bits()[0];
        self.cnf
            .assert_root(self.lowering.aig(), root, selector)
            .map_err(|error| map_sat_error(&error))?;
        Ok(true)
    }

    fn retain_warm_semantics(
        &mut self,
        semantics: &[WarmArraySemantic],
    ) -> Result<(), SolverError> {
        for semantic in semantics {
            if let Some(existing) = self.warm_array_semantics.get(&semantic.select_term) {
                if existing.definition != semantic.definition
                    || existing.dependencies != semantic.dependencies
                {
                    return Err(SolverError::Backend(format!(
                        "warm structural read #{} was retained with inconsistent semantics",
                        semantic.select_term.index()
                    )));
                }
            } else {
                self.warm_array_semantics
                    .insert(semantic.select_term, semantic.clone());
            }
        }
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
            warm_array_selects: Vec::new(),
            warm_uf_apps: Vec::new(),
            warm_array_uf_apps: Vec::new(),
            warm_array_equalities: Vec::new(),
            warm_array_relation_flags: Vec::new(),
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
        Ok(self.solve_with_extra(arena, &[])?.result)
    }

    /// Checks active warm assertions and returns the SAT solver's failed-frame
    /// assertion core on `unsat`.
    ///
    /// Each non-base frame is activated by one SAT assumption. The returned core
    /// contains every base-frame assertion plus assertions from the failed frame
    /// selectors. Callers that need literal-granular cores should place one
    /// assertion in each frame.
    pub(crate) fn check_with_active_assertion_core(
        &mut self,
        arena: &TermArena,
    ) -> Result<(CheckResult, Vec<TermId>), SolverError> {
        let outcome = self.solve_with_extra(arena, &[])?;
        Ok((outcome.result, outcome.active_assertion_core))
    }

    /// Checks whether the active warm assertions refute one additional Boolean
    /// assumption, without reconstructing or replaying a SAT model.
    ///
    /// On refutation, the returned active-frame assertion core is a reason for
    /// the negation of `assumption`. This is the exact implication primitive used
    /// by bounded online BV theory propagation.
    pub(crate) fn refute_assumption(
        &mut self,
        arena: &TermArena,
        assumption: TermId,
    ) -> Result<WarmRefutationProbe, SolverError> {
        if self.has_deferred_theory_assertions() {
            return Err(SolverError::Unsupported(
                "active array/UF theory assertions cannot use the warm BV implication probe"
                    .to_owned(),
            ));
        }
        let one_shot = [OneShotAssumption {
            original: assumption,
            encoded: assumption,
            warm_array_selects: Vec::new(),
            warm_uf_apps: Vec::new(),
            warm_array_uf_apps: Vec::new(),
            warm_array_equalities: Vec::new(),
            warm_array_relation_flags: Vec::new(),
            congruence_lemmas: Vec::new(),
        }];
        let (ephemeral, _) = self.encode_one_shot_assumptions(arena, &one_shot)?;
        let mut active = self
            .frames
            .iter()
            .filter_map(|frame| frame.selector)
            .collect::<Vec<_>>();
        active.extend_from_slice(&ephemeral);
        match self
            .cnf
            .solve(&active, self.config.timeout)
            .map_err(|error| map_sat_error(&error))?
        {
            SatResult::Sat(_) => Ok(WarmRefutationProbe::Satisfiable),
            SatResult::Unsat(evidence) => Ok(WarmRefutationProbe::Refuted {
                active_core: self.active_assertion_core(&evidence.failed_assumptions),
            }),
            SatResult::Unknown(reason) => {
                let kind = if reason.detail.contains("timeout") {
                    UnknownKind::Timeout
                } else {
                    UnknownKind::Other
                };
                Ok(WarmRefutationProbe::Unknown(UnknownReason {
                    kind,
                    detail: reason.detail,
                }))
            }
        }
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
        Ok(self.solve_with_extra(arena, assumptions)?.result)
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
        Ok(self.solve_with_encoded_extra(arena, &assumptions)?.result)
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
        let outcome = self.solve_with_extra(arena, assumptions)?;
        Ok(match outcome.result {
            CheckResult::Sat(model) => AssumptionOutcome::Sat(model),
            CheckResult::Unsat => AssumptionOutcome::Unsat {
                core: outcome.assumption_core,
            },
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
        let outcome = self.solve_with_encoded_extra(arena, &assumptions)?;
        Ok(match outcome.result {
            CheckResult::Sat(model) => AssumptionOutcome::Sat(model),
            CheckResult::Unsat => AssumptionOutcome::Unsat {
                core: outcome.assumption_core,
            },
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

    fn active_warm_array_uf_app_terms(&self) -> Vec<TermId> {
        self.frames
            .iter()
            .flat_map(|frame| frame.warm_array_uf_apps.iter().copied())
            .collect()
    }

    fn active_warm_array_equalities(&self) -> Vec<WarmArrayEquality> {
        self.frames
            .iter()
            .flat_map(|frame| frame.warm_array_equalities.iter().copied())
            .collect()
    }

    fn active_warm_array_relation_flags(&self) -> Vec<WarmArrayRelationFlag> {
        self.frames
            .iter()
            .flat_map(|frame| frame.warm_array_relation_flags.iter().copied())
            .collect()
    }

    fn abstract_warm_array_selects(
        &mut self,
        arena: &mut TermArena,
        term: TermId,
        existing_selects: &[TermId],
        existing_uf_apps: &[TermId],
        existing_equalities: &[WarmArrayEquality],
    ) -> Result<WarmArrayEncoding, SolverError> {
        let mut work = WarmAbstractionWork::default();
        let term = self.abstract_warm_array_selects_inner(arena, term, &mut work)?;
        let mut congruence_lemmas = std::mem::take(&mut work.congruence_lemmas);
        let new_indices = self.warm_array_select_indices(&work.select_terms);
        self.add_warm_array_equality_observations(
            arena,
            existing_equalities,
            &new_indices,
            &mut work,
            &mut congruence_lemmas,
        )?;
        let mut prior = existing_selects.to_vec();
        for &select in &work.select_terms {
            for &other in &prior {
                if let Some(lemma) =
                    self.warm_array_congruence_lemma(arena, other, select, existing_equalities)?
                {
                    congruence_lemmas.push(lemma);
                }
            }
            prior.push(select);
        }
        let mut prior = existing_uf_apps.to_vec();
        for &app in &work.uf_app_terms {
            for &other in &prior {
                if let Some(lemma) = self.warm_uf_congruence_lemma(arena, other, app)? {
                    congruence_lemmas.push(lemma);
                }
            }
            prior.push(app);
        }
        Ok(WarmArrayEncoding {
            term,
            select_terms: work.select_terms,
            uf_app_terms: work.uf_app_terms,
            array_uf_app_terms: work.array_uf_app_terms,
            array_relation_flags: work.array_relation_flags,
            congruence_lemmas,
            structural_semantics: work.structural_semantics,
        })
    }

    fn abstract_warm_array_selects_inner(
        &mut self,
        arena: &mut TermArena,
        term: TermId,
        work: &mut WarmAbstractionWork,
    ) -> Result<TermId, SolverError> {
        if let Some(&abstracted) = work.memo.get(&term) {
            return Ok(abstracted);
        }

        if let Some(relation) = warm_array_relation_literal(arena, term)
            && relation.polarity == WarmArrayRelationPolarity::Equal
        {
            let flag = self.retain_warm_array_relation_flag(arena, relation, work)?;
            work.memo.insert(term, flag);
            return Ok(flag);
        }

        if let Some(select) = Self::supported_warm_array_select(arena, term) {
            let value_term = self.retain_warm_array_select(arena, term, select, work)?;
            work.memo.insert(term, value_term);
            return Ok(value_term);
        }

        if let Some(app) = Self::supported_warm_uf_app(arena, term)
            && app
                .args
                .iter()
                .all(|&arg| !needs_deferred_theory(arena, arg))
        {
            let abstracted = self.get_or_create_warm_uf_app(arena, term, app)?;
            if !work.uf_app_terms.contains(&term) {
                work.uf_app_terms.push(term);
            }
            work.memo.insert(term, abstracted.value_term);
            return Ok(abstracted.value_term);
        }

        let original_args = if let TermNode::App { args, .. } = arena.node(term) {
            args.to_vec()
        } else {
            work.memo.insert(term, term);
            return Ok(term);
        };
        let mut changed = false;
        let mut abstracted_args = Vec::with_capacity(original_args.len());
        for &arg in &original_args {
            let abstracted = self.abstract_warm_array_selects_inner(arena, arg, work)?;
            changed |= abstracted != arg;
            abstracted_args.push(abstracted);
        }
        let rebuilt = if changed {
            arena.rebuild_with_args(term, &abstracted_args)
        } else {
            term
        };
        let abstracted = if let Some(select) = Self::supported_warm_array_select(arena, rebuilt) {
            self.retain_warm_array_select(arena, rebuilt, select, work)?
        } else if let Some(app) = Self::supported_warm_uf_app(arena, rebuilt)
            && app
                .args
                .iter()
                .all(|&arg| !needs_deferred_theory(arena, arg))
        {
            let abstracted = self.get_or_create_warm_uf_app(arena, rebuilt, app)?;
            if !work.uf_app_terms.contains(&rebuilt) {
                work.uf_app_terms.push(rebuilt);
            }
            abstracted.value_term
        } else {
            rebuilt
        };
        work.memo.insert(term, abstracted);
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
        if !is_supported_warm_array_parent(arena, *array) {
            return None;
        }
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
        let projection_symbol = match arena.node(*array) {
            TermNode::Symbol(symbol) => Some(*symbol),
            _ => None,
        };
        let array_uf_app = supported_warm_array_uf_app_shape(arena, *array).then_some(*array);
        Some(WarmArraySelect {
            array_parent: *array,
            projection_symbol,
            array_uf_app,
            index: *index,
            encoded_index: *index,
            value_symbol: None,
            value_term: term,
            index_width,
            element,
            element_sort,
        })
    }

    fn retain_warm_array_select(
        &mut self,
        arena: &mut TermArena,
        term: TermId,
        mut select: WarmArraySelect,
        work: &mut WarmAbstractionWork,
    ) -> Result<TermId, SolverError> {
        select.encoded_index = self.abstract_warm_array_selects_inner(arena, select.index, work)?;
        if needs_deferred_theory(arena, select.encoded_index) {
            return Err(SolverError::Unsupported(format!(
                "warm array read #{} has an unsupported scalar index",
                term.index()
            )));
        }
        if let Some(app_term) = select.array_uf_app {
            let app = self.retain_warm_array_uf_app(arena, app_term, work)?;
            select.projection_symbol = Some(app.projection_symbol);
            if !work.array_uf_app_terms.contains(&app_term) {
                work.array_uf_app_terms.push(app_term);
            }
        } else if let Some(owner) = self.warm_structural_array_owners.get(&select.array_parent) {
            select.projection_symbol = Some(owner.projection_symbol);
        }
        let abstracted = self.get_or_create_warm_array_select(arena, term, select)?;
        if !work.select_terms.contains(&term) {
            work.select_terms.push(term);
        }
        if matches!(arena.node(abstracted.array_parent), TermNode::Symbol(_))
            || abstracted.array_uf_app.is_some()
        {
            return Ok(abstracted.value_term);
        }
        if self.warm_array_semantics.contains_key(&term) {
            self.extend_warm_array_semantic_dependencies(term, &mut work.select_terms);
            return Ok(abstracted.value_term);
        }
        if !work
            .structural_semantics
            .iter()
            .any(|semantic| semantic.select_term == term)
        {
            let semantic_rhs = Self::simplify_memory_for_warm_assertion(arena, term);
            if semantic_rhs == term {
                return Err(SolverError::Unsupported(format!(
                    "warm structural array read #{} has no supported exact summary",
                    term.index()
                )));
            }
            let abstracted_rhs =
                self.abstract_warm_array_selects_inner(arena, semantic_rhs, work)?;
            let definition = arena
                .eq(abstracted.value_term, abstracted_rhs)
                .map_err(|error| map_ir_error(&error))?;
            let dependencies = self.warm_array_select_dependencies(arena, abstracted_rhs);
            work.structural_semantics.push(WarmArraySemantic {
                select_term: term,
                definition,
                dependencies,
            });
        }
        Ok(abstracted.value_term)
    }

    fn extend_warm_array_semantic_dependencies(
        &self,
        select_term: TermId,
        select_terms: &mut Vec<TermId>,
    ) {
        let mut stack = vec![select_term];
        while let Some(term) = stack.pop() {
            let Some(semantic) = self.warm_array_semantics.get(&term) else {
                continue;
            };
            for &dependency in semantic.dependencies.iter().rev() {
                if !select_terms.contains(&dependency) {
                    select_terms.push(dependency);
                    stack.push(dependency);
                }
            }
        }
    }

    fn warm_array_select_dependencies(&self, arena: &TermArena, term: TermId) -> Vec<TermId> {
        let owners = self
            .warm_array_selects
            .iter()
            .map(|(&select_term, select)| (select.value_term, select_term))
            .collect::<HashMap<_, _>>();
        let mut dependencies = Vec::new();
        let mut seen = HashSet::new();
        let mut stack = vec![term];
        while let Some(current) = stack.pop() {
            if !seen.insert(current) {
                continue;
            }
            if let Some(&select_term) = owners.get(&current) {
                dependencies.push(select_term);
                continue;
            }
            if let TermNode::App { args, .. } = arena.node(current) {
                stack.extend(args.iter().rev().copied());
            }
        }
        dependencies.sort_by_key(|dependency| dependency.index());
        dependencies.dedup();
        dependencies
    }

    fn prepare_warm_array_equality(
        &mut self,
        arena: &mut TermArena,
        relation: WarmArrayRelation,
        existing_selects: &[TermId],
        existing_uf_apps: &[TermId],
        existing_equalities: &[WarmArrayEquality],
    ) -> Result<(WarmArrayEquality, WarmArrayEncoding), SolverError> {
        debug_assert_eq!(relation.polarity, WarmArrayRelationPolarity::Equal);
        let mut work = WarmAbstractionWork::default();
        let left = self.retain_warm_array_equality_operand(arena, relation.left, &mut work)?;
        let right = self.retain_warm_array_equality_operand(arena, relation.right, &mut work)?;
        let equality = WarmArrayEquality {
            left: left.owner,
            right: right.owner,
            left_parent: left.parent,
            right_parent: right.parent,
            left_structural: left.structural,
            right_structural: right.structural,
        };

        let newly_introduced_indices = self.warm_array_select_indices(&work.select_terms);
        let mut congruence_lemmas = std::mem::take(&mut work.congruence_lemmas);
        self.add_warm_array_equality_observations(
            arena,
            existing_equalities,
            &newly_introduced_indices,
            &mut work,
            &mut congruence_lemmas,
        )?;
        let mut equalities = existing_equalities.to_vec();
        equalities.push(equality);
        let mut observation_indices = self.warm_array_select_indices(existing_selects);
        extend_unique_terms(
            &mut observation_indices,
            &self.warm_array_select_indices(&work.select_terms),
        );
        if equality.has_structural_side() {
            collect_warm_store_indices(
                arena,
                equality.left_parent,
                Sort::BitVec(relation.index_width),
                &mut observation_indices,
            );
            collect_warm_store_indices(
                arena,
                equality.right_parent,
                Sort::BitVec(relation.index_width),
                &mut observation_indices,
            );
            let probe = self.warm_array_equality_probe(arena, relation)?;
            if !observation_indices.contains(&probe) {
                observation_indices.push(probe);
            }
        }
        observation_indices.sort_by_key(|term| term.index());
        observation_indices.dedup();

        self.add_warm_array_equality_observations(
            arena,
            std::slice::from_ref(&equality),
            &observation_indices,
            &mut work,
            &mut congruence_lemmas,
        )?;
        let mut all_selects = existing_selects.to_vec();
        all_selects.extend(work.select_terms.iter().copied());
        all_selects.sort_by_key(|term| term.index());
        all_selects.dedup();
        congruence_lemmas.extend(self.warm_array_congruence_lemmas_for_selects(
            arena,
            &all_selects,
            &equalities,
        )?);

        let mut prior_uf_apps = existing_uf_apps.to_vec();
        for &app in &work.uf_app_terms {
            for &other in &prior_uf_apps {
                if let Some(lemma) = self.warm_uf_congruence_lemma(arena, other, app)? {
                    congruence_lemmas.push(lemma);
                }
            }
            prior_uf_apps.push(app);
        }

        Ok((
            equality,
            WarmArrayEncoding {
                term: arena.bool_const(true),
                select_terms: work.select_terms,
                uf_app_terms: work.uf_app_terms,
                array_uf_app_terms: work.array_uf_app_terms,
                array_relation_flags: work.array_relation_flags,
                congruence_lemmas,
                structural_semantics: work.structural_semantics,
            },
        ))
    }

    fn retain_warm_array_relation_flag(
        &mut self,
        arena: &mut TermArena,
        relation: WarmArrayRelation,
        work: &mut WarmAbstractionWork,
    ) -> Result<TermId, SolverError> {
        debug_assert_eq!(relation.polarity, WarmArrayRelationPolarity::Equal);
        let flag_symbol = self.warm_array_relation_flag_symbol(arena, relation)?;
        let flag_term = arena.var(flag_symbol);

        let (equality, positive) =
            self.prepare_warm_array_equality(arena, relation, &[], &[], &[])?;
        let negative = self.abstract_warm_array_disequality(
            arena,
            WarmArrayRelation {
                polarity: WarmArrayRelationPolarity::Distinct,
                ..relation
            },
            &[],
            &[],
            &[],
        )?;

        for &lemma in &positive.congruence_lemmas {
            let guarded = guarded_warm_root(arena, flag_term, lemma, true)?;
            if !work.congruence_lemmas.contains(&guarded) {
                work.congruence_lemmas.push(guarded);
            }
        }
        let guarded_diff = guarded_warm_root(arena, flag_term, negative.term, false)?;
        if !work.congruence_lemmas.contains(&guarded_diff) {
            work.congruence_lemmas.push(guarded_diff);
        }
        extend_unique_terms(&mut work.congruence_lemmas, &negative.congruence_lemmas);

        extend_unique_terms(&mut work.select_terms, &positive.select_terms);
        extend_unique_terms(&mut work.uf_app_terms, &positive.uf_app_terms);
        extend_unique_terms(&mut work.array_uf_app_terms, &positive.array_uf_app_terms);
        for flag in positive.array_relation_flags {
            if !work
                .array_relation_flags
                .iter()
                .any(|existing| existing.flag == flag.flag)
            {
                work.array_relation_flags.push(flag);
            }
        }
        for semantic in positive.structural_semantics {
            if !work
                .structural_semantics
                .iter()
                .any(|existing| existing.select_term == semantic.select_term)
            {
                work.structural_semantics.push(semantic);
            }
        }

        extend_unique_terms(&mut work.select_terms, &negative.select_terms);
        extend_unique_terms(&mut work.uf_app_terms, &negative.uf_app_terms);
        extend_unique_terms(&mut work.array_uf_app_terms, &negative.array_uf_app_terms);
        for flag in negative.array_relation_flags {
            if !work
                .array_relation_flags
                .iter()
                .any(|existing| existing.flag == flag.flag)
            {
                work.array_relation_flags.push(flag);
            }
        }
        for semantic in negative.structural_semantics {
            if !work
                .structural_semantics
                .iter()
                .any(|existing| existing.select_term == semantic.select_term)
            {
                work.structural_semantics.push(semantic);
            }
        }

        if !work.array_relation_flags.iter().any(|flag| {
            flag.flag == flag_symbol
                && flag.equality.left == equality.left
                && flag.equality.right == equality.right
        }) {
            work.array_relation_flags.push(WarmArrayRelationFlag {
                flag: flag_symbol,
                equality,
            });
        }

        Ok(flag_term)
    }

    fn warm_array_select_indices(&self, selects: &[TermId]) -> Vec<TermId> {
        let mut indices = selects
            .iter()
            .filter_map(|term| self.warm_array_selects.get(term).map(|select| select.index))
            .collect::<Vec<_>>();
        indices.sort_by_key(|term| term.index());
        indices.dedup();
        indices
    }

    fn warm_array_equality_probe(
        &mut self,
        arena: &mut TermArena,
        relation: WarmArrayRelation,
    ) -> Result<TermId, SolverError> {
        if let Some(&symbol) = self
            .warm_array_equality_probe_symbols
            .get(&relation.literal)
        {
            let (_name, sort) = arena.symbol(symbol);
            if sort != Sort::BitVec(relation.index_width) {
                return Err(SolverError::Backend(format!(
                    "warm array equality #{} retained a probe of inconsistent sort",
                    relation.literal.index()
                )));
            }
            return Ok(arena.var(symbol));
        }
        let base_name = format!("!axeyum_warm_array_probe_{}", relation.literal.index());
        let name = fresh_internal_symbol_name(arena, &base_name);
        let symbol = arena
            .declare_internal(&name, Sort::BitVec(relation.index_width))
            .map_err(|error| map_ir_error(&error))?;
        self.internal_symbols.insert(symbol);
        self.warm_array_equality_probe_symbols
            .insert(relation.literal, symbol);
        Ok(arena.var(symbol))
    }

    fn warm_array_relation_flag_symbol(
        &mut self,
        arena: &mut TermArena,
        relation: WarmArrayRelation,
    ) -> Result<SymbolId, SolverError> {
        if let Some(&symbol) = self.warm_array_relation_flag_symbols.get(&relation.literal) {
            let (_name, sort) = arena.symbol(symbol);
            if sort != Sort::Bool {
                return Err(SolverError::Backend(format!(
                    "warm array relation #{} retained a non-Boolean flag",
                    relation.literal.index()
                )));
            }
            return Ok(symbol);
        }
        let base_name = format!("!axeyum_warm_array_rel_{}", relation.literal.index());
        let name = fresh_internal_symbol_name(arena, &base_name);
        let symbol = arena
            .declare_internal(&name, Sort::Bool)
            .map_err(|error| map_ir_error(&error))?;
        self.internal_symbols.insert(symbol);
        self.warm_array_relation_flag_symbols
            .insert(relation.literal, symbol);
        Ok(symbol)
    }

    fn add_warm_array_equality_observations(
        &mut self,
        arena: &mut TermArena,
        equalities: &[WarmArrayEquality],
        indices: &[TermId],
        work: &mut WarmAbstractionWork,
        roots: &mut Vec<TermId>,
    ) -> Result<(), SolverError> {
        for equality in equalities {
            if !equality.has_structural_side() {
                continue;
            }
            let index_sort = arena
                .sort_of(equality.left_parent)
                .array_sorts()
                .map(|sorts| sorts.0);
            for &index in indices {
                if Some(arena.sort_of(index)) != index_sort {
                    continue;
                }
                let left_read = arena
                    .select(equality.left_parent, index)
                    .map_err(|error| map_ir_error(&error))?;
                let right_read = arena
                    .select(equality.right_parent, index)
                    .map_err(|error| map_ir_error(&error))?;
                let left = self.abstract_warm_array_selects_inner(arena, left_read, work)?;
                let right = self.abstract_warm_array_selects_inner(arena, right_read, work)?;
                let root = arena
                    .eq(left, right)
                    .map_err(|error| map_ir_error(&error))?;
                if !roots.contains(&root) {
                    roots.push(root);
                }
            }
        }
        Ok(())
    }

    fn add_warm_array_relation_flag_observation_closure(
        &mut self,
        arena: &mut TermArena,
        existing_flags: &[WarmArrayRelationFlag],
        context_selects: &[TermId],
        encoding: &mut WarmArrayEncoding,
    ) -> Result<(), SolverError> {
        if existing_flags.is_empty() && encoding.array_relation_flags.is_empty() {
            return Ok(());
        }

        let new_indices = self.warm_array_select_indices(&encoding.select_terms);
        if !existing_flags.is_empty() && !new_indices.is_empty() {
            let mut work = WarmAbstractionWork::default();
            let mut roots = Vec::new();
            self.add_warm_array_relation_flag_observations(
                arena,
                existing_flags,
                &new_indices,
                &mut work,
                &mut roots,
            )?;
            extend_unique_terms(&mut work.congruence_lemmas, &roots);
            merge_warm_work_into_encoding(encoding, work);
        }

        if !encoding.array_relation_flags.is_empty() {
            let mut indices = self.warm_array_select_indices(context_selects);
            extend_unique_terms(&mut indices, &new_indices);
            if !indices.is_empty() {
                let flags = encoding.array_relation_flags.clone();
                let mut work = WarmAbstractionWork::default();
                let mut roots = Vec::new();
                self.add_warm_array_relation_flag_observations(
                    arena, &flags, &indices, &mut work, &mut roots,
                )?;
                extend_unique_terms(&mut work.congruence_lemmas, &roots);
                merge_warm_work_into_encoding(encoding, work);
            }
        }
        Ok(())
    }

    fn add_warm_array_relation_flag_observations(
        &mut self,
        arena: &mut TermArena,
        flags: &[WarmArrayRelationFlag],
        indices: &[TermId],
        work: &mut WarmAbstractionWork,
        roots: &mut Vec<TermId>,
    ) -> Result<(), SolverError> {
        for flag in flags {
            let index_sort = arena
                .sort_of(flag.equality.left_parent)
                .array_sorts()
                .map(|sorts| sorts.0);
            let flag_term = arena.var(flag.flag);
            for &index in indices {
                if Some(arena.sort_of(index)) != index_sort {
                    continue;
                }
                let left_read = arena
                    .select(flag.equality.left_parent, index)
                    .map_err(|error| map_ir_error(&error))?;
                let right_read = arena
                    .select(flag.equality.right_parent, index)
                    .map_err(|error| map_ir_error(&error))?;
                let left = self.abstract_warm_array_selects_inner(arena, left_read, work)?;
                let right = self.abstract_warm_array_selects_inner(arena, right_read, work)?;
                let read_equal = arena
                    .eq(left, right)
                    .map_err(|error| map_ir_error(&error))?;
                let guarded = guarded_warm_root(arena, flag_term, read_equal, true)?;
                if !roots.contains(&guarded) {
                    roots.push(guarded);
                }
            }
        }
        Ok(())
    }

    fn retain_warm_array_equality_operand(
        &mut self,
        arena: &mut TermArena,
        term: TermId,
        work: &mut WarmAbstractionWork,
    ) -> Result<WarmArrayEqualityOperand, SolverError> {
        if let TermNode::Symbol(symbol) = arena.node(term) {
            return Ok(WarmArrayEqualityOperand {
                owner: *symbol,
                parent: term,
                structural: None,
            });
        }
        if supported_warm_array_uf_app_shape(arena, term) {
            let app = self.retain_warm_array_uf_app(arena, term, work)?;
            if !work.array_uf_app_terms.contains(&term) {
                work.array_uf_app_terms.push(term);
            }
            return Ok(WarmArrayEqualityOperand {
                owner: app.projection_symbol,
                parent: term,
                structural: None,
            });
        }
        if !is_supported_warm_array_parent(arena, term) {
            return Err(SolverError::Unsupported(format!(
                "warm positive array equality operand #{} has no supported structural owner",
                term.index()
            )));
        }
        if let Some(owner) = self.warm_structural_array_owners.get(&term).cloned() {
            extend_unique_terms(&mut work.select_terms, &owner.select_terms);
            extend_unique_terms(&mut work.uf_app_terms, &owner.uf_app_terms);
            extend_unique_terms(&mut work.array_uf_app_terms, &owner.array_uf_app_terms);
            return Ok(WarmArrayEqualityOperand {
                owner: owner.projection_symbol,
                parent: term,
                structural: Some(owner.rewritten_term),
            });
        }

        let select_start = work.select_terms.len();
        let uf_start = work.uf_app_terms.len();
        let array_uf_start = work.array_uf_app_terms.len();
        let rewritten = self.rewrite_warm_structural_array_parent(arena, term, work)?;
        let base_name = format!("!axeyum_warm_array_owner_{}", term.index());
        let name = fresh_internal_symbol_name(arena, &base_name);
        let sort = arena.sort_of(term);
        let projection_symbol = arena
            .declare_internal(&name, sort)
            .map_err(|error| map_ir_error(&error))?;
        self.internal_symbols.insert(projection_symbol);
        let owner = WarmStructuralArrayOwner {
            projection_symbol,
            rewritten_term: rewritten,
            select_terms: work.select_terms[select_start..].to_vec(),
            uf_app_terms: work.uf_app_terms[uf_start..].to_vec(),
            array_uf_app_terms: work.array_uf_app_terms[array_uf_start..].to_vec(),
        };
        self.warm_structural_array_owners.insert(term, owner);
        for select in self.warm_array_selects.values_mut() {
            if select.array_parent == term {
                select.projection_symbol = Some(projection_symbol);
            }
        }
        Ok(WarmArrayEqualityOperand {
            owner: projection_symbol,
            parent: term,
            structural: Some(rewritten),
        })
    }

    fn rewrite_warm_structural_array_parent(
        &mut self,
        arena: &mut TermArena,
        term: TermId,
        work: &mut WarmAbstractionWork,
    ) -> Result<TermId, SolverError> {
        let node = arena.node(term).clone();
        match node {
            TermNode::Symbol(_) => Ok(term),
            TermNode::App {
                op: Op::Apply(_), ..
            } if supported_warm_array_uf_app_shape(arena, term) => {
                let app = self.retain_warm_array_uf_app(arena, term, work)?;
                if !work.array_uf_app_terms.contains(&term) {
                    work.array_uf_app_terms.push(term);
                }
                Ok(arena.var(app.projection_symbol))
            }
            TermNode::App {
                op: Op::ConstArray { .. },
                args,
            } => {
                let [value] = args.as_ref() else {
                    return Err(SolverError::Backend(
                        "warm constant-array owner had invalid arity".to_owned(),
                    ));
                };
                let value = self.abstract_warm_array_selects_inner(arena, *value, work)?;
                Ok(arena.rebuild_with_args(term, &[value]))
            }
            TermNode::App {
                op: Op::Store,
                args,
            } => {
                let [base, index, value] = args.as_ref() else {
                    return Err(SolverError::Backend(
                        "warm store-array owner had invalid arity".to_owned(),
                    ));
                };
                let base = self.rewrite_warm_structural_array_parent(arena, *base, work)?;
                let index = self.abstract_warm_array_selects_inner(arena, *index, work)?;
                let value = self.abstract_warm_array_selects_inner(arena, *value, work)?;
                Ok(arena.rebuild_with_args(term, &[base, index, value]))
            }
            TermNode::App { op: Op::Ite, args } => {
                let [condition, then_array, else_array] = args.as_ref() else {
                    return Err(SolverError::Backend(
                        "warm array-ITE owner had invalid arity".to_owned(),
                    ));
                };
                let condition = self.abstract_warm_array_selects_inner(arena, *condition, work)?;
                let then_array =
                    self.rewrite_warm_structural_array_parent(arena, *then_array, work)?;
                let else_array =
                    self.rewrite_warm_structural_array_parent(arena, *else_array, work)?;
                Ok(arena.rebuild_with_args(term, &[condition, then_array, else_array]))
            }
            _ => Err(SolverError::Unsupported(format!(
                "warm structural array owner #{} uses an unsupported parent",
                term.index()
            ))),
        }
    }

    fn abstract_warm_array_disequality(
        &mut self,
        arena: &mut TermArena,
        relation: WarmArrayRelation,
        existing_selects: &[TermId],
        existing_uf_apps: &[TermId],
        existing_equalities: &[WarmArrayEquality],
    ) -> Result<WarmArrayEncoding, SolverError> {
        debug_assert_eq!(relation.polarity, WarmArrayRelationPolarity::Distinct);
        let diff_symbol = if let Some(&symbol) = self.warm_array_diff_symbols.get(&relation.literal)
        {
            let (_name, sort) = arena.symbol(symbol);
            if sort != Sort::BitVec(relation.index_width) {
                return Err(SolverError::Backend(format!(
                    "warm array relation #{} retained a diff witness of inconsistent sort",
                    relation.literal.index()
                )));
            }
            symbol
        } else {
            let base_name = format!("!axeyum_warm_array_diff_{}", relation.literal.index());
            let name = fresh_internal_symbol_name(arena, &base_name);
            let symbol = arena
                .declare_internal(&name, Sort::BitVec(relation.index_width))
                .map_err(|error| map_ir_error(&error))?;
            self.internal_symbols.insert(symbol);
            self.warm_array_diff_symbols
                .insert(relation.literal, symbol);
            symbol
        };
        let diff = arena.var(diff_symbol);
        let left_read = arena
            .select(relation.left, diff)
            .map_err(|error| map_ir_error(&error))?;
        let right_read = arena
            .select(relation.right, diff)
            .map_err(|error| map_ir_error(&error))?;
        let reads_equal = arena
            .eq(left_read, right_read)
            .map_err(|error| map_ir_error(&error))?;
        let witness_root = arena
            .not(reads_equal)
            .map_err(|error| map_ir_error(&error))?;
        self.abstract_warm_array_selects(
            arena,
            witness_root,
            existing_selects,
            existing_uf_apps,
            existing_equalities,
        )
    }

    fn get_or_create_warm_array_select(
        &mut self,
        arena: &mut TermArena,
        term: TermId,
        mut select: WarmArraySelect,
    ) -> Result<WarmArraySelect, SolverError> {
        if let Some(mut existing) = self.warm_array_selects.get(&term).copied() {
            if existing.projection_symbol.is_none() && select.projection_symbol.is_some() {
                existing.projection_symbol = select.projection_symbol;
                self.warm_array_selects.insert(term, existing);
            } else if existing.projection_symbol != select.projection_symbol
                && select.projection_symbol.is_some()
            {
                return Err(SolverError::Backend(format!(
                    "warm array read #{} acquired inconsistent projection owners",
                    term.index()
                )));
            }
            return Ok(existing);
        }
        let base_name = format!("!axeyum_warm_select_{}", term.index());
        let name = fresh_internal_symbol_name(arena, &base_name);
        let value_symbol = arena
            .declare_internal(&name, select.element_sort)
            .map_err(|error| map_ir_error(&error))?;
        let value_term = arena.var(value_symbol);
        self.internal_symbols.insert(value_symbol);
        select.value_symbol = Some(value_symbol);
        select.value_term = value_term;
        self.warm_array_selects.insert(term, select);
        Ok(select)
    }

    fn warm_array_congruence_lemma(
        &self,
        arena: &mut TermArena,
        left: TermId,
        right: TermId,
        equalities: &[WarmArrayEquality],
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
        let same_parent_guard = if left.array_parent == right.array_parent
            || left
                .projection_symbol
                .zip(right.projection_symbol)
                .is_some_and(|(left, right)| warm_array_symbols_equal(left, right, equalities))
        {
            None
        } else if let (Some(left_app), Some(right_app)) = (left.array_uf_app, right.array_uf_app) {
            let Some(left_app) = self.warm_array_uf_apps.get(&left_app) else {
                return Ok(None);
            };
            let Some(right_app) = self.warm_array_uf_apps.get(&right_app) else {
                return Ok(None);
            };
            if left_app.func != right_app.func {
                return Ok(None);
            }
            conjunction_of_equalities(arena, &left_app.encoded_args, &right_app.encoded_args)?
        } else {
            return Ok(None);
        };
        let same_index = arena
            .eq(left.encoded_index, right.encoded_index)
            .map_err(|error| map_ir_error(&error))?;
        let same_value = arena
            .eq(left.value_term, right.value_term)
            .map_err(|error| map_ir_error(&error))?;
        let same_inputs = match same_parent_guard {
            Some(same_parent) => arena
                .and(same_parent, same_index)
                .map_err(|error| map_ir_error(&error))?,
            None => same_index,
        };
        let distinct_inputs = arena
            .not(same_inputs)
            .map_err(|error| map_ir_error(&error))?;
        arena
            .or(distinct_inputs, same_value)
            .map(Some)
            .map_err(|error| map_ir_error(&error))
    }

    fn warm_array_congruence_lemmas_for_selects(
        &self,
        arena: &mut TermArena,
        selects: &[TermId],
        equalities: &[WarmArrayEquality],
    ) -> Result<Vec<TermId>, SolverError> {
        let mut lemmas = Vec::new();
        for (i, &left) in selects.iter().enumerate() {
            for &right in &selects[i + 1..] {
                if let Some(lemma) =
                    self.warm_array_congruence_lemma(arena, left, right, equalities)?
                {
                    lemmas.push(lemma);
                }
            }
        }
        Ok(lemmas)
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

    fn retain_warm_array_uf_app(
        &mut self,
        arena: &mut TermArena,
        term: TermId,
        work: &mut WarmAbstractionWork,
    ) -> Result<WarmArrayUfApp, SolverError> {
        let TermNode::App {
            op: Op::Apply(func),
            args,
            ..
        } = arena.node(term)
        else {
            return Err(SolverError::Backend(format!(
                "warm array UF parent #{} is not an application",
                term.index()
            )));
        };
        let func = *func;
        let args = args.to_vec();
        let (_name, params, result_sort) = arena.function(func);
        let param_count = params.len();
        if !supported_warm_array_uf_app_shape(arena, term) {
            return Err(SolverError::Unsupported(format!(
                "warm array UF parent #{} has an unsupported signature",
                term.index()
            )));
        }

        let mut encoded_args = Vec::with_capacity(args.len());
        for &arg in &args {
            let encoded = self.abstract_warm_array_selects_inner(arena, arg, work)?;
            if needs_deferred_theory(arena, encoded) {
                return Err(SolverError::Unsupported(format!(
                    "warm array UF parent #{} has an unsupported scalar argument",
                    term.index()
                )));
            }
            encoded_args.push(encoded);
        }
        if let Some(existing) = self.warm_array_uf_apps.get(&term) {
            if existing.func != func
                || existing.args != args
                || existing.encoded_args != encoded_args
                || existing.result_sort != result_sort
            {
                return Err(SolverError::Backend(format!(
                    "warm array UF parent #{} was retained inconsistently",
                    term.index()
                )));
            }
            return Ok(existing.clone());
        }

        debug_assert_eq!(args.len(), param_count);
        let base_name = format!("!axeyum_warm_array_uf_{}", term.index());
        let name = fresh_internal_symbol_name(arena, &base_name);
        let projection_symbol = arena
            .declare_internal(&name, result_sort)
            .map_err(|error| map_ir_error(&error))?;
        self.internal_symbols.insert(projection_symbol);
        let app = WarmArrayUfApp {
            func,
            args,
            encoded_args,
            projection_symbol,
            result_sort,
        };
        self.warm_array_uf_apps.insert(term, app.clone());
        Ok(app)
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
            .declare_internal(&name, app.result_sort)
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
        let mut active_equalities = self.active_warm_array_equalities();
        let mut active_relation_flags = self.active_warm_array_relation_flags();
        let mut simplified = Vec::with_capacity(assumptions.len());
        for &term in assumptions {
            if arena.sort_of(term) != Sort::Bool {
                return Err(SolverError::NonBooleanAssertion(term));
            }
            let encoded = Self::simplify_memory_for_retained_warm_assertion(arena, term);
            if !Self::term_supported_by_warm_abstraction(arena, encoded) {
                return Err(SolverError::Unsupported(format!(
                    "array/UF assumption #{} is outside the retained warm abstraction",
                    term.index()
                )));
            }
            let relation = warm_array_relation_literal(arena, encoded);
            if !self.warm_array_equality_observation_budget_holds(
                arena,
                encoded,
                relation,
                &active_selects,
                &active_equalities,
            ) {
                return Err(SolverError::Unsupported(format!(
                    "array/UF assumption #{} exceeds the retained structural-equality observation budget",
                    term.index()
                )));
            }
            if relation
                .is_some_and(|relation| relation.polarity == WarmArrayRelationPolarity::Equal)
            {
                let (equality, mut prepared) = self.prepare_warm_array_equality(
                    arena,
                    relation.expect("checked as positive relation"),
                    &active_selects,
                    &active_uf_apps,
                    &active_equalities,
                )?;
                self.add_warm_array_relation_flag_observation_closure(
                    arena,
                    &active_relation_flags,
                    &active_selects,
                    &mut prepared,
                )?;
                self.retain_warm_semantics(&prepared.structural_semantics)?;
                active_equalities.push(equality);
                active_selects.extend(prepared.select_terms.iter().copied());
                active_uf_apps.extend(prepared.uf_app_terms.iter().copied());
                active_relation_flags.extend(prepared.array_relation_flags.iter().copied());
                simplified.push(OneShotAssumption {
                    original: term,
                    encoded: arena.bool_const(true),
                    warm_array_selects: prepared.select_terms,
                    warm_uf_apps: prepared.uf_app_terms,
                    warm_array_uf_apps: prepared.array_uf_app_terms,
                    warm_array_equalities: vec![equality],
                    warm_array_relation_flags: prepared.array_relation_flags,
                    congruence_lemmas: prepared.congruence_lemmas,
                });
                continue;
            }
            let mut encoded = match relation {
                Some(relation) => self.abstract_warm_array_disequality(
                    arena,
                    relation,
                    &active_selects,
                    &active_uf_apps,
                    &active_equalities,
                )?,
                None => self.abstract_warm_array_selects(
                    arena,
                    encoded,
                    &active_selects,
                    &active_uf_apps,
                    &active_equalities,
                )?,
            };
            self.add_warm_array_relation_flag_observation_closure(
                arena,
                &active_relation_flags,
                &active_selects,
                &mut encoded,
            )?;
            self.retain_warm_semantics(&encoded.structural_semantics)?;
            active_selects.extend(encoded.select_terms.iter().copied());
            active_uf_apps.extend(encoded.uf_app_terms.iter().copied());
            active_relation_flags.extend(encoded.array_relation_flags.iter().copied());
            simplified.push(OneShotAssumption {
                original: term,
                encoded: encoded.term,
                warm_array_selects: encoded.select_terms,
                warm_uf_apps: encoded.uf_app_terms,
                warm_array_uf_apps: encoded.array_uf_app_terms,
                warm_array_equalities: Vec::new(),
                warm_array_relation_flags: encoded.array_relation_flags,
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
    ) -> Result<IncrementalSolveOutcome, SolverError> {
        let assumptions = assumptions
            .iter()
            .map(|&term| OneShotAssumption {
                original: term,
                encoded: term,
                warm_array_selects: Vec::new(),
                warm_uf_apps: Vec::new(),
                warm_array_uf_apps: Vec::new(),
                warm_array_equalities: Vec::new(),
                warm_array_relation_flags: Vec::new(),
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
    ) -> Result<IncrementalSolveOutcome, SolverError> {
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

        let one_shot = collect_warm_one_shot_terms(assumptions);
        let active_selects = self.active_warm_array_select_closure(&one_shot.selects);

        let deadline = self
            .config
            .timeout
            .and_then(|timeout| Instant::now().checked_add(timeout));
        let mut refinement_rounds = 0usize;
        loop {
            if deadline.is_some_and(|deadline| Instant::now() >= deadline) {
                return Ok(IncrementalSolveOutcome::unknown(UnknownReason {
                    kind: UnknownKind::Timeout,
                    detail: "warm structural refinement reached the shared query deadline"
                        .to_owned(),
                }));
            }
            let timeout =
                deadline.map(|deadline| deadline.saturating_duration_since(Instant::now()));
            let result = self
                .cnf
                .solve(&active, timeout)
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
                    match self.check_warm_candidate(
                        arena,
                        &reconstructed,
                        &active_selects,
                        &one_shot,
                        assumptions,
                        deadline,
                    )? {
                        WarmCandidateCheck::Refine(violated) => {
                            if refinement_rounds >= MAX_WARM_STRUCTURAL_REFINEMENT_ROUNDS {
                                return Ok(IncrementalSolveOutcome::unknown(UnknownReason {
                                    kind: UnknownKind::ResourceLimit,
                                    detail: format!(
                                        "warm structural refinement exceeded {MAX_WARM_STRUCTURAL_REFINEMENT_ROUNDS} candidate rounds"
                                    ),
                                }));
                            }
                            if let Some(reason) =
                                self.activate_warm_array_semantics(arena, violated, deadline)?
                            {
                                return Ok(IncrementalSolveOutcome::unknown(reason));
                            }
                            refinement_rounds += 1;
                            self.warm_array_refinement_rounds =
                                self.warm_array_refinement_rounds.saturating_add(1);
                        }
                        WarmCandidateCheck::Sat(model) => {
                            return Ok(IncrementalSolveOutcome::sat(model));
                        }
                        WarmCandidateCheck::Unknown(reason) => {
                            return Ok(IncrementalSolveOutcome::unknown(reason));
                        }
                    }
                }
                SatResult::Unsat(evidence) => {
                    return Ok(self.warm_unsat_outcome(
                        &evidence,
                        assumptions,
                        &assumption_selectors,
                    ));
                }
                SatResult::Unknown(reason) => {
                    let kind = if reason.detail.contains("timeout") {
                        UnknownKind::Timeout
                    } else {
                        UnknownKind::Other
                    };
                    return Ok(IncrementalSolveOutcome::unknown(UnknownReason {
                        kind,
                        detail: reason.detail,
                    }));
                }
            }
        }
    }

    fn active_warm_array_select_closure(&self, one_shot_selects: &[TermId]) -> Vec<TermId> {
        let mut active = self.active_warm_array_select_terms();
        active.extend_from_slice(one_shot_selects);
        for select_term in active.clone() {
            self.extend_warm_array_semantic_dependencies(select_term, &mut active);
        }
        active.sort_by_key(|term| term.index());
        active.dedup();
        active
    }

    fn check_warm_candidate(
        &self,
        arena: &TermArena,
        assignment: &Assignment,
        active_selects: &[TermId],
        one_shot: &WarmOneShotTerms,
        assumptions: &[OneShotAssumption],
        deadline: Option<Instant>,
    ) -> Result<WarmCandidateCheck, SolverError> {
        let violated =
            match self.violated_warm_array_semantics(arena, assignment, active_selects, deadline) {
                Ok(violated) => violated,
                Err(reason) => return Ok(WarmCandidateCheck::Unknown(reason)),
            };
        if !violated.is_empty() {
            return Ok(WarmCandidateCheck::Refine(violated));
        }
        let model =
            match self.complete_model_with_warm_theories(arena, assignment, one_shot, deadline) {
                Ok(model) => model,
                Err(reason) => return Ok(WarmCandidateCheck::Unknown(reason)),
            };
        let original_assumptions = original_assumptions(assumptions);
        if let Some(reason) = self.replay(arena, &original_assumptions, &model)? {
            return Ok(WarmCandidateCheck::Unknown(reason));
        }
        Ok(WarmCandidateCheck::Sat(model))
    }

    fn activate_warm_array_semantics(
        &mut self,
        arena: &TermArena,
        violated: Vec<WarmArraySemantic>,
        deadline: Option<Instant>,
    ) -> Result<Option<UnknownReason>, SolverError> {
        for semantic in violated {
            if !self.encode_warm_root_with_deadline(arena, semantic.definition, None, deadline)? {
                return Ok(Some(UnknownReason {
                    kind: UnknownKind::Timeout,
                    detail: format!(
                        "warm structural definition for read #{} exceeded the shared query deadline",
                        semantic.select_term.index()
                    ),
                }));
            }
            self.warm_array_semantics_encoded
                .insert(semantic.select_term);
        }
        Ok(None)
    }

    fn warm_unsat_outcome(
        &self,
        evidence: &SatUnsatEvidence,
        assumptions: &[OneShotAssumption],
        assumption_selectors: &[CnfVar],
    ) -> IncrementalSolveOutcome {
        let mut core = Vec::new();
        for lit in &evidence.failed_assumptions {
            if let Some(i) = assumption_selectors
                .iter()
                .position(|&selector| selector == lit.var())
            {
                core.push(assumptions[i].original);
            }
        }
        if core.is_empty() && !assumptions.is_empty() {
            core.extend(original_assumptions(assumptions));
        }
        IncrementalSolveOutcome {
            result: CheckResult::Unsat,
            assumption_core: core,
            active_assertion_core: self.active_assertion_core(&evidence.failed_assumptions),
        }
    }

    fn violated_warm_array_semantics(
        &self,
        arena: &TermArena,
        assignment: &Assignment,
        active_selects: &[TermId],
        deadline: Option<Instant>,
    ) -> Result<Vec<WarmArraySemantic>, UnknownReason> {
        let candidate = complete_warm_candidate_assignment(arena, assignment);
        let mut violated = Vec::new();
        for &select_term in active_selects {
            if deadline.is_some_and(|deadline| Instant::now() >= deadline) {
                return Err(UnknownReason {
                    kind: UnknownKind::Timeout,
                    detail: "warm structural candidate checking reached the shared query deadline"
                        .to_owned(),
                });
            }
            if self.warm_array_semantics_encoded.contains(&select_term) {
                continue;
            }
            let Some(semantic) = self.warm_array_semantics.get(&select_term) else {
                continue;
            };
            match eval(arena, semantic.definition, &candidate) {
                Ok(Value::Bool(true)) => {}
                Ok(Value::Bool(false)) => violated.push(semantic.clone()),
                Ok(value) => {
                    return Err(UnknownReason {
                        kind: UnknownKind::Other,
                        detail: format!(
                            "warm structural definition for read #{} evaluated to non-Boolean {value}",
                            select_term.index()
                        ),
                    });
                }
                Err(error) => {
                    return Err(UnknownReason {
                        kind: UnknownKind::Other,
                        detail: format!(
                            "warm structural definition for read #{} could not be evaluated: {error}",
                            select_term.index()
                        ),
                    });
                }
            }
        }
        Ok(violated)
    }

    fn active_assertion_core(&self, failed_assumptions: &[axeyum_cnf::CnfLit]) -> Vec<TermId> {
        let failed_selectors = failed_assumptions
            .iter()
            .map(|literal| literal.var())
            .collect::<HashSet<_>>();
        let mut core = Vec::new();
        for frame in &self.frames {
            if frame
                .selector
                .is_none_or(|selector| failed_selectors.contains(&selector))
            {
                core.extend(frame.assertions.iter().copied());
            }
        }
        if core.is_empty() && self.frames.iter().any(|frame| !frame.assertions.is_empty()) {
            core.extend(
                self.frames
                    .iter()
                    .flat_map(|frame| frame.assertions.iter().copied()),
            );
        }
        core
    }

    fn complete_model_with_warm_theories(
        &self,
        arena: &TermArena,
        assignment: &Assignment,
        one_shot: &WarmOneShotTerms,
        deadline: Option<Instant>,
    ) -> Result<Model, UnknownReason> {
        let mut model = complete_model_filtered(arena, assignment, &self.internal_symbols);
        self.project_warm_array_selects(arena, assignment, &one_shot.selects, &mut model)?;
        self.project_warm_uf_apps(arena, assignment, &one_shot.uf_apps, &mut model)?;
        self.project_warm_array_equalities(
            arena,
            assignment,
            &one_shot.selects,
            &one_shot.array_equalities,
            &one_shot.array_relation_flags,
            &mut model,
            deadline,
        )?;
        self.project_warm_array_uf_apps(arena, assignment, &one_shot.array_uf_apps, &mut model)?;
        Ok(filter_internal_model(&model, &self.internal_symbols))
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
            let Some(array_symbol) = select.projection_symbol else {
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
                array_symbol,
                &select_value,
                &index_value,
                model,
            )?;
            model.set(array_symbol, array_value);
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

    fn project_warm_array_uf_apps(
        &self,
        arena: &TermArena,
        assignment: &Assignment,
        one_shot_array_uf_apps: &[TermId],
        model: &mut Model,
    ) -> Result<(), UnknownReason> {
        let mut app_terms = self.active_warm_array_uf_app_terms();
        app_terms.extend_from_slice(one_shot_array_uf_apps);
        app_terms.sort_by_key(|term| term.index());
        app_terms.dedup();

        let mut groups: Vec<WarmArrayUfProjectionGroup> = Vec::new();
        for app_term in app_terms {
            let Some(app) = self.warm_array_uf_apps.get(&app_term) else {
                return Err(UnknownReason {
                    kind: UnknownKind::Other,
                    detail: format!(
                        "warm array UF application #{} lost its retained metadata",
                        app_term.index()
                    ),
                });
            };
            let model_assignment =
                assignment_with_internal(arena, model, assignment, &self.internal_symbols);
            let (_name, params, result_sort) = arena.function(app.func);
            let mut args = Vec::with_capacity(app.encoded_args.len());
            for (&arg, &sort) in app.encoded_args.iter().zip(params) {
                let value = eval(arena, arg, &model_assignment).map_err(|error| UnknownReason {
                    kind: UnknownKind::Other,
                    detail: format!(
                        "warm array UF argument #{} for application #{} could not be evaluated: {error}",
                        arg.index(),
                        app_term.index()
                    ),
                })?;
                let value = normalize_bitvec_value(value);
                if value.sort() != sort {
                    return Err(UnknownReason {
                        kind: UnknownKind::Other,
                        detail: format!(
                            "warm array UF argument #{} for application #{} evaluated to {value} of wrong sort",
                            arg.index(),
                            app_term.index()
                        ),
                    });
                }
                args.push(value);
            }
            debug_assert_eq!(result_sort, app.result_sort);
            if let Some(group) = groups
                .iter_mut()
                .find(|group| group.func == app.func && group.args == args)
            {
                group.projection_symbols.push(app.projection_symbol);
            } else {
                groups.push(WarmArrayUfProjectionGroup {
                    func: app.func,
                    args,
                    projection_symbols: vec![app.projection_symbol],
                    result_sort: app.result_sort,
                });
            }
        }

        for group in groups {
            let result = merge_equal_array_group(arena, model, &group.projection_symbols)?;
            let (_name, params, result_sort) = arena.function(group.func);
            debug_assert_eq!(result_sort, group.result_sort);
            let interpretation = match model.function(group.func).cloned() {
                Some(existing) if existing.uses_value_storage() => existing,
                _ => {
                    let default =
                        well_founded_default(arena, result_sort).ok_or_else(|| UnknownReason {
                            kind: UnknownKind::Other,
                            detail: format!(
                                "warm array UF result sort {result_sort} has no default value"
                            ),
                        })?;
                    FuncValue::constant_value(params.to_vec(), result_sort, default)
                }
            };
            model.set_function(group.func, interpretation.define_value(&group.args, result));
        }
        Ok(())
    }

    #[allow(clippy::too_many_arguments)]
    fn project_warm_array_equalities(
        &self,
        arena: &TermArena,
        assignment: &Assignment,
        one_shot_selects: &[TermId],
        one_shot_array_equalities: &[WarmArrayEquality],
        one_shot_array_relation_flags: &[WarmArrayRelationFlag],
        model: &mut Model,
        deadline: Option<Instant>,
    ) -> Result<(), UnknownReason> {
        let mut equalities = self.active_warm_array_equalities();
        equalities.extend_from_slice(one_shot_array_equalities);
        for flag in self
            .active_warm_array_relation_flags()
            .into_iter()
            .chain(one_shot_array_relation_flags.iter().copied())
        {
            match assignment.get(flag.flag) {
                Some(Value::Bool(true)) => equalities.push(flag.equality),
                Some(Value::Bool(false)) | None => {}
                Some(value) => {
                    return Err(UnknownReason {
                        kind: UnknownKind::Other,
                        detail: format!(
                            "warm array relation flag #{} evaluated to non-Boolean {value}",
                            flag.flag.index()
                        ),
                    });
                }
            }
        }
        if equalities.is_empty() {
            return Ok(());
        }

        for group in warm_array_equality_groups(&equalities) {
            if group.len() < 2 {
                continue;
            }
            let merged = merge_equal_array_group(arena, model, &group)?;
            for symbol in group {
                model.set(symbol, merged.clone());
            }
        }
        self.realize_warm_structural_array_equalities(
            arena,
            assignment,
            one_shot_selects,
            &equalities,
            model,
            deadline,
        )
    }

    fn realize_warm_structural_array_equalities(
        &self,
        arena: &TermArena,
        assignment: &Assignment,
        one_shot_selects: &[TermId],
        equalities: &[WarmArrayEquality],
        model: &mut Model,
        deadline: Option<Instant>,
    ) -> Result<(), UnknownReason> {
        let equations = equalities
            .iter()
            .flat_map(|equality| {
                [
                    equality.left_structural.map(|term| (equality.left, term)),
                    equality.right_structural.map(|term| (equality.right, term)),
                ]
            })
            .flatten()
            .collect::<Vec<_>>();
        if equations.is_empty() {
            return Ok(());
        }

        let groups = warm_array_equality_groups(equalities);
        let active_selects = self.active_warm_array_select_closure(one_shot_selects);
        let mut projected =
            assignment_with_internal(arena, model, assignment, &self.internal_symbols);
        let max_rounds = equations
            .len()
            .saturating_mul(2)
            .clamp(1, MAX_WARM_STRUCTURAL_REFINEMENT_ROUNDS);
        for _round in 0..max_rounds {
            check_warm_structural_projection_deadline(deadline)?;
            let mut mismatches = 0usize;
            let mut progressed = false;
            for &(owner, structural) in &equations {
                check_warm_structural_projection_deadline(deadline)?;
                let owner_value = warm_array_owner_value(owner, &projected)?;
                let structural_value = eval_warm_structural_term(arena, structural, &projected)?;
                if owner_value == structural_value {
                    continue;
                }
                mismatches += 1;
                if self.try_realize_warm_structural_equation(
                    arena,
                    &active_selects,
                    &groups,
                    owner,
                    structural,
                    &owner_value,
                    &structural_value,
                    &mut projected,
                    deadline,
                )? {
                    progressed = true;
                }
            }
            if mismatches == 0 {
                break;
            }
            if !progressed {
                return Err(UnknownReason {
                    kind: UnknownKind::Other,
                    detail: "warm structural array equality could not realize a total model"
                        .to_owned(),
                });
            }
        }
        for &(owner, structural) in &equations {
            check_warm_structural_projection_deadline(deadline)?;
            if warm_array_owner_value(owner, &projected)?
                != eval_warm_structural_term(arena, structural, &projected)?
            {
                return Err(UnknownReason {
                    kind: UnknownKind::ResourceLimit,
                    detail: "warm structural array equality did not converge within its fixed-point bound"
                        .to_owned(),
                });
            }
        }

        for (symbol, _name, sort) in arena.symbols() {
            if matches!(sort, Sort::Array { .. })
                && let Some(value) = projected.get(symbol)
            {
                model.set(symbol, value);
            }
        }
        Ok(())
    }

    #[allow(clippy::too_many_arguments)]
    fn try_realize_warm_structural_equation(
        &self,
        arena: &TermArena,
        active_selects: &[TermId],
        groups: &[Vec<SymbolId>],
        owner: SymbolId,
        structural: TermId,
        owner_value: &Value,
        structural_value: &Value,
        projected: &mut Assignment,
        deadline: Option<Instant>,
    ) -> Result<bool, UnknownReason> {
        let mut candidate = projected.clone();
        if self.assign_warm_array_owner_class(
            arena,
            active_selects,
            groups,
            owner,
            structural_value,
            &mut candidate,
        )? && warm_array_owner_value(owner, &candidate)?
            == eval_warm_structural_term(arena, structural, &candidate)?
        {
            *projected = candidate;
            return Ok(true);
        }

        let mut candidate = projected.clone();
        if self.realize_warm_structural_array_term(
            arena,
            active_selects,
            groups,
            structural,
            owner_value,
            &mut candidate,
            deadline,
        )? == WarmStructuralRealization::Changed
            && warm_array_owner_value(owner, &candidate)?
                == eval_warm_structural_term(arena, structural, &candidate)?
        {
            *projected = candidate;
            return Ok(true);
        }
        Ok(false)
    }

    #[allow(clippy::too_many_arguments)]
    fn realize_warm_structural_array_term(
        &self,
        arena: &TermArena,
        active_selects: &[TermId],
        groups: &[Vec<SymbolId>],
        term: TermId,
        target: &Value,
        projected: &mut Assignment,
        deadline: Option<Instant>,
    ) -> Result<WarmStructuralRealization, UnknownReason> {
        let mut current = term;
        for _step in 0..MAX_WARM_STRUCTURAL_ARRAY_NODES {
            check_warm_structural_projection_deadline(deadline)?;
            if eval_warm_structural_term(arena, current, projected)? == *target {
                return Ok(WarmStructuralRealization::Unchanged);
            }
            match arena.node(current) {
                TermNode::Symbol(owner) if matches!(arena.sort_of(current), Sort::Array { .. }) => {
                    return if self.assign_warm_array_owner_class(
                        arena,
                        active_selects,
                        groups,
                        *owner,
                        target,
                        projected,
                    )? {
                        Ok(WarmStructuralRealization::Changed)
                    } else {
                        Ok(WarmStructuralRealization::Incompatible)
                    };
                }
                TermNode::App {
                    op: Op::Store,
                    args,
                } => {
                    let index = eval_warm_structural_term(arena, args[1], projected)?;
                    let element = eval_warm_structural_term(arena, args[2], projected)?;
                    if warm_array_value_select(target, &index)? != element {
                        return Ok(WarmStructuralRealization::Incompatible);
                    }
                    current = args[0];
                }
                TermNode::App { op: Op::Ite, args } => {
                    let condition = eval_warm_structural_term(arena, args[0], projected)?;
                    let Value::Bool(condition) = condition else {
                        return Err(UnknownReason {
                            kind: UnknownKind::Other,
                            detail: "warm structural array ITE guard evaluated to a non-Boolean"
                                .to_owned(),
                        });
                    };
                    current = if condition { args[1] } else { args[2] };
                }
                _ => return Ok(WarmStructuralRealization::Incompatible),
            }
        }
        Ok(WarmStructuralRealization::Incompatible)
    }

    fn assign_warm_array_owner_class(
        &self,
        arena: &TermArena,
        active_selects: &[TermId],
        groups: &[Vec<SymbolId>],
        owner: SymbolId,
        target: &Value,
        projected: &mut Assignment,
    ) -> Result<bool, UnknownReason> {
        let members = groups
            .iter()
            .find(|group| group.contains(&owner))
            .map_or_else(|| vec![owner], Clone::clone);
        for &select_term in active_selects {
            let Some(select) = self.warm_array_selects.get(&select_term).copied() else {
                continue;
            };
            if !select
                .projection_symbol
                .is_some_and(|symbol| members.contains(&symbol))
            {
                continue;
            }
            let Some(value_symbol) = select.value_symbol else {
                return Err(UnknownReason {
                    kind: UnknownKind::Other,
                    detail: format!(
                        "warm structural equality read #{} lost its scalar owner",
                        select_term.index()
                    ),
                });
            };
            let expected = projected.get(value_symbol).ok_or_else(|| UnknownReason {
                kind: UnknownKind::Other,
                detail: format!(
                    "warm structural equality read #{} lost its candidate value",
                    select_term.index()
                ),
            })?;
            let index = eval_warm_structural_term(arena, select.encoded_index, projected)?;
            if warm_array_value_select(target, &index)? != expected {
                return Ok(false);
            }
        }
        let changed = members
            .iter()
            .any(|&symbol| projected.get(symbol).as_ref() != Some(target));
        if !changed {
            return Ok(false);
        }
        for symbol in members {
            projected.set(symbol, target.clone());
        }
        Ok(true)
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

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum WarmSimplificationMode {
    ExpandStructuralReads,
    RetainStructuralReads,
}

fn simplify_memory_for_warm_assertion_inner(
    arena: &mut TermArena,
    term: TermId,
    memo: &mut HashMap<TermId, TermId>,
    mode: WarmSimplificationMode,
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
        .map(|&arg| simplify_memory_for_warm_assertion_inner(arena, arg, memo, mode))
        .collect::<Vec<_>>();
    let rebuilt = if simplified_args == original_args {
        term
    } else {
        arena.rebuild_with_args(term, &simplified_args)
    };
    let simplified = match collapse_trivial_warm_term(arena, rebuilt)
        .or_else(|| collapse_read_over_write(arena, rebuilt, mode))
    {
        Some(collapsed) if collapsed != rebuilt => {
            simplify_memory_for_warm_assertion_inner(arena, collapsed, memo, mode)
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
        Op::Ite => collapse_trivial_ite(arena, &args),
        Op::Eq => collapse_trivial_eq(arena, &args),
        Op::BoolNot | Op::BoolAnd | Op::BoolOr | Op::BoolXor | Op::BoolImplies => {
            collapse_trivial_bool(arena, op, &args)
        }
        Op::BvNot
        | Op::BvNeg
        | Op::BvAdd
        | Op::BvSub
        | Op::BvMul
        | Op::BvUdiv
        | Op::BvUrem
        | Op::BvSdiv
        | Op::BvSrem
        | Op::BvSmod
        | Op::BvAnd
        | Op::BvOr
        | Op::BvXor
        | Op::BvUlt
        | Op::BvUle
        | Op::BvUgt
        | Op::BvUge
        | Op::BvShl
        | Op::BvLshr
        | Op::BvAshr
        | Op::BvSlt
        | Op::BvSle
        | Op::BvSgt
        | Op::BvSge
        | Op::Extract { .. }
        | Op::ZeroExt { .. }
        | Op::SignExt { .. } => collapse_trivial_bv(arena, op, &args),
        _ => None,
    }
}

fn collapse_trivial_ite(arena: &mut TermArena, args: &[TermId]) -> Option<TermId> {
    let [condition, then_term, else_term] = args else {
        return None;
    };
    match arena.node(*condition) {
        TermNode::BoolConst(true) => return Some(*then_term),
        TermNode::BoolConst(false) => return Some(*else_term),
        _ => {}
    }
    if then_term == else_term {
        return Some(*then_term);
    }
    match (arena.node(*then_term), arena.node(*else_term)) {
        (TermNode::BoolConst(true), TermNode::BoolConst(false)) => Some(*condition),
        (TermNode::BoolConst(false), TermNode::BoolConst(true)) => arena.not(*condition).ok(),
        _ => None,
    }
}

fn collapse_trivial_eq(arena: &mut TermArena, args: &[TermId]) -> Option<TermId> {
    let [left, right] = args else {
        return None;
    };
    if left == right {
        return Some(arena.bool_const(true));
    }
    if known_literal_distinct(arena, *left, *right) {
        return Some(arena.bool_const(false));
    }
    if arena.sort_of(*left) == Sort::Bool {
        if let Some(value) = bool_const_value(arena, *left) {
            return bool_equality_with_const(arena, *right, value);
        }
        if let Some(value) = bool_const_value(arena, *right) {
            return bool_equality_with_const(arena, *left, value);
        }
    }
    distribute_eq_over_scalar_ite(arena, *left, *right)
}

fn collapse_trivial_bool(arena: &mut TermArena, op: Op, args: &[TermId]) -> Option<TermId> {
    match op {
        Op::BoolNot => {
            let [arg] = args else {
                return None;
            };
            collapse_bool_not(arena, *arg)
        }
        Op::BoolAnd | Op::BoolOr | Op::BoolXor | Op::BoolImplies => {
            let [left, right] = args else {
                return None;
            };
            match op {
                Op::BoolAnd => collapse_bool_and(arena, *left, *right),
                Op::BoolOr => collapse_bool_or(arena, *left, *right),
                Op::BoolXor => collapse_bool_xor(arena, *left, *right),
                Op::BoolImplies => collapse_bool_implies(arena, *left, *right),
                _ => unreachable!("outer match restricts Bool binary ops"),
            }
        }
        _ => None,
    }
}

fn collapse_trivial_bv(arena: &mut TermArena, op: Op, args: &[TermId]) -> Option<TermId> {
    match op {
        Op::BvNot | Op::BvNeg | Op::Extract { .. } | Op::ZeroExt { .. } | Op::SignExt { .. } => {
            let [arg] = args else {
                return None;
            };
            match op {
                Op::BvNot => collapse_bv_not(arena, *arg),
                Op::BvNeg => collapse_bv_neg(arena, *arg),
                Op::Extract { hi, lo } => collapse_bv_extract(arena, hi, lo, *arg),
                Op::ZeroExt { by } | Op::SignExt { by } => collapse_bv_extension(arena, by, *arg),
                _ => unreachable!("outer match restricts BV unary ops"),
            }
        }
        Op::BvAdd
        | Op::BvSub
        | Op::BvMul
        | Op::BvUdiv
        | Op::BvUrem
        | Op::BvSdiv
        | Op::BvSrem
        | Op::BvSmod
        | Op::BvAnd
        | Op::BvOr
        | Op::BvXor
        | Op::BvUlt
        | Op::BvUle
        | Op::BvUgt
        | Op::BvUge
        | Op::BvShl
        | Op::BvLshr
        | Op::BvAshr
        | Op::BvSlt
        | Op::BvSle
        | Op::BvSgt
        | Op::BvSge => {
            let [left, right] = args else {
                return None;
            };
            match op {
                Op::BvAdd => collapse_bv_add(arena, *left, *right),
                Op::BvSub => collapse_bv_sub(arena, *left, *right),
                Op::BvMul => collapse_bv_mul(arena, *left, *right),
                Op::BvUdiv | Op::BvUrem | Op::BvSdiv | Op::BvSrem | Op::BvSmod => {
                    collapse_bv_div_rem(arena, op, *left, *right)
                }
                Op::BvAnd => collapse_bv_and(arena, *left, *right),
                Op::BvOr => collapse_bv_or(arena, *left, *right),
                Op::BvXor => collapse_bv_xor(arena, *left, *right),
                Op::BvShl | Op::BvLshr | Op::BvAshr => collapse_bv_shift(arena, op, *left, *right),
                Op::BvUlt
                | Op::BvUle
                | Op::BvUgt
                | Op::BvUge
                | Op::BvSlt
                | Op::BvSle
                | Op::BvSgt
                | Op::BvSge => collapse_bv_comparison(arena, op, *left, *right),
                _ => unreachable!("outer match restricts BV binary ops"),
            }
        }
        _ => None,
    }
}

fn bool_const_value(arena: &TermArena, term: TermId) -> Option<bool> {
    match arena.node(term) {
        TermNode::BoolConst(value) => Some(*value),
        _ => None,
    }
}

fn bool_equality_with_const(arena: &mut TermArena, term: TermId, constant: bool) -> Option<TermId> {
    if constant {
        Some(term)
    } else {
        arena.not(term).ok()
    }
}

fn collapse_bool_not(arena: &mut TermArena, term: TermId) -> Option<TermId> {
    match arena.node(term) {
        TermNode::BoolConst(value) => Some(arena.bool_const(!value)),
        TermNode::App {
            op: Op::BoolNot,
            args,
            ..
        } => {
            let [inner] = args.as_ref() else {
                return None;
            };
            Some(*inner)
        }
        _ => None,
    }
}

fn collapse_bool_and(arena: &mut TermArena, left: TermId, right: TermId) -> Option<TermId> {
    if left == right {
        return Some(left);
    }
    match (
        bool_const_value(arena, left),
        bool_const_value(arena, right),
    ) {
        (Some(false), _) | (_, Some(false)) => return Some(arena.bool_const(false)),
        (Some(true), _) => return Some(right),
        (_, Some(true)) => return Some(left),
        _ => {}
    }
    are_negations(arena, left, right).then(|| arena.bool_const(false))
}

fn collapse_bool_or(arena: &mut TermArena, left: TermId, right: TermId) -> Option<TermId> {
    if left == right {
        return Some(left);
    }
    match (
        bool_const_value(arena, left),
        bool_const_value(arena, right),
    ) {
        (Some(true), _) | (_, Some(true)) => return Some(arena.bool_const(true)),
        (Some(false), _) => return Some(right),
        (_, Some(false)) => return Some(left),
        _ => {}
    }
    are_negations(arena, left, right).then(|| arena.bool_const(true))
}

fn collapse_bool_xor(arena: &mut TermArena, left: TermId, right: TermId) -> Option<TermId> {
    if left == right {
        return Some(arena.bool_const(false));
    }
    match (
        bool_const_value(arena, left),
        bool_const_value(arena, right),
    ) {
        (Some(left_value), Some(right_value)) => {
            return Some(arena.bool_const(left_value ^ right_value));
        }
        (Some(false), _) => return Some(right),
        (_, Some(false)) => return Some(left),
        (Some(true), _) => return arena.not(right).ok(),
        (_, Some(true)) => return arena.not(left).ok(),
        _ => {}
    }
    are_negations(arena, left, right).then(|| arena.bool_const(true))
}

fn collapse_bool_implies(arena: &mut TermArena, left: TermId, right: TermId) -> Option<TermId> {
    if left == right {
        return Some(arena.bool_const(true));
    }
    match (
        bool_const_value(arena, left),
        bool_const_value(arena, right),
    ) {
        (Some(left_value), Some(right_value)) => {
            return Some(arena.bool_const(!left_value || right_value));
        }
        (Some(false), _) | (_, Some(true)) => return Some(arena.bool_const(true)),
        (Some(true), _) => return Some(right),
        (_, Some(false)) => return arena.not(left).ok(),
        _ => {}
    }
    are_negations(arena, left, right).then_some(right)
}

fn are_negations(arena: &TermArena, left: TermId, right: TermId) -> bool {
    negated_term(arena, left).is_some_and(|inner| inner == right)
        || negated_term(arena, right).is_some_and(|inner| inner == left)
}

fn negated_term(arena: &TermArena, term: TermId) -> Option<TermId> {
    let TermNode::App {
        op: Op::BoolNot,
        args,
        ..
    } = arena.node(term)
    else {
        return None;
    };
    let [inner] = args.as_ref() else {
        return None;
    };
    Some(*inner)
}

fn collapse_bv_not(arena: &mut TermArena, term: TermId) -> Option<TermId> {
    let TermNode::App {
        op: Op::BvNot,
        args,
        ..
    } = arena.node(term)
    else {
        return None;
    };
    let [inner] = args.as_ref() else {
        return None;
    };
    matches!(arena.sort_of(*inner), Sort::BitVec(_)).then_some(*inner)
}

fn collapse_bv_neg(arena: &mut TermArena, term: TermId) -> Option<TermId> {
    let sort = arena.sort_of(term);
    if !matches!(sort, Sort::BitVec(_)) {
        return None;
    }
    if bv_const_is_zero(arena, term) {
        return bv_zero_for_sort(arena, sort);
    }
    let TermNode::App {
        op: Op::BvNeg,
        args,
        ..
    } = arena.node(term)
    else {
        return None;
    };
    let [inner] = args.as_ref() else {
        return None;
    };
    (arena.sort_of(*inner) == sort).then_some(*inner)
}

fn collapse_bv_extract(arena: &TermArena, hi: u32, lo: u32, term: TermId) -> Option<TermId> {
    let Sort::BitVec(width) = arena.sort_of(term) else {
        return None;
    };
    (lo == 0 && hi.checked_add(1) == Some(width)).then_some(term)
}

fn collapse_bv_extension(arena: &TermArena, by: u32, term: TermId) -> Option<TermId> {
    (by == 0 && matches!(arena.sort_of(term), Sort::BitVec(_))).then_some(term)
}

fn collapse_bv_add(arena: &mut TermArena, left: TermId, right: TermId) -> Option<TermId> {
    let sort = arena.sort_of(left);
    if !matches!(sort, Sort::BitVec(_)) || arena.sort_of(right) != sort {
        return None;
    }
    if bv_const_is_zero(arena, left) {
        return Some(right);
    }
    if bv_const_is_zero(arena, right) {
        return Some(left);
    }
    if are_bv_negations(arena, left, right) {
        return bv_zero_for_sort(arena, sort);
    }
    None
}

fn collapse_bv_sub(arena: &mut TermArena, left: TermId, right: TermId) -> Option<TermId> {
    let sort = arena.sort_of(left);
    if !matches!(sort, Sort::BitVec(_)) || arena.sort_of(right) != sort {
        return None;
    }
    if left == right {
        return bv_zero_for_sort(arena, sort);
    }
    if bv_const_is_zero(arena, right) {
        return Some(left);
    }
    if bv_const_is_zero(arena, left) {
        return arena.bv_neg(right).ok();
    }
    None
}

fn collapse_bv_mul(arena: &mut TermArena, left: TermId, right: TermId) -> Option<TermId> {
    let sort = arena.sort_of(left);
    if !matches!(sort, Sort::BitVec(_)) || arena.sort_of(right) != sort {
        return None;
    }
    if bv_const_is_zero(arena, left) || bv_const_is_zero(arena, right) {
        return bv_zero_for_sort(arena, sort);
    }
    if bv_const_is_one(arena, left) {
        return Some(right);
    }
    if bv_const_is_one(arena, right) {
        return Some(left);
    }
    None
}

fn collapse_bv_div_rem(
    arena: &mut TermArena,
    op: Op,
    left: TermId,
    right: TermId,
) -> Option<TermId> {
    let sort = arena.sort_of(left);
    if !matches!(sort, Sort::BitVec(_)) || arena.sort_of(right) != sort {
        return None;
    }
    match op {
        Op::BvUdiv => {
            if bv_const_is_zero(arena, right) {
                return bv_ones_for_sort(arena, sort);
            }
            if bv_const_is_one(arena, right) {
                return Some(left);
            }
            if bv_const_is_zero(arena, left) && bv_const_is_nonzero(arena, right) {
                return bv_zero_for_sort(arena, sort);
            }
            None
        }
        Op::BvSdiv => {
            if bv_const_is_one(arena, right) {
                return Some(left);
            }
            if bv_const_is_zero(arena, left) && bv_const_is_nonzero(arena, right) {
                return bv_zero_for_sort(arena, sort);
            }
            None
        }
        Op::BvUrem | Op::BvSrem | Op::BvSmod => {
            if left == right || bv_const_is_one(arena, right) || bv_const_is_zero(arena, left) {
                return bv_zero_for_sort(arena, sort);
            }
            if bv_const_is_zero(arena, right) {
                return Some(left);
            }
            None
        }
        _ => None,
    }
}

fn collapse_bv_and(arena: &mut TermArena, left: TermId, right: TermId) -> Option<TermId> {
    let sort = arena.sort_of(left);
    if !matches!(sort, Sort::BitVec(_)) || arena.sort_of(right) != sort {
        return None;
    }
    if left == right {
        return Some(left);
    }
    if bv_const_is_zero(arena, left) || bv_const_is_zero(arena, right) {
        return bv_zero_for_sort(arena, sort);
    }
    if bv_const_is_ones(arena, left) {
        return Some(right);
    }
    if bv_const_is_ones(arena, right) {
        return Some(left);
    }
    None
}

fn collapse_bv_or(arena: &mut TermArena, left: TermId, right: TermId) -> Option<TermId> {
    let sort = arena.sort_of(left);
    if !matches!(sort, Sort::BitVec(_)) || arena.sort_of(right) != sort {
        return None;
    }
    if left == right {
        return Some(left);
    }
    if bv_const_is_ones(arena, left) || bv_const_is_ones(arena, right) {
        return bv_ones_for_sort(arena, sort);
    }
    if bv_const_is_zero(arena, left) {
        return Some(right);
    }
    if bv_const_is_zero(arena, right) {
        return Some(left);
    }
    None
}

fn collapse_bv_xor(arena: &mut TermArena, left: TermId, right: TermId) -> Option<TermId> {
    let sort = arena.sort_of(left);
    if !matches!(sort, Sort::BitVec(_)) || arena.sort_of(right) != sort {
        return None;
    }
    if left == right {
        return bv_zero_for_sort(arena, sort);
    }
    if bv_const_is_zero(arena, left) {
        return Some(right);
    }
    if bv_const_is_zero(arena, right) {
        return Some(left);
    }
    None
}

fn collapse_bv_shift(arena: &mut TermArena, op: Op, left: TermId, right: TermId) -> Option<TermId> {
    let sort = arena.sort_of(left);
    if !matches!(sort, Sort::BitVec(_)) || arena.sort_of(right) != sort {
        return None;
    }
    if bv_const_is_zero(arena, right) {
        return Some(left);
    }
    if bv_const_is_zero(arena, left) {
        return bv_zero_for_sort(arena, sort);
    }
    if matches!(op, Op::BvAshr) && bv_const_is_ones(arena, left) {
        return bv_ones_for_sort(arena, sort);
    }
    None
}

fn collapse_bv_comparison(
    arena: &mut TermArena,
    op: Op,
    left: TermId,
    right: TermId,
) -> Option<TermId> {
    let sort = arena.sort_of(left);
    if !matches!(sort, Sort::BitVec(_)) || arena.sort_of(right) != sort {
        return None;
    }
    if left == right {
        return match op {
            Op::BvUlt | Op::BvUgt | Op::BvSlt | Op::BvSgt => Some(arena.bool_const(false)),
            Op::BvUle | Op::BvUge | Op::BvSle | Op::BvSge => Some(arena.bool_const(true)),
            _ => None,
        };
    }
    match op {
        Op::BvUlt if bv_const_is_zero(arena, right) || bv_const_is_ones(arena, left) => {
            Some(arena.bool_const(false))
        }
        Op::BvUle if bv_const_is_zero(arena, left) || bv_const_is_ones(arena, right) => {
            Some(arena.bool_const(true))
        }
        Op::BvUgt if bv_const_is_zero(arena, left) || bv_const_is_ones(arena, right) => {
            Some(arena.bool_const(false))
        }
        Op::BvUge if bv_const_is_zero(arena, right) || bv_const_is_ones(arena, left) => {
            Some(arena.bool_const(true))
        }
        _ => None,
    }
}

fn are_bv_negations(arena: &TermArena, left: TermId, right: TermId) -> bool {
    bv_negated_term(arena, left).is_some_and(|inner| inner == right)
        || bv_negated_term(arena, right).is_some_and(|inner| inner == left)
}

fn bv_negated_term(arena: &TermArena, term: TermId) -> Option<TermId> {
    let TermNode::App {
        op: Op::BvNeg,
        args,
        ..
    } = arena.node(term)
    else {
        return None;
    };
    let [inner] = args.as_ref() else {
        return None;
    };
    matches!(arena.sort_of(*inner), Sort::BitVec(_)).then_some(*inner)
}

fn bv_const_is_zero(arena: &TermArena, term: TermId) -> bool {
    match arena.node(term) {
        TermNode::BvConst { value, .. } => *value == 0,
        TermNode::WideBvConst(value) => value.is_zero(),
        _ => false,
    }
}

fn bv_const_is_one(arena: &TermArena, term: TermId) -> bool {
    match arena.node(term) {
        TermNode::BvConst { value, .. } => *value == 1,
        TermNode::WideBvConst(value) => *value == WideUint::from_u128(1, value.width()),
        _ => false,
    }
}

fn bv_const_is_nonzero(arena: &TermArena, term: TermId) -> bool {
    match arena.node(term) {
        TermNode::BvConst { value, .. } => *value != 0,
        TermNode::WideBvConst(value) => !value.is_zero(),
        _ => false,
    }
}

fn bv_const_is_ones(arena: &TermArena, term: TermId) -> bool {
    match arena.node(term) {
        TermNode::BvConst { width, value } => {
            let ones = if *width >= 128 {
                u128::MAX
            } else {
                (1u128 << *width) - 1
            };
            *value == ones
        }
        TermNode::WideBvConst(value) => *value == WideUint::ones(value.width()),
        _ => false,
    }
}

fn bv_zero_for_sort(arena: &mut TermArena, sort: Sort) -> Option<TermId> {
    let Sort::BitVec(width) = sort else {
        return None;
    };
    arena.bv_const(width, 0).ok()
}

fn bv_ones_for_sort(arena: &mut TermArena, sort: Sort) -> Option<TermId> {
    let Sort::BitVec(width) = sort else {
        return None;
    };
    if width > 128 {
        Some(arena.wide_bv_const(WideUint::ones(width)))
    } else {
        let ones = if width == 128 {
            u128::MAX
        } else {
            (1u128 << width) - 1
        };
        arena.bv_const(width, ones).ok()
    }
}

fn distribute_eq_over_scalar_ite(
    arena: &mut TermArena,
    left: TermId,
    right: TermId,
) -> Option<TermId> {
    if !is_warm_scalar_sort(arena.sort_of(left)) {
        return None;
    }
    if let Some((condition, then_term, else_term)) = ite_parts(arena, left) {
        let then_eq = arena.eq(then_term, right).ok()?;
        let else_eq = arena.eq(else_term, right).ok()?;
        return arena.ite(condition, then_eq, else_eq).ok();
    }
    if let Some((condition, then_term, else_term)) = ite_parts(arena, right) {
        let then_eq = arena.eq(left, then_term).ok()?;
        let else_eq = arena.eq(left, else_term).ok()?;
        return arena.ite(condition, then_eq, else_eq).ok();
    }
    None
}

fn ite_parts(arena: &TermArena, term: TermId) -> Option<(TermId, TermId, TermId)> {
    let TermNode::App {
        op: Op::Ite, args, ..
    } = arena.node(term)
    else {
        return None;
    };
    let [condition, then_term, else_term] = args.as_ref() else {
        return None;
    };
    Some((*condition, *then_term, *else_term))
}

fn collapse_read_over_write(
    arena: &mut TermArena,
    term: TermId,
    mode: WarmSimplificationMode,
) -> Option<TermId> {
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
    if mode == WarmSimplificationMode::ExpandStructuralReads {
        if let Some(value) = const_array_default(arena, array) {
            return Some(value);
        }
        if let Some(distributed) = distribute_select_over_array_ite(arena, array, read_index) {
            return Some(distributed);
        }
        if let Some(distributed) = distribute_select_over_index_ite(arena, array, read_index) {
            return Some(distributed);
        }
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
    if mode == WarmSimplificationMode::ExpandStructuralReads
        && let Some(distributed) =
            distribute_select_over_store_index_ite(arena, base, write_index, value, read_index)
    {
        return Some(distributed);
    }
    let base = drop_shadowed_stores_at_index(arena, base, write_index);
    if write_index == read_index {
        return Some(value);
    }
    if known_literal_distinct(arena, write_index, read_index) {
        return arena.select(base, read_index).ok();
    }
    if mode == WarmSimplificationMode::RetainStructuralReads {
        if let Some((original_base, _, _)) = store_parts(arena, array)
            && base != original_base
        {
            let pruned_store = arena.store(base, write_index, value).ok()?;
            return arena.select(pruned_store, read_index).ok();
        }
        return None;
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

fn distribute_select_over_store_index_ite(
    arena: &mut TermArena,
    base: TermId,
    write_index: TermId,
    value: TermId,
    read_index: TermId,
) -> Option<TermId> {
    let (condition, then_index, else_index) = match arena.node(write_index) {
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
    let then_array = arena.store(base, then_index, value).ok()?;
    let else_array = arena.store(base, else_index, value).ok()?;
    let then_read = arena.select(then_array, read_index).ok()?;
    let else_read = arena.select(else_array, read_index).ok()?;
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

fn warm_array_relation_literal(arena: &TermArena, term: TermId) -> Option<WarmArrayRelation> {
    let (equality, polarity) = match arena.node(term) {
        TermNode::App { op: Op::Eq, .. } => (term, WarmArrayRelationPolarity::Equal),
        TermNode::App {
            op: Op::BoolNot,
            args,
        } => {
            let [inner] = args.as_ref() else {
                return None;
            };
            if !matches!(arena.node(*inner), TermNode::App { op: Op::Eq, .. }) {
                return None;
            }
            (*inner, WarmArrayRelationPolarity::Distinct)
        }
        _ => return None,
    };
    let TermNode::App {
        op: Op::Eq, args, ..
    } = arena.node(equality)
    else {
        return None;
    };
    let [left, right] = args.as_ref() else {
        return None;
    };
    let Sort::Array {
        index: ArraySortKey::BitVec(index_width),
        element,
    } = arena.sort_of(*left)
    else {
        return None;
    };
    if arena.sort_of(*right) != arena.sort_of(*left) || !is_warm_array_element_sort(element) {
        return None;
    }
    Some(WarmArrayRelation {
        literal: term,
        left: *left,
        right: *right,
        polarity,
        index_width,
    })
}

fn warm_array_relation_covers(
    arena: &TermArena,
    relation: WarmArrayRelation,
    scalar_memo: &mut HashMap<TermId, bool>,
) -> bool {
    match relation.polarity {
        WarmArrayRelationPolarity::Equal | WarmArrayRelationPolarity::Distinct => {
            [relation.left, relation.right]
                .into_iter()
                .all(|term| warm_array_parent_covers(arena, term, scalar_memo))
        }
    }
}

fn warm_array_relation_has_structural_parent(
    arena: &TermArena,
    relation: WarmArrayRelation,
) -> bool {
    [relation.left, relation.right].into_iter().any(|parent| {
        !matches!(arena.node(parent), TermNode::Symbol(_))
            && !supported_warm_array_uf_app_shape(arena, parent)
    })
}

fn collect_warm_select_indices(arena: &TermArena, root: TermId, indices: &mut Vec<TermId>) {
    let mut stack = vec![root];
    let mut seen = HashSet::new();
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        if let TermNode::App {
            op: Op::Select,
            args,
        } = arena.node(term)
            && !indices.contains(&args[1])
        {
            indices.push(args[1]);
        }
        if let TermNode::App { args, .. } = arena.node(term) {
            stack.extend(args.iter().rev().copied());
        }
    }
    indices.sort_by_key(|term| term.index());
}

fn is_warm_array_element_sort(sort: ArraySortKey) -> bool {
    matches!(sort, ArraySortKey::Bool | ArraySortKey::BitVec(_))
}

fn is_supported_warm_array_parent(arena: &TermArena, term: TermId) -> bool {
    let Sort::Array {
        index: ArraySortKey::BitVec(_),
        element,
    } = arena.sort_of(term)
    else {
        return false;
    };
    if !is_warm_array_element_sort(element) {
        return false;
    }
    matches!(
        arena.node(term),
        TermNode::Symbol(_)
            | TermNode::App {
                op: Op::Store | Op::Ite | Op::ConstArray { .. },
                ..
            }
    ) || supported_warm_array_uf_app_shape(arena, term)
}

fn warm_array_parent_covers(
    arena: &TermArena,
    root: TermId,
    scalar_memo: &mut HashMap<TermId, bool>,
) -> bool {
    let mut stack = vec![(root, 0usize)];
    let mut seen = HashSet::new();
    let mut structural_nodes = 0usize;
    while let Some((term, depth)) = stack.pop() {
        if depth > MAX_WARM_STRUCTURAL_ARRAY_DEPTH {
            return false;
        }
        if !seen.insert(term) {
            continue;
        }
        if !is_supported_warm_array_parent(arena, term) {
            return false;
        }
        if !matches!(arena.node(term), TermNode::Symbol(_)) {
            structural_nodes += 1;
            if structural_nodes > MAX_WARM_STRUCTURAL_ARRAY_NODES {
                return false;
            }
        }
        match arena.node(term) {
            TermNode::Symbol(_) => {}
            TermNode::App {
                op: Op::ConstArray { .. },
                args,
            } => {
                let [value] = args.as_ref() else {
                    return false;
                };
                if !warm_abstraction_covers_term(arena, *value, scalar_memo) {
                    return false;
                }
            }
            TermNode::App {
                op: Op::Store,
                args,
            } => {
                let [base, index, value] = args.as_ref() else {
                    return false;
                };
                if !warm_abstraction_covers_term(arena, *index, scalar_memo)
                    || !warm_abstraction_covers_term(arena, *value, scalar_memo)
                {
                    return false;
                }
                stack.push((*base, depth + 1));
            }
            TermNode::App {
                op: Op::Ite, args, ..
            } => {
                let [condition, then_array, else_array] = args.as_ref() else {
                    return false;
                };
                if !warm_abstraction_covers_term(arena, *condition, scalar_memo) {
                    return false;
                }
                stack.push((*else_array, depth + 1));
                stack.push((*then_array, depth + 1));
            }
            TermNode::App {
                op: Op::Apply(_),
                args,
            } if supported_warm_array_uf_app_shape(arena, term) => {
                if !args
                    .iter()
                    .copied()
                    .all(|arg| warm_abstraction_covers_term(arena, arg, scalar_memo))
                {
                    return false;
                }
            }
            _ => return false,
        }
    }
    true
}

fn warm_structural_array_limits_hold(arena: &TermArena, root: TermId) -> bool {
    let mut stack = vec![root];
    let mut seen = HashSet::new();
    let mut structural = HashSet::new();
    let mut array_uf_apps = HashSet::new();
    let mut generated_relation_reads = 0usize;
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        if let TermNode::App {
            op: Op::Select,
            args,
        } = arena.node(term)
        {
            structural.insert(term);
            let [array, _index] = args.as_ref() else {
                return false;
            };
            if !record_warm_array_parent_limits(arena, *array, &mut structural, &mut array_uf_apps)
            {
                return false;
            }
        }
        if let Some(relation) = warm_array_relation_literal(arena, term) {
            let nested_positive_flag =
                relation.polarity == WarmArrayRelationPolarity::Equal && term != root;
            if relation.polarity == WarmArrayRelationPolarity::Distinct || nested_positive_flag {
                generated_relation_reads = generated_relation_reads.saturating_add(2);
            }
            for parent in [relation.left, relation.right] {
                if !record_warm_array_parent_limits(
                    arena,
                    parent,
                    &mut structural,
                    &mut array_uf_apps,
                ) {
                    return false;
                }
            }
            if structural.len().saturating_add(generated_relation_reads)
                > MAX_WARM_STRUCTURAL_ARRAY_NODES
                || array_uf_apps.len() > MAX_WARM_ARRAY_UF_APPS_PER_ROOT
            {
                return false;
            }
            continue;
        }
        if structural.len().saturating_add(generated_relation_reads)
            > MAX_WARM_STRUCTURAL_ARRAY_NODES
            || array_uf_apps.len() > MAX_WARM_ARRAY_UF_APPS_PER_ROOT
        {
            return false;
        }
        if let TermNode::App { args, .. } = arena.node(term) {
            stack.extend(args.iter().copied());
        }
    }
    true
}

fn record_warm_array_parent_limits(
    arena: &TermArena,
    root: TermId,
    structural: &mut HashSet<TermId>,
    array_uf_apps: &mut HashSet<TermId>,
) -> bool {
    let mut parent_stack = vec![(root, 0usize)];
    let mut parent_seen = HashSet::new();
    while let Some((parent, depth)) = parent_stack.pop() {
        if depth > MAX_WARM_STRUCTURAL_ARRAY_DEPTH {
            return false;
        }
        if !parent_seen.insert(parent) {
            continue;
        }
        if !matches!(arena.node(parent), TermNode::Symbol(_)) {
            structural.insert(parent);
        }
        if structural.len() > MAX_WARM_STRUCTURAL_ARRAY_NODES {
            return false;
        }
        match arena.node(parent) {
            TermNode::App {
                op: Op::Store,
                args,
            } => {
                let [base, _, _] = args.as_ref() else {
                    return false;
                };
                parent_stack.push((*base, depth + 1));
            }
            TermNode::App {
                op: Op::Ite, args, ..
            } if matches!(arena.sort_of(parent), Sort::Array { .. }) => {
                let [_, then_array, else_array] = args.as_ref() else {
                    return false;
                };
                parent_stack.push((*else_array, depth + 1));
                parent_stack.push((*then_array, depth + 1));
            }
            TermNode::Symbol(_)
            | TermNode::App {
                op: Op::ConstArray { .. },
                ..
            } => {}
            TermNode::App {
                op: Op::Apply(_), ..
            } if supported_warm_array_uf_app_shape(arena, parent) => {
                array_uf_apps.insert(parent);
                if array_uf_apps.len() > MAX_WARM_ARRAY_UF_APPS_PER_ROOT {
                    return false;
                }
            }
            _ => return false,
        }
    }
    true
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
    if let Some(relation) = warm_array_relation_literal(arena, term)
        && relation.polarity == WarmArrayRelationPolarity::Equal
    {
        return warm_array_relation_covers(arena, relation, memo);
    }

    if supported_warm_array_select_shape(arena, term) {
        match arena.node(term) {
            TermNode::App { args, .. } => {
                let [array, index] = args.as_ref() else {
                    return false;
                };
                return warm_abstraction_covers_term(arena, *index, memo)
                    && warm_array_parent_covers(arena, *array, memo);
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
    let Sort::Array {
        index: ArraySortKey::BitVec(index_width),
        element,
    } = arena.sort_of(*array)
    else {
        return false;
    };
    is_supported_warm_array_parent(arena, *array)
        && is_warm_array_element_sort(element)
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

fn supported_warm_array_uf_app_shape(arena: &TermArena, term: TermId) -> bool {
    let TermNode::App {
        op: Op::Apply(func),
        args,
        ..
    } = arena.node(term)
    else {
        return false;
    };
    let (_name, params, result_sort) = arena.function(*func);
    let Sort::Array {
        index: ArraySortKey::BitVec(_),
        element,
    } = result_sort
    else {
        return false;
    };
    is_warm_array_element_sort(element)
        && args.len() == params.len()
        && params.iter().copied().all(is_warm_scalar_sort)
        && args
            .iter()
            .zip(params)
            .all(|(&arg, &sort)| arena.sort_of(arg) == sort)
}

fn warm_array_symbols_equal(
    left: SymbolId,
    right: SymbolId,
    equalities: &[WarmArrayEquality],
) -> bool {
    if left == right {
        return true;
    }
    let mut stack = vec![left];
    let mut seen = HashSet::new();
    while let Some(symbol) = stack.pop() {
        if !seen.insert(symbol) {
            continue;
        }
        for equality in equalities {
            let next = if equality.left == symbol {
                Some(equality.right)
            } else if equality.right == symbol {
                Some(equality.left)
            } else {
                None
            };
            if let Some(next) = next {
                if next == right {
                    return true;
                }
                stack.push(next);
            }
        }
    }
    false
}

fn warm_array_equality_groups(equalities: &[WarmArrayEquality]) -> Vec<Vec<SymbolId>> {
    let mut groups: Vec<Vec<SymbolId>> = Vec::new();
    for equality in equalities {
        let left_group = groups
            .iter()
            .position(|group| group.contains(&equality.left));
        let right_group = groups
            .iter()
            .position(|group| group.contains(&equality.right));
        match (left_group, right_group) {
            (Some(left), Some(right)) if left == right => {}
            (Some(left), Some(right)) => {
                let (keep, remove) = if left < right {
                    (left, right)
                } else {
                    (right, left)
                };
                let removed = groups.remove(remove);
                for symbol in removed {
                    if !groups[keep].contains(&symbol) {
                        groups[keep].push(symbol);
                    }
                }
            }
            (Some(group), None) => {
                if !groups[group].contains(&equality.right) {
                    groups[group].push(equality.right);
                }
            }
            (None, Some(group)) => {
                if !groups[group].contains(&equality.left) {
                    groups[group].push(equality.left);
                }
            }
            (None, None) => groups.push(vec![equality.left, equality.right]),
        }
    }
    for group in &mut groups {
        group.sort();
        group.dedup();
    }
    groups.sort_by_key(|group| group.first().copied());
    groups
}

fn merge_equal_array_group(
    arena: &TermArena,
    model: &Model,
    group: &[SymbolId],
) -> Result<Value, UnknownReason> {
    let Some(&first) = group.first() else {
        return Err(UnknownReason {
            kind: UnknownKind::Other,
            detail: "cannot merge an empty warm array-equality group".to_owned(),
        });
    };
    let (_name, sort) = arena.symbol(first);
    for &symbol in group {
        let (_name, other_sort) = arena.symbol(symbol);
        if other_sort != sort {
            return Err(UnknownReason {
                kind: UnknownKind::Other,
                detail: "warm array equality connected symbols with different sorts".to_owned(),
            });
        }
    }
    match sort {
        Sort::Array {
            index: ArraySortKey::BitVec(index_width),
            element: ArraySortKey::BitVec(element_width),
        } if index_width <= 128 && element_width <= 128 => {
            merge_equal_compact_bv_arrays(index_width, element_width, model, group)
        }
        Sort::Array { index, element } => {
            merge_equal_generic_arrays(arena, index, element, model, group)
        }
        other => Err(UnknownReason {
            kind: UnknownKind::Other,
            detail: format!("warm array equality projected non-array sort {other}"),
        }),
    }
}

fn merge_equal_compact_bv_arrays(
    index_width: u32,
    element_width: u32,
    model: &Model,
    group: &[SymbolId],
) -> Result<Value, UnknownReason> {
    let mut entries = BTreeMap::new();
    for &symbol in group {
        let Some(Value::Array(array)) = model.get(symbol) else {
            continue;
        };
        if array.index_width() != index_width || array.element_width() != element_width {
            return Err(UnknownReason {
                kind: UnknownKind::Other,
                detail: "warm equal-array projection saw mismatched compact array sort".to_owned(),
            });
        }
        for (index, value) in array.entries() {
            match entries.insert(index, value) {
                Some(existing) if existing != value => {
                    return Err(UnknownReason {
                        kind: UnknownKind::Other,
                        detail: format!(
                            "warm equal-array projection found conflicting values at index {index}"
                        ),
                    });
                }
                _ => {}
            }
        }
    }
    let mut merged = ArrayValue::constant(index_width, element_width, 0);
    for (index, value) in entries {
        merged = merged.store(index, value);
    }
    Ok(Value::Array(merged))
}

fn merge_equal_generic_arrays(
    arena: &TermArena,
    index: ArraySortKey,
    element: ArraySortKey,
    model: &Model,
    group: &[SymbolId],
) -> Result<Value, UnknownReason> {
    let default = well_founded_default(arena, element.to_sort()).ok_or_else(|| UnknownReason {
        kind: UnknownKind::Other,
        detail: format!("warm equal-array projection had no default for element sort {element}"),
    })?;
    let mut entries: Vec<(Value, Value)> = Vec::new();
    for &symbol in group {
        let Some(value) = model.get(symbol) else {
            continue;
        };
        let array = match value {
            Value::GenericArray(array)
                if array.index_sort() == index && array.element_sort() == element =>
            {
                array
            }
            Value::Array(array)
                if index == ArraySortKey::BitVec(array.index_width())
                    && element == ArraySortKey::BitVec(array.element_width()) =>
            {
                for (raw_index, raw_value) in array.entries() {
                    let index_value = Value::Bv {
                        width: array.index_width(),
                        value: raw_index,
                    };
                    let element_value = Value::Bv {
                        width: array.element_width(),
                        value: raw_value,
                    };
                    push_equal_generic_array_entry(&mut entries, index_value, element_value)?;
                }
                continue;
            }
            _ => {
                return Err(UnknownReason {
                    kind: UnknownKind::Other,
                    detail: "warm equal-array projection saw mismatched generic array sort"
                        .to_owned(),
                });
            }
        };
        for (entry_index, entry_value) in array.entries() {
            push_equal_generic_array_entry(&mut entries, entry_index.clone(), entry_value.clone())?;
        }
    }

    let mut merged = GenericArrayValue::constant(index, element, default);
    for (entry_index, entry_value) in entries {
        merged = merged.store(entry_index, entry_value);
    }
    Ok(Value::GenericArray(merged))
}

fn push_equal_generic_array_entry(
    entries: &mut Vec<(Value, Value)>,
    index: Value,
    value: Value,
) -> Result<(), UnknownReason> {
    if let Some((_, existing)) = entries.iter().find(|(seen, _)| *seen == index) {
        if *existing != value {
            return Err(UnknownReason {
                kind: UnknownKind::Other,
                detail: format!(
                    "warm equal-array projection found conflicting values at index {index}"
                ),
            });
        }
        return Ok(());
    }
    entries.push((index, value));
    Ok(())
}

fn extend_unique_terms(target: &mut Vec<TermId>, terms: &[TermId]) {
    for &term in terms {
        if !target.contains(&term) {
            target.push(term);
        }
    }
}

fn guarded_warm_root(
    arena: &mut TermArena,
    flag: TermId,
    root: TermId,
    when_true: bool,
) -> Result<TermId, SolverError> {
    let guard = if when_true {
        flag
    } else {
        arena.not(flag).map_err(|error| map_ir_error(&error))?
    };
    arena
        .implies(guard, root)
        .map_err(|error| map_ir_error(&error))
}

fn merge_warm_work_into_encoding(encoding: &mut WarmArrayEncoding, work: WarmAbstractionWork) {
    extend_unique_terms(&mut encoding.select_terms, &work.select_terms);
    extend_unique_terms(&mut encoding.uf_app_terms, &work.uf_app_terms);
    extend_unique_terms(&mut encoding.array_uf_app_terms, &work.array_uf_app_terms);
    extend_unique_terms(&mut encoding.congruence_lemmas, &work.congruence_lemmas);
    for flag in work.array_relation_flags {
        if !encoding
            .array_relation_flags
            .iter()
            .any(|existing| existing.flag == flag.flag)
        {
            encoding.array_relation_flags.push(flag);
        }
    }
    for semantic in work.structural_semantics {
        if !encoding
            .structural_semantics
            .iter()
            .any(|existing| existing.select_term == semantic.select_term)
        {
            encoding.structural_semantics.push(semantic);
        }
    }
}

fn collect_warm_store_indices(
    arena: &TermArena,
    root: TermId,
    index_sort: Sort,
    indices: &mut Vec<TermId>,
) {
    let mut stack = vec![root];
    let mut seen = HashSet::new();
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        match arena.node(term) {
            TermNode::App {
                op: Op::Store,
                args,
            } => {
                if arena.sort_of(args[1]) == index_sort && !indices.contains(&args[1]) {
                    indices.push(args[1]);
                }
                stack.push(args[0]);
            }
            TermNode::App { op: Op::Ite, args }
                if matches!(arena.sort_of(term), Sort::Array { .. }) =>
            {
                stack.push(args[2]);
                stack.push(args[1]);
            }
            _ => {}
        }
    }
}

fn check_warm_structural_projection_deadline(
    deadline: Option<Instant>,
) -> Result<(), UnknownReason> {
    if deadline.is_some_and(|deadline| Instant::now() >= deadline) {
        Err(UnknownReason {
            kind: UnknownKind::Timeout,
            detail: "warm structural array equality exhausted the shared query deadline".to_owned(),
        })
    } else {
        Ok(())
    }
}

fn eval_warm_structural_term(
    arena: &TermArena,
    term: TermId,
    assignment: &Assignment,
) -> Result<Value, UnknownReason> {
    eval(arena, term, assignment).map_err(|error| UnknownReason {
        kind: UnknownKind::Other,
        detail: format!(
            "warm structural array equality could not evaluate term #{}: {error}",
            term.index()
        ),
    })
}

fn warm_array_owner_value(
    owner: SymbolId,
    assignment: &Assignment,
) -> Result<Value, UnknownReason> {
    assignment.get(owner).ok_or_else(|| UnknownReason {
        kind: UnknownKind::Other,
        detail: format!(
            "warm structural array equality lost owner #{}",
            owner.index()
        ),
    })
}

fn warm_array_value_select(array: &Value, index: &Value) -> Result<Value, UnknownReason> {
    match array {
        Value::Array(array) => {
            let Some((_, index)) = index.as_bv() else {
                return Err(UnknownReason {
                    kind: UnknownKind::Other,
                    detail: "warm structural compact array received a non-BV index".to_owned(),
                });
            };
            Ok(Value::Bv {
                width: array.element_width(),
                value: array.select(index),
            })
        }
        Value::GenericArray(array) => {
            if index.sort() != array.index_sort().to_sort() {
                return Err(UnknownReason {
                    kind: UnknownKind::Other,
                    detail: "warm structural generic array received an index of wrong sort"
                        .to_owned(),
                });
            }
            Ok(array.select(index))
        }
        other => Err(UnknownReason {
            kind: UnknownKind::Other,
            detail: format!("warm structural equality expected an array value, got {other}"),
        }),
    }
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
    let Some(value_symbol) = select.value_symbol else {
        return Err(UnknownReason {
            kind: UnknownKind::Other,
            detail: format!(
                "warm array select abstraction #{} had no internal value symbol",
                select_term.index()
            ),
        });
    };
    let value = assignment
        .get(value_symbol)
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
    match eval(arena, select.encoded_index, assignment) {
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
    array_symbol: SymbolId,
    select_value: &Value,
    index_value: &Value,
    model: &Model,
) -> Result<Value, UnknownReason> {
    match select.element {
        ArraySortKey::BitVec(_) => project_warm_bv_array_select(
            select_term,
            select,
            array_symbol,
            select_value,
            index_value,
            model,
        ),
        ArraySortKey::Bool => project_warm_bool_array_select(
            select_term,
            select,
            array_symbol,
            select_value,
            index_value,
            model,
        ),
        other => Err(UnknownReason {
            kind: UnknownKind::Other,
            detail: format!("unsupported warm array element sort {other}"),
        }),
    }
}

fn project_warm_bv_array_select(
    select_term: TermId,
    select: WarmArraySelect,
    array_symbol: SymbolId,
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
        let array = match model.get(array_symbol) {
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
    let array = match model.get(array_symbol) {
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
    array_symbol: SymbolId,
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
    let array = match model.get(array_symbol) {
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
        if let Some(value) = model
            .get(symbol)
            .or_else(|| assignment.get(symbol))
            .or_else(|| well_founded_default(arena, sort))
        {
            merged.set(symbol, value);
        }
    }
    merged
}

fn complete_warm_candidate_assignment(arena: &TermArena, assignment: &Assignment) -> Assignment {
    let mut completed = assignment.clone();
    for (symbol, _name, sort) in arena.symbols() {
        if completed.get(symbol).is_none()
            && let Some(value) = well_founded_default(arena, sort)
        {
            completed.set(symbol, value);
        }
    }
    completed
}

fn original_assumptions(assumptions: &[OneShotAssumption]) -> Vec<TermId> {
    assumptions
        .iter()
        .map(|assumption| assumption.original)
        .collect()
}

fn collect_warm_one_shot_terms(assumptions: &[OneShotAssumption]) -> WarmOneShotTerms {
    WarmOneShotTerms {
        selects: assumptions
            .iter()
            .flat_map(|assumption| assumption.warm_array_selects.iter().copied())
            .collect(),
        uf_apps: assumptions
            .iter()
            .flat_map(|assumption| assumption.warm_uf_apps.iter().copied())
            .collect(),
        array_uf_apps: assumptions
            .iter()
            .flat_map(|assumption| assumption.warm_array_uf_apps.iter().copied())
            .collect(),
        array_equalities: assumptions
            .iter()
            .flat_map(|assumption| assumption.warm_array_equalities.iter().copied())
            .collect(),
        array_relation_flags: assumptions
            .iter()
            .flat_map(|assumption| assumption.warm_array_relation_flags.iter().copied())
            .collect(),
    }
}

fn filter_internal_model(model: &Model, hidden_symbols: &HashSet<SymbolId>) -> Model {
    let mut filtered = Model::new();
    for (symbol, value) in model.iter() {
        if !hidden_symbols.contains(&symbol) {
            filtered.set(symbol, value);
        }
    }
    for (func, value) in model.functions() {
        filtered.set_function(func, value.clone());
    }
    for (numerator, quotient) in model.real_div_zeros() {
        filtered.set_real_div_zero(numerator, quotient);
    }
    filtered
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

#[cfg(test)]
mod tests {
    use super::*;

    fn structural_observation_root(arena: &mut TermArena, count: u128) -> TermId {
        let array = arena
            .array_var_with_sorts(
                "warm_observation_budget_reads",
                Sort::BitVec(16),
                Sort::BitVec(8),
            )
            .unwrap();
        let zero = arena.bv_const(8, 0).unwrap();
        let mut root = arena.bool_const(true);
        for raw_index in 0..count {
            let index = arena.bv_const(16, raw_index).unwrap();
            let read = arena.select(array, index).unwrap();
            let equality = arena.eq(read, zero).unwrap();
            root = arena.and(root, equality).unwrap();
        }
        root
    }

    fn structural_equality_metadata(arena: &mut TermArena) -> WarmArrayEquality {
        let left = arena
            .array_var_with_sorts(
                "warm_observation_budget_left",
                Sort::BitVec(16),
                Sort::BitVec(8),
            )
            .unwrap();
        let right = arena
            .array_var_with_sorts(
                "warm_observation_budget_right",
                Sort::BitVec(16),
                Sort::BitVec(8),
            )
            .unwrap();
        let index = arena.bv_const(16, 511).unwrap();
        let value = arena.bv_const(8, 1).unwrap();
        let stored = arena.store(left, index, value).unwrap();
        let TermNode::Symbol(left_owner) = arena.node(left) else {
            unreachable!()
        };
        let TermNode::Symbol(right_owner) = arena.node(right) else {
            unreachable!()
        };
        WarmArrayEquality {
            left: *left_owner,
            right: *right_owner,
            left_parent: stored,
            right_parent: right,
            left_structural: Some(stored),
            right_structural: None,
        }
    }

    #[test]
    fn structural_equality_observation_budget_is_exact() {
        let mut admitted_arena = TermArena::new();
        let equality = structural_equality_metadata(&mut admitted_arena);
        let root = structural_observation_root(&mut admitted_arena, 256);
        let solver = IncrementalBvSolver::new();
        assert!(solver.warm_array_equality_observation_budget_holds(
            &admitted_arena,
            root,
            None,
            &[],
            &[equality]
        ));

        let mut refused_arena = TermArena::new();
        let equality = structural_equality_metadata(&mut refused_arena);
        let root = structural_observation_root(&mut refused_arena, 257);
        let solver = IncrementalBvSolver::new();
        assert!(!solver.warm_array_equality_observation_budget_holds(
            &refused_arena,
            root,
            None,
            &[],
            &[equality]
        ));
    }
}
