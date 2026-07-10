//! Canonical online `QF_UFBV`/base-select `QF_ABV`/`QF_AUFBV` combination over
//! [`crate::cdclt::CdclT`].
//!
//! Array reads are first replaced by the shared lazy-ROW abstraction: base selects
//! and reads through stores receive fresh scalar results, while store hit/miss
//! axioms are deferred. Array equality atoms become Boolean flags with bounded
//! observed-index and diff-witness reads. Uninterpreted applications are then
//! replaced by fresh
//! scalar symbols through [`axeyum_rewrite::abstract_functions`], also without
//! eager Ackermann constraints.
//! The Boolean structure is Tseitin-encoded once per canonical round. The first
//! block of Boolean variables denotes every semantic Bool/BV atom plus the
//! currently materialized interface equalities for same-function application
//! arguments and results.
//!
//! Each canonical CDCL(T) round drives two theories in lockstep:
//! - [`crate::euf_egraph::EufTheory`] owns congruence over the original terms;
//! - [`crate::IncrementalBvSolver`] owns exact finite-domain Bool/BV semantics over
//!   the function-free abstraction and maps its failed decision-frame selectors
//!   back to a sound active theory-literal core whenever that conjunction is
//!   bit-vector UNSAT.
//!
//! The first round is the function-free relaxation. A SAT candidate is scanned for
//! same-function applications with equal argument values and unequal result values,
//! plus base-array selects whose parents share a final e-class and whose equal
//! indices have unequal results, and store-read sites whose result violates
//! read-over-write, plus equality flags inconsistent with an observed read or diff
//! witness. Array flags retain their original array equality as the EUF atom, so
//! equality transitivity and congruence are handled directly by the live
//! backtrackable e-graph instead of by cross-diff observations. Cross-parent select
//! lemmas carry the e-graph equality explanation as a Boolean guard, so they remain
//! valid after another canonical round chooses a different branch.
//! Only violated pairs/sites materialize argument/index/result equalities, hit/miss
//! axioms, or extensionality instances for the next round. Congruent applications
//! use the e-graph; array facts add valid implications directly to the Boolean
//! skeleton. Exact BV owns every scalar atom.
//! The loop reaches a replaying model, relaxation UNSAT, or explicit
//! round/interface/deadline bounds. Eager reductions remain fallbacks and
//! differential oracles.
//!
//! Soundness:
//! - each partial interface set is a relaxation of full UF/array consistency, so
//!   UNSAT from any round implies original-query UNSAT;
//! - each materialized array implication is a valid select-congruence or
//!   read-over-write instance; cross-parent congruence is guarded by the equality
//!   literals explaining the parent merge;
//! - every BV conflict is a re-solved UNSAT conjunction of the reported active
//!   literals;
//! - every EUF conflict/propagation is an e-graph explanation;
//! - `sat` is accepted only after the abstraction model is projected to
//!   [`axeyum_ir::FuncValue`] interpretations, then one shared array model per
//!   candidate-true symbol equality class, and every original assertion replays;
//! - unsupported/resource-bound states degrade to `Unknown`.

use std::collections::{HashMap, HashSet};
use std::time::Instant;

use axeyum_egraph::ENodeId;
use axeyum_ir::{
    ArraySortKey, Assignment, FuncId, Op, Sort, SymbolId, TermArena, TermId, TermNode, TermStats,
    Value, eval,
};
use axeyum_rewrite::{FuncElimError, FunctionAbstraction, abstract_functions, replace_subterms};

use crate::abv::{
    OnlineArrayEquality, RowKind, RowSite, abstract_rows_for_online, project_online_row_assignment,
};
use crate::backend::{CheckResult, SolverConfig, SolverError, UnknownKind, UnknownReason};
use crate::cdclt::{CdclT, Lit as CdcltLit, Outcome};
use crate::euf_egraph::{Encoder, EufTheory, TheoryLit, TheoryProp, TheorySolver};
use crate::incremental::IncrementalBvSolver;
use crate::model::Model;

/// Maximum input DAG admitted before the recursive function abstraction.
const MAX_INPUT_DAG_NODES: u64 = 16_384;
/// Maximum recursive term depth admitted before function abstraction.
const MAX_INPUT_DEPTH: u64 = 4_096;
/// Maximum semantic atoms (formula atoms plus generated interface equalities).
const MAX_THEORY_ATOMS: usize = 1_024;
/// Maximum materialized interface equalities before bounded refinement declines.
const MAX_INTERFACE_ATOMS: usize = 512;
/// Maximum canonical-driver rebuilds while materializing violated interface pairs.
const MAX_INTERFACE_REFINEMENT_ROUNDS: usize = 64;
/// Maximum Boolean variables after Tseitin encoding.
const MAX_BOOLEAN_VARIABLES: usize = 8_192;
/// Maximum Boolean clauses after Tseitin encoding.
const MAX_BOOLEAN_CLAUSES: usize = 32_768;
/// Maximum interface set eligible for exact one-candidate-per-state BV propagation.
const MAX_BV_PROPAGATION_INTERFACE_ATOMS: usize = 64;
/// Maximum implication probes accumulated in one online BV theory instance.
const MAX_BV_PROPAGATION_PROBES: usize = 128;

#[derive(Debug, Clone)]
struct OriginalApplication {
    term: TermId,
    func: FuncId,
    args: Vec<TermId>,
}

#[derive(Debug, Clone)]
struct CombinedApplication {
    original: OriginalApplication,
    rewritten_args: Vec<TermId>,
    fresh: axeyum_ir::SymbolId,
}

#[derive(Debug, Clone)]
struct CombinedSelect {
    array: SymbolId,
    array_term: TermId,
    original_index: TermId,
    rewritten_index: TermId,
    fresh: SymbolId,
}

#[derive(Debug, Clone)]
struct CombinedRowStore {
    original: RowSite,
    rewritten_index: TermId,
    rewritten_store_index: TermId,
    rewritten_store_elem: TermId,
    rewritten_inner: TermId,
}

#[derive(Debug, Clone)]
struct CombinedArrayEqualityObservation {
    original_lhs_read: TermId,
    original_rhs_read: TermId,
    rewritten_lhs_read: TermId,
    rewritten_rhs_read: TermId,
    is_diff_witness: bool,
}

#[derive(Debug, Clone)]
struct CombinedArrayEquality {
    flag: SymbolId,
    lhs: TermId,
    rhs: TermId,
    observations: Vec<CombinedArrayEqualityObservation>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct ArraySelectAxiom {
    left: usize,
    right: usize,
    /// Abstract equality atoms whose conjunction put the two array parents in one
    /// e-class. Empty when both reads already have the same syntactic parent.
    guard: Vec<TermId>,
}

struct SelectParentClass {
    root: ENodeId,
    /// Abstract equality atoms explaining this parent's equality to the first
    /// observed parent in the class.
    reasons: Vec<TermId>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum ArrayEqualityAxiomKind {
    Equal,
    Diff,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct ArrayEqualityAxiom {
    equality: usize,
    observation: usize,
    kind: ArrayEqualityAxiomKind,
}

enum WalkError {
    Timeout,
    NonBoolean(TermId),
}

#[derive(Debug)]
enum BuildFailure {
    Unknown(UnknownReason),
    Error(SolverError),
}

type BuildResult<T> = Result<T, BuildFailure>;

struct PreparedAbstraction {
    had_arrays: bool,
    row_sites: Vec<RowSite>,
    semantic_assertions: Vec<TermId>,
    abstracted_assertions: Vec<TermId>,
    abstraction: FunctionAbstraction,
    applications: Vec<CombinedApplication>,
    selects: Vec<CombinedSelect>,
    row_stores: Vec<CombinedRowStore>,
    array_equalities: Vec<CombinedArrayEquality>,
    replacements: HashMap<TermId, TermId>,
}

struct PreparedArrayRoots {
    had_arrays: bool,
    semantic_assertions: Vec<TermId>,
    row_sites: Vec<RowSite>,
    array_equalities: Vec<OnlineArrayEquality>,
    function_roots: Vec<TermId>,
}

struct TheoryAtoms {
    original: Vec<TermId>,
    abstracted: Vec<TermId>,
    propagation_candidates: Vec<bool>,
}

#[derive(Default)]
struct AtomAccumulator {
    original: Vec<TermId>,
    abstracted: Vec<TermId>,
    abstract_index: HashMap<TermId, usize>,
    propagation_candidates: Vec<bool>,
}

impl AtomAccumulator {
    fn register(
        &mut self,
        arena: &TermArena,
        original: TermId,
        abstracted: TermId,
        propagation_candidate: bool,
    ) -> Result<(), SolverError> {
        if arena.sort_of(original) != Sort::Bool || arena.sort_of(abstracted) != Sort::Bool {
            return Err(SolverError::Backend(
                "online UFBV atom abstraction changed Boolean sort".to_owned(),
            ));
        }
        if matches!(arena.node(abstracted), TermNode::BoolConst(_)) {
            return Ok(());
        }
        if let Some(&index) = self.abstract_index.get(&abstracted) {
            self.propagation_candidates[index] |= propagation_candidate;
            return Ok(());
        }
        let index = self.abstracted.len();
        self.original.push(original);
        self.abstracted.push(abstracted);
        self.abstract_index.insert(abstracted, index);
        self.propagation_candidates.push(propagation_candidate);
        Ok(())
    }

    fn finish(self) -> TheoryAtoms {
        TheoryAtoms {
            original: self.original,
            abstracted: self.abstracted,
            propagation_candidates: self.propagation_candidates,
        }
    }
}

struct BooleanSkeleton {
    variable_count: usize,
    clauses: Vec<Vec<CdcltLit>>,
}

enum RoundResult {
    Unsat,
    Unknown(UnknownReason),
    Sat {
        assignment: Assignment,
        select_parent_classes: Vec<SelectParentClass>,
    },
}

#[derive(Debug, Default)]
struct InterfaceRefinementStats {
    rounds: usize,
    sat_candidates: usize,
    pairs_added: usize,
    function_pairs_added: usize,
    array_pairs_added: usize,
    parent_select_pairs_added: usize,
    row_axioms_added: usize,
    array_equality_axioms_added: usize,
    max_interface_atoms: usize,
}

#[derive(Default)]
struct GroundValueCache {
    values: HashMap<TermId, Option<Value>>,
}

impl GroundValueCache {
    fn ensure(&mut self, arena: &TermArena, term: TermId) {
        self.values
            .entry(term)
            .or_insert_with(|| eval(arena, term, &Assignment::new()).ok());
    }

    fn provably_distinct(&mut self, arena: &TermArena, left: TermId, right: TermId) -> bool {
        if left == right {
            return false;
        }
        self.ensure(arena, left);
        self.ensure(arena, right);
        matches!(
            (self.values.get(&left), self.values.get(&right)),
            (Some(Some(left)), Some(Some(right))) if left != right
        )
    }
}

/// Exact Bool/BV theory state backed by the persistent incremental bit-blaster.
struct BvTheory<'a> {
    arena: &'a TermArena,
    positive: Vec<TermId>,
    negative: Vec<TermId>,
    solver: IncrementalBvSolver,
    assigned: Vec<Option<bool>>,
    assigned_log: Vec<usize>,
    scopes: Vec<(usize, bool)>,
    propagation_candidates: Vec<bool>,
    propagation_cursor: usize,
    pending_propagations: Vec<TheoryProp>,
    propagation_probes: usize,
    propagation_hits: usize,
    deadline: Option<Instant>,
    last_model: Option<Model>,
    last_unknown: Option<UnknownReason>,
    failure: Option<String>,
}

impl<'a> BvTheory<'a> {
    fn new(
        arena: &'a TermArena,
        positive: Vec<TermId>,
        negative: Vec<TermId>,
        propagation_candidates: Vec<bool>,
        config: &SolverConfig,
        deadline: Option<Instant>,
    ) -> Self {
        let atom_count = positive.len();
        Self {
            arena,
            positive,
            negative,
            solver: IncrementalBvSolver::with_config(config.clone()),
            assigned: vec![None; atom_count],
            assigned_log: Vec::new(),
            scopes: Vec::new(),
            propagation_candidates,
            propagation_cursor: 0,
            pending_propagations: Vec::new(),
            propagation_probes: 0,
            propagation_hits: 0,
            deadline,
            last_model: None,
            last_unknown: None,
            failure: None,
        }
    }

    fn assert(&mut self, atom: usize, value: bool) -> Result<(), Vec<TheoryLit>> {
        if let Some(existing) = self.assigned[atom] {
            if existing != value {
                self.failure = Some(format!(
                    "online UFBV received contradictory assignments for theory atom {atom}"
                ));
            }
            return Ok(());
        }
        self.assigned[atom] = Some(value);
        self.assigned_log.push(atom);
        if self.failure.is_some() {
            return Ok(());
        }

        let remaining = self
            .deadline
            .map(|deadline| deadline.saturating_duration_since(Instant::now()));
        if remaining.is_some_and(|duration| duration.is_zero()) {
            self.last_model = None;
            self.last_unknown = Some(UnknownReason {
                kind: UnknownKind::Timeout,
                detail: "online UFBV BV theory exhausted the shared deadline".to_owned(),
            });
            return Ok(());
        }
        self.solver.set_timeout(remaining);
        let literal = if value {
            self.positive[atom]
        } else {
            self.negative[atom]
        };
        if let Err(error) = self.solver.assert(self.arena, literal) {
            self.failure = Some(format!("online UFBV BV assertion failed: {error}"));
            self.last_model = None;
            return Ok(());
        }

        match self.solver.check_with_active_assertion_core(self.arena) {
            Ok((CheckResult::Sat(model), _)) => {
                self.last_model = Some(model);
                self.last_unknown = None;
                self.refresh_propagation();
                Ok(())
            }
            Ok((CheckResult::Unsat, core)) => {
                self.last_model = None;
                self.last_unknown = None;
                self.pending_propagations.clear();
                Err(self.map_active_core(&core))
            }
            Ok((CheckResult::Unknown(reason), _)) => {
                self.last_model = None;
                self.last_unknown = Some(reason);
                self.pending_propagations.clear();
                Ok(())
            }
            Err(error) => {
                self.failure = Some(format!("online UFBV warm BV check failed: {error}"));
                self.last_model = None;
                self.pending_propagations.clear();
                Ok(())
            }
        }
    }

    fn push(&mut self) {
        let pushed = if self.failure.is_some() {
            false
        } else {
            match self.solver.push() {
                Ok(()) => true,
                Err(error) => {
                    self.failure = Some(format!("online UFBV BV push failed: {error}"));
                    false
                }
            }
        };
        self.scopes.push((self.assigned_log.len(), pushed));
    }

    fn pop(&mut self) {
        let Some((assigned_len, pushed)) = self.scopes.pop() else {
            return;
        };
        if pushed && !self.solver.pop() {
            self.failure = Some("online UFBV BV scope stack became unbalanced".to_owned());
        }
        while self.assigned_log.len() > assigned_len {
            if let Some(atom) = self.assigned_log.pop() {
                self.assigned[atom] = None;
            }
        }
        self.pending_propagations.clear();
        self.refresh_propagation();
    }

    fn active_core(&self) -> Vec<TheoryLit> {
        self.assigned
            .iter()
            .enumerate()
            .filter_map(|(atom, value)| value.map(|value| TheoryLit { atom, value }))
            .collect()
    }

    fn map_active_core(&self, terms: &[TermId]) -> Vec<TheoryLit> {
        let core_terms = terms.iter().copied().collect::<HashSet<_>>();
        let core = self
            .assigned
            .iter()
            .enumerate()
            .filter_map(|(atom, value)| {
                let value = (*value)?;
                let term = if value {
                    self.positive[atom]
                } else {
                    self.negative[atom]
                };
                core_terms
                    .contains(&term)
                    .then_some(TheoryLit { atom, value })
            })
            .collect::<Vec<_>>();
        if core.is_empty() {
            self.active_core()
        } else {
            core
        }
    }

    fn refresh_propagation(&mut self) {
        self.pending_propagations
            .retain(|propagation| self.assigned[propagation.lit.atom].is_none());
        if self.failure.is_some()
            || self.last_unknown.is_some()
            || self.propagation_probes >= MAX_BV_PROPAGATION_PROBES
            || self
                .propagation_candidates
                .iter()
                .filter(|&&candidate| candidate)
                .count()
                > MAX_BV_PROPAGATION_INTERFACE_ATOMS
        {
            return;
        }
        let Some(model) = &self.last_model else {
            return;
        };
        let atom_count = self.positive.len();
        let Some(atom) = (0..atom_count)
            .map(|offset| (self.propagation_cursor + offset) % atom_count)
            .find(|&atom| {
                self.propagation_candidates[atom]
                    && self.assigned[atom].is_none()
                    && !self
                        .pending_propagations
                        .iter()
                        .any(|propagation| propagation.lit.atom == atom)
            })
        else {
            return;
        };
        self.propagation_cursor = (atom + 1) % atom_count;
        let assignment = model.to_assignment();
        let Ok(Value::Bool(value)) = eval(self.arena, self.positive[atom], &assignment) else {
            return;
        };
        let opposite = if value {
            self.negative[atom]
        } else {
            self.positive[atom]
        };
        let remaining = self
            .deadline
            .map(|deadline| deadline.saturating_duration_since(Instant::now()));
        if remaining.is_some_and(|duration| duration.is_zero()) {
            return;
        }
        self.solver.set_timeout(remaining);
        self.propagation_probes += 1;
        match self.solver.refute_assumption(self.arena, opposite) {
            Ok(crate::incremental::WarmRefutationProbe::Refuted { active_core }) => {
                self.propagation_hits += 1;
                self.pending_propagations.push(TheoryProp {
                    lit: TheoryLit { atom, value },
                    reason: self.map_active_core(&active_core),
                });
            }
            Ok(crate::incremental::WarmRefutationProbe::Satisfiable) => {}
            Ok(crate::incremental::WarmRefutationProbe::Unknown(reason)) => {
                if reason.kind == UnknownKind::Timeout {
                    self.last_unknown = Some(reason);
                }
            }
            Err(error) => {
                self.failure = Some(format!("online UFBV BV propagation probe failed: {error}"));
            }
        }
    }

    fn propagations(&self) -> Vec<TheoryProp> {
        self.pending_propagations.clone()
    }

    fn candidate_assignment(&self) -> Result<Assignment, UnknownReason> {
        if let Some(detail) = &self.failure {
            return Err(UnknownReason {
                kind: UnknownKind::Incomplete,
                detail: detail.clone(),
            });
        }
        if let Some(reason) = &self.last_unknown {
            return Err(reason.clone());
        }
        let Some(model) = &self.last_model else {
            return Err(UnknownReason {
                kind: UnknownKind::Incomplete,
                detail: "online UFBV reached a total trail without a BV model".to_owned(),
            });
        };
        Ok(model.to_assignment())
    }
}

/// One lockstep theory surface for the canonical driver.
struct CombinedUfbvTheory<'a> {
    euf: EufTheory,
    bv: BvTheory<'a>,
}

impl TheorySolver for CombinedUfbvTheory<'_> {
    fn assert(&mut self, atom: usize, value: bool) -> Result<(), Vec<TheoryLit>> {
        // Both components must observe the assignment even if either one reports
        // a conflict, so their backtrack stacks remain aligned with CdclT.
        let euf_conflict = self.euf.assert(atom, value).err();
        let bv_conflict = self.bv.assert(atom, value).err();
        match (euf_conflict, bv_conflict) {
            (Some(core), _) | (None, Some(core)) => Err(core),
            (None, None) => Ok(()),
        }
    }

    fn push(&mut self) {
        self.euf.push();
        self.bv.push();
    }

    fn pop(&mut self) {
        self.euf.pop();
        self.bv.pop();
    }

    fn propagate(&self) -> Vec<TheoryProp> {
        let mut propagations = self.euf.propagate();
        for propagation in self.bv.propagations() {
            if !propagations
                .iter()
                .any(|existing| existing.lit == propagation.lit)
            {
                propagations.push(propagation);
            }
        }
        propagations
    }
}

/// Decides the admitted scalar `QF_UFBV` fragment through canonical online
/// `CdclT` with live EUF+BV theory combination.
///
/// This route is complete for admitted Bool/BV function applications and Boolean
/// structure supported by the shared skeleton encoder. Resource caps are an
/// implementation bound, not a logic restriction; over-bound inputs return
/// `Unknown` and retain the eager/lazy fallbacks at the dispatcher.
///
/// # Errors
///
/// Returns [`SolverError::Unsupported`] for non-scalar/non-BV constructs or an IR
/// abstraction failure. Budget exhaustion is [`CheckResult::Unknown`].
pub fn check_qf_ufbv_online_cdclt(
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
) -> Result<CheckResult, SolverError> {
    let deadline = config
        .timeout
        .and_then(|timeout| Instant::now().checked_add(timeout));
    match build_and_solve(arena, assertions, config, deadline, false) {
        Ok(result) => Ok(result),
        Err(BuildFailure::Unknown(reason)) => Ok(CheckResult::Unknown(reason)),
        Err(BuildFailure::Error(error)) => Err(error),
    }
}

/// Decides the admitted finite scalar array slice (Bool/BitVec components),
/// optionally combined with scalar Bool/BitVec uninterpreted functions, through
/// replay-guided canonical `CdclT` rounds.
///
/// Base-array selects and reads through stores start as independent fresh scalar
/// results. Candidate equal-index/unequal-result pairs materialize select
/// congruence; violated store reads materialize the exact hit/miss ROW axiom.
/// Array equality flags retain the original equality for the canonical e-graph
/// and materialize only violated observed-index congruence or diff-witness
/// instances. Function applications use the same dynamic interface path. SAT is
/// accepted only after projecting functions, then class-owned arrays, and
/// replaying the original query.
///
/// # Errors
///
/// Returns [`SolverError::Unsupported`] for shapes outside finite Bool/BV arrays
/// and functions. Budget exhaustion is [`CheckResult::Unknown`].
pub fn check_qf_aufbv_online_cdclt(
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
) -> Result<CheckResult, SolverError> {
    let deadline = config
        .timeout
        .and_then(|timeout| Instant::now().checked_add(timeout));
    match build_and_solve(arena, assertions, config, deadline, true) {
        Ok(result) => Ok(result),
        Err(BuildFailure::Unknown(reason)) => Ok(CheckResult::Unknown(reason)),
        Err(BuildFailure::Error(error)) => Err(error),
    }
}

fn build_and_solve(
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
    deadline: Option<Instant>,
    admit_arrays: bool,
) -> BuildResult<CheckResult> {
    build_and_solve_with_stats_impl(arena, assertions, config, deadline, admit_arrays)
        .map(|(result, _stats)| result)
}

#[cfg(test)]
fn build_and_solve_with_stats(
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
    deadline: Option<Instant>,
) -> BuildResult<(CheckResult, InterfaceRefinementStats)> {
    build_and_solve_with_stats_impl(arena, assertions, config, deadline, false)
}

#[cfg(test)]
fn build_and_solve_arrays_with_stats(
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
    deadline: Option<Instant>,
) -> BuildResult<(CheckResult, InterfaceRefinementStats)> {
    build_and_solve_with_stats_impl(arena, assertions, config, deadline, true)
}

#[allow(clippy::too_many_lines)]
fn build_and_solve_with_stats_impl(
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
    deadline: Option<Instant>,
    admit_arrays: bool,
) -> BuildResult<(CheckResult, InterfaceRefinementStats)> {
    admit_input(arena, assertions, config, deadline, admit_arrays)?;
    let prepared = prepare_abstraction(arena, assertions, deadline, admit_arrays)?;
    let groups = application_groups(&prepared.applications);
    let select_parent_terms: Vec<TermId> = prepared
        .selects
        .iter()
        .map(|select| select.array_term)
        .collect();
    let mut ground_values = GroundValueCache::default();
    let mut function_pairs = Vec::new();
    let mut array_pairs = Vec::new();
    let mut row_axioms = Vec::new();
    let mut array_equality_axioms = Vec::new();
    let mut materialized_functions = HashSet::new();
    let mut materialized_arrays = HashSet::new();
    let mut materialized_rows = HashSet::new();
    let mut materialized_array_equalities = HashSet::new();
    let mut interface_count = 0usize;
    let mut stats = InterfaceRefinementStats::default();

    // Every round contains only valid UF congruence obligations, so it remains a
    // relaxation of the original query. UNSAT transfers immediately; SAT must
    // either replay or expose at least one new violated application pair.
    loop {
        stats.rounds += 1;
        let (atoms, round_assertions) = build_theory_atoms(
            arena,
            &prepared,
            &function_pairs,
            &array_pairs,
            &row_axioms,
            &array_equality_axioms,
            deadline,
        )?;
        stats.max_interface_atoms = stats.max_interface_atoms.max(
            atoms
                .propagation_candidates
                .iter()
                .filter(|&&candidate| candidate)
                .count(),
        );
        match solve_cdclt_round(
            arena,
            config,
            deadline,
            &round_assertions,
            atoms,
            &select_parent_terms,
        )? {
            RoundResult::Unsat => return Ok((CheckResult::Unsat, stats)),
            RoundResult::Unknown(reason) => {
                return Ok((CheckResult::Unknown(reason), stats));
            }
            RoundResult::Sat {
                assignment,
                select_parent_classes,
            } => {
                stats.sat_candidates += 1;
                let violated_functions = violated_application_pairs(
                    arena,
                    &prepared.applications,
                    &groups,
                    &assignment,
                    &materialized_functions,
                    &mut ground_values,
                    deadline,
                )?;
                let violated_arrays = violated_select_pairs(
                    arena,
                    &prepared.selects,
                    &select_parent_classes,
                    &assignment,
                    &materialized_arrays,
                    &mut ground_values,
                    deadline,
                )?;
                let violated_rows = violated_row_stores(
                    arena,
                    &prepared.row_stores,
                    &assignment,
                    &materialized_rows,
                    deadline,
                )?;
                let violated_array_equalities = violated_array_equality_axioms(
                    arena,
                    &prepared.array_equalities,
                    &assignment,
                    &materialized_array_equalities,
                    deadline,
                )?;
                if violated_functions.is_empty()
                    && violated_arrays.is_empty()
                    && violated_rows.is_empty()
                    && violated_array_equalities.is_empty()
                {
                    return Ok((
                        project_replay_composed(arena, &prepared, assertions, &assignment),
                        stats,
                    ));
                }
                if stats.rounds >= MAX_INTERFACE_REFINEMENT_ROUNDS {
                    return Ok((
                        unknown(
                            UnknownKind::ResourceLimit,
                            format!(
                                "online UFBV interface refinement exceeded {MAX_INTERFACE_REFINEMENT_ROUNDS} rounds"
                            ),
                        ),
                        stats,
                    ));
                }
                for pair @ (left, _right) in violated_functions {
                    interface_count = interface_count.saturating_add(
                        prepared.applications[left]
                            .original
                            .args
                            .len()
                            .saturating_add(1),
                    );
                    if interface_count > MAX_INTERFACE_ATOMS {
                        return Ok((interface_limit_unknown(prepared.had_arrays), stats));
                    }
                    if materialized_functions.insert(pair) {
                        function_pairs.push(pair);
                        stats.pairs_added += 1;
                        stats.function_pairs_added += 1;
                    }
                }
                for axiom in violated_arrays {
                    interface_count = interface_count.saturating_add(2);
                    if interface_count > MAX_INTERFACE_ATOMS {
                        return Ok((interface_limit_unknown(true), stats));
                    }
                    let pair = (axiom.left, axiom.right);
                    if materialized_arrays.insert(axiom.clone()) {
                        if prepared.selects[pair.0].array != prepared.selects[pair.1].array {
                            stats.parent_select_pairs_added += 1;
                        }
                        array_pairs.push(axiom);
                        stats.pairs_added += 1;
                        stats.array_pairs_added += 1;
                    }
                }
                for site in violated_rows {
                    interface_count = interface_count.saturating_add(3);
                    if interface_count > MAX_INTERFACE_ATOMS {
                        return Ok((interface_limit_unknown(true), stats));
                    }
                    if materialized_rows.insert(site) {
                        row_axioms.push(site);
                        stats.row_axioms_added += 1;
                    }
                }
                for axiom in violated_array_equalities {
                    interface_count = interface_count.saturating_add(1);
                    if interface_count > MAX_INTERFACE_ATOMS {
                        return Ok((interface_limit_unknown(true), stats));
                    }
                    if materialized_array_equalities.insert(axiom) {
                        array_equality_axioms.push(axiom);
                        stats.array_equality_axioms_added += 1;
                    }
                }
            }
        }
    }
}

fn interface_limit_unknown(has_arrays: bool) -> CheckResult {
    let logic = if has_arrays { "AUFBV" } else { "UFBV" };
    unknown(
        UnknownKind::ResourceLimit,
        format!(
            "online {logic} materialized interface equalities exceed the bounded cap of {MAX_INTERFACE_ATOMS}"
        ),
    )
}

fn solve_cdclt_round(
    arena: &mut TermArena,
    config: &SolverConfig,
    deadline: Option<Instant>,
    assertions: &[TermId],
    atoms: TheoryAtoms,
    select_parent_terms: &[TermId],
) -> BuildResult<RoundResult> {
    let skeleton = encode_boolean_skeleton(arena, assertions, &atoms.abstracted, deadline)?;

    let mut negative_atoms = Vec::with_capacity(atoms.abstracted.len());
    for &atom in &atoms.abstracted {
        negative_atoms.push(arena.not(atom)?);
    }
    let atom_count = atoms.original.len();
    let abstract_atoms = atoms.abstracted.clone();
    let euf = EufTheory::new_with_observed_terms(arena, &atoms.original, select_parent_terms);
    let bv = BvTheory::new(
        arena,
        atoms.abstracted,
        negative_atoms,
        atoms.propagation_candidates,
        config,
        deadline,
    );
    let mut theory = CombinedUfbvTheory { euf, bv };
    let mut solver = CdclT::new(
        skeleton.variable_count,
        atom_count,
        skeleton.clauses,
        deadline,
    );
    Ok(match solver.solve(&mut theory) {
        Outcome::Unsat => RoundResult::Unsat,
        Outcome::Unknown => {
            let kind = if deadline.is_some_and(|deadline| Instant::now() >= deadline) {
                UnknownKind::Timeout
            } else {
                UnknownKind::ResourceLimit
            };
            RoundResult::Unknown(UnknownReason {
                kind,
                detail: "online UFBV canonical CdclT search exhausted its budget".to_owned(),
            })
        }
        Outcome::Sat => match theory.bv.candidate_assignment() {
            Ok(assignment) => {
                let select_parent_classes = theory
                    .euf
                    .observed_classes_with_reasons(select_parent_terms)
                    .into_iter()
                    .map(|(root, reasons)| SelectParentClass {
                        root,
                        reasons: reasons
                            .into_iter()
                            .map(|atom| abstract_atoms[atom])
                            .collect(),
                    })
                    .collect();
                RoundResult::Sat {
                    assignment,
                    select_parent_classes,
                }
            }
            Err(reason) => RoundResult::Unknown(reason),
        },
    })
}

fn admit_input(
    arena: &TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
    deadline: Option<Instant>,
    admit_arrays: bool,
) -> BuildResult<()> {
    if deadline.is_some_and(|deadline| Instant::now() >= deadline) {
        return Err(build_unknown(
            UnknownKind::Timeout,
            "online UFBV deadline elapsed before construction",
        ));
    }
    let stats = TermStats::compute(arena, assertions);
    let node_cap = config
        .node_budget
        .unwrap_or(MAX_INPUT_DAG_NODES)
        .min(MAX_INPUT_DAG_NODES);
    if stats.dag_nodes > node_cap {
        return Err(build_unknown(
            UnknownKind::NodeBudget,
            format!(
                "online UFBV input has {} DAG nodes, exceeding the admission cap of {node_cap}",
                stats.dag_nodes
            ),
        ));
    }
    if stats.max_depth > MAX_INPUT_DEPTH {
        return Err(build_unknown(
            UnknownKind::ResourceLimit,
            format!(
                "online UFBV input depth {} exceeds the recursive abstraction cap of {MAX_INPUT_DEPTH}",
                stats.max_depth
            ),
        ));
    }
    if !uses_only_bool_bv_and_admitted_arrays(arena, assertions, admit_arrays) {
        return Err(BuildFailure::Error(SolverError::Unsupported(
            if admit_arrays {
                "online AUFBV combination admits only Bool, BitVec, and Bool/BV-component array terms"
            } else {
                "online UFBV combination admits only Bool and BitVec terms"
            }
            .to_owned(),
        )));
    }
    Ok(())
}

fn uses_only_bool_bv_and_admitted_arrays(
    arena: &TermArena,
    assertions: &[TermId],
    admit_arrays: bool,
) -> bool {
    let mut seen = HashSet::new();
    let mut stack = assertions.to_vec();
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        let admitted_sort = matches!(arena.sort_of(term), Sort::Bool | Sort::BitVec(_))
            || admit_arrays
                && matches!(
                    arena.sort_of(term),
                    Sort::Array { index, element }
                        if finite_scalar_array_key(index) && finite_scalar_array_key(element)
                );
        if !admitted_sort {
            return false;
        }
        if let TermNode::App { args, .. } = arena.node(term) {
            stack.extend(args.iter().copied());
        }
    }
    true
}

fn finite_scalar_array_key(key: ArraySortKey) -> bool {
    matches!(key, ArraySortKey::Bool | ArraySortKey::BitVec(_))
}

fn contains_array_terms(arena: &TermArena, assertions: &[TermId]) -> bool {
    let mut seen = HashSet::new();
    let mut stack = assertions.to_vec();
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        if matches!(arena.sort_of(term), Sort::Array { .. }) {
            return true;
        }
        if let TermNode::App { args, .. } = arena.node(term) {
            stack.extend(args.iter().copied());
        }
    }
    false
}

fn prepare_array_roots(
    arena: &mut TermArena,
    assertions: &[TermId],
    admit_arrays: bool,
) -> BuildResult<PreparedArrayRoots> {
    let had_arrays = contains_array_terms(arena, assertions);
    if had_arrays && !admit_arrays {
        return Err(BuildFailure::Error(SolverError::Unsupported(
            "online UFBV combination does not admit arrays".to_owned(),
        )));
    }
    let (semantic_assertions, row_sites, array_equalities) = if had_arrays {
        let Some(rows) = abstract_rows_for_online(arena, assertions)? else {
            return Err(BuildFailure::Error(SolverError::Unsupported(
                "online AUFBV lazy-ROW abstraction does not admit this array shape".to_owned(),
            )));
        };
        (rows.assertions, rows.sites, rows.equalities)
    } else {
        (assertions.to_vec(), Vec::new(), Vec::new())
    };
    let mut roots = semantic_assertions.clone();
    for site in &row_sites {
        roots.push(site.index);
        match site.kind {
            RowKind::Store {
                store_index,
                store_elem,
                inner,
            } => roots.extend([store_index, store_elem, inner]),
            RowKind::Const { value } => roots.push(value),
            RowKind::Var { .. } => {}
        }
    }
    for equality in &array_equalities {
        for observation in &equality.observations {
            roots.extend([
                observation.index,
                observation.lhs_read,
                observation.rhs_read,
            ]);
        }
    }
    Ok(PreparedArrayRoots {
        had_arrays,
        semantic_assertions,
        row_sites,
        array_equalities,
        function_roots: roots,
    })
}

fn combine_row_sites(
    arena: &mut TermArena,
    row_sites: &[RowSite],
    replacements: &HashMap<TermId, TermId>,
) -> BuildResult<(Vec<CombinedSelect>, Vec<CombinedRowStore>)> {
    let mut memo = HashMap::new();
    let mut selects = Vec::new();
    let mut stores = Vec::new();
    for site in row_sites {
        let rewritten_index = replace_subterms(arena, site.index, replacements, &mut memo)?;
        match site.kind {
            RowKind::Var { array } => {
                let array_term = arena.var(array);
                selects.push(CombinedSelect {
                    array,
                    array_term,
                    original_index: site.index,
                    rewritten_index,
                    fresh: site.fresh,
                });
            }
            RowKind::Store {
                store_index,
                store_elem,
                inner,
            } => stores.push(CombinedRowStore {
                original: site.clone(),
                rewritten_index,
                rewritten_store_index: replace_subterms(
                    arena,
                    store_index,
                    replacements,
                    &mut memo,
                )?,
                rewritten_store_elem: replace_subterms(arena, store_elem, replacements, &mut memo)?,
                rewritten_inner: replace_subterms(arena, inner, replacements, &mut memo)?,
            }),
            RowKind::Const { .. } => {}
        }
    }
    Ok((selects, stores))
}

fn combine_array_equalities(
    arena: &mut TermArena,
    equalities: &[OnlineArrayEquality],
    replacements: &HashMap<TermId, TermId>,
) -> BuildResult<Vec<CombinedArrayEquality>> {
    let mut memo = HashMap::new();
    let mut combined = Vec::with_capacity(equalities.len());
    for equality in equalities {
        let mut observations = Vec::with_capacity(equality.observations.len());
        for observation in &equality.observations {
            observations.push(CombinedArrayEqualityObservation {
                original_lhs_read: observation.lhs_read,
                original_rhs_read: observation.rhs_read,
                rewritten_lhs_read: replace_subterms(
                    arena,
                    observation.lhs_read,
                    replacements,
                    &mut memo,
                )?,
                rewritten_rhs_read: replace_subterms(
                    arena,
                    observation.rhs_read,
                    replacements,
                    &mut memo,
                )?,
                is_diff_witness: observation.is_diff_witness,
            });
        }
        combined.push(CombinedArrayEquality {
            flag: equality.flag,
            lhs: equality.lhs,
            rhs: equality.rhs,
            observations,
        });
    }
    Ok(combined)
}

fn prepare_abstraction(
    arena: &mut TermArena,
    assertions: &[TermId],
    deadline: Option<Instant>,
    admit_arrays: bool,
) -> BuildResult<PreparedAbstraction> {
    let PreparedArrayRoots {
        had_arrays,
        semantic_assertions,
        row_sites,
        array_equalities,
        function_roots,
    } = prepare_array_roots(arena, assertions, admit_arrays)?;
    let semantic_count = semantic_assertions.len();
    let original_applications =
        match collect_original_applications(arena, &function_roots, deadline) {
            Ok(applications) => applications,
            Err(WalkError::Timeout) => {
                return Err(build_unknown(
                    UnknownKind::Timeout,
                    "online UFBV deadline elapsed during application discovery",
                ));
            }
            Err(WalkError::NonBoolean(term)) => {
                return Err(BuildFailure::Error(SolverError::NonBooleanAssertion(term)));
            }
        };
    if original_applications.is_empty() && row_sites.is_empty() {
        return Err(BuildFailure::Error(SolverError::Unsupported(
            "online UFBV/AUFBV combination requires an applied uninterpreted function or abstracted array read"
                .to_owned(),
        )));
    }
    let abstraction = abstract_functions(arena, &function_roots).map_err(map_elim_error)?;
    let abstracted_assertions = abstraction.assertions()[..semantic_count].to_vec();
    let rewritten_applications: Vec<(FuncId, Vec<TermId>, axeyum_ir::SymbolId)> = abstraction
        .applications()
        .into_iter()
        .map(|(func, args, fresh)| (func, args.to_vec(), fresh))
        .collect();
    if original_applications.len() != rewritten_applications.len() {
        return Err(BuildFailure::Error(SolverError::Backend(
            "function abstraction application metadata lost discovery-order alignment".to_owned(),
        )));
    }

    let mut applications = Vec::with_capacity(original_applications.len());
    let mut replacements = HashMap::new();
    for (original, (func, rewritten_args, fresh)) in original_applications
        .into_iter()
        .zip(rewritten_applications)
    {
        if original.func != func || original.args.len() != rewritten_args.len() {
            return Err(BuildFailure::Error(SolverError::Backend(
                "function abstraction application signature lost alignment".to_owned(),
            )));
        }
        replacements.insert(original.term, arena.var(fresh));
        applications.push(CombinedApplication {
            original,
            rewritten_args,
            fresh,
        });
    }
    let (selects, row_stores) = combine_row_sites(arena, &row_sites, &replacements)?;
    let array_equalities = combine_array_equalities(arena, &array_equalities, &replacements)?;
    Ok(PreparedAbstraction {
        had_arrays,
        row_sites,
        semantic_assertions,
        abstracted_assertions,
        abstraction,
        applications,
        selects,
        row_stores,
        array_equalities,
        replacements,
    })
}

fn build_theory_atoms(
    arena: &mut TermArena,
    prepared: &PreparedAbstraction,
    function_pairs: &[(usize, usize)],
    array_pairs: &[ArraySelectAxiom],
    row_axioms: &[usize],
    array_equality_axioms: &[ArrayEqualityAxiom],
    deadline: Option<Instant>,
) -> BuildResult<(TheoryAtoms, Vec<TermId>)> {
    let mut atoms = AtomAccumulator::default();
    let mut atom_memo = HashMap::new();
    let mut array_flag_originals = HashMap::new();
    for equality in &prepared.array_equalities {
        let flag = arena.var(equality.flag);
        let original = arena.eq(equality.lhs, equality.rhs)?;
        array_flag_originals.insert(flag, original);
    }
    let mut formula_atoms = Vec::new();
    let mut seen_terms = HashSet::new();
    for &assertion in &prepared.semantic_assertions {
        if let Err(error) = collect_formula_atoms(
            arena,
            assertion,
            &mut formula_atoms,
            &mut seen_terms,
            deadline,
        ) {
            return Err(match error {
                WalkError::Timeout => build_unknown(
                    UnknownKind::Timeout,
                    "online UFBV deadline elapsed during atom discovery",
                ),
                WalkError::NonBoolean(term) => {
                    BuildFailure::Error(SolverError::NonBooleanAssertion(term))
                }
            });
        }
    }
    for atom in formula_atoms {
        let rewritten = replace_subterms(arena, atom, &prepared.replacements, &mut atom_memo)?;
        let original = array_flag_originals.get(&atom).copied().unwrap_or(atom);
        atoms.register(arena, original, rewritten, false)?;
    }

    add_interface_atoms(
        arena,
        &prepared.applications,
        function_pairs,
        deadline,
        &mut atoms,
    )?;
    let mut round_assertions = prepared.abstracted_assertions.clone();
    add_array_interface_atoms(
        arena,
        &prepared.selects,
        array_pairs,
        deadline,
        &mut atoms,
        &mut round_assertions,
    )?;
    add_row_axiom_atoms(
        arena,
        &prepared.row_stores,
        row_axioms,
        deadline,
        &mut atoms,
        &mut round_assertions,
    )?;
    add_array_equality_axiom_atoms(
        arena,
        &prepared.array_equalities,
        array_equality_axioms,
        deadline,
        &mut atoms,
        &mut round_assertions,
    )?;

    if atoms.original.is_empty() {
        return Err(BuildFailure::Error(SolverError::Unsupported(
            "online UFBV abstraction produced no semantic Boolean atoms".to_owned(),
        )));
    }
    if atoms.original.len() > MAX_THEORY_ATOMS {
        return Err(build_unknown(
            UnknownKind::ResourceLimit,
            format!(
                "online UFBV has {} semantic atoms, exceeding the cap of {MAX_THEORY_ATOMS}",
                atoms.original.len()
            ),
        ));
    }
    Ok((atoms.finish(), round_assertions))
}

fn application_groups(applications: &[CombinedApplication]) -> Vec<(FuncId, Vec<usize>)> {
    let mut groups: Vec<(FuncId, Vec<usize>)> = Vec::new();
    for (index, application) in applications.iter().enumerate() {
        if let Some((_, members)) = groups
            .iter_mut()
            .find(|(func, _)| *func == application.original.func)
        {
            members.push(index);
        } else {
            groups.push((application.original.func, vec![index]));
        }
    }
    groups
}

fn select_class_groups(classes: &[SelectParentClass]) -> Vec<(ENodeId, Vec<usize>)> {
    let mut groups: Vec<(ENodeId, Vec<usize>)> = Vec::new();
    for (index, class) in classes.iter().enumerate() {
        if let Some((_, members)) = groups
            .iter_mut()
            .find(|(existing, _)| *existing == class.root)
        {
            members.push(index);
        } else {
            groups.push((class.root, vec![index]));
        }
    }
    groups
}

fn violated_application_pairs(
    arena: &TermArena,
    applications: &[CombinedApplication],
    groups: &[(FuncId, Vec<usize>)],
    assignment: &Assignment,
    materialized: &HashSet<(usize, usize)>,
    ground_values: &mut GroundValueCache,
    deadline: Option<Instant>,
) -> BuildResult<Vec<(usize, usize)>> {
    let mut violated = Vec::new();
    for (_func, members) in groups {
        for left_pos in 0..members.len() {
            for right_pos in (left_pos + 1)..members.len() {
                if deadline.is_some_and(|deadline| Instant::now() >= deadline) {
                    return Err(build_unknown(
                        UnknownKind::Timeout,
                        "online UFBV deadline elapsed while refining interface equalities",
                    ));
                }
                let pair = (members[left_pos], members[right_pos]);
                if materialized.contains(&pair) {
                    continue;
                }
                let left = &applications[pair.0];
                let right = &applications[pair.1];
                if applications_may_be_congruent(arena, left, right, ground_values)
                    && rewritten_arguments_equal(arena, left, right, assignment)
                    && application_results_differ(left, right, assignment)
                {
                    violated.push(pair);
                }
            }
        }
    }
    Ok(violated)
}

fn violated_select_pairs(
    arena: &TermArena,
    selects: &[CombinedSelect],
    classes: &[SelectParentClass],
    assignment: &Assignment,
    materialized: &HashSet<ArraySelectAxiom>,
    ground_values: &mut GroundValueCache,
    deadline: Option<Instant>,
) -> BuildResult<Vec<ArraySelectAxiom>> {
    debug_assert_eq!(selects.len(), classes.len());
    let mut violated = Vec::new();
    for (_class, members) in select_class_groups(classes) {
        for left_pos in 0..members.len() {
            for right_pos in (left_pos + 1)..members.len() {
                if deadline.is_some_and(|deadline| Instant::now() >= deadline) {
                    return Err(build_unknown(
                        UnknownKind::Timeout,
                        "online AUFBV deadline elapsed while refining array interfaces",
                    ));
                }
                let pair = (members[left_pos], members[right_pos]);
                let left = &selects[pair.0];
                let right = &selects[pair.1];
                if ground_values.provably_distinct(arena, left.original_index, right.original_index)
                {
                    continue;
                }
                let indices_equal = matches!(
                    (
                        eval(arena, left.rewritten_index, assignment),
                        eval(arena, right.rewritten_index, assignment)
                    ),
                    (Ok(left), Ok(right)) if left == right
                );
                let results_differ = matches!(
                    (assignment.get(left.fresh), assignment.get(right.fresh)),
                    (Some(left), Some(right)) if left != right
                );
                if indices_equal && results_differ {
                    let guard = if left.array_term == right.array_term {
                        Vec::new()
                    } else {
                        let mut guard = classes[pair.0].reasons.clone();
                        guard.extend(classes[pair.1].reasons.iter().copied());
                        guard.sort_unstable();
                        guard.dedup();
                        guard
                    };
                    debug_assert!(left.array_term == right.array_term || !guard.is_empty());
                    let axiom = ArraySelectAxiom {
                        left: pair.0,
                        right: pair.1,
                        guard,
                    };
                    if !materialized.contains(&axiom) {
                        violated.push(axiom);
                    }
                }
            }
        }
    }
    Ok(violated)
}

fn violated_row_stores(
    arena: &TermArena,
    stores: &[CombinedRowStore],
    assignment: &Assignment,
    materialized: &HashSet<usize>,
    deadline: Option<Instant>,
) -> BuildResult<Vec<usize>> {
    let mut violated = Vec::new();
    for (index, store) in stores.iter().enumerate() {
        if materialized.contains(&index) {
            continue;
        }
        if deadline.is_some_and(|deadline| Instant::now() >= deadline) {
            return Err(build_unknown(
                UnknownKind::Timeout,
                "online AUFBV deadline elapsed while refining ROW axioms",
            ));
        }
        let Ok(read_index) = eval(arena, store.rewritten_index, assignment) else {
            continue;
        };
        let Ok(store_index) = eval(arena, store.rewritten_store_index, assignment) else {
            continue;
        };
        let Some(actual) = assignment.get(store.original.fresh) else {
            continue;
        };
        let expected_term = if read_index == store_index {
            store.rewritten_store_elem
        } else {
            store.rewritten_inner
        };
        if matches!(eval(arena, expected_term, assignment), Ok(expected) if actual != expected) {
            violated.push(index);
        }
    }
    Ok(violated)
}

fn violated_array_equality_axioms(
    arena: &TermArena,
    equalities: &[CombinedArrayEquality],
    assignment: &Assignment,
    materialized: &HashSet<ArrayEqualityAxiom>,
    deadline: Option<Instant>,
) -> BuildResult<Vec<ArrayEqualityAxiom>> {
    let mut violated = Vec::new();
    for (equality_index, equality) in equalities.iter().enumerate() {
        if deadline.is_some_and(|deadline| Instant::now() >= deadline) {
            return Err(build_unknown(
                UnknownKind::Timeout,
                "online AUFBV deadline elapsed while refining array extensionality",
            ));
        }
        let Some(Value::Bool(flag_true)) = assignment.get(equality.flag) else {
            continue;
        };
        for (observation_index, observation) in equality.observations.iter().enumerate() {
            let kind = if flag_true {
                ArrayEqualityAxiomKind::Equal
            } else if observation.is_diff_witness {
                ArrayEqualityAxiomKind::Diff
            } else {
                continue;
            };
            let axiom = ArrayEqualityAxiom {
                equality: equality_index,
                observation: observation_index,
                kind,
            };
            if materialized.contains(&axiom) {
                continue;
            }
            let reads_equal = matches!(
                (
                    eval(arena, observation.rewritten_lhs_read, assignment),
                    eval(arena, observation.rewritten_rhs_read, assignment)
                ),
                (Ok(lhs), Ok(rhs)) if lhs == rhs
            );
            let is_violated = match kind {
                ArrayEqualityAxiomKind::Equal => !reads_equal,
                ArrayEqualityAxiomKind::Diff => reads_equal,
            };
            if is_violated {
                violated.push(axiom);
            }
        }
    }
    Ok(violated)
}

fn rewritten_arguments_equal(
    arena: &TermArena,
    left: &CombinedApplication,
    right: &CombinedApplication,
    assignment: &Assignment,
) -> bool {
    debug_assert_eq!(left.rewritten_args.len(), right.rewritten_args.len());
    left.rewritten_args
        .iter()
        .zip(&right.rewritten_args)
        .all(|(&left, &right)| {
            match (
                eval(arena, left, assignment),
                eval(arena, right, assignment),
            ) {
                (Ok(left), Ok(right)) => left == right,
                _ => false,
            }
        })
}

fn application_results_differ(
    left: &CombinedApplication,
    right: &CombinedApplication,
    assignment: &Assignment,
) -> bool {
    matches!(
        (assignment.get(left.fresh), assignment.get(right.fresh)),
        (Some(left), Some(right)) if left != right
    )
}

#[cfg(test)]
fn relevant_application_pairs(
    arena: &TermArena,
    applications: &[CombinedApplication],
    groups: &[(FuncId, Vec<usize>)],
    deadline: Option<Instant>,
) -> BuildResult<Vec<(usize, usize)>> {
    let mut ground_values = GroundValueCache::default();
    let mut pairs = Vec::new();
    let mut interface_count = 0usize;
    for (_func, members) in groups {
        for left_pos in 0..members.len() {
            for right_pos in (left_pos + 1)..members.len() {
                if deadline.is_some_and(|deadline| Instant::now() >= deadline) {
                    return Err(build_unknown(
                        UnknownKind::Timeout,
                        "online UFBV deadline elapsed while filtering interface equalities",
                    ));
                }
                let left = members[left_pos];
                let right = members[right_pos];
                if applications_may_be_congruent(
                    arena,
                    &applications[left],
                    &applications[right],
                    &mut ground_values,
                ) {
                    interface_count = interface_count
                        .saturating_add(applications[left].original.args.len().saturating_add(1));
                    if interface_count > MAX_INTERFACE_ATOMS {
                        return Err(build_unknown(
                            UnknownKind::ResourceLimit,
                            format!(
                                "online UFBV relevant argument/result interface equalities exceed the bounded first-slice cap of {MAX_INTERFACE_ATOMS}"
                            ),
                        ));
                    }
                    pairs.push((left, right));
                }
            }
        }
    }
    Ok(pairs)
}

fn applications_may_be_congruent(
    arena: &TermArena,
    left: &CombinedApplication,
    right: &CombinedApplication,
    ground_values: &mut GroundValueCache,
) -> bool {
    debug_assert_eq!(left.original.args.len(), right.original.args.len());
    left.original
        .args
        .iter()
        .zip(&right.original.args)
        .all(|(&left, &right)| !ground_values.provably_distinct(arena, left, right))
}

fn add_interface_atoms(
    arena: &mut TermArena,
    applications: &[CombinedApplication],
    pairs: &[(usize, usize)],
    deadline: Option<Instant>,
    atoms: &mut AtomAccumulator,
) -> BuildResult<()> {
    for &(left, right) in pairs {
        if deadline.is_some_and(|deadline| Instant::now() >= deadline) {
            return Err(build_unknown(
                UnknownKind::Timeout,
                "online UFBV deadline elapsed while building interface equalities",
            ));
        }
        let left = &applications[left];
        let right = &applications[right];
        for ((&original_left, &original_right), (&abstract_left, &abstract_right)) in left
            .original
            .args
            .iter()
            .zip(&right.original.args)
            .zip(left.rewritten_args.iter().zip(&right.rewritten_args))
        {
            let original_eq = arena.eq(original_left, original_right)?;
            let abstract_eq = arena.eq(abstract_left, abstract_right)?;
            atoms.register(arena, original_eq, abstract_eq, true)?;
        }
        let original_result = arena.eq(left.original.term, right.original.term)?;
        let left_fresh = arena.var(left.fresh);
        let right_fresh = arena.var(right.fresh);
        let abstract_result = arena.eq(left_fresh, right_fresh)?;
        atoms.register(arena, original_result, abstract_result, true)?;
    }
    Ok(())
}

fn add_array_interface_atoms(
    arena: &mut TermArena,
    selects: &[CombinedSelect],
    axioms: &[ArraySelectAxiom],
    deadline: Option<Instant>,
    atoms: &mut AtomAccumulator,
    round_assertions: &mut Vec<TermId>,
) -> BuildResult<()> {
    for axiom in axioms {
        if deadline.is_some_and(|deadline| Instant::now() >= deadline) {
            return Err(build_unknown(
                UnknownKind::Timeout,
                "online AUFBV deadline elapsed while building array interfaces",
            ));
        }
        let left = &selects[axiom.left];
        let right = &selects[axiom.right];
        let original_index_eq = arena.eq(left.original_index, right.original_index)?;
        let abstract_index_eq = arena.eq(left.rewritten_index, right.rewritten_index)?;
        atoms.register(arena, original_index_eq, abstract_index_eq, true)?;

        let left_result = arena.var(left.fresh);
        let right_result = arena.var(right.fresh);
        let result_eq = arena.eq(left_result, right_result)?;
        atoms.register(arena, result_eq, result_eq, true)?;
        let mut antecedent = abstract_index_eq;
        for &guard in &axiom.guard {
            antecedent = arena.and(guard, antecedent)?;
        }
        round_assertions.push(arena.implies(antecedent, result_eq)?);
    }
    Ok(())
}

fn add_row_axiom_atoms(
    arena: &mut TermArena,
    stores: &[CombinedRowStore],
    sites: &[usize],
    deadline: Option<Instant>,
    atoms: &mut AtomAccumulator,
    round_assertions: &mut Vec<TermId>,
) -> BuildResult<()> {
    for &site in sites {
        if deadline.is_some_and(|deadline| Instant::now() >= deadline) {
            return Err(build_unknown(
                UnknownKind::Timeout,
                "online AUFBV deadline elapsed while building ROW axioms",
            ));
        }
        let store = &stores[site];
        let RowKind::Store {
            store_index,
            store_elem,
            inner,
        } = store.original.kind
        else {
            return Err(BuildFailure::Error(SolverError::Backend(
                "online ROW metadata lost its store kind".to_owned(),
            )));
        };
        let original_same = arena.eq(store.original.index, store_index)?;
        let abstract_same = arena.eq(store.rewritten_index, store.rewritten_store_index)?;
        atoms.register(arena, original_same, abstract_same, true)?;

        let result = arena.var(store.original.fresh);
        let original_hit = arena.eq(result, store_elem)?;
        let abstract_hit = arena.eq(result, store.rewritten_store_elem)?;
        atoms.register(arena, original_hit, abstract_hit, true)?;
        let original_miss = arena.eq(result, inner)?;
        let abstract_miss = arena.eq(result, store.rewritten_inner)?;
        atoms.register(arena, original_miss, abstract_miss, true)?;

        let hit = arena.implies(abstract_same, abstract_hit)?;
        let different = arena.not(abstract_same)?;
        let miss = arena.implies(different, abstract_miss)?;
        round_assertions.push(arena.and(hit, miss)?);
    }
    Ok(())
}

fn add_array_equality_axiom_atoms(
    arena: &mut TermArena,
    equalities: &[CombinedArrayEquality],
    axioms: &[ArrayEqualityAxiom],
    deadline: Option<Instant>,
    atoms: &mut AtomAccumulator,
    round_assertions: &mut Vec<TermId>,
) -> BuildResult<()> {
    for &axiom in axioms {
        if deadline.is_some_and(|deadline| Instant::now() >= deadline) {
            return Err(build_unknown(
                UnknownKind::Timeout,
                "online AUFBV deadline elapsed while building array extensionality axioms",
            ));
        }
        let equality = &equalities[axiom.equality];
        let observation = &equality.observations[axiom.observation];
        let original_read_eq =
            arena.eq(observation.original_lhs_read, observation.original_rhs_read)?;
        let abstract_read_eq = arena.eq(
            observation.rewritten_lhs_read,
            observation.rewritten_rhs_read,
        )?;
        atoms.register(arena, original_read_eq, abstract_read_eq, true)?;

        let flag = arena.var(equality.flag);
        let lemma = match axiom.kind {
            ArrayEqualityAxiomKind::Equal => arena.implies(flag, abstract_read_eq)?,
            ArrayEqualityAxiomKind::Diff => {
                let not_flag = arena.not(flag)?;
                let reads_differ = arena.not(abstract_read_eq)?;
                arena.implies(not_flag, reads_differ)?
            }
        };
        round_assertions.push(lemma);
    }
    Ok(())
}

fn encode_boolean_skeleton(
    arena: &TermArena,
    assertions: &[TermId],
    abstract_atoms: &[TermId],
    deadline: Option<Instant>,
) -> BuildResult<BooleanSkeleton> {
    let mut encoder = Encoder::new(abstract_atoms);
    let mut clauses = Vec::new();
    for &assertion in assertions {
        if deadline.is_some_and(|deadline| Instant::now() >= deadline) {
            return Err(build_unknown(
                UnknownKind::Timeout,
                "online UFBV deadline elapsed while encoding the Boolean skeleton",
            ));
        }
        let Some(top) = encoder.encode(arena, assertion, &mut clauses) else {
            return Err(BuildFailure::Error(SolverError::Unsupported(
                "Boolean skeleton outside the online UFBV encoder".to_owned(),
            )));
        };
        clauses.push(vec![crate::euf_egraph::Lit {
            var: top,
            positive: true,
        }]);
        if clauses.len() > MAX_BOOLEAN_CLAUSES {
            return Err(build_unknown(
                UnknownKind::ResourceLimit,
                format!("online UFBV Boolean skeleton exceeds {MAX_BOOLEAN_CLAUSES} clauses"),
            ));
        }
    }
    if encoder.var_count > MAX_BOOLEAN_VARIABLES {
        return Err(build_unknown(
            UnknownKind::ResourceLimit,
            format!(
                "online UFBV Boolean skeleton has {} variables, exceeding {MAX_BOOLEAN_VARIABLES}",
                encoder.var_count
            ),
        ));
    }
    let clauses = clauses
        .into_iter()
        .map(|clause| {
            clause
                .into_iter()
                .map(|lit| CdcltLit {
                    var: lit.var,
                    positive: lit.positive,
                })
                .collect()
        })
        .collect();
    Ok(BooleanSkeleton {
        variable_count: encoder.var_count,
        clauses,
    })
}

impl From<SolverError> for BuildFailure {
    fn from(error: SolverError) -> Self {
        Self::Error(error)
    }
}

impl From<axeyum_ir::IrError> for BuildFailure {
    fn from(error: axeyum_ir::IrError) -> Self {
        Self::Error(SolverError::from(error))
    }
}

fn build_unknown(kind: UnknownKind, detail: impl Into<String>) -> BuildFailure {
    BuildFailure::Unknown(UnknownReason {
        kind,
        detail: detail.into(),
    })
}

fn collect_formula_atoms(
    arena: &TermArena,
    term: TermId,
    atoms: &mut Vec<TermId>,
    seen: &mut HashSet<TermId>,
    deadline: Option<Instant>,
) -> Result<(), WalkError> {
    if deadline.is_some_and(|deadline| Instant::now() >= deadline) {
        return Err(WalkError::Timeout);
    }
    if !seen.insert(term) {
        return Ok(());
    }
    if arena.sort_of(term) != Sort::Bool {
        return Err(WalkError::NonBoolean(term));
    }
    match arena.node(term) {
        TermNode::BoolConst(_) => {}
        TermNode::App {
            op: Op::BoolNot | Op::BoolAnd | Op::BoolOr | Op::BoolImplies | Op::BoolXor | Op::Ite,
            args,
        } => {
            for &arg in args {
                collect_formula_atoms(arena, arg, atoms, seen, deadline)?;
            }
        }
        _ => atoms.push(term),
    }
    Ok(())
}

fn collect_original_applications(
    arena: &TermArena,
    assertions: &[TermId],
    deadline: Option<Instant>,
) -> Result<Vec<OriginalApplication>, WalkError> {
    fn visit(
        arena: &TermArena,
        term: TermId,
        seen: &mut HashSet<TermId>,
        out: &mut Vec<OriginalApplication>,
        deadline: Option<Instant>,
    ) -> Result<(), WalkError> {
        if deadline.is_some_and(|deadline| Instant::now() >= deadline) {
            return Err(WalkError::Timeout);
        }
        if !seen.insert(term) {
            return Ok(());
        }
        if let TermNode::App { op, args } = arena.node(term) {
            for &arg in args {
                visit(arena, arg, seen, out, deadline)?;
            }
            if let Op::Apply(func) = op {
                out.push(OriginalApplication {
                    term,
                    func: *func,
                    args: args.to_vec(),
                });
            }
        }
        Ok(())
    }

    let mut out = Vec::new();
    let mut seen = HashSet::new();
    for &assertion in assertions {
        visit(arena, assertion, &mut seen, &mut out, deadline)?;
    }
    Ok(out)
}

fn map_elim_error(error: FuncElimError) -> SolverError {
    match error {
        FuncElimError::Unsupported(message) => SolverError::Unsupported(message),
        FuncElimError::Ir(error) => SolverError::Backend(error.to_string()),
    }
}

fn project_replay_composed(
    arena: &TermArena,
    prepared: &PreparedAbstraction,
    assertions: &[TermId],
    assignment: &Assignment,
) -> CheckResult {
    let with_functions = match prepared.abstraction.project_model(arena, assignment) {
        Ok(projected) => projected,
        Err(error) => {
            return unknown(
                UnknownKind::Incomplete,
                format!("online AUFBV function projection failed: {error}"),
            );
        }
    };
    let projected = if prepared.had_arrays {
        let equivalent_arrays =
            true_symbol_array_equalities(arena, &prepared.array_equalities, &with_functions);
        match project_online_row_assignment(
            arena,
            &prepared.row_sites,
            &equivalent_arrays,
            &with_functions,
        ) {
            Ok(projected) => projected,
            Err(error) => {
                return unknown(
                    UnknownKind::Incomplete,
                    format!("online AUFBV array projection failed: {error}"),
                );
            }
        }
    } else {
        with_functions
    };

    for &assertion in assertions {
        match eval(arena, assertion, &projected) {
            Ok(Value::Bool(true)) => {}
            Ok(Value::Bool(false)) => {
                return unknown(
                    UnknownKind::Incomplete,
                    format!(
                        "online AUFBV projected candidate failed replay at assertion #{}",
                        assertion.index()
                    ),
                );
            }
            Ok(value) => {
                return unknown(
                    UnknownKind::Incomplete,
                    format!(
                        "online AUFBV replay produced non-Boolean {value} at assertion #{}",
                        assertion.index()
                    ),
                );
            }
            Err(error) => {
                return unknown(
                    UnknownKind::Incomplete,
                    format!(
                        "online AUFBV replay failed at assertion #{}: {error}",
                        assertion.index()
                    ),
                );
            }
        }
    }

    let mut model = Model::new();
    for (symbol, name, _sort) in arena.symbols() {
        if name.starts_with("!row_sel_")
            || name.starts_with("!ext_eq_")
            || name.starts_with("!ext_diff_")
            || name.starts_with("!fn_app_")
        {
            continue;
        }
        if let Some(value) = projected.get(symbol) {
            model.set(symbol, value);
        }
    }
    for (func, _name, _params, _result) in arena.functions() {
        if let Some(value) = projected.function(func) {
            model.set_function(func, value.clone());
        }
    }
    CheckResult::Sat(model)
}

fn true_symbol_array_equalities(
    arena: &TermArena,
    equalities: &[CombinedArrayEquality],
    assignment: &Assignment,
) -> Vec<(SymbolId, SymbolId)> {
    let mut pairs = Vec::new();
    for equality in equalities {
        if !matches!(assignment.get(equality.flag), Some(Value::Bool(true))) {
            continue;
        }
        let (TermNode::Symbol(left), TermNode::Symbol(right)) =
            (arena.node(equality.lhs), arena.node(equality.rhs))
        else {
            continue;
        };
        pairs.push((*left, *right));
    }
    pairs
}

fn unknown(kind: UnknownKind, detail: impl Into<String>) -> CheckResult {
    CheckResult::Unknown(UnknownReason {
        kind,
        detail: detail.into(),
    })
}

#[cfg(test)]
mod tests {
    use std::time::Duration;

    use axeyum_ir::{Sort, TermArena, TermId, TermNode, Value, eval};
    use axeyum_smtlib::parse_script;

    use super::{
        BvTheory, CombinedUfbvTheory, application_groups, build_and_solve_arrays_with_stats,
        build_and_solve_with_stats, build_theory_atoms, check_qf_aufbv_online_cdclt,
        check_qf_ufbv_online_cdclt, encode_boolean_skeleton, prepare_abstraction,
        relevant_application_pairs,
    };
    use crate::cdclt::{CdclT, Outcome};
    use crate::euf_egraph::EufTheory;
    use crate::euf_egraph::{TheoryLit, TheoryProp};
    use crate::{CheckResult, SolverConfig};

    #[derive(Debug)]
    struct RawSolveStats {
        outcome: Outcome,
        interface_atoms: usize,
        propagation_probes: usize,
        propagation_hits: usize,
        driver_propagations: usize,
    }

    #[test]
    fn array_flags_preserve_original_equalities_for_the_egraph() {
        let mut arena = TermArena::new();
        let left = arena.array_var("egraph_flag_left", 4, 8).unwrap();
        let right = arena.array_var("egraph_flag_right", 4, 8).unwrap();
        let original_equality = arena.eq(left, right).unwrap();
        let prepared = prepare_abstraction(&mut arena, &[original_equality], None, true)
            .expect("array equality should abstract");
        let flag = arena.var(prepared.array_equalities[0].flag);
        let (atoms, _assertions) =
            build_theory_atoms(&mut arena, &prepared, &[], &[], &[], &[], None)
                .expect("array equality should build theory atoms");
        let atom = atoms
            .abstracted
            .iter()
            .position(|&term| term == flag)
            .expect("array flag should be a canonical theory atom");
        assert_eq!(atoms.original[atom], original_equality);
    }

    fn raw_solve_stats(arena: &mut TermArena, assertions: &[axeyum_ir::TermId]) -> RawSolveStats {
        let prepared = prepare_abstraction(arena, assertions, None, false)
            .expect("bounded UFBV case should abstract");
        let groups = application_groups(&prepared.applications);
        let pairs = relevant_application_pairs(arena, &prepared.applications, &groups, None)
            .expect("bounded UFBV case should select interface pairs");
        let (atoms, round_assertions) =
            build_theory_atoms(arena, &prepared, &pairs, &[], &[], &[], None)
                .expect("bounded UFBV case should build theory atoms");
        let skeleton = encode_boolean_skeleton(arena, &round_assertions, &atoms.abstracted, None)
            .expect("bounded UFBV case should encode");
        let negative = atoms
            .abstracted
            .iter()
            .map(|&atom| arena.not(atom).unwrap())
            .collect();
        let atom_count = atoms.original.len();
        let interface_atoms = atoms
            .propagation_candidates
            .iter()
            .filter(|&&candidate| candidate)
            .count();
        let euf = EufTheory::new(arena, &atoms.original);
        let bv = BvTheory::new(
            arena,
            atoms.abstracted,
            negative,
            atoms.propagation_candidates,
            &SolverConfig::default(),
            None,
        );
        let mut theory = CombinedUfbvTheory { euf, bv };
        let mut solver = CdclT::new(skeleton.variable_count, atom_count, skeleton.clauses, None);
        let outcome = solver.solve(&mut theory);
        RawSolveStats {
            outcome,
            interface_atoms,
            propagation_probes: theory.bv.propagation_probes,
            propagation_hits: theory.bv.propagation_hits,
            driver_propagations: solver.theory_propagations(),
        }
    }

    fn dynamic_solve_stats(
        arena: &mut TermArena,
        assertions: &[axeyum_ir::TermId],
    ) -> (CheckResult, super::InterfaceRefinementStats) {
        build_and_solve_with_stats(arena, assertions, &SolverConfig::default(), None)
            .expect("bounded UFBV refinement case should build")
    }

    fn dynamic_array_solve_stats(
        arena: &mut TermArena,
        assertions: &[axeyum_ir::TermId],
    ) -> (CheckResult, super::InterfaceRefinementStats) {
        build_and_solve_arrays_with_stats(arena, assertions, &SolverConfig::default(), None)
            .expect("bounded AUFBV refinement case should build")
    }

    #[test]
    fn warm_bv_final_conflict_drops_irrelevant_literal() {
        let mut arena = TermArena::new();
        let x = arena.bv_var("core_x", 4).unwrap();
        let z = arena.bv_var("core_z", 4).unwrap();
        let zero = arena.bv_const(4, 0).unwrap();
        let one = arena.bv_const(4, 1).unwrap();
        let z_zero = arena.eq(z, zero).unwrap();
        let x_zero = arena.eq(x, zero).unwrap();
        let x_one = arena.eq(x, one).unwrap();
        let positive = vec![z_zero, x_zero, x_one];
        let negative = positive
            .iter()
            .map(|&atom| arena.not(atom).unwrap())
            .collect();
        let mut theory = BvTheory::new(
            &arena,
            positive,
            negative,
            vec![false; 3],
            &SolverConfig::default(),
            None,
        );

        theory.push();
        assert!(theory.assert(0, true).is_ok());
        theory.push();
        assert!(theory.assert(1, true).is_ok());
        theory.push();
        let core = theory.assert(2, true).unwrap_err();
        assert_eq!(
            core,
            vec![
                TheoryLit {
                    atom: 1,
                    value: true
                },
                TheoryLit {
                    atom: 2,
                    value: true
                }
            ]
        );
    }

    #[test]
    fn warm_bv_decision_frames_follow_theory_backtracking() {
        let mut arena = TermArena::new();
        let x = arena.bv_var("scope_x", 4).unwrap();
        let zero = arena.bv_const(4, 0).unwrap();
        let one = arena.bv_const(4, 1).unwrap();
        let x_zero = arena.eq(x, zero).unwrap();
        let x_one = arena.eq(x, one).unwrap();
        let positive = vec![x_zero, x_one];
        let negative = positive
            .iter()
            .map(|&atom| arena.not(atom).unwrap())
            .collect();
        let mut theory = BvTheory::new(
            &arena,
            positive,
            negative,
            vec![false; 2],
            &SolverConfig::default(),
            None,
        );

        theory.push();
        assert!(theory.assert(0, true).is_ok());
        assert_eq!(theory.solver.scope_depth(), 1);
        theory.pop();
        assert_eq!(theory.solver.scope_depth(), 0);
        assert!(theory.assert(1, true).is_ok());
    }

    #[test]
    fn warm_bv_propagates_an_entailed_interface_equality() {
        let mut arena = TermArena::new();
        let x = arena.bv_var("prop_x", 4).unwrap();
        let y = arena.bv_var("prop_y", 4).unwrap();
        let one = arena.bv_const(4, 1).unwrap();
        let x_shifted = arena.bv_add(x, one).unwrap();
        let y_shifted = arena.bv_add(y, one).unwrap();
        let same_shifted = arena.eq(x_shifted, y_shifted).unwrap();
        let same_input = arena.eq(x, y).unwrap();
        let positive = vec![same_shifted, same_input];
        let negative = positive
            .iter()
            .map(|&atom| arena.not(atom).unwrap())
            .collect();
        let mut theory = BvTheory::new(
            &arena,
            positive,
            negative,
            vec![false, true],
            &SolverConfig::default(),
            None,
        );

        assert!(theory.assert(0, true).is_ok());
        assert_eq!(
            theory.propagations(),
            vec![TheoryProp {
                lit: TheoryLit {
                    atom: 1,
                    value: true
                },
                reason: vec![TheoryLit {
                    atom: 0,
                    value: true
                }]
            }]
        );
    }

    #[test]
    fn cdclt_driver_consumes_bv_interface_propagation() {
        let mut arena = TermArena::new();
        let function = arena
            .declare_fun("prop_f", &[Sort::BitVec(4)], Sort::BitVec(4))
            .unwrap();
        let x = arena.bv_var("driver_prop_x", 4).unwrap();
        let y = arena.bv_var("driver_prop_y", 4).unwrap();
        let one = arena.bv_const(4, 1).unwrap();
        let x_shifted = arena.bv_add(x, one).unwrap();
        let y_shifted = arena.bv_add(y, one).unwrap();
        let same_shifted = arena.eq(x_shifted, y_shifted).unwrap();
        let fx = arena.apply(function, &[x]).unwrap();
        let fy = arena.apply(function, &[y]).unwrap();
        let same_result = arena.eq(fx, fy).unwrap();
        let assertions = vec![same_shifted, same_result];
        let stats = raw_solve_stats(&mut arena, &assertions);
        assert_eq!(stats.outcome, Outcome::Sat);
        assert!(
            stats.driver_propagations > 0,
            "the canonical driver should consume the BV-implied x=y interface equality; probes={}, hits={}",
            stats.propagation_probes,
            stats.propagation_hits,
        );
    }

    #[test]
    fn bug520_exercises_bounded_bv_interface_propagation() {
        let mut script = parse_script(include_str!(
            "../../../corpus/public-curated/non-incremental/QF_UFBV/cvc5-regress-clean/cli__regress1__bug520.smt2"
        ))
        .expect("bug520 parses");
        let stats = raw_solve_stats(&mut script.arena, &script.assertions);

        assert_eq!(stats.outcome, Outcome::Sat);
        assert_eq!(stats.interface_atoms, 20);
        assert!(stats.propagation_probes > 0, "stats={stats:?}");
        assert!(stats.propagation_hits > 0, "stats={stats:?}");
        assert!(stats.driver_propagations > 0, "stats={stats:?}");
    }

    #[test]
    fn bug520_materializes_only_violated_interface_pairs() {
        let mut script = parse_script(include_str!(
            "../../../corpus/public-curated/non-incremental/QF_UFBV/cvc5-regress-clean/cli__regress1__bug520.smt2"
        ))
        .expect("bug520 parses");
        let (result, stats) = dynamic_solve_stats(&mut script.arena, &script.assertions);

        assert!(matches!(result, CheckResult::Sat(_)), "stats={stats:?}");
        assert_eq!(stats.rounds, 1, "stats={stats:?}");
        assert_eq!(stats.sat_candidates, 1, "stats={stats:?}");
        assert_eq!(stats.pairs_added, 0, "stats={stats:?}");
        assert_eq!(stats.max_interface_atoms, 0, "stats={stats:?}");
    }

    #[test]
    fn statically_distinct_ground_keys_prune_impossible_application_pairs() {
        let mut arena = TermArena::new();
        let f = arena
            .declare_fun("relevant_f", &[Sort::BitVec(4)], Sort::BitVec(4))
            .unwrap();
        let zero = arena.bv_const(4, 0).unwrap();
        let one = arena.bv_const(4, 1).unwrap();
        let two = arena.bv_const(4, 2).unwrap();
        let x = arena.bv_var("relevant_x", 4).unwrap();
        let f_zero = arena.apply(f, &[zero]).unwrap();
        let f_one = arena.apply(f, &[one]).unwrap();
        let f_x = arena.apply(f, &[x]).unwrap();
        let assertions = [
            arena.eq(f_zero, zero).unwrap(),
            arena.eq(f_one, one).unwrap(),
            arena.eq(f_x, two).unwrap(),
        ];

        let stats = raw_solve_stats(&mut arena, &assertions);
        assert_eq!(stats.outcome, Outcome::Sat);
        assert_eq!(stats.interface_atoms, 4, "stats={stats:?}");
    }

    #[test]
    fn equal_ground_values_keep_their_congruence_pair() {
        let mut arena = TermArena::new();
        let f = arena
            .declare_fun("ground_equal_f", &[Sort::BitVec(4)], Sort::BitVec(4))
            .unwrap();
        let one = arena.bv_const(4, 1).unwrap();
        let two = arena.bv_const(4, 2).unwrap();
        let computed_two = arena.bv_add(one, one).unwrap();
        assert_ne!(computed_two, two);
        let direct = arena.apply(f, &[two]).unwrap();
        let computed = arena.apply(f, &[computed_two]).unwrap();
        let same_result = arena.eq(direct, computed).unwrap();
        let different_result = arena.not(same_result).unwrap();

        let stats = raw_solve_stats(&mut arena, &[different_result]);
        assert_eq!(stats.outcome, Outcome::Unsat);
        assert_eq!(stats.interface_atoms, 2, "stats={stats:?}");
    }

    #[test]
    fn bv_implied_argument_equality_refutes_uf_disequality() {
        let mut arena = TermArena::new();
        let f = arena
            .declare_fun("f", &[Sort::BitVec(4)], Sort::BitVec(4))
            .unwrap();
        let x = arena.bv_var("x", 4).unwrap();
        let y = arena.bv_var("y", 4).unwrap();
        let one = arena.bv_const(4, 1).unwrap();
        let x1 = arena.bv_add(x, one).unwrap();
        let y1 = arena.bv_add(y, one).unwrap();
        let same_shifted = arena.eq(x1, y1).unwrap();
        let fx = arena.apply(f, &[x]).unwrap();
        let fy = arena.apply(f, &[y]).unwrap();
        let same_result = arena.eq(fx, fy).unwrap();
        let different_result = arena.not(same_result).unwrap();

        assert_eq!(
            check_qf_ufbv_online_cdclt(
                &mut arena,
                &[same_shifted, different_result],
                &SolverConfig::default(),
            )
            .unwrap(),
            CheckResult::Unsat
        );
    }

    #[test]
    fn congruent_results_flow_into_bv_ordering() {
        let mut arena = TermArena::new();
        let f = arena
            .declare_fun("f", &[Sort::BitVec(4)], Sort::BitVec(4))
            .unwrap();
        let x = arena.bv_var("x", 4).unwrap();
        let y = arena.bv_var("y", 4).unwrap();
        let same_arg = arena.eq(x, y).unwrap();
        let fx = arena.apply(f, &[x]).unwrap();
        let fy = arena.apply(f, &[y]).unwrap();
        let strict = arena.bv_ult(fx, fy).unwrap();

        let (result, stats) = dynamic_solve_stats(&mut arena, &[same_arg, strict]);
        assert_eq!(result, CheckResult::Unsat);
        assert_eq!(stats.rounds, 2, "stats={stats:?}");
        assert_eq!(stats.sat_candidates, 1, "stats={stats:?}");
        assert_eq!(stats.pairs_added, 1, "stats={stats:?}");
        assert_eq!(stats.max_interface_atoms, 2, "stats={stats:?}");
    }

    #[test]
    fn nested_congruence_refines_to_a_fixpoint() {
        let mut arena = TermArena::new();
        let g = arena
            .declare_fun("dynamic_g", &[Sort::BitVec(4)], Sort::BitVec(4))
            .unwrap();
        let f = arena
            .declare_fun("dynamic_outer_f", &[Sort::BitVec(4)], Sort::BitVec(4))
            .unwrap();
        let x = arena.bv_var("dynamic_nested_x", 4).unwrap();
        let y = arena.bv_var("dynamic_nested_y", 4).unwrap();
        let same_arg = arena.eq(x, y).unwrap();
        let gx = arena.apply(g, &[x]).unwrap();
        let gy = arena.apply(g, &[y]).unwrap();
        let g_strict = arena.bv_ult(gx, gy).unwrap();
        let fallback = arena.bool_var("dynamic_nested_fallback").unwrap();
        let g_strict_or_fallback = arena.or(g_strict, fallback).unwrap();
        let fgx = arena.apply(f, &[gx]).unwrap();
        let fgy = arena.apply(f, &[gy]).unwrap();
        let strict = arena.bv_ult(fgx, fgy).unwrap();

        let (result, stats) =
            dynamic_solve_stats(&mut arena, &[same_arg, g_strict_or_fallback, strict]);
        assert_eq!(result, CheckResult::Unsat);
        assert_eq!(stats.rounds, 3, "stats={stats:?}");
        assert_eq!(stats.sat_candidates, 2, "stats={stats:?}");
        assert_eq!(stats.pairs_added, 2, "stats={stats:?}");
        assert_eq!(stats.max_interface_atoms, 3, "stats={stats:?}");
    }

    #[test]
    fn array_select_congruence_refines_in_two_rounds() {
        let mut arena = TermArena::new();
        let array = arena.array_var("dynamic_array", 4, 8).unwrap();
        let i = arena.bv_var("dynamic_array_i", 4).unwrap();
        let j = arena.bv_var("dynamic_array_j", 4).unwrap();
        let read_i = arena.select(array, i).unwrap();
        let read_j = arena.select(array, j).unwrap();
        let same_index = arena.eq(i, j).unwrap();
        let same_read = arena.eq(read_i, read_j).unwrap();
        let different_read = arena.not(same_read).unwrap();

        let (result, stats) = dynamic_array_solve_stats(&mut arena, &[same_index, different_read]);
        assert_eq!(result, CheckResult::Unsat);
        assert_eq!(stats.rounds, 2, "stats={stats:?}");
        assert_eq!(stats.sat_candidates, 1, "stats={stats:?}");
        assert_eq!(stats.array_pairs_added, 1, "stats={stats:?}");
        assert_eq!(stats.function_pairs_added, 0, "stats={stats:?}");
        assert_eq!(stats.max_interface_atoms, 2, "stats={stats:?}");
    }

    #[test]
    fn array_then_function_congruence_reaches_a_fixpoint() {
        let mut arena = TermArena::new();
        let array = arena.array_var("dynamic_nested_array", 4, 4).unwrap();
        let function = arena
            .declare_fun("dynamic_array_outer_f", &[Sort::BitVec(4)], Sort::BitVec(4))
            .unwrap();
        let i = arena.bv_var("dynamic_nested_array_i", 4).unwrap();
        let j = arena.bv_var("dynamic_nested_array_j", 4).unwrap();
        let same_index = arena.eq(i, j).unwrap();
        let read_i = arena.select(array, i).unwrap();
        let read_j = arena.select(array, j).unwrap();
        let read_strict = arena.bv_ult(read_i, read_j).unwrap();
        let fallback = arena.bool_var("dynamic_array_fallback").unwrap();
        let read_strict_or_fallback = arena.or(read_strict, fallback).unwrap();
        let f_read_i = arena.apply(function, &[read_i]).unwrap();
        let f_read_j = arena.apply(function, &[read_j]).unwrap();
        let result_strict = arena.bv_ult(f_read_i, f_read_j).unwrap();

        let (result, stats) = dynamic_array_solve_stats(
            &mut arena,
            &[same_index, read_strict_or_fallback, result_strict],
        );
        assert_eq!(result, CheckResult::Unsat);
        assert_eq!(stats.rounds, 3, "stats={stats:?}");
        assert_eq!(stats.sat_candidates, 2, "stats={stats:?}");
        assert_eq!(stats.array_pairs_added, 1, "stats={stats:?}");
        assert_eq!(stats.function_pairs_added, 1, "stats={stats:?}");
        assert_eq!(stats.pairs_added, 2, "stats={stats:?}");
    }

    #[test]
    fn merged_array_parents_schedule_select_congruence() {
        let mut arena = TermArena::new();
        let left = arena.array_var("dynamic_eq_left", 4, 8).unwrap();
        let right = arena.array_var("dynamic_eq_right", 4, 8).unwrap();
        let index = arena.bv_const(4, 5).unwrap();
        let arrays_equal = arena.eq(left, right).unwrap();
        let left_read = arena.select(left, index).unwrap();
        let right_read = arena.select(right, index).unwrap();
        let reads_equal = arena.eq(left_read, right_read).unwrap();
        let reads_differ = arena.not(reads_equal).unwrap();

        let (result, stats) = dynamic_array_solve_stats(&mut arena, &[arrays_equal, reads_differ]);
        assert_eq!(result, CheckResult::Unsat);
        assert_eq!(stats.rounds, 2, "stats={stats:?}");
        assert_eq!(stats.sat_candidates, 1, "stats={stats:?}");
        assert_eq!(stats.parent_select_pairs_added, 1, "stats={stats:?}");
        assert_eq!(stats.array_equality_axioms_added, 0, "stats={stats:?}");
    }

    #[test]
    fn transitive_parent_merge_schedules_only_the_violated_endpoint_reads() {
        let mut arena = TermArena::new();
        let a = arena.array_var("dynamic_parent_a", 4, 8).unwrap();
        let b = arena.array_var("dynamic_parent_b", 4, 8).unwrap();
        let c = arena.array_var("dynamic_parent_c", 4, 8).unwrap();
        let index = arena.bv_const(4, 5).unwrap();
        let a_eq_b = arena.eq(a, b).unwrap();
        let b_eq_c = arena.eq(b, c).unwrap();
        let read_a = arena.select(a, index).unwrap();
        let read_c = arena.select(c, index).unwrap();
        let reads_equal = arena.eq(read_a, read_c).unwrap();
        let reads_differ = arena.not(reads_equal).unwrap();

        let (result, stats) =
            dynamic_array_solve_stats(&mut arena, &[a_eq_b, b_eq_c, reads_differ]);
        assert_eq!(result, CheckResult::Unsat, "stats={stats:?}");
        assert_eq!(stats.rounds, 2, "stats={stats:?}");
        assert_eq!(stats.parent_select_pairs_added, 1, "stats={stats:?}");
        assert_eq!(stats.array_equality_axioms_added, 0, "stats={stats:?}");
    }

    #[test]
    fn direct_symbol_equalities_do_not_prepare_the_query_index_cross_product() {
        let mut arena = TermArena::new();
        let arrays: Vec<_> = (0..80)
            .map(|index| {
                arena
                    .array_var(&format!("dynamic_parent_scale_{index}"), 8, 8)
                    .unwrap()
            })
            .collect();
        let zero = arena.bv_const(8, 0).unwrap();
        let mut assertions = Vec::new();
        for pair in arrays.windows(2) {
            assertions.push(arena.eq(pair[0], pair[1]).unwrap());
        }
        for (index, &array) in arrays.iter().enumerate() {
            let index = arena.bv_const(8, index as u128).unwrap();
            let read = arena.select(array, index).unwrap();
            assertions.push(arena.eq(read, zero).unwrap());
        }

        let (result, stats) = dynamic_array_solve_stats(&mut arena, &assertions);
        assert!(matches!(result, CheckResult::Sat(_)), "stats={stats:?}");
        assert_eq!(stats.rounds, 1, "stats={stats:?}");
        assert_eq!(stats.parent_select_pairs_added, 0, "stats={stats:?}");
        assert_eq!(stats.array_equality_axioms_added, 0, "stats={stats:?}");
    }

    #[test]
    fn transitive_array_disequality_refutes_on_the_live_egraph() {
        let mut arena = TermArena::new();
        let a = arena.array_var("dynamic_queue_a", 4, 8).unwrap();
        let b = arena.array_var("dynamic_queue_b", 4, 8).unwrap();
        let c = arena.array_var("dynamic_queue_c", 4, 8).unwrap();
        let a_eq_b = arena.eq(a, b).unwrap();
        let b_eq_c = arena.eq(b, c).unwrap();
        let a_eq_c = arena.eq(a, c).unwrap();
        let a_ne_c = arena.not(a_eq_c).unwrap();

        let (result, stats) = dynamic_array_solve_stats(&mut arena, &[a_eq_b, b_eq_c, a_ne_c]);
        assert_eq!(result, CheckResult::Unsat, "stats={stats:?}");
        assert_eq!(stats.rounds, 1, "stats={stats:?}");
        assert_eq!(stats.sat_candidates, 0, "stats={stats:?}");
        assert_eq!(stats.array_equality_axioms_added, 0, "stats={stats:?}");
    }

    #[test]
    fn disconnected_array_disequality_replays_with_class_owned_models() {
        let mut arena = TermArena::new();
        let a = arena.array_var("dynamic_delayed_a", 4, 8).unwrap();
        let b = arena.array_var("dynamic_delayed_b", 4, 8).unwrap();
        let c = arena.array_var("dynamic_delayed_c", 4, 8).unwrap();
        let d = arena.array_var("dynamic_delayed_d", 4, 8).unwrap();
        let a_eq_b = arena.eq(a, b).unwrap();
        let c_eq_d = arena.eq(c, d).unwrap();
        let c_ne_d = arena.not(c_eq_d).unwrap();

        let (result, stats) = dynamic_array_solve_stats(&mut arena, &[a_eq_b, c_ne_d]);
        let CheckResult::Sat(model) = result else {
            panic!("expected replayed SAT, stats={stats:?}");
        };
        let assignment = model.to_assignment();
        assert_eq!(eval(&arena, a_eq_b, &assignment), Ok(Value::Bool(true)));
        assert_eq!(eval(&arena, c_ne_d, &assignment), Ok(Value::Bool(true)));
        assert_eq!(eval(&arena, a, &assignment), eval(&arena, b, &assignment));
    }

    #[test]
    fn boolean_array_choice_backtracks_and_projects_the_surviving_class() {
        let mut arena = TermArena::new();
        let a = arena.array_var("dynamic_backtrack_a", 4, 8).unwrap();
        let b = arena.array_var("dynamic_backtrack_b", 4, 8).unwrap();
        let c = arena.array_var("dynamic_backtrack_c", 4, 8).unwrap();
        let a_eq_b = arena.eq(a, b).unwrap();
        let a_eq_c = arena.eq(a, c).unwrap();
        let choice = arena.or(a_eq_b, a_eq_c).unwrap();
        let a_ne_b = arena.not(a_eq_b).unwrap();

        let (result, stats) = dynamic_array_solve_stats(&mut arena, &[choice, a_ne_b]);
        let CheckResult::Sat(model) = result else {
            panic!("expected the non-conflicting equality branch, stats={stats:?}");
        };
        let assignment = model.to_assignment();
        assert_eq!(eval(&arena, choice, &assignment), Ok(Value::Bool(true)));
        assert_eq!(eval(&arena, a_ne_b, &assignment), Ok(Value::Bool(true)));
        assert_eq!(eval(&arena, a_eq_c, &assignment), Ok(Value::Bool(true)));
        assert_eq!(eval(&arena, a, &assignment), eval(&arena, c, &assignment));
    }

    #[test]
    fn parent_select_axiom_is_guarded_across_boolean_array_branches() {
        let mut arena = TermArena::new();
        let a = arena.array_var("dynamic_guard_a", 4, 8).unwrap();
        let b = arena.array_var("dynamic_guard_b", 4, 8).unwrap();
        let c = arena.array_var("dynamic_guard_c", 4, 8).unwrap();
        let index = arena.bv_const(4, 5).unwrap();
        let a_eq_b = arena.eq(a, b).unwrap();
        let a_eq_c = arena.eq(a, c).unwrap();
        let choice = arena.or(a_eq_b, a_eq_c).unwrap();
        let read_a = arena.select(a, index).unwrap();
        let read_b = arena.select(b, index).unwrap();
        let reads_equal = arena.eq(read_a, read_b).unwrap();
        let reads_differ = arena.not(reads_equal).unwrap();

        let (result, stats) = dynamic_array_solve_stats(&mut arena, &[choice, reads_differ]);
        let CheckResult::Sat(model) = result else {
            panic!("expected the alternate array-equality branch, stats={stats:?}");
        };
        let assignment = model.to_assignment();
        assert_eq!(eval(&arena, choice, &assignment), Ok(Value::Bool(true)));
        assert_eq!(
            eval(&arena, reads_differ, &assignment),
            Ok(Value::Bool(true))
        );
        assert_eq!(eval(&arena, a_eq_b, &assignment), Ok(Value::Bool(false)));
        assert_eq!(eval(&arena, a_eq_c, &assignment), Ok(Value::Bool(true)));
        assert!(stats.parent_select_pairs_added >= 1, "stats={stats:?}");
    }

    #[test]
    fn parent_select_pair_reschedules_for_an_alternate_equality_explanation() {
        let mut arena = TermArena::new();
        let a = arena.array_var("dynamic_reguard_a", 4, 8).unwrap();
        let b = arena.array_var("dynamic_reguard_b", 4, 8).unwrap();
        let c = arena.array_var("dynamic_reguard_c", 4, 8).unwrap();
        let d = arena.array_var("dynamic_reguard_d", 4, 8).unwrap();
        let index = arena.bv_const(4, 5).unwrap();
        let a_eq_c = arena.eq(a, c).unwrap();
        let c_eq_b = arena.eq(c, b).unwrap();
        let a_eq_d = arena.eq(a, d).unwrap();
        let d_eq_b = arena.eq(d, b).unwrap();
        let path_c = arena.and(a_eq_c, c_eq_b).unwrap();
        let path_d = arena.and(a_eq_d, d_eq_b).unwrap();
        let choice = arena.or(path_c, path_d).unwrap();
        let read_a = arena.select(a, index).unwrap();
        let read_b = arena.select(b, index).unwrap();
        let reads_equal = arena.eq(read_a, read_b).unwrap();
        let reads_differ = arena.not(reads_equal).unwrap();

        let (result, stats) = dynamic_array_solve_stats(&mut arena, &[choice, reads_differ]);
        assert_eq!(result, CheckResult::Unsat, "stats={stats:?}");
        assert!(stats.parent_select_pairs_added >= 2, "stats={stats:?}");
    }

    #[test]
    fn transitive_symbol_equalities_share_one_projected_array_model() {
        let mut arena = TermArena::new();
        let a = arena.array_var("dynamic_class_a", 4, 8).unwrap();
        let b = arena.array_var("dynamic_class_b", 4, 8).unwrap();
        let c = arena.array_var("dynamic_class_c", 4, 8).unwrap();
        let index_a = arena.bv_const(4, 1).unwrap();
        let index_c = arena.bv_const(4, 2).unwrap();
        let value_a = arena.bv_const(8, 7).unwrap();
        let value_c = arena.bv_const(8, 9).unwrap();
        let a_eq_b = arena.eq(a, b).unwrap();
        let b_eq_c = arena.eq(b, c).unwrap();
        let read_a = arena.select(a, index_a).unwrap();
        let read_c = arena.select(c, index_c).unwrap();
        let pin_a = arena.eq(read_a, value_a).unwrap();
        let pin_c = arena.eq(read_c, value_c).unwrap();

        let (result, stats) =
            dynamic_array_solve_stats(&mut arena, &[a_eq_b, b_eq_c, pin_a, pin_c]);
        let CheckResult::Sat(model) = result else {
            panic!("expected a class-owned SAT model, stats={stats:?}");
        };
        let assignment = model.to_assignment();
        let a_value = eval(&arena, a, &assignment).expect("projected a");
        assert_eq!(eval(&arena, b, &assignment), Ok(a_value.clone()));
        assert_eq!(eval(&arena, c, &assignment), Ok(a_value.clone()));
        assert_eq!(eval(&arena, pin_a, &assignment), Ok(Value::Bool(true)));
        assert_eq!(eval(&arena, pin_c, &assignment), Ok(Value::Bool(true)));
        let array = a_value.as_array().expect("compact BV array model");
        assert_eq!(array.select(1), 7);
        assert_eq!(array.select(2), 9);
    }

    #[test]
    fn store_and_uf_array_path_refutes_on_the_live_egraph() {
        let mut arena = TermArena::new();
        let a = arena.array_var("dynamic_queue_store_a", 4, 8).unwrap();
        let b = arena.array_var("dynamic_queue_store_b", 4, 8).unwrap();
        let c = arena.array_var("dynamic_queue_store_c", 4, 8).unwrap();
        let function = arena
            .declare_fun(
                "dynamic_queue_store_index",
                &[Sort::BitVec(4)],
                Sort::BitVec(4),
            )
            .unwrap();
        let x = arena.bv_var("dynamic_queue_store_x", 4).unwrap();
        let value = arena.bv_var("dynamic_queue_store_value", 8).unwrap();
        let index = arena.apply(function, &[x]).unwrap();
        let stored = arena.store(a, index, value).unwrap();
        let stored_eq_b = arena.eq(stored, b).unwrap();
        let b_eq_c = arena.eq(b, c).unwrap();
        let stored_eq_c = arena.eq(stored, c).unwrap();
        let stored_ne_c = arena.not(stored_eq_c).unwrap();

        let (result, stats) =
            dynamic_array_solve_stats(&mut arena, &[stored_eq_b, b_eq_c, stored_ne_c]);
        assert_eq!(result, CheckResult::Unsat, "stats={stats:?}");
        assert_eq!(stats.rounds, 1, "stats={stats:?}");
        assert_eq!(stats.sat_candidates, 0, "stats={stats:?}");
        assert_eq!(stats.row_axioms_added, 0, "stats={stats:?}");
    }

    #[test]
    fn egraph_transitivity_avoids_the_cross_observation_cap() {
        let mut arena = TermArena::new();
        let arrays: Vec<_> = (0..40)
            .map(|index| {
                arena
                    .array_var(&format!("dynamic_queue_cap_{index}"), 4, 8)
                    .unwrap()
            })
            .collect();
        let mut assertions = Vec::new();
        for pair in arrays.windows(2) {
            assertions.push(arena.eq(pair[0], pair[1]).unwrap());
        }
        for target in 20..40 {
            let equal = arena.eq(arrays[0], arrays[target]).unwrap();
            assertions.push(arena.not(equal).unwrap());
        }

        let (result, stats) = dynamic_array_solve_stats(&mut arena, &assertions);
        assert_eq!(result, CheckResult::Unsat, "stats={stats:?}");
        assert_eq!(stats.rounds, 1, "stats={stats:?}");
        assert_eq!(stats.sat_candidates, 0, "stats={stats:?}");
        assert_eq!(stats.array_equality_axioms_added, 0, "stats={stats:?}");
    }

    #[test]
    fn self_array_disequality_refutes_on_the_live_egraph() {
        let mut arena = TermArena::new();
        let array = arena.array_var("dynamic_self_diff", 4, 8).unwrap();
        let self_equal = arena.eq(array, array).unwrap();
        let self_different = arena.not(self_equal).unwrap();

        let (result, stats) = dynamic_array_solve_stats(&mut arena, &[self_different]);
        assert_eq!(result, CheckResult::Unsat);
        assert_eq!(stats.rounds, 1, "stats={stats:?}");
        assert_eq!(stats.sat_candidates, 0, "stats={stats:?}");
        assert_eq!(stats.array_equality_axioms_added, 0, "stats={stats:?}");
    }

    #[test]
    fn array_disequality_projects_a_diff_witness() {
        let mut arena = TermArena::new();
        let left = arena.array_var("dynamic_diff_left", 4, 8).unwrap();
        let right = arena.array_var("dynamic_diff_right", 4, 8).unwrap();
        let equal = arena.eq(left, right).unwrap();
        let different = arena.not(equal).unwrap();

        let (result, stats) = dynamic_array_solve_stats(&mut arena, &[different]);
        let CheckResult::Sat(model) = result else {
            panic!("expected replayed SAT, stats={stats:?}");
        };
        assert_eq!(
            eval(&arena, different, &model.to_assignment()),
            Ok(Value::Bool(true))
        );
        assert!(stats.rounds <= 2, "stats={stats:?}");
        assert!(stats.array_equality_axioms_added <= 1, "stats={stats:?}");
    }

    #[test]
    fn store_equality_combines_extensionality_with_row() {
        let mut arena = TermArena::new();
        let array = arena.array_var("dynamic_store_eq_array", 4, 8).unwrap();
        let index = arena.bv_var("dynamic_store_eq_index", 4).unwrap();
        let value = arena.bv_var("dynamic_store_eq_value", 8).unwrap();
        let stored = arena.store(array, index, value).unwrap();
        let arrays_equal = arena.eq(stored, array).unwrap();
        let base_read = arena.select(array, index).unwrap();
        let read_equals_value = arena.eq(base_read, value).unwrap();
        let read_differs = arena.not(read_equals_value).unwrap();

        let (result, stats) = dynamic_array_solve_stats(&mut arena, &[arrays_equal, read_differs]);
        assert_eq!(result, CheckResult::Unsat);
        assert!(stats.rounds <= 3, "stats={stats:?}");
        assert!(stats.array_equality_axioms_added >= 1, "stats={stats:?}");
        assert!(stats.row_axioms_added >= 1, "stats={stats:?}");
    }

    #[test]
    fn parent_select_hook_shares_uf_bearing_indices() {
        let mut arena = TermArena::new();
        let left = arena.array_var("dynamic_eq_uf_left", 4, 8).unwrap();
        let right = arena.array_var("dynamic_eq_uf_right", 4, 8).unwrap();
        let function = arena
            .declare_fun("dynamic_eq_index_f", &[Sort::BitVec(4)], Sort::BitVec(4))
            .unwrap();
        let x = arena.bv_var("dynamic_eq_uf_x", 4).unwrap();
        let y = arena.bv_var("dynamic_eq_uf_y", 4).unwrap();
        let fx = arena.apply(function, &[x]).unwrap();
        let fy = arena.apply(function, &[y]).unwrap();
        let same_arguments = arena.eq(x, y).unwrap();
        let arrays_equal = arena.eq(left, right).unwrap();
        let left_read = arena.select(left, fx).unwrap();
        let right_read = arena.select(right, fy).unwrap();
        let reads_equal = arena.eq(left_read, right_read).unwrap();
        let reads_differ = arena.not(reads_equal).unwrap();
        let indices_strict = arena.bv_ult(fx, fy).unwrap();
        let impossible_choice = arena.or(indices_strict, reads_differ).unwrap();

        let (result, stats) = dynamic_array_solve_stats(
            &mut arena,
            &[same_arguments, arrays_equal, impossible_choice],
        );
        assert_eq!(result, CheckResult::Unsat);
        assert!(stats.rounds <= 5, "stats={stats:?}");
        assert!(stats.function_pairs_added >= 1, "stats={stats:?}");
        assert!(stats.parent_select_pairs_added >= 1, "stats={stats:?}");
        assert_eq!(stats.array_equality_axioms_added, 0, "stats={stats:?}");
    }

    #[test]
    fn row_store_hit_materializes_one_axiom() {
        let mut arena = TermArena::new();
        let array = arena.array_var("dynamic_row_hit_array", 4, 8).unwrap();
        let index = arena.bv_var("dynamic_row_hit_index", 4).unwrap();
        let value = arena.bv_var("dynamic_row_hit_value", 8).unwrap();
        let stored = arena.store(array, index, value).unwrap();
        let read = arena.select(stored, index).unwrap();
        let same = arena.eq(read, value).unwrap();
        let different = arena.not(same).unwrap();

        let (result, stats) = dynamic_array_solve_stats(&mut arena, &[different]);
        assert_eq!(result, CheckResult::Unsat);
        assert_eq!(stats.rounds, 2, "stats={stats:?}");
        assert_eq!(stats.sat_candidates, 1, "stats={stats:?}");
        assert_eq!(stats.row_axioms_added, 1, "stats={stats:?}");
        assert_eq!(stats.array_pairs_added, 0, "stats={stats:?}");
    }

    #[test]
    fn row_store_miss_materializes_one_axiom() {
        let mut arena = TermArena::new();
        let array = arena.array_var("dynamic_row_miss_array", 4, 8).unwrap();
        let stored_index = arena.bv_var("dynamic_row_stored_index", 4).unwrap();
        let read_index = arena.bv_var("dynamic_row_read_index", 4).unwrap();
        let value = arena.bv_var("dynamic_row_miss_value", 8).unwrap();
        let stored = arena.store(array, stored_index, value).unwrap();
        let stored_read = arena.select(stored, read_index).unwrap();
        let base_read = arena.select(array, read_index).unwrap();
        let same_index = arena.eq(stored_index, read_index).unwrap();
        let different_index = arena.not(same_index).unwrap();
        let same_read = arena.eq(stored_read, base_read).unwrap();
        let different_read = arena.not(same_read).unwrap();

        let (result, stats) =
            dynamic_array_solve_stats(&mut arena, &[different_index, different_read]);
        assert_eq!(result, CheckResult::Unsat);
        assert_eq!(stats.rounds, 2, "stats={stats:?}");
        assert_eq!(stats.row_axioms_added, 1, "stats={stats:?}");
    }

    #[test]
    fn row_axiom_shares_uf_bearing_indices_with_euf() {
        let mut arena = TermArena::new();
        let array = arena.array_var("dynamic_row_uf_array", 4, 8).unwrap();
        let function = arena
            .declare_fun("dynamic_row_index_f", &[Sort::BitVec(4)], Sort::BitVec(4))
            .unwrap();
        let x = arena.bv_var("dynamic_row_uf_x", 4).unwrap();
        let y = arena.bv_var("dynamic_row_uf_y", 4).unwrap();
        let value = arena.bv_var("dynamic_row_uf_value", 8).unwrap();
        let fx = arena.apply(function, &[x]).unwrap();
        let fy = arena.apply(function, &[y]).unwrap();
        let stored = arena.store(array, fx, value).unwrap();
        let read = arena.select(stored, fy).unwrap();
        let same_arg = arena.eq(x, y).unwrap();
        let same_value = arena.eq(read, value).unwrap();
        let different_value = arena.not(same_value).unwrap();

        let (result, stats) = dynamic_array_solve_stats(&mut arena, &[same_arg, different_value]);
        assert_eq!(result, CheckResult::Unsat);
        assert!(stats.row_axioms_added >= 1, "stats={stats:?}");
        assert!(stats.rounds <= 3, "stats={stats:?}");
    }

    #[test]
    fn concrete_miss_store_chain_replays_without_row_axioms() {
        let mut arena = TermArena::new();
        let array = arena.array_var("dynamic_row_chain_array", 8, 8).unwrap();
        let key = arena.bv_var("dynamic_row_chain_key", 8).unwrap();
        let base_read = arena.select(array, key).unwrap();
        let mut memory = array;
        let mut assertions = Vec::new();
        for ordinal in 0..24 {
            let index = arena.bv_const(8, ordinal).unwrap();
            let value = arena.bv_const(8, ordinal + 1).unwrap();
            memory = arena.store(memory, index, value).unwrap();
            let same = arena.eq(key, index).unwrap();
            assertions.push(arena.not(same).unwrap());
        }
        let read = arena.select(memory, key).unwrap();
        assertions.push(arena.eq(read, base_read).unwrap());

        let (result, stats) = dynamic_array_solve_stats(&mut arena, &assertions);
        assert!(matches!(result, CheckResult::Sat(_)), "stats={stats:?}");
        assert_eq!(stats.rounds, 1, "stats={stats:?}");
        assert_eq!(stats.row_axioms_added, 0, "stats={stats:?}");
        assert_eq!(stats.array_pairs_added, 0, "stats={stats:?}");
    }

    #[test]
    fn symbolic_array_table_replays_without_quadratic_interfaces() {
        let mut arena = TermArena::new();
        let array = arena.array_var("dynamic_symbolic_table", 8, 8).unwrap();
        let mut assertions = Vec::new();
        for ordinal in 0..24 {
            let index = arena
                .bv_var(&format!("dynamic_table_index_{ordinal}"), 8)
                .unwrap();
            let read = arena.select(array, index).unwrap();
            assertions.push(arena.eq(read, index).unwrap());
        }

        let (result, stats) = dynamic_array_solve_stats(&mut arena, &assertions);
        let CheckResult::Sat(model) = result else {
            panic!("expected replayed SAT, stats={stats:?}");
        };
        let assignment = model.to_assignment();
        assert!(
            assertions
                .iter()
                .all(|&term| eval(&arena, term, &assignment) == Ok(Value::Bool(true)))
        );
        assert_eq!(stats.rounds, 1, "stats={stats:?}");
        assert_eq!(stats.array_pairs_added, 0, "stats={stats:?}");
        assert_eq!(stats.max_interface_atoms, 0, "stats={stats:?}");
    }

    #[test]
    fn projected_array_model_uses_majority_else_value() {
        let mut arena = TermArena::new();
        let array = arena.array_var("dynamic_majority_model", 8, 8).unwrap();
        let TermNode::Symbol(array_symbol) = arena.node(array) else {
            panic!("array variable must be a symbol");
        };
        let array_symbol = *array_symbol;
        let mut assertions = Vec::new();
        for index in 0..16u128 {
            let index_term = arena.bv_const(8, index).unwrap();
            let expected = if index < 12 { 7 } else { index - 9 };
            let expected_term = arena.bv_const(8, expected).unwrap();
            let read = arena.select(array, index_term).unwrap();
            assertions.push(arena.eq(read, expected_term).unwrap());
        }

        let (result, stats) = dynamic_array_solve_stats(&mut arena, &assertions);
        let CheckResult::Sat(model) = result else {
            panic!("expected replayed SAT, stats={stats:?}");
        };
        let Value::Array(array_value) = model.get(array_symbol).unwrap() else {
            panic!("expected a projected BV array value");
        };
        assert_eq!(array_value.default_element(), 7);
        assert_eq!(array_value.entries().count(), 4);
        assert_eq!(stats.rounds, 1, "stats={stats:?}");
        let assignment = model.to_assignment();
        assert!(
            assertions
                .iter()
                .all(|&assertion| eval(&arena, assertion, &assignment) == Ok(Value::Bool(true)))
        );
    }

    #[test]
    fn forced_array_aliases_stop_at_the_interface_cap() {
        let mut arena = TermArena::new();
        let array = arena.array_var("dynamic_forced_array", 8, 8).unwrap();
        let zero = arena.bv_const(8, 0).unwrap();
        let mut assertions = Vec::new();
        for ordinal in 0..24 {
            let index = arena
                .bv_var(&format!("dynamic_forced_index_{ordinal}"), 8)
                .unwrap();
            let value = arena.bv_const(8, ordinal).unwrap();
            let read = arena.select(array, index).unwrap();
            assertions.push(arena.eq(index, zero).unwrap());
            assertions.push(arena.eq(read, value).unwrap());
        }

        let (result, stats) = dynamic_array_solve_stats(&mut arena, &assertions);
        assert!(
            matches!(
                result,
                CheckResult::Unknown(crate::UnknownReason {
                    kind: crate::UnknownKind::ResourceLimit,
                    ..
                })
            ),
            "result={result:?}, stats={stats:?}"
        );
        assert_eq!(stats.rounds, 1, "stats={stats:?}");
        assert_eq!(stats.sat_candidates, 1, "stats={stats:?}");
        assert_eq!(stats.array_pairs_added, 256, "stats={stats:?}");
        assert_eq!(stats.function_pairs_added, 0, "stats={stats:?}");
    }

    #[test]
    fn public_array_entry_projects_and_replays_a_sat_model() {
        let mut arena = TermArena::new();
        let array = arena.array_var("public_dynamic_array", 4, 8).unwrap();
        let zero_index = arena.bv_const(4, 0).unwrap();
        let one_index = arena.bv_const(4, 1).unwrap();
        let zero_value = arena.bv_const(8, 0x2a).unwrap();
        let one_value = arena.bv_const(8, 0x7c).unwrap();
        let read_zero = arena.select(array, zero_index).unwrap();
        let read_one = arena.select(array, one_index).unwrap();
        let assertions = [
            arena.eq(read_zero, zero_value).unwrap(),
            arena.eq(read_one, one_value).unwrap(),
        ];

        let result =
            check_qf_aufbv_online_cdclt(&mut arena, &assertions, &SolverConfig::default()).unwrap();
        let CheckResult::Sat(model) = result else {
            panic!("expected SAT, got {result:?}");
        };
        let assignment = model.to_assignment();
        assert!(
            assertions
                .iter()
                .all(|&term| eval(&arena, term, &assignment) == Ok(Value::Bool(true)))
        );
    }

    fn two_scalar_values(arena: &mut TermArena, sort: Sort) -> (TermId, TermId) {
        match sort {
            Sort::Bool => (arena.bool_const(false), arena.bool_const(true)),
            Sort::BitVec(width) => (
                arena.bv_const(width, 0).unwrap(),
                arena.bv_const(width, 1).unwrap(),
            ),
            other => panic!("finite scalar test does not admit {other:?}"),
        }
    }

    #[test]
    fn bool_and_bv_array_component_matrix_projects_replayable_models() {
        for (ordinal, (index_sort, element_sort)) in [
            (Sort::Bool, Sort::Bool),
            (Sort::Bool, Sort::BitVec(3)),
            (Sort::BitVec(3), Sort::Bool),
            (Sort::BitVec(3), Sort::BitVec(3)),
        ]
        .into_iter()
        .enumerate()
        {
            let mut arena = TermArena::new();
            let array = arena
                .array_var_with_sorts(
                    &format!("finite_scalar_array_{ordinal}"),
                    index_sort,
                    element_sort,
                )
                .unwrap();
            let (first_index, second_index) = two_scalar_values(&mut arena, index_sort);
            let (first_value, second_value) = two_scalar_values(&mut arena, element_sort);
            let first_read = arena.select(array, first_index).unwrap();
            let second_read = arena.select(array, second_index).unwrap();
            let assertions = [
                arena.eq(first_read, first_value).unwrap(),
                arena.eq(second_read, second_value).unwrap(),
            ];

            let result =
                check_qf_aufbv_online_cdclt(&mut arena, &assertions, &SolverConfig::default())
                    .unwrap();
            let CheckResult::Sat(model) = result else {
                panic!("expected SAT for {index_sort:?}->{element_sort:?}, got {result:?}");
            };
            let assignment = model.to_assignment();
            assert!(
                assertions
                    .iter()
                    .all(|&term| eval(&arena, term, &assignment) == Ok(Value::Bool(true))),
                "model did not replay for {index_sort:?}->{element_sort:?}: {model:?}"
            );
            let TermNode::Symbol(symbol) = arena.node(array) else {
                panic!("array variable must remain a symbol")
            };
            if (index_sort, element_sort) != (Sort::BitVec(3), Sort::BitVec(3)) {
                assert!(
                    matches!(model.get(*symbol), Some(Value::GenericArray(_))),
                    "mixed array should use the generic model representation: {model:?}"
                );
            }
        }
    }

    #[test]
    fn public_bool_array_issue5925_decides_unsat() {
        let mut script = parse_script(include_str!(
            "../../../corpus/public-curated/non-incremental/QF_ABV/cvc5-regress-clean/cli__regress0__arrays__issue5925.smt2"
        ))
        .expect("issue5925 parses");

        let result = check_qf_aufbv_online_cdclt(
            &mut script.arena,
            &script.assertions,
            &SolverConfig::default(),
        )
        .unwrap();

        assert_eq!(result, CheckResult::Unsat);
    }

    #[test]
    fn non_finite_scalar_array_components_remain_outside_admission() {
        let mut arena = TermArena::new();
        let array = arena
            .array_var_with_sorts("int_array", Sort::Int, Sort::Bool)
            .unwrap();
        let index = arena.int_var("int_array_index").unwrap();
        let read = arena.select(array, index).unwrap();

        let result = check_qf_aufbv_online_cdclt(&mut arena, &[read], &SolverConfig::default());

        assert!(matches!(result, Err(crate::SolverError::Unsupported(_))));
    }

    #[test]
    fn projected_sat_model_replays_original_applications() {
        let mut arena = TermArena::new();
        let f = arena
            .declare_fun("f", &[Sort::BitVec(4)], Sort::BitVec(4))
            .unwrap();
        let x = arena.bv_var("x", 4).unwrap();
        let y = arena.bv_var("y", 4).unwrap();
        let fx = arena.apply(f, &[x]).unwrap();
        let fy = arena.apply(f, &[y]).unwrap();
        let x_ne_y_eq = arena.eq(x, y).unwrap();
        let x_ne_y = arena.not(x_ne_y_eq).unwrap();
        let one = arena.bv_const(4, 1).unwrap();
        let two = arena.bv_const(4, 2).unwrap();
        let fx_one = arena.eq(fx, one).unwrap();
        let fy_two = arena.eq(fy, two).unwrap();
        let assertions = [x_ne_y, fx_one, fy_two];

        let CheckResult::Sat(model) =
            check_qf_ufbv_online_cdclt(&mut arena, &assertions, &SolverConfig::default()).unwrap()
        else {
            panic!("expected replaying online UFBV model");
        };
        let assignment = model.to_assignment();
        assert!(assertions.iter().all(|&assertion| {
            matches!(eval(&arena, assertion, &assignment), Ok(Value::Bool(true)))
        }));
    }

    #[test]
    fn zero_timeout_is_first_class_unknown() {
        let mut arena = TermArena::new();
        let f = arena
            .declare_fun("f", &[Sort::BitVec(4)], Sort::BitVec(4))
            .unwrap();
        let x = arena.bv_var("x", 4).unwrap();
        let fx = arena.apply(f, &[x]).unwrap();
        let assertion = arena.eq(fx, x).unwrap();
        let result = check_qf_ufbv_online_cdclt(
            &mut arena,
            &[assertion],
            &SolverConfig::default().with_timeout(Duration::ZERO),
        )
        .unwrap();
        assert!(matches!(
            result,
            CheckResult::Unknown(crate::UnknownReason {
                kind: crate::UnknownKind::Timeout,
                ..
            })
        ));
    }

    #[test]
    fn statically_distinct_ground_table_bypasses_quadratic_interface_cap() {
        let mut arena = TermArena::new();
        let f = arena
            .declare_fun("f", &[Sort::BitVec(8)], Sort::BitVec(8))
            .unwrap();
        let mut assertions = Vec::new();
        for value in 0..24 {
            let argument = arena.bv_const(8, value).unwrap();
            let application = arena.apply(f, &[argument]).unwrap();
            assertions.push(arena.eq(application, argument).unwrap());
        }

        let stats = raw_solve_stats(&mut arena, &assertions);
        assert_eq!(stats.outcome, Outcome::Sat);
        assert_eq!(stats.interface_atoms, 0, "stats={stats:?}");

        let CheckResult::Sat(model) =
            check_qf_ufbv_online_cdclt(&mut arena, &assertions, &SolverConfig::default()).unwrap()
        else {
            panic!("expected the concrete-key table to pass the relevant-interface cap");
        };
        let assignment = model.to_assignment();
        assert!(assertions.iter().all(|&assertion| {
            matches!(eval(&arena, assertion, &assignment), Ok(Value::Bool(true)))
        }));
    }

    #[test]
    fn unconstrained_symbolic_table_avoids_quadratic_interface_cap() {
        let mut arena = TermArena::new();
        let f = arena
            .declare_fun("dynamic_f", &[Sort::BitVec(8)], Sort::BitVec(8))
            .unwrap();
        let mut assertions = Vec::new();
        for index in 0..24 {
            let argument = arena.bv_var(&format!("dynamic_x_{index}"), 8).unwrap();
            let application = arena.apply(f, &[argument]).unwrap();
            assertions.push(arena.eq(application, argument).unwrap());
        }

        let (result, stats) = dynamic_solve_stats(&mut arena, &assertions);
        let CheckResult::Sat(model) = result else {
            panic!("expected the consistent symbolic table to replay, stats={stats:?}");
        };
        assert_eq!(stats.rounds, 1, "stats={stats:?}");
        assert_eq!(stats.pairs_added, 0, "stats={stats:?}");
        assert_eq!(stats.max_interface_atoms, 0, "stats={stats:?}");
        let assignment = model.to_assignment();
        assert!(assertions.iter().all(|&assertion| {
            matches!(eval(&arena, assertion, &assignment), Ok(Value::Bool(true)))
        }));
    }

    #[test]
    fn forced_symbolic_violations_respect_materialized_interface_cap() {
        let mut arena = TermArena::new();
        let f = arena
            .declare_fun("forced_dynamic_f", &[Sort::BitVec(8)], Sort::BitVec(8))
            .unwrap();
        let zero = arena.bv_const(8, 0).unwrap();
        let mut assertions = Vec::new();
        for index in 0..24 {
            let argument = arena
                .bv_var(&format!("forced_dynamic_x_{index}"), 8)
                .unwrap();
            let application = arena.apply(f, &[argument]).unwrap();
            let output = arena.bv_const(8, index).unwrap();
            assertions.push(arena.bv_ule(argument, zero).unwrap());
            assertions.push(arena.eq(application, output).unwrap());
        }

        let (result, stats) = dynamic_solve_stats(&mut arena, &assertions);
        assert!(
            matches!(
                result,
                CheckResult::Unknown(crate::UnknownReason {
                    kind: crate::UnknownKind::ResourceLimit,
                    ..
                })
            ),
            "stats={stats:?}"
        );
        assert_eq!(stats.rounds, 1, "stats={stats:?}");
        assert_eq!(stats.sat_candidates, 1, "stats={stats:?}");
        assert_eq!(stats.pairs_added, 256, "stats={stats:?}");
    }
}
