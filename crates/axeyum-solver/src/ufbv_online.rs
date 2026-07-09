//! Canonical online `QF_UFBV` combination over [`crate::cdclt::CdclT`].
//!
//! Uninterpreted applications are first replaced by fresh scalar symbols through
//! [`axeyum_rewrite::abstract_functions`], with no eager Ackermann constraints.
//! The Boolean structure is Tseitin-encoded once. The first block of Boolean
//! variables denotes every semantic Bool/BV atom plus explicit interface
//! equalities for same-function application arguments and results.
//!
//! A single CDCL(T) trail then drives two theories in lockstep:
//! - [`crate::euf_egraph::EufTheory`] owns congruence over the original terms;
//! - [`crate::IncrementalBvSolver`] owns exact finite-domain Bool/BV semantics over
//!   the function-free abstraction and maps its failed decision-frame selectors
//!   back to a sound active theory-literal core whenever that conjunction is
//!   bit-vector UNSAT.
//!
//! Interface argument equalities are case-split by `CdclT`. Congruent applications
//! make the e-graph propagate their generated result equality, which the BV theory
//! immediately enforces over the fresh result symbols. Conversely, a BV-infeasible
//! interface choice becomes a learned theory clause. This is the first live P1.6
//! equality bus between EUF and BV; eager Ackermann remains the fallback and
//! differential oracle.
//!
//! Soundness:
//! - every BV conflict is a re-solved UNSAT conjunction of the reported active
//!   literals;
//! - every EUF conflict/propagation is an e-graph explanation;
//! - `sat` is accepted only after the abstraction model is projected to
//!   [`axeyum_ir::FuncValue`] interpretations and every original assertion replays;
//! - unsupported/resource-bound states degrade to `Unknown`.

use std::collections::{HashMap, HashSet};
use std::time::Instant;

use axeyum_ir::{FuncId, Op, Sort, TermArena, TermId, TermNode, TermStats};
use axeyum_rewrite::{FuncElimError, FunctionAbstraction, abstract_functions, replace_subterms};

use crate::backend::{CheckResult, SolverConfig, SolverError, UnknownKind, UnknownReason};
use crate::cdclt::{CdclT, Lit as CdcltLit, Outcome};
use crate::euf::project_replay_build;
use crate::euf_egraph::{Encoder, EufTheory, TheoryLit, TheoryProp, TheorySolver};
use crate::incremental::IncrementalBvSolver;
use crate::model::Model;

/// Maximum input DAG admitted before the recursive function abstraction.
const MAX_INPUT_DAG_NODES: u64 = 16_384;
/// Maximum recursive term depth admitted before function abstraction.
const MAX_INPUT_DEPTH: u64 = 4_096;
/// Maximum semantic atoms (formula atoms plus generated interface equalities).
const MAX_THEORY_ATOMS: usize = 1_024;
/// Maximum generated interface equalities before the bounded first slice declines.
const MAX_INTERFACE_ATOMS: usize = 512;
/// Maximum Boolean variables after Tseitin encoding.
const MAX_BOOLEAN_VARIABLES: usize = 8_192;
/// Maximum Boolean clauses after Tseitin encoding.
const MAX_BOOLEAN_CLAUSES: usize = 32_768;

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

enum WalkError {
    Timeout,
    NonBoolean(TermId),
}

enum BuildFailure {
    Unknown(UnknownReason),
    Error(SolverError),
}

type BuildResult<T> = Result<T, BuildFailure>;

struct PreparedAbstraction {
    abstraction: FunctionAbstraction,
    applications: Vec<CombinedApplication>,
    replacements: HashMap<TermId, TermId>,
}

struct TheoryAtoms {
    original: Vec<TermId>,
    abstracted: Vec<TermId>,
}

#[derive(Default)]
struct AtomAccumulator {
    original: Vec<TermId>,
    abstracted: Vec<TermId>,
    abstract_index: HashMap<TermId, usize>,
}

impl AtomAccumulator {
    fn register(
        &mut self,
        arena: &TermArena,
        original: TermId,
        abstracted: TermId,
    ) -> Result<(), SolverError> {
        if arena.sort_of(original) != Sort::Bool || arena.sort_of(abstracted) != Sort::Bool {
            return Err(SolverError::Backend(
                "online UFBV atom abstraction changed Boolean sort".to_owned(),
            ));
        }
        if matches!(arena.node(abstracted), TermNode::BoolConst(_))
            || self.abstract_index.contains_key(&abstracted)
        {
            return Ok(());
        }
        let index = self.abstracted.len();
        self.original.push(original);
        self.abstracted.push(abstracted);
        self.abstract_index.insert(abstracted, index);
        Ok(())
    }

    fn finish(self) -> TheoryAtoms {
        TheoryAtoms {
            original: self.original,
            abstracted: self.abstracted,
        }
    }
}

struct BooleanSkeleton {
    variable_count: usize,
    clauses: Vec<Vec<CdcltLit>>,
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
                Ok(())
            }
            Ok((CheckResult::Unsat, core)) => {
                self.last_model = None;
                self.last_unknown = None;
                Err(self.map_active_core(&core))
            }
            Ok((CheckResult::Unknown(reason), _)) => {
                self.last_model = None;
                self.last_unknown = Some(reason);
                Ok(())
            }
            Err(error) => {
                self.failure = Some(format!("online UFBV warm BV check failed: {error}"));
                self.last_model = None;
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

    fn projected_result(
        &self,
        abstraction: &FunctionAbstraction,
        originals: &[TermId],
    ) -> CheckResult {
        if let Some(detail) = &self.failure {
            return unknown(UnknownKind::Incomplete, detail.clone());
        }
        if let Some(reason) = &self.last_unknown {
            return CheckResult::Unknown(reason.clone());
        }
        let Some(model) = &self.last_model else {
            return unknown(
                UnknownKind::Incomplete,
                "online UFBV reached a total trail without a BV model",
            );
        };
        project_replay_build(self.arena, abstraction, originals, &model.to_assignment())
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
        self.euf.propagate()
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
    match build_and_solve(arena, assertions, config, deadline) {
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
) -> BuildResult<CheckResult> {
    admit_input(arena, assertions, config, deadline)?;
    let prepared = prepare_abstraction(arena, assertions, deadline)?;
    let atoms = build_theory_atoms(arena, assertions, &prepared, deadline)?;
    let skeleton = encode_boolean_skeleton(
        arena,
        prepared.abstraction.assertions(),
        &atoms.abstracted,
        deadline,
    )?;

    let mut negative_atoms = Vec::with_capacity(atoms.abstracted.len());
    for &atom in &atoms.abstracted {
        negative_atoms.push(arena.not(atom)?);
    }
    let atom_count = atoms.original.len();
    let euf = EufTheory::new(arena, &atoms.original);
    let bv = BvTheory::new(arena, atoms.abstracted, negative_atoms, config, deadline);
    let mut theory = CombinedUfbvTheory { euf, bv };
    let mut solver = CdclT::new(
        skeleton.variable_count,
        atom_count,
        skeleton.clauses,
        deadline,
    );
    Ok(match solver.solve(&mut theory) {
        Outcome::Unsat => CheckResult::Unsat,
        Outcome::Unknown => {
            let kind = if deadline.is_some_and(|deadline| Instant::now() >= deadline) {
                UnknownKind::Timeout
            } else {
                UnknownKind::ResourceLimit
            };
            unknown(
                kind,
                "online UFBV canonical CdclT search exhausted its budget",
            )
        }
        Outcome::Sat => theory
            .bv
            .projected_result(&prepared.abstraction, assertions),
    })
}

fn admit_input(
    arena: &TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
    deadline: Option<Instant>,
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
    if !uses_only_bool_and_bv(arena, assertions) {
        return Err(BuildFailure::Error(SolverError::Unsupported(
            "online UFBV combination admits only Bool and BitVec terms".to_owned(),
        )));
    }
    Ok(())
}

fn uses_only_bool_and_bv(arena: &TermArena, assertions: &[TermId]) -> bool {
    let mut seen = HashSet::new();
    let mut stack = assertions.to_vec();
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        if !matches!(arena.sort_of(term), Sort::Bool | Sort::BitVec(_)) {
            return false;
        }
        if let TermNode::App { args, .. } = arena.node(term) {
            stack.extend(args.iter().copied());
        }
    }
    true
}

fn prepare_abstraction(
    arena: &mut TermArena,
    assertions: &[TermId],
    deadline: Option<Instant>,
) -> BuildResult<PreparedAbstraction> {
    let original_applications = match collect_original_applications(arena, assertions, deadline) {
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
    if original_applications.is_empty() {
        return Err(BuildFailure::Error(SolverError::Unsupported(
            "online UFBV combination requires an applied uninterpreted function".to_owned(),
        )));
    }
    let abstraction = abstract_functions(arena, assertions).map_err(map_elim_error)?;
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
    Ok(PreparedAbstraction {
        abstraction,
        applications,
        replacements,
    })
}

fn build_theory_atoms(
    arena: &mut TermArena,
    assertions: &[TermId],
    prepared: &PreparedAbstraction,
    deadline: Option<Instant>,
) -> BuildResult<TheoryAtoms> {
    let mut atoms = AtomAccumulator::default();
    let mut atom_memo = HashMap::new();
    let mut formula_atoms = Vec::new();
    let mut seen_terms = HashSet::new();
    for &assertion in assertions {
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
        atoms.register(arena, atom, rewritten)?;
    }

    let groups = application_groups(&prepared.applications);
    let interface_count = count_interface_atoms(&prepared.applications, &groups);
    if interface_count > MAX_INTERFACE_ATOMS {
        return Err(build_unknown(
            UnknownKind::ResourceLimit,
            format!(
                "online UFBV needs {interface_count} argument/result interface equalities, exceeding the bounded first-slice cap of {MAX_INTERFACE_ATOMS}"
            ),
        ));
    }
    add_interface_atoms(arena, &prepared.applications, groups, deadline, &mut atoms)?;

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
    Ok(atoms.finish())
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

fn count_interface_atoms(
    applications: &[CombinedApplication],
    groups: &[(FuncId, Vec<usize>)],
) -> usize {
    groups.iter().fold(0usize, |total, (_func, members)| {
        let arity = members
            .first()
            .map_or(0, |&index| applications[index].original.args.len());
        let pairs = members
            .len()
            .saturating_mul(members.len().saturating_sub(1))
            / 2;
        total.saturating_add(pairs.saturating_mul(arity.saturating_add(1)))
    })
}

fn add_interface_atoms(
    arena: &mut TermArena,
    applications: &[CombinedApplication],
    groups: Vec<(FuncId, Vec<usize>)>,
    deadline: Option<Instant>,
    atoms: &mut AtomAccumulator,
) -> BuildResult<()> {
    for (_func, members) in groups {
        for left_pos in 0..members.len() {
            for right_pos in (left_pos + 1)..members.len() {
                if deadline.is_some_and(|deadline| Instant::now() >= deadline) {
                    return Err(build_unknown(
                        UnknownKind::Timeout,
                        "online UFBV deadline elapsed while building interface equalities",
                    ));
                }
                let left = &applications[members[left_pos]];
                let right = &applications[members[right_pos]];
                for ((&original_left, &original_right), (&abstract_left, &abstract_right)) in left
                    .original
                    .args
                    .iter()
                    .zip(&right.original.args)
                    .zip(left.rewritten_args.iter().zip(&right.rewritten_args))
                {
                    let original_eq = arena.eq(original_left, original_right)?;
                    let abstract_eq = arena.eq(abstract_left, abstract_right)?;
                    atoms.register(arena, original_eq, abstract_eq)?;
                }
                let original_result = arena.eq(left.original.term, right.original.term)?;
                let left_fresh = arena.var(left.fresh);
                let right_fresh = arena.var(right.fresh);
                let abstract_result = arena.eq(left_fresh, right_fresh)?;
                atoms.register(arena, original_result, abstract_result)?;
            }
        }
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

fn unknown(kind: UnknownKind, detail: impl Into<String>) -> CheckResult {
    CheckResult::Unknown(UnknownReason {
        kind,
        detail: detail.into(),
    })
}

#[cfg(test)]
mod tests {
    use std::time::Duration;

    use axeyum_ir::{Sort, TermArena, Value, eval};

    use super::{BvTheory, check_qf_ufbv_online_cdclt};
    use crate::euf_egraph::TheoryLit;
    use crate::{CheckResult, SolverConfig};

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
        let mut theory = BvTheory::new(&arena, positive, negative, &SolverConfig::default(), None);

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
        let mut theory = BvTheory::new(&arena, positive, negative, &SolverConfig::default(), None);

        theory.push();
        assert!(theory.assert(0, true).is_ok());
        assert_eq!(theory.solver.scope_depth(), 1);
        theory.pop();
        assert_eq!(theory.solver.scope_depth(), 0);
        assert!(theory.assert(1, true).is_ok());
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

        assert_eq!(
            check_qf_ufbv_online_cdclt(&mut arena, &[same_arg, strict], &SolverConfig::default(),)
                .unwrap(),
            CheckResult::Unsat
        );
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
    fn overbound_interface_bus_is_first_class_unknown() {
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

        let result =
            check_qf_ufbv_online_cdclt(&mut arena, &assertions, &SolverConfig::default()).unwrap();
        assert!(matches!(
            result,
            CheckResult::Unknown(crate::UnknownReason {
                kind: crate::UnknownKind::ResourceLimit,
                ..
            })
        ));
    }
}
