//! Query planning: structural cache keys and conservative slicing.

use std::collections::{BTreeSet, HashMap};

use axeyum_ir::{
    Assignment, IrError, Op, Sort, SymbolId, TermArena, TermId, TermNode, TermStats, Value, eval,
};

use crate::{AssertionId, AssumptionId, Query};

const FNV_OFFSET: u64 = 0xcbf2_9ce4_8422_2325;
const FNV_PRIME: u64 = 0x0000_0100_0000_01b3;

/// Role and stable source ID for a Boolean term in a [`Query`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum QueryTermRole {
    /// A required assertion.
    Assertion(AssertionId),
    /// An active assumption.
    Assumption(AssumptionId),
}

impl QueryTermRole {
    fn tag(self) -> u64 {
        match self {
            QueryTermRole::Assertion(_) => 1,
            QueryTermRole::Assumption(_) => 2,
        }
    }

    fn index(self) -> usize {
        match self {
            QueryTermRole::Assertion(id) => id.index(),
            QueryTermRole::Assumption(id) => id.index(),
        }
    }
}

/// Deterministic structural key suitable for query-cache lookup.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StructuralCacheKey {
    /// FNV-1a digest over role-tagged term fingerprints.
    pub digest: u64,
    /// Number of assertion terms contributing to the key.
    pub assertions: u64,
    /// Number of assumption terms contributing to the key.
    pub assumptions: u64,
    /// Number of unique DAG nodes reachable from keyed terms.
    pub dag_nodes: u64,
    /// Saturating unfolded tree-node count for keyed terms.
    pub tree_nodes: u64,
}

impl StructuralCacheKey {
    /// Returns the digest as lowercase fixed-width hexadecimal.
    pub fn hex(&self) -> String {
        format!("{:016x}", self.digest)
    }
}

/// One term submitted by a query plan.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PlannedTerm {
    /// Original query role and stable ID.
    pub role: QueryTermRole,
    /// Boolean term submitted to the solver.
    pub term: TermId,
}

/// Why a planner omitted a term from the submitted solver query.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DropReason {
    /// The term has non-empty symbol support disjoint from the target support.
    DisjointSupport,
    /// The term was not one of the exact target terms requested by the plan.
    NotTarget,
}

/// A term not submitted by a query plan.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DroppedTerm {
    /// Original query role and stable ID.
    pub role: QueryTermRole,
    /// Boolean term omitted from the solver query.
    pub term: TermId,
    /// Reason it was omitted.
    pub reason: DropReason,
}

/// A solver-facing query plan plus replay metadata for the original query.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct QueryPlan {
    original_terms: Vec<PlannedTerm>,
    solver_terms: Vec<PlannedTerm>,
    dropped_terms: Vec<DroppedTerm>,
    original_key: StructuralCacheKey,
    solver_key: StructuralCacheKey,
    target_support: Vec<SymbolId>,
}

impl QueryPlan {
    /// Terms submitted to the solver, with original query provenance.
    pub fn planned_terms(&self) -> &[PlannedTerm] {
        &self.solver_terms
    }

    /// Boolean terms submitted to the solver.
    pub fn solver_terms(&self) -> impl Iterator<Item = TermId> + '_ {
        self.solver_terms.iter().map(|entry| entry.term)
    }

    /// Terms omitted by the planner.
    pub fn dropped_terms(&self) -> &[DroppedTerm] {
        &self.dropped_terms
    }

    /// Structural key for the original query.
    pub fn original_cache_key(&self) -> &StructuralCacheKey {
        &self.original_key
    }

    /// Structural key for the solver-submitted query.
    pub fn solver_cache_key(&self) -> &StructuralCacheKey {
        &self.solver_key
    }

    /// Target symbol support used for slicing, in stable symbol order.
    pub fn target_support(&self) -> &[SymbolId] {
        &self.target_support
    }

    /// Returns `true` when the submitted solver query differs from the
    /// original query.
    pub fn is_sliced(&self) -> bool {
        !self.dropped_terms.is_empty()
    }

    /// Replays an assignment against every term in the original query.
    ///
    /// A `sat` answer from a sliced plan is accepted only after this check
    /// succeeds. The current projection is identity: the assignment is checked
    /// directly against original assertions and assumptions.
    ///
    /// # Errors
    ///
    /// Returns [`QueryReplayFailure`] for the first failed original term.
    pub fn replay_original(
        &self,
        arena: &TermArena,
        assignment: &Assignment,
    ) -> Result<(), QueryReplayFailure> {
        for entry in &self.original_terms {
            match eval(arena, entry.term, assignment) {
                Ok(Value::Bool(true)) => {}
                Ok(Value::Bool(false)) => {
                    return Err(QueryReplayFailure::Unsatisfied {
                        role: entry.role,
                        term: entry.term,
                    });
                }
                Ok(value) => {
                    return Err(QueryReplayFailure::NonBoolean {
                        role: entry.role,
                        term: entry.term,
                        value,
                    });
                }
                Err(error) => {
                    return Err(QueryReplayFailure::Evaluation {
                        role: entry.role,
                        term: entry.term,
                        error,
                    });
                }
            }
        }
        Ok(())
    }
}

/// Original-query replay failure for a planned model.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum QueryReplayFailure {
    /// An original Boolean term evaluated to false.
    Unsatisfied {
        /// Original role and ID.
        role: QueryTermRole,
        /// Original term.
        term: TermId,
    },
    /// Evaluation failed, usually due to a missing symbol assignment.
    Evaluation {
        /// Original role and ID.
        role: QueryTermRole,
        /// Original term.
        term: TermId,
        /// Evaluator error.
        error: IrError,
    },
    /// Internal invariant failure: a query term evaluated to a non-Boolean
    /// value.
    NonBoolean {
        /// Original role and ID.
        role: QueryTermRole,
        /// Original term.
        term: TermId,
        /// Non-Boolean value.
        value: Value,
    },
}

impl core::fmt::Display for QueryReplayFailure {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            QueryReplayFailure::Unsatisfied { role, term } => write!(
                f,
                "original {:?} #{} term #{} evaluated to false",
                role_kind(*role),
                role.index(),
                term.index()
            ),
            QueryReplayFailure::Evaluation { role, term, error } => write!(
                f,
                "original {:?} #{} term #{} failed replay: {error}",
                role_kind(*role),
                role.index(),
                term.index()
            ),
            QueryReplayFailure::NonBoolean { role, term, value } => write!(
                f,
                "original {:?} #{} term #{} replayed to non-Boolean {value}",
                role_kind(*role),
                role.index(),
                term.index()
            ),
        }
    }
}

impl core::error::Error for QueryReplayFailure {}

#[derive(Debug, Clone, Copy)]
enum RoleKind {
    Assertion,
    Assumption,
}

fn role_kind(role: QueryTermRole) -> RoleKind {
    match role {
        QueryTermRole::Assertion(_) => RoleKind::Assertion,
        QueryTermRole::Assumption(_) => RoleKind::Assumption,
    }
}

pub(crate) fn plan_full(arena: &TermArena, query: &Query) -> QueryPlan {
    let original_terms = query
        .solver_entries()
        .map(|(role, term)| PlannedTerm { role, term })
        .collect::<Vec<_>>();
    let key = structural_cache_key(
        arena,
        original_terms.iter().map(|entry| (entry.role, entry.term)),
    );

    QueryPlan {
        original_terms: original_terms.clone(),
        solver_terms: original_terms,
        dropped_terms: Vec::new(),
        original_key: key.clone(),
        solver_key: key,
        target_support: Vec::new(),
    }
}

pub(crate) fn slice_for_targets(arena: &TermArena, query: &Query, targets: &[TermId]) -> QueryPlan {
    if targets.is_empty() {
        return plan_full(arena, query);
    }

    let target_support_set = support_for_terms(arena, targets);
    if target_support_set.is_empty() {
        return plan_full(arena, query);
    }

    let mut original_terms = Vec::new();
    let mut solver_terms = Vec::new();
    let mut dropped_terms = Vec::new();

    for (role, term) in query.solver_entries() {
        let planned = PlannedTerm { role, term };
        original_terms.push(planned.clone());

        let support = support_for_terms(arena, &[term]);
        let keep = support.is_empty()
            || support
                .iter()
                .any(|symbol| target_support_set.contains(symbol));

        if keep {
            solver_terms.push(planned);
        } else {
            dropped_terms.push(DroppedTerm {
                role,
                term,
                reason: DropReason::DisjointSupport,
            });
        }
    }

    let original_key = structural_cache_key(
        arena,
        original_terms.iter().map(|entry| (entry.role, entry.term)),
    );
    let solver_key = structural_cache_key(
        arena,
        solver_terms.iter().map(|entry| (entry.role, entry.term)),
    );

    QueryPlan {
        original_terms,
        solver_terms,
        dropped_terms,
        original_key,
        solver_key,
        target_support: target_support_set.into_iter().collect(),
    }
}

pub(crate) fn slice_exact_targets(
    arena: &TermArena,
    query: &Query,
    targets: &[TermId],
) -> QueryPlan {
    if targets.is_empty() {
        return plan_full(arena, query);
    }

    let target_terms = targets.iter().copied().collect::<BTreeSet<_>>();
    let mut original_terms = Vec::new();
    let mut solver_terms = Vec::new();
    let mut dropped_terms = Vec::new();

    for (role, term) in query.solver_entries() {
        let planned = PlannedTerm { role, term };
        original_terms.push(planned.clone());

        if target_terms.contains(&term) {
            solver_terms.push(planned);
        } else {
            dropped_terms.push(DroppedTerm {
                role,
                term,
                reason: DropReason::NotTarget,
            });
        }
    }

    let original_key = structural_cache_key(
        arena,
        original_terms.iter().map(|entry| (entry.role, entry.term)),
    );
    let solver_key = structural_cache_key(
        arena,
        solver_terms.iter().map(|entry| (entry.role, entry.term)),
    );

    QueryPlan {
        original_terms,
        solver_terms,
        dropped_terms,
        original_key,
        solver_key,
        target_support: support_for_terms(arena, targets).into_iter().collect(),
    }
}

pub(crate) fn structural_cache_key(
    arena: &TermArena,
    entries: impl Iterator<Item = (QueryTermRole, TermId)>,
) -> StructuralCacheKey {
    let mut assertion_fingerprints = Vec::new();
    let mut assumption_fingerprints = Vec::new();
    let mut roots = Vec::new();

    for (role, term) in entries {
        roots.push(term);
        let fingerprint = term_fingerprint(arena, term);
        match role {
            QueryTermRole::Assertion(_) => assertion_fingerprints.push(fingerprint),
            QueryTermRole::Assumption(_) => assumption_fingerprints.push(fingerprint),
        }
    }

    assertion_fingerprints.sort_unstable();
    assumption_fingerprints.sort_unstable();

    let mut digest = FNV_OFFSET;
    update_u64(&mut digest, 0x4158_4559_554d_514b);
    update_u64(&mut digest, usize_to_u64(assertion_fingerprints.len()));
    for fingerprint in &assertion_fingerprints {
        update_u64(&mut digest, QueryTermRole::Assertion(AssertionId(0)).tag());
        update_u64(&mut digest, *fingerprint);
    }
    update_u64(&mut digest, usize_to_u64(assumption_fingerprints.len()));
    for fingerprint in &assumption_fingerprints {
        update_u64(
            &mut digest,
            QueryTermRole::Assumption(AssumptionId(0)).tag(),
        );
        update_u64(&mut digest, *fingerprint);
    }

    let shape = TermStats::compute(arena, &roots);
    StructuralCacheKey {
        digest,
        assertions: usize_to_u64(assertion_fingerprints.len()),
        assumptions: usize_to_u64(assumption_fingerprints.len()),
        dag_nodes: shape.dag_nodes,
        tree_nodes: shape.tree_nodes,
    }
}

fn term_fingerprint(arena: &TermArena, root: TermId) -> u64 {
    let mut memo = HashMap::new();
    let mut stack = vec![(root, false)];

    while let Some((term, children_ready)) = stack.pop() {
        if memo.contains_key(&term) {
            continue;
        }
        match arena.node(term) {
            TermNode::BoolConst(value) => {
                let mut hash = FNV_OFFSET;
                update_u64(&mut hash, 1);
                update_u64(&mut hash, u64::from(*value));
                memo.insert(term, hash);
            }
            TermNode::BvConst { width, value } => {
                let mut hash = FNV_OFFSET;
                update_u64(&mut hash, 2);
                update_u64(&mut hash, u64::from(*width));
                update_u128(&mut hash, *value);
                memo.insert(term, hash);
            }
            TermNode::IntConst(value) => {
                let mut hash = FNV_OFFSET;
                update_u64(&mut hash, 5);
                update_bytes(&mut hash, &value.to_le_bytes());
                memo.insert(term, hash);
            }
            TermNode::RealConst(value) => {
                let mut hash = FNV_OFFSET;
                update_u64(&mut hash, 6);
                update_bytes(&mut hash, &value.numerator().to_le_bytes());
                update_bytes(&mut hash, &value.denominator().to_le_bytes());
                memo.insert(term, hash);
            }
            TermNode::Symbol(symbol) => {
                let (name, sort) = arena.symbol(*symbol);
                let mut hash = FNV_OFFSET;
                update_u64(&mut hash, 3);
                update_sort(&mut hash, sort);
                update_bytes(&mut hash, name.as_bytes());
                memo.insert(term, hash);
            }
            TermNode::App { op, args } if children_ready => {
                let mut hash = FNV_OFFSET;
                update_u64(&mut hash, 4);
                update_sort(&mut hash, arena.sort_of(term));
                update_op(&mut hash, *op);
                update_u64(&mut hash, usize_to_u64(args.len()));
                for arg in args {
                    update_u64(&mut hash, memo[arg]);
                }
                memo.insert(term, hash);
            }
            TermNode::App { args, .. } => {
                stack.push((term, true));
                for &arg in args.iter().rev() {
                    stack.push((arg, false));
                }
            }
        }
    }

    memo[&root]
}

fn support_for_terms(arena: &TermArena, roots: &[TermId]) -> BTreeSet<SymbolId> {
    let mut support = BTreeSet::new();
    let mut seen = BTreeSet::new();
    let mut stack = roots.to_vec();

    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        match arena.node(term) {
            TermNode::Symbol(symbol) => {
                support.insert(*symbol);
            }
            TermNode::App { args, .. } => {
                for &arg in args {
                    stack.push(arg);
                }
            }
            TermNode::BoolConst(_)
            | TermNode::BvConst { .. }
            | TermNode::IntConst(_)
            | TermNode::RealConst(_) => {}
        }
    }

    support
}

fn update_sort(hash: &mut u64, sort: Sort) {
    match sort {
        Sort::Bool => update_u64(hash, 1),
        Sort::BitVec(width) => {
            update_u64(hash, 2);
            update_u64(hash, u64::from(width));
        }
        Sort::Array { index, element } => {
            update_u64(hash, 3);
            update_u64(hash, u64::from(index));
            update_u64(hash, u64::from(element));
        }
        Sort::Int => update_u64(hash, 4),
        Sort::Real => update_u64(hash, 5),
        Sort::Datatype(id) => {
            update_u64(hash, 6);
            update_u64(hash, u64::try_from(id.index()).unwrap_or(u64::MAX));
        }
    }
}

#[allow(clippy::too_many_lines)]
fn update_op(hash: &mut u64, op: Op) {
    match op {
        Op::BoolNot => update_u64(hash, 1),
        Op::BoolAnd => update_u64(hash, 2),
        Op::BoolOr => update_u64(hash, 3),
        Op::BoolXor => update_u64(hash, 4),
        Op::BoolImplies => update_u64(hash, 5),
        Op::BvNot => update_u64(hash, 6),
        Op::BvAnd => update_u64(hash, 7),
        Op::BvOr => update_u64(hash, 8),
        Op::BvXor => update_u64(hash, 9),
        Op::BvNand => update_u64(hash, 10),
        Op::BvNor => update_u64(hash, 11),
        Op::BvXnor => update_u64(hash, 12),
        Op::BvNeg => update_u64(hash, 13),
        Op::BvAdd => update_u64(hash, 14),
        Op::BvSub => update_u64(hash, 15),
        Op::BvMul => update_u64(hash, 16),
        Op::BvUdiv => update_u64(hash, 17),
        Op::BvUrem => update_u64(hash, 18),
        Op::BvSdiv => update_u64(hash, 19),
        Op::BvSrem => update_u64(hash, 20),
        Op::BvSmod => update_u64(hash, 21),
        Op::BvShl => update_u64(hash, 22),
        Op::BvLshr => update_u64(hash, 23),
        Op::BvAshr => update_u64(hash, 24),
        Op::BvUlt => update_u64(hash, 25),
        Op::BvUle => update_u64(hash, 26),
        Op::BvUgt => update_u64(hash, 27),
        Op::BvUge => update_u64(hash, 28),
        Op::BvSlt => update_u64(hash, 29),
        Op::BvSle => update_u64(hash, 30),
        Op::BvSgt => update_u64(hash, 31),
        Op::BvSge => update_u64(hash, 32),
        Op::Eq => update_u64(hash, 33),
        Op::Ite => update_u64(hash, 34),
        Op::BvComp => update_u64(hash, 35),
        Op::Extract { hi, lo } => {
            update_u64(hash, 36);
            update_u64(hash, u64::from(hi));
            update_u64(hash, u64::from(lo));
        }
        Op::Concat => update_u64(hash, 37),
        Op::ZeroExt { by } => {
            update_u64(hash, 38);
            update_u64(hash, u64::from(by));
        }
        Op::SignExt { by } => {
            update_u64(hash, 39);
            update_u64(hash, u64::from(by));
        }
        Op::RotateLeft { by } => {
            update_u64(hash, 40);
            update_u64(hash, u64::from(by));
        }
        Op::RotateRight { by } => {
            update_u64(hash, 41);
            update_u64(hash, u64::from(by));
        }
        Op::Select => update_u64(hash, 42),
        Op::Store => update_u64(hash, 43),
        Op::ConstArray { index } => {
            update_u64(hash, 69);
            update_u64(hash, u64::from(index));
        }
        Op::Bv2Nat => update_u64(hash, 70),
        Op::Int2Bv { width } => {
            update_u64(hash, 71);
            update_u64(hash, u64::from(width));
        }
        Op::Apply(func) => {
            update_u64(hash, 44);
            update_u64(hash, u64::try_from(func.index()).unwrap_or(u64::MAX));
        }
        Op::IntNeg => update_u64(hash, 45),
        Op::IntAdd => update_u64(hash, 46),
        Op::IntSub => update_u64(hash, 47),
        Op::IntMul => update_u64(hash, 48),
        Op::IntDiv => update_u64(hash, 66),
        Op::IntMod => update_u64(hash, 67),
        Op::IntAbs => update_u64(hash, 68),
        Op::IntLt => update_u64(hash, 49),
        Op::IntLe => update_u64(hash, 50),
        Op::IntGt => update_u64(hash, 51),
        Op::IntGe => update_u64(hash, 52),
        Op::RealNeg => update_u64(hash, 53),
        Op::RealAdd => update_u64(hash, 54),
        Op::RealSub => update_u64(hash, 55),
        Op::RealMul => update_u64(hash, 56),
        Op::RealLt => update_u64(hash, 57),
        Op::RealLe => update_u64(hash, 58),
        Op::RealGt => update_u64(hash, 59),
        Op::RealGe => update_u64(hash, 60),
        Op::Forall(var) => {
            update_u64(hash, 61);
            update_u64(hash, u64::try_from(var.index()).unwrap_or(u64::MAX));
        }
        Op::Exists(var) => {
            update_u64(hash, 62);
            update_u64(hash, u64::try_from(var.index()).unwrap_or(u64::MAX));
        }
        Op::DtConstruct { constructor, .. } => {
            update_u64(hash, 63);
            update_u64(hash, u64::try_from(constructor.index()).unwrap_or(u64::MAX));
        }
        Op::DtSelect { constructor, index } => {
            update_u64(hash, 64);
            update_u64(hash, u64::try_from(constructor.index()).unwrap_or(u64::MAX));
            update_u64(hash, u64::from(index));
        }
        Op::DtTest(constructor) => {
            update_u64(hash, 65);
            update_u64(hash, u64::try_from(constructor.index()).unwrap_or(u64::MAX));
        }
    }
}

fn update_u128(hash: &mut u64, value: u128) {
    update_bytes(hash, &value.to_le_bytes());
}

fn update_u64(hash: &mut u64, value: u64) {
    update_bytes(hash, &value.to_le_bytes());
}

fn update_bytes(hash: &mut u64, bytes: &[u8]) {
    for b in bytes {
        *hash ^= u64::from(*b);
        *hash = hash.wrapping_mul(FNV_PRIME);
    }
}

fn usize_to_u64(n: usize) -> u64 {
    u64::try_from(n).unwrap_or(u64::MAX)
}
