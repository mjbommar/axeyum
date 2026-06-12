//! Query objects for Axeyum.
//!
//! A [`Query`] is a cheap, owned value object over terms stored in a
//! [`axeyum_ir::TermArena`]. It gives Phase 3 a first-class place for
//! assertions, assumptions, and scopes before slicing or rewriting can change
//! what a model is required to satisfy.

use axeyum_ir::{Sort, TermArena, TermId};

mod planning;

pub use planning::{
    DropReason, DroppedTerm, PlannedTerm, QueryPlan, QueryReplayFailure, QueryTermRole,
    StructuralCacheKey,
};

/// Stable handle for an assertion inside a [`Query`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct AssertionId(u32);

impl AssertionId {
    /// The dense index of this assertion.
    pub fn index(self) -> usize {
        self.0 as usize
    }
}

/// Stable handle for an assumption inside a [`Query`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct AssumptionId(u32);

impl AssumptionId {
    /// The dense index of this assumption.
    pub fn index(self) -> usize {
        self.0 as usize
    }
}

/// Stable handle for a scope inside a [`Query`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ScopeId(u32);

impl ScopeId {
    /// The dense index of this scope.
    pub fn index(self) -> usize {
        self.0 as usize
    }
}

/// Root query scope. Every query contains this scope.
pub const ROOT_SCOPE: ScopeId = ScopeId(0);

/// A Boolean assertion that must hold in any satisfying model.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Assertion {
    /// The asserted Boolean term.
    pub term: TermId,
    /// Stable scope containing this assertion.
    pub scope: ScopeId,
    /// Optional user-facing label for diagnostics, cores, and evidence.
    pub label: Option<String>,
}

/// A Boolean assumption active for the current one-shot query.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Assumption {
    /// The assumed Boolean term.
    pub term: TermId,
    /// Stable scope containing this assumption.
    pub scope: ScopeId,
    /// Optional user-facing label for failed-assumption and evidence reports.
    pub label: Option<String>,
}

/// A query scope used for provenance and future activation-literal lowering.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Scope {
    /// Parent scope, or `None` for [`ROOT_SCOPE`].
    pub parent: Option<ScopeId>,
    /// Optional user-facing label.
    pub label: Option<String>,
}

/// Owned query value passed between planning, rewriting, and solving layers.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Query {
    scopes: Vec<Scope>,
    assertions: Vec<Assertion>,
    assumptions: Vec<Assumption>,
}

impl Query {
    /// Starts building a query against `arena`.
    pub fn builder(arena: &TermArena) -> QueryBuilder<'_> {
        QueryBuilder::new(arena)
    }

    /// Returns all scopes in stable creation order.
    pub fn scopes(&self) -> &[Scope] {
        &self.scopes
    }

    /// Returns all assertions in stable insertion order.
    pub fn assertions(&self) -> &[Assertion] {
        &self.assertions
    }

    /// Returns all assumptions in stable insertion order.
    pub fn assumptions(&self) -> &[Assumption] {
        &self.assumptions
    }

    /// Iterates over Boolean terms that a one-shot backend must enforce.
    ///
    /// Phase 3 starts assumptions-first, but one-shot backends can soundly
    /// enforce active assumptions by passing them as ordinary assertions.
    pub fn solver_terms(&self) -> impl Iterator<Item = TermId> + '_ {
        self.assertions
            .iter()
            .map(|entry| entry.term)
            .chain(self.assumptions.iter().map(|entry| entry.term))
    }

    /// Number of Boolean terms enforced by [`Query::solver_terms`].
    pub fn solver_term_count(&self) -> usize {
        self.assertions.len() + self.assumptions.len()
    }

    /// Returns `true` when the query has no assertions or assumptions.
    pub fn is_empty(&self) -> bool {
        self.assertions.is_empty() && self.assumptions.is_empty()
    }

    /// Computes a deterministic structural cache key for this query.
    ///
    /// The key hashes term structure, operators, constants, symbol names, and
    /// symbol sorts. It does not depend on arena-local [`TermId`] allocation or
    /// user-facing labels.
    pub fn structural_cache_key(&self, arena: &TermArena) -> StructuralCacheKey {
        planning::structural_cache_key(arena, self.solver_entries())
    }

    /// Builds a plan that submits the full query.
    pub fn plan_full(&self, arena: &TermArena) -> QueryPlan {
        planning::plan_full(arena, self)
    }

    /// Builds a target-support slice of this query.
    ///
    /// Terms whose symbol support intersects `targets` are kept. Ground terms
    /// are kept. Terms with disjoint non-empty support may be dropped from the
    /// submitted solver query, but any `sat` model from the plan must replay
    /// against the original query before it is accepted.
    pub fn slice_for_targets(&self, arena: &TermArena, targets: &[TermId]) -> QueryPlan {
        planning::slice_for_targets(arena, self, targets)
    }

    /// Builds an exact-target slice of this query.
    ///
    /// Only query terms whose term ID appears in `targets` are submitted. This
    /// is more aggressive than [`Query::slice_for_targets`]: it may drop terms
    /// with overlapping symbol support, so callers must replay any `sat` model
    /// against the original query before accepting it.
    pub fn slice_exact_targets(&self, arena: &TermArena, targets: &[TermId]) -> QueryPlan {
        planning::slice_exact_targets(arena, self, targets)
    }

    fn solver_entries(&self) -> impl Iterator<Item = (QueryTermRole, TermId)> + '_ {
        self.assertions
            .iter()
            .enumerate()
            .map(|(i, entry)| {
                (
                    QueryTermRole::Assertion(AssertionId(
                        u32::try_from(i).expect("assertion count fits u32"),
                    )),
                    entry.term,
                )
            })
            .chain(self.assumptions.iter().enumerate().map(|(i, entry)| {
                (
                    QueryTermRole::Assumption(AssumptionId(
                        u32::try_from(i).expect("assumption count fits u32"),
                    )),
                    entry.term,
                )
            }))
    }
}

/// Builder that validates terms against the owning arena.
#[derive(Debug)]
pub struct QueryBuilder<'a> {
    arena: &'a TermArena,
    scopes: Vec<Scope>,
    assertions: Vec<Assertion>,
    assumptions: Vec<Assumption>,
}

impl<'a> QueryBuilder<'a> {
    /// Creates a new builder with only the root scope.
    pub fn new(arena: &'a TermArena) -> Self {
        Self {
            arena,
            scopes: vec![Scope {
                parent: None,
                label: Some("root".to_owned()),
            }],
            assertions: Vec::new(),
            assumptions: Vec::new(),
        }
    }

    /// Creates a child scope and returns its stable ID.
    ///
    /// # Errors
    ///
    /// Returns [`QueryError::UnknownScope`] if `parent` does not belong to this
    /// query.
    ///
    /// # Panics
    ///
    /// Panics on query corruption or pathological scope counts exceeding `u32`.
    pub fn scope(&mut self, parent: ScopeId, label: Option<String>) -> Result<ScopeId, QueryError> {
        self.check_scope(parent)?;
        let id = ScopeId(u32::try_from(self.scopes.len()).expect("scope count fits u32"));
        self.scopes.push(Scope {
            parent: Some(parent),
            label,
        });
        Ok(id)
    }

    /// Adds an assertion in the root scope.
    ///
    /// # Errors
    ///
    /// Returns [`QueryError::NonBooleanAssertion`] if `term` is not Boolean.
    pub fn assert(&mut self, term: TermId) -> Result<AssertionId, QueryError> {
        self.assert_in(ROOT_SCOPE, term, None)
    }

    /// Adds a labeled assertion in `scope`.
    ///
    /// # Errors
    ///
    /// Returns [`QueryError::UnknownScope`] for an invalid scope or
    /// [`QueryError::NonBooleanAssertion`] if `term` is not Boolean.
    ///
    /// # Panics
    ///
    /// Panics on query corruption or pathological assertion counts exceeding
    /// `u32`.
    pub fn assert_in(
        &mut self,
        scope: ScopeId,
        term: TermId,
        label: Option<String>,
    ) -> Result<AssertionId, QueryError> {
        self.check_scope(scope)?;
        self.expect_bool(term, QueryTermKind::Assertion)?;
        let id =
            AssertionId(u32::try_from(self.assertions.len()).expect("assertion count fits u32"));
        self.assertions.push(Assertion { term, scope, label });
        Ok(id)
    }

    /// Adds an assumption in the root scope.
    ///
    /// # Errors
    ///
    /// Returns [`QueryError::NonBooleanAssumption`] if `term` is not Boolean.
    pub fn assume(&mut self, term: TermId) -> Result<AssumptionId, QueryError> {
        self.assume_in(ROOT_SCOPE, term, None)
    }

    /// Adds a labeled assumption in `scope`.
    ///
    /// # Errors
    ///
    /// Returns [`QueryError::UnknownScope`] for an invalid scope or
    /// [`QueryError::NonBooleanAssumption`] if `term` is not Boolean.
    ///
    /// # Panics
    ///
    /// Panics on query corruption or pathological assumption counts exceeding
    /// `u32`.
    pub fn assume_in(
        &mut self,
        scope: ScopeId,
        term: TermId,
        label: Option<String>,
    ) -> Result<AssumptionId, QueryError> {
        self.check_scope(scope)?;
        self.expect_bool(term, QueryTermKind::Assumption)?;
        let id =
            AssumptionId(u32::try_from(self.assumptions.len()).expect("assumption count fits u32"));
        self.assumptions.push(Assumption { term, scope, label });
        Ok(id)
    }

    /// Finishes the builder.
    pub fn build(self) -> Query {
        Query {
            scopes: self.scopes,
            assertions: self.assertions,
            assumptions: self.assumptions,
        }
    }

    fn check_scope(&self, scope: ScopeId) -> Result<(), QueryError> {
        if scope.index() < self.scopes.len() {
            Ok(())
        } else {
            Err(QueryError::UnknownScope(scope))
        }
    }

    fn expect_bool(&self, term: TermId, kind: QueryTermKind) -> Result<(), QueryError> {
        let sort = self.arena.sort_of(term);
        if sort == Sort::Bool {
            Ok(())
        } else {
            match kind {
                QueryTermKind::Assertion => Err(QueryError::NonBooleanAssertion { term, sort }),
                QueryTermKind::Assumption => Err(QueryError::NonBooleanAssumption { term, sort }),
            }
        }
    }
}

#[derive(Debug, Clone, Copy)]
enum QueryTermKind {
    Assertion,
    Assumption,
}

/// Query construction errors.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum QueryError {
    /// An assertion term is not Boolean.
    NonBooleanAssertion {
        /// Offending term.
        term: TermId,
        /// Actual sort.
        sort: Sort,
    },
    /// An assumption term is not Boolean.
    NonBooleanAssumption {
        /// Offending term.
        term: TermId,
        /// Actual sort.
        sort: Sort,
    },
    /// Scope ID does not belong to this query.
    UnknownScope(ScopeId),
}

impl core::fmt::Display for QueryError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            QueryError::NonBooleanAssertion { term, sort } => {
                write!(
                    f,
                    "assertion #{} has sort {sort:?}, expected Bool",
                    term.index()
                )
            }
            QueryError::NonBooleanAssumption { term, sort } => {
                write!(
                    f,
                    "assumption #{} has sort {sort:?}, expected Bool",
                    term.index()
                )
            }
            QueryError::UnknownScope(scope) => write!(f, "unknown scope #{}", scope.index()),
        }
    }
}

impl core::error::Error for QueryError {}

#[cfg(test)]
mod tests {
    use axeyum_ir::{Assignment, Sort, TermArena, Value};

    use super::{DropReason, Query, QueryError, QueryReplayFailure, QueryTermRole, ROOT_SCOPE};

    #[test]
    fn query_preserves_assertion_assumption_and_scope_order() {
        let mut arena = TermArena::new();
        let p = arena.bool_var("p").unwrap();
        let q = arena.bool_var("q").unwrap();
        let r = arena.bool_var("r").unwrap();
        let mut builder = Query::builder(&arena);
        let child = builder
            .scope(ROOT_SCOPE, Some("branch".to_owned()))
            .unwrap();

        assert_eq!(builder.assert(p).unwrap().index(), 0);
        assert_eq!(
            builder
                .assert_in(child, q, Some("branch assertion".to_owned()))
                .unwrap()
                .index(),
            1
        );
        assert_eq!(builder.assume(r).unwrap().index(), 0);

        let query = builder.build();
        assert_eq!(query.scopes().len(), 2);
        assert_eq!(query.assertions()[1].scope, child);
        assert_eq!(query.assumptions()[0].scope, ROOT_SCOPE);
        assert_eq!(
            query.solver_terms().collect::<Vec<_>>(),
            vec![p, q, r],
            "one-shot backends enforce assertions and active assumptions"
        );
    }

    #[test]
    fn query_rejects_non_boolean_terms() {
        let mut arena = TermArena::new();
        let x = arena.bv_var("x", 8).unwrap();
        let mut builder = Query::builder(&arena);

        assert!(matches!(
            builder.assert(x),
            Err(QueryError::NonBooleanAssertion {
                sort: Sort::BitVec(8),
                ..
            })
        ));
        assert!(matches!(
            builder.assume(x),
            Err(QueryError::NonBooleanAssumption {
                sort: Sort::BitVec(8),
                ..
            })
        ));
    }

    #[test]
    fn query_is_send_sync_owned_value() {
        fn assert_send_sync<T: Send + Sync>() {}

        assert_send_sync::<Query>();
    }

    #[test]
    fn structural_cache_key_uses_structure_not_term_ids_or_labels() {
        let mut left = TermArena::new();
        let x = left.bv_var("x", 8).unwrap();
        let one = left.bv_const(8, 1).unwrap();
        let two = left.bv_const(8, 2).unwrap();
        let sum = left.bv_add(x, one).unwrap();
        let formula = left.eq(sum, two).unwrap();
        let mut left_builder = Query::builder(&left);
        left_builder
            .assert_in(ROOT_SCOPE, formula, Some("left label".to_owned()))
            .unwrap();
        let left_query = left_builder.build();

        let mut right = TermArena::new();
        let _padding = right.bv_const(16, 7).unwrap();
        let x = right.bv_var("x", 8).unwrap();
        let two = right.bv_const(8, 2).unwrap();
        let one = right.bv_const(8, 1).unwrap();
        let sum = right.bv_add(x, one).unwrap();
        let formula = right.eq(sum, two).unwrap();
        let mut right_builder = Query::builder(&right);
        right_builder
            .assert_in(ROOT_SCOPE, formula, Some("right label".to_owned()))
            .unwrap();
        let right_query = right_builder.build();

        assert_eq!(
            left_query.structural_cache_key(&left),
            right_query.structural_cache_key(&right)
        );

        let mut changed_role = Query::builder(&right);
        changed_role.assume(formula).unwrap();
        assert_ne!(
            left_query.structural_cache_key(&left),
            changed_role.build().structural_cache_key(&right),
            "assertion and assumption roles are distinct cache inputs"
        );
    }

    #[test]
    fn target_slice_keeps_intersecting_support_and_tracks_dropped_terms() {
        let mut arena = TermArena::new();
        let x = arena.bv_var("x", 8).unwrap();
        let y = arena.bv_var("y", 8).unwrap();
        let zero = arena.bv_const(8, 0).unwrap();
        let one = arena.bv_const(8, 1).unwrap();
        let x_is_zero = arena.eq(x, zero).unwrap();
        let y_is_one = arena.eq(y, one).unwrap();
        let ground_true = arena.eq(one, one).unwrap();
        let mut builder = Query::builder(&arena);
        builder.assert(x_is_zero).unwrap();
        builder.assert(y_is_one).unwrap();
        builder.assume(ground_true).unwrap();
        let query = builder.build();

        let plan = query.slice_for_targets(&arena, &[x]);
        assert!(plan.is_sliced());
        assert_eq!(
            plan.solver_terms().collect::<Vec<_>>(),
            vec![x_is_zero, ground_true],
            "slicing keeps target-support and ground terms"
        );
        assert_eq!(plan.dropped_terms().len(), 1);
        assert_eq!(plan.dropped_terms()[0].term, y_is_one);
        assert_eq!(plan.dropped_terms()[0].reason, DropReason::DisjointSupport);
        assert!(matches!(
            plan.dropped_terms()[0].role,
            QueryTermRole::Assertion(id) if id.index() == 1
        ));
        assert_ne!(plan.original_cache_key(), plan.solver_cache_key());
    }

    #[test]
    fn exact_slice_keeps_only_requested_terms_and_replays_original_query() {
        let mut arena = TermArena::new();
        let x_sym = arena.declare("x", Sort::BitVec(8)).unwrap();
        let y_sym = arena.declare("y", Sort::BitVec(8)).unwrap();
        let x = arena.var(x_sym);
        let y = arena.var(y_sym);
        let zero = arena.bv_const(8, 0).unwrap();
        let one = arena.bv_const(8, 1).unwrap();
        let x_is_zero = arena.eq(x, zero).unwrap();
        let x_is_one = arena.eq(x, one).unwrap();
        let y_is_one = arena.eq(y, one).unwrap();
        let mut builder = Query::builder(&arena);
        builder.assert(x_is_zero).unwrap();
        builder.assert(x_is_one).unwrap();
        builder.assert(y_is_one).unwrap();
        let query = builder.build();

        let plan = query.slice_exact_targets(&arena, &[x_is_zero]);

        assert!(plan.is_sliced());
        assert_eq!(
            plan.solver_terms().collect::<Vec<_>>(),
            vec![x_is_zero],
            "exact slicing does not keep other assertions just because support overlaps"
        );
        assert_eq!(plan.dropped_terms().len(), 2);
        assert_eq!(plan.dropped_terms()[0].term, x_is_one);
        assert_eq!(plan.dropped_terms()[0].reason, DropReason::NotTarget);
        assert_eq!(plan.dropped_terms()[1].term, y_is_one);
        assert_eq!(plan.dropped_terms()[1].reason, DropReason::NotTarget);

        let mut incomplete = Assignment::new();
        incomplete.set(x_sym, Value::Bv { width: 8, value: 0 });
        incomplete.set(y_sym, Value::Bv { width: 8, value: 1 });
        assert!(matches!(
            plan.replay_original(&arena, &incomplete),
            Err(QueryReplayFailure::Unsatisfied {
                role: QueryTermRole::Assertion(id),
                term,
            }) if id.index() == 1 && term == x_is_one
        ));
    }

    #[test]
    fn sliced_plan_replays_original_query_before_accepting_sat() {
        let mut arena = TermArena::new();
        let x_sym = arena.declare("x", Sort::BitVec(8)).unwrap();
        let y_sym = arena.declare("y", Sort::BitVec(8)).unwrap();
        let x = arena.var(x_sym);
        let y = arena.var(y_sym);
        let zero = arena.bv_const(8, 0).unwrap();
        let one = arena.bv_const(8, 1).unwrap();
        let x_is_zero = arena.eq(x, zero).unwrap();
        let y_is_one = arena.eq(y, one).unwrap();
        let mut builder = Query::builder(&arena);
        builder.assert(x_is_zero).unwrap();
        builder.assert(y_is_one).unwrap();
        let query = builder.build();
        let plan = query.slice_for_targets(&arena, &[x]);

        let mut valid = Assignment::new();
        valid.set(x_sym, Value::Bv { width: 8, value: 0 });
        valid.set(y_sym, Value::Bv { width: 8, value: 1 });
        assert!(plan.replay_original(&arena, &valid).is_ok());

        let mut invalid = Assignment::new();
        invalid.set(x_sym, Value::Bv { width: 8, value: 0 });
        invalid.set(y_sym, Value::Bv { width: 8, value: 3 });
        assert!(matches!(
            plan.replay_original(&arena, &invalid),
            Err(QueryReplayFailure::Unsatisfied {
                role: QueryTermRole::Assertion(id),
                term,
            }) if id.index() == 1 && term == y_is_one
        ));
    }
}
