//! `axeyum.ir.query` — the query object, its plan, and the replay contract.
//!
//! `QueryBuilder<'a>` borrows the arena for its whole life and is consumed by
//! `build`, which does not survive contact with `#[pymethods]`. So the whole
//! build runs inside one Rust call: Python hands over `(scope, term, label)`
//! triples and gets a finished [`Query`](axeyum.ir.query.Query) back.

#![allow(
    // PyO3's calling convention hands `PyRef`/`PyRefMut` guards and owned
    // `Vec<Term>` arguments in by value; there is no by-reference form.
    clippy::needless_pass_by_value,
    clippy::trivially_copy_pass_by_ref
)]

use axeyum_query::{
    DropReason, Query, QueryPlan, QueryReplayFailure, QueryTermRole, ROOT_SCOPE, ScopeId,
    StructuralCacheKey,
};
use pyo3::prelude::*;
use pyo3::types::PyModule;

use crate::error::AxeyumError;
use crate::ir::arena::Arena;
use crate::ir::evaluate::PyAssignment;
use crate::ir::types::{Symbol, Term, check_epoch};

/// The structural identity of a query.
///
/// Deterministic and independent of arena-local `TermId` allocation and of
/// labels, which is exactly what makes [`hex`](Self::hex) a safe cache key.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyclass(module = "axeyum._native.ir.query")
)]
#[pyclass(frozen, module = "axeyum", name = "StructuralCacheKey")]
pub struct PyStructuralCacheKey {
    key: StructuralCacheKey,
}

#[cfg_attr(feature = "stub-gen", pyo3_stub_gen::derive::gen_stub_pymethods)]
#[pymethods]
impl PyStructuralCacheKey {
    /// The 64-bit structural digest.
    #[getter]
    fn digest(&self) -> u64 {
        self.key.digest
    }

    /// Number of assertions covered.
    #[getter]
    fn assertions(&self) -> u64 {
        self.key.assertions
    }

    /// Number of assumptions covered.
    #[getter]
    fn assumptions(&self) -> u64 {
        self.key.assumptions
    }

    /// Distinct DAG nodes covered.
    #[getter]
    fn dag_nodes(&self) -> u64 {
        self.key.dag_nodes
    }

    /// Nodes the same formula would have with no sharing.
    #[getter]
    fn tree_nodes(&self) -> u64 {
        self.key.tree_nodes
    }

    /// The whole key as a hex string — a safe, portable cache key.
    fn hex(&self) -> String {
        self.key.hex()
    }

    fn __repr__(&self) -> String {
        format!("StructuralCacheKey({})", self.key.hex())
    }
}

/// The role a term plays in a query, as `(kind, index)`.
///
/// The index is the assertion's or assumption's position in the query, so a
/// dropped term can be traced back to the exact input that supplied it.
fn role_name(role: QueryTermRole) -> (&'static str, usize) {
    match role {
        QueryTermRole::Assertion(id) => ("assertion", id.index()),
        QueryTermRole::Assumption(id) => ("assumption", id.index()),
    }
}

/// Why the planner dropped a term.
fn drop_name(reason: DropReason) -> &'static str {
    match reason {
        DropReason::DisjointSupport => "disjoint-support",
        DropReason::NotTarget => "not-target",
    }
}

/// A planned (possibly sliced) view of a query.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyclass(module = "axeyum._native.ir.query")
)]
#[pyclass(frozen, module = "axeyum", name = "QueryPlan")]
pub struct PyQueryPlan {
    plan: QueryPlan,
    epoch: u64,
}

#[cfg_attr(feature = "stub-gen", pyo3_stub_gen::derive::gen_stub_pymethods)]
#[pymethods]
impl PyQueryPlan {
    /// Whether the planner dropped anything. When this is `True`, a `sat`
    /// answer over the plan is only about the SLICE — call
    /// [`replay_original`](Self::replay_original) before accepting it.
    fn is_sliced(&self) -> bool {
        self.plan.is_sliced()
    }

    /// `(role, role index, term)` for each term the plan keeps.
    #[getter]
    fn planned_terms(&self) -> Vec<(&'static str, usize, Term)> {
        self.plan
            .planned_terms()
            .iter()
            .map(|planned| {
                let (kind, index) = role_name(planned.role);
                (kind, index, Term::new(self.epoch, planned.term))
            })
            .collect()
    }

    /// `(role, role index, term, reason)` for each term the plan dropped.
    #[getter]
    fn dropped_terms(&self) -> Vec<(&'static str, usize, Term, &'static str)> {
        self.plan
            .dropped_terms()
            .iter()
            .map(|dropped| {
                let (kind, index) = role_name(dropped.role);
                (
                    kind,
                    index,
                    Term::new(self.epoch, dropped.term),
                    drop_name(dropped.reason),
                )
            })
            .collect()
    }

    /// The terms a backend would actually receive.
    #[getter]
    fn solver_terms(&self) -> Vec<Term> {
        self.plan
            .solver_terms()
            .map(|term| Term::new(self.epoch, term))
            .collect()
    }

    /// The structural key of the whole original query.
    #[getter]
    fn original_cache_key(&self) -> PyStructuralCacheKey {
        PyStructuralCacheKey {
            key: self.plan.original_cache_key().clone(),
        }
    }

    /// The structural key of the sliced view handed to the backend.
    #[getter]
    fn solver_cache_key(&self) -> PyStructuralCacheKey {
        PyStructuralCacheKey {
            key: self.plan.solver_cache_key().clone(),
        }
    }

    /// The symbols the slice targets.
    #[getter]
    fn target_support(&self) -> Vec<Symbol> {
        self.plan
            .target_support()
            .iter()
            .map(|&symbol| Symbol::new(self.epoch, symbol))
            .collect()
    }

    /// Re-checks every DROPPED term against `assignment`.
    ///
    /// **Mandatory before accepting a `sat` from a sliced plan.** Returns
    /// `None` on success; otherwise a `(kind, role, term)` triple naming the
    /// first failure — `"unsatisfied"`, `"evaluation"` or `"non-boolean"`.
    fn replay_original(
        &self,
        arena: PyRef<'_, Arena>,
        assignment: PyRef<'_, PyAssignment>,
    ) -> PyResult<Option<(String, String, usize, Term)>> {
        check_epoch(self.epoch, arena.epoch, "Arena")?;
        check_epoch(self.epoch, assignment.epoch, "Assignment")?;
        match self
            .plan
            .replay_original(&arena.arena, &assignment.assignment)
        {
            Ok(()) => Ok(None),
            Err(failure) => {
                use QueryReplayFailure as F;
                let (kind, role, term) = match failure {
                    F::Unsatisfied { role, term } => ("unsatisfied", role, term),
                    F::Evaluation { role, term, .. } => ("evaluation", role, term),
                    F::NonBoolean { role, term, .. } => ("non-boolean", role, term),
                };
                let (role_kind, role_index) = role_name(role);
                Ok(Some((
                    kind.to_owned(),
                    role_kind.to_owned(),
                    role_index,
                    Term::new(self.epoch, term),
                )))
            }
        }
    }

    fn __repr__(&self) -> String {
        format!(
            "QueryPlan(planned={}, dropped={}, sliced={})",
            self.plan.planned_terms().len(),
            self.plan.dropped_terms().len(),
            self.plan.is_sliced()
        )
    }
}

/// A scoped query: assertions, assumptions and labels over one arena.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyclass(module = "axeyum._native.ir.query")
)]
#[pyclass(frozen, module = "axeyum", name = "Query")]
pub struct PyQuery {
    query: Query,
    epoch: u64,
}

#[cfg_attr(feature = "stub-gen", pyo3_stub_gen::derive::gen_stub_pymethods)]
#[pymethods]
impl PyQuery {
    /// Builds a query from `(scope, term, label)` triples in one Rust call.
    ///
    /// `scope` is a scope index (`0` is the root scope, and further scopes are
    /// created in order by `scope_parents`); `label` may be `None`.
    /// Assumptions use the same shape and are supplied separately.
    #[new]
    #[pyo3(signature = (arena, assertions, assumptions = Vec::new(), scope_parents = Vec::new()))]
    fn new(
        arena: PyRef<'_, Arena>,
        assertions: Vec<(usize, Term, Option<String>)>,
        assumptions: Vec<(usize, Term, Option<String>)>,
        scope_parents: Vec<(usize, Option<String>)>,
    ) -> PyResult<Self> {
        let epoch = arena.epoch;
        let mut builder = Query::builder(&arena.arena);
        let mut scopes: Vec<ScopeId> = vec![ROOT_SCOPE];
        for (parent, label) in scope_parents {
            let parent = *scopes
                .get(parent)
                .ok_or_else(|| AxeyumError::new_err(format!("unknown scope index {parent}")))?;
            let scope = builder
                .scope(parent, label)
                .map_err(|error| AxeyumError::new_err(error.to_string()))?;
            scopes.push(scope);
        }
        for (scope, term, label) in assertions {
            let term = term.resolve(epoch)?;
            let scope = *scopes
                .get(scope)
                .ok_or_else(|| AxeyumError::new_err(format!("unknown scope index {scope}")))?;
            builder
                .assert_in(scope, term, label)
                .map_err(|error| AxeyumError::new_err(error.to_string()))?;
        }
        for (scope, term, label) in assumptions {
            let term = term.resolve(epoch)?;
            let scope = *scopes
                .get(scope)
                .ok_or_else(|| AxeyumError::new_err(format!("unknown scope index {scope}")))?;
            builder
                .assume_in(scope, term, label)
                .map_err(|error| AxeyumError::new_err(error.to_string()))?;
        }
        Ok(Self {
            query: builder.build(),
            epoch,
        })
    }

    /// Number of terms a backend would receive.
    fn __len__(&self) -> usize {
        self.query.solver_term_count()
    }

    /// Whether the query has no terms at all.
    fn is_empty(&self) -> bool {
        self.query.is_empty()
    }

    /// `(term, scope index, label)` for each assertion.
    #[getter]
    fn assertions(&self) -> Vec<(Term, usize, Option<String>)> {
        self.query
            .assertions()
            .iter()
            .map(|assertion| {
                (
                    Term::new(self.epoch, assertion.term),
                    assertion.scope.index(),
                    assertion.label.clone(),
                )
            })
            .collect()
    }

    /// `(term, scope index, label)` for each assumption.
    #[getter]
    fn assumptions(&self) -> Vec<(Term, usize, Option<String>)> {
        self.query
            .assumptions()
            .iter()
            .map(|assumption| {
                (
                    Term::new(self.epoch, assumption.term),
                    assumption.scope.index(),
                    assumption.label.clone(),
                )
            })
            .collect()
    }

    /// The structural identity of this query.
    fn structural_cache_key(&self, arena: PyRef<'_, Arena>) -> PyResult<PyStructuralCacheKey> {
        check_epoch(self.epoch, arena.epoch, "Arena")?;
        Ok(PyStructuralCacheKey {
            key: self.query.structural_cache_key(&arena.arena),
        })
    }

    /// The unsliced plan (every term kept).
    fn plan_full(&self, arena: PyRef<'_, Arena>) -> PyResult<PyQueryPlan> {
        check_epoch(self.epoch, arena.epoch, "Arena")?;
        Ok(PyQueryPlan {
            plan: self.query.plan_full(&arena.arena),
            epoch: self.epoch,
        })
    }

    /// A plan keeping only what the `targets` structurally depend on.
    fn slice_for_targets(
        &self,
        arena: PyRef<'_, Arena>,
        targets: Vec<Term>,
    ) -> PyResult<PyQueryPlan> {
        check_epoch(self.epoch, arena.epoch, "Arena")?;
        let targets = arena.resolve_terms(&targets)?;
        Ok(PyQueryPlan {
            plan: self.query.slice_for_targets(&arena.arena, &targets),
            epoch: self.epoch,
        })
    }

    fn __repr__(&self) -> String {
        format!(
            "Query(assertions={}, assumptions={}, scopes={})",
            self.query.assertions().len(),
            self.query.assumptions().len(),
            self.query.scopes().len()
        )
    }
}

/// Builds the `ir.query` submodule.
pub(crate) fn register<'py>(parent: &Bound<'py, PyModule>) -> PyResult<Bound<'py, PyModule>> {
    let py = parent.py();
    let module = PyModule::new(py, "axeyum._native.ir.query")?;
    module.add(
        "__doc__",
        "tier R + C -- the query object, its plan, and `replay_original`, which is \
         mandatory before accepting a sat from a sliced plan.",
    )?;
    module.add_class::<PyQuery>()?;
    module.add_class::<PyQueryPlan>()?;
    module.add_class::<PyStructuralCacheKey>()?;
    parent.add("query", &module)?;
    Ok(module)
}
