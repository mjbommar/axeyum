//! `axeyum.cas` — propositional formulas over a bounded variable set (tier R).
//!
//! The whole module is decided by **explicit enumeration**, so it carries one
//! budget and states it: `BOOL_MAX_VARS` (20). Every method that would have to
//! walk `2 ** n` rows returns `None` above it — `truth_table`, `is_tautology`,
//! `is_satisfiable`, `is_contradiction`, `equivalent`, `simplify_qmc`. That
//! `None` is *the budget declined*, and it is deliberately not `False`: a
//! formula this module cannot enumerate is not thereby unsatisfiable. For
//! anything past the budget the SAT front door in `axeyum.smt` is the answer.

use axeyum_cas::BoolExpr as CasBoolExpr;
use pyo3::prelude::*;
use pyo3::types::{PyAny, PyDict, PyModule};
use std::collections::BTreeMap;

/// A propositional formula over `bool` constants and named variables.
///
/// Tier R: owned plain data, immutable once built. `And`, `Or` and `Xor` are
/// variadic; the empty `And` is `True` and the empty `Or`/`Xor` are `False`.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyclass(module = "axeyum._native.cas")
)]
#[pyclass(frozen, from_py_object, module = "axeyum", name = "BoolExpr")]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BoolExpr {
    inner: CasBoolExpr,
}

impl BoolExpr {
    /// Wraps a Rust formula.
    fn wrap(inner: CasBoolExpr) -> Self {
        Self { inner }
    }

    /// Unwraps a list of formulas.
    fn unwrap_vec(operands: &[BoolExpr]) -> Vec<CasBoolExpr> {
        operands
            .iter()
            .map(|operand| operand.inner.clone())
            .collect()
    }
}

#[cfg_attr(feature = "stub-gen", pyo3_stub_gen::derive::gen_stub_pymethods)]
#[pymethods]
impl BoolExpr {
    /// The constant `True` or `False`.
    #[staticmethod]
    fn constant(value: bool) -> BoolExpr {
        BoolExpr::wrap(CasBoolExpr::constant(value))
    }

    /// A named propositional variable.
    #[staticmethod]
    fn var(name: &str) -> BoolExpr {
        BoolExpr::wrap(CasBoolExpr::var(name))
    }

    /// Negation.
    #[staticmethod]
    fn negate(inner: &BoolExpr) -> BoolExpr {
        BoolExpr::wrap(CasBoolExpr::negate(inner.inner.clone()))
    }

    /// Variadic conjunction; the empty conjunction is `True`.
    ///
    /// Exported as `and_` because `and` is a Python keyword: a `#[pyclass]`
    /// method named `and` is registered but unreachable from Python source,
    /// which is surface that exists and cannot be called.
    #[staticmethod]
    #[pyo3(name = "and_")]
    fn and(operands: Vec<BoolExpr>) -> BoolExpr {
        BoolExpr::wrap(CasBoolExpr::and(BoolExpr::unwrap_vec(&operands)))
    }

    /// Variadic disjunction; the empty disjunction is `False`.
    ///
    /// Exported as `or_`; see [`Self::and`] for why.
    #[staticmethod]
    #[pyo3(name = "or_")]
    fn or(operands: Vec<BoolExpr>) -> BoolExpr {
        BoolExpr::wrap(CasBoolExpr::or(BoolExpr::unwrap_vec(&operands)))
    }

    /// Variadic exclusive-or (parity); the empty case is `False`.
    #[staticmethod]
    fn xor(operands: Vec<BoolExpr>) -> BoolExpr {
        BoolExpr::wrap(CasBoolExpr::xor(BoolExpr::unwrap_vec(&operands)))
    }

    /// Material implication `antecedent -> consequent`.
    #[staticmethod]
    fn implies(antecedent: &BoolExpr, consequent: &BoolExpr) -> BoolExpr {
        BoolExpr::wrap(CasBoolExpr::implies(
            antecedent.inner.clone(),
            consequent.inner.clone(),
        ))
    }

    /// Bi-implication `left <-> right`.
    #[staticmethod]
    fn iff(left: &BoolExpr, right: &BoolExpr) -> BoolExpr {
        BoolExpr::wrap(CasBoolExpr::iff(left.inner.clone(), right.inner.clone()))
    }

    /// The number of nodes in the formula.
    fn size(&self) -> usize {
        self.inner.size()
    }

    /// The distinct variable names, sorted.
    #[getter]
    fn variables(&self) -> Vec<String> {
        self.inner.variables()
    }

    /// The truth value under `assignment`, or `None` when a variable is unbound.
    ///
    /// # Errors
    ///
    /// Propagates the per-entry extraction error.
    fn evaluate(&self, assignment: &Bound<'_, PyDict>) -> PyResult<Option<bool>> {
        let mut env: BTreeMap<String, bool> = BTreeMap::new();
        for (key, value) in assignment {
            env.insert(key.extract()?, value.extract()?);
        }
        Ok(self.inner.evaluate(&env))
    }

    /// `[(assignment, value), ...]` over every assignment, or `None` past
    /// `BOOL_MAX_VARS`.
    ///
    /// The assignment is a list of booleans positionally aligned with
    /// `variables`.
    fn truth_table(&self) -> Option<Vec<(Vec<bool>, bool)>> {
        self.inner.truth_table()
    }

    /// Whether the formula is true under every assignment; `None` past the
    /// budget.
    fn is_tautology(&self) -> Option<bool> {
        self.inner.is_tautology()
    }

    /// Whether some assignment satisfies the formula; `None` past the budget.
    ///
    /// A `None` here is **not** `False`: past `BOOL_MAX_VARS` this module
    /// declines to enumerate and claims nothing.
    fn is_satisfiable(&self) -> Option<bool> {
        self.inner.is_satisfiable()
    }

    /// Whether no assignment satisfies the formula; `None` past the budget.
    fn is_contradiction(&self) -> Option<bool> {
        self.inner.is_contradiction()
    }

    /// Whether the two formulas agree on every assignment; `None` past the
    /// budget.
    fn equivalent(&self, other: &BoolExpr) -> Option<bool> {
        self.inner.equivalent(&other.inner)
    }

    /// The disjunctive normal form.
    fn to_dnf(&self) -> BoolExpr {
        BoolExpr::wrap(self.inner.to_dnf())
    }

    /// The conjunctive normal form.
    fn to_cnf(&self) -> BoolExpr {
        BoolExpr::wrap(self.inner.to_cnf())
    }

    /// The Quine-McCluskey minimal form, or `None` past the budget.
    fn simplify_qmc(&self) -> Option<BoolExpr> {
        self.inner.simplify_qmc().map(BoolExpr::wrap)
    }

    fn __eq__(&self, other: &Bound<'_, PyAny>) -> bool {
        // `cast` + `get`, never `extract`: `extract` on a `#[pyclass]` CLONES the
        // whole wrapped value to compare it and then drops it. Structural
        // equality, not logical: use `equivalent` for the semantic question.
        other
            .cast::<BoolExpr>()
            .is_ok_and(|other| other.get().inner == self.inner)
    }

    fn __repr__(&self) -> String {
        format!(
            "BoolExpr(size={}, variables={})",
            self.inner.size(),
            self.inner.variables().len()
        )
    }
}

/// Registers the propositional surface on `module`.
///
/// # Errors
///
/// Propagates any Python error raised while setting the module attributes.
pub(crate) fn register(module: &Bound<'_, PyModule>) -> PyResult<()> {
    module.add_class::<BoolExpr>()?;
    module.add("BOOL_MAX_VARS", axeyum_cas::boolean::MAX_VARS)?;
    #[cfg(feature = "stub-gen")]
    pyo3_stub_gen::module_variable!("axeyum._native.cas", "BOOL_MAX_VARS", usize);
    Ok(())
}
