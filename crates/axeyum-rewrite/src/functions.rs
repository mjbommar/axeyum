//! Eager elimination of uninterpreted functions (`QF_UFBV`) to `QF_BV`
//! by Ackermann reduction (ADR-0013).
//!
//! Each distinct application `f(a_1, .., a_n)` over an uninterpreted function
//! `f` becomes a fresh scalar symbol, and for every pair of applications of the
//! same `f` a **congruence** constraint is added:
//!
//! ```text
//! (a_1 = b_1 AND .. AND a_n = b_n) -> f(a) = f(b)
//! ```
//!
//! relating the two fresh symbols. The result is pure `QF_BV`, decided by the
//! existing bit-blasting pipeline. A satisfying model is projected back to
//! function interpretations ([`FuncValue`]) by
//! [`FunctionElimination::project_model`], which replays exactly as for scalars
//! and arrays.
//!
//! This is the same eager strategy as array elimination
//! ([`crate::eliminate_arrays`]); the two passes compose to reduce `QF_AUFBV`
//! to `QF_BV` (eliminate arrays first, then functions).

use std::collections::HashMap;

use axeyum_ir::{
    Assignment, FuncId, FuncValue, IrError, Op, Sort, SymbolId, TermArena, TermId, TermNode, Value,
    eval,
};

use crate::canonical::build_app;

/// A canonical default value for an arithmetic result sort (`Int 0` / `Real 0`),
/// used as the unconstrained default of a projected arithmetic-sorted function
/// interpretation. Panics for a non-arithmetic sort (the arithmetic projection
/// path only calls it for `Int`/`Real`).
fn default_value_of(sort: Sort) -> Value {
    match sort {
        Sort::Int => Value::Int(0),
        Sort::Real => Value::Real(axeyum_ir::Rational::zero()),
        other => panic!("default_value_of called on non-arithmetic sort {other:?}"),
    }
}

/// Error from uninterpreted-function elimination.
#[derive(Debug, Clone)]
pub enum FuncElimError {
    /// A construct outside the supported `QF_UFBV` fragment.
    Unsupported(String),
    /// An IR builder error while constructing replacement terms.
    Ir(IrError),
}

impl core::fmt::Display for FuncElimError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            FuncElimError::Unsupported(what) => write!(f, "unsupported function construct: {what}"),
            FuncElimError::Ir(error) => write!(f, "function elimination IR error: {error}"),
        }
    }
}

impl core::error::Error for FuncElimError {}

impl From<IrError> for FuncElimError {
    fn from(error: IrError) -> Self {
        FuncElimError::Ir(error)
    }
}

/// Applications of one function as `(rewritten args, fresh symbol)` pairs, in
/// discovery order — the per-function group used for congruence pairing.
type ApplyGroup = Vec<(Vec<TermId>, SymbolId)>;

/// One eliminated application of an uninterpreted function, retained so a
/// `QF_BV` model can be projected back to a function interpretation.
#[derive(Debug, Clone)]
struct ProjectedApply {
    func: FuncId,
    /// The rewritten (pure-`QF_BV`) argument terms.
    args: Vec<TermId>,
    fresh: SymbolId,
}

/// Result of eliminating uninterpreted functions from a set of assertions.
#[derive(Debug, Clone)]
pub struct FunctionElimination {
    assertions: Vec<TermId>,
    abstraction: Vec<TermId>,
    applies: Vec<ProjectedApply>,
    had_functions: bool,
}

impl FunctionElimination {
    /// The pure-`QF_BV` assertions: rewritten originals plus congruence
    /// constraints.
    pub fn assertions(&self) -> &[TermId] {
        &self.assertions
    }

    /// The rewritten-only assertions WITHOUT the appended congruence
    /// constraints: each uninterpreted application is abstracted as a fresh
    /// scalar variable, but no functional-consistency lemmas are present. This
    /// is the relaxation a lazy/on-demand Ackermann procedure ([`crate`]
    /// consumers in `axeyum-solver`) starts from, adding congruence lemmas only
    /// for the application pairs a candidate model violates.
    pub fn abstraction(&self) -> &[TermId] {
        &self.abstraction
    }

    /// The eliminated applications as `(func, rewritten args, fresh symbol)`
    /// triples, in discovery order (deterministic). Used to build on-demand
    /// congruence lemmas: a pair `(i, j)` of entries for the same `func`
    /// (matching arity) whose argument tuples are equal under a candidate model
    /// but whose fresh symbols differ is a functional-consistency violation.
    pub fn applications(&self) -> Vec<(FuncId, &[TermId], SymbolId)> {
        self.applies
            .iter()
            .map(|apply| (apply.func, apply.args.as_slice(), apply.fresh))
            .collect()
    }

    /// Whether the input actually contained any uninterpreted-function
    /// applications.
    pub fn had_functions(&self) -> bool {
        self.had_functions
    }

    /// Projects a `QF_BV` model of the eliminated assertions back to a model
    /// over the original query, reconstructing each function's interpretation
    /// from its eliminated applications.
    ///
    /// # Errors
    ///
    /// Returns [`IrError`] if an argument term fails to evaluate under `model`.
    ///
    /// # Panics
    ///
    /// Panics if `model` is not a complete model of the eliminated assertions
    /// (a fresh application symbol is unassigned), which cannot happen for a
    /// model returned by a backend that solved those assertions.
    pub fn project_model(
        &self,
        arena: &TermArena,
        model: &Assignment,
    ) -> Result<Assignment, IrError> {
        let mut projected = model.clone();
        // Per function, the (argument-value tuple, result-value) entries, kept in
        // the application discovery order so the projection is deterministic.
        let mut tables: HashMap<FuncId, Vec<(Vec<Value>, Value)>> = HashMap::new();
        // The discovery order of distinct `FuncId`s, so we build interpretations
        // (and thus the arithmetic entry order) deterministically.
        let mut func_order: Vec<FuncId> = Vec::new();
        for apply in &self.applies {
            let mut key = Vec::with_capacity(apply.args.len());
            for &arg in &apply.args {
                key.push(eval(arena, arg, model)?);
            }
            let result = model
                .get(apply.fresh)
                .expect("fresh application symbol is assigned");
            if !tables.contains_key(&apply.func) {
                func_order.push(apply.func);
            }
            tables.entry(apply.func).or_default().push((key, result));
        }
        for func in func_order {
            let entries = tables.remove(&func).expect("func recorded in order");
            let (_, params, result) = arena.function(func);
            let arith = matches!(result, Sort::Int | Sort::Real)
                || params.iter().any(|s| matches!(s, Sort::Int | Sort::Real));
            let mut value = if arith {
                // Default result is any value of the result sort; the original
                // query only constrains the explicitly recorded applications.
                let default = default_value_of(result);
                FuncValue::constant_value(params.to_vec(), result, default)
            } else {
                FuncValue::constant(params.to_vec(), result, 0)
            };
            for (args, element) in entries {
                value = if arith {
                    value.define_value(&args, element)
                } else {
                    let key: Vec<u128> = args.iter().map(Value::scalar_code).collect();
                    value.define(&key, element.scalar_code())
                };
            }
            projected.set_function(func, value);
        }
        Ok(projected)
    }
}

/// Eliminates all uninterpreted-function applications from `assertions`,
/// returning equisatisfiable pure-`QF_BV` assertions plus model-projection
/// metadata.
///
/// If no assertion contains an application, the assertions are returned
/// unchanged.
///
/// # Errors
///
/// Returns [`FuncElimError`] for constructs outside the supported `QF_UFBV`
/// fragment, or for an internal IR builder error.
pub fn eliminate_functions(
    arena: &mut TermArena,
    assertions: &[TermId],
) -> Result<FunctionElimination, FuncElimError> {
    let had_functions = assertions.iter().any(|&term| contains_apply(arena, term));
    if !had_functions {
        return Ok(FunctionElimination {
            assertions: assertions.to_vec(),
            abstraction: assertions.to_vec(),
            applies: Vec::new(),
            had_functions: false,
        });
    }

    let mut ctx = Eliminator::default();
    let mut rewritten = Vec::with_capacity(assertions.len());
    for &assertion in assertions {
        rewritten.push(ctx.rewrite(arena, assertion)?);
    }
    // The abstraction is the rewritten-only assertions, before the eager
    // congruence lemmas are appended.
    let abstraction = rewritten.clone();
    rewritten.extend(ctx.congruence_constraints(arena)?);

    Ok(FunctionElimination {
        assertions: rewritten,
        abstraction,
        applies: ctx.applies,
        had_functions: true,
    })
}

#[derive(Default)]
struct Eliminator {
    /// Rewrite cache for terms.
    term_memo: HashMap<TermId, TermId>,
    /// Cache for `(func, rewritten args) -> fresh symbol`.
    apply_memo: HashMap<(FuncId, Vec<TermId>), SymbolId>,
    /// Applications per function, in discovery order, for congruence pairing.
    groups: Vec<(FuncId, ApplyGroup)>,
    /// Flat list for model projection.
    applies: Vec<ProjectedApply>,
    fresh_counter: usize,
}

impl Eliminator {
    fn rewrite(&mut self, arena: &mut TermArena, term: TermId) -> Result<TermId, FuncElimError> {
        if let Some(&cached) = self.term_memo.get(&term) {
            return Ok(cached);
        }
        let node = arena.node(term).clone();
        let result = match node {
            TermNode::BoolConst(_)
            | TermNode::BvConst { .. }
            | TermNode::WideBvConst(_)
            | TermNode::IntConst(_)
            | TermNode::RealConst(_)
            | TermNode::Symbol(_) => term,
            TermNode::App {
                op: Op::Apply(func),
                args,
            } => {
                let mut rewritten_args = Vec::with_capacity(args.len());
                for &arg in &args {
                    rewritten_args.push(self.rewrite(arena, arg)?);
                }
                self.resolve_apply(arena, func, rewritten_args)?
            }
            TermNode::App { op, args } => {
                let mut lowered = Vec::with_capacity(args.len());
                for &arg in &args {
                    lowered.push(self.rewrite(arena, arg)?);
                }
                build_app(arena, op, &lowered)?
            }
        };
        self.term_memo.insert(term, result);
        Ok(result)
    }

    /// Resolves `func(args)` (with `args` already rewritten) to a fresh scalar
    /// symbol, recording it for congruence and projection.
    fn resolve_apply(
        &mut self,
        arena: &mut TermArena,
        func: FuncId,
        args: Vec<TermId>,
    ) -> Result<TermId, FuncElimError> {
        if let Some(&fresh) = self.apply_memo.get(&(func, args.clone())) {
            return Ok(arena.var(fresh));
        }
        let result_sort = arena.function(func).2;
        let fresh = self.fresh_symbol(arena, result_sort)?;
        self.record_apply(func, args.clone(), fresh);
        self.apply_memo.insert((func, args), fresh);
        Ok(arena.var(fresh))
    }

    fn fresh_symbol(
        &mut self,
        arena: &mut TermArena,
        sort: Sort,
    ) -> Result<SymbolId, FuncElimError> {
        let name = format!("!fn_app_{}", self.fresh_counter);
        self.fresh_counter += 1;
        Ok(arena.declare(&name, sort)?)
    }

    fn record_apply(&mut self, func: FuncId, args: Vec<TermId>, fresh: SymbolId) {
        self.applies.push(ProjectedApply {
            func,
            args: args.clone(),
            fresh,
        });
        if let Some((_, group)) = self.groups.iter_mut().find(|(g, _)| *g == func) {
            group.push((args, fresh));
        } else {
            self.groups.push((func, vec![(args, fresh)]));
        }
    }

    fn congruence_constraints(&self, arena: &mut TermArena) -> Result<Vec<TermId>, FuncElimError> {
        let mut constraints = Vec::new();
        for (_func, group) in &self.groups {
            for i in 0..group.len() {
                for j in (i + 1)..group.len() {
                    let (args_i, fresh_i) = &group[i];
                    let (args_j, fresh_j) = &group[j];
                    // Conjunction of pairwise argument equalities.
                    let mut same_args: Option<TermId> = None;
                    for (&a, &b) in args_i.iter().zip(args_j) {
                        let eq = arena.eq(a, b)?;
                        same_args = Some(match same_args {
                            Some(acc) => arena.and(acc, eq)?,
                            None => eq,
                        });
                    }
                    let var_i = arena.var(*fresh_i);
                    let var_j = arena.var(*fresh_j);
                    let same_result = arena.eq(var_i, var_j)?;
                    // Zero-arity functions (constants) need no guard: identical
                    // applications already intern to one symbol, so a pair here
                    // means distinct argument tuples — but a 0-ary function has
                    // only one tuple, so `same_args` is always present for n>=1.
                    let constraint = match same_args {
                        Some(guard) => arena.implies(guard, same_result)?,
                        None => same_result,
                    };
                    constraints.push(constraint);
                }
            }
        }
        Ok(constraints)
    }
}

/// Returns `true` if `term` contains any uninterpreted-function application.
fn contains_apply(arena: &TermArena, term: TermId) -> bool {
    let mut seen = std::collections::BTreeSet::new();
    let mut stack = vec![term];
    while let Some(t) = stack.pop() {
        if !seen.insert(t) {
            continue;
        }
        match arena.node(t) {
            TermNode::App { op, args } => {
                if matches!(op, Op::Apply(_)) {
                    return true;
                }
                stack.extend(args.iter().copied());
            }
            TermNode::BoolConst(_)
            | TermNode::BvConst { .. }
            | TermNode::WideBvConst(_)
            | TermNode::IntConst(_)
            | TermNode::RealConst(_)
            | TermNode::Symbol(_) => {}
        }
    }
    false
}

#[cfg(test)]
mod tests {
    use super::{contains_apply, eliminate_functions};
    use axeyum_ir::{Assignment, FuncValue, Sort, TermArena, Value, eval};

    fn bv(width: u32, value: u128) -> Value {
        Value::Bv { width, value }
    }

    #[test]
    fn no_functions_passes_through_unchanged() {
        let mut arena = TermArena::new();
        let x = arena.bv_var("x", 8).unwrap();
        let one = arena.bv_const(8, 1).unwrap();
        let f = arena.eq(x, one).unwrap();
        let elim = eliminate_functions(&mut arena, &[f]).unwrap();
        assert!(!elim.had_functions());
        assert_eq!(elim.assertions(), &[f]);
    }

    #[test]
    fn distinct_applications_generate_one_congruence_constraint() {
        // F: f(x) == f(y) with f : BV3 -> BV3.
        let mut arena = TermArena::new();
        let f = arena
            .declare_fun("f", &[Sort::BitVec(3)], Sort::BitVec(3))
            .unwrap();
        let x_sym = arena.declare("x", Sort::BitVec(3)).unwrap();
        let y_sym = arena.declare("y", Sort::BitVec(3)).unwrap();
        let x = arena.var(x_sym);
        let y = arena.var(y_sym);
        let fx = arena.apply(f, &[x]).unwrap();
        let fy = arena.apply(f, &[y]).unwrap();
        let formula = arena.eq(fx, fy).unwrap();

        let elim = eliminate_functions(&mut arena, &[formula]).unwrap();
        assert!(elim.had_functions());
        // The rewritten formula plus exactly one congruence constraint.
        assert_eq!(elim.assertions().len(), 2);
        for &t in elim.assertions() {
            assert!(
                !contains_apply(&arena, t),
                "no applications remain after elimination"
            );
        }

        // For every interpretation of f and every x, y, the rewritten formula
        // matches the original and the congruence constraint holds.
        let mut interp = FuncValue::constant(vec![Sort::BitVec(3)], Sort::BitVec(3), 0);
        for k in 0..8u128 {
            interp = interp.define(&[k], (k.wrapping_mul(3).wrapping_add(2)) & 0x7);
        }
        for x_val in 0..8u128 {
            for y_val in 0..8u128 {
                let mut model = Assignment::new();
                model.set(x_sym, bv(3, x_val));
                model.set(y_sym, bv(3, y_val));
                model.set_function(f, interp.clone());
                let original = eval(&arena, formula, &model).unwrap();

                let projected = consistent_model(&arena, &elim, &model);
                assert_eq!(
                    eval(&arena, elim.assertions()[0], &projected).unwrap(),
                    original,
                    "x={x_val} y={y_val}"
                );
                assert_eq!(
                    eval(&arena, elim.assertions()[1], &projected).unwrap(),
                    Value::Bool(true),
                    "congruence holds under a consistent model"
                );
            }
        }
    }

    #[test]
    fn binary_function_eliminates_and_projects() {
        // F: f(x, y) == f(y, x) with f : (BV3, BV3) -> BV3 — the rewritten
        // form must agree with the original under any interpretation, and the
        // projected model reconstructs f from its applications.
        let mut arena = TermArena::new();
        let f = arena
            .declare_fun("f", &[Sort::BitVec(3), Sort::BitVec(3)], Sort::BitVec(3))
            .unwrap();
        let x_sym = arena.declare("x", Sort::BitVec(3)).unwrap();
        let y_sym = arena.declare("y", Sort::BitVec(3)).unwrap();
        let x = arena.var(x_sym);
        let y = arena.var(y_sym);
        let fxy = arena.apply(f, &[x, y]).unwrap();
        let fyx = arena.apply(f, &[y, x]).unwrap();
        let formula = arena.eq(fxy, fyx).unwrap();

        let elim = eliminate_functions(&mut arena, &[formula]).unwrap();
        assert!(elim.had_functions());
        for &t in elim.assertions() {
            assert!(!contains_apply(&arena, t));
        }

        let mut interp =
            FuncValue::constant(vec![Sort::BitVec(3), Sort::BitVec(3)], Sort::BitVec(3), 0);
        for a in 0..8u128 {
            for b in 0..8u128 {
                interp = interp.define(&[a, b], (a.wrapping_add(b.wrapping_mul(2))) & 0x7);
            }
        }
        for x_val in 0..8u128 {
            for y_val in 0..8u128 {
                let mut model = Assignment::new();
                model.set(x_sym, bv(3, x_val));
                model.set(y_sym, bv(3, y_val));
                model.set_function(f, interp.clone());
                let original = eval(&arena, formula, &model).unwrap();
                let projected = consistent_model(&arena, &elim, &model);
                assert_eq!(
                    eval(&arena, elim.assertions()[0], &projected).unwrap(),
                    original
                );
                for &c in &elim.assertions()[1..] {
                    assert_eq!(eval(&arena, c, &projected).unwrap(), Value::Bool(true));
                }
            }
        }
    }

    #[test]
    fn project_model_reconstructs_interpretation() {
        // Assigning the fresh application symbols directly, project_model must
        // produce a FuncValue under which the original applications evaluate to
        // the assigned values.
        let mut arena = TermArena::new();
        let f = arena
            .declare_fun("f", &[Sort::BitVec(4)], Sort::BitVec(8))
            .unwrap();
        let a = arena.bv_const(4, 1).unwrap();
        let b = arena.bv_const(4, 2).unwrap();
        let fa = arena.apply(f, &[a]).unwrap();
        let fb = arena.apply(f, &[b]).unwrap();
        let neq = {
            let e = arena.eq(fa, fb).unwrap();
            arena.not(e).unwrap()
        };

        let elim = eliminate_functions(&mut arena, &[neq]).unwrap();
        // Build a QF_BV model: assign each fresh symbol a distinct value.
        let mut bv_model = Assignment::new();
        // Find the fresh symbols by re-deriving them: the eliminated assertion
        // is `(not (= s0 s1))`; set them via the arena's symbol table.
        for (sym, name, sort) in arena.symbols() {
            if name.starts_with("!fn_app_") {
                let Sort::BitVec(w) = sort else { continue };
                // s0 -> 0xaa, s1 -> 0xbb (distinct, satisfying the disequality).
                let value = if name.ends_with('0') { 0xaa } else { 0xbb };
                bv_model.set(sym, bv(w, value));
            }
        }
        let projected = elim.project_model(&arena, &bv_model).unwrap();
        // The reconstructed f makes the original disequality true.
        assert_eq!(eval(&arena, neq, &projected).unwrap(), Value::Bool(true));
        assert_eq!(eval(&arena, fa, &projected).unwrap(), bv(8, 0xaa));
        assert_eq!(eval(&arena, fb, &projected).unwrap(), bv(8, 0xbb));
    }

    /// Extends `model` with each fresh application symbol set to the true value
    /// of the function at the (rewritten) arguments — the consistent assignment.
    fn consistent_model(
        arena: &TermArena,
        elim: &super::FunctionElimination,
        model: &Assignment,
    ) -> Assignment {
        let mut projected = model.clone();
        for apply in &elim.applies {
            let interp = model.function(apply.func).unwrap();
            let key: Vec<u128> = apply
                .args
                .iter()
                .map(|&a| eval(arena, a, model).unwrap().scalar_code())
                .collect();
            let code = interp.apply(&key);
            let result_sort = arena.function(apply.func).2;
            projected.set(apply.fresh, Value::from_scalar_code(result_sort, code));
        }
        projected
    }
}
