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

use std::collections::{BTreeMap, BTreeSet, HashMap};

use axeyum_ir::{
    Assignment, FuncId, FuncValue, IrError, Op, Sort, SortId, SymbolId, TermArena, TermId,
    TermNode, Value, eval, well_founded_default,
};

use crate::canonical::build_app;

/// A canonical default value for a full-value-storage function result sort.
fn default_value_of(arena: &TermArena, sort: Sort) -> Result<Value, IrError> {
    well_founded_default(arena, sort).ok_or(IrError::Unsupported(
        "uninterpreted-function model projection: uninhabited result sort",
    ))
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

/// Result of abstracting uninterpreted-function applications without adding
/// Ackermann congruence constraints.
///
/// Each application is replaced by the same fresh scalar symbol used by
/// [`eliminate_functions`], but [`Self::assertions`] contains only the rewritten
/// originals. It is therefore a **relaxation**, not an equisatisfiable reduction:
/// an `unsat` result transfers to the original query, while a `sat` candidate must
/// first be made functionally consistent and projected/replayed through
/// [`Self::project_model`]. This is the construction boundary for lazy EUF and
/// online theory-combination procedures that generate congruence facts on demand
/// instead of paying the eager quadratic expansion.
#[derive(Debug, Clone)]
pub struct FunctionAbstraction {
    projection: FunctionElimination,
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
        let mut used_uninterpreted_tokens = used_uninterpreted_tokens(arena, &projected);
        for (symbol, name, sort) in arena.symbols() {
            if projected.get(symbol).is_some() || name.starts_with("!fn_app_") {
                continue;
            }
            if let Some(default) =
                projection_default_value(arena, sort, &mut used_uninterpreted_tokens)
            {
                projected.set(symbol, default);
            }
        }
        // Per function, the (argument-value tuple, result-value) entries, kept in
        // the application discovery order so the projection is deterministic.
        let mut tables: HashMap<FuncId, Vec<(Vec<Value>, Value)>> = HashMap::new();
        // The discovery order of distinct `FuncId`s, so we build interpretations
        // (and thus the arithmetic entry order) deterministically.
        let mut func_order: Vec<FuncId> = Vec::new();
        for apply in &self.applies {
            let mut key = Vec::with_capacity(apply.args.len());
            for &arg in &apply.args {
                key.push(eval(arena, arg, &projected)?);
            }
            // A fresh application symbol may be unassigned in the model — notably a
            // NESTED arithmetic-sorted application (e.g. `g(f(c), …)` where the inner
            // result feeds an outer one), whose value is not pinned in the base
            // model. Decline gracefully (the caller maps a projection `Err` to a
            // sound `Unknown`) rather than panic — `unknown` is first-class, and the
            // "never crash" invariant is total.
            let result = model.get(apply.fresh).ok_or(IrError::Unsupported(
                "uninterpreted-function model projection: a fresh application symbol \
                 (e.g. a nested arithmetic-sorted application) is unassigned",
            ))?;
            if !tables.contains_key(&apply.func) {
                func_order.push(apply.func);
            }
            tables.entry(apply.func).or_default().push((key, result));
        }
        for func in func_order {
            let entries = tables.remove(&func).expect("func recorded in order");
            let (_, params, result) = arena.function(func);
            let value_storage = FuncValue::uses_value_storage_for(params, result);
            let mut value = if value_storage {
                // Default result is any value of the result sort; the original
                // query only constrains the explicitly recorded applications.
                let default = default_value_of(arena, result)?;
                FuncValue::constant_value(params.to_vec(), result, default)
            } else {
                FuncValue::constant(params.to_vec(), result, 0)
            };
            for (args, element) in entries {
                value = if value_storage {
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

impl FunctionAbstraction {
    /// The rewritten original assertions with each application replaced by a
    /// fresh scalar symbol and no congruence constraints appended.
    pub fn assertions(&self) -> &[TermId] {
        &self.projection.assertions
    }

    /// The abstracted applications as `(func, rewritten args, fresh symbol)`
    /// triples in deterministic discovery order.
    pub fn applications(&self) -> Vec<(FuncId, &[TermId], SymbolId)> {
        self.projection.applications()
    }

    /// Whether the input actually contained any uninterpreted-function
    /// applications.
    pub fn had_functions(&self) -> bool {
        self.projection.had_functions()
    }

    /// Projects a functionally-consistent model of the abstraction back to an
    /// assignment over the original uninterpreted functions.
    ///
    /// This performs the same deterministic projection as
    /// [`FunctionElimination::project_model`]. The caller must establish
    /// functional consistency first; final replay remains the acceptance gate.
    ///
    /// # Errors
    ///
    /// Returns [`IrError`] if an argument or fresh application value cannot be
    /// reconstructed from `model`.
    pub fn project_model(
        &self,
        arena: &TermArena,
        model: &Assignment,
    ) -> Result<Assignment, IrError> {
        self.projection.project_model(arena, model)
    }
}

fn used_uninterpreted_tokens(
    arena: &TermArena,
    assignment: &Assignment,
) -> BTreeMap<SortId, BTreeSet<u128>> {
    let mut used: BTreeMap<SortId, BTreeSet<u128>> = BTreeMap::new();
    for (symbol, _name, sort) in arena.symbols() {
        let Sort::Uninterpreted(sort_id) = sort else {
            continue;
        };
        if let Some(Value::Uninterpreted { value, .. }) = assignment.get(symbol) {
            used.entry(sort_id).or_default().insert(value);
        }
    }
    used
}

fn projection_default_value(
    arena: &TermArena,
    sort: Sort,
    used_uninterpreted_tokens: &mut BTreeMap<SortId, BTreeSet<u128>>,
) -> Option<Value> {
    if let Sort::Uninterpreted(sort_id) = sort {
        let used = used_uninterpreted_tokens.entry(sort_id).or_default();
        let mut token = 0u128;
        while used.contains(&token) {
            token = token.checked_add(1)?;
        }
        used.insert(token);
        return Some(Value::Uninterpreted {
            sort: sort_id,
            value: token,
        });
    }
    well_founded_default(arena, sort)
}

/// Abstracts uninterpreted-function applications to fresh scalar symbols without
/// constructing eager Ackermann congruence constraints.
///
/// The returned formula is a relaxation. It is intended for lazy procedures that
/// add only demanded congruence facts or explicitly case-split interface
/// equalities. Callers may transfer `unsat` directly, but may return `sat` only
/// after establishing functional consistency and replaying the projected model.
/// Unlike [`eliminate_functions`], this construction never materializes the
/// quadratic application-pair constraint set.
///
/// # Errors
///
/// Returns [`FuncElimError`] for constructs outside the supported scalar UF
/// fragment or for an IR builder error.
pub fn abstract_functions(
    arena: &mut TermArena,
    assertions: &[TermId],
) -> Result<FunctionAbstraction, FuncElimError> {
    let had_functions = assertions.iter().any(|&term| contains_apply(arena, term));
    if !had_functions {
        return Ok(FunctionAbstraction {
            projection: FunctionElimination {
                assertions: assertions.to_vec(),
                abstraction: assertions.to_vec(),
                applies: Vec::new(),
                had_functions: false,
            },
        });
    }

    let mut ctx = Eliminator::default();
    let mut rewritten = Vec::with_capacity(assertions.len());
    for &assertion in assertions {
        rewritten.push(ctx.rewrite(arena, assertion)?);
    }
    Ok(FunctionAbstraction {
        projection: FunctionElimination {
            assertions: rewritten.clone(),
            abstraction: rewritten,
            applies: ctx.applies,
            had_functions: true,
        },
    })
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
        Ok(arena.declare_internal(&name, sort)?)
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
    use super::{abstract_functions, contains_apply, eliminate_functions};
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
    fn abstraction_skips_congruence_and_preserves_projection() {
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

        let abstraction = abstract_functions(&mut arena, &[formula]).unwrap();
        assert!(abstraction.had_functions());
        assert_eq!(abstraction.assertions().len(), 1);
        assert!(!contains_apply(&arena, abstraction.assertions()[0]));
        let applications = abstraction.applications();
        assert_eq!(applications.len(), 2);

        let mut candidate = Assignment::new();
        candidate.set(x_sym, bv(3, 1));
        candidate.set(y_sym, bv(3, 2));
        candidate.set(applications[0].2, bv(3, 5));
        candidate.set(applications[1].2, bv(3, 6));
        let abstract_value = eval(&arena, abstraction.assertions()[0], &candidate).unwrap();
        let projected = abstraction.project_model(&arena, &candidate).unwrap();
        assert_eq!(eval(&arena, formula, &projected).unwrap(), abstract_value);

        let eager = eliminate_functions(&mut arena, &[formula]).unwrap();
        assert_eq!(eager.assertions().len(), 2);
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

    #[test]
    fn project_model_completes_symbols_needed_by_array_argument_keys() {
        let mut arena = TermArena::new();
        let a = arena
            .array_var_with_sorts("a", Sort::Int, Sort::Int)
            .unwrap();
        let array_sort = arena.sort_of(a);
        let i = arena.declare("i", Sort::Int).unwrap();
        let f = arena.declare_fun("f", &[array_sort], Sort::Int).unwrap();
        let zero = arena.int_const(0);
        let i_term = arena.var(i);
        let stored = arena.store(a, i_term, zero).unwrap();
        let app = arena.apply(f, &[stored]).unwrap();
        let one = arena.int_const(1);
        let assertion = arena.eq(app, one).unwrap();

        let elim = eliminate_functions(&mut arena, &[assertion]).unwrap();
        let (_, _, fresh) = elim.applications()[0];
        let mut model = Assignment::new();
        model.set(fresh, Value::Int(1));

        let projected = elim.project_model(&arena, &model).unwrap();
        assert_eq!(
            eval(&arena, assertion, &projected).unwrap(),
            Value::Bool(true)
        );
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
