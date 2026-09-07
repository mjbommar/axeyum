//! Eager elimination of uninterpreted functions (`QF_UFBV`) to `QF_BV`
//! by Ackermann reduction (ADR-0013).
//!
//! Each distinct application `f(a_1, .., a_n)` over an uninterpreted function
//! `f` becomes a fresh result-sort symbol, and for every pair of applications of the
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

/// Applications of one function as `(rewritten args, fresh result symbol)` pairs, in
/// discovery order — the per-function group used for congruence pairing.
type ApplyGroup = Vec<(Vec<TermId>, SymbolId)>;

/// One eliminated application of an uninterpreted function, retained so a
/// `QF_BV` model can be projected back to a function interpretation.
#[derive(Debug, Clone)]
struct ProjectedApply {
    func: FuncId,
    /// The rewritten argument terms.
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
/// Each application is replaced by the same fresh result-sort symbol used by
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
            // A metadata-only or nested application may not occur in the scalar
            // abstraction. Choosing the result sort's well-founded default is a
            // valid interpretation for that unconstrained point; inserting it into
            // `projected` also lets later, outer application keys evaluate.
            if projected.get(apply.fresh).is_none() {
                let result_sort = arena.symbol(apply.fresh).1;
                let default =
                    projection_default_value(arena, result_sort, &mut used_uninterpreted_tokens)
                        .ok_or(IrError::Unsupported(
                            "uninterpreted-function model projection: application result sort \
                     has no well-founded default",
                        ))?;
                projected.set(apply.fresh, default);
            }
            let result = projected
                .get(apply.fresh)
                .expect("application result was assigned or default-completed");
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
    /// fresh result-sort symbol and no congruence constraints appended.
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

/// Abstracts uninterpreted-function applications to fresh result-sort symbols without
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
/// Returns [`FuncElimError`] for unsupported result sorts or an IR builder error.
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
    if ctx
        .applies
        .iter()
        .any(|apply| matches!(arena.function(apply.func).2, Sort::Array { .. }))
    {
        return Err(FuncElimError::Unsupported(
            "eager Ackermann elimination does not admit array-valued function results; \
             use canonical AUFBV combination"
                .to_owned(),
        ));
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
            | TermNode::WideIntConst(_)
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
                self.resolve_apply(arena, term, func, rewritten_args)?
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

    /// Resolves `func(args)` (with `args` already rewritten) to a fresh
    /// result-sort symbol, recording it for congruence and projection.
    fn resolve_apply(
        &mut self,
        arena: &mut TermArena,
        source: TermId,
        func: FuncId,
        args: Vec<TermId>,
    ) -> Result<TermId, FuncElimError> {
        if let Some(&fresh) = self.apply_memo.get(&(func, args.clone())) {
            return Ok(arena.var(fresh));
        }
        let result_sort = arena.function(func).2;
        let fresh = Self::fresh_symbol(arena, source, result_sort)?;
        self.record_apply(func, args.clone(), fresh);
        self.apply_memo.insert((func, args), fresh);
        Ok(arena.var(fresh))
    }

    fn fresh_symbol(
        arena: &mut TermArena,
        source: TermId,
        sort: Sort,
    ) -> Result<SymbolId, FuncElimError> {
        // The source term id is unique inside one arena and stable across the
        // repeated elimination probes used by auto-dispatch.  Reusing this name
        // for the same application is safe; distinct applications can never
        // alias merely because a new `Eliminator` restarted a local counter.
        let name = format!("!fn_app_{}", source.index());
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
            | TermNode::WideIntConst(_)
            | TermNode::RealConst(_)
            | TermNode::Symbol(_) => {}
        }
    }
    false
}

#[cfg(test)]
mod tests {
    use super::{FuncElimError, abstract_functions, contains_apply, eliminate_functions};
    use axeyum_ir::{
        ArraySortKey, ArrayValue, Assignment, FuncValue, Sort, TermArena, Value, eval,
    };

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
    fn abstraction_projects_array_results_while_eager_elimination_declines() {
        let mut arena = TermArena::new();
        let array_sort = Sort::Array {
            index: ArraySortKey::BitVec(4),
            element: ArraySortKey::BitVec(8),
        };
        let f = arena
            .declare_fun("array_result_f", &[Sort::BitVec(3)], array_sort)
            .unwrap();
        let x = arena.bv_var("array_result_x", 3).unwrap();
        let application = arena.apply(f, &[x]).unwrap();
        let index = arena.bv_const(4, 2).unwrap();
        let value = arena.bv_const(8, 0xaa).unwrap();
        let read = arena.select(application, index).unwrap();
        let formula = arena.eq(read, value).unwrap();

        let abstraction = abstract_functions(&mut arena, &[formula]).unwrap();
        assert_eq!(abstraction.applications().len(), 1);
        assert!(!contains_apply(&arena, abstraction.assertions()[0]));
        let (_, _, fresh) = abstraction.applications()[0];
        assert_eq!(arena.symbol(fresh).1, array_sort);

        let projected_array = Value::Array(ArrayValue::constant(4, 8, 0).store(2, 0xaa));
        let mut candidate = Assignment::new();
        candidate.set(fresh, projected_array);
        let projected = abstraction.project_model(&arena, &candidate).unwrap();
        assert_eq!(eval(&arena, formula, &projected), Ok(Value::Bool(true)));
        assert_eq!(
            projected.function(f).unwrap().result(),
            array_sort,
            "projection must retain the array result sort"
        );

        assert!(matches!(
            eliminate_functions(&mut arena, &[formula]),
            Err(FuncElimError::Unsupported(message))
                if message.contains("array-valued function results")
        ));
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
        // Assign distinct values in deterministic application-discovery order.
        for (index, (_, _, fresh)) in elim.applications().into_iter().enumerate() {
            let Sort::BitVec(width) = arena.symbol(fresh).1 else {
                panic!("test applications have bit-vector results")
            };
            let value = if index == 0 { 0xaa } else { 0xbb };
            bv_model.set(fresh, bv(width, value));
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

    #[test]
    fn repeated_elimination_uses_disjoint_fresh_symbols() {
        let mut arena = TermArena::new();
        let bool_function = arena
            .declare_fun("bool_function", &[Sort::Bool], Sort::Bool)
            .unwrap();
        let int_function = arena
            .declare_fun("int_function", &[Sort::Int], Sort::Int)
            .unwrap();
        let bool_arg = arena.bool_var("bool_arg").unwrap();
        let int_arg = arena.int_var("int_arg").unwrap();
        let bool_app = arena.apply(bool_function, &[bool_arg]).unwrap();
        let int_app = arena.apply(int_function, &[int_arg]).unwrap();

        let first = eliminate_functions(&mut arena, &[bool_app]).unwrap();
        let second = eliminate_functions(&mut arena, &[int_app]).unwrap();
        let repeated = eliminate_functions(&mut arena, &[bool_app]).unwrap();
        let (_, _, first_fresh) = first.applications()[0];
        let (_, _, second_fresh) = second.applications()[0];
        let (_, _, repeated_fresh) = repeated.applications()[0];

        assert_ne!(first_fresh, second_fresh);
        assert_eq!(first_fresh, repeated_fresh);
        assert_eq!(arena.symbol(first_fresh).1, Sort::Bool);
        assert_eq!(arena.symbol(second_fresh).1, Sort::Int);
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

// ---------------------------------------------------------------------------
// The Ackermann-replacement faithfulness witness (ADR-1721 §7, ported).
// ---------------------------------------------------------------------------
//
// `eliminate_functions` does two things and they owe different evidence, in
// exactly the split `eliminate_arrays` has. The **congruence** half only ADDS
// constraints, so it can break `unsat` alone, and
// `AckermannUnsatCertificate::recheck` discharges it by rebuilding the pairwise
// set from an independent implementation of the schema. The **abstraction**
// half -- every application `f(a…)` replaced by a fresh result-sort symbol --
// is a REPLACEMENT, so it can break both directions, and `recheck` only
// re-derives it: it re-runs the same producer on the same input and compares.
// `trust.rs` says what that is worth in its own words -- it "proves
// *determinism* but not *faithfulness*; a stably-wrong circuit … survives
// re-derivation" -- against a real shipped wrong-`unsat`.
//
// This witness is the independent reference, in the shape
// [`crate::witness_read_over_write`] already proved on arrays and
// `crates/axeyum-fp/tests/fpa2bv_faithfulness.rs` before it: it does NOT re-run
// the transform. It interprets both sides under one concrete assignment, with
// each function given a genuine [`FuncValue`] interpretation and each fresh
// application symbol bound to what that interpretation returns at the
// application's evaluated arguments -- the exact model extension the
// abstraction's soundness argument assumes -- and compares the values. The
// original assertion is evaluated by the ground evaluator's `Op::Apply` arm,
// which never goes through this module's rewriting at all.
//
// A disagreement is a hard finding. A sample that cannot be built or evaluated
// is counted as *unavailable*, never silently treated as agreement.

/// Number of sampled assignments [`witness_function_abstraction`] is normally
/// given.
///
/// Sample 0 is the all-zero corner and sample 1 the all-ones corner; the rest
/// are seeded pseudorandom, so the sequence is deterministic (a public API
/// promise) and reproducible across runs and hosts.
///
/// **The two corner samples cannot discriminate on their own**: at sample 0
/// every function returns zero at every key, so an abstraction that confused
/// two applications of the same function would still agree. The pseudorandom
/// samples are what give the witness teeth, which is why the default is more
/// than two.
pub const FUNCTION_ABSTRACTION_WITNESS_SAMPLES: usize = 8;

/// A disagreement between an original assertion and its post-abstraction form
/// under one concrete assignment: the Ackermann abstraction is **not** faithful,
/// so any `unsat` derived through it is unsound.
#[derive(Debug, Clone, PartialEq)]
pub struct FunctionAbstractionDisagreement {
    /// Index of the sampled assignment.
    pub sample: usize,
    /// Index of the assertion, into the caller's `assertions` slice.
    pub assertion: usize,
    /// Value of the original, function-applying assertion.
    pub original: Value,
    /// Value of the rewritten abstraction of that assertion.
    pub abstracted: Value,
}

/// Outcome of the Ackermann-abstraction faithfulness witness.
///
/// `compared` and `unavailable` partition the `(sample, assertion)` pairs the
/// witness attempted, so a caller can report coverage instead of assuming it.
/// `compared == 0` is **not** a pass and [`Self::is_faithful`] does not treat it
/// as one.
#[derive(Debug, Clone, PartialEq)]
pub struct FunctionAbstractionWitness {
    /// `(sample, assertion)` pairs where both sides evaluated and agreed.
    pub compared: usize,
    /// `(sample, assertion)` pairs skipped: a sort the sampler cannot build, an
    /// application whose arguments never resolved, or an evaluator refusal. A
    /// coverage hole, not a pass.
    pub unavailable: usize,
    /// The first disagreement found, if any. Its presence is a soundness alarm.
    pub disagreement: Option<FunctionAbstractionDisagreement>,
    /// `(sample, application)` pairs where an `Op::Apply` subterm of the
    /// ORIGINAL assertions had no entry in the interpretation the abstraction's
    /// own application list built at that sample's argument values.
    ///
    /// **This is the count the value comparison cannot make**, and it exists
    /// because the value comparison was measured to miss the defect it matters
    /// most for. Mutating `eliminate_functions` so that every application of one
    /// function shares one fresh symbol turns the SATISFIABLE
    /// `f(a) = 1 ∧ f(b) = 2` into a wrong `unsat`, and
    /// `AckermannUnsatCertificate::recheck` returned `Ok(true)` over it *with
    /// the value comparison already in place* — because the two sides are
    /// compared as BOOLEANS, and `f(b) = 2` and `f(a) = 2` are both simply
    /// `false` at almost every sample. Agreement on `false` is not agreement.
    ///
    /// A merged or dropped application leaves an original `Op::Apply` with no
    /// entry at its arguments, which is structural rather than probabilistic.
    /// Non-zero is a soundness alarm.
    pub unnamed_applications: usize,
}

impl FunctionAbstractionWitness {
    /// `true` only when at least one pair was compared, none disagreed, and
    /// every original application was named by the abstraction.
    ///
    /// Deliberately `false` for an all-`unavailable` run: a witness that
    /// examined nothing has not witnessed anything.
    #[must_use]
    pub fn is_faithful(&self) -> bool {
        self.disagreement.is_none() && self.unnamed_applications == 0 && self.compared > 0
    }
}

/// Witnesses that `elim`'s function-abstraction step is faithful to
/// uninterpreted-function semantics, by evaluating the original assertions and
/// their abstractions under the same concrete assignments.
///
/// `arena` must be the arena the elimination ran on -- the fresh application
/// symbols live there -- and `assertions` the ORIGINAL, function-applying
/// assertions it was given, the same pair [`eliminate_functions`] was called
/// with. For each sample the witness binds every symbol, builds one
/// [`FuncValue`] per uninterpreted function from the applications' evaluated
/// arguments, binds each fresh symbol to that function's value there, and
/// compares `assertions[k]` against `elim.abstraction()[k]`.
///
/// The comparison is against [`FunctionElimination::abstraction`], not
/// [`FunctionElimination::assertions`]: the congruence constraints are a
/// separate obligation with its own discharge, and every sampled assignment
/// satisfies them by construction anyway, since the fresh symbols are read out
/// of a genuine function.
///
/// Returns `compared == 0` with no disagreement when `elim` eliminated no
/// functions, or when `assertions` and the abstraction have different lengths.
/// Both are "nothing to witness" rather than a pass, and
/// [`FunctionAbstractionWitness::is_faithful`] reports them as such.
#[must_use]
pub fn witness_function_abstraction(
    arena: &TermArena,
    assertions: &[TermId],
    elim: &FunctionElimination,
    samples: usize,
) -> FunctionAbstractionWitness {
    let mut witness = FunctionAbstractionWitness {
        compared: 0,
        unavailable: 0,
        disagreement: None,
        unnamed_applications: 0,
    };
    let abstraction = elim.abstraction();
    if !elim.had_functions() || abstraction.len() != assertions.len() {
        return witness;
    }
    let seeds = function_seeds(arena);
    // Collected once: every `Op::Apply` subterm of the ORIGINAL assertions,
    // which is the population the abstraction is supposed to have named.
    let original_applications = collect_applications(arena, assertions);

    for sample in 0..samples {
        let Some(mut assignment) = crate::arrays::sample_assignment(arena, sample) else {
            witness.unavailable += assertions.len();
            continue;
        };
        let Some(tables) = bind_application_symbols(arena, elim, &seeds, sample, &mut assignment)
        else {
            witness.unavailable += assertions.len();
            continue;
        };
        // Every original application must be NAMED by the abstraction at this
        // sample's argument values. See `unnamed_applications` for the measured
        // defect this catches and the value comparison does not.
        for &(func, ref args) in &original_applications {
            let mut values = Vec::with_capacity(args.len());
            let mut resolved = true;
            for &arg in args {
                match eval(arena, arg, &assignment) {
                    Ok(value) => values.push(value),
                    Err(_) => {
                        resolved = false;
                        break;
                    }
                }
            }
            if !resolved {
                witness.unavailable += 1;
                continue;
            }
            let named = tables
                .get(&func)
                .is_some_and(|table| table.iter().any(|(key, _)| *key == values));
            if !named {
                witness.unnamed_applications += 1;
            }
        }
        // One memo per sample, shared across BOTH sides and every assertion:
        // the assignment is fixed within a sample, and the two sides share most
        // of their structure (the abstraction is the originals with
        // applications replaced). Built only after every binding is in place --
        // a memo carried through the fixpoint below would cache values computed
        // against a partial assignment.
        let mut memo: HashMap<TermId, Value> = HashMap::new();
        for (index, (&original, &abstracted)) in
            assertions.iter().zip(abstraction.iter()).enumerate()
        {
            let (Ok(lhs), Ok(rhs)) = (
                axeyum_ir::eval_with_memo(arena, original, &assignment, &mut memo),
                axeyum_ir::eval_with_memo(arena, abstracted, &assignment, &mut memo),
            ) else {
                witness.unavailable += 1;
                continue;
            };
            witness.compared += 1;
            if lhs != rhs && witness.disagreement.is_none() {
                witness.disagreement = Some(FunctionAbstractionDisagreement {
                    sample,
                    assertion: index,
                    original: lhs,
                    abstracted: rhs,
                });
            }
        }
    }
    witness
}

/// A stable per-function seed, taken from the arena's own declaration order
/// (which is a determinism promise) rather than from anything `FuncId` exposes.
fn function_seeds(arena: &TermArena) -> BTreeMap<FuncId, u64> {
    arena
        .functions()
        .enumerate()
        .map(|(index, (func, _, _, _))| (func, index as u64 + 1))
        .collect()
}

/// Builds one [`FuncValue`] per uninterpreted function and binds every fresh
/// application symbol to that function's value at the application's evaluated
/// arguments.
///
/// An application's arguments may themselves contain abstracted applications --
/// `f(g(x))` -- so this iterates to a fixpoint rather than assuming discovery
/// order is topological. Returns `false` when applications remain unresolved
/// and no progress is left, or when a sort cannot be sampled, which makes the
/// whole sample *unavailable*.
///
/// **The table is keyed by argument VALUES, not by application index.** That is
/// what makes the extension a function: two applications of the same `f` whose
/// arguments evaluate equal get the same result, so the sampled assignment
/// satisfies the congruence constraints by construction and the witness is
/// about the abstraction alone.
type ApplicationTables = BTreeMap<FuncId, Vec<(Vec<Value>, Value)>>;

fn bind_application_symbols(
    arena: &TermArena,
    elim: &FunctionElimination,
    seeds: &BTreeMap<FuncId, u64>,
    sample: usize,
    assignment: &mut Assignment,
) -> Option<ApplicationTables> {
    let applications = elim.applications();
    let mut tables: ApplicationTables = BTreeMap::new();

    let mut pending: Vec<usize> = (0..applications.len()).collect();
    while !pending.is_empty() {
        let mut progressed = false;
        let mut still_pending = Vec::with_capacity(pending.len());
        for &position in &pending {
            let (func, args, fresh) = applications[position];
            // No memo here: the assignment grows as bindings are added, so a
            // cached value could predate the binding it depends on.
            let mut values = Vec::with_capacity(args.len());
            let mut resolved = true;
            for &arg in args {
                match eval(arena, arg, assignment) {
                    Ok(value) => values.push(value),
                    Err(_) => {
                        resolved = false;
                        break;
                    }
                }
            }
            if !resolved {
                still_pending.push(position);
                continue;
            }
            let (_, _, result_sort) = arena.function(func);
            let seed_base = seeds.get(&func).copied().unwrap_or(1);
            let table = tables.entry(func).or_default();
            let result = match table.iter().find(|(key, _)| *key == values) {
                Some((_, existing)) => existing.clone(),
                None => {
                    let seed = crate::arrays::mix(seed_base, table.len() as u64 + 1);
                    let value = sample_value_of_sort(result_sort, sample, seed)?;
                    table.push((values.clone(), value.clone()));
                    value
                }
            };
            assignment.set(fresh, result);
            progressed = true;
        }
        if !still_pending.is_empty() && !progressed {
            return None;
        }
        pending = still_pending;
    }

    // Publish each table as a real interpretation, so the ORIGINAL assertions'
    // `Op::Apply` nodes evaluate to the same values the fresh symbols carry.
    for (func, points) in &tables {
        let func = *func;
        let (_, params, result_sort) = arena.function(func);
        let params: Vec<Sort> = params.to_vec();
        let default = sample_value_of_sort(result_sort, sample, crate::arrays::mix(0, 0))?;
        let mut interpretation = if FuncValue::uses_value_storage_for(&params, result_sort) {
            FuncValue::constant_value(params, result_sort, default)
        } else {
            FuncValue::constant(params, result_sort, default.scalar_code())
        };
        for (key, value) in points {
            interpretation = if interpretation.uses_value_storage() {
                interpretation.define_value(key, value.clone())
            } else {
                let coded: Vec<u128> = key.iter().map(Value::scalar_code).collect();
                interpretation.define(&coded, value.scalar_code())
            };
        }
        assignment.set_function(func, interpretation);
    }
    Some(tables)
}

/// Every `Op::Apply` subterm reachable from `assertions`, as
/// `(function, argument terms)`, deduplicated by term id and visited in a
/// deterministic order.
fn collect_applications(arena: &TermArena, assertions: &[TermId]) -> Vec<(FuncId, Vec<TermId>)> {
    let mut seen: BTreeSet<TermId> = BTreeSet::new();
    let mut found = Vec::new();
    let mut stack: Vec<TermId> = assertions.iter().rev().copied().collect();
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        if let TermNode::App { op, args } = arena.node(term) {
            if let Op::Apply(func) = op {
                found.push((*func, args.to_vec()));
            }
            stack.extend(args.iter().copied());
        }
    }
    found
}

/// A sampled value of `sort`, or `None` for a sort this witness cannot build.
///
/// Deliberately narrow: `Bool` and `BitVec` up to 128 bits are what
/// `eliminate_functions`' shipping consumer (`QF_UFBV`) produces. Anything else
/// makes the sample *unavailable*, which is a reported coverage hole rather
/// than a silent pass.
fn sample_value_of_sort(sort: Sort, sample: usize, seed: u64) -> Option<Value> {
    match sort {
        Sort::Bool => Some(Value::Bool(crate::arrays::sample_bit(sample, seed))),
        Sort::BitVec(width) if width <= 128 => Some(Value::Bv {
            width,
            value: crate::arrays::sample_bits(sample, seed, width),
        }),
        _ => None,
    }
}
