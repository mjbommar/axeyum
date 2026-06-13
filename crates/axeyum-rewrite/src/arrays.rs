//! Eager elimination of arrays (`QF_ABV`) to `QF_BV` (ADR-0010).
//!
//! Two steps reduce array reasoning to pure bit-vectors:
//!
//! 1. **Read-over-write.** `select(store(a, i, e), j)` rewrites to
//!    `ite(i = j, e, select(a, j))`, and `select(ite(c, t, e), j)` to
//!    `ite(c, select(t, j), select(e, j))`, until every remaining `select`
//!    reads an array *variable*.
//! 2. **Ackermann reduction.** Each distinct `select(a, idx)` over an array
//!    variable `a` becomes a fresh `BitVec` symbol, and for every pair of such
//!    selects on the same `a` a consistency constraint `i = j -> s_i = s_j` is
//!    added.
//!
//! The result is pure `QF_BV`, decided by the existing bit-blasting pipeline. A
//! satisfying model is projected back to array values by
//! [`ArrayElimination::project_model`], which replays exactly as for scalars.

use std::collections::HashMap;

use axeyum_ir::{
    ArrayValue, Assignment, IrError, Op, Sort, SymbolId, TermArena, TermId, TermNode, Value, eval,
};

use crate::canonical::build_app;

/// Error from array elimination.
#[derive(Debug, Clone)]
pub enum ArrayElimError {
    /// A construct outside the supported `QF_ABV` fragment (e.g. array equality,
    /// or a `select` over a base that is neither a variable, a store, nor an
    /// `ite` of arrays).
    Unsupported(String),
    /// An IR builder error while constructing replacement terms.
    Ir(IrError),
}

impl core::fmt::Display for ArrayElimError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            ArrayElimError::Unsupported(what) => write!(f, "unsupported array construct: {what}"),
            ArrayElimError::Ir(error) => write!(f, "array elimination IR error: {error}"),
        }
    }
}

impl core::error::Error for ArrayElimError {}

impl From<IrError> for ArrayElimError {
    fn from(error: IrError) -> Self {
        ArrayElimError::Ir(error)
    }
}

/// One eliminated `select` over an array variable, retained so a `QF_BV` model
/// can be projected back to an array value.
#[derive(Debug, Clone)]
struct ProjectedSelect {
    array: SymbolId,
    index: TermId,
    fresh: SymbolId,
}

/// Result of eliminating arrays from a set of assertions.
#[derive(Debug, Clone)]
pub struct ArrayElimination {
    assertions: Vec<TermId>,
    selects: Vec<ProjectedSelect>,
    had_arrays: bool,
}

impl ArrayElimination {
    /// The pure-`QF_BV` assertions: rewritten originals plus Ackermann
    /// consistency constraints.
    pub fn assertions(&self) -> &[TermId] {
        &self.assertions
    }

    /// Whether the input actually contained any array constructs.
    pub fn had_arrays(&self) -> bool {
        self.had_arrays
    }

    /// Projects a `QF_BV` model of the eliminated assertions back to a model over
    /// the original query, reconstructing each array variable's value from its
    /// eliminated selects.
    ///
    /// # Errors
    ///
    /// Returns [`IrError`] if a select index fails to evaluate under `model`.
    ///
    /// # Panics
    ///
    /// Panics if `model` is not a complete model of the eliminated assertions
    /// (a select index is non-bit-vector or a fresh select symbol is
    /// unassigned), which cannot happen for a model returned by a backend that
    /// solved those assertions.
    pub fn project_model(
        &self,
        arena: &TermArena,
        model: &Assignment,
    ) -> Result<Assignment, IrError> {
        let mut projected = model.clone();
        let mut arrays: HashMap<SymbolId, Vec<(u128, u128)>> = HashMap::new();
        for select in &self.selects {
            let index = eval(arena, select.index, model)?
                .as_bv()
                .expect("select index is bit-vector sorted")
                .1;
            let value = model
                .get(select.fresh)
                .and_then(|v| v.as_bv())
                .expect("fresh select symbol is assigned")
                .1;
            arrays.entry(select.array).or_default().push((index, value));
        }
        for (array, entries) in arrays {
            let (index_width, element_width) = arena
                .symbol(array)
                .1
                .array_widths()
                .expect("projected symbol is array sorted");
            let mut value = ArrayValue::constant(index_width, element_width, 0);
            for (index, element) in entries {
                value = value.store(index, element);
            }
            projected.set(array, Value::Array(value));
        }
        Ok(projected)
    }
}

/// Eliminates all array constructs from `assertions`, returning equisatisfiable
/// pure-`QF_BV` assertions plus model-projection metadata.
///
/// If no assertion contains arrays, the assertions are returned unchanged.
///
/// # Errors
///
/// Returns [`ArrayElimError`] for constructs outside the supported `QF_ABV`
/// fragment, or for an internal IR builder error.
pub fn eliminate_arrays(
    arena: &mut TermArena,
    assertions: &[TermId],
) -> Result<ArrayElimination, ArrayElimError> {
    let had_arrays = assertions.iter().any(|&term| contains_array(arena, term));
    if !had_arrays {
        return Ok(ArrayElimination {
            assertions: assertions.to_vec(),
            selects: Vec::new(),
            had_arrays: false,
        });
    }

    let mut ctx = Eliminator::default();
    let mut rewritten = Vec::with_capacity(assertions.len());
    for &assertion in assertions {
        rewritten.push(ctx.rewrite(arena, assertion)?);
    }
    rewritten.extend(ctx.ackermann_constraints(arena)?);

    Ok(ArrayElimination {
        assertions: rewritten,
        selects: ctx.selects,
        had_arrays: true,
    })
}

#[derive(Default)]
struct Eliminator {
    /// Rewrite cache for Bool/BV terms.
    term_memo: HashMap<TermId, TermId>,
    /// Cache for `resolve_select(array, index)`.
    select_memo: HashMap<(TermId, TermId), TermId>,
    /// Selects per array variable, in discovery order, for Ackermann pairing.
    groups: Vec<(SymbolId, Vec<(TermId, SymbolId)>)>,
    /// Flat list for model projection.
    selects: Vec<ProjectedSelect>,
    fresh_counter: usize,
}

impl Eliminator {
    fn rewrite(&mut self, arena: &mut TermArena, term: TermId) -> Result<TermId, ArrayElimError> {
        if let Some(&cached) = self.term_memo.get(&term) {
            return Ok(cached);
        }
        if matches!(arena.sort_of(term), Sort::Array { .. }) {
            return Err(ArrayElimError::Unsupported(
                "array-sorted term in a non-select position".to_owned(),
            ));
        }
        let node = arena.node(term).clone();
        let result = match node {
            TermNode::BoolConst(_)
            | TermNode::BvConst { .. }
            | TermNode::IntConst(_)
            | TermNode::RealConst(_)
            | TermNode::Symbol(_) => term,
            TermNode::App {
                op: Op::Select,
                args,
            } => {
                let index = self.rewrite(arena, args[1])?;
                self.resolve_select(arena, args[0], index)?
            }
            TermNode::App { op: Op::Store, .. } => {
                return Err(ArrayElimError::Unsupported(
                    "store in a non-select position".to_owned(),
                ));
            }
            TermNode::App { op: Op::Eq, args } if is_array(arena, args[0]) => {
                return Err(ArrayElimError::Unsupported("array equality".to_owned()));
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

    /// Resolves `select(array, index)` (with `index` already rewritten) to a
    /// pure-`QF_BV` term.
    fn resolve_select(
        &mut self,
        arena: &mut TermArena,
        array: TermId,
        index: TermId,
    ) -> Result<TermId, ArrayElimError> {
        if let Some(&cached) = self.select_memo.get(&(array, index)) {
            return Ok(cached);
        }
        let node = arena.node(array).clone();
        let result = match node {
            TermNode::App {
                op: Op::Store,
                args,
            } => {
                let store_index = self.rewrite(arena, args[1])?;
                let store_element = self.rewrite(arena, args[2])?;
                let same = arena.eq(index, store_index)?;
                let otherwise = self.resolve_select(arena, args[0], index)?;
                arena.ite(same, store_element, otherwise)?
            }
            TermNode::App { op: Op::Ite, args } => {
                let condition = self.rewrite(arena, args[0])?;
                let then_select = self.resolve_select(arena, args[1], index)?;
                let else_select = self.resolve_select(arena, args[2], index)?;
                arena.ite(condition, then_select, else_select)?
            }
            TermNode::Symbol(array_symbol) => {
                let element_width = arena
                    .symbol(array_symbol)
                    .1
                    .array_widths()
                    .expect("array operand is array sorted")
                    .1;
                let fresh = self.fresh_select_symbol(arena, element_width)?;
                self.record_select(array_symbol, index, fresh);
                arena.var(fresh)
            }
            _ => {
                return Err(ArrayElimError::Unsupported(
                    "select over a non-variable, non-store, non-ite array".to_owned(),
                ));
            }
        };
        self.select_memo.insert((array, index), result);
        Ok(result)
    }

    fn fresh_select_symbol(
        &mut self,
        arena: &mut TermArena,
        width: u32,
    ) -> Result<SymbolId, ArrayElimError> {
        let name = format!("!arr_sel_{}", self.fresh_counter);
        self.fresh_counter += 1;
        Ok(arena.declare(&name, Sort::BitVec(width))?)
    }

    fn record_select(&mut self, array: SymbolId, index: TermId, fresh: SymbolId) {
        self.selects.push(ProjectedSelect {
            array,
            index,
            fresh,
        });
        if let Some((_, group)) = self.groups.iter_mut().find(|(a, _)| *a == array) {
            group.push((index, fresh));
        } else {
            self.groups.push((array, vec![(index, fresh)]));
        }
    }

    fn ackermann_constraints(&self, arena: &mut TermArena) -> Result<Vec<TermId>, ArrayElimError> {
        let mut constraints = Vec::new();
        for (_array, group) in &self.groups {
            for i in 0..group.len() {
                for j in (i + 1)..group.len() {
                    let (index_i, fresh_i) = group[i];
                    let (index_j, fresh_j) = group[j];
                    let same_index = arena.eq(index_i, index_j)?;
                    let var_i = arena.var(fresh_i);
                    let var_j = arena.var(fresh_j);
                    let same_value = arena.eq(var_i, var_j)?;
                    constraints.push(arena.implies(same_index, same_value)?);
                }
            }
        }
        Ok(constraints)
    }
}

fn is_array(arena: &TermArena, term: TermId) -> bool {
    matches!(arena.sort_of(term), Sort::Array { .. })
}

/// Returns `true` if `term` contains any array sort or array operator.
fn contains_array(arena: &TermArena, term: TermId) -> bool {
    let mut seen = std::collections::BTreeSet::new();
    let mut stack = vec![term];
    while let Some(t) = stack.pop() {
        if !seen.insert(t) {
            continue;
        }
        if is_array(arena, t) {
            return true;
        }
        match arena.node(t) {
            TermNode::App { op, args } => {
                if matches!(op, Op::Select | Op::Store) {
                    return true;
                }
                stack.extend(args.iter().copied());
            }
            TermNode::BoolConst(_)
            | TermNode::BvConst { .. }
            | TermNode::IntConst(_)
            | TermNode::RealConst(_)
            | TermNode::Symbol(_) => {}
        }
    }
    false
}

#[cfg(test)]
mod tests {
    use super::{contains_array, eliminate_arrays};
    use axeyum_ir::{ArrayValue, Assignment, Sort, TermArena, Value, eval};

    fn bv(width: u32, value: u128) -> Value {
        Value::Bv { width, value }
    }

    /// Builds a concrete array value over index width 3, element width 4.
    fn sample_array(default: u128) -> ArrayValue {
        ArrayValue::constant(3, 4, default)
            .store(1, 0xa)
            .store(5, 0x3)
    }

    #[test]
    fn no_arrays_passes_through_unchanged() {
        let mut arena = TermArena::new();
        let x = arena.bv_var("x", 8).unwrap();
        let one = arena.bv_const(8, 1).unwrap();
        let f = arena.eq(x, one).unwrap();
        let elim = eliminate_arrays(&mut arena, &[f]).unwrap();
        assert!(!elim.had_arrays());
        assert_eq!(elim.assertions(), &[f]);
    }

    #[test]
    fn array_equality_is_unsupported() {
        let mut arena = TermArena::new();
        let a = arena.array_var("a", 3, 4).unwrap();
        let i = arena.bv_var("i", 3).unwrap();
        let e = arena.bv_var("e", 4).unwrap();
        let stored = arena.store(a, i, e).unwrap();
        let array_eq = arena.eq(a, stored).unwrap();
        assert!(eliminate_arrays(&mut arena, &[array_eq]).is_err());
    }

    #[test]
    #[allow(clippy::many_single_char_names)] // a, i, j, e, k are the array, indices, element, constant
    fn read_over_write_eliminates_arrays_and_preserves_denotation() {
        // F: select(store(a, i, e), j) == k
        let mut arena = TermArena::new();
        let a_sym = arena
            .declare(
                "a",
                Sort::Array {
                    index: 3,
                    element: 4,
                },
            )
            .unwrap();
        let i_sym = arena.declare("i", Sort::BitVec(3)).unwrap();
        let j_sym = arena.declare("j", Sort::BitVec(3)).unwrap();
        let e_sym = arena.declare("e", Sort::BitVec(4)).unwrap();
        let k_sym = arena.declare("k", Sort::BitVec(4)).unwrap();
        let a = arena.var(a_sym);
        let i = arena.var(i_sym);
        let j = arena.var(j_sym);
        let e = arena.var(e_sym);
        let k = arena.var(k_sym);
        let stored = arena.store(a, i, e).unwrap();
        let read = arena.select(stored, j).unwrap();
        let f = arena.eq(read, k).unwrap();

        let elim = eliminate_arrays(&mut arena, &[f]).unwrap();
        assert!(elim.had_arrays());
        for &t in elim.assertions() {
            assert!(
                !contains_array(&arena, t),
                "no array ops remain after elimination"
            );
        }

        for default in [0u128, 7, 15] {
            let array = sample_array(default);
            for i_val in 0..8u128 {
                for j_val in 0..8u128 {
                    for e_val in [0u128, 0xa, 0xf] {
                        let k_val = 0xau128;
                        // Concrete model of the original (array-containing) query.
                        let mut model = Assignment::new();
                        model.set(a_sym, Value::Array(array.clone()));
                        model.set(i_sym, bv(3, i_val));
                        model.set(j_sym, bv(3, j_val));
                        model.set(e_sym, bv(4, e_val));
                        model.set(k_sym, bv(4, k_val));
                        let original = eval(&arena, f, &model).unwrap();

                        // Extend with the consistent fresh select values, then
                        // every eliminated assertion must evaluate true and the
                        // rewritten formula must match the original.
                        let projected = consistent_model(&arena, &elim, &model);
                        assert_eq!(
                            eval(&arena, elim.assertions()[0], &projected).unwrap(),
                            original,
                            "default={default} i={i_val} j={j_val} e={e_val}"
                        );
                        for &constraint in &elim.assertions()[1..] {
                            assert_eq!(
                                eval(&arena, constraint, &projected).unwrap(),
                                Value::Bool(true),
                                "ackermann constraint holds under a consistent model"
                            );
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn distinct_selects_generate_consistent_ackermann_constraints() {
        // F: select(a, i) == select(a, j) — two selects on the same array.
        let mut arena = TermArena::new();
        let a_sym = arena
            .declare(
                "a",
                Sort::Array {
                    index: 3,
                    element: 4,
                },
            )
            .unwrap();
        let i_sym = arena.declare("i", Sort::BitVec(3)).unwrap();
        let j_sym = arena.declare("j", Sort::BitVec(3)).unwrap();
        let a = arena.var(a_sym);
        let i = arena.var(i_sym);
        let j = arena.var(j_sym);
        let read_i = arena.select(a, i).unwrap();
        let read_j = arena.select(a, j).unwrap();
        let f = arena.eq(read_i, read_j).unwrap();

        let elim = eliminate_arrays(&mut arena, &[f]).unwrap();
        // One Ackermann constraint for the single pair of selects.
        assert_eq!(elim.assertions().len(), 2);

        let array = sample_array(2);
        for i_val in 0..8u128 {
            for j_val in 0..8u128 {
                let mut model = Assignment::new();
                model.set(a_sym, Value::Array(array.clone()));
                model.set(i_sym, bv(3, i_val));
                model.set(j_sym, bv(3, j_val));
                let original = eval(&arena, f, &model).unwrap();
                let projected = consistent_model(&arena, &elim, &model);
                assert_eq!(
                    eval(&arena, elim.assertions()[0], &projected).unwrap(),
                    original
                );
                assert_eq!(
                    eval(&arena, elim.assertions()[1], &projected).unwrap(),
                    Value::Bool(true)
                );
            }
        }
    }

    /// Extends `model` with each fresh select symbol set to the true value of
    /// the array at the (non-nested) select index — the consistent assignment.
    fn consistent_model(
        arena: &TermArena,
        elim: &super::ArrayElimination,
        model: &Assignment,
    ) -> Assignment {
        let mut projected = model.clone();
        for select in &elim.selects {
            let index = eval(arena, select.index, model).unwrap().as_bv().unwrap().1;
            let array = model.get(select.array).unwrap();
            let element = array.as_array().unwrap().select(index);
            let width = array.as_array().unwrap().element_width();
            projected.set(select.fresh, bv(width, element));
        }
        projected
    }
}
