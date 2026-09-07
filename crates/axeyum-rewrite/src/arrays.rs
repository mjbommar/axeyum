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
    eval_with_memo,
};

use crate::canonical::build_app;

/// Largest index width for which array equality is expanded by bounded
/// extensionality (`2^iw` index enumeration). Capped to keep the eager expansion
/// — and the `O(n²)` Ackermann pairing over the resulting selects — bounded;
/// wider-index equalities are reported `Unsupported` rather than blowing up.
const MAX_ARRAY_EQ_INDEX_BITS: u32 = 8;

/// Error from array elimination.
#[derive(Debug, Clone)]
pub enum ArrayElimError {
    /// A construct outside the supported `QF_ABV` fragment (e.g. array equality
    /// over an index too wide to enumerate, or a `select` over a base that is
    /// neither a variable, a store, nor an `ite` of arrays).
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
    abstraction: Vec<TermId>,
    selects: Vec<ProjectedSelect>,
    had_arrays: bool,
}

/// Array abstraction without eager select-congruence constraints.
///
/// Read-over-write and bounded extensionality are still rewritten exactly, but
/// each remaining select over an array symbol is represented by a fresh scalar
/// symbol. The returned assertions are therefore a relaxation until a caller
/// enforces select congruence or accepts a candidate only after projection and
/// replay.
#[derive(Debug, Clone)]
pub struct ArrayAbstraction {
    projection: ArrayElimination,
}

impl ArrayElimination {
    /// The pure-`QF_BV` assertions: rewritten originals plus Ackermann
    /// consistency constraints.
    pub fn assertions(&self) -> &[TermId] {
        &self.assertions
    }

    /// The rewritten-only assertions WITHOUT the appended Ackermann
    /// select-congruence constraints: each `select` over an array variable is
    /// abstracted as a fresh `BitVec` variable, but no select-consistency
    /// lemmas are present. This is the relaxation a lazy/on-demand
    /// select-congruence procedure ([`crate`] consumers in `axeyum-solver`)
    /// starts from, adding congruence lemmas only for the select pairs a
    /// candidate model violates. Read-over-write is already applied (stores are
    /// eliminated) in this abstraction; only select congruence is deferred.
    pub fn abstraction(&self) -> &[TermId] {
        &self.abstraction
    }

    /// The eliminated selects as `(array symbol, index term, fresh result
    /// symbol)` triples, in discovery order (deterministic). Used to build
    /// on-demand select-congruence lemmas: a pair of entries on the same array
    /// whose index terms are equal under a candidate model but whose fresh
    /// symbols differ is a select-consistency violation.
    pub fn selects(&self) -> Vec<(SymbolId, TermId, SymbolId)> {
        self.selects
            .iter()
            .map(|select| (select.array, select.index, select.fresh))
            .collect()
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

impl ArrayAbstraction {
    /// The rewritten original assertions with base-array selects replaced by
    /// fresh scalar symbols and no select-congruence constraints appended.
    pub fn assertions(&self) -> &[TermId] {
        &self.projection.assertions
    }

    /// The abstracted selects as `(array symbol, rewritten index, fresh result)`
    /// triples in deterministic discovery order.
    pub fn selects(&self) -> Vec<(SymbolId, TermId, SymbolId)> {
        self.projection.selects()
    }

    /// Whether the input actually contained an array construct.
    pub fn had_arrays(&self) -> bool {
        self.projection.had_arrays()
    }

    /// Projects a select-consistent abstraction model back to array values.
    ///
    /// # Errors
    ///
    /// Returns [`IrError`] if a select index cannot be evaluated.
    pub fn project_model(
        &self,
        arena: &TermArena,
        model: &Assignment,
    ) -> Result<Assignment, IrError> {
        self.projection.project_model(arena, model)
    }
}

/// Abstracts array reads to fresh scalar symbols without constructing eager
/// pairwise select-congruence constraints.
///
/// The returned formula is a relaxation. Callers may transfer `unsat`
/// directly, but may return `sat` only after establishing select consistency,
/// projecting array values, and replaying the original assertions. Unlike
/// [`eliminate_arrays`], this construction never materializes the quadratic
/// select-pair constraint set.
///
/// # Errors
///
/// Returns [`ArrayElimError`] for constructs outside the supported `QF_ABV`
/// fragment or for an IR builder error.
pub fn abstract_arrays(
    arena: &mut TermArena,
    assertions: &[TermId],
) -> Result<ArrayAbstraction, ArrayElimError> {
    let had_arrays = assertions.iter().any(|&term| contains_array(arena, term));
    if !had_arrays {
        return Ok(ArrayAbstraction {
            projection: ArrayElimination {
                assertions: assertions.to_vec(),
                abstraction: assertions.to_vec(),
                selects: Vec::new(),
                had_arrays: false,
            },
        });
    }

    let mut ctx = Eliminator::default();
    let mut rewritten = Vec::with_capacity(assertions.len());
    for &assertion in assertions {
        rewritten.push(ctx.rewrite(arena, assertion)?);
    }
    Ok(ArrayAbstraction {
        projection: ArrayElimination {
            assertions: rewritten.clone(),
            abstraction: rewritten,
            selects: ctx.selects,
            had_arrays: true,
        },
    })
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
            abstraction: assertions.to_vec(),
            selects: Vec::new(),
            had_arrays: false,
        });
    }

    let mut ctx = Eliminator::default();
    let mut rewritten = Vec::with_capacity(assertions.len());
    for &assertion in assertions {
        rewritten.push(ctx.rewrite(arena, assertion)?);
    }
    // The abstraction is the rewritten-only (post-read-over-write) assertions,
    // before the eager Ackermann select-congruence lemmas are appended.
    let abstraction = rewritten.clone();
    rewritten.extend(ctx.ackermann_constraints(arena)?);

    Ok(ArrayElimination {
        assertions: rewritten,
        abstraction,
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
            | TermNode::WideBvConst(_)
            | TermNode::IntConst(_)
            | TermNode::WideIntConst(_)
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
                self.eliminate_array_eq(arena, args[0], args[1])?
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
            TermNode::App {
                op: Op::ConstArray { .. },
                args,
            } => {
                // `select((as const _) v, i) = v` for every `i`.
                self.rewrite(arena, args[0])?
            }
            TermNode::Symbol(array_symbol) => {
                let Some((_index_width, element_width)) =
                    arena.symbol(array_symbol).1.array_widths()
                else {
                    return Err(ArrayElimError::Unsupported(
                        "eager array elimination supports only bit-vector-indexed, \
                         bit-vector-valued arrays"
                            .to_owned(),
                    ));
                };
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

    /// Eliminates an array equality `a = b` by **bounded extensionality**: over
    /// an `iw`-bit index the arrays are equal iff they agree at every one of the
    /// `2^iw` indices, so this expands to `⋀_{i<2^iw} select(a, i) = select(b, i)`
    /// — an exact, equisatisfiable rewrite. Each `select` resolves through the
    /// same machinery (and Ackermann pairing) as ordinary selects, so symbolic
    /// selects on `a`/`b` elsewhere stay consistent. Refused (sound) when the
    /// index is too wide to enumerate (`iw > MAX_ARRAY_EQ_INDEX_BITS`).
    fn eliminate_array_eq(
        &mut self,
        arena: &mut TermArena,
        a: TermId,
        b: TermId,
    ) -> Result<TermId, ArrayElimError> {
        let Some((iw, _)) = arena.sort_of(a).array_widths() else {
            return Err(ArrayElimError::Unsupported(
                "bounded extensionality currently supports only bit-vector-indexed arrays"
                    .to_owned(),
            ));
        };
        // **Write-index extensionality** (sound, and complete for store chains over
        // a *shared base*): peel both sides' store chains. If they bottom out at the
        // same base array term `S`, then for any index `i` not written by either
        // chain, `a[i] = S[i] = b[i]` automatically — so `a = b` iff `a` and `b`
        // agree at the (finite) set of *written* indices. This decides wide-index
        // `store-chain = store-chain` equalities (e.g. 64-bit indices) that the
        // `2^iw` concrete enumeration below cannot, without enumerating the domain.
        let (base_a, idx_a) = peel_store_chain(arena, a);
        let (base_b, idx_b) = peel_store_chain(arena, b);
        if base_a == base_b && !(idx_a.is_empty() && idx_b.is_empty()) {
            let mut indices = idx_a;
            indices.extend(idx_b);
            let mut seen = std::collections::HashSet::new();
            indices.retain(|t| seen.insert(*t));
            let mut acc: Option<TermId> = None;
            for w in indices {
                // A write index may itself contain array reads (e.g.
                // `store(a, select(a, b), v)`); eliminate those first so the
                // resolved selects carry no raw `Select` into the backend.
                let w = self.rewrite(arena, w)?;
                let sa = self.resolve_select(arena, a, w)?;
                let sb = self.resolve_select(arena, b, w)?;
                let eq_w = arena.eq(sa, sb)?;
                acc = Some(match acc {
                    None => eq_w,
                    Some(prev) => arena.and(prev, eq_w)?,
                });
            }
            return Ok(acc.unwrap_or_else(|| arena.bool_const(true)));
        }
        if iw > MAX_ARRAY_EQ_INDEX_BITS {
            return Err(ArrayElimError::Unsupported(format!(
                "array equality over a {iw}-bit index (bounded extensionality supports \
                 indices up to {MAX_ARRAY_EQ_INDEX_BITS} bits)"
            )));
        }
        let count = 1u128 << iw;
        let mut acc: Option<TermId> = None;
        for i in 0..count {
            let idx = arena.bv_const(iw, i)?;
            let sa = self.resolve_select(arena, a, idx)?;
            let sb = self.resolve_select(arena, b, idx)?;
            let eq_i = arena.eq(sa, sb)?;
            acc = Some(match acc {
                None => eq_i,
                Some(prev) => arena.and(prev, eq_i)?,
            });
        }
        match acc {
            Some(t) => Ok(t),
            None => Ok(arena.bool_const(true)), // 2^iw == 0 is impossible (iw >= 1)
        }
    }

    fn fresh_select_symbol(
        &mut self,
        arena: &mut TermArena,
        width: u32,
    ) -> Result<SymbolId, ArrayElimError> {
        let name = format!("!arr_sel_{}", self.fresh_counter);
        self.fresh_counter += 1;
        Ok(arena.declare_internal(&name, Sort::BitVec(width))?)
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

/// Peels a `store` chain `store(store(…base…, i₁, v₁), …, iₙ, vₙ)` into its base
/// array term and the list of written indices `[iₙ, …, i₁]`. Stops at the first
/// non-`store` term (a variable, `ite`, `const-array`, …), which is the base.
fn peel_store_chain(arena: &TermArena, mut t: TermId) -> (TermId, Vec<TermId>) {
    let mut indices = Vec::new();
    while let TermNode::App {
        op: Op::Store,
        args,
    } = arena.node(t)
    {
        indices.push(args[1]);
        t = args[0];
    }
    (t, indices)
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
            | TermNode::WideBvConst(_)
            | TermNode::IntConst(_)
            | TermNode::WideIntConst(_)
            | TermNode::RealConst(_)
            | TermNode::Symbol(_) => {}
        }
    }
    false
}

// ===========================================================================
// Read-over-write faithfulness witness (ADR-1721 section 7)
// ===========================================================================
//
// `ArrayElimUnsatCertificate::recheck` re-derives the eager elimination and
// compares it to itself. That is a genuine discharge for the Ackermann half --
// the appended congruence set is rebuilt by an independent implementation of one
// schema, so a *spurious* extra constraint is caught -- but it says nothing
// about read-over-write, which is recomputed by the same `resolve_select` on the
// same input. Measured 2026-09-06: with the `Op::Store` arm's `ite` branches
// swapped, `recheck` returns `Ok(true)` over a query that is genuinely
// satisfiable.
//
// This witness is the independent reference that closes it, in the shape
// `crates/axeyum-fp/tests/fpa2bv_faithfulness.rs` already proved on the same
// defect class: rather than re-running the transform, it interprets BOTH sides
// under one concrete assignment and compares the values. Arrays get real
// [`ArrayValue`] maps, each abstracted select symbol is bound to the element the
// sampled array actually holds at the evaluated index -- the exact model
// extension the elimination's soundness argument assumes -- and the original
// assertion is evaluated by the ground evaluator's array semantics, which do not
// go through `resolve_select` at all.
//
// A disagreement is a hard finding. A sample that cannot be built or evaluated
// is counted as *unavailable*, never silently treated as agreement: the same
// honest-hole discipline `PreconditionAudit::denotation_unavailable` uses.

/// Number of sampled assignments [`witness_read_over_write`] is normally given.
///
/// Sample 0 is the all-zero corner and sample 1 the all-ones corner; the rest
/// are seeded pseudorandom, so the sequence is deterministic (a public API
/// promise) and reproducible across runs and hosts.
pub const READ_OVER_WRITE_WITNESS_SAMPLES: usize = 8;

/// Number of overriding entries written into each sampled array value.
///
/// A constant array would make read-over-write's two branches agree whenever the
/// stored element happened to match the default, so the sampled arrays must
/// actually vary across indices for the witness to have teeth.
const SAMPLED_ARRAY_ENTRIES: usize = 4;

/// A disagreement between an original assertion and its post-read-over-write
/// abstraction under one concrete assignment: the elimination is **not**
/// faithful, so any `unsat` derived through it is unsound.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ReadOverWriteDisagreement {
    /// Index of the sampled assignment.
    pub sample: usize,
    /// Index of the assertion, into the caller's `assertions` slice.
    pub assertion: usize,
    /// Value of the original, array-using assertion.
    pub original: Value,
    /// Value of the rewritten abstraction of that assertion.
    pub abstracted: Value,
}

/// Outcome of the read-over-write faithfulness witness.
///
/// `compared` and `unavailable` partition the `(sample, assertion)` pairs the
/// witness attempted, so a caller can report coverage instead of assuming it.
/// `compared == 0` is **not** a pass and [`Self::is_faithful`] does not treat it
/// as one.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ReadOverWriteWitness {
    /// `(sample, assertion)` pairs where both sides evaluated and agreed.
    pub compared: usize,
    /// `(sample, assertion)` pairs skipped: a sort the sampler cannot build, or
    /// an evaluator refusal. A coverage hole, not a pass.
    pub unavailable: usize,
    /// The first disagreement found, if any. Its presence is a soundness alarm.
    pub disagreement: Option<ReadOverWriteDisagreement>,
}

impl ReadOverWriteWitness {
    /// `true` only when at least one pair was compared and none disagreed.
    ///
    /// Deliberately `false` for an all-`unavailable` run: a witness that
    /// examined nothing has not witnessed anything.
    #[must_use]
    pub fn is_faithful(&self) -> bool {
        self.disagreement.is_none() && self.compared > 0
    }
}

/// Witnesses that `elim`'s read-over-write step is faithful to array semantics,
/// by evaluating the original assertions and their abstractions under the same
/// concrete assignments.
///
/// `arena` must be the arena the elimination ran on -- the fresh select symbols
/// live there -- and `assertions` the ORIGINAL, array-using assertions it was
/// given, the same pair [`eliminate_arrays`] was called with. For each sample
/// the witness binds every symbol, overrides each abstracted select symbol with
/// the element the sampled array actually holds at the evaluated index, and
/// compares `assertions[k]` against `elim.abstraction()[k]`.
///
/// The comparison is against [`ArrayElimination::abstraction`], not
/// [`ArrayElimination::assertions`]: the Ackermann constraints are a separate
/// obligation with its own discharge, and every sampled assignment satisfies
/// them by construction anyway, since the fresh symbols are read out of a
/// genuine function.
///
/// Returns `compared == 0` with no disagreement when `elim` eliminated no
/// arrays, or when `assertions` and the abstraction have different lengths.
/// Both are "nothing to witness" rather than a pass, and
/// [`ReadOverWriteWitness::is_faithful`] reports them as such.
#[must_use]
pub fn witness_read_over_write(
    arena: &TermArena,
    assertions: &[TermId],
    elim: &ArrayElimination,
    samples: usize,
) -> ReadOverWriteWitness {
    let mut witness = ReadOverWriteWitness {
        compared: 0,
        unavailable: 0,
        disagreement: None,
    };
    let abstraction = elim.abstraction();
    if !elim.had_arrays() || abstraction.len() != assertions.len() {
        return witness;
    }
    let selects = elim.selects();

    for sample in 0..samples {
        let Some(mut assignment) = sample_assignment(arena, sample) else {
            witness.unavailable += assertions.len();
            continue;
        };
        if !bind_select_symbols(arena, &selects, &mut assignment) {
            witness.unavailable += assertions.len();
            continue;
        }
        // One memo per sample, shared across BOTH sides and every assertion.
        // The assignment is fixed within a sample, so a subterm's value is too,
        // and the two sides share most of their structure (the abstraction is the
        // originals with `select`s replaced). A memo per `eval` call would re-walk
        // that shared structure `2 * assertions.len()` times per sample, which on
        // a large `QF_ABV` query is the difference between a witness worth running
        // inside `recheck` and one that is not.
        let mut memo: HashMap<TermId, Value> = HashMap::new();
        for (index, (&original, &abstracted)) in
            assertions.iter().zip(abstraction.iter()).enumerate()
        {
            let (Ok(lhs), Ok(rhs)) = (
                eval_with_memo(arena, original, &assignment, &mut memo),
                eval_with_memo(arena, abstracted, &assignment, &mut memo),
            ) else {
                witness.unavailable += 1;
                continue;
            };
            witness.compared += 1;
            if lhs != rhs && witness.disagreement.is_none() {
                witness.disagreement = Some(ReadOverWriteDisagreement {
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

/// Builds one sampled assignment over every symbol in `arena`, or `None` if any
/// symbol has a sort this witness cannot sample.
///
/// The abstracted select symbols are `BitVec`, so they get a sampled placeholder
/// here and are overwritten by [`bind_select_symbols`]. Overwriting is
/// deliberate: a select whose index term fails to evaluate must leave the whole
/// sample *unavailable* rather than silently keep an unrelated sampled value.
fn sample_assignment(arena: &TermArena, sample: usize) -> Option<Assignment> {
    let mut assignment = Assignment::new();
    let mut counter = 0u64;
    for (symbol, _name, sort) in arena.symbols() {
        counter += 1;
        let seed = mix(sample as u64, counter);
        let value = match sort {
            Sort::Bool => Value::Bool(sample_bit(sample, seed)),
            Sort::BitVec(width) if width <= 128 => Value::Bv {
                width,
                value: sample_bits(sample, seed, width),
            },
            Sort::Array { .. } => {
                let (index_width, element_width) = sort.array_widths()?;
                if index_width > 128 || element_width > 128 {
                    return None;
                }
                Value::Array(sample_array(sample, seed, index_width, element_width))
            }
            _ => return None,
        };
        assignment.set(symbol, value);
    }
    Some(assignment)
}

/// Binds each abstracted select symbol to the element the sampled array holds at
/// the evaluated index.
///
/// An index term may itself contain abstracted selects -- a read whose index is
/// another read -- so this iterates to a fixpoint rather than assuming discovery
/// order is topological. Returns `false` when selects remain unresolved and no
/// progress is left, which makes the whole sample *unavailable*.
fn bind_select_symbols(
    arena: &TermArena,
    selects: &[(SymbolId, TermId, SymbolId)],
    assignment: &mut Assignment,
) -> bool {
    let mut pending: Vec<usize> = (0..selects.len()).collect();
    while !pending.is_empty() {
        let mut progressed = false;
        let mut still_pending = Vec::with_capacity(pending.len());
        for &position in &pending {
            let (array, index_term, fresh) = selects[position];
            let Ok(Value::Bv { value: index, .. }) = eval(arena, index_term, assignment) else {
                still_pending.push(position);
                continue;
            };
            let Some(Value::Array(map)) = assignment.get(array) else {
                return false;
            };
            assignment.set(
                fresh,
                Value::Bv {
                    width: map.element_width(),
                    value: map.select(index),
                },
            );
            progressed = true;
        }
        if !progressed {
            return false;
        }
        pending = still_pending;
    }
    true
}

/// A sampled array: a constant base plus [`SAMPLED_ARRAY_ENTRIES`] overriding
/// entries, so the map is not constant and read-over-write's two branches are
/// distinguishable.
fn sample_array(sample: usize, seed: u64, index_width: u32, element_width: u32) -> ArrayValue {
    let mut map = ArrayValue::constant(
        index_width,
        element_width,
        sample_bits(sample, seed, element_width),
    );
    for entry in 0..SAMPLED_ARRAY_ENTRIES {
        let entry_seed = mix(seed, entry as u64 + 1);
        let index = sample_bits(sample, entry_seed, index_width);
        let element = sample_bits(sample, mix(entry_seed, 0x5eed), element_width);
        map = map.store(index, element);
    }
    map
}

/// Sample 0 is the all-zero corner, sample 1 the all-ones corner, the rest are
/// seeded pseudorandom.
fn sample_bits(sample: usize, seed: u64, width: u32) -> u128 {
    let mask = if width >= 128 {
        u128::MAX
    } else {
        (1u128 << width) - 1
    };
    match sample {
        0 => 0,
        1 => mask,
        _ => ((u128::from(mix(seed, 1)) << 64) | u128::from(mix(seed, 2))) & mask,
    }
}

fn sample_bit(sample: usize, seed: u64) -> bool {
    match sample {
        0 => false,
        1 => true,
        _ => mix(seed, 3) & 1 == 1,
    }
}

/// `SplitMix64`, so the sample sequence is deterministic and host-independent.
fn mix(a: u64, b: u64) -> u64 {
    let mut z = a
        .wrapping_mul(0x9e37_79b9_7f4a_7c15)
        .wrapping_add(b)
        .wrapping_add(0x9e37_79b9_7f4a_7c15);
    z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
    z ^ (z >> 31)
}

#[cfg(test)]
mod tests {
    use super::{ArrayElimError, abstract_arrays, contains_array, eliminate_arrays};
    use axeyum_ir::{ArraySortKey, ArrayValue, Assignment, Sort, TermArena, Value, eval};

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
    fn abstraction_does_not_materialize_quadratic_select_pairs() {
        let mut arena = TermArena::new();
        let array = arena.array_var("table", 8, 8).unwrap();
        let mut assertions = Vec::new();
        for ordinal in 0..24 {
            let index = arena.bv_var(&format!("index_{ordinal}"), 8).unwrap();
            let value = arena.bv_var(&format!("value_{ordinal}"), 8).unwrap();
            let read = arena.select(array, index).unwrap();
            assertions.push(arena.eq(read, value).unwrap());
        }

        let abstraction = abstract_arrays(&mut arena, &assertions).unwrap();
        assert!(abstraction.had_arrays());
        assert_eq!(abstraction.selects().len(), 24);
        assert_eq!(abstraction.assertions().len(), assertions.len());

        let eager = eliminate_arrays(&mut arena, &assertions).unwrap();
        assert_eq!(eager.assertions().len(), assertions.len() + 24 * 23 / 2);
    }

    #[test]
    #[allow(clippy::many_single_char_names)] // a, i, e, b, c: arrays, index, element
    fn array_equality_eliminates_by_bounded_extensionality() {
        // 3-bit index: `a = store(a, i, e)` expands over the 8 indices and
        // eliminates successfully (extensionality; ADR-0010 follow-up).
        let mut arena = TermArena::new();
        let a = arena.array_var("a", 3, 4).unwrap();
        let i = arena.bv_var("i", 3).unwrap();
        let e = arena.bv_var("e", 4).unwrap();
        let stored = arena.store(a, i, e).unwrap();
        let array_eq = arena.eq(a, stored).unwrap();
        assert!(eliminate_arrays(&mut arena, &[array_eq]).is_ok());

        // A wide index exceeds the enumeration cap and stays Unsupported (sound).
        let b = arena.array_var("b", 16, 8).unwrap();
        let c = arena.array_var("c", 16, 8).unwrap();
        let wide_eq = arena.eq(b, c).unwrap();
        assert!(matches!(
            eliminate_arrays(&mut arena, &[wide_eq]),
            Err(ArrayElimError::Unsupported(_))
        ));
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
                    index: ArraySortKey::BitVec(3),
                    element: ArraySortKey::BitVec(4),
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
                    index: ArraySortKey::BitVec(3),
                    element: ArraySortKey::BitVec(4),
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
