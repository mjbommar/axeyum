//! Datatype simplification: read-over-construct (ADR-0022).
//!
//! The denotation-preserving core of datatype solving, analogous to array
//! read-over-write ([`crate::eliminate_arrays`]):
//!
//! - `select_i(construct_c(a0, …, an))` → `a_i` when the selector's constructor
//!   matches the constructor that built the value (the field is exactly `a_i`);
//! - `is_c(construct_d(…))` → `true`/`false` (the constant `c == d`);
//! - `(= x construct_C(a…))` → the constructor axiom `is_C(x) ∧ ⋀ sel_i(x) = a_i`,
//!   with each conjunct re-folded (so a nested constructor expands too);
//! - a datatype-sorted `ite` is LIFTED out of `is` / `select` / `=`:
//!   `sel_c(ite(b, x, y))` → `ite(b, sel_c(x), sel_c(y))`, and likewise for the
//!   tester and for either side of an equality, bounded by
//!   [`ITE_LIFT_MAX_LEAVES`].
//!
//! Every rewrite preserves denotation under every assignment (they mirror the
//! evaluator's datatype semantics exactly), so no model projection is needed.
//! A selector over a *different* constructor is left untouched: SMT-LIB leaves
//! it UNSPECIFIED, so there is no value to fold it to — folding it to the
//! evaluator's total-convention default would be a wrong answer, not a
//! simplification (ADR-1930; `axeyum_solver::datatype_native` abstracts it to a
//! free variable instead). Applied bottom-up, this collapses datatype terms that
//! are built from explicit constructors down to the underlying theories
//! (bit-vectors, Booleans, …); datatype *variables* (which need a native
//! datatype theory) are left in place for the caller to detect and report
//! unsupported.

use std::collections::HashMap;

use axeyum_ir::{IrError, Op, Sort, TermArena, TermId, TermNode};

use crate::canonical::build_app;

/// Rewrites each assertion, folding `select`/`test` over matching constructors.
///
/// # Errors
///
/// Returns [`IrError`] from the IR builders during term reconstruction.
pub fn simplify_datatypes(
    arena: &mut TermArena,
    assertions: &[TermId],
) -> Result<Vec<TermId>, IrError> {
    let mut memo: HashMap<TermId, TermId> = HashMap::new();
    let mut out = Vec::with_capacity(assertions.len());
    for &assertion in assertions {
        out.push(simplify(arena, assertion, &mut memo)?);
    }
    Ok(out)
}

/// Bottom-up simplification of one term.
fn simplify(
    arena: &mut TermArena,
    term: TermId,
    memo: &mut HashMap<TermId, TermId>,
) -> Result<TermId, IrError> {
    if let Some(&cached) = memo.get(&term) {
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
        TermNode::App { op, args } => {
            // Simplify children first.
            let mut new_args = Vec::with_capacity(args.len());
            for &arg in &args {
                new_args.push(simplify(arena, arg, memo)?);
            }
            fold_datatype_op(arena, op, &new_args)?
        }
    };
    memo.insert(term, result);
    Ok(result)
}

/// The most branch combinations an `ite` lift is allowed to create. A lift is
/// linear in one `ite` tree but MULTIPLICATIVE when an equality has one on each
/// side, so an unbounded rule is an exponential blow-up waiting for the right
/// input. 64 covers the shapes the `QF_DT` corpus actually writes (the
/// `barrett-jsat` `typed_` family nests one or two deep); past it the term is
/// left alone, which is the identity rewrite.
const ITE_LIFT_MAX_LEAVES: usize = 64;

/// Folds a datatype `select`/`test` whose argument is now an explicit
/// constructor application; otherwise rebuilds the op over the simplified args.
fn fold_datatype_op(arena: &mut TermArena, op: Op, args: &[TermId]) -> Result<TermId, IrError> {
    // Lift a datatype-sorted `ite` out of `is` / `select` / `=` first:
    //
    //   sel_c(ite(b, x, y))  ->  ite(b, sel_c(x), sel_c(y))
    //   is_c(ite(b, x, y))   ->  ite(b, is_c(x),  is_c(y))
    //   (= (ite b x y) z)    ->  ite(b, (= x z),  (= y z))
    //
    // Denotation-preserving under every assignment: the `ite` selects one
    // branch, and the operator is applied to that branch either way. It is what
    // turns a datatype-sorted `ite` -- which nothing downstream can expand, and
    // which the native route refuses as "a datatype-sorted term other than a
    // free variable or constructor" -- into Boolean structure over operands that
    // CAN be expanded. Measured on the QF_DT parity list: the whole `typed_`
    // half of `barrett-jsat` writes `(= (ite ((_ is cons) x) (car x) (leaf
    // zero)) y)` and similar.
    if let Some(lifted) = lift_dt_ite(arena, op, args)? {
        return Ok(lifted);
    }
    match op {
        Op::DtSelect { constructor, index } => {
            if let Some((built, fields)) = as_construct(arena, args[0])
                && built == constructor
            {
                // select_c(construct_c(a0, …)) = a_index.
                return Ok(fields[index as usize]);
            }
            build_app(arena, op, args)
        }
        Op::DtTest(constructor) => {
            if let Some((built, _)) = as_construct(arena, args[0]) {
                // is_c(construct_d(…)) = (c == d).
                return Ok(arena.bool_const(built == constructor));
            }
            build_app(arena, op, args)
        }
        // Datatype constructor equality `(= x C(a…))` is the constructor axiom:
        // `is_C(x) ∧ ⋀ sel_i(x) = a_i` (just `is_C(x)` for a nullary C). This
        // makes the common idiom `(= c red)` decidable by the native solver,
        // which otherwise only accepts `is`/`select` over a variable.
        Op::Eq if matches!(arena.sort_of(args[0]), Sort::Datatype(_)) => {
            if let Some((ctor, fields)) = as_construct(arena, args[0]) {
                return expand_constructor_eq(arena, ctor, &fields, args[1]);
            }
            if let Some((ctor, fields)) = as_construct(arena, args[1]) {
                return expand_constructor_eq(arena, ctor, &fields, args[0]);
            }
            build_app(arena, op, args)
        }
        _ => build_app(arena, op, args),
    }
}

/// Expands `(= other C(fields…))` to the constructor axiom `is_C(other) ∧ ⋀
/// sel_i(other) = fields_i`. The produced `select`/`test` are re-folded (so when
/// `other` is itself a constructor the whole thing collapses to a constant).
///
/// The per-field equality is re-folded TOO, which is not cosmetic: a field may
/// itself be a constructor application, and `(= (car x) (node null))` is the
/// same shape this function exists to expand. Building it with a raw
/// `arena.eq` left a constructor standing on one side of an equality, which the
/// native route refuses outright (`is`/`select`/`==` over a non-variable
/// datatype term). The `QF_DT` corpus writes nested constructors routinely —
/// `(= (cons (node null) (children (leaf x1))) x4)` is one assertion from one
/// file. Recursion terminates because each step strips one constructor layer
/// from a finite term.
fn expand_constructor_eq(
    arena: &mut TermArena,
    ctor: axeyum_ir::ConstructorId,
    fields: &[TermId],
    other: TermId,
) -> Result<TermId, IrError> {
    let mut acc = fold_datatype_op(arena, Op::DtTest(ctor), &[other])?;
    for (i, &field) in fields.iter().enumerate() {
        let sel = fold_datatype_op(
            arena,
            Op::DtSelect {
                constructor: ctor,
                index: u32::try_from(i).expect("field index fits u32"),
            },
            &[other],
        )?;
        let eq = fold_datatype_op(arena, Op::Eq, &[sel, field])?;
        acc = arena.and(acc, eq)?;
    }
    Ok(acc)
}

/// `(condition, then, else)` when `term` is a DATATYPE-sorted `ite`.
fn as_dt_ite(arena: &TermArena, term: TermId) -> Option<(TermId, TermId, TermId)> {
    match arena.node(term) {
        TermNode::App { op: Op::Ite, args } if matches!(arena.sort_of(term), Sort::Datatype(_)) => {
            Some((args[0], args[1], args[2]))
        }
        _ => None,
    }
}

/// How many branch combinations fully distributing `term`'s datatype-sorted
/// `ite` tree would produce, saturating just past `cap` so a pathological input
/// costs a bounded walk.
fn dt_ite_leaves(arena: &TermArena, term: TermId, cap: usize) -> usize {
    match as_dt_ite(arena, term) {
        Some((_, then_t, else_t)) => dt_ite_leaves(arena, then_t, cap)
            .saturating_add(dt_ite_leaves(arena, else_t, cap))
            .min(cap.saturating_add(1)),
        None => 1,
    }
}

/// Distributes `op` over a datatype-sorted `ite` operand, or `None` when there
/// is none to distribute or the lift would exceed [`ITE_LIFT_MAX_LEAVES`].
fn lift_dt_ite(arena: &mut TermArena, op: Op, args: &[TermId]) -> Result<Option<TermId>, IrError> {
    let position = match op {
        Op::DtSelect { .. } | Op::DtTest(_) => 0,
        Op::Eq if args.len() == 2 && matches!(arena.sort_of(args[0]), Sort::Datatype(_)) => {
            if as_dt_ite(arena, args[0]).is_some() {
                0
            } else if as_dt_ite(arena, args[1]).is_some() {
                1
            } else {
                return Ok(None);
            }
        }
        _ => return Ok(None),
    };
    let Some((condition, then_t, else_t)) = as_dt_ite(arena, args[position]) else {
        return Ok(None);
    };
    // The budget is over the WHOLE operand list: an equality with an `ite` on
    // each side multiplies, and checking only the one being lifted here would
    // miss that (the second side is lifted by the recursive calls below).
    let leaves: usize = args
        .iter()
        .map(|&arg| dt_ite_leaves(arena, arg, ITE_LIFT_MAX_LEAVES))
        .product();
    if leaves > ITE_LIFT_MAX_LEAVES {
        return Ok(None);
    }
    let mut then_args = args.to_vec();
    then_args[position] = then_t;
    let mut else_args = args.to_vec();
    else_args[position] = else_t;
    let then_folded = fold_datatype_op(arena, op, &then_args)?;
    let else_folded = fold_datatype_op(arena, op, &else_args)?;
    Ok(Some(arena.ite(condition, then_folded, else_folded)?))
}

/// If `term` is `construct_c(args…)`, returns `(c, args)`.
fn as_construct(
    arena: &TermArena,
    term: TermId,
) -> Option<(axeyum_ir::ConstructorId, Vec<TermId>)> {
    match arena.node(term) {
        TermNode::App {
            op: Op::DtConstruct { constructor, .. },
            args,
        } => Some((*constructor, args.to_vec())),
        _ => None,
    }
}
