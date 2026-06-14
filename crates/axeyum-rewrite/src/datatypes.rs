//! Datatype simplification: read-over-construct (ADR-0022).
//!
//! The denotation-preserving core of datatype solving, analogous to array
//! read-over-write ([`crate::eliminate_arrays`]):
//!
//! - `select_i(construct_c(a0, …, an))` → `a_i` when the selector's constructor
//!   matches the constructor that built the value (the field is exactly `a_i`);
//! - `is_c(construct_d(…))` → `true`/`false` (the constant `c == d`).
//!
//! Both rewrites preserve denotation under every assignment (they mirror the
//! evaluator's datatype semantics exactly), so no model projection is needed.
//! A selector over a *different* constructor is left untouched: it is undefined
//! (the evaluator errors), so it is never folded. Applied bottom-up, this
//! collapses datatype terms that are built from explicit constructors down to
//! the underlying theories (bit-vectors, Booleans, …); datatype *variables*
//! (which need a native datatype theory) are left in place for the caller to
//! detect and report unsupported.

use std::collections::HashMap;

use axeyum_ir::{IrError, Op, TermArena, TermId, TermNode};

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
        | TermNode::IntConst(_)
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

/// Folds a datatype `select`/`test` whose argument is now an explicit
/// constructor application; otherwise rebuilds the op over the simplified args.
fn fold_datatype_op(arena: &mut TermArena, op: Op, args: &[TermId]) -> Result<TermId, IrError> {
    match op {
        Op::DtSelect { constructor, index } => {
            if let Some((built, fields)) = as_construct(arena, args[0]) {
                if built == constructor {
                    // select_c(construct_c(a0, …)) = a_index.
                    return Ok(fields[index as usize]);
                }
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
        _ => build_app(arena, op, args),
    }
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
