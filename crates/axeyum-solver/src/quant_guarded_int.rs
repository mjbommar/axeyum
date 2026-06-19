//! Guarded-finite-`Int` universal expansion.
//!
//! Finite-domain quantifier expansion (in `axeyum-rewrite`) is complete for
//! `Bool`/`BitVec`-sorted bound variables but rejects `Int` (an infinite sort).
//! Yet a very common — and decidable — shape is a universal whose body *guards*
//! the integer variable to an explicit, concrete range:
//!
//! ```text
//! ∀x:Int. (lo <= x ∧ x <= hi) => inner(x)
//! ```
//!
//! For an **integer** `x` this is *logically equivalent* to the finite
//! conjunction `⋀_{v=lo}^{hi} inner[x := v]`: outside `[lo, hi]` the guard is
//! false so the implication is vacuously true, and inside it is exactly
//! `inner[v]`. The rewrite is therefore **exact** — both `sat` and `unsat`
//! transfer to the original — so the engine may decide the resulting
//! quantifier-free conjunction directly.
//!
//! This pass rewrites *only* this guarded shape, leaving every other universal
//! (and every other assertion) untouched, so it is strictly additive: it can
//! only turn an otherwise-`unknown` result into `sat`/`unsat`, never change an
//! already-decided one. A range whose size exceeds [`RANGE_SIZE_CAP`], or that
//! is inverted/unbounded, is left unexpanded (a graceful `unknown` via the
//! existing fallback) rather than risking a memory blow-up.

use std::collections::HashMap;

use axeyum_ir::{Op, Sort, SymbolId, TermArena, TermId, TermNode};
use axeyum_rewrite::replace_subterms;

use crate::backend::SolverError;

/// The largest integer range `hi - lo + 1` a guarded universal will be expanded
/// over. A wider range is left unexpanded (a sound `unknown`), so an
/// unbounded/huge guard never blows up the formula or memory.
pub const RANGE_SIZE_CAP: i128 = 4096;

/// Rewrites every top-level guarded-finite-`Int` universal in `assertions` to its
/// equivalent finite conjunction, leaving all other assertions unchanged.
///
/// Returns the (possibly) rewritten assertions and whether any rewrite fired.
/// The rewrite is equivalence-preserving, so a caller may decide the result with
/// the ordinary quantifier-free / finite-expansion dispatch and trust both the
/// `sat` and `unsat` verdicts.
///
/// # Errors
///
/// Returns [`SolverError::Backend`] only on an internal IR builder failure (which
/// cannot occur for well-sorted input); detection failures are *not* errors —
/// the assertion is simply passed through unchanged.
pub fn expand_guarded_int_universals(
    arena: &mut TermArena,
    assertions: &[TermId],
) -> Result<(Vec<TermId>, bool), SolverError> {
    let mut out = Vec::with_capacity(assertions.len());
    let mut rewrote = false;
    for &assertion in assertions {
        match try_expand_assertion(arena, assertion)? {
            Some(expanded) => {
                rewrote = true;
                out.push(expanded);
            }
            None => out.push(assertion),
        }
    }
    Ok((out, rewrote))
}

/// Attempts the guarded-`Int` rewrite on a single top-level assertion. Returns
/// `Ok(None)` when the assertion is not a matching guarded universal (left
/// unchanged by the caller).
fn try_expand_assertion(
    arena: &mut TermArena,
    assertion: TermId,
) -> Result<Option<TermId>, SolverError> {
    // Must be a top-level `forall x. body` with an `Int`-sorted bound variable.
    let TermNode::App {
        op: Op::Forall(var),
        args,
    } = arena.node(assertion)
    else {
        return Ok(None);
    };
    let var = *var;
    let body = args[0];
    if arena.symbol(var).1 != Sort::Int {
        return Ok(None);
    }

    // Body must be an implication `guard => inner`.
    let TermNode::App {
        op: Op::BoolImplies,
        args: imp_args,
    } = arena.node(body)
    else {
        return Ok(None);
    };
    let guard = imp_args[0];
    let inner = imp_args[1];

    // A nested quantifier anywhere in the body is out of scope: the bound var
    // could be re-bound/shadowed and the substitution would be unsound, so fall
    // back rather than guess.
    if contains_quantifier(arena, body) {
        return Ok(None);
    }

    // The guard must pin `x` to a concrete `[lo, hi]` integer range.
    let Some((lo, hi)) = detect_range(arena, guard, var) else {
        return Ok(None);
    };

    // Range must be non-empty and within the deterministic cap; otherwise leave
    // it unexpanded (graceful `unknown`, never an OOM).
    if lo > hi {
        return Ok(None);
    }
    let Some(width) = hi.checked_sub(lo).and_then(|d| d.checked_add(1)) else {
        return Ok(None);
    };
    if width > RANGE_SIZE_CAP {
        return Ok(None);
    }

    // Expand to ⋀_{v=lo}^{hi} inner[x := v]. Substituting a *ground* Int constant
    // for the (quantifier-free-body) bound variable is capture-free.
    let var_term = arena.var(var);
    let err = |e: axeyum_ir::IrError| SolverError::Backend(e.to_string());
    let mut conjunction: Option<TermId> = None;
    let mut v = lo;
    loop {
        let value = arena.int_const(v);
        let mut replacements: HashMap<TermId, TermId> = HashMap::new();
        replacements.insert(var_term, value);
        let mut memo: HashMap<TermId, TermId> = HashMap::new();
        let instance = replace_subterms(arena, inner, &replacements, &mut memo).map_err(err)?;
        conjunction = Some(match conjunction {
            Some(acc) => arena.and(acc, instance).map_err(err)?,
            None => instance,
        });
        if v == hi {
            break;
        }
        v += 1;
    }
    // `lo <= hi` guarantees at least one instance.
    Ok(Some(
        conjunction.expect("non-empty range yields an instance"),
    ))
}

/// Detects whether `guard` constrains `var` to a concrete closed integer range
/// `[lo, hi]`, returning `(lo, hi)`.
///
/// Handled shapes (with `lo`, `hi` literal `Int` constants and `x` the bound
/// variable):
/// - a conjunction `(and a b)` of one lower-bound atom and one upper-bound atom,
///   in either order;
/// - each atom one of `(<= c x)`, `(x >= c)`  → lower bound `x >= c`,
///   `(<= x c)`, `(x >= c)` reversed, etc. — every `<=`/`>=` orientation that
///   pins one side of `x` to a literal.
///
/// Returns `None` for any other shape (a non-conjunctive guard, a missing or
/// duplicated bound, a non-literal bound, or `x` not isolated on one side).
fn detect_range(arena: &TermArena, guard: TermId, var: SymbolId) -> Option<(i128, i128)> {
    let TermNode::App {
        op: Op::BoolAnd,
        args,
    } = arena.node(guard)
    else {
        return None;
    };
    if args.len() != 2 {
        return None;
    }
    let (a, b) = (args[0], args[1]);
    let bound_a = atom_bound(arena, a, var)?;
    let bound_b = atom_bound(arena, b, var)?;
    match (bound_a, bound_b) {
        (Bound::Lower(lo), Bound::Upper(hi)) | (Bound::Upper(hi), Bound::Lower(lo)) => {
            Some((lo, hi))
        }
        // Two lower or two upper bounds do not pin a finite range.
        _ => None,
    }
}

/// One side of an integer range constraint on the bound variable.
enum Bound {
    /// `x >= c` (a lower bound `c`).
    Lower(i128),
    /// `x <= c` (an upper bound `c`).
    Upper(i128),
}

/// Interprets a single guard atom as a lower/upper bound on `var`, when it is a
/// `<=`/`>=` comparison with `var` isolated on one side and a literal `Int`
/// constant on the other. Returns `None` otherwise (e.g. `var` on both sides, a
/// non-literal bound, or a non-comparison atom).
fn atom_bound(arena: &TermArena, atom: TermId, var: SymbolId) -> Option<Bound> {
    let TermNode::App { op, args } = arena.node(atom) else {
        return None;
    };
    if args.len() != 2 {
        return None;
    }
    let (left, right) = (args[0], args[1]);
    let left_is_var = is_var(arena, left, var);
    let right_is_var = is_var(arena, right, var);
    // Exactly one side must be the bare bound variable; the other a literal.
    let (var_on_left, other) = match (left_is_var, right_is_var) {
        (true, false) => (true, right),
        (false, true) => (false, left),
        _ => return None,
    };
    let c = int_literal(arena, other)?;
    match op {
        // x <= c  →  upper c ;  c <= x  →  lower c
        Op::IntLe => Some(if var_on_left {
            Bound::Upper(c)
        } else {
            Bound::Lower(c)
        }),
        // x >= c  →  lower c ;  c >= x  →  upper c
        Op::IntGe => Some(if var_on_left {
            Bound::Lower(c)
        } else {
            Bound::Upper(c)
        }),
        _ => None,
    }
}

/// Whether `term` is the bare bound variable `var`.
fn is_var(arena: &TermArena, term: TermId, var: SymbolId) -> bool {
    matches!(arena.node(term), TermNode::Symbol(s) if *s == var)
}

/// The literal `Int` value of `term`, if it is an integer constant.
fn int_literal(arena: &TermArena, term: TermId) -> Option<i128> {
    match arena.node(term) {
        TermNode::IntConst(value) => Some(*value),
        _ => None,
    }
}

/// Whether `term` contains any quantifier operator.
fn contains_quantifier(arena: &TermArena, term: TermId) -> bool {
    let mut seen = std::collections::BTreeSet::new();
    let mut stack = vec![term];
    while let Some(t) = stack.pop() {
        if !seen.insert(t) {
            continue;
        }
        if let TermNode::App { op, args } = arena.node(t) {
            if matches!(op, Op::Forall(_) | Op::Exists(_)) {
                return true;
            }
            stack.extend(args.iter().copied());
        }
    }
    false
}
