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
//!
//! The `inner` body need *not* be quantifier-free: substituting a ground `Int`
//! constant for `x` is capture-free as long as no inner quantifier re-binds `x`
//! itself (which would be unsound shadowing — such a body is declined). An inner
//! `∃y. …` is carried through into each instance verbatim; the caller
//! re-skolemizes the exposed top-level existentials and re-dispatches, so e.g.
//! `∀x:Int. (0≤x≤3) ⇒ ∃y. y = x*x` expands to `⋀_{v=0}^{3} ∃y. y = v*v` and is
//! then decided.

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

/// Skolemizes every existential `∃y. body` that sits in a **strictly positive**
/// Boolean position of each assertion — reachable from the assertion root through
/// only `∧`/`∨` connectives (and nested positive existentials) — replacing it with
/// `body[y := s]` for a fresh constant `s` of `y`'s sort.
///
/// This is the exact shape the guarded-`Int` expansion exposes: expanding
/// `∀x:Int. (lo≤x≤hi) ⇒ ∃y. P(x, y)` yields `⋀_{v} ∃y. P(v, y)`, a conjunction of
/// top-level (positive) existentials that [`skolemize_top_existentials`] (which
/// only matches an assertion whose *root* is `∃`) cannot reach.
///
/// Soundness: under `∧`/`∨` an existential occurs positively, so `… ∃y.P(y) …`
/// is equisatisfiable with `… P(s) …` for a fresh `s` (the solver chooses the
/// witness). Quantifiers reached through any *other* operator (a negation, the
/// antecedent of `⇒`, the test of an `ite`, an equality, …) may be in a negative
/// or mixed position where naive skolemization is unsound, so the descent **stops
/// at every non-`∧`/`∨` node** and leaves that subterm untouched — a residual
/// quantifier there simply routes to the sound refutation/`unknown` fallback,
/// never to a wrong verdict. Universals are likewise left in place. Returns the
/// rewritten assertions and whether any existential was skolemized.
///
/// `next_skolem` seeds (and is advanced past) the fresh-constant counter so the
/// names never collide with the top-level skolemizer's `!sk_*` constants.
///
/// # Errors
///
/// Returns [`SolverError::Backend`] only on an internal IR builder failure.
pub fn skolemize_positive_existentials(
    arena: &mut TermArena,
    assertions: &[TermId],
    next_skolem: &mut u32,
) -> Result<(Vec<TermId>, bool), SolverError> {
    let mut out = Vec::with_capacity(assertions.len());
    let mut changed = false;
    for &assertion in assertions {
        let (rewritten, hit) = skolemize_positive(arena, assertion, next_skolem)?;
        changed |= hit;
        out.push(rewritten);
    }
    Ok((out, changed))
}

/// Recursive worker for [`skolemize_positive_existentials`]. Descends only through
/// `∧`/`∨` (positive connectives) and positive existentials; every other node is
/// returned unchanged.
fn skolemize_positive(
    arena: &mut TermArena,
    term: TermId,
    next_skolem: &mut u32,
) -> Result<(TermId, bool), SolverError> {
    let err = |e: axeyum_ir::IrError| SolverError::Backend(e.to_string());
    match arena.node(term).clone() {
        TermNode::App {
            op: Op::Exists(sym),
            args,
        } => {
            // Positive existential: replace the bound variable with a fresh
            // constant of its sort, then continue skolemizing positively into the
            // (now-substituted) body.
            let sort = arena.symbol(sym).1;
            let skolem = arena
                .declare(&format!("!gk_{}", *next_skolem), sort)
                .map_err(err)?;
            *next_skolem += 1;
            let bound = arena.var(sym);
            let fresh = arena.var(skolem);
            let mut map: HashMap<TermId, TermId> = HashMap::new();
            map.insert(bound, fresh);
            let mut memo: HashMap<TermId, TermId> = HashMap::new();
            let substituted = replace_subterms(arena, args[0], &map, &mut memo).map_err(err)?;
            let (inner, _) = skolemize_positive(arena, substituted, next_skolem)?;
            Ok((inner, true))
        }
        TermNode::App {
            op: op @ (Op::BoolAnd | Op::BoolOr),
            args,
        } => {
            // Both children of `∧`/`∨` are positive positions; recurse.
            let mut new_args = Vec::with_capacity(args.len());
            let mut changed = false;
            for &arg in &args {
                let (rewritten, hit) = skolemize_positive(arena, arg, next_skolem)?;
                changed |= hit;
                new_args.push(rewritten);
            }
            if !changed {
                return Ok((term, false));
            }
            let rebuilt = match op {
                Op::BoolAnd => new_args
                    .into_iter()
                    .try_fold(None::<TermId>, |acc, a| {
                        Ok::<_, SolverError>(Some(match acc {
                            Some(prev) => arena.and(prev, a).map_err(err)?,
                            None => a,
                        }))
                    })?
                    .expect("non-empty and"),
                Op::BoolOr => new_args
                    .into_iter()
                    .try_fold(None::<TermId>, |acc, a| {
                        Ok::<_, SolverError>(Some(match acc {
                            Some(prev) => arena.or(prev, a).map_err(err)?,
                            None => a,
                        }))
                    })?
                    .expect("non-empty or"),
                _ => unreachable!("matched only BoolAnd/BoolOr"),
            };
            Ok((rebuilt, true))
        }
        // Any other node (negation, implication, ite, equality, comparison, a
        // universal, a leaf, …) is a position where positive skolemization is not
        // sound (or not applicable). Leave it byte-identical.
        _ => Ok((term, false)),
    }
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

    // A nested quantifier that *re-binds the outer variable* `x` (same
    // `SymbolId`) is out of scope: substituting `x := v` would capture the
    // inner-bound occurrences and be unsound, so fall back rather than guess.
    // Inner quantifiers over *other* variables are fine — the substitution of a
    // ground `Int` constant for `x` is capture-free regardless of body shape
    // (`x` is not bound by them), and the resulting `∃y. …` instances are
    // handled by re-skolemizing the exposed top-level existentials downstream.
    if rebinds_var(arena, body, var) {
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
    // for the bound variable is capture-free: `x` is not re-bound anywhere in the
    // body (checked above), so no inner binder can shadow the occurrences we
    // rewrite. Any inner `∃y. …` in `inner` is carried through verbatim.
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

/// Whether any inner quantifier in `term` re-binds the outer bound variable
/// `var` (the same [`SymbolId`]). Substituting `var := v` into a body that
/// shadows `var` would capture the inner-bound occurrences and be unsound, so
/// the guarded expansion declines for such a body. Inner quantifiers over *other*
/// variables are not a problem (the substitution of `var` is capture-free w.r.t.
/// them), so they do not trigger a decline.
fn rebinds_var(arena: &TermArena, term: TermId, var: SymbolId) -> bool {
    let mut seen = std::collections::BTreeSet::new();
    let mut stack = vec![term];
    while let Some(t) = stack.pop() {
        if !seen.insert(t) {
            continue;
        }
        if let TermNode::App { op, args } = arena.node(t) {
            if let Op::Forall(bound) | Op::Exists(bound) = op
                && *bound == var
            {
                return true;
            }
            stack.extend(args.iter().copied());
        }
    }
    false
}
