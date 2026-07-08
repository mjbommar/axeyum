//! Finite-range refutation for `bv2nat` (G2).
//!
//! `bv2nat(b)` of a `W`-bit bit-vector is provably in `[0, 2^W - 1]`. The exact
//! integer refuters ([`crate::check_with_lia_simplex`] / the Diophantine and
//! DPLL(LIA) paths) reject a raw `bv2nat(b)` subterm as `Unsupported` — they only
//! linearize integer *symbols* — so an unsatisfiable range constraint such as
//! `bv2nat(b) >= 16` over a 4-bit `b` never becomes `unsat`; the bounded
//! bit-blaster downstream reports `unknown` (no model within the width).
//!
//! [`abstract_bv2nat_for_refutation`] closes that gap by **abstracting** each
//! distinct `bv2nat(b)` term to a fresh `Int` symbol `n` and conjoining the true
//! fact `0 <= n <= 2^W - 1`. The abstraction is a *relaxation*: every model of the
//! original induces a model of the abstraction (take `n := bv2nat(b)`), so an
//! `unsat` of the abstraction transfers soundly to the original. It is used only
//! to discharge `unsat` — the satisfiable / undecided directions fall through to
//! the existing exact path on the *original* assertions, where the bounded
//! bit-blaster handles `bv2nat` natively.
//!
//! Soundness invariants:
//!
//! - The arena hash-conses, so the **same** `bv2nat(b)` `TermId` maps to the
//!   **same** fresh symbol (one entry per distinct term); distinct `b` are
//!   independent variables.
//! - `0 <= bv2nat(b) <= 2^W - 1` is a true fact for *every* `b`, so adding it
//!   weakens nothing — it is sound for both `sat` and `unsat`.
//! - A width guard ([`MAX_BOUND_WIDTH`]) keeps `2^W - 1` within `i128`, so no
//!   pathological constant is ever built; wider `b` are left unabstracted
//!   (graceful: the caller keeps its current behaviour).

use std::collections::HashMap;

use axeyum_ir::{Op, Sort, TermArena, TermId, TermNode};
use axeyum_rewrite::replace_subterms;

use crate::backend::SolverError;

/// Largest bit-vector width for which the range bound `0 <= bv2nat(b) <= 2^W - 1`
/// is materialized. `2^62 - 1` fits comfortably in `i128`, so the constant is
/// always exact; wider `b` are left unabstracted (the constant would not be a
/// faithful `i128`), degrading gracefully to the caller's prior behaviour.
const MAX_BOUND_WIDTH: u32 = 62;

/// Abstracts every distinct `bv2nat(b)` subterm of `assertions` to a fresh `Int`
/// symbol and appends the true range fact `0 <= n <= 2^W - 1` (for `b` of width
/// `W <= MAX_BOUND_WIDTH`). Returns `Ok(None)` when no abstractable `bv2nat` is
/// present (nothing to do — the caller proceeds on the originals unchanged) and
/// otherwise `Ok(Some(relaxed))`, the rewritten assertions plus the bound
/// constraints.
///
/// The returned query is a sound **relaxation**: any model of `assertions`
/// extends to a model of `relaxed` by taking each fresh symbol to be the value of
/// its `bv2nat(b)`, so `unsat` of `relaxed` implies `unsat` of `assertions`. The
/// converse does not hold (the fresh symbols are otherwise unconstrained), so a
/// non-`unsat` outcome must be discarded by the caller.
///
/// # Errors
///
/// Returns [`SolverError::Backend`] if a fresh symbol cannot be declared or a
/// subterm cannot be rebuilt (cannot occur for well-sorted input).
pub fn abstract_bv2nat_for_refutation(
    arena: &mut TermArena,
    assertions: &[TermId],
) -> Result<Option<Vec<TermId>>, SolverError> {
    // Collect the distinct `bv2nat(b)` terms with their bit-vector widths, in a
    // deterministic (first-seen) order over the assertion DAG.
    let mut targets: Vec<(TermId, u32)> = Vec::new();
    let mut seen = std::collections::BTreeSet::new();
    let mut stack: Vec<TermId> = assertions.to_vec();
    while let Some(t) = stack.pop() {
        if !seen.insert(t) {
            continue;
        }
        if let TermNode::App { op, args } = arena.node(t) {
            if matches!(op, Op::Bv2Nat)
                && let Sort::BitVec(w) = arena.sort_of(args[0])
                && w <= MAX_BOUND_WIDTH
                && !targets.iter().any(|&(term, _)| term == t)
            {
                targets.push((t, w));
            }
            let args = args.clone();
            stack.extend(args);
        }
    }
    if targets.is_empty() {
        return Ok(None);
    }

    let err = |e: axeyum_ir::IrError| SolverError::Backend(e.to_string());

    // One fresh Int symbol per distinct `bv2nat(b)` term. The arena hash-conses,
    // so identical `bv2nat(b)` share a `TermId` and therefore a single fresh var;
    // distinct `b` get distinct vars.
    let mut replacements: HashMap<TermId, TermId> = HashMap::new();
    let mut bounds: Vec<TermId> = Vec::new();
    for (i, &(target, width)) in targets.iter().enumerate() {
        let name = format!("!bv2nat.{i}");
        let sym = arena.declare_internal(&name, Sort::Int).map_err(err)?;
        let var = arena.var(sym);
        replacements.insert(target, var);

        // 0 <= var  (lower bound; always exact).
        let zero = arena.int_const(0);
        bounds.push(arena.int_ge(var, zero).map_err(err)?);
        // var <= 2^W - 1  (upper bound; `width <= MAX_BOUND_WIDTH` keeps it in i128).
        let upper = (1i128 << width) - 1;
        let upper_const = arena.int_const(upper);
        bounds.push(arena.int_le(var, upper_const).map_err(err)?);
    }

    let mut memo: HashMap<TermId, TermId> = HashMap::new();
    let mut out = Vec::with_capacity(assertions.len() + bounds.len());
    for &a in assertions {
        out.push(replace_subterms(arena, a, &replacements, &mut memo).map_err(err)?);
    }
    out.extend(bounds);
    Ok(Some(out))
}
