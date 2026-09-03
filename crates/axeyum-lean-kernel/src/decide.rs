//! `decide` — the fourth producer: close a **closed** (no free variable) goal
//! by kernel reduction, over ℕ and `Bool`.
//!
//! `decide` is the cheapest producer in the sense of
//! [ADR-0601](../../../docs/research/09-decisions/adr-0601-three-producers-one-trust-anchor.md):
//! there is no search at all, only a fuel-bounded `whnf` walk. It is what
//! every `_evaluates_correctly` test in this crate already writes by hand as
//! a `def_eq` boolean check — this module turns that check into a **kernel
//! proof term**, so the assertion becomes "the kernel accepts this
//! declaration", not "a boolean came back `true`".
//!
//! ## The fragment
//!
//! `Eq Nat lhs rhs`, `Eq Bool lhs rhs`, `Nat.le lhs rhs`, `Nat.lt lhs rhs` —
//! all four over CLOSED terms only (`goal` and every subterm it mentions must
//! carry no `FVar`; a stray loose `BVar` at the top is likewise refused,
//! since a well-formed top-level goal never has one). Anything else declines
//! [`Decline::GoalNotAtomic`], and a goal with a free variable anywhere in it
//! declines [`Decline::NotClosed`] before any reduction is attempted.
//!
//! ## Why a fuel bound, when this calculus is strongly normalizing
//!
//! Every closed, well-typed `Nat` term here does eventually reach a
//! `zero`/`succ` normal form — but "eventually" is not "cheaply": every
//! numeral is unary, so counting up to a genuinely large magnitude costs
//! real wall-clock time, and a term built from nested `WellFounded.fix`
//! unfolds accessibility proofs along the way, not just the arithmetic.
//! [`MAX_MAGNITUDE`] bounds how many `succ` layers this producer will peel
//! before giving up with [`Decline::Undecidable`] — a decline, never a wrong
//! answer, and never a hang. Every call site in this crate keeps magnitudes
//! at or under 30 (`docs/contributor-guide/prelude-build-cost.md`), so the
//! bound costs nothing in practice.
//!
//! ## What gets emitted
//!
//! - `Eq`: `Eq.refl lhs` (or `Eq.refl` at the `Bool` carrier), relying on the
//!   kernel's own `def_eq` to accept it against the stated goal — the
//!   producer only confirms up front that both sides reduce to the *same*
//!   value, so it never hands the kernel a term it expects to be refused.
//! - `Nat.le` / `Nat.lt`: `Nat.le` is declared here as an indexed inductive
//!   with constructors `le_refl : Le n n` and
//!   `le_step : Le n m → Le n (succ m)` (see `nat_prelude::order`), so the
//!   witness for `lo ≤ hi` is `le_step` applied `hi − lo` times to
//!   `le_refl lo`. `Lt a b` is definitionally `Le (succ a) b`, so the `<`
//!   case reduces to the same construction on `succ a` and `b`.
//!
//! ## Two numeral representations, both peeled
//!
//! `whnf` does not always land on a `succ`/`zero` chain: a term built from
//! `Bool`-selected arithmetic (`Nat.pair`'s `if a < b then … else …`, found
//! the hard way when this producer's own retirement conversion first hit
//! it) can reduce to the kernel's compact literal form,
//! `ExprNode::Lit(Lit::Nat(_))`, instead — `Kernel::def_eq` already bridges
//! the two representations (confirmed directly: `def_eq(pair 0 0, zero)` is
//! `true` even though `whnf(pair 0 0)` is a `Lit`, not a `Const zero`), so
//! this producer's own value-peeling has to recognise both, or it declines
//! on perfectly good closed goals. [`nat_value`] checks for a `Lit` at every
//! step, not only at the end, since a `succ` argument can itself whnf to one.

#![allow(clippy::many_single_char_names)]

use crate::ExprNode;
use crate::Lit;
use crate::NatLit;
use crate::NatOps;
use crate::NatPrelude;
use crate::expr::ExprId;

/// The most `succ` layers this producer will peel off a single side of a
/// goal before declining. Every numeral in this kernel is unary — see the
/// module docs.
pub const MAX_MAGNITUDE: u32 = 30;

/// Why [`run`] produced no term.
///
/// Every variant is a *decline*: the goal may still be true (or, for a
/// mismatched `Eq`/`Nat.le`, is simply not what this producer was asked to
/// re-derive) — `decide` never claims a goal is false.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Decline {
    /// `goal` (or a subterm it mentions) carries a free variable.
    NotClosed,
    /// `goal`'s shape is not `Eq Nat`, `Eq Bool`, `Nat.le`, or `Nat.lt`.
    GoalNotAtomic,
    /// Reduction did not reach a `zero`/`succ`/`Bool` value within the fuel
    /// bound, or the two sides reduced to different values (an `Eq`/`Nat.le`
    /// that is not actually true is reported this way rather than as a
    /// separate "refuted" variant, matching `linarith`'s
    /// `NoCertificate` — this producer never claims a goal is FALSE, only
    /// that IT did not close it).
    Undecidable,
}

// --- closedness -------------------------------------------------------

/// `true` when `e` (recursively, through every subterm) carries no `FVar`.
///
/// A loose `BVar` is not treated as "not closed" here: a well-formed
/// top-level goal never has one, and every recursive call stays under
/// whatever binders it started under, so the check is purely about `FVar`.
fn is_closed<D: NatOps>(d: &mut D, e: ExprId) -> bool {
    match d.kernel().expr_node(e).clone() {
        ExprNode::FVar(_) => false,
        ExprNode::BVar(_) | ExprNode::Sort(_) | ExprNode::Const(_, _) | ExprNode::Lit(_) => true,
        ExprNode::Proj(_, _, inner) => is_closed(d, inner),
        ExprNode::App(f, a) => is_closed(d, f) && is_closed(d, a),
        ExprNode::Lam(_, ty, body, _) | ExprNode::Pi(_, ty, body, _) => {
            is_closed(d, ty) && is_closed(d, body)
        }
        ExprNode::Let(_, ty, val, body) => {
            is_closed(d, ty) && is_closed(d, val) && is_closed(d, body)
        }
    }
}

// --- goal parsing -------------------------------------------------------

/// The four shapes this producer (and [`crate::tactic`]'s combinator) knows
/// how to build a relation term for.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Shape {
    Eq,
    Le,
    Lt,
}

fn spine<D: NatOps>(d: &mut D, e: ExprId) -> (ExprId, Vec<ExprId>) {
    let mut args = Vec::new();
    let mut head = e;
    loop {
        let node = d.kernel().expr_node(head).clone();
        let ExprNode::App(f, a) = node else { break };
        args.push(a);
        head = f;
    }
    args.reverse();
    (head, args)
}

fn head_const<D: NatOps>(d: &mut D, e: ExprId) -> Option<crate::NameId> {
    match d.kernel().expr_node(e).clone() {
        ExprNode::Const(n, _) => Some(n),
        _ => None,
    }
}

/// Parse `goal` as `Eq Nat lhs rhs`, `Eq Bool lhs rhs`, `Nat.le lhs rhs` or
/// `Nat.lt lhs rhs`. Shared with [`crate::tactic`], which needs the same
/// shapes to build the gluing motives.
pub(crate) fn parse_goal<D: NatOps>(
    d: &mut D,
    prelude: &NatPrelude,
    e: ExprId,
) -> Option<(Shape, ExprId, ExprId)> {
    let (head, args) = spine(d, e);
    let name = head_const(d, head)?;
    if name == prelude.logic.eq && args.len() == 3 {
        return Some((Shape::Eq, args[1], args[2]));
    }
    if name == prelude.le && args.len() == 2 {
        return Some((Shape::Le, args[0], args[1]));
    }
    if name == prelude.lt && args.len() == 2 {
        return Some((Shape::Lt, args[0], args[1]));
    }
    None
}

// --- reduction ------------------------------------------------------------

/// Peel `e` down to its numeral value: `whnf`, and if the head is `succ`,
/// recurse into the argument; if `whnf` instead landed on the kernel's
/// compact `Lit` representation (see the module docs), finish counting from
/// there via [`lit_value`]. Counts layers up to [`MAX_MAGNITUDE`].
fn nat_value<D: NatOps>(d: &mut D, prelude: &NatPrelude, e: ExprId) -> Result<u32, Decline> {
    let mut cur = e;
    let mut n = 0u32;
    loop {
        let w = d.kernel().whnf(cur);
        if let ExprNode::Const(name, _) = d.kernel().expr_node(w).clone()
            && name == prelude.zero
        {
            return Ok(n);
        }
        if let ExprNode::Lit(Lit::Nat(lit)) = d.kernel().expr_node(w).clone() {
            return lit_value(n, lit);
        }
        if let ExprNode::App(f, a) = d.kernel().expr_node(w).clone()
            && let ExprNode::Const(name, _) = d.kernel().expr_node(f).clone()
            && name == prelude.succ
        {
            n += 1;
            if n > MAX_MAGNITUDE {
                return Err(Decline::Undecidable);
            }
            cur = a;
            continue;
        }
        return Err(Decline::Undecidable);
    }
}

/// Finish [`nat_value`]'s count from a `Lit` reached partway through
/// peeling: `lit`'s own magnitude, added to the `succ` layers already
/// counted, bounded the same way.
fn lit_value(mut n: u32, lit: NatLit) -> Result<u32, Decline> {
    let mut cur = lit;
    loop {
        if cur.is_zero() {
            return Ok(n);
        }
        n += 1;
        if n > MAX_MAGNITUDE {
            return Err(Decline::Undecidable);
        }
        cur = cur.predecessor().expect("just checked `cur` is not zero");
    }
}

/// `true` when `w` (already `whnf`'d) is `Bool.true`/`Bool.false`; `None`
/// when it is neither.
fn bool_value<D: NatOps>(d: &mut D, e: ExprId) -> Result<bool, Decline> {
    let w = d.kernel().whnf(e);
    let t = d.bool_true();
    let f = d.bool_false();
    if w == t {
        return Ok(true);
    }
    if w == f {
        return Ok(false);
    }
    Err(Decline::Undecidable)
}

/// Build a proof of `Nat.le (num lo) (num hi)` for `lo ≤ hi`: `le_step`
/// applied `hi − lo` times to `le_refl (num lo)`.
fn le_witness<D: NatOps>(d: &mut D, prelude: &NatPrelude, lo: u32, hi: u32) -> ExprId {
    let base = d.num(lo);
    let mut proof = d.lemma(prelude.le_refl, &[base]);
    let mut current = base;
    for _ in lo..hi {
        let next = d.succ(current);
        proof = d.lemma(prelude.le_step, &[base, current, proof]);
        current = next;
    }
    proof
}

/// Prove `goal`, a closed `Eq Nat`, `Eq Bool`, `Nat.le` or `Nat.lt`
/// proposition, by kernel reduction, or decline.
///
/// The returned `ExprId` is an **unchecked** proof term, exactly as every
/// other producer in this crate returns one — the caller pushes it through
/// [`Kernel::add_declaration`](crate::Kernel::add_declaration) (or
/// [`Kernel::infer`](crate::Kernel::infer)), and that is the only thing
/// standing behind it.
///
/// # Errors
///
/// [`Decline::NotClosed`] on a free variable, [`Decline::GoalNotAtomic`] on
/// an unrecognised shape, [`Decline::Undecidable`] when reduction does not
/// settle within [`MAX_MAGNITUDE`] or the two sides disagree.
pub fn run<D: NatOps>(d: &mut D, prelude: &NatPrelude, goal: ExprId) -> Result<ExprId, Decline> {
    if !is_closed(d, goal) {
        return Err(Decline::NotClosed);
    }
    let (shape, lhs, rhs) = parse_goal(d, prelude, goal).ok_or(Decline::GoalNotAtomic)?;

    // `Eq Bool _ _` is the one shape whose operands are not `Nat`-valued;
    // `parse_goal` cannot distinguish it from `Eq Nat` by name alone (`Eq`
    // is polymorphic), so try the `Bool` reading first and fall back.
    if shape == Shape::Eq
        && let (Ok(l), Ok(r)) = (bool_value(d, lhs), bool_value(d, rhs))
    {
        if l == r {
            return Ok(d.bool_refl(lhs));
        }
        return Err(Decline::Undecidable);
    }

    match shape {
        Shape::Eq => {
            let lv = nat_value(d, prelude, lhs)?;
            let rv = nat_value(d, prelude, rhs)?;
            if lv != rv {
                return Err(Decline::Undecidable);
            }
            Ok(d.refl(lhs))
        }
        Shape::Le => {
            let lv = nat_value(d, prelude, lhs)?;
            let rv = nat_value(d, prelude, rhs)?;
            if lv > rv {
                return Err(Decline::Undecidable);
            }
            Ok(le_witness(d, prelude, lv, rv))
        }
        Shape::Lt => {
            let succ_lhs = d.succ(lhs);
            let lv = nat_value(d, prelude, succ_lhs)?;
            let rv = nat_value(d, prelude, rhs)?;
            if lv > rv {
                return Err(Decline::Undecidable);
            }
            Ok(le_witness(d, prelude, lv, rv))
        }
    }
}

#[cfg(test)]
mod tests;
