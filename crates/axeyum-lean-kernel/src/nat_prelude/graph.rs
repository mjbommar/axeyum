//! `Nat.Graph` — a computed finite-graph carrier: a decidable adjacency
//! relation together with a vertex bound (ADR-1608).
//!
//! # What this is and why it is shaped like `Nat.Finset`
//!
//! ADR-1520 answered "what is a finite multiset here" by *computing* the
//! carrier rather than extracting it from a quotient, and ADR-1577 did the same
//! for finite sets: `Nat.Finset` is a `(Nat → Bool)` predicate plus a bound,
//! with `memB` truncating at the bound **inside its own definition** so that
//! `mk` applies to any predicate with no well-formedness obligation.
//!
//! A finite simple graph is the exact sibling of that object:
//!
//! ```text
//! inductive Nat.Graph : Type
//!   | mk : (Nat → Nat → Bool) → Nat → Nat.Graph
//!
//! Nat.Graph.rel   g : Nat → Nat → Bool  -- the stored relation, raw
//! Nat.Graph.order g : Nat               -- the vertex bound; vertices are [0, order)
//! Nat.Graph.adjB  g i j :=
//!   andB (andB (i < order g) (j < order g))
//!        (andB (neB i j) (andB (rel g i j) (rel g j i)))
//! ```
//!
//! # The design choice: symmetry and irreflexivity are FORCED, not assumed
//!
//! The two candidate designs were:
//!
//! 1. **Side conditions.** Carry `IsSymmetric g` and `IsIrreflexive g` as
//!    separate predicates and add them as hypotheses to every downstream
//!    statement, or as `Prop` fields of the constructor.
//! 2. **Truncate in the definition**, as `Nat.Finset.memB` truncates at the
//!    bound.
//!
//! This module takes (2), for the reason ADR-1577 gives verbatim. Under (1)
//! every `mk` carries a proof obligation, so a graph produced by an untrusted
//! search — which is the whole point of having the carrier — cannot be
//! transcribed into the kernel without also transcribing two proofs about it.
//! Under (2), [`declare_adjacency_laws`]'s `adjB_symm` and `adjB_irrefl` are
//! theorems about **every** `Nat.Graph`, with no side condition, and
//! `Nat.Graph.mk` applies to any relation at any bound. The lower-bound
//! certificate for a Ramsey number is then a bare relation, exactly as
//! `Nat.Rado.schurSet` is a bare `Nat.Finset` (ADR-1596).
//!
//! The cost is the mirror of `Nat.Finset`'s: `rel` is not observable outside
//! the diagonal-free part of `[0, order)²`, and that is the correct semantics
//! rather than a compromise — two relations that induce the same edges ARE the
//! same graph.
//!
//! **Symmetrization is by conjunction, not disjunction.** `adjB g i j` demands
//! `rel g i j` **and** `rel g j i`, so an edge exists only where the stored
//! relation records it in both directions. The alternative (disjunction, the
//! "symmetric closure") was rejected because it silently promotes a one-sided
//! entry to an edge: a search emitting a directed adjacency table by mistake
//! would get a graph carrying edges it never asserted. With conjunction the
//! failure direction is the safe one — a malformed table yields FEWER edges,
//! never more — and `graph_tests.rs` pins exactly this with a deliberately
//! asymmetric relation.
//!
//! # What is built on it
//!
//! * `neighbors g v : Nat.Finset` — the neighbourhood **is** a `Nat.Finset`,
//!   with no conversion: `Nat.Finset.mk (adjB g v) (order g)`. Because `adjB`
//!   is already truncated, `memB_neighbors` says membership in the
//!   neighbourhood is adjacency, at every index, with no side condition.
//! * `degree g v := Nat.Finset.card (neighbors g v)`, so every counting law in
//!   `finset.rs` applies to degrees for free — `degree_le_order` is one
//!   application of `Nat.countRange_le`.
//!
//! # Every definition here is evaluated
//!
//! The kernel cannot tell a `Definition` is wrong; a `degree` computing the
//! wrong number would have the right type and an empty axiom footprint.
//! `graph_tests.rs` reduces each operation to a numeral at tiny discriminating
//! arguments — a triangle has every degree `2`, a path on three vertices has
//! degrees `1, 2, 1` — and pairs every positive with the specific wrong formula
//! it rules out.

#![allow(clippy::many_single_char_names, clippy::too_many_lines)]

use super::NatPrelude;
use super::ops::{NatDev, NatOps};
use crate::BinderInfo;
use crate::KernelError;
use crate::env::Declaration;
use crate::env::ReducibilityHint;
use crate::expr::ExprId;

// ---------------------------------------------------------------------------
// Small term builders.
// ---------------------------------------------------------------------------

/// The carrier constant `Nat.Graph`.
pub(super) fn graph_ty(d: &mut NatDev<'_>, p: &NatPrelude) -> ExprId {
    d.kernel().const_(p.graph, vec![])
}

/// `Nat → Nat → Bool`, the type of a stored adjacency relation.
pub(super) fn rel_ty(d: &mut NatDev<'_>) -> ExprId {
    let nat = d.nat_ty();
    let bool_ty = d.bool_ty();
    let inner = d.arrow(nat, bool_ty);
    d.arrow(nat, inner)
}

/// `Bool.rec (fun _ => Bool) on_false on_true condition` — a `Bool`-valued
/// `if`. This prelude's per-file convention is a private copy of this one-liner
/// (`finset.rs`, `finite_set.rs` and `multiset.rs` each carry their own).
pub(super) fn bool_select_bool(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    condition: ExprId,
    on_true: ExprId,
    on_false: ExprId,
) -> ExprId {
    let bool_ty = d.bool_ty();
    let anon = d.anon_name();
    let motive = d.kernel().lam(anon, bool_ty, bool_ty, BinderInfo::Default);
    let one = d.level_one();
    let rec = d.kernel().const_(p.logic.bool_rec, vec![one]);
    d.apply(rec, &[motive, on_false, on_true, condition])
}

/// Congruence in a one-hole `Bool` context: `h : Eq Bool a b` gives
/// `Eq Bool (f a) (f b)`. The `Bool` twin of [`NatOps::congr`], which is
/// `Nat`-typed.
pub(super) fn bool_congr(
    d: &mut NatDev<'_>,
    a: ExprId,
    b: ExprId,
    h: ExprId,
    f: &dyn Fn(&mut NatDev<'_>, ExprId) -> ExprId,
) -> ExprId {
    let fa = f(d, a);
    let motive = d.bool_eq_motive(a, &|d, x| {
        let fx = f(d, x);
        d.bool_eq(fa, fx)
    });
    let refl_case = d.bool_refl(fa);
    d.bool_transport(a, motive, refl_case, b, h)
}

/// `Nat.Graph.rel g i j`.
fn g_rel(d: &mut NatDev<'_>, p: &NatPrelude, g: ExprId, i: ExprId, j: ExprId) -> ExprId {
    d.const_app(p.graph_rel, &[g, i, j])
}

/// `Nat.Graph.order g`.
pub(super) fn g_order(d: &mut NatDev<'_>, p: &NatPrelude, g: ExprId) -> ExprId {
    d.const_app(p.graph_order, &[g])
}

/// `Nat.Graph.andB a b`.
pub(super) fn and_b(d: &mut NatDev<'_>, p: &NatPrelude, a: ExprId, b: ExprId) -> ExprId {
    d.const_app(p.graph_and_b, &[a, b])
}

/// `Nat.Graph.notB b`.
pub(super) fn not_b(d: &mut NatDev<'_>, p: &NatPrelude, b: ExprId) -> ExprId {
    d.const_app(p.graph_not_b, &[b])
}

/// `Nat.Graph.orB a b`.
pub(super) fn or_b(d: &mut NatDev<'_>, p: &NatPrelude, a: ExprId, b: ExprId) -> ExprId {
    d.const_app(p.graph_or_b, &[a, b])
}

/// `Nat.Graph.neB i j` — the `Bool` decision `i ≠ j`.
fn ne_b(d: &mut NatDev<'_>, p: &NatPrelude, i: ExprId, j: ExprId) -> ExprId {
    d.const_app(p.graph_ne_b, &[i, j])
}

/// `Nat.Graph.adjB g i j`.
pub(super) fn adj_b(d: &mut NatDev<'_>, p: &NatPrelude, g: ExprId, i: ExprId, j: ExprId) -> ExprId {
    d.const_app(p.graph_adj_b, &[g, i, j])
}

/// `Nat.ble (succ i) n` — the `Bool` decision `i < n`.
fn blt(d: &mut NatDev<'_>, i: ExprId, n: ExprId) -> ExprId {
    let succ_i = d.succ(i);
    d.ble(succ_i, n)
}

/// The two halves of `adjB`'s body, unfolded: `(i < n) && (j < n)` and
/// `neB i j && (rel g i j && rel g j i)`.
fn adj_parts(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    g: ExprId,
    i: ExprId,
    j: ExprId,
) -> (ExprId, ExprId) {
    let n = g_order(d, p, g);
    let li = blt(d, i, n);
    let lj = blt(d, j, n);
    let range = and_b(d, p, li, lj);
    let rij = g_rel(d, p, g, i, j);
    let rji = g_rel(d, p, g, j, i);
    let both = and_b(d, p, rij, rji);
    let distinct = ne_b(d, p, i, j);
    let edge = and_b(d, p, distinct, both);
    (range, edge)
}

/// `neB i j = <target>` from `beq i j = <target'>` — the one-hole context is
/// `neB`'s own body, so this is the only congruence step the `neB` proofs need.
fn ne_b_congr(d: &mut NatDev<'_>, p: &NatPrelude, from: ExprId, to: ExprId, h: ExprId) -> ExprId {
    let p = *p;
    bool_congr(d, from, to, h, &|d, x| {
        let t = d.bool_true();
        let f = d.bool_false();
        bool_select_bool(d, &p, x, f, t)
    })
}

// ---------------------------------------------------------------------------
// The carrier and its projections.
// ---------------------------------------------------------------------------

fn declare_carrier(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let anon = d.anon_name();
    let one = d.level_one();
    let type0 = d.kernel().sort(one);
    let rty = rel_ty(d);

    {
        let mk_ty = {
            let concl = d.kernel().const_(p.graph, vec![]);
            let inner = d.arrow(nat, concl);
            d.arrow(rty, inner)
        };
        d.kernel()
            .add_inductive(p.graph, &[], 0, type0, &[(p.graph_mk, mk_ty)])?;
    }

    let gr = graph_ty(d, &p);

    // rel : Graph -> Nat -> Nat -> Bool
    //     := fun g => Graph.rec.{1} (fun _ => Nat -> Nat -> Bool) (fun f _ => f) g
    {
        let motive = d.kernel().lam(anon, gr, rty, BinderInfo::Default);
        let minor = {
            let f_fv = d.fresh_fvar();
            let f = d.kernel().fvar(f_fv);
            let b_fv = d.fresh_fvar();
            let inner = d.lam_fv(b_fv, nat, f);
            d.lam_fv(f_fv, rty, inner)
        };
        let g_fv = d.fresh_fvar();
        let g = d.kernel().fvar(g_fv);
        let rec = d.kernel().const_(p.graph_rec, vec![one]);
        let body = d.apply(rec, &[motive, minor, g]);
        let value = d.lam_fv(g_fv, gr, body);
        let ty = d.arrow(gr, rty);
        d.kernel().add_declaration(Declaration::Definition {
            name: p.graph_rel,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(1),
        })?;
    }

    // order : Graph -> Nat := fun g => Graph.rec.{1} (fun _ => Nat) (fun _ b => b) g
    {
        let motive = d.kernel().lam(anon, gr, nat, BinderInfo::Default);
        let minor = {
            let f_fv = d.fresh_fvar();
            let b_fv = d.fresh_fvar();
            let b = d.kernel().fvar(b_fv);
            let inner = d.lam_fv(b_fv, nat, b);
            d.lam_fv(f_fv, rty, inner)
        };
        let g_fv = d.fresh_fvar();
        let g = d.kernel().fvar(g_fv);
        let rec = d.kernel().const_(p.graph_rec, vec![one]);
        let body = d.apply(rec, &[motive, minor, g]);
        let value = d.lam_fv(g_fv, gr, body);
        let ty = d.arrow(gr, nat);
        d.kernel().add_declaration(Declaration::Definition {
            name: p.graph_order,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(1),
        })?;
    }

    Ok(())
}

/// `andB`, `orB` and `neB` — the three `Bool` combinators `adjB` is assembled
/// from. This prelude had no `Bool` algebra of its own (every user so far
/// spelled a `Bool.rec` inline), and `adjB`'s symmetry proof needs
/// commutativity as a *named* lemma rather than eight inline cases.
fn declare_bool_algebra(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let bool_ty = d.bool_ty();

    // andB a b := if a then b else false
    {
        let a_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let b_fv = d.fresh_fvar();
        let b = d.kernel().fvar(b_fv);
        let false_ = d.bool_false();
        let body = bool_select_bool(d, &p, a, b, false_);
        let value = {
            let inner = d.lam_fv(b_fv, bool_ty, body);
            d.lam_fv(a_fv, bool_ty, inner)
        };
        let ty = {
            let inner = d.arrow(bool_ty, bool_ty);
            d.arrow(bool_ty, inner)
        };
        d.kernel().add_declaration(Declaration::Definition {
            name: p.graph_and_b,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(1),
        })?;
    }

    // orB a b := if a then true else b
    {
        let a_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let b_fv = d.fresh_fvar();
        let b = d.kernel().fvar(b_fv);
        let true_ = d.bool_true();
        let body = bool_select_bool(d, &p, a, true_, b);
        let value = {
            let inner = d.lam_fv(b_fv, bool_ty, body);
            d.lam_fv(a_fv, bool_ty, inner)
        };
        let ty = {
            let inner = d.arrow(bool_ty, bool_ty);
            d.arrow(bool_ty, inner)
        };
        d.kernel().add_declaration(Declaration::Definition {
            name: p.graph_or_b,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(1),
        })?;
    }

    // notB b := if b then false else true
    {
        let b_fv = d.fresh_fvar();
        let b = d.kernel().fvar(b_fv);
        let true_ = d.bool_true();
        let false_ = d.bool_false();
        let body = bool_select_bool(d, &p, b, false_, true_);
        let value = d.lam_fv(b_fv, bool_ty, body);
        let ty = d.arrow(bool_ty, bool_ty);
        d.kernel().add_declaration(Declaration::Definition {
            name: p.graph_not_b,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(1),
        })?;
    }

    // neB i j := if beq i j then false else true
    {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let cond = d.beq(i, j);
        let true_ = d.bool_true();
        let false_ = d.bool_false();
        let body = bool_select_bool(d, &p, cond, false_, true_);
        let value = {
            let inner = d.lam_fv(j_fv, nat, body);
            d.lam_fv(i_fv, nat, inner)
        };
        let ty = {
            let inner = d.arrow(nat, bool_ty);
            d.arrow(nat, inner)
        };
        d.kernel().add_declaration(Declaration::Definition {
            name: p.graph_ne_b,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(1),
        })?;
    }

    Ok(())
}

/// The five `andB` laws every proof below runs on. `andB_comm` and
/// `andB_false_right` are `Bool.rec` case splits whose every leaf is
/// `Eq.refl`; the other three are one congruence step each.
fn declare_bool_laws(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let bool_ty = d.bool_ty();
    let zero_level = d.kernel().level_zero();

    // andB_comm : ∀ a b, Eq Bool (andB a b) (andB b a)
    {
        let a_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let b_fv = d.fresh_fvar();
        let b = d.kernel().fvar(b_fv);
        let lhs = and_b(d, &p, a, b);
        let rhs = and_b(d, &p, b, a);
        let concl = d.bool_eq(lhs, rhs);
        let ty = {
            let inner = d.pi_fv(b_fv, bool_ty, concl);
            d.pi_fv(a_fv, bool_ty, inner)
        };

        // fun a => Bool.rec (fun x => ∀ y, andB x y = andB y x) <false> <true> a
        let outer_motive = {
            let x_fv = d.fresh_fvar();
            let x = d.kernel().fvar(x_fv);
            let y_fv = d.fresh_fvar();
            let y = d.kernel().fvar(y_fv);
            let l = and_b(d, &p, x, y);
            let r = and_b(d, &p, y, x);
            let eq = d.bool_eq(l, r);
            let inner = d.pi_fv(y_fv, bool_ty, eq);
            d.lam_fv(x_fv, bool_ty, inner)
        };
        // With `x` concrete, split on `y`; all four leaves are closed `Bool`
        // terms that reduce to the same value, so each is `Eq.refl`.
        let branch = |d: &mut NatDev<'_>, x_is_true: bool| -> ExprId {
            let x = if x_is_true {
                d.bool_true()
            } else {
                d.bool_false()
            };
            let inner_motive = {
                let y_fv = d.fresh_fvar();
                let y = d.kernel().fvar(y_fv);
                let l = and_b(d, &p, x, y);
                let r = and_b(d, &p, y, x);
                let eq = d.bool_eq(l, r);
                d.lam_fv(y_fv, bool_ty, eq)
            };
            let leaf_true = {
                let t = d.bool_true();
                let v = and_b(d, &p, x, t);
                d.bool_refl(v)
            };
            let leaf_false = {
                let f = d.bool_false();
                let v = and_b(d, &p, x, f);
                d.bool_refl(v)
            };
            let y_fv = d.fresh_fvar();
            let y = d.kernel().fvar(y_fv);
            let rec = d.kernel().const_(p.logic.bool_rec, vec![zero_level]);
            let body = d.apply(rec, &[inner_motive, leaf_false, leaf_true, y]);
            d.lam_fv(y_fv, bool_ty, body)
        };
        let case_true = branch(d, true);
        let case_false = branch(d, false);
        let value = {
            let a2_fv = d.fresh_fvar();
            let a2 = d.kernel().fvar(a2_fv);
            let rec = d.kernel().const_(p.logic.bool_rec, vec![zero_level]);
            let body = d.apply(rec, &[outer_motive, case_false, case_true, a2]);
            d.lam_fv(a2_fv, bool_ty, body)
        };
        d.declare_theorem(p.graph_and_b_comm, ty, value)?;
    }

    // andB_false_right : ∀ a, Eq Bool (andB a false) false
    {
        let a_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let false_ = d.bool_false();
        let lhs = and_b(d, &p, a, false_);
        let concl = d.bool_eq(lhs, false_);
        let ty = d.pi_fv(a_fv, bool_ty, concl);

        let motive = {
            let x_fv = d.fresh_fvar();
            let x = d.kernel().fvar(x_fv);
            let f = d.bool_false();
            let l = and_b(d, &p, x, f);
            let body = d.bool_eq(l, f);
            d.lam_fv(x_fv, bool_ty, body)
        };
        let leaf = {
            let f = d.bool_false();
            d.bool_refl(f)
        };
        let value = {
            let a2_fv = d.fresh_fvar();
            let a2 = d.kernel().fvar(a2_fv);
            let rec = d.kernel().const_(p.logic.bool_rec, vec![zero_level]);
            let body = d.apply(rec, &[motive, leaf, leaf, a2]);
            d.lam_fv(a2_fv, bool_ty, body)
        };
        d.declare_theorem(p.graph_and_b_false_right, ty, value)?;
    }

    // andB_intro : ∀ a b, a = true → b = true → andB a b = true
    {
        let a_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let b_fv = d.fresh_fvar();
        let b = d.kernel().fvar(b_fv);
        let true_ = d.bool_true();
        let ha_ty = d.bool_eq(a, true_);
        let ha_fv = d.fresh_fvar();
        let ha = d.kernel().fvar(ha_fv);
        let hb_ty = d.bool_eq(b, true_);
        let hb_fv = d.fresh_fvar();
        let hb = d.kernel().fvar(hb_fv);
        let lhs = and_b(d, &p, a, b);
        let concl = d.bool_eq(lhs, true_);

        // `andB a b = andB true b`, whose right side δι-reduces to `b`.
        let step1 = bool_congr(d, a, true_, ha, &|d, x| and_b(d, &p, x, b));
        let proof = d.bool_trans(lhs, b, true_, step1, hb);

        let ty = {
            let s4 = d.arrow(hb_ty, concl);
            let s3 = d.arrow(ha_ty, s4);
            let s2 = d.pi_fv(b_fv, bool_ty, s3);
            d.pi_fv(a_fv, bool_ty, s2)
        };
        let value = {
            let s4 = d.lam_fv(hb_fv, hb_ty, proof);
            let s3 = d.lam_fv(ha_fv, ha_ty, s4);
            let s2 = d.lam_fv(b_fv, bool_ty, s3);
            d.lam_fv(a_fv, bool_ty, s2)
        };
        d.declare_theorem(p.graph_and_b_intro, ty, value)?;
    }

    // andB_left : ∀ a b, andB a b = true → a = true
    {
        let a_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let b_fv = d.fresh_fvar();
        let b = d.kernel().fvar(b_fv);
        let true_ = d.bool_true();
        let false_ = d.bool_false();
        let lhs = and_b(d, &p, a, b);
        let h_ty = d.bool_eq(lhs, true_);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let concl = d.bool_eq(a, true_);

        let dichotomy = super::ops::bool_true_or_false(d, &p, a);
        let is_true = d.bool_eq(a, true_);
        let is_false = d.bool_eq(a, false_);
        let on_true = {
            let ht_fv = d.fresh_fvar();
            let ht = d.kernel().fvar(ht_fv);
            d.lam_fv(ht_fv, is_true, ht)
        };
        let on_false = {
            let hf_fv = d.fresh_fvar();
            let hf = d.kernel().fvar(hf_fv);
            // `andB a b = andB false b`, whose right side reduces to `false`.
            let collapse = bool_congr(d, a, false_, hf, &|d, x| and_b(d, &p, x, b));
            let flipped = d.bool_symm(lhs, false_, collapse);
            let absurd = d.bool_trans(false_, lhs, true_, flipped, h);
            let body = d.false_true_elim(concl, absurd);
            d.lam_fv(hf_fv, is_false, body)
        };
        let proof = d.const_app(
            p.logic.or_elim,
            &[is_true, is_false, concl, dichotomy, on_true, on_false],
        );

        let ty = {
            let s3 = d.arrow(h_ty, concl);
            let s2 = d.pi_fv(b_fv, bool_ty, s3);
            d.pi_fv(a_fv, bool_ty, s2)
        };
        let value = {
            let s3 = d.lam_fv(h_fv, h_ty, proof);
            let s2 = d.lam_fv(b_fv, bool_ty, s3);
            d.lam_fv(a_fv, bool_ty, s2)
        };
        d.declare_theorem(p.graph_and_b_left, ty, value)?;
    }

    // andB_right : ∀ a b, andB a b = true → b = true
    {
        let a_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let b_fv = d.fresh_fvar();
        let b = d.kernel().fvar(b_fv);
        let true_ = d.bool_true();
        let lhs = and_b(d, &p, a, b);
        let swapped = and_b(d, &p, b, a);
        let h_ty = d.bool_eq(lhs, true_);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let concl = d.bool_eq(b, true_);

        let comm = d.const_app(p.graph_and_b_comm, &[b, a]);
        let swapped_true = d.bool_trans(swapped, lhs, true_, comm, h);
        let proof = d.const_app(p.graph_and_b_left, &[b, a, swapped_true]);

        let ty = {
            let s3 = d.arrow(h_ty, concl);
            let s2 = d.pi_fv(b_fv, bool_ty, s3);
            d.pi_fv(a_fv, bool_ty, s2)
        };
        let value = {
            let s3 = d.lam_fv(h_fv, h_ty, proof);
            let s2 = d.lam_fv(b_fv, bool_ty, s3);
            d.lam_fv(a_fv, bool_ty, s2)
        };
        d.declare_theorem(p.graph_and_b_right, ty, value)?;
    }

    Ok(())
}

/// `adjB`, `neighbors` and `degree`.
fn declare_operations(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let bool_ty = d.bool_ty();
    let gr = graph_ty(d, &p);
    let fs = d.kernel().const_(p.finset, vec![]);

    // adjB : Graph -> Nat -> Nat -> Bool
    {
        let g_fv = d.fresh_fvar();
        let g = d.kernel().fvar(g_fv);
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let (range, edge) = adj_parts(d, &p, g, i, j);
        let body = and_b(d, &p, range, edge);
        let value = {
            let s3 = d.lam_fv(j_fv, nat, body);
            let s2 = d.lam_fv(i_fv, nat, s3);
            d.lam_fv(g_fv, gr, s2)
        };
        let ty = {
            let s3 = d.arrow(nat, bool_ty);
            let s2 = d.arrow(nat, s3);
            d.arrow(gr, s2)
        };
        d.kernel().add_declaration(Declaration::Definition {
            name: p.graph_adj_b,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(2),
        })?;
    }

    // neighbors : Graph -> Nat -> Nat.Finset := fun g v => Finset.mk (adjB g v) (order g)
    {
        let g_fv = d.fresh_fvar();
        let g = d.kernel().fvar(g_fv);
        let v_fv = d.fresh_fvar();
        let v = d.kernel().fvar(v_fv);
        let fn_ = d.const_app(p.graph_adj_b, &[g, v]);
        let n = g_order(d, &p, g);
        let body = d.const_app(p.finset_mk, &[fn_, n]);
        let value = {
            let inner = d.lam_fv(v_fv, nat, body);
            d.lam_fv(g_fv, gr, inner)
        };
        let ty = {
            let inner = d.arrow(nat, fs);
            d.arrow(gr, inner)
        };
        d.kernel().add_declaration(Declaration::Definition {
            name: p.graph_neighbors,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(4),
        })?;
    }

    // degree : Graph -> Nat -> Nat := fun g v => Finset.card (neighbors g v)
    {
        let g_fv = d.fresh_fvar();
        let g = d.kernel().fvar(g_fv);
        let v_fv = d.fresh_fvar();
        let v = d.kernel().fvar(v_fv);
        let nb = d.const_app(p.graph_neighbors, &[g, v]);
        let body = d.const_app(p.finset_card, &[nb]);
        let value = {
            let inner = d.lam_fv(v_fv, nat, body);
            d.lam_fv(g_fv, gr, inner)
        };
        let ty = {
            let inner = d.arrow(nat, nat);
            d.arrow(gr, inner)
        };
        d.kernel().add_declaration(Declaration::Definition {
            name: p.graph_degree,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(5),
        })?;
    }

    Ok(())
}

// ---------------------------------------------------------------------------
// The adjacency laws — every one of them side-condition-free.
// ---------------------------------------------------------------------------

fn declare_adjacency_laws(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let gr = graph_ty(d, &p);

    // adjB_symm : ∀ g i j, Eq Bool (adjB g i j) (adjB g j i)
    {
        let g_fv = d.fresh_fvar();
        let g = d.kernel().fvar(g_fv);
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);

        let n = g_order(d, &p, g);
        let li = blt(d, i, n);
        let lj = blt(d, j, n);
        let range = and_b(d, &p, li, lj);
        let range_swapped = and_b(d, &p, lj, li);
        let rij = g_rel(d, &p, g, i, j);
        let rji = g_rel(d, &p, g, j, i);
        let both = and_b(d, &p, rij, rji);
        let both_swapped = and_b(d, &p, rji, rij);
        let ne_ij = ne_b(d, &p, i, j);
        let ne_ji = ne_b(d, &p, j, i);
        let edge = and_b(d, &p, ne_ij, both);
        let edge_mid = and_b(d, &p, ne_ji, both);
        let edge_swapped = and_b(d, &p, ne_ji, both_swapped);
        let lhs = and_b(d, &p, range, edge);
        let mid = and_b(d, &p, range_swapped, edge);
        let rhs = and_b(d, &p, range_swapped, edge_swapped);

        let h_range = d.const_app(p.graph_and_b_comm, &[li, lj]);
        let h_both = d.const_app(p.graph_and_b_comm, &[rij, rji]);
        let h_ne = {
            let beq_ij = d.beq(i, j);
            let beq_ji = d.beq(j, i);
            let base = d.const_app(p.beq_comm, &[i, j]);
            ne_b_congr(d, &p, beq_ij, beq_ji, base)
        };
        let h_edge_a = bool_congr(d, ne_ij, ne_ji, h_ne, &|d, x| and_b(d, &p, x, both));
        let h_edge_b = bool_congr(d, both, both_swapped, h_both, &|d, x| {
            and_b(d, &p, ne_ji, x)
        });
        let h_edge = d.bool_trans(edge, edge_mid, edge_swapped, h_edge_a, h_edge_b);
        let step1 = bool_congr(d, range, range_swapped, h_range, &|d, x| {
            and_b(d, &p, x, edge)
        });
        let step2 = bool_congr(d, edge, edge_swapped, h_edge, &|d, x| {
            and_b(d, &p, range_swapped, x)
        });
        let proof = d.bool_trans(lhs, mid, rhs, step1, step2);

        let concl = {
            let l = adj_b(d, &p, g, i, j);
            let r = adj_b(d, &p, g, j, i);
            d.bool_eq(l, r)
        };
        let ty = {
            let s3 = d.pi_fv(j_fv, nat, concl);
            let s2 = d.pi_fv(i_fv, nat, s3);
            d.pi_fv(g_fv, gr, s2)
        };
        let value = {
            let s3 = d.lam_fv(j_fv, nat, proof);
            let s2 = d.lam_fv(i_fv, nat, s3);
            d.lam_fv(g_fv, gr, s2)
        };
        d.declare_theorem(p.graph_adj_b_symm, ty, value)?;
    }

    // adjB_irrefl : ∀ g i, Eq Bool (adjB g i i) false
    {
        let g_fv = d.fresh_fvar();
        let g = d.kernel().fvar(g_fv);
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let false_ = d.bool_false();
        let true_ = d.bool_true();

        let (range, edge) = adj_parts(d, &p, g, i, i);
        let rii = g_rel(d, &p, g, i, i);
        let both = and_b(d, &p, rii, rii);
        let ne_ii = ne_b(d, &p, i, i);
        let beq_ii = d.beq(i, i);
        let h_beq = d.const_app(p.beq_refl, &[i]);
        // `neB i i = if true then false else true`, i.e. `false`.
        let h_ne = ne_b_congr(d, &p, beq_ii, true_, h_beq);
        // `andB (neB i i) both = andB false both`, i.e. `false`.
        let h_edge = bool_congr(d, ne_ii, false_, h_ne, &|d, x| and_b(d, &p, x, both));
        // `andB range edge = andB range false`.
        let step = bool_congr(d, edge, false_, h_edge, &|d, x| and_b(d, &p, range, x));
        let collapse = d.const_app(p.graph_and_b_false_right, &[range]);
        let whole = and_b(d, &p, range, edge);
        let target = and_b(d, &p, range, false_);
        let proof = d.bool_trans(whole, target, false_, step, collapse);

        let concl = {
            let l = adj_b(d, &p, g, i, i);
            let f = d.bool_false();
            d.bool_eq(l, f)
        };
        let ty = {
            let s2 = d.pi_fv(i_fv, nat, concl);
            d.pi_fv(g_fv, gr, s2)
        };
        let value = {
            let s2 = d.lam_fv(i_fv, nat, proof);
            d.lam_fv(g_fv, gr, s2)
        };
        d.declare_theorem(p.graph_adj_b_irrefl, ty, value)?;
    }

    // adjB_of_order_le : ∀ g i j, Le (order g) i → Eq Bool (adjB g i j) false
    {
        let g_fv = d.fresh_fvar();
        let g = d.kernel().fvar(g_fv);
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let n = g_order(d, &p, g);
        let h_ty = d.le(n, i);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let false_ = d.bool_false();

        let (range, edge) = adj_parts(d, &p, g, i, j);
        let li = blt(d, i, n);
        let lj = blt(d, j, n);
        let succ_i = d.succ(i);
        // `Le (order g) i` gives `Lt (order g) (succ i)`, which is
        // `ble_eq_false_of_lt`'s hypothesis at `(succ i, order g)`.
        let hlt = d.lemma(p.succ_le_succ, &[n, i, h]);
        let h_li = d.lemma(p.ble_eq_false_of_lt, &[succ_i, n, hlt]);
        // `andB (blt i n) (blt j n) = andB false (blt j n)`, i.e. `false`.
        let h_range = bool_congr(d, li, false_, h_li, &|d, x| and_b(d, &p, x, lj));
        // `andB range edge = andB false edge`, i.e. `false`.
        let proof = bool_congr(d, range, false_, h_range, &|d, x| and_b(d, &p, x, edge));

        let concl = {
            let l = adj_b(d, &p, g, i, j);
            let f = d.bool_false();
            d.bool_eq(l, f)
        };
        let ty = {
            let s4 = d.arrow(h_ty, concl);
            let s3 = d.pi_fv(j_fv, nat, s4);
            let s2 = d.pi_fv(i_fv, nat, s3);
            d.pi_fv(g_fv, gr, s2)
        };
        let value = {
            let s4 = d.lam_fv(h_fv, h_ty, proof);
            let s3 = d.lam_fv(j_fv, nat, s4);
            let s2 = d.lam_fv(i_fv, nat, s3);
            d.lam_fv(g_fv, gr, s2)
        };
        d.declare_theorem(p.graph_adj_b_of_order_le, ty, value)?;
    }

    // lt_order_of_adjB : ∀ g i j, adjB g i j = true → Lt i (order g)
    {
        let g_fv = d.fresh_fvar();
        let g = d.kernel().fvar(g_fv);
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let true_ = d.bool_true();
        let adj = adj_b(d, &p, g, i, j);
        let h_ty = d.bool_eq(adj, true_);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let n = g_order(d, &p, g);
        let concl = d.lt(i, n);

        let (range, edge) = adj_parts(d, &p, g, i, j);
        let li = blt(d, i, n);
        let lj = blt(d, j, n);
        let h_range = d.const_app(p.graph_and_b_left, &[range, edge, h]);
        let h_li = d.const_app(p.graph_and_b_left, &[li, lj, h_range]);
        let succ_i = d.succ(i);
        let proof = d.lemma(p.le_of_ble_eq_true, &[succ_i, n, h_li]);

        let ty = {
            let s4 = d.arrow(h_ty, concl);
            let s3 = d.pi_fv(j_fv, nat, s4);
            let s2 = d.pi_fv(i_fv, nat, s3);
            d.pi_fv(g_fv, gr, s2)
        };
        let value = {
            let s4 = d.lam_fv(h_fv, h_ty, proof);
            let s3 = d.lam_fv(j_fv, nat, s4);
            let s2 = d.lam_fv(i_fv, nat, s3);
            d.lam_fv(g_fv, gr, s2)
        };
        d.declare_theorem(p.graph_lt_order_of_adj_b, ty, value)?;
    }

    // ne_of_adjB : ∀ g i j, adjB g i j = true → Eq Nat i j → False
    {
        let g_fv = d.fresh_fvar();
        let g = d.kernel().fvar(g_fv);
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let true_ = d.bool_true();
        let false_ = d.bool_false();
        let adj = adj_b(d, &p, g, i, j);
        let h_ty = d.bool_eq(adj, true_);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let heq_ty = d.eq(i, j);
        let heq_fv = d.fresh_fvar();
        let heq = d.kernel().fvar(heq_fv);
        let false_prop = d.kernel().const_(p.logic.false_, vec![]);

        let (range, edge) = adj_parts(d, &p, g, i, j);
        let rij = g_rel(d, &p, g, i, j);
        let rji = g_rel(d, &p, g, j, i);
        let both = and_b(d, &p, rij, rji);
        let ne_ij = ne_b(d, &p, i, j);
        let h_edge = d.const_app(p.graph_and_b_right, &[range, edge, h]);
        let h_ne_true = d.const_app(p.graph_and_b_left, &[ne_ij, both, h_edge]);
        let beq_ij = d.beq(i, j);
        let h_beq = d.lemma(p.beq_eq_true_of_eq, &[i, j, heq]);
        let h_ne_false = ne_b_congr(d, &p, beq_ij, true_, h_beq);
        let flipped = d.bool_symm(ne_ij, false_, h_ne_false);
        let absurd = d.bool_trans(false_, ne_ij, true_, flipped, h_ne_true);
        let proof = d.false_true_elim(false_prop, absurd);

        let ty = {
            let s5 = d.arrow(heq_ty, false_prop);
            let s4 = d.arrow(h_ty, s5);
            let s3 = d.pi_fv(j_fv, nat, s4);
            let s2 = d.pi_fv(i_fv, nat, s3);
            d.pi_fv(g_fv, gr, s2)
        };
        let value = {
            let s5 = d.lam_fv(heq_fv, heq_ty, proof);
            let s4 = d.lam_fv(h_fv, h_ty, s5);
            let s3 = d.lam_fv(j_fv, nat, s4);
            let s2 = d.lam_fv(i_fv, nat, s3);
            d.lam_fv(g_fv, gr, s2)
        };
        d.declare_theorem(p.graph_ne_of_adj_b, ty, value)?;
    }

    // adjB_of_rel : ∀ g i j, Lt i (order g) → Lt j (order g) →
    //   Eq Bool (beq i j) false → rel g i j = true → rel g j i = true →
    //   adjB g i j = true
    {
        let g_fv = d.fresh_fvar();
        let g = d.kernel().fvar(g_fv);
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let n = g_order(d, &p, g);
        let true_ = d.bool_true();
        let false_ = d.bool_false();

        let hi_ty = d.lt(i, n);
        let hi_fv = d.fresh_fvar();
        let hi = d.kernel().fvar(hi_fv);
        let hj_ty = d.lt(j, n);
        let hj_fv = d.fresh_fvar();
        let hj = d.kernel().fvar(hj_fv);
        let beq_ij = d.beq(i, j);
        let hne_ty = d.bool_eq(beq_ij, false_);
        let hne_fv = d.fresh_fvar();
        let hne = d.kernel().fvar(hne_fv);
        let rij = g_rel(d, &p, g, i, j);
        let rji = g_rel(d, &p, g, j, i);
        let h1_ty = d.bool_eq(rij, true_);
        let h1_fv = d.fresh_fvar();
        let h1 = d.kernel().fvar(h1_fv);
        let h2_ty = d.bool_eq(rji, true_);
        let h2_fv = d.fresh_fvar();
        let h2 = d.kernel().fvar(h2_fv);

        let li = blt(d, i, n);
        let lj = blt(d, j, n);
        let succ_i = d.succ(i);
        let succ_j = d.succ(j);
        let h_li = d.lemma(p.ble_eq_true_of_le, &[succ_i, n, hi]);
        let h_lj = d.lemma(p.ble_eq_true_of_le, &[succ_j, n, hj]);
        let h_range = d.const_app(p.graph_and_b_intro, &[li, lj, h_li, h_lj]);
        let h_both = d.const_app(p.graph_and_b_intro, &[rij, rji, h1, h2]);
        let ne_ij = ne_b(d, &p, i, j);
        let h_ne = ne_b_congr(d, &p, beq_ij, false_, hne);
        let both = and_b(d, &p, rij, rji);
        let h_edge = d.const_app(p.graph_and_b_intro, &[ne_ij, both, h_ne, h_both]);
        let range = and_b(d, &p, li, lj);
        let edge = and_b(d, &p, ne_ij, both);
        let proof = d.const_app(p.graph_and_b_intro, &[range, edge, h_range, h_edge]);

        let adj = adj_b(d, &p, g, i, j);
        let concl = d.bool_eq(adj, true_);
        let ty = {
            let s8 = d.arrow(h2_ty, concl);
            let s7 = d.arrow(h1_ty, s8);
            let s6 = d.arrow(hne_ty, s7);
            let s5 = d.arrow(hj_ty, s6);
            let s4 = d.arrow(hi_ty, s5);
            let s3 = d.pi_fv(j_fv, nat, s4);
            let s2 = d.pi_fv(i_fv, nat, s3);
            d.pi_fv(g_fv, gr, s2)
        };
        let value = {
            let s8 = d.lam_fv(h2_fv, h2_ty, proof);
            let s7 = d.lam_fv(h1_fv, h1_ty, s8);
            let s6 = d.lam_fv(hne_fv, hne_ty, s7);
            let s5 = d.lam_fv(hj_fv, hj_ty, s6);
            let s4 = d.lam_fv(hi_fv, hi_ty, s5);
            let s3 = d.lam_fv(j_fv, nat, s4);
            let s2 = d.lam_fv(i_fv, nat, s3);
            d.lam_fv(g_fv, gr, s2)
        };
        d.declare_theorem(p.graph_adj_b_of_rel, ty, value)?;
    }

    Ok(())
}

// ---------------------------------------------------------------------------
// Neighbourhoods and degrees, over `Nat.Finset`.
// ---------------------------------------------------------------------------

fn declare_neighbourhood_laws(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let gr = graph_ty(d, &p);

    // memB_neighbors : ∀ g v i, Eq Bool (Finset.memB (neighbors g v) i) (adjB g v i)
    {
        let g_fv = d.fresh_fvar();
        let g = d.kernel().fvar(g_fv);
        let v_fv = d.fresh_fvar();
        let v = d.kernel().fvar(v_fv);
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let true_ = d.bool_true();
        let false_ = d.bool_false();
        let n = g_order(d, &p, g);
        let nb = d.const_app(p.graph_neighbors, &[g, v]);
        let mem = d.const_app(p.finset_mem_b, &[nb, i]);
        let adj = adj_b(d, &p, g, v, i);
        let concl = d.bool_eq(mem, adj);

        let succ_i = d.succ(i);
        let decide = d.ble(succ_i, n);
        let dichotomy = super::ops::bool_true_or_false(d, &p, decide);
        let is_true = d.bool_eq(decide, true_);
        let is_false = d.bool_eq(decide, false_);
        let on_true = {
            let ht_fv = d.fresh_fvar();
            let ht = d.kernel().fvar(ht_fv);
            let hlt = d.lemma(p.le_of_ble_eq_true, &[succ_i, n, ht]);
            // `bound (neighbors g v)` is `order g` by ι, and `pred` is `adjB g v`.
            let body = d.lemma(p.finset_mem_b_of_lt, &[nb, i, hlt]);
            d.lam_fv(ht_fv, is_true, body)
        };
        let on_false = {
            let hf_fv = d.fresh_fvar();
            let hf = d.kernel().fvar(hf_fv);
            let hgt = d.lemma(p.lt_of_ble_eq_false, &[succ_i, n, hf]);
            let hle = d.lemma(p.le_of_succ_le_succ, &[n, i, hgt]);
            let h_mem = d.lemma(p.finset_mem_b_of_bound_le, &[nb, i, hle]);
            let h_sym = d.const_app(p.graph_adj_b_symm, &[g, v, i]);
            let adj_flipped = adj_b(d, &p, g, i, v);
            let h_zero = d.const_app(p.graph_adj_b_of_order_le, &[g, i, v, hle]);
            let h_adj = d.bool_trans(adj, adj_flipped, false_, h_sym, h_zero);
            let h_adj_back = d.bool_symm(adj, false_, h_adj);
            let body = d.bool_trans(mem, false_, adj, h_mem, h_adj_back);
            d.lam_fv(hf_fv, is_false, body)
        };
        let proof = d.const_app(
            p.logic.or_elim,
            &[is_true, is_false, concl, dichotomy, on_true, on_false],
        );

        let ty = {
            let s3 = d.pi_fv(i_fv, nat, concl);
            let s2 = d.pi_fv(v_fv, nat, s3);
            d.pi_fv(g_fv, gr, s2)
        };
        let value = {
            let s3 = d.lam_fv(i_fv, nat, proof);
            let s2 = d.lam_fv(v_fv, nat, s3);
            d.lam_fv(g_fv, gr, s2)
        };
        d.declare_theorem(p.graph_mem_b_neighbors, ty, value)?;
    }

    // degree_le_order : ∀ g v, Le (degree g v) (order g)
    {
        let g_fv = d.fresh_fvar();
        let g = d.kernel().fvar(g_fv);
        let v_fv = d.fresh_fvar();
        let v = d.kernel().fvar(v_fv);
        let n = g_order(d, &p, g);
        let deg = d.const_app(p.graph_degree, &[g, v]);
        let concl = d.le(deg, n);
        // `degree g v` is `countRange (memB (neighbors g v)) (order g)` by δι.
        // It is NOT `countRange (adjB g v) (order g)`: `memB` truncates, so the
        // two predicates agree pointwise but are not the same FUNCTION, and
        // this kernel has no `funext`.
        let nb = d.const_app(p.graph_neighbors, &[g, v]);
        let mem_fn = d.const_app(p.finset_mem_b, &[nb]);
        let proof = d.const_app(p.count_range_le, &[mem_fn, n]);
        let ty = {
            let s2 = d.pi_fv(v_fv, nat, concl);
            d.pi_fv(g_fv, gr, s2)
        };
        let value = {
            let s2 = d.lam_fv(v_fv, nat, proof);
            d.lam_fv(g_fv, gr, s2)
        };
        d.declare_theorem(p.graph_degree_le_order, ty, value)?;
    }

    Ok(())
}

// ---------------------------------------------------------------------------
// Entry point.
// ---------------------------------------------------------------------------

/// Declare `Nat.Graph`, its `Bool` algebra, `adjB` and its laws, and
/// neighbourhoods and degrees over `Nat.Finset`.
///
/// # Errors
///
/// Returns the kernel's rejection if any declaration fails to type-check.
pub(super) fn declare_graph_all(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    declare_carrier(d, p)?;
    declare_bool_algebra(d, p)?;
    declare_bool_laws(d, p)?;
    declare_operations(d, p)?;
    declare_adjacency_laws(d, p)?;
    declare_neighbourhood_laws(d, p)?;
    Ok(())
}
