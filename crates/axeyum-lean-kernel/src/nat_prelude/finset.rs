//! `Nat.Finset` — a computed finite-set carrier: a decidable membership
//! predicate together with a bound.
//!
//! # What this is for
//!
//! Mathlib's `Finset` is a quotient of lists by permutation and needs
//! `Quot.sound`, which this kernel refuses on purpose. ADR-1520 answered the
//! same problem for multisets by *computing* the carrier instead of extracting
//! it: `Nat.Multiset` is a multiplicity function plus a bound, and that was
//! enough to state and prove uniqueness of prime factorization. ADR-1577 does
//! the same for sets, for the two things `Finset` gives Mathlib that this
//! prelude lacked:
//!
//! 1. **Sums over an arbitrary finite set.** Every sum here was `Nat.sumRange`
//!    over `[0,n)` or an ad hoc `Nat.sumRangeIf` at a spelled-out predicate;
//!    there was no object "the sum of `f` over `{i < n | p i}`".
//! 2. **Cardinality arguments** — inclusion–exclusion, monotonicity under
//!    inclusion, pigeonhole — over a set rather than over a loose
//!    `(predicate, bound)` pair that every call site re-spells.
//!
//! ```text
//! inductive Nat.Finset : Type
//!   | mk : (Nat → Bool) → Nat → Nat.Finset
//!
//! Nat.Finset.memB s i := if i < bound s then pred s i else false
//! Nat.Finset.card s   := countRange (memB s) (bound s)
//! Nat.Finset.sum  s f := sumRangeIf (memB s) f (bound s)
//! ```
//!
//! No quotient, no `propext`, no `List`. Order is never represented, so there
//! is nothing to quotient by — the same reason ADR-1520 gives, and the reason
//! the axiom footprint of everything below is `[]`.
//!
//! # The three design choices, each a decision rather than a detail
//!
//! **1. `memB` truncates inside its own definition**, exactly as
//! `Nat.Multiset.count` does. The alternative is a well-formedness premise
//! ("this predicate is false above this bound") on every downstream statement
//! and a proof obligation on every `mk`. Truncating instead makes
//! [`declare_membership_laws`]'s `memB_of_bound_le` a theorem about EVERY
//! `Nat.Finset` with no side condition, so `mk` applies to any predicate at any
//! bound. The cost is that `pred` is not observable at or above the bound, and
//! that is the correct semantics rather than a compromise: two sets that agree
//! below their bounds and disagree above them ARE the same set.
//!
//! **2. `card` folds `memB`, not `pred`.** `countRange` only reads its
//! predicate below the fold's own bound, so at the set's own bound the two
//! agree; but `union`'s bound is LARGER than either operand's, and there
//! `countRange (pred s)` would read `s`'s raw predicate outside `s`. Folding
//! `memB` is what makes `card (union s t)` mean what it says.
//!
//! **3. `union`/`inter` take the SUM of the two bounds, not the maximum** —
//! ADR-1520's choice for `Nat.Multiset.add`, for a sharper reason here.
//! `Nat.max` lives in the `Max` namespace and its comparison lemmas are stated
//! there, but the decisive point is that `Nat.countRange_split` is stated at
//! `countRange f (add m j)` — so with a SUM bound it applies LITERALLY, with no
//! `Le`-to-`Exists` step and no case analysis on which bound is larger. That is
//! [`declare_card_eq_count_range_add`], the workhorse every two-set law comes
//! back through: fold both sets over the common bound `bound s + bound t`, then
//! collapse each side to its own `card`.
//!
//! # What this carrier deliberately does NOT provide
//!
//! - **No `List` and no permutation quotient.** As above.
//! - **No `Finset.image`.** Mathlib's needs decidable equality on an arbitrary
//!   type; here the element type is `Nat` and the image of a bounded set under
//!   a bounded map is expressible, but nothing needs it yet and it is not
//!   declared.
//! - **No polymorphism: `Nat` only.** `Nat.Multiset` made the same restriction
//!   for the same reason — this prelude's fold machinery
//!   (`countRange`/`sumRange`/`sumRangeIf`) is `Nat`-indexed throughout.
//! - **No extensional equality of sets.** [`declare_decisions`]'s `beq` is a
//!   `Bool`-valued bounded loop. Two sets with the same members but different
//!   stored predicates above their bounds are NOT `Eq` at type `Nat.Finset`,
//!   and nothing here pretends otherwise; every statement that would want set
//!   equality is stated pointwise or through `beq` instead.
//!
//! # What is reused rather than rebuilt
//!
//! Almost all of the algebra already existed at the level of bare predicates,
//! and this module is deliberately thin on top of it: `Nat.countRange` and its
//! lemma family (`totient.rs`, `count_range_bij.rs`, `count_range_permute.rs`),
//! `Nat.setUnion`/`setInter`/`setDiff`/`setCompl` and `Nat.Subset` with
//! `Nat.countRange_union_add_inter` and `Nat.countRange_le_of_subset`
//! (`finite_set.rs`), and `Nat.sumRangeIf` with `sumRangeIf_congr_lt`
//! (`subset_sum.rs`).
//!
//! # Every definition here is evaluated
//!
//! The kernel cannot tell a `Definition` is wrong — a `card` that computed the
//! wrong number would have the right type, an empty axiom footprint, and would
//! pass every sweep in this repository. `finset_tests.rs` reduces each
//! operation to a numeral at tiny discriminating arguments and pairs every
//! positive with the specific wrong formula it rules out.

use super::NatPrelude;
use super::ops::{NatDev, NatOps};
use crate::BinderInfo;
use crate::KernelError;
use crate::env::Declaration;
use crate::env::ReducibilityHint;
use crate::expr::ExprId;

// ---------------------------------------------------------------------------
// Term builders.
// ---------------------------------------------------------------------------

/// The carrier constant `Nat.Finset`.
fn finset_ty(d: &mut NatDev<'_>, p: &NatPrelude) -> ExprId {
    d.kernel().const_(p.finset, vec![])
}

/// `Nat.Finset.mk f b`.
fn mk_finset(d: &mut NatDev<'_>, p: &NatPrelude, f: ExprId, b: ExprId) -> ExprId {
    d.const_app(p.finset_mk, &[f, b])
}

/// `Nat.Finset.pred s`, the stored predicate (NOT truncated at the bound).
fn fs_pred(d: &mut NatDev<'_>, p: &NatPrelude, s: ExprId) -> ExprId {
    d.const_app(p.finset_pred, &[s])
}

/// `Nat.Finset.bound s`.
fn fs_bound(d: &mut NatDev<'_>, p: &NatPrelude, s: ExprId) -> ExprId {
    d.const_app(p.finset_bound, &[s])
}

/// `Nat.Finset.memB s : Nat → Bool`, the membership function of `s`.
fn fs_mem_fn(d: &mut NatDev<'_>, p: &NatPrelude, s: ExprId) -> ExprId {
    d.const_app(p.finset_mem_b, &[s])
}

/// `Nat.Finset.memB s i`.
fn fs_mem(d: &mut NatDev<'_>, p: &NatPrelude, s: ExprId, i: ExprId) -> ExprId {
    d.const_app(p.finset_mem_b, &[s, i])
}

/// `Nat.Finset.card s`.
fn fs_card(d: &mut NatDev<'_>, p: &NatPrelude, s: ExprId) -> ExprId {
    d.const_app(p.finset_card, &[s])
}

/// `Nat.countRange f n` — this prelude's per-file convention is a private copy
/// of this one-liner rather than an exported helper (`totient.rs` and
/// `finite_set.rs` each carry their own).
fn count_range(d: &mut NatDev<'_>, p: &NatPrelude, f: ExprId, n: ExprId) -> ExprId {
    d.const_app(p.count_range, &[f, n])
}

/// `Nat.sumRangeIf q f n`.
fn sum_range_if(d: &mut NatDev<'_>, p: &NatPrelude, q: ExprId, f: ExprId, n: ExprId) -> ExprId {
    d.const_app(p.sum_range_if, &[q, f, n])
}

/// `Nat.setUnion f g : Nat → Bool` (the two-argument partial application).
fn set_union(d: &mut NatDev<'_>, p: &NatPrelude, f: ExprId, g: ExprId) -> ExprId {
    d.const_app(p.set_union, &[f, g])
}

/// `Nat.setInter f g : Nat → Bool`.
fn set_inter(d: &mut NatDev<'_>, p: &NatPrelude, f: ExprId, g: ExprId) -> ExprId {
    d.const_app(p.set_inter, &[f, g])
}

/// `Nat.setDiff f g : Nat → Bool`.
fn set_diff(d: &mut NatDev<'_>, p: &NatPrelude, f: ExprId, g: ExprId) -> ExprId {
    d.const_app(p.set_diff, &[f, g])
}

/// `Bool.rec (fun _ => Bool) on_false on_true condition` — computational
/// `if condition then on_true else on_false` at `Bool`. The `Bool`-codomain
/// sibling of [`NatOps::bool_select_nat`]; `finite_set.rs` and `multiset.rs`
/// each carry their own copy under this prelude's per-file convention.
fn bool_select_bool(
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

/// `heq : Eq Bool cond true ⊢ Eq Bool (bool_select_bool cond a b) a`.
fn select_bool_true(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    cond: ExprId,
    a: ExprId,
    b: ExprId,
    heq: ExprId,
) -> ExprId {
    let p = *p;
    let true_val = d.bool_true();
    let back = d.bool_symm(cond, true_val, heq);
    let motive = d.bool_eq_motive(true_val, &|d, value| {
        let sel = bool_select_bool(d, &p, value, a, b);
        d.bool_eq(sel, a)
    });
    let refl_case = d.bool_refl(a);
    d.bool_transport(true_val, motive, refl_case, cond, back)
}

/// `heq : Eq Bool cond false ⊢ Eq Bool (bool_select_bool cond a b) b`.
fn select_bool_false(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    cond: ExprId,
    a: ExprId,
    b: ExprId,
    heq: ExprId,
) -> ExprId {
    let p = *p;
    let false_val = d.bool_false();
    let back = d.bool_symm(cond, false_val, heq);
    let motive = d.bool_eq_motive(false_val, &|d, value| {
        let sel = bool_select_bool(d, &p, value, a, b);
        d.bool_eq(sel, b)
    });
    let refl_case = d.bool_refl(b);
    d.bool_transport(false_val, motive, refl_case, cond, back)
}

/// The predicate type `Nat → Bool`.
fn pred_ty(d: &mut NatDev<'_>) -> ExprId {
    let nat = d.nat_ty();
    let bool_ty = d.bool_ty();
    d.arrow(nat, bool_ty)
}

/// The summand type `Nat → Nat`.
fn fun_ty(d: &mut NatDev<'_>) -> ExprId {
    let nat = d.nat_ty();
    d.arrow(nat, nat)
}

// ---------------------------------------------------------------------------
// The carrier and its projections.
// ---------------------------------------------------------------------------

/// `Nat.Finset`, `Nat.Finset.mk`, the two `Finset.rec` projections, and the
/// truncated `memB`.
fn declare_carrier(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let anon = d.anon_name();
    let one = d.level_one();
    let type0 = d.kernel().sort(one);
    let pty = pred_ty(d);

    {
        let mk_ty = {
            let concl = d.kernel().const_(p.finset, vec![]);
            let inner = d.arrow(nat, concl);
            d.arrow(pty, inner)
        };
        d.kernel()
            .add_inductive(p.finset, &[], 0, type0, &[(p.finset_mk, mk_ty)])?;
    }

    let fs = finset_ty(d, &p);

    // pred : Finset -> Nat -> Bool
    //      := fun s => Finset.rec.{1} (fun _ => Nat -> Bool) (fun f _ => f) s
    {
        let motive = d.kernel().lam(anon, fs, pty, BinderInfo::Default);
        let minor = {
            let f_fv = d.fresh_fvar();
            let f = d.kernel().fvar(f_fv);
            let b_fv = d.fresh_fvar();
            let inner = d.lam_fv(b_fv, nat, f);
            d.lam_fv(f_fv, pty, inner)
        };
        let s_fv = d.fresh_fvar();
        let s = d.kernel().fvar(s_fv);
        let rec = d.kernel().const_(p.finset_rec, vec![one]);
        let body = d.apply(rec, &[motive, minor, s]);
        let value = d.lam_fv(s_fv, fs, body);
        let ty = d.arrow(fs, pty);
        d.kernel().add_declaration(Declaration::Definition {
            name: p.finset_pred,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(1),
        })?;
    }

    // bound : Finset -> Nat
    //       := fun s => Finset.rec.{1} (fun _ => Nat) (fun _ b => b) s
    {
        let motive = d.kernel().lam(anon, fs, nat, BinderInfo::Default);
        let minor = {
            let f_fv = d.fresh_fvar();
            let b_fv = d.fresh_fvar();
            let b = d.kernel().fvar(b_fv);
            let inner = d.lam_fv(b_fv, nat, b);
            d.lam_fv(f_fv, pty, inner)
        };
        let s_fv = d.fresh_fvar();
        let s = d.kernel().fvar(s_fv);
        let rec = d.kernel().const_(p.finset_rec, vec![one]);
        let body = d.apply(rec, &[motive, minor, s]);
        let value = d.lam_fv(s_fv, fs, body);
        let ty = d.arrow(fs, nat);
        d.kernel().add_declaration(Declaration::Definition {
            name: p.finset_bound,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(1),
        })?;
    }

    // memB : Finset -> Nat -> Bool
    //      := fun s i => if ble (succ i) (bound s) then pred s i else false
    {
        let s_fv = d.fresh_fvar();
        let s = d.kernel().fvar(s_fv);
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let succ_i = d.succ(i);
        let b = fs_bound(d, &p, s);
        let cond = d.ble(succ_i, b);
        let raw = fs_pred(d, &p, s);
        let raw_at = d.apply(raw, &[i]);
        let false_ = d.bool_false();
        let body = bool_select_bool(d, &p, cond, raw_at, false_);
        let value = {
            let inner = d.lam_fv(i_fv, nat, body);
            d.lam_fv(s_fv, fs, inner)
        };
        let ty = {
            let bool_ty = d.bool_ty();
            let inner = d.arrow(nat, bool_ty);
            d.arrow(fs, inner)
        };
        d.kernel().add_declaration(Declaration::Definition {
            name: p.finset_mem_b,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(2),
        })?;
    }

    Ok(())
}

/// `card`, `sum`, and the six constructions over the carrier.
fn declare_operations(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let fs = finset_ty(d, &p);
    let pty = pred_ty(d);
    let fty = fun_ty(d);

    // card : Finset -> Nat := fun s => countRange (memB s) (bound s)
    {
        let s_fv = d.fresh_fvar();
        let s = d.kernel().fvar(s_fv);
        let m = fs_mem_fn(d, &p, s);
        let b = fs_bound(d, &p, s);
        let body = count_range(d, &p, m, b);
        let value = d.lam_fv(s_fv, fs, body);
        let ty = d.arrow(fs, nat);
        d.kernel().add_declaration(Declaration::Definition {
            name: p.finset_card,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(3),
        })?;
    }

    // sum : Finset -> (Nat -> Nat) -> Nat
    //     := fun s f => sumRangeIf (memB s) f (bound s)
    {
        let s_fv = d.fresh_fvar();
        let s = d.kernel().fvar(s_fv);
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let m = fs_mem_fn(d, &p, s);
        let b = fs_bound(d, &p, s);
        let body = sum_range_if(d, &p, m, f, b);
        let value = {
            let inner = d.lam_fv(f_fv, fty, body);
            d.lam_fv(s_fv, fs, inner)
        };
        let ty = {
            let inner = d.arrow(fty, nat);
            d.arrow(fs, inner)
        };
        d.kernel().add_declaration(Declaration::Definition {
            name: p.finset_sum,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(3),
        })?;
    }

    // Binary set operations. `union`/`inter` share the SUM bound; `sdiff` keeps
    // the left bound, since the difference cannot reach outside `s`.
    for (name, combine, sum_bound) in [
        (
            p.finset_union,
            set_union as fn(&mut NatDev<'_>, &NatPrelude, ExprId, ExprId) -> ExprId,
            true,
        ),
        (
            p.finset_inter,
            set_inter as fn(&mut NatDev<'_>, &NatPrelude, ExprId, ExprId) -> ExprId,
            true,
        ),
        (
            p.finset_sdiff,
            set_diff as fn(&mut NatDev<'_>, &NatPrelude, ExprId, ExprId) -> ExprId,
            false,
        ),
    ] {
        let s_fv = d.fresh_fvar();
        let s = d.kernel().fvar(s_fv);
        let t_fv = d.fresh_fvar();
        let t = d.kernel().fvar(t_fv);
        let ms = fs_mem_fn(d, &p, s);
        let mt = fs_mem_fn(d, &p, t);
        let combined = combine(d, &p, ms, mt);
        let bs = fs_bound(d, &p, s);
        let bound = if sum_bound {
            let bt = fs_bound(d, &p, t);
            d.add(bs, bt)
        } else {
            bs
        };
        let built = mk_finset(d, &p, combined, bound);
        let value = {
            let inner = d.lam_fv(t_fv, fs, built);
            d.lam_fv(s_fv, fs, inner)
        };
        let ty = {
            let inner = d.arrow(fs, fs);
            d.arrow(fs, inner)
        };
        d.kernel().add_declaration(Declaration::Definition {
            name,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(4),
        })?;
    }

    // filter : (Nat -> Bool) -> Finset -> Finset
    //        := fun q s => mk (setInter (memB s) q) (bound s)
    {
        let q_fv = d.fresh_fvar();
        let q = d.kernel().fvar(q_fv);
        let s_fv = d.fresh_fvar();
        let s = d.kernel().fvar(s_fv);
        let ms = fs_mem_fn(d, &p, s);
        let combined = set_inter(d, &p, ms, q);
        let b = fs_bound(d, &p, s);
        let built = mk_finset(d, &p, combined, b);
        let value = {
            let inner = d.lam_fv(s_fv, fs, built);
            d.lam_fv(q_fv, pty, inner)
        };
        let ty = {
            let inner = d.arrow(fs, fs);
            d.arrow(pty, inner)
        };
        d.kernel().add_declaration(Declaration::Definition {
            name: p.finset_filter,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(4),
        })?;
    }

    // range : Nat -> Finset := fun n => mk (fun _ => true) n
    {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let always = {
            let k_fv = d.fresh_fvar();
            let t = d.bool_true();
            d.lam_fv(k_fv, nat, t)
        };
        let built = mk_finset(d, &p, always, n);
        let value = d.lam_fv(n_fv, nat, built);
        let ty = d.arrow(nat, fs);
        d.kernel().add_declaration(Declaration::Definition {
            name: p.finset_range,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(4),
        })?;
    }

    // singleton : Nat -> Finset := fun a => mk (fun k => beq k a) (succ a)
    {
        let a_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let q = {
            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let body = d.beq(k, a);
            d.lam_fv(k_fv, nat, body)
        };
        let succ_a = d.succ(a);
        let built = mk_finset(d, &p, q, succ_a);
        let value = d.lam_fv(a_fv, nat, built);
        let ty = d.arrow(nat, fs);
        d.kernel().add_declaration(Declaration::Definition {
            name: p.finset_singleton,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(4),
        })?;
    }

    Ok(())
}

/// `allBelow`, `subsetB` and `beq` — the three `Bool`-valued decisions.
fn declare_decisions(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let bool_ty = d.bool_ty();
    let fs = finset_ty(d, &p);
    let pty = pred_ty(d);
    let anon = d.anon_name();
    let one = d.level_one();

    // allBelow : (Nat -> Bool) -> Nat -> Bool
    //          := fun f n => Nat.rec.{1} (fun _ => Bool) true
    //                          (fun k ih => if f k then ih else false) n
    {
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let motive = d.kernel().lam(anon, nat, bool_ty, BinderInfo::Default);
        let base = d.bool_true();
        let step = {
            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let ih_fv = d.fresh_fvar();
            let ih = d.kernel().fvar(ih_fv);
            let fk = d.apply(f, &[k]);
            let false_ = d.bool_false();
            let body = bool_select_bool(d, &p, fk, ih, false_);
            let inner = d.lam_fv(ih_fv, bool_ty, body);
            d.lam_fv(k_fv, nat, inner)
        };
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let rec = d.kernel().const_(p.rec, vec![one]);
        let body = d.apply(rec, &[motive, base, step, n]);
        let value = {
            let inner = d.lam_fv(n_fv, nat, body);
            d.lam_fv(f_fv, pty, inner)
        };
        let ty = {
            let inner = d.arrow(nat, bool_ty);
            d.arrow(pty, inner)
        };
        d.kernel().add_declaration(Declaration::Definition {
            name: p.finset_all_below,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(3),
        })?;
    }

    // subsetB : Finset -> Finset -> Bool
    //         := fun s t => allBelow (fun i => if memB s i then memB t i else true)
    //                                (bound s)
    {
        let s_fv = d.fresh_fvar();
        let s = d.kernel().fvar(s_fv);
        let t_fv = d.fresh_fvar();
        let t = d.kernel().fvar(t_fv);
        let implication = {
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let msi = fs_mem(d, &p, s, i);
            let mti = fs_mem(d, &p, t, i);
            let true_ = d.bool_true();
            let body = bool_select_bool(d, &p, msi, mti, true_);
            d.lam_fv(i_fv, nat, body)
        };
        let bs = fs_bound(d, &p, s);
        let body = d.const_app(p.finset_all_below, &[implication, bs]);
        let value = {
            let inner = d.lam_fv(t_fv, fs, body);
            d.lam_fv(s_fv, fs, inner)
        };
        let ty = {
            let inner = d.arrow(fs, bool_ty);
            d.arrow(fs, inner)
        };
        d.kernel().add_declaration(Declaration::Definition {
            name: p.finset_subset_b,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(4),
        })?;
    }

    // beq : Finset -> Finset -> Bool
    //     := fun s t => allBelow (fun i => if memB s i then memB t i
    //                                      else (if memB t i then false else true))
    //                            (bound s + bound t)
    {
        let s_fv = d.fresh_fvar();
        let s = d.kernel().fvar(s_fv);
        let t_fv = d.fresh_fvar();
        let t = d.kernel().fvar(t_fv);
        let agreement = {
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let msi = fs_mem(d, &p, s, i);
            let mti = fs_mem(d, &p, t, i);
            let true_ = d.bool_true();
            let false_ = d.bool_false();
            let neither = bool_select_bool(d, &p, mti, false_, true_);
            let body = bool_select_bool(d, &p, msi, mti, neither);
            d.lam_fv(i_fv, nat, body)
        };
        let width = {
            let bs = fs_bound(d, &p, s);
            let bt = fs_bound(d, &p, t);
            d.add(bs, bt)
        };
        let body = d.const_app(p.finset_all_below, &[agreement, width]);
        let value = {
            let inner = d.lam_fv(t_fv, fs, body);
            d.lam_fv(s_fv, fs, inner)
        };
        let ty = {
            let inner = d.arrow(fs, bool_ty);
            d.arrow(fs, inner)
        };
        d.kernel().add_declaration(Declaration::Definition {
            name: p.finset_beq,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(4),
        })?;
    }

    Ok(())
}

// ---------------------------------------------------------------------------
// Membership laws.
// ---------------------------------------------------------------------------

/// `Nat.Finset.memB_of_lt : ∀ s i, Lt i (bound s) → Eq Bool (memB s i) (pred s i)`
/// and
/// `Nat.Finset.memB_of_bound_le : ∀ s i, Le (bound s) i → Eq Bool (memB s i) false`.
///
/// The second is the one design choice 1 buys: it holds of EVERY `Nat.Finset`,
/// with no well-formedness premise, because `memB` truncates in its own
/// definition.
fn declare_membership_laws(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let fs = finset_ty(d, &p);

    // memB_of_lt
    {
        let s_fv = d.fresh_fvar();
        let s = d.kernel().fvar(s_fv);
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let b = fs_bound(d, &p, s);
        let hyp_ty = d.lt(i, b);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);

        let succ_i = d.succ(i);
        let cond = d.ble(succ_i, b);
        // `Lt i b` is `Le (succ i) b` definitionally, so `ble_eq_true_of_le`
        // applies with no bridging step.
        let hb = d.lemma(p.ble_eq_true_of_le, &[succ_i, b, h]);
        let raw = fs_pred(d, &p, s);
        let raw_at = d.apply(raw, &[i]);
        let false_ = d.bool_false();
        let proof = select_bool_true(d, &p, cond, raw_at, false_, hb);

        let concl = {
            let lhs = fs_mem(d, &p, s, i);
            d.bool_eq(lhs, raw_at)
        };
        let ty = {
            let with_h = d.arrow(hyp_ty, concl);
            let with_i = d.pi_fv(i_fv, nat, with_h);
            d.pi_fv(s_fv, fs, with_i)
        };
        let value = {
            let with_h = d.lam_fv(h_fv, hyp_ty, proof);
            let with_i = d.lam_fv(i_fv, nat, with_h);
            d.lam_fv(s_fv, fs, with_i)
        };
        d.declare_theorem(p.finset_mem_b_of_lt, ty, value)?;
    }

    // memB_of_bound_le
    {
        let s_fv = d.fresh_fvar();
        let s = d.kernel().fvar(s_fv);
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let b = fs_bound(d, &p, s);
        let hyp_ty = d.le(b, i);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);

        let succ_i = d.succ(i);
        // `Le (bound s) i` gives `Le (succ (bound s)) (succ i)`, which IS
        // `Lt (bound s) (succ i)` — exactly `ble_eq_false_of_lt`'s hypothesis
        // at `(succ i, bound s)`.
        let hlt = d.lemma(p.succ_le_succ, &[b, i, h]);
        let cond = d.ble(succ_i, b);
        let hb = d.lemma(p.ble_eq_false_of_lt, &[succ_i, b, hlt]);
        let raw = fs_pred(d, &p, s);
        let raw_at = d.apply(raw, &[i]);
        let false_ = d.bool_false();
        let proof = select_bool_false(d, &p, cond, raw_at, false_, hb);

        let concl = {
            let lhs = fs_mem(d, &p, s, i);
            let f = d.bool_false();
            d.bool_eq(lhs, f)
        };
        let ty = {
            let with_h = d.arrow(hyp_ty, concl);
            let with_i = d.pi_fv(i_fv, nat, with_h);
            d.pi_fv(s_fv, fs, with_i)
        };
        let value = {
            let with_h = d.lam_fv(h_fv, hyp_ty, proof);
            let with_i = d.lam_fv(i_fv, nat, with_h);
            d.lam_fv(s_fv, fs, with_i)
        };
        d.declare_theorem(p.finset_mem_b_of_bound_le, ty, value)?;
    }

    Ok(())
}

// ---------------------------------------------------------------------------
// The workhorse: counting over a longer range than the set's own bound.
// ---------------------------------------------------------------------------

/// `Nat.Finset.card_eq_countRange_add : ∀ s j,
/// Eq Nat (countRange (memB s) (add (bound s) j)) (card s)`.
///
/// `Nat.countRange_split` peels `[0, bound s)` off the front; the tail counts
/// `memB s` at indices `bound s + k`, every one of which is `false` by
/// `memB_of_bound_le`, so `countRange_eq_zero_of_all_false` collapses it and
/// `add_zero` closes. This is the ONLY place the sum-bound choice is cashed in,
/// and everything downstream reaches a common bound through it.
fn declare_card_eq_count_range_add(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let fs = finset_ty(d, &p);

    let s_fv = d.fresh_fvar();
    let s = d.kernel().fvar(s_fv);
    let j_fv = d.fresh_fvar();
    let j = d.kernel().fvar(j_fv);

    let m = fs_mem_fn(d, &p, s);
    let bs = fs_bound(d, &p, s);
    let total = d.add(bs, j);

    let split = d.lemma(p.count_range_split, &[m, bs, j]);
    // The tail predicate `fun k => memB s (bound s + k)`, spelled exactly as
    // `countRange_split` states it.
    let tail_pred = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let shifted = d.add(bs, k);
        let body = fs_mem(d, &p, s, shifted);
        d.lam_fv(k_fv, nat, body)
    };
    let tail_zero = {
        let all_false = {
            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let shifted = d.add(bs, k);
            let hk_fv = d.fresh_fvar();
            let hk_ty = d.lt(k, j);
            let bound_le = d.lemma(p.le_add_right, &[bs, k]);
            let body = d.lemma(p.finset_mem_b_of_bound_le, &[s, shifted, bound_le]);
            let with_hk = d.lam_fv(hk_fv, hk_ty, body);
            d.lam_fv(k_fv, nat, with_hk)
        };
        d.lemma(
            p.count_range_eq_zero_of_all_false,
            &[tail_pred, j, all_false],
        )
    };

    let head = count_range(d, &p, m, bs);
    let tail = count_range(d, &p, tail_pred, j);
    let zero = d.zero();

    let start = count_range(d, &p, m, total);
    let mid = d.add(head, tail);
    let with_zero = d.add(head, zero);
    let collapse = d.congr(tail, zero, tail_zero, &|d, x| d.add(head, x));
    let close = d.lemma(p.add_zero, &[head]);
    let (_, proof) = d.chain(start, &[(mid, split), (with_zero, collapse), (head, close)]);

    let concl = {
        let card = fs_card(d, &p, s);
        d.eq(start, card)
    };
    let ty = {
        let with_j = d.pi_fv(j_fv, nat, concl);
        d.pi_fv(s_fv, fs, with_j)
    };
    let value = {
        let with_j = d.lam_fv(j_fv, nat, proof);
        d.lam_fv(s_fv, fs, with_j)
    };
    d.declare_theorem(p.finset_card_eq_count_range_add, ty, value)?;
    Ok(())
}

// ---------------------------------------------------------------------------
// Inclusion–exclusion.
// ---------------------------------------------------------------------------

/// `Nat.Finset.card_union_add_card_inter : ∀ s t,
/// Eq Nat (add (card (union s t)) (card (inter s t))) (add (card s) (card t))`.
///
/// Stated ADDITIVELY: `Nat.sub` is truncated, so the familiar subtractive form
/// would need a `≤` side condition this one does not. `finite_set.rs`'s
/// `countRange_union_add_inter` makes the same choice, and this is its
/// carrier-level lift — the whole content added here is that both sets are
/// folded over ONE bound and each side comes back to its own `card`.
fn declare_card_union_add_card_inter(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let fs = finset_ty(d, &p);

    let s_fv = d.fresh_fvar();
    let s = d.kernel().fvar(s_fv);
    let t_fv = d.fresh_fvar();
    let t = d.kernel().fvar(t_fv);

    let ms = fs_mem_fn(d, &p, s);
    let mt = fs_mem_fn(d, &p, t);
    let bs = fs_bound(d, &p, s);
    let bt = fs_bound(d, &p, t);
    let width = d.add(bs, bt);

    let union = d.const_app(p.finset_union, &[s, t]);
    let inter = d.const_app(p.finset_inter, &[s, t]);
    let m_union = fs_mem_fn(d, &p, union);
    let m_inter = fs_mem_fn(d, &p, inter);
    let u_pred = set_union(d, &p, ms, mt);
    let i_pred = set_inter(d, &p, ms, mt);

    // Below the common bound, `memB (union s t)` IS `setUnion (memB s) (memB t)`:
    // `bound (union s t)` and `pred (union s t)` reduce to `width` and `u_pred`
    // by iota, so `memB_of_lt` applies with no transport at all.
    let h_union = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let hi_fv = d.fresh_fvar();
        let hi_ty = d.lt(i, width);
        let hi = d.kernel().fvar(hi_fv);
        let step = d.lemma(p.finset_mem_b_of_lt, &[union, i, hi]);
        let with_hi = d.lam_fv(hi_fv, hi_ty, step);
        let pointwise = d.lam_fv(i_fv, nat, with_hi);
        d.lemma(p.count_range_congr_lt, &[m_union, u_pred, width, pointwise])
    };
    let h_inter = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let hi_fv = d.fresh_fvar();
        let hi_ty = d.lt(i, width);
        let hi = d.kernel().fvar(hi_fv);
        let step = d.lemma(p.finset_mem_b_of_lt, &[inter, i, hi]);
        let with_hi = d.lam_fv(hi_fv, hi_ty, step);
        let pointwise = d.lam_fv(i_fv, nat, with_hi);
        d.lemma(p.count_range_congr_lt, &[m_inter, i_pred, width, pointwise])
    };

    let inclusion_exclusion = d.lemma(p.count_range_union_add_inter, &[ms, mt, width]);

    // `countRange (memB s) (bs + bt) = card s` directly; the `t` side needs
    // `add_comm` first, because the workhorse peels the set's OWN bound off the
    // front of the sum.
    let h_card_s = d.lemma(p.finset_card_eq_count_range_add, &[s, bt]);
    let h_card_t = {
        let comm = d.lemma(p.add_comm, &[bs, bt]);
        let swapped = d.add(bt, bs);
        let move_bound = d.congr(width, swapped, comm, &|d, x| {
            let mt_inner = fs_mem_fn(d, &p, t);
            count_range(d, &p, mt_inner, x)
        });
        let collapse = d.lemma(p.finset_card_eq_count_range_add, &[t, bs]);
        let lhs = count_range(d, &p, mt, width);
        let midpoint = count_range(d, &p, mt, swapped);
        let card_t = fs_card(d, &p, t);
        d.trans(lhs, midpoint, card_t, move_bound, collapse)
    };

    let cr_union_memb = count_range(d, &p, m_union, width);
    let cr_inter_memb = count_range(d, &p, m_inter, width);
    let cr_union_pred = count_range(d, &p, u_pred, width);
    let cr_inter_pred = count_range(d, &p, i_pred, width);
    let cr_s = count_range(d, &p, ms, width);
    let cr_t = count_range(d, &p, mt, width);
    let card_s = fs_card(d, &p, s);
    let card_t = fs_card(d, &p, t);

    let start = d.add(cr_union_memb, cr_inter_memb);
    let after_union = d.add(cr_union_pred, cr_inter_memb);
    let after_inter = d.add(cr_union_pred, cr_inter_pred);
    let after_ie = d.add(cr_s, cr_t);
    let after_s = d.add(card_s, cr_t);
    let after_t = d.add(card_s, card_t);

    let step_union = d.congr(cr_union_memb, cr_union_pred, h_union, &|d, x| {
        d.add(x, cr_inter_memb)
    });
    let step_inter = d.congr(cr_inter_memb, cr_inter_pred, h_inter, &|d, x| {
        d.add(cr_union_pred, x)
    });
    let step_s = d.congr(cr_s, card_s, h_card_s, &|d, x| d.add(x, cr_t));
    let step_t = d.congr(cr_t, card_t, h_card_t, &|d, x| d.add(card_s, x));

    let (_, proof) = d.chain(
        start,
        &[
            (after_union, step_union),
            (after_inter, step_inter),
            (after_ie, inclusion_exclusion),
            (after_s, step_s),
            (after_t, step_t),
        ],
    );

    let concl = {
        let card_union = fs_card(d, &p, union);
        let card_inter = fs_card(d, &p, inter);
        let lhs = d.add(card_union, card_inter);
        d.eq(lhs, after_t)
    };
    let ty = {
        let with_t = d.pi_fv(t_fv, fs, concl);
        d.pi_fv(s_fv, fs, with_t)
    };
    let value = {
        let with_t = d.lam_fv(t_fv, fs, proof);
        d.lam_fv(s_fv, fs, with_t)
    };
    d.declare_theorem(p.finset_card_union_add_card_inter, ty, value)?;
    Ok(())
}

// ---------------------------------------------------------------------------
// `allBelow` and the reflection half.
// ---------------------------------------------------------------------------

/// `False.rec` into `target` from a proof of `False`.
fn from_false(d: &mut NatDev<'_>, p: &NatPrelude, false_proof: ExprId, target: ExprId) -> ExprId {
    let anon = d.anon_name();
    let false_ty = d.kernel().const_(p.logic.false_, vec![]);
    let motive = d.kernel().lam(anon, false_ty, target, BinderInfo::Default);
    let level_zero = d.kernel().level_zero();
    let rec = d.kernel().const_(p.logic.false_rec, vec![level_zero]);
    d.apply(rec, &[motive, false_proof])
}

/// Non-dependent `Or.rec` into a `Prop` goal.
#[allow(clippy::too_many_arguments)]
fn or_elim(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    left_ty: ExprId,
    right_ty: ExprId,
    goal: ExprId,
    left_case: ExprId,
    right_case: ExprId,
    or_proof: ExprId,
) -> ExprId {
    let anon = d.anon_name();
    let or_ty = d.const_app(p.logic.or, &[left_ty, right_ty]);
    let motive = d.kernel().lam(anon, or_ty, goal, BinderInfo::Default);
    let or_rec = d.kernel().const_(p.logic.or_rec, vec![]);
    d.apply(
        or_rec,
        &[left_ty, right_ty, motive, left_case, right_case, or_proof],
    )
}

/// `Nat.Finset.allBelow_of_all_true : ∀ f n,
/// (∀ i, Lt i n → Eq Bool (f i) true) → Eq Bool (allBelow f n) true`
/// and its converse
/// `Nat.Finset.allBelow_true_at : ∀ f n, Eq Bool (allBelow f n) true →
/// ∀ i, Lt i n → Eq Bool (f i) true`.
///
/// The REFLECTION direction (`allBelow_true_at`) is the one
/// `Nat.Multiset.eqBelow` deliberately does not carry — ADR-1520 §2 says so
/// explicitly — and it is what makes a `Bool`-valued `subsetB` usable as a
/// hypothesis instead of decorative. Both are ordinary inductions on the bound
/// whose step decides `f j` with `ops::bool_true_or_false` (two constructors,
/// no excluded middle): at `true` the guard reduces away and the induction
/// hypothesis carries; at `false` the whole loop is `false`, which contradicts
/// the `= true` premise through `false_true_elim`.
fn declare_all_below_laws(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let pty = pred_ty(d);

    // allBelow_of_all_true
    {
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);

        // `∀ i, Lt i n → f i = true`, at an arbitrary bound.
        let all_true_ty = |d: &mut NatDev<'_>, n: ExprId| -> ExprId {
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let hi_ty = d.lt(i, n);
            let fi = d.apply(f, &[i]);
            let t = d.bool_true();
            let concl = d.bool_eq(fi, t);
            let with_hi = d.arrow(hi_ty, concl);
            d.pi_fv(i_fv, nat, with_hi)
        };
        let motive_at = |d: &mut NatDev<'_>, n: ExprId| -> ExprId {
            let hyp = all_true_ty(d, n);
            let loop_ = d.const_app(p.finset_all_below, &[f, n]);
            let t = d.bool_true();
            let concl = d.bool_eq(loop_, t);
            d.arrow(hyp, concl)
        };

        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let body = d.induct(
            &|d, x| motive_at(d, x),
            &|d| {
                // `allBelow f 0` IS `true` by iota, so the hypothesis is unused.
                let zero = d.zero();
                let hyp_ty = all_true_ty(d, zero);
                let h_fv = d.fresh_fvar();
                let t = d.bool_true();
                let refl_true = d.bool_refl(t);
                d.lam_fv(h_fv, hyp_ty, refl_true)
            },
            &|d, j, ih| {
                let succ_j = d.succ(j);
                let hyp_ty = all_true_ty(d, succ_j);
                let h_fv = d.fresh_fvar();
                let h = d.kernel().fvar(h_fv);

                // `f j = true` at the new index.
                let self_lt = d.lemma(p.lt_succ_self, &[j]);
                let hfj = d.apply(h, &[j, self_lt]);

                // The induction hypothesis needs the SHORTER premise.
                let shorter = {
                    let i_fv = d.fresh_fvar();
                    let i = d.kernel().fvar(i_fv);
                    let hi_fv = d.fresh_fvar();
                    let hi_ty = d.lt(i, j);
                    let hi = d.kernel().fvar(hi_fv);
                    let succ_i = d.succ(i);
                    // `Lt i j` is `Le (succ i) j`; `le_succ_of_le` moves it to
                    // `Le (succ i) (succ j)`, which IS `Lt i (succ j)`.
                    let widened = d.lemma(p.le_succ_of_le, &[succ_i, j, hi]);
                    let step = d.apply(h, &[i, widened]);
                    let with_hi = d.lam_fv(hi_fv, hi_ty, step);
                    d.lam_fv(i_fv, nat, with_hi)
                };
                let tail = d.apply(ih, &[shorter]);

                let loop_j = d.const_app(p.finset_all_below, &[f, j]);
                let fj = d.apply(f, &[j]);
                let false_ = d.bool_false();
                let guard = bool_select_bool(d, &p, fj, loop_j, false_);
                let unguard = select_bool_true(d, &p, fj, loop_j, false_, hfj);
                let t = d.bool_true();
                let proof = d.bool_trans(guard, loop_j, t, unguard, tail);
                d.lam_fv(h_fv, hyp_ty, proof)
            },
            n,
        );

        let ty = {
            let concl = motive_at(d, n);
            let with_n = d.pi_fv(n_fv, nat, concl);
            d.pi_fv(f_fv, pty, with_n)
        };
        let value = {
            let with_n = d.lam_fv(n_fv, nat, body);
            d.lam_fv(f_fv, pty, with_n)
        };
        d.declare_theorem(p.finset_all_below_of_all_true, ty, value)?;
    }

    // allBelow_true_at
    {
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);

        let all_true_ty = |d: &mut NatDev<'_>, n: ExprId| -> ExprId {
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let hi_ty = d.lt(i, n);
            let fi = d.apply(f, &[i]);
            let t = d.bool_true();
            let concl = d.bool_eq(fi, t);
            let with_hi = d.arrow(hi_ty, concl);
            d.pi_fv(i_fv, nat, with_hi)
        };
        let motive_at = |d: &mut NatDev<'_>, n: ExprId| -> ExprId {
            let loop_ = d.const_app(p.finset_all_below, &[f, n]);
            let t = d.bool_true();
            let hyp = d.bool_eq(loop_, t);
            let concl = all_true_ty(d, n);
            d.arrow(hyp, concl)
        };

        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let body = d.induct(
            &|d, x| motive_at(d, x),
            &|d| {
                // Nothing is below `0`, so every index is refuted rather than
                // answered.
                let zero = d.zero();
                let loop_ = d.const_app(p.finset_all_below, &[f, zero]);
                let t = d.bool_true();
                let hyp_ty = d.bool_eq(loop_, t);
                let h_fv = d.fresh_fvar();
                let i_fv = d.fresh_fvar();
                let i = d.kernel().fvar(i_fv);
                let hi_ty = d.lt(i, zero);
                let hi_fv = d.fresh_fvar();
                let hi = d.kernel().fvar(hi_fv);
                let refuted = d.lemma(p.not_lt_zero, &[i, hi]);
                let goal = {
                    let fi = d.apply(f, &[i]);
                    let t2 = d.bool_true();
                    d.bool_eq(fi, t2)
                };
                let absurd = from_false(d, &p, refuted, goal);
                let with_hi = d.lam_fv(hi_fv, hi_ty, absurd);
                let with_i = d.lam_fv(i_fv, nat, with_hi);
                d.lam_fv(h_fv, hyp_ty, with_i)
            },
            &|d, j, ih| {
                let succ_j = d.succ(j);
                let loop_succ = d.const_app(p.finset_all_below, &[f, succ_j]);
                let t = d.bool_true();
                let hyp_ty = d.bool_eq(loop_succ, t);
                let h_fv = d.fresh_fvar();
                let h = d.kernel().fvar(h_fv);

                let goal = all_true_ty(d, succ_j);

                let loop_j = d.const_app(p.finset_all_below, &[f, j]);
                let fj = d.apply(f, &[j]);
                let false_ = d.bool_false();
                let guard = bool_select_bool(d, &p, fj, loop_j, false_);

                let decided = super::ops::bool_true_or_false(d, &p, fj);
                let left_ty = {
                    let t2 = d.bool_true();
                    d.bool_eq(fj, t2)
                };
                let right_ty = {
                    let f2 = d.bool_false();
                    d.bool_eq(fj, f2)
                };

                // `f j = true`: the guard reduces to the shorter loop, so the
                // induction hypothesis applies below `j`, and the new index `j`
                // itself is answered by the case hypothesis transported along
                // `i = j`.
                let left_case = {
                    let hfj_fv = d.fresh_fvar();
                    let hfj = d.kernel().fvar(hfj_fv);
                    let unguard = select_bool_true(d, &p, fj, loop_j, false_, hfj);
                    let back = d.bool_symm(guard, loop_j, unguard);
                    let t2 = d.bool_true();
                    let tail = d.bool_trans(loop_j, guard, t2, back, h);
                    let below = d.apply(ih, &[tail]);

                    let i_fv = d.fresh_fvar();
                    let i = d.kernel().fvar(i_fv);
                    let hi_fv = d.fresh_fvar();
                    let hi_ty = d.lt(i, succ_j);
                    let hi = d.kernel().fvar(hi_fv);
                    let le_ij = d.lemma(p.le_of_lt_succ, &[i, j, hi]);
                    let split = d.lemma(p.lt_or_eq_of_le, &[i, j, le_ij]);
                    let lt_ty = d.lt(i, j);
                    let eq_ty = d.eq(i, j);
                    let inner_goal = {
                        let fi = d.apply(f, &[i]);
                        let t3 = d.bool_true();
                        d.bool_eq(fi, t3)
                    };
                    let strictly_below = {
                        let hlt_fv = d.fresh_fvar();
                        let hlt = d.kernel().fvar(hlt_fv);
                        let step = d.apply(below, &[i, hlt]);
                        d.lam_fv(hlt_fv, lt_ty, step)
                    };
                    let at_the_top = {
                        let heq_fv = d.fresh_fvar();
                        let heq = d.kernel().fvar(heq_fv);
                        let back_eq = d.symm(i, j, heq);
                        let motive = d.eq_motive(j, &|d, x| {
                            let fx = d.apply(f, &[x]);
                            let t3 = d.bool_true();
                            d.bool_eq(fx, t3)
                        });
                        let moved = d.transport(j, motive, hfj, i, back_eq);
                        d.lam_fv(heq_fv, eq_ty, moved)
                    };
                    let answered = or_elim(
                        d,
                        &p,
                        lt_ty,
                        eq_ty,
                        inner_goal,
                        strictly_below,
                        at_the_top,
                        split,
                    );
                    let with_hi = d.lam_fv(hi_fv, hi_ty, answered);
                    let with_i = d.lam_fv(i_fv, nat, with_hi);
                    d.lam_fv(hfj_fv, left_ty, with_i)
                };

                // `f j = false`: the whole loop is `false`, contradicting `h`.
                let right_case = {
                    let hfj_fv = d.fresh_fvar();
                    let hfj = d.kernel().fvar(hfj_fv);
                    let collapse = select_bool_false(d, &p, fj, loop_j, false_, hfj);
                    let f2 = d.bool_false();
                    let back = d.bool_symm(guard, f2, collapse);
                    let t2 = d.bool_true();
                    let impossible = d.bool_trans(f2, guard, t2, back, h);
                    let absurd = d.false_true_elim(goal, impossible);
                    d.lam_fv(hfj_fv, right_ty, absurd)
                };

                let answered = or_elim(
                    d, &p, left_ty, right_ty, goal, left_case, right_case, decided,
                );
                d.lam_fv(h_fv, hyp_ty, answered)
            },
            n,
        );

        let ty = {
            let concl = motive_at(d, n);
            let with_n = d.pi_fv(n_fv, nat, concl);
            d.pi_fv(f_fv, pty, with_n)
        };
        let value = {
            let with_n = d.lam_fv(n_fv, nat, body);
            d.lam_fv(f_fv, pty, with_n)
        };
        d.declare_theorem(p.finset_all_below_true_at, ty, value)?;
    }

    Ok(())
}

// ---------------------------------------------------------------------------
// Cardinality is monotone under inclusion.
// ---------------------------------------------------------------------------

/// `Nat.Finset.card_le_of_subsetB : ∀ s t,
/// Eq Bool (subsetB s t) true → Le (card s) (card t)`.
///
/// `subsetB` ranges only over `[0, bound s)`; `Nat.countRange_le_of_subset`
/// wants `Nat.Subset (memB s) (memB t) width` over the COMMON bound. The gap is
/// closed without a second search: at an index at or above `bound s`,
/// `memB_of_bound_le` says `memB s i = false`, so the `Subset` premise
/// `memB s i = true` is refuted and the obligation is vacuous there. That is
/// the whole content of the lift, and it is only available because `memB`
/// truncates in its own definition.
fn declare_card_le_of_subset_b(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let fs = finset_ty(d, &p);

    let s_fv = d.fresh_fvar();
    let s = d.kernel().fvar(s_fv);
    let t_fv = d.fresh_fvar();
    let t = d.kernel().fvar(t_fv);

    let ms = fs_mem_fn(d, &p, s);
    let mt = fs_mem_fn(d, &p, t);
    let bs = fs_bound(d, &p, s);
    let bt = fs_bound(d, &p, t);
    let width = d.add(bs, bt);

    let hyp_ty = {
        let decided = d.const_app(p.finset_subset_b, &[s, t]);
        let tr = d.bool_true();
        d.bool_eq(decided, tr)
    };
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    // The `Bool`-valued implication `subsetB` loops over, as a function.
    let implication = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let msi = fs_mem(d, &p, s, i);
        let mti = fs_mem(d, &p, t, i);
        let tr = d.bool_true();
        let body = bool_select_bool(d, &p, msi, mti, tr);
        d.lam_fv(i_fv, nat, body)
    };
    // `∀ i, Lt i (bound s) → implication i = true`.
    let pointwise = d.lemma(p.finset_all_below_true_at, &[implication, bs, h]);

    // `Nat.Subset (memB s) (memB t) width`, spelled out.
    let subset = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let hk_fv = d.fresh_fvar();
        let hk_ty = d.lt(k, width);
        let hs_fv = d.fresh_fvar();
        let hs = d.kernel().fvar(hs_fv);
        let msk = fs_mem(d, &p, s, k);
        let mtk = fs_mem(d, &p, t, k);
        let tr = d.bool_true();
        let hs_ty = d.bool_eq(msk, tr);
        let goal = d.bool_eq(mtk, tr);

        let decided = d.lemma(p.lt_or_ge, &[k, bs]);
        let left_ty = d.lt(k, bs);
        let right_ty = d.le(bs, k);

        // Below `bound s`: the loop answered this index, and `memB s k = true`
        // collapses the implication's guard to `memB t k`.
        let left_case = {
            let hlt_fv = d.fresh_fvar();
            let hlt = d.kernel().fvar(hlt_fv);
            let answered = d.apply(pointwise, &[k, hlt]);
            let guard = bool_select_bool(d, &p, msk, mtk, tr);
            let collapse = select_bool_true(d, &p, msk, mtk, tr, hs);
            let back = d.bool_symm(guard, mtk, collapse);
            let step = d.bool_trans(mtk, guard, tr, back, answered);
            d.lam_fv(hlt_fv, left_ty, step)
        };
        // At or above `bound s`: `memB s k` is `false`, so the premise `hs` is
        // impossible and the obligation is vacuous.
        let right_case = {
            let hge_fv = d.fresh_fvar();
            let hge = d.kernel().fvar(hge_fv);
            let vanishes = d.lemma(p.finset_mem_b_of_bound_le, &[s, k, hge]);
            let fa = d.bool_false();
            let back = d.bool_symm(msk, fa, vanishes);
            let impossible = d.bool_trans(fa, msk, tr, back, hs);
            let absurd = d.false_true_elim(goal, impossible);
            d.lam_fv(hge_fv, right_ty, absurd)
        };

        let answered = or_elim(
            d, &p, left_ty, right_ty, goal, left_case, right_case, decided,
        );
        let with_hs = d.lam_fv(hs_fv, hs_ty, answered);
        let with_hk = d.lam_fv(hk_fv, hk_ty, with_hs);
        d.lam_fv(k_fv, nat, with_hk)
    };

    let counted = d.lemma(p.count_range_le_of_subset, &[ms, mt, width, subset]);

    // Both sides come back to their own `card` through the workhorse; the `t`
    // side needs `add_comm` first.
    let h_card_s = d.lemma(p.finset_card_eq_count_range_add, &[s, bt]);
    let h_card_t = {
        let comm = d.lemma(p.add_comm, &[bs, bt]);
        let swapped = d.add(bt, bs);
        let move_bound = d.congr(width, swapped, comm, &|d, x| {
            let mt_inner = fs_mem_fn(d, &p, t);
            count_range(d, &p, mt_inner, x)
        });
        let collapse = d.lemma(p.finset_card_eq_count_range_add, &[t, bs]);
        let lhs = count_range(d, &p, mt, width);
        let midpoint = count_range(d, &p, mt, swapped);
        let card_t = fs_card(d, &p, t);
        d.trans(lhs, midpoint, card_t, move_bound, collapse)
    };

    let cr_s = count_range(d, &p, ms, width);
    let cr_t = count_range(d, &p, mt, width);
    let card_s = fs_card(d, &p, s);
    let card_t = fs_card(d, &p, t);

    let moved_left = {
        let motive = d.eq_motive(cr_s, &|d, x| d.le(x, cr_t));
        d.transport(cr_s, motive, counted, card_s, h_card_s)
    };
    let moved_right = {
        let motive = d.eq_motive(cr_t, &|d, x| d.le(card_s, x));
        d.transport(cr_t, motive, moved_left, card_t, h_card_t)
    };

    let concl = d.le(card_s, card_t);
    let ty = {
        let with_h = d.arrow(hyp_ty, concl);
        let with_t = d.pi_fv(t_fv, fs, with_h);
        d.pi_fv(s_fv, fs, with_t)
    };
    let value = {
        let with_h = d.lam_fv(h_fv, hyp_ty, moved_right);
        let with_t = d.lam_fv(t_fv, fs, with_h);
        d.lam_fv(s_fv, fs, with_t)
    };
    d.declare_theorem(p.finset_card_le_of_subset_b, ty, value)?;
    Ok(())
}

// ---------------------------------------------------------------------------
// Summing over a set.
// ---------------------------------------------------------------------------

/// `heq : Eq Bool cond true ⊢ Eq Nat (bool_select_nat cond a b) a` — the
/// `Nat`-codomain twin of [`select_bool_true`].
fn select_nat_true(d: &mut NatDev<'_>, cond: ExprId, a: ExprId, b: ExprId, heq: ExprId) -> ExprId {
    let true_val = d.bool_true();
    let back = d.bool_symm(cond, true_val, heq);
    let motive = d.bool_eq_motive(true_val, &|d, value| {
        let sel = d.bool_select_nat(value, a, b);
        d.eq(sel, a)
    });
    let refl_case = d.refl(a);
    d.bool_transport(true_val, motive, refl_case, cond, back)
}

/// `heq : Eq Bool cond false ⊢ Eq Nat (bool_select_nat cond a b) b`.
fn select_nat_false(d: &mut NatDev<'_>, cond: ExprId, a: ExprId, b: ExprId, heq: ExprId) -> ExprId {
    let false_val = d.bool_false();
    let back = d.bool_symm(cond, false_val, heq);
    let motive = d.bool_eq_motive(false_val, &|d, value| {
        let sel = d.bool_select_nat(value, a, b);
        d.eq(sel, b)
    });
    let refl_case = d.refl(b);
    d.bool_transport(false_val, motive, refl_case, cond, back)
}

/// `h : Eq Bool a b ⊢ Eq Nat (body a) (body b)` — [`NatOps::congr`] transports
/// along a `Nat` equality and always closes into `Eq Nat`; this one transports
/// along a `Bool` equality into the same place. `gauss_lemma.rs` carries its own
/// copy under the same name, per this prelude's per-file convention.
fn congr_bool_to_nat(
    d: &mut NatDev<'_>,
    a: ExprId,
    b: ExprId,
    h: ExprId,
    f: &dyn Fn(&mut NatDev<'_>, ExprId) -> ExprId,
) -> ExprId {
    let fa = f(d, a);
    let motive = d.bool_eq_motive(a, &|d, x| {
        let fx = f(d, x);
        d.eq(fa, fx)
    });
    let refl_case = d.refl(fa);
    d.bool_transport(a, motive, refl_case, b, h)
}

/// `Nat.Finset.sum_eq_sumRangeIf_add : ∀ s j f,
/// Eq Nat (sumRangeIf (memB s) f (add (bound s) j)) (sum s f)`.
///
/// [`declare_card_eq_count_range_add`]'s twin on the additive side, and needed
/// for the same reason: a two-set law folds both sums over the common bound
/// `bound s + bound t` and each side has to come back to its own `sum`. The
/// tail is not merely zero-COUNTED but zero-VALUED — `memB s (bound s + k)` is
/// `false`, so the guard selects `0` whatever `f` is there — which is what
/// `sumRange_const_zero` then collapses.
fn declare_sum_eq_sum_range_if_add(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let fs = finset_ty(d, &p);
    let fty = fun_ty(d);

    let s_fv = d.fresh_fvar();
    let s = d.kernel().fvar(s_fv);
    let j_fv = d.fresh_fvar();
    let j = d.kernel().fvar(j_fv);
    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);

    let bs = fs_bound(d, &p, s);
    let total = d.add(bs, j);

    // `fun i => if memB s i then f i else 0`, the function `sumRangeIf` folds.
    let selected = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let msi = fs_mem(d, &p, s, i);
        let fi = d.apply(f, &[i]);
        let zero = d.zero();
        let body = d.bool_select_nat(msi, fi, zero);
        d.lam_fv(i_fv, nat, body)
    };
    let split = d.lemma(p.sum_range_split, &[selected, bs, j]);

    let tail_fn = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let shifted = d.add(bs, k);
        let body = d.apply(selected, &[shifted]);
        d.lam_fv(k_fv, nat, body)
    };
    let const_zero = {
        let k_fv = d.fresh_fvar();
        let z = d.zero();
        d.lam_fv(k_fv, nat, z)
    };
    let tail_is_zero_fn = {
        let pointwise = {
            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let hk_fv = d.fresh_fvar();
            let hk_ty = d.lt(k, j);
            let shifted = d.add(bs, k);
            let bound_le = d.lemma(p.le_add_right, &[bs, k]);
            let vanishes = d.lemma(p.finset_mem_b_of_bound_le, &[s, shifted, bound_le]);
            let msk = fs_mem(d, &p, s, shifted);
            let fk = d.apply(f, &[shifted]);
            let zero = d.zero();
            let step = select_nat_false(d, msk, fk, zero, vanishes);
            let with_hk = d.lam_fv(hk_fv, hk_ty, step);
            d.lam_fv(k_fv, nat, with_hk)
        };
        d.lemma(p.sum_range_congr_lt, &[tail_fn, const_zero, j, pointwise])
    };
    let tail_zero = {
        let collapse = d.lemma(p.sum_range_const_zero, &[j]);
        let lhs = d.sum_range(tail_fn, j);
        let mid = d.sum_range(const_zero, j);
        let zero = d.zero();
        d.trans(lhs, mid, zero, tail_is_zero_fn, collapse)
    };

    let head = d.sum_range(selected, bs);
    let tail = d.sum_range(tail_fn, j);
    let zero = d.zero();
    let start = d.sum_range(selected, total);
    let mid = d.add(head, tail);
    let with_zero = d.add(head, zero);
    let collapse = d.congr(tail, zero, tail_zero, &|d, x| d.add(head, x));
    let close = d.lemma(p.add_zero, &[head]);
    let (_, proof) = d.chain(start, &[(mid, split), (with_zero, collapse), (head, close)]);

    let concl = {
        let lhs = {
            let m = fs_mem_fn(d, &p, s);
            sum_range_if(d, &p, m, f, total)
        };
        let rhs = d.const_app(p.finset_sum, &[s, f]);
        d.eq(lhs, rhs)
    };
    let ty = {
        let with_f = d.pi_fv(f_fv, fty, concl);
        let with_j = d.pi_fv(j_fv, nat, with_f);
        d.pi_fv(s_fv, fs, with_j)
    };
    let value = {
        let with_f = d.lam_fv(f_fv, fty, proof);
        let with_j = d.lam_fv(j_fv, nat, with_f);
        d.lam_fv(s_fv, fs, with_j)
    };
    d.declare_theorem(p.finset_sum_eq_sum_range_if_add, ty, value)?;
    Ok(())
}

/// `Nat.Finset.sum_union_disjoint : ∀ s t f,
/// (∀ i, Eq Bool (setInter (memB s) (memB t) i) false) →
/// Eq Nat (sum (union s t) f) (add (sum s f) (sum t f))`.
///
/// The hypothesis is DISJOINTNESS SPELLED POINTWISE rather than
/// `card (inter s t) = 0`, and deliberately: this kernel has no route from a
/// zero count back to a pointwise `false` without a second bounded search, and
/// every consumer of "these two sets do not meet" has the pointwise fact in
/// hand already (`Nat.setInter` is where `finite_set.rs` puts it).
///
/// The whole proof is ONE per-index identity —
/// `sel (union i) (f i) 0 = sel (s i) (f i) 0 + sel (t i) (f i) 0` — decided on
/// `memB s i` alone, plus `Nat.sumRange_add`. Disjointness is used in exactly
/// one branch: at `memB s i = true` it forces `memB t i = false`, so the right
/// summand is `0` and `add_zero` closes; at `memB s i = false` the left summand
/// is `0` by definition and `zero_add` closes with no hypothesis at all.
fn declare_sum_union_disjoint(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let fs = finset_ty(d, &p);
    let fty = fun_ty(d);

    let s_fv = d.fresh_fvar();
    let s = d.kernel().fvar(s_fv);
    let t_fv = d.fresh_fvar();
    let t = d.kernel().fvar(t_fv);
    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);

    let ms = fs_mem_fn(d, &p, s);
    let mt = fs_mem_fn(d, &p, t);
    let bs = fs_bound(d, &p, s);
    let bt = fs_bound(d, &p, t);
    let width = d.add(bs, bt);
    let union = d.const_app(p.finset_union, &[s, t]);
    let m_union = fs_mem_fn(d, &p, union);
    let u_pred = set_union(d, &p, ms, mt);
    let i_pred = set_inter(d, &p, ms, mt);

    let hyp_ty = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let meet = d.apply(i_pred, &[i]);
        let fa = d.bool_false();
        let body = d.bool_eq(meet, fa);
        d.pi_fv(i_fv, nat, body)
    };
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    // The three selected functions, as lambdas, so `sumRange_add` applies.
    let sel_of = |d: &mut NatDev<'_>, q: ExprId| -> ExprId {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let qi = d.apply(q, &[i]);
        let fi = d.apply(f, &[i]);
        let zero = d.zero();
        let body = d.bool_select_nat(qi, fi, zero);
        d.lam_fv(i_fv, nat, body)
    };
    let sel_s = sel_of(d, ms);
    let sel_t = sel_of(d, mt);
    let sel_sum = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let a = d.apply(sel_s, &[i]);
        let b = d.apply(sel_t, &[i]);
        let body = d.add(a, b);
        d.lam_fv(i_fv, nat, body)
    };

    // Step 1: the union's membership agrees with `setUnion` below the common
    // bound, so the fold may be restated at the bare predicate.
    let restate = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let hi_fv = d.fresh_fvar();
        let hi_ty = d.lt(i, width);
        let hi = d.kernel().fvar(hi_fv);
        let step = d.lemma(p.finset_mem_b_of_lt, &[union, i, hi]);
        let with_hi = d.lam_fv(hi_fv, hi_ty, step);
        let pred_agree = d.lam_fv(i_fv, nat, with_hi);
        let fun_agree = {
            let i2_fv = d.fresh_fvar();
            let i2 = d.kernel().fvar(i2_fv);
            let hi2_fv = d.fresh_fvar();
            let hi2_ty = d.lt(i2, width);
            let fi = d.apply(f, &[i2]);
            let step2 = d.refl(fi);
            let with_hi2 = d.lam_fv(hi2_fv, hi2_ty, step2);
            d.lam_fv(i2_fv, nat, with_hi2)
        };
        d.lemma(
            p.sum_range_if_congr_lt,
            &[m_union, u_pred, f, f, width, pred_agree, fun_agree],
        )
    };

    // Step 2: the per-index split, decided on `memB s i` alone.
    let per_index = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let msi = fs_mem(d, &p, s, i);
        let mti = fs_mem(d, &p, t, i);
        let fi = d.apply(f, &[i]);
        let zero = d.zero();
        let ui = d.apply(u_pred, &[i]);
        let sel_u_i = d.bool_select_nat(ui, fi, zero);
        let sel_s_i = d.bool_select_nat(msi, fi, zero);
        let sel_t_i = d.bool_select_nat(mti, fi, zero);
        let goal = {
            let rhs = d.add(sel_s_i, sel_t_i);
            d.eq(sel_u_i, rhs)
        };

        let decided = super::ops::bool_true_or_false(d, &p, msi);
        let left_ty = {
            let tr = d.bool_true();
            d.bool_eq(msi, tr)
        };
        let right_ty = {
            let fa = d.bool_false();
            d.bool_eq(msi, fa)
        };

        // `memB s i = true`: the union selects `f i`, and disjointness forces
        // `memB t i = false`, so the right summand vanishes.
        let left_case = {
            let hms_fv = d.fresh_fvar();
            let hms = d.kernel().fvar(hms_fv);
            let tr = d.bool_true();
            let union_true = select_bool_true(d, &p, msi, tr, mti, hms);
            let a = select_nat_true(d, ui, fi, zero, union_true);

            let meet = d.apply(i_pred, &[i]);
            let false_lit = d.bool_false();
            let inter_is_t = select_bool_true(d, &p, msi, mti, false_lit, hms);
            let hmeet = d.apply(h, &[i]);
            let back = d.bool_symm(meet, mti, inter_is_t);
            let fa = d.bool_false();
            let t_false = d.bool_trans(mti, meet, fa, back, hmeet);
            let t_zero = select_nat_false(d, mti, fi, zero, t_false);
            let s_is_f = select_nat_true(d, msi, fi, zero, hms);

            let with_zero = d.add(fi, zero);
            let az = d.lemma(p.add_zero, &[fi]);
            let unfold_zero = d.symm(with_zero, fi, az);
            let back_s = d.symm(sel_s_i, fi, s_is_f);
            let put_s = d.congr(fi, sel_s_i, back_s, &|d, x| d.add(x, zero));
            let back_t = d.symm(sel_t_i, zero, t_zero);
            let put_t = d.congr(zero, sel_t_i, back_t, &|d, x| d.add(sel_s_i, x));
            let step2 = d.add(sel_s_i, zero);
            let step3 = d.add(sel_s_i, sel_t_i);
            let (_, proof) = d.chain(
                sel_u_i,
                &[
                    (fi, a),
                    (with_zero, unfold_zero),
                    (step2, put_s),
                    (step3, put_t),
                ],
            );
            d.lam_fv(hms_fv, left_ty, proof)
        };

        // `memB s i = false`: the union selects `memB t i` and the left summand
        // is `0`. Disjointness is not used at all here.
        let right_case = {
            let hms_fv = d.fresh_fvar();
            let hms = d.kernel().fvar(hms_fv);
            let tr = d.bool_true();
            let union_is_t = select_bool_false(d, &p, msi, tr, mti, hms);
            let a = congr_bool_to_nat(d, ui, mti, union_is_t, &|d, x| {
                d.bool_select_nat(x, fi, zero)
            });
            let s_zero = select_nat_false(d, msi, fi, zero, hms);
            let zero_left = d.add(zero, sel_t_i);
            let za = d.lemma(p.zero_add, &[sel_t_i]);
            let unfold_zero = d.symm(zero_left, sel_t_i, za);
            let back_s = d.symm(sel_s_i, zero, s_zero);
            let put_s = d.congr(zero, sel_s_i, back_s, &|d, x| d.add(x, sel_t_i));
            let step3 = d.add(sel_s_i, sel_t_i);
            let (_, proof) = d.chain(
                sel_u_i,
                &[(sel_t_i, a), (zero_left, unfold_zero), (step3, put_s)],
            );
            d.lam_fv(hms_fv, right_ty, proof)
        };

        let answered = or_elim(
            d, &p, left_ty, right_ty, goal, left_case, right_case, decided,
        );
        d.lam_fv(i_fv, nat, answered)
    };

    let sel_u = sel_of(d, u_pred);
    let regroup = d.lemma(p.sum_range_congr, &[sel_u, sel_sum, width, per_index]);
    let separate = d.lemma(p.sum_range_add, &[sel_s, sel_t, width]);

    // Each side back to its own `sum`; the `t` side moves the bound first.
    let h_sum_s = d.lemma(p.finset_sum_eq_sum_range_if_add, &[s, bt, f]);
    let h_sum_t = {
        let comm = d.lemma(p.add_comm, &[bs, bt]);
        let swapped = d.add(bt, bs);
        let move_bound = d.congr(width, swapped, comm, &|d, x| {
            let mt_inner = fs_mem_fn(d, &p, t);
            sum_range_if(d, &p, mt_inner, f, x)
        });
        let collapse = d.lemma(p.finset_sum_eq_sum_range_if_add, &[t, bs, f]);
        let lhs = sum_range_if(d, &p, mt, f, width);
        let midpoint = sum_range_if(d, &p, mt, f, swapped);
        let sum_t = d.const_app(p.finset_sum, &[t, f]);
        d.trans(lhs, midpoint, sum_t, move_bound, collapse)
    };

    let fold_union = sum_range_if(d, &p, m_union, f, width);
    let fold_u_pred = d.sum_range(sel_u, width);
    let fold_sum = d.sum_range(sel_sum, width);
    let fold_s = d.sum_range(sel_s, width);
    let fold_t = d.sum_range(sel_t, width);
    let sum_s = d.const_app(p.finset_sum, &[s, f]);
    let sum_t = d.const_app(p.finset_sum, &[t, f]);

    let separated = d.add(fold_s, fold_t);
    let after_s = d.add(sum_s, fold_t);
    let after_t = d.add(sum_s, sum_t);
    let step_s = d.congr(fold_s, sum_s, h_sum_s, &|d, x| d.add(x, fold_t));
    let step_t = d.congr(fold_t, sum_t, h_sum_t, &|d, x| d.add(sum_s, x));

    let (_, proof) = d.chain(
        fold_union,
        &[
            (fold_u_pred, restate),
            (fold_sum, regroup),
            (separated, separate),
            (after_s, step_s),
            (after_t, step_t),
        ],
    );

    let concl = {
        let lhs = d.const_app(p.finset_sum, &[union, f]);
        d.eq(lhs, after_t)
    };
    let ty = {
        let with_h = d.arrow(hyp_ty, concl);
        let with_f = d.pi_fv(f_fv, fty, with_h);
        let with_t = d.pi_fv(t_fv, fs, with_f);
        d.pi_fv(s_fv, fs, with_t)
    };
    let value = {
        let with_h = d.lam_fv(h_fv, hyp_ty, proof);
        let with_f = d.lam_fv(f_fv, fty, with_h);
        let with_t = d.lam_fv(t_fv, fs, with_f);
        d.lam_fv(s_fv, fs, with_t)
    };
    d.declare_theorem(p.finset_sum_union_disjoint, ty, value)?;
    Ok(())
}

// ---------------------------------------------------------------------------
// Summing over sets that agree.
// ---------------------------------------------------------------------------

/// `Nat.Finset.sum_congr_of_beq : ∀ s t f, Eq Bool (beq s t) true →
/// Eq Nat (sum s f) (sum t f)`.
///
/// This kernel has no `funext`, so there is no "`s` and `t` are equal sets"
/// hypothesis to take: the premise is the DECIDED pointwise agreement `beq`,
/// and the proof reads it back with [`declare_all_below_laws`]'s reflection
/// lemma. That is `Nat.sumRangeIf_congr_lt`'s shape one level up — bounded
/// agreement of the predicates, bounded agreement of the summands (here
/// `Eq.refl`, since the summand is shared) — and it is the reason the reflection
/// direction had to exist before this statement could be made at all.
///
/// The per-index step is a nested `Bool` decision: `memB s i = true` collapses
/// `beq`'s guard to `memB t i`, which the premise then forces to `true`; at
/// `memB s i = false` the inner guard is reached, and its `memB t i = true`
/// branch is `false` — contradicting the premise — while its `false` branch
/// closes. Three leaves, one of them a refutation.
fn declare_sum_congr_of_beq(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let fs = finset_ty(d, &p);
    let fty = fun_ty(d);

    let s_fv = d.fresh_fvar();
    let s = d.kernel().fvar(s_fv);
    let t_fv = d.fresh_fvar();
    let t = d.kernel().fvar(t_fv);
    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);

    let ms = fs_mem_fn(d, &p, s);
    let mt = fs_mem_fn(d, &p, t);
    let bs = fs_bound(d, &p, s);
    let bt = fs_bound(d, &p, t);
    let width = d.add(bs, bt);

    let hyp_ty = {
        let decided = d.const_app(p.finset_beq, &[s, t]);
        let tr = d.bool_true();
        d.bool_eq(decided, tr)
    };
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    // `beq`'s loop body, as a function: the pointwise biconditional.
    let agreement = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let msi = fs_mem(d, &p, s, i);
        let mti = fs_mem(d, &p, t, i);
        let tr = d.bool_true();
        let fa = d.bool_false();
        let neither = bool_select_bool(d, &p, mti, fa, tr);
        let body = bool_select_bool(d, &p, msi, mti, neither);
        d.lam_fv(i_fv, nat, body)
    };
    let pointwise = d.lemma(p.finset_all_below_true_at, &[agreement, width, h]);

    // `∀ i, Lt i width → memB s i = memB t i`.
    let members_agree = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let hi_fv = d.fresh_fvar();
        let hi_ty = d.lt(i, width);
        let hi = d.kernel().fvar(hi_fv);
        let msi = fs_mem(d, &p, s, i);
        let mti = fs_mem(d, &p, t, i);
        let tr = d.bool_true();
        let fa = d.bool_false();
        let neither = bool_select_bool(d, &p, mti, fa, tr);
        let guard = bool_select_bool(d, &p, msi, mti, neither);
        let answered = d.apply(pointwise, &[i, hi]);
        let goal = d.bool_eq(msi, mti);

        let outer = super::ops::bool_true_or_false(d, &p, msi);
        let outer_left_ty = d.bool_eq(msi, tr);
        let outer_right_ty = d.bool_eq(msi, fa);

        // `memB s i = true`: the guard is `memB t i`, which the premise makes
        // `true`, and both sides are then `true`.
        let outer_left = {
            let hms_fv = d.fresh_fvar();
            let hms = d.kernel().fvar(hms_fv);
            let collapse = select_bool_true(d, &p, msi, mti, neither, hms);
            let back = d.bool_symm(guard, mti, collapse);
            let t_true = d.bool_trans(mti, guard, tr, back, answered);
            let back_t = d.bool_symm(mti, tr, t_true);
            let step = d.bool_trans(msi, tr, mti, hms, back_t);
            d.lam_fv(hms_fv, outer_left_ty, step)
        };

        // `memB s i = false`: the guard is the inner biconditional branch.
        let outer_right = {
            let hms_fv = d.fresh_fvar();
            let hms = d.kernel().fvar(hms_fv);
            let collapse = select_bool_false(d, &p, msi, mti, neither, hms);
            let back = d.bool_symm(guard, neither, collapse);
            let inner_true = d.bool_trans(neither, guard, tr, back, answered);

            let inner = super::ops::bool_true_or_false(d, &p, mti);
            let inner_left_ty = d.bool_eq(mti, tr);
            let inner_right_ty = d.bool_eq(mti, fa);

            // `memB t i = true` here would make the branch `false`, which
            // contradicts the premise. This is the leaf that makes `beq` a
            // BICONDITIONAL rather than a one-sided inclusion.
            let inner_left = {
                let hmt_fv = d.fresh_fvar();
                let hmt = d.kernel().fvar(hmt_fv);
                let is_false = select_bool_true(d, &p, mti, fa, tr, hmt);
                let back_inner = d.bool_symm(neither, fa, is_false);
                let impossible = d.bool_trans(fa, neither, tr, back_inner, inner_true);
                let absurd = d.false_true_elim(goal, impossible);
                d.lam_fv(hmt_fv, inner_left_ty, absurd)
            };
            let inner_right = {
                let hmt_fv = d.fresh_fvar();
                let hmt = d.kernel().fvar(hmt_fv);
                let back_t = d.bool_symm(mti, fa, hmt);
                let step = d.bool_trans(msi, fa, mti, hms, back_t);
                d.lam_fv(hmt_fv, inner_right_ty, step)
            };
            let decided_inner = or_elim(
                d,
                &p,
                inner_left_ty,
                inner_right_ty,
                goal,
                inner_left,
                inner_right,
                inner,
            );
            d.lam_fv(hms_fv, outer_right_ty, decided_inner)
        };

        let decided = or_elim(
            d,
            &p,
            outer_left_ty,
            outer_right_ty,
            goal,
            outer_left,
            outer_right,
            outer,
        );
        let with_hi = d.lam_fv(hi_fv, hi_ty, decided);
        d.lam_fv(i_fv, nat, with_hi)
    };

    let summands_agree = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let hi_fv = d.fresh_fvar();
        let hi_ty = d.lt(i, width);
        let fi = d.apply(f, &[i]);
        let step = d.refl(fi);
        let with_hi = d.lam_fv(hi_fv, hi_ty, step);
        d.lam_fv(i_fv, nat, with_hi)
    };
    let folds_agree = d.lemma(
        p.sum_range_if_congr_lt,
        &[ms, mt, f, f, width, members_agree, summands_agree],
    );

    let h_sum_s = d.lemma(p.finset_sum_eq_sum_range_if_add, &[s, bt, f]);
    let h_sum_t = {
        let comm = d.lemma(p.add_comm, &[bs, bt]);
        let swapped = d.add(bt, bs);
        let move_bound = d.congr(width, swapped, comm, &|d, x| {
            let mt_inner = fs_mem_fn(d, &p, t);
            sum_range_if(d, &p, mt_inner, f, x)
        });
        let collapse = d.lemma(p.finset_sum_eq_sum_range_if_add, &[t, bs, f]);
        let lhs = sum_range_if(d, &p, mt, f, width);
        let midpoint = sum_range_if(d, &p, mt, f, swapped);
        let sum_t = d.const_app(p.finset_sum, &[t, f]);
        d.trans(lhs, midpoint, sum_t, move_bound, collapse)
    };

    let fold_s = sum_range_if(d, &p, ms, f, width);
    let fold_t = sum_range_if(d, &p, mt, f, width);
    let sum_s = d.const_app(p.finset_sum, &[s, f]);
    let sum_t = d.const_app(p.finset_sum, &[t, f]);

    let open_s = d.symm(fold_s, sum_s, h_sum_s);
    let (_, proof) = d.chain(
        sum_s,
        &[(fold_s, open_s), (fold_t, folds_agree), (sum_t, h_sum_t)],
    );

    let concl = d.eq(sum_s, sum_t);
    let ty = {
        let with_h = d.arrow(hyp_ty, concl);
        let with_f = d.pi_fv(f_fv, fty, with_h);
        let with_t = d.pi_fv(t_fv, fs, with_f);
        d.pi_fv(s_fv, fs, with_t)
    };
    let value = {
        let with_h = d.lam_fv(h_fv, hyp_ty, proof);
        let with_f = d.lam_fv(f_fv, fty, with_h);
        let with_t = d.lam_fv(t_fv, fs, with_f);
        d.lam_fv(s_fv, fs, with_t)
    };
    d.declare_theorem(p.finset_sum_congr_of_beq, ty, value)?;
    Ok(())
}

/// Every `Nat.Finset` declaration, in dependency order.
///
/// # Errors
///
/// Returns the trusted gate's rejection.
pub(super) fn declare_finset_all(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    declare_carrier(d, p)?;
    declare_operations(d, p)?;
    declare_decisions(d, p)?;
    declare_membership_laws(d, p)?;
    declare_card_eq_count_range_add(d, p)?;
    declare_card_union_add_card_inter(d, p)?;
    declare_all_below_laws(d, p)?;
    declare_card_le_of_subset_b(d, p)?;
    declare_sum_eq_sum_range_if_add(d, p)?;
    declare_sum_union_disjoint(d, p)?;
    declare_sum_congr_of_beq(d, p)?;
    Ok(())
}
