//! General inclusion–exclusion over a family of decidable subsets of `[0,m)`
//! (roadmap W2-19, ADR-1624).
//!
//! # The statement, and why it is not signed
//!
//! ```text
//! Nat.Subsets.inclusion_exclusion : ∀ A n m,
//!   ieSum A n m true + countRange (unionAt A n) m = ieSum A n m false + m
//!
//! Nat.Subsets.inclusion_exclusion_pos : ∀ A n m,
//!   countRange (unionAt A n) m + ieSumPos A n m true = ieSumPos A n m false
//! ```
//!
//! `ieSum A n m b` is the sum of `card (⋂_{i ∈ s} A i)` over the subsets `s` of
//! `[0,n)` of cardinality parity `b`, and `ieSumPos` is the same over the
//! NON-EMPTY subsets. The second statement is the classical one — the union's
//! cardinality plus the even-subset sum equals the odd-subset sum — and it is
//! the first with the empty set's contribution (which is `m`, the whole ambient
//! range) cancelled off both sides.
//!
//! `Nat` has no negatives, so `∑ (−1)^{|s|+1} |A_s|` cannot be written. Both
//! statements are therefore `even + something = odd`, the graded-pair shape
//! ADR-1619 chose for Möbius. Two `Nat` equations, not one signed one.
//!
//! # The proof is two swaps and one per-element identity
//!
//! `card (⋂_{i ∈ s} A i)` is `∑_{v < m} ∏_{i ∈ s} [v ∈ A i]`, so
//! `Nat.Subsets.sumSel_swap` turns the sum over subsets of a sum over elements
//! into a sum over elements of a sum over subsets. Inside, at a FIXED `v`, the
//! subset sum is a product-expansion:
//!
//! ```text
//! sumSel n (fun s => meetInd A n s v) b = prodPar (fun i => A i v) n b
//! ```
//!
//! and `prodPar` satisfies the whole of the argument in one line:
//! `prodPar c n true = prodPar c n false + noneOf c n`, where `noneOf c n` is
//! `1` when no `i < n` has `c i` and `0` otherwise. Summing that over `v` gives
//! the count of the elements in NO member of the family, and
//! `Nat.countRange_compl` turns it into `m − |⋃ A i|` without a subtraction.
//!
//! The per-element identity is where the support invariant is spent: the
//! induction step rewrites `meetInd A (succ n) s v` to `meetInd A n s v` for
//! the sets the fold actually enumerates, which is exactly
//! `Nat.Subsets.sumSel_congr`'s hypothesis.
//!
//! # The two-set case is recovered, as a theorem
//!
//! `Nat.Subsets.inclusion_exclusion_two` is
//! `Nat.countRange_union_add_inter`'s statement at `p := A 0`, `q := A 1`,
//! derived from the general theorem at `n = 2`. It is not a test that the two
//! agree — it is the general result instantiated, so a general theorem that
//! failed to specialise would not compile.

#![allow(clippy::many_single_char_names, clippy::too_many_lines)]

use super::NatPrelude;
use super::graph::not_b;
use super::ops::{NatDev, NatOps, bool_true_or_false};
use super::subset_sums::{
    add_congr, bool_select_bool, empty_set, insert_at, or_elim, set_ty, sum_sel, sum_sel_pos,
    supported, with_top,
};
use crate::KernelError;
use crate::env::Declaration;
use crate::env::ReducibilityHint;
use crate::expr::{BinderInfo, ExprId};

// ---------------------------------------------------------------------------
// Small term builders.
// ---------------------------------------------------------------------------

/// `Nat → Nat → Bool` — a family of decidable subsets: `A i v` is `v ∈ A i`.
fn family_ty(d: &mut NatDev<'_>) -> ExprId {
    let nat = d.nat_ty();
    let cty = set_ty(d);
    d.arrow(nat, cty)
}

/// `Nat.Subsets.anyOf c n`.
pub(super) fn any_of(d: &mut NatDev<'_>, p: &NatPrelude, c: ExprId, n: ExprId) -> ExprId {
    d.const_app(p.subsets_any_of, &[c, n])
}

/// `Nat.Subsets.noneOf c n`.
pub(super) fn none_of(d: &mut NatDev<'_>, p: &NatPrelude, c: ExprId, n: ExprId) -> ExprId {
    d.const_app(p.subsets_none_of, &[c, n])
}

/// `Nat.Subsets.prodPar c n b`.
pub(super) fn prod_par(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    c: ExprId,
    n: ExprId,
    b: ExprId,
) -> ExprId {
    d.const_app(p.subsets_prod_par, &[c, n, b])
}

/// `Nat.Subsets.meetInd A n s v`.
pub(super) fn meet_ind(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    a: ExprId,
    n: ExprId,
    s: ExprId,
    v: ExprId,
) -> ExprId {
    d.const_app(p.subsets_meet_ind, &[a, n, s, v])
}

/// `Nat.Subsets.meetCard A n s m`.
pub(super) fn meet_card(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    a: ExprId,
    n: ExprId,
    s: ExprId,
    m: ExprId,
) -> ExprId {
    d.const_app(p.subsets_meet_card, &[a, n, s, m])
}

/// `Nat.Subsets.unionAt A n`.
pub(super) fn union_at(d: &mut NatDev<'_>, p: &NatPrelude, a: ExprId, n: ExprId) -> ExprId {
    d.const_app(p.subsets_union_at, &[a, n])
}

/// `Nat.Subsets.ieSum A n m b`.
pub(super) fn ie_sum(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    a: ExprId,
    n: ExprId,
    m: ExprId,
    b: ExprId,
) -> ExprId {
    d.const_app(p.subsets_ie_sum, &[a, n, m, b])
}

/// `Nat.Subsets.ieSumPos A n m b`.
pub(super) fn ie_sum_pos(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    a: ExprId,
    n: ExprId,
    m: ExprId,
    b: ExprId,
) -> ExprId {
    d.const_app(p.subsets_ie_sum_pos, &[a, n, m, b])
}

/// `fun i => A i v` — the family read at one ambient element.
fn slice_fn(d: &mut NatDev<'_>, a: ExprId, v: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let body = d.apply(a, &[i, v]);
    d.lam_fv(i_fv, nat, body)
}

/// `fun i => bool_select_nat (A i v) 1 0` — the `{0,1}` indicator of that
/// slice, which is what a PRODUCT over a subset needs.
fn ind_fn(d: &mut NatDev<'_>, a: ExprId, v: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let cond = d.apply(a, &[i, v]);
    let one = d.num(1);
    let zero = d.zero();
    let body = d.bool_select_nat(cond, one, zero);
    d.lam_fv(i_fv, nat, body)
}

/// `fun s => meetInd A n s v` — the summand `sumSel` folds at a fixed `v`.
fn meet_at(d: &mut NatDev<'_>, p: &NatPrelude, a: ExprId, n: ExprId, v: ExprId) -> ExprId {
    let p = *p;
    let sty = set_ty(d);
    let s_fv = d.fresh_fvar();
    let s = d.kernel().fvar(s_fv);
    let body = meet_ind(d, &p, a, n, s, v);
    d.lam_fv(s_fv, sty, body)
}

/// `fun s => meetCard A n s m` — the summand `ieSum` folds.
fn card_at(d: &mut NatDev<'_>, p: &NatPrelude, a: ExprId, n: ExprId, m: ExprId) -> ExprId {
    let p = *p;
    let sty = set_ty(d);
    let s_fv = d.fresh_fvar();
    let s = d.kernel().fvar(s_fv);
    let body = meet_card(d, &p, a, n, s, m);
    d.lam_fv(s_fv, sty, body)
}

/// Congruence from a `Bool` equation into a `Nat`-valued one-hole context:
/// `h : Eq Bool a b ⊢ Eq Nat (f a) (f b)`. The mirror of `subset_search.rs`'s
/// `nat_to_bool_congr`; `NatOps::congr` takes a `Nat` equation and does not
/// apply.
fn bool_to_nat_congr(
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

// ---------------------------------------------------------------------------
// The definitions.
// ---------------------------------------------------------------------------

fn declare_definitions(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let bool_ty = d.bool_ty();
    let cty = set_ty(d);
    let fam = family_ty(d);
    let anon = d.anon_name();
    let one = d.level_one();

    // anyOf : (Nat -> Bool) -> Nat -> Bool
    //   | c 0        = false
    //   | c (succ m) = if anyOf c m then true else c m
    {
        let c_fv = d.fresh_fvar();
        let c = d.kernel().fvar(c_fv);
        let motive = d.kernel().lam(anon, nat, bool_ty, BinderInfo::Default);
        let base = d.bool_false();
        let step = {
            let m_fv = d.fresh_fvar();
            let m = d.kernel().fvar(m_fv);
            let ih_fv = d.fresh_fvar();
            let ih = d.kernel().fvar(ih_fv);
            let tv = d.bool_true();
            let cm = d.apply(c, &[m]);
            let body = bool_select_bool(d, &p, ih, tv, cm);
            let with_ih = d.lam_fv(ih_fv, bool_ty, body);
            d.lam_fv(m_fv, nat, with_ih)
        };
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let rec = d.kernel().const_(p.rec, vec![one]);
        let body = d.apply(rec, &[motive, base, step, n]);
        let value = {
            let with_n = d.lam_fv(n_fv, nat, body);
            d.lam_fv(c_fv, cty, with_n)
        };
        let ty = {
            let inner = d.arrow(nat, bool_ty);
            d.arrow(cty, inner)
        };
        d.kernel().add_declaration(Declaration::Definition {
            name: p.subsets_any_of,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(30),
        })?;
    }

    // noneOf : (Nat -> Bool) -> Nat -> Nat
    //   := fun c n => prodRange (fun i => if c i then 0 else 1) n
    {
        let c_fv = d.fresh_fvar();
        let c = d.kernel().fvar(c_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let f = {
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let ci = d.apply(c, &[i]);
            let zero = d.zero();
            let one_lit = d.num(1);
            let body = d.bool_select_nat(ci, zero, one_lit);
            d.lam_fv(i_fv, nat, body)
        };
        let body = d.const_app(p.prod_range, &[f, n]);
        let value = {
            let with_n = d.lam_fv(n_fv, nat, body);
            d.lam_fv(c_fv, cty, with_n)
        };
        let ty = {
            let inner = d.arrow(nat, nat);
            d.arrow(cty, inner)
        };
        d.kernel().add_declaration(Declaration::Definition {
            name: p.subsets_none_of,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(31),
        })?;
    }

    // prodPar : (Nat -> Bool) -> Nat -> Bool -> Nat
    //   | c 0        b = if b then 1 else 0
    //   | c (succ m) b = prodPar c m b + prodPar c m (notB b) * (if c m then 1 else 0)
    {
        let c_fv = d.fresh_fvar();
        let c = d.kernel().fvar(c_fv);
        let carrier = d.arrow(bool_ty, nat);
        let motive = d.kernel().lam(anon, nat, carrier, BinderInfo::Default);
        let base = {
            let b_fv = d.fresh_fvar();
            let b = d.kernel().fvar(b_fv);
            let one_lit = d.num(1);
            let zero = d.zero();
            let body = d.bool_select_nat(b, one_lit, zero);
            d.lam_fv(b_fv, bool_ty, body)
        };
        let step = {
            let m_fv = d.fresh_fvar();
            let m = d.kernel().fvar(m_fv);
            let ih_fv = d.fresh_fvar();
            let ih = d.kernel().fvar(ih_fv);
            let b_fv = d.fresh_fvar();
            let b = d.kernel().fvar(b_fv);
            let left = d.apply(ih, &[b]);
            let flipped = not_b(d, &p, b);
            let other = d.apply(ih, &[flipped]);
            let cm = d.apply(c, &[m]);
            let one_lit = d.num(1);
            let zero = d.zero();
            let ind = d.bool_select_nat(cm, one_lit, zero);
            let scaled = d.mul(other, ind);
            let body = d.add(left, scaled);
            let with_b = d.lam_fv(b_fv, bool_ty, body);
            let with_ih = d.lam_fv(ih_fv, carrier, with_b);
            d.lam_fv(m_fv, nat, with_ih)
        };
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let rec = d.kernel().const_(p.rec, vec![one]);
        let body = d.apply(rec, &[motive, base, step, n]);
        let value = {
            let with_n = d.lam_fv(n_fv, nat, body);
            d.lam_fv(c_fv, cty, with_n)
        };
        let ty = {
            let inner = d.arrow(nat, carrier);
            d.arrow(cty, inner)
        };
        d.kernel().add_declaration(Declaration::Definition {
            name: p.subsets_prod_par,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(32),
        })?;
    }

    // meetInd : (Nat -> Nat -> Bool) -> Nat -> (Nat -> Bool) -> Nat -> Nat
    //   := fun A n s v => prodRangeIf s (fun i => if A i v then 1 else 0) n
    {
        let a_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let s_fv = d.fresh_fvar();
        let s = d.kernel().fvar(s_fv);
        let v_fv = d.fresh_fvar();
        let v = d.kernel().fvar(v_fv);
        let f = ind_fn(d, a, v);
        let body = d.const_app(p.prod_range_if, &[s, f, n]);
        let value = {
            let with_v = d.lam_fv(v_fv, nat, body);
            let with_s = d.lam_fv(s_fv, cty, with_v);
            let with_n = d.lam_fv(n_fv, nat, with_s);
            d.lam_fv(a_fv, fam, with_n)
        };
        let ty = {
            let inner = d.arrow(nat, nat);
            let with_s = d.arrow(cty, inner);
            let with_n = d.arrow(nat, with_s);
            d.arrow(fam, with_n)
        };
        d.kernel().add_declaration(Declaration::Definition {
            name: p.subsets_meet_ind,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(33),
        })?;
    }

    // meetCard : (Nat -> Nat -> Bool) -> Nat -> (Nat -> Bool) -> Nat -> Nat
    //   := fun A n s m => sumRange (fun v => meetInd A n s v) m
    {
        let a_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let s_fv = d.fresh_fvar();
        let s = d.kernel().fvar(s_fv);
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let row = {
            let v_fv = d.fresh_fvar();
            let v = d.kernel().fvar(v_fv);
            let body = meet_ind(d, &p, a, n, s, v);
            d.lam_fv(v_fv, nat, body)
        };
        let body = d.sum_range(row, m);
        let value = {
            let with_m = d.lam_fv(m_fv, nat, body);
            let with_s = d.lam_fv(s_fv, cty, with_m);
            let with_n = d.lam_fv(n_fv, nat, with_s);
            d.lam_fv(a_fv, fam, with_n)
        };
        let ty = {
            let inner = d.arrow(nat, nat);
            let with_s = d.arrow(cty, inner);
            let with_n = d.arrow(nat, with_s);
            d.arrow(fam, with_n)
        };
        d.kernel().add_declaration(Declaration::Definition {
            name: p.subsets_meet_card,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(34),
        })?;
    }

    // unionAt : (Nat -> Nat -> Bool) -> Nat -> (Nat -> Bool)
    //   := fun A n v => anyOf (fun i => A i v) n
    {
        let a_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let v_fv = d.fresh_fvar();
        let v = d.kernel().fvar(v_fv);
        let slice = slice_fn(d, a, v);
        let body = any_of(d, &p, slice, n);
        let value = {
            let with_v = d.lam_fv(v_fv, nat, body);
            let with_n = d.lam_fv(n_fv, nat, with_v);
            d.lam_fv(a_fv, fam, with_n)
        };
        let ty = {
            let inner = d.arrow(nat, cty);
            d.arrow(fam, inner)
        };
        d.kernel().add_declaration(Declaration::Definition {
            name: p.subsets_union_at,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(35),
        })?;
    }

    // ieSum / ieSumPos : (Nat -> Nat -> Bool) -> Nat -> Nat -> Bool -> Nat
    for (name, pos) in [(p.subsets_ie_sum, false), (p.subsets_ie_sum_pos, true)] {
        let a_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let b_fv = d.fresh_fvar();
        let b = d.kernel().fvar(b_fv);
        let summand = card_at(d, &p, a, n, m);
        let body = if pos {
            sum_sel_pos(d, &p, n, summand, b)
        } else {
            sum_sel(d, &p, n, summand, b)
        };
        let value = {
            let with_b = d.lam_fv(b_fv, bool_ty, body);
            let with_m = d.lam_fv(m_fv, nat, with_b);
            let with_n = d.lam_fv(n_fv, nat, with_m);
            d.lam_fv(a_fv, fam, with_n)
        };
        let ty = {
            let inner = d.arrow(bool_ty, nat);
            let with_m = d.arrow(nat, inner);
            let with_n = d.arrow(nat, with_m);
            d.arrow(fam, with_n)
        };
        d.kernel().add_declaration(Declaration::Definition {
            name,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(36),
        })?;
    }

    Ok(())
}

// ---------------------------------------------------------------------------
// The unfolding equations.
// ---------------------------------------------------------------------------

fn declare_equations(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let bool_ty = d.bool_ty();
    let cty = set_ty(d);

    // anyOf_succ : forall c n, anyOf c (succ n) = if anyOf c n then true else c n
    {
        let c_fv = d.fresh_fvar();
        let c = d.kernel().fvar(c_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let sn = d.succ(n);
        let lhs = any_of(d, &p, c, sn);
        let lower = any_of(d, &p, c, n);
        let tv = d.bool_true();
        let cn = d.apply(c, &[n]);
        let rhs = bool_select_bool(d, &p, lower, tv, cn);
        let concl = d.bool_eq(lhs, rhs);
        let ty = {
            let with_n = d.pi_fv(n_fv, nat, concl);
            d.pi_fv(c_fv, cty, with_n)
        };
        let proof = d.bool_refl(lhs);
        let value = {
            let with_n = d.lam_fv(n_fv, nat, proof);
            d.lam_fv(c_fv, cty, with_n)
        };
        d.declare_theorem(p.subsets_any_of_succ, ty, value)?;
    }

    // prodPar_succ : forall c n b,
    //   prodPar c (succ n) b = prodPar c n b + prodPar c n (notB b) * (if c n then 1 else 0)
    {
        let c_fv = d.fresh_fvar();
        let c = d.kernel().fvar(c_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let b_fv = d.fresh_fvar();
        let b = d.kernel().fvar(b_fv);
        let sn = d.succ(n);
        let lhs = prod_par(d, &p, c, sn, b);
        let low = prod_par(d, &p, c, n, b);
        let flipped = not_b(d, &p, b);
        let other = prod_par(d, &p, c, n, flipped);
        let cn = d.apply(c, &[n]);
        let one_lit = d.num(1);
        let zero = d.zero();
        let ind = d.bool_select_nat(cn, one_lit, zero);
        let scaled = d.mul(other, ind);
        let rhs = d.add(low, scaled);
        let concl = d.eq(lhs, rhs);
        let ty = {
            let with_b = d.pi_fv(b_fv, bool_ty, concl);
            let with_n = d.pi_fv(n_fv, nat, with_b);
            d.pi_fv(c_fv, cty, with_n)
        };
        let proof = d.refl(lhs);
        let value = {
            let with_b = d.lam_fv(b_fv, bool_ty, proof);
            let with_n = d.lam_fv(n_fv, nat, with_b);
            d.lam_fv(c_fv, cty, with_n)
        };
        d.declare_theorem(p.subsets_prod_par_succ, ty, value)?;
    }

    Ok(())
}

// ---------------------------------------------------------------------------
// `noneOf` is the indicator of "no member".
// ---------------------------------------------------------------------------

/// `Nat.Subsets.noneOf_eq : ∀ c n,
/// noneOf c n = bool_select_nat (anyOf c n) 0 1`.
fn declare_none_of_eq(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let cty = set_ty(d);

    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);

    let motive_at = |d: &mut NatDev<'_>, n: ExprId| -> ExprId {
        let lhs = none_of(d, &p, c, n);
        let any = any_of(d, &p, c, n);
        let zero = d.zero();
        let one_lit = d.num(1);
        let rhs = d.bool_select_nat(any, zero, one_lit);
        d.eq(lhs, rhs)
    };

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let body = d.induct(
        &|d, x| motive_at(d, x),
        &|d| {
            let one_lit = d.num(1);
            d.refl(one_lit)
        },
        &|d, j, ih| {
            // `noneOf c (succ j) = noneOf c j * (if c j then 0 else 1)`.
            let low = none_of(d, &p, c, j);
            let cj = d.apply(c, &[j]);
            let zero = d.zero();
            let one_lit = d.num(1);
            let tail = d.bool_select_nat(cj, zero, one_lit);
            let product = d.mul(low, tail);
            let sj0 = d.succ(j);
            let start = none_of(d, &p, c, sj0);
            let unfold = d.refl(start);

            // Rewrite the head by the induction hypothesis.
            let any_j = any_of(d, &p, c, j);
            let zero2 = d.zero();
            let one2 = d.num(1);
            let head = d.bool_select_nat(any_j, zero2, one2);
            let rewritten = d.congr(low, head, ih, &|d, x| d.mul(x, tail));
            let mid = d.mul(head, tail);

            // Split on `anyOf c j`, then on `c j` inside the `false` branch.
            let sj = d.succ(j);
            let any_sj = any_of(d, &p, c, sj);
            let zero3 = d.zero();
            let one3 = d.num(1);
            let target = d.bool_select_nat(any_sj, zero3, one3);
            let goal = d.eq(mid, target);

            let tv = d.bool_true();
            let fal = d.bool_false();
            let is_true = d.bool_eq(any_j, tv);
            let is_false = d.bool_eq(any_j, fal);
            let decided = bool_true_or_false(d, &p, any_j);

            // At `anyOf c j = true`: the head is `0`, so the product is `0`,
            // and `anyOf c (succ j)` is `true` too.
            let on_true = {
                let h_fv = d.fresh_fvar();
                let h = d.kernel().fvar(h_fv);
                let step = bool_to_nat_congr(d, any_j, tv, h, &|d, x| {
                    let zero = d.zero();
                    let one_lit = d.num(1);
                    let sel = d.bool_select_nat(x, zero, one_lit);
                    d.mul(sel, tail)
                });
                // `0 * tail = 0`.
                let zeroed = d.lemma(p.zero_mul, &[tail]);
                let zero_l = d.zero();
                let zero_prod = d.mul(zero_l, tail);
                let z = d.zero();
                let collapse = d.trans(mid, zero_prod, z, step, zeroed);
                // `0 = if anyOf c (succ j) then 0 else 1` — the `true` branch
                // travels back through `anyOf_succ`.
                let sym_t = d.bool_symm(any_j, tv, h);
                let back = bool_to_nat_congr(d, tv, any_j, sym_t, &|d, x| {
                    let tv2 = d.bool_true();
                    let cj2 = d.apply(c, &[j]);
                    let inner = bool_select_bool(d, &p, x, tv2, cj2);
                    let zero = d.zero();
                    let one_lit = d.num(1);
                    d.bool_select_nat(inner, zero, one_lit)
                });
                let proof = d.trans(mid, z, target, collapse, back);
                d.lam_fv(h_fv, is_true, proof)
            };

            // At `anyOf c j = false`: the head is `1`, the product is `tail`,
            // and `anyOf c (succ j)` is `c j`.
            let on_false = {
                let h_fv = d.fresh_fvar();
                let h = d.kernel().fvar(h_fv);
                let step = bool_to_nat_congr(d, any_j, fal, h, &|d, x| {
                    let zero = d.zero();
                    let one_lit = d.num(1);
                    let sel = d.bool_select_nat(x, zero, one_lit);
                    d.mul(sel, tail)
                });
                let one_l = d.num(1);
                let one_prod = d.mul(one_l, tail);
                let unit = d.lemma(p.one_mul, &[tail]);
                let collapse = d.trans(mid, one_prod, tail, step, unit);
                let sym_f = d.bool_symm(any_j, fal, h);
                let back = bool_to_nat_congr(d, fal, any_j, sym_f, &|d, x| {
                    let tv2 = d.bool_true();
                    let cj2 = d.apply(c, &[j]);
                    let inner = bool_select_bool(d, &p, x, tv2, cj2);
                    let zero = d.zero();
                    let one_lit = d.num(1);
                    d.bool_select_nat(inner, zero, one_lit)
                });
                let proof = d.trans(mid, tail, target, collapse, back);
                d.lam_fv(h_fv, is_false, proof)
            };

            let split = or_elim(d, &p, is_true, is_false, goal, on_true, on_false, decided);
            let s1 = d.trans(start, product, mid, unfold, rewritten);
            d.trans(start, mid, target, s1, split)
        },
        n,
    );

    let stmt = motive_at(d, n);
    let ty = {
        let with_n = d.pi_fv(n_fv, nat, stmt);
        d.pi_fv(c_fv, cty, with_n)
    };
    let value = {
        let with_n = d.lam_fv(n_fv, nat, body);
        d.lam_fv(c_fv, cty, with_n)
    };
    d.declare_theorem(p.subsets_none_of_eq, ty, value)
}

// ---------------------------------------------------------------------------
// The product expansion's alternating identity.
// ---------------------------------------------------------------------------

/// `Nat.Subsets.prodPar_even : ∀ c n,
/// prodPar c n true = prodPar c n false + noneOf c n`.
///
/// The whole of inclusion–exclusion, before it is summed over the ambient
/// range. The induction step is one `Bool` dichotomy on `c n`: when the new
/// element is IN, the residue `noneOf` is multiplied by `0` and the two graded
/// halves exchange; when it is OUT, both halves are unchanged and so is the
/// residue.
fn declare_prod_par_even(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let cty = set_ty(d);

    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);

    let motive_at = |d: &mut NatDev<'_>, n: ExprId| -> ExprId {
        let tv = d.bool_true();
        let fal = d.bool_false();
        let lhs = prod_par(d, &p, c, n, tv);
        let odd = prod_par(d, &p, c, n, fal);
        let residue = none_of(d, &p, c, n);
        let rhs = d.add(odd, residue);
        d.eq(lhs, rhs)
    };

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let body = d.induct(
        &|d, x| motive_at(d, x),
        &|d| {
            // `1 = 0 + 1`.
            let one_lit = d.num(1);
            let za = d.lemma(p.zero_add, &[one_lit]);
            let zero = d.zero();
            let one2 = d.num(1);
            let sum = d.add(zero, one2);
            let one3 = d.num(1);
            d.symm(sum, one3, za)
        },
        &|d, j, ih| {
            let tv = d.bool_true();
            let fal = d.bool_false();
            let even = prod_par(d, &p, c, j, tv);
            let odd = prod_par(d, &p, c, j, fal);
            let residue = none_of(d, &p, c, j);
            let cj = d.apply(c, &[j]);

            let sj = d.succ(j);
            let start = prod_par(d, &p, c, sj, tv);
            let target = {
                let odd_s = prod_par(d, &p, c, sj, fal);
                let res_s = none_of(d, &p, c, sj);
                d.add(odd_s, res_s)
            };
            let goal = d.eq(start, target);

            // `start ≡ even + odd * g` and `target ≡ (odd + even * g) + residue * h`.
            let is_true = d.bool_eq(cj, tv);
            let is_false = d.bool_eq(cj, fal);
            let decided = bool_true_or_false(d, &p, cj);

            // At `c j = true`: `g = 1`, `h = 0`, so the claim is
            // `even + odd * 1 = (odd + even * 1) + residue * 0`.
            let on_true = {
                let hb_fv = d.fresh_fvar();
                let hb = d.kernel().fvar(hb_fv);
                let goal_at = |d: &mut NatDev<'_>, x: ExprId| -> ExprId {
                    let one_lit = d.num(1);
                    let zero = d.zero();
                    let gg = d.bool_select_nat(x, one_lit, zero);
                    let zero_b = d.zero();
                    let one_b = d.num(1);
                    let hh = d.bool_select_nat(x, zero_b, one_b);
                    let lhs = {
                        let scaled = d.mul(odd, gg);
                        d.add(even, scaled)
                    };
                    let rhs = {
                        let scaled = d.mul(even, gg);
                        let inner = d.add(odd, scaled);
                        let res = d.mul(residue, hh);
                        d.add(inner, res)
                    };
                    d.eq(lhs, rhs)
                };
                let motive = d.bool_eq_motive(tv, &|d, x| goal_at(d, x));
                let refl_case = {
                    // `even + odd * 1 = (odd + even * 1) + residue * 0`.
                    let one_lit = d.num(1);
                    let odd_one = d.mul(odd, one_lit);
                    let unit_o = d.lemma(p.mul_one, &[odd]);
                    let lhs0 = d.add(even, odd_one);
                    let lhs1 = d.add(even, odd);
                    let e1 = d.congr(odd_one, odd, unit_o, &|d, x| d.add(even, x));
                    let comm = d.lemma(p.add_comm, &[even, odd]);
                    let rhs1 = d.add(odd, even);
                    let e2 = d.trans(lhs0, lhs1, rhs1, e1, comm);
                    // `odd + even = (odd + even * 1) + residue * 0`.
                    let one2 = d.num(1);
                    let even_one = d.mul(even, one2);
                    let unit_e = d.lemma(p.mul_one, &[even]);
                    let back_e = d.symm(even_one, even, unit_e);
                    let rhs2 = d.add(odd, even_one);
                    let e3 = d.congr(even, even_one, back_e, &|d, x| d.add(odd, x));
                    let zero_l = d.zero();
                    let res_zero = d.mul(residue, zero_l);
                    let vanish = d.lemma(p.mul_zero, &[residue]);
                    let zero_r = d.zero();
                    let plus_zero = d.lemma(p.add_zero, &[rhs2]);
                    let rhs3 = d.add(rhs2, zero_r);
                    let e4 = d.symm(rhs3, rhs2, plus_zero);
                    let rhs4 = d.add(rhs2, res_zero);
                    let widen_r = d.symm(res_zero, zero_r, vanish);
                    let e5 = d.congr(zero_r, res_zero, widen_r, &|d, x| d.add(rhs2, x));
                    let s1 = d.trans(lhs0, rhs1, rhs2, e2, e3);
                    let s2 = d.trans(lhs0, rhs2, rhs3, s1, e4);
                    d.trans(lhs0, rhs3, rhs4, s2, e5)
                };
                let back = d.bool_symm(cj, tv, hb);
                let proof = d.bool_transport(tv, motive, refl_case, cj, back);
                d.lam_fv(hb_fv, is_true, proof)
            };

            // At `c j = false`: `g = 0`, `h = 1`, so the claim is
            // `even + odd * 0 = (odd + even * 0) + residue * 1`, i.e. the
            // induction hypothesis with two `add_zero`s and a `mul_one`.
            let on_false = {
                let hb_fv = d.fresh_fvar();
                let hb = d.kernel().fvar(hb_fv);
                let goal_at = |d: &mut NatDev<'_>, x: ExprId| -> ExprId {
                    let one_lit = d.num(1);
                    let zero = d.zero();
                    let gg = d.bool_select_nat(x, one_lit, zero);
                    let zero_b = d.zero();
                    let one_b = d.num(1);
                    let hh = d.bool_select_nat(x, zero_b, one_b);
                    let lhs = {
                        let scaled = d.mul(odd, gg);
                        d.add(even, scaled)
                    };
                    let rhs = {
                        let scaled = d.mul(even, gg);
                        let inner = d.add(odd, scaled);
                        let res = d.mul(residue, hh);
                        d.add(inner, res)
                    };
                    d.eq(lhs, rhs)
                };
                let motive = d.bool_eq_motive(fal, &|d, x| goal_at(d, x));
                let refl_case = {
                    // `even + odd * 0 = even`.
                    let zero_l = d.zero();
                    let odd_zero = d.mul(odd, zero_l);
                    let vanish_o = d.lemma(p.mul_zero, &[odd]);
                    let lhs0 = d.add(even, odd_zero);
                    let zero_r = d.zero();
                    let lhs1 = d.add(even, zero_r);
                    let e1 = d.congr(odd_zero, zero_r, vanish_o, &|d, x| d.add(even, x));
                    let e2 = d.lemma(p.add_zero, &[even]);
                    let s1 = d.trans(lhs0, lhs1, even, e1, e2);
                    // `even = odd + residue` is the hypothesis.
                    let odd_plus = d.add(odd, residue);
                    let s2 = d.trans(lhs0, even, odd_plus, s1, ih);
                    // `odd + residue = (odd + even * 0) + residue * 1`.
                    let zero_2 = d.zero();
                    let even_zero = d.mul(even, zero_2);
                    let vanish_e = d.lemma(p.mul_zero, &[even]);
                    let zero_3 = d.zero();
                    let back_e = d.symm(even_zero, zero_3, vanish_e);
                    let odd_z = d.add(odd, zero_3);
                    let plus_zero_odd = d.lemma(p.add_zero, &[odd]);
                    let widen_odd = d.symm(odd_z, odd, plus_zero_odd);
                    let odd_ez = d.add(odd, even_zero);
                    let back_e2 = d.symm(even_zero, zero_3, back_e);
                    let widen2 = d.congr(zero_3, even_zero, back_e2, &|d, x| d.add(odd, x));
                    let one_2 = d.num(1);
                    let res_one = d.mul(residue, one_2);
                    let unit_r = d.lemma(p.mul_one, &[residue]);
                    let back_r = d.symm(res_one, residue, unit_r);
                    let target1 = d.add(odd_ez, residue);
                    let target2 = d.add(odd_ez, res_one);
                    let widen_all = d.trans(odd, odd_z, odd_ez, widen_odd, widen2);
                    let e3 = add_congr(d, odd, odd_ez, widen_all, residue, res_one, back_r);
                    let _ = target1;
                    d.trans(lhs0, odd_plus, target2, s2, e3)
                };
                let back = d.bool_symm(cj, fal, hb);
                let proof = d.bool_transport(fal, motive, refl_case, cj, back);
                d.lam_fv(hb_fv, is_false, proof)
            };

            or_elim(d, &p, is_true, is_false, goal, on_true, on_false, decided)
        },
        n,
    );

    let stmt = motive_at(d, n);
    let ty = {
        let with_n = d.pi_fv(n_fv, nat, stmt);
        d.pi_fv(c_fv, cty, with_n)
    };
    let value = {
        let with_n = d.lam_fv(n_fv, nat, body);
        d.lam_fv(c_fv, cty, with_n)
    };
    d.declare_theorem(p.subsets_prod_par_even, ty, value)
}

// ---------------------------------------------------------------------------
// The per-element identity: at a fixed ambient element the subset sum IS the
// product expansion.
// ---------------------------------------------------------------------------

/// `Nat.Subsets.prodRange_one : ∀ n, prodRange (fun _ => 1) n = 1`.
fn declare_prod_range_one(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();

    let ones = |d: &mut NatDev<'_>| -> ExprId {
        let nat = d.nat_ty();
        let anon = d.anon_name();
        let one = d.num(1);
        d.kernel().lam(anon, nat, one, BinderInfo::Default)
    };

    let motive_at = |d: &mut NatDev<'_>, n: ExprId| -> ExprId {
        let f = ones(d);
        let lhs = d.const_app(p.prod_range, &[f, n]);
        let one = d.num(1);
        d.eq(lhs, one)
    };

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let body = d.induct(
        &|d, x| motive_at(d, x),
        &|d| {
            let one = d.num(1);
            d.refl(one)
        },
        &|d, j, ih| {
            let f = ones(d);
            let sj = d.succ(j);
            let start = d.const_app(p.prod_range, &[f, sj]);
            let low = d.const_app(p.prod_range, &[f, j]);
            let one = d.num(1);
            let mid = d.mul(low, one);
            let unfold = d.lemma(p.prod_range_succ, &[f, j]);
            let one_b = d.num(1);
            let stop = d.mul(one_b, one_b);
            let collapse = d.congr(low, one_b, ih, &|d, x| {
                let one_c = d.num(1);
                d.mul(x, one_c)
            });
            d.trans(start, mid, stop, unfold, collapse)
        },
        n,
    );

    let stmt = motive_at(d, n);
    let ty = d.pi_fv(n_fv, nat, stmt);
    let value = d.lam_fv(n_fv, nat, body);
    d.declare_theorem(p.subsets_prod_range_one, ty, value)
}

/// `Nat.Subsets.meetCard_empty : ∀ A n m, meetCard A n empty m = m` — the
/// intersection over NO members is the whole ambient range.
fn declare_meet_card_empty(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let fam = family_ty(d);

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);

    let e = empty_set(d, &p);
    let start = meet_card(d, &p, a, n, e, m);

    let row = {
        let v_fv = d.fresh_fvar();
        let v = d.kernel().fvar(v_fv);
        let body = meet_ind(d, &p, a, n, e, v);
        d.lam_fv(v_fv, nat, body)
    };
    let ones = {
        let anon = d.anon_name();
        let one = d.num(1);
        d.kernel().lam(anon, nat, one, BinderInfo::Default)
    };
    let pointwise = {
        let v_fv = d.fresh_fvar();
        let body = d.lemma(p.subsets_prod_range_one, &[n]);
        d.lam_fv(v_fv, nat, body)
    };
    let flatten = d.lemma(p.sum_range_congr, &[row, ones, m, pointwise]);
    let all_ones = d.sum_range(ones, m);
    let one = d.num(1);
    let counted = d.lemma(p.sum_range_const, &[one, m]);
    let scaled = d.mul(one, m);
    let unit = d.lemma(p.one_mul, &[m]);

    let s1 = d.trans(start, all_ones, scaled, flatten, counted);
    let proof = d.trans(start, scaled, m, s1, unit);

    let concl = d.eq(start, m);
    let ty = {
        let with_m = d.pi_fv(m_fv, nat, concl);
        let with_n = d.pi_fv(n_fv, nat, with_m);
        d.pi_fv(a_fv, fam, with_n)
    };
    let value = {
        let with_m = d.lam_fv(m_fv, nat, proof);
        let with_n = d.lam_fv(n_fv, nat, with_m);
        d.lam_fv(a_fv, fam, with_n)
    };
    d.declare_theorem(p.subsets_meet_card_empty, ty, value)
}

/// `Nat.Subsets.sumSel_meetInd : ∀ A n b v,
/// sumSel n (fun s => meetInd A n s v) b = prodPar (fun i => A i v) n b`.
///
/// The step consumes `sumSel_congr` twice — once to drop the new element's
/// factor from the sets that do NOT contain it (this is where `Supported` is
/// spent), once to expose it as a scalar on the sets that do — and then
/// `sumSel_mul_right` pulls the scalar out. What is left matches `prodPar`'s
/// own recursion by `Eq.refl`.
fn declare_sum_sel_meet_ind(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let bool_ty = d.bool_ty();
    let cty = set_ty(d);
    let fam = family_ty(d);

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);

    let motive_at = |d: &mut NatDev<'_>, n: ExprId| -> ExprId {
        let b_fv = d.fresh_fvar();
        let b = d.kernel().fvar(b_fv);
        let v_fv = d.fresh_fvar();
        let v = d.kernel().fvar(v_fv);
        let summand = meet_at(d, &p, a, n, v);
        let lhs = sum_sel(d, &p, n, summand, b);
        let slice = slice_fn(d, a, v);
        let rhs = prod_par(d, &p, slice, n, b);
        let concl = d.eq(lhs, rhs);
        let with_v = d.pi_fv(v_fv, nat, concl);
        d.pi_fv(b_fv, bool_ty, with_v)
    };

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let body = d.induct(
        &|d, x| motive_at(d, x),
        &|d| {
            // `sumSel 0 F b ≡ if b then 1 else 0 ≡ prodPar c 0 b`.
            let b_fv = d.fresh_fvar();
            let b = d.kernel().fvar(b_fv);
            let v_fv = d.fresh_fvar();
            let v = d.kernel().fvar(v_fv);
            let zero = d.zero();
            let summand = meet_at(d, &p, a, zero, v);
            let lhs = sum_sel(d, &p, zero, summand, b);
            let proof = d.refl(lhs);
            let with_v = d.lam_fv(v_fv, nat, proof);
            d.lam_fv(b_fv, bool_ty, with_v)
        },
        &|d, j, ih| {
            let b_fv = d.fresh_fvar();
            let b = d.kernel().fvar(b_fv);
            let v_fv = d.fresh_fvar();
            let v = d.kernel().fvar(v_fv);
            let sj = d.succ(j);
            let flipped = not_b(d, &p, b);

            let wide = meet_at(d, &p, a, sj, v);
            let narrow = meet_at(d, &p, a, j, v);
            let indf = ind_fn(d, a, v);
            let gj = d.apply(indf, &[j]);

            // The low half: on a set supported below `j`, the extra factor is
            // `1`, so the width can be narrowed.
            let low_agree = {
                let s_fv = d.fresh_fvar();
                let s = d.kernel().fvar(s_fv);
                let sup = supported(d, &p, s, j);
                let hs_fv = d.fresh_fvar();
                let hs = d.kernel().fvar(hs_fv);

                let start = meet_ind(d, &p, a, sj, s, v);
                let base = d.const_app(p.prod_range_if, &[s, indf, j]);
                let unfold = d.lemma(p.prod_range_if_succ, &[s, indf, j]);
                let sj_mem = d.apply(s, &[j]);
                let one_lit = d.num(1);
                let factor = d.bool_select_nat(sj_mem, gj, one_lit);
                let mid = d.mul(base, factor);

                let refl_j = d.lemma(p.le_refl, &[j]);
                let is_out = d.apply(hs, &[j, refl_j]);
                let fal = d.bool_false();
                let drop = bool_to_nat_congr(d, sj_mem, fal, is_out, &|d, x| {
                    let one_c = d.num(1);
                    let sel = d.bool_select_nat(x, gj, one_c);
                    d.mul(base, sel)
                });
                let one_b = d.num(1);
                let mid2 = d.mul(base, one_b);
                let unit = d.lemma(p.mul_one, &[base]);

                let s1 = d.trans(start, mid, mid2, unfold, drop);
                let proof = d.trans(start, mid2, base, s1, unit);
                let with_hs = d.lam_fv(hs_fv, sup, proof);
                d.lam_fv(s_fv, cty, with_hs)
            };
            let low = d.lemma(p.subsets_sum_sel_congr, &[j, wide, narrow, b, low_agree]);
            let low_ih = d.apply(ih, &[b, v]);
            let slice = slice_fn(d, a, v);
            let low_val = prod_par(d, &p, slice, j, b);
            let a1 = sum_sel(d, &p, j, wide, b);
            let a1_mid = sum_sel(d, &p, j, narrow, b);
            let low_proof = d.trans(a1, a1_mid, low_val, low, low_ih);

            // The high half: on `insertAt j s` the extra factor is the new
            // element's indicator, and it comes out as a scalar.
            let scaled = {
                let s_fv = d.fresh_fvar();
                let s = d.kernel().fvar(s_fv);
                let inner = meet_ind(d, &p, a, j, s, v);
                let body = d.mul(inner, gj);
                d.lam_fv(s_fv, cty, body)
            };
            let wide_top = with_top(d, &p, wide, j);
            let high_agree = {
                let s_fv = d.fresh_fvar();
                let s = d.kernel().fvar(s_fv);
                let sup = supported(d, &p, s, j);
                let hs_fv = d.fresh_fvar();

                let ins = insert_at(d, &p, j, s);
                let start = meet_ind(d, &p, a, sj, ins, v);
                let base = d.const_app(p.prod_range_if, &[ins, indf, j]);
                let unfold = d.lemma(p.prod_range_if_succ, &[ins, indf, j]);
                let ins_j = d.apply(ins, &[j]);
                let one_lit = d.num(1);
                let factor = d.bool_select_nat(ins_j, gj, one_lit);
                let mid = d.mul(base, factor);

                // `insertAt j s j = true`, by `beq_refl`.
                let tv = d.bool_true();
                let beq_jj = d.beq(j, j);
                let refl_beq = d.lemma(p.beq_refl, &[j]);
                let back_beq = d.bool_symm(beq_jj, tv, refl_beq);
                let sj_val = d.apply(s, &[j]);
                let motive = d.bool_eq_motive(tv, &|d, x| {
                    let tv2 = d.bool_true();
                    let sel = bool_select_bool(d, &p, x, tv2, sj_val);
                    let tv3 = d.bool_true();
                    d.bool_eq(sel, tv3)
                });
                let refl_case = d.bool_refl(tv);
                let is_in = d.bool_transport(tv, motive, refl_case, beq_jj, back_beq);

                let expose = bool_to_nat_congr(d, ins_j, tv, is_in, &|d, x| {
                    let one_c = d.num(1);
                    let sel = d.bool_select_nat(x, gj, one_c);
                    d.mul(base, sel)
                });
                let mid2 = d.mul(base, gj);

                // `prodRangeIf (insertAt j s) indf j = prodRangeIf s indf j`.
                let pred_agree = {
                    let i_fv = d.fresh_fvar();
                    let i = d.kernel().fvar(i_fv);
                    let hlt_ty = d.lt(i, j);
                    let hlt_fv = d.fresh_fvar();
                    let hlt = d.kernel().fvar(hlt_fv);
                    let ne_proof = {
                        let he_fv = d.fresh_fvar();
                        let he = d.kernel().fvar(he_fv);
                        let he_ty = d.eq(i, j);
                        let motive = d.eq_motive(i, &|d, x| d.lt(x, j));
                        let moved = d.transport(i, motive, hlt, j, he);
                        let absurd = d.lemma(p.lt_irrefl, &[j, moved]);
                        d.lam_fv(he_fv, he_ty, absurd)
                    };
                    let beq_false = d.lemma(p.beq_eq_false_of_ne, &[i, j, ne_proof]);
                    let cond = d.beq(i, j);
                    let tv2 = d.bool_true();
                    let si = d.apply(s, &[i]);
                    let sel = bool_select_bool(d, &p, cond, tv2, si);
                    let fal = d.bool_false();
                    let back = d.bool_symm(cond, fal, beq_false);
                    let motive = d.bool_eq_motive(fal, &|d, x| {
                        let tv3 = d.bool_true();
                        let inner = bool_select_bool(d, &p, x, tv3, si);
                        d.bool_eq(inner, si)
                    });
                    let refl_case = d.bool_refl(si);
                    let body = d.bool_transport(fal, motive, refl_case, cond, back);
                    let _ = sel;
                    let with_hlt = d.lam_fv(hlt_fv, hlt_ty, body);
                    d.lam_fv(i_fv, nat, with_hlt)
                };
                let fun_agree = {
                    let i_fv = d.fresh_fvar();
                    let i = d.kernel().fvar(i_fv);
                    let hlt_ty = d.lt(i, j);
                    let hlt_fv = d.fresh_fvar();
                    let at_i = d.apply(indf, &[i]);
                    let body = d.refl(at_i);
                    let with_hlt = d.lam_fv(hlt_fv, hlt_ty, body);
                    d.lam_fv(i_fv, nat, with_hlt)
                };
                let narrow_base = d.const_app(p.prod_range_if, &[s, indf, j]);
                let same = d.lemma(
                    p.prod_range_if_congr_lt,
                    &[ins, s, indf, indf, j, pred_agree, fun_agree],
                );
                let mid3 = d.mul(narrow_base, gj);
                let rebase = d.congr(base, narrow_base, same, &|d, x| d.mul(x, gj));

                let s1 = d.trans(start, mid, mid2, unfold, expose);
                let proof = d.trans(start, mid2, mid3, s1, rebase);
                let with_hs = d.lam_fv(hs_fv, sup, proof);
                d.lam_fv(s_fv, cty, with_hs)
            };
            let high = d.lemma(
                p.subsets_sum_sel_congr,
                &[j, wide_top, scaled, flipped, high_agree],
            );
            let pull = d.lemma(p.subsets_sum_sel_mul_right, &[j, narrow, gj, flipped]);
            let high_ih = d.apply(ih, &[flipped, v]);
            let a2 = sum_sel(d, &p, j, wide_top, flipped);
            let a2_mid = sum_sel(d, &p, j, scaled, flipped);
            let a2_mid2 = {
                let inner = sum_sel(d, &p, j, narrow, flipped);
                d.mul(inner, gj)
            };
            let high_val = {
                let inner = prod_par(d, &p, slice, j, flipped);
                d.mul(inner, gj)
            };
            let h1 = d.trans(a2, a2_mid, a2_mid2, high, pull);
            let inner_lhs = sum_sel(d, &p, j, narrow, flipped);
            let inner_rhs = prod_par(d, &p, slice, j, flipped);
            let scale_ih = d.congr(inner_lhs, inner_rhs, high_ih, &|d, x| d.mul(x, gj));
            let high_proof = d.trans(a2, a2_mid2, high_val, h1, scale_ih);

            let proof = add_congr(d, a1, low_val, low_proof, a2, high_val, high_proof);
            let with_v = d.lam_fv(v_fv, nat, proof);
            d.lam_fv(b_fv, bool_ty, with_v)
        },
        n,
    );

    let stmt = motive_at(d, n);
    let ty = {
        let with_n = d.pi_fv(n_fv, nat, stmt);
        d.pi_fv(a_fv, fam, with_n)
    };
    let value = {
        let with_n = d.lam_fv(n_fv, nat, body);
        d.lam_fv(a_fv, fam, with_n)
    };
    d.declare_theorem(p.subsets_sum_sel_meet_ind, ty, value)
}

// ---------------------------------------------------------------------------
// The theorem.
// ---------------------------------------------------------------------------

/// `ieSum A n m b = sumRange (fun v => prodPar (fun i => A i v) n b) m` —
/// swap, then replace each column by the product expansion.
fn ie_sum_as_range(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    a: ExprId,
    n: ExprId,
    m: ExprId,
    b: ExprId,
) -> (ExprId, ExprId) {
    let p = *p;
    let nat = d.nat_ty();
    let cty = set_ty(d);

    // `fun s v => meetInd A n s v`.
    let grid = {
        let s_fv = d.fresh_fvar();
        let s = d.kernel().fvar(s_fv);
        let v_fv = d.fresh_fvar();
        let v = d.kernel().fvar(v_fv);
        let body = meet_ind(d, &p, a, n, s, v);
        let with_v = d.lam_fv(v_fv, nat, body);
        d.lam_fv(s_fv, cty, with_v)
    };
    let swapped = d.lemma(p.subsets_sum_sel_swap, &[n, grid, b, m]);

    let columns = {
        let v_fv = d.fresh_fvar();
        let v = d.kernel().fvar(v_fv);
        let summand = meet_at(d, &p, a, n, v);
        let body = sum_sel(d, &p, n, summand, b);
        d.lam_fv(v_fv, nat, body)
    };
    let expansions = {
        let v_fv = d.fresh_fvar();
        let v = d.kernel().fvar(v_fv);
        let slice = slice_fn(d, a, v);
        let body = prod_par(d, &p, slice, n, b);
        d.lam_fv(v_fv, nat, body)
    };
    let pointwise = {
        let v_fv = d.fresh_fvar();
        let v = d.kernel().fvar(v_fv);
        let body = d.lemma(p.subsets_sum_sel_meet_ind, &[a, n, b, v]);
        d.lam_fv(v_fv, nat, body)
    };
    let replaced = d.lemma(p.sum_range_congr, &[columns, expansions, m, pointwise]);

    let start = ie_sum(d, &p, a, n, m, b);
    let mid = d.sum_range(columns, m);
    let stop = d.sum_range(expansions, m);
    let proof = d.trans(start, mid, stop, swapped, replaced);
    (proof, stop)
}

/// `Nat.Subsets.inclusion_exclusion` and `inclusion_exclusion_pos`.
fn declare_inclusion_exclusion(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let fam = family_ty(d);

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);

    let tv = d.bool_true();
    let fal = d.bool_false();
    let (even_range, even_sum) = ie_sum_as_range(d, &p, a, n, m, tv);
    let (odd_range, odd_sum) = ie_sum_as_range(d, &p, a, n, m, fal);

    // `sumRange (fun v => prodPar c_v n true) m
    //    = sumRange (fun v => prodPar c_v n false + noneOf c_v n) m`.
    let evens = {
        let v_fv = d.fresh_fvar();
        let v = d.kernel().fvar(v_fv);
        let slice = slice_fn(d, a, v);
        let body = prod_par(d, &p, slice, n, tv);
        d.lam_fv(v_fv, nat, body)
    };
    let odds = {
        let v_fv = d.fresh_fvar();
        let v = d.kernel().fvar(v_fv);
        let slice = slice_fn(d, a, v);
        let body = prod_par(d, &p, slice, n, fal);
        d.lam_fv(v_fv, nat, body)
    };
    let residues = {
        let v_fv = d.fresh_fvar();
        let v = d.kernel().fvar(v_fv);
        let slice = slice_fn(d, a, v);
        let body = none_of(d, &p, slice, n);
        d.lam_fv(v_fv, nat, body)
    };
    let merged = {
        let v_fv = d.fresh_fvar();
        let v = d.kernel().fvar(v_fv);
        let l = d.apply(odds, &[v]);
        let r = d.apply(residues, &[v]);
        let body = d.add(l, r);
        d.lam_fv(v_fv, nat, body)
    };
    let pointwise = {
        let v_fv = d.fresh_fvar();
        let v = d.kernel().fvar(v_fv);
        let slice = slice_fn(d, a, v);
        let body = d.lemma(p.subsets_prod_par_even, &[slice, n]);
        d.lam_fv(v_fv, nat, body)
    };
    let expand = d.lemma(p.sum_range_congr, &[evens, merged, m, pointwise]);
    let merged_sum = d.sum_range(merged, m);
    let split = d.lemma(p.sum_range_add, &[odds, residues, m]);
    let odd_total = d.sum_range(odds, m);
    let residue_total = d.sum_range(residues, m);
    let separated = d.add(odd_total, residue_total);

    // `sumRange (fun v => noneOf c_v n) m = countRange (setCompl (unionAt A n)) m`.
    let union_pred = union_at(d, &p, a, n);
    let compl = d.const_app(p.set_compl, &[union_pred]);
    let compl_ind = {
        let v_fv = d.fresh_fvar();
        let v = d.kernel().fvar(v_fv);
        let at_v = d.apply(compl, &[v]);
        let one = d.num(1);
        let zero = d.zero();
        let body = d.bool_select_nat(at_v, one, zero);
        d.lam_fv(v_fv, nat, body)
    };
    let residue_pointwise = {
        let v_fv = d.fresh_fvar();
        let v = d.kernel().fvar(v_fv);
        let slice = slice_fn(d, a, v);
        let start = none_of(d, &p, slice, n);
        let named = d.lemma(p.subsets_none_of_eq, &[slice, n]);
        let any = any_of(d, &p, slice, n);
        let zero = d.zero();
        let one = d.num(1);
        let mid = d.bool_select_nat(any, zero, one);

        // `if x then 0 else 1 = if (if x then false else true) then 1 else 0`,
        // by a `Bool` dichotomy whose two branches are both `refl`.
        let goal_at = |d: &mut NatDev<'_>, x: ExprId| -> ExprId {
            let zero = d.zero();
            let one = d.num(1);
            let lhs = d.bool_select_nat(x, zero, one);
            let fal2 = d.bool_false();
            let tv2 = d.bool_true();
            let flipped = bool_select_bool(d, &p, x, fal2, tv2);
            let one_b = d.num(1);
            let zero_b = d.zero();
            let rhs = d.bool_select_nat(flipped, one_b, zero_b);
            d.eq(lhs, rhs)
        };
        let tv2 = d.bool_true();
        let fal2 = d.bool_false();
        let is_true = d.bool_eq(any, tv2);
        let is_false = d.bool_eq(any, fal2);
        let decided = bool_true_or_false(d, &p, any);
        let goal = goal_at(d, any);
        let on_true = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let back = d.bool_symm(any, tv2, h);
            let motive = d.bool_eq_motive(tv2, &|d, x| goal_at(d, x));
            let zero_c = d.zero();
            let refl_case = d.refl(zero_c);
            let proof = d.bool_transport(tv2, motive, refl_case, any, back);
            d.lam_fv(h_fv, is_true, proof)
        };
        let on_false = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let back = d.bool_symm(any, fal2, h);
            let motive = d.bool_eq_motive(fal2, &|d, x| goal_at(d, x));
            let one_c = d.num(1);
            let refl_case = d.refl(one_c);
            let proof = d.bool_transport(fal2, motive, refl_case, any, back);
            d.lam_fv(h_fv, is_false, proof)
        };
        let flip = or_elim(d, &p, is_true, is_false, goal, on_true, on_false, decided);
        let stop = d.apply(compl_ind, &[v]);
        let body = d.trans(start, mid, stop, named, flip);
        d.lam_fv(v_fv, nat, body)
    };
    let as_compl = d.lemma(
        p.sum_range_congr,
        &[residues, compl_ind, m, residue_pointwise],
    );
    let compl_range = d.sum_range(compl_ind, m);
    let compl_count = d.const_app(p.count_range, &[compl, m]);
    let as_count = d.lemma(p.count_range_eq_sum_range, &[compl, m]);
    let back_count = d.symm(compl_count, compl_range, as_count);
    let residue_eq = d.trans(
        residue_total,
        compl_range,
        compl_count,
        as_compl,
        back_count,
    );

    // `ieSum A n m true = ieSum A n m false + countRange (setCompl U) m`.
    let ie_true = ie_sum(d, &p, a, n, m, tv);
    let ie_false = ie_sum(d, &p, a, n, m, fal);
    let back_odd = d.symm(ie_false, odd_sum, odd_range);
    let star_rhs = d.add(ie_false, compl_count);
    let regrouped = add_congr(
        d,
        odd_total,
        ie_false,
        back_odd,
        residue_total,
        compl_count,
        residue_eq,
    );
    let s1 = d.trans(ie_true, even_sum, merged_sum, even_range, expand);
    let s2 = d.trans(ie_true, merged_sum, separated, s1, split);
    let star = d.trans(ie_true, separated, star_rhs, s2, regrouped);

    // `ieSum true + countRange U m = ieSum false + m`.
    let union_count = d.const_app(p.count_range, &[union_pred, m]);
    let lift = d.congr(ie_true, star_rhs, star, &|d, x| d.add(x, union_count));
    let assoc = d.lemma(p.add_assoc, &[ie_false, compl_count, union_count]);
    let inner = d.add(compl_count, union_count);
    let inner_swapped = d.add(union_count, compl_count);
    let comm = d.lemma(p.add_comm, &[compl_count, union_count]);
    let swap = d.congr(inner, inner_swapped, comm, &|d, t| d.add(ie_false, t));
    let complete = d.lemma(p.count_range_compl, &[union_pred, m]);
    let close = d.congr(inner_swapped, m, complete, &|d, t| d.add(ie_false, t));

    let goal_lhs = d.add(ie_true, union_count);
    let mid1 = d.add(star_rhs, union_count);
    let mid2 = d.add(ie_false, inner);
    let mid3 = d.add(ie_false, inner_swapped);
    let goal_rhs = d.add(ie_false, m);
    let t1 = d.trans(goal_lhs, mid1, mid2, lift, assoc);
    let t2 = d.trans(goal_lhs, mid2, mid3, t1, swap);
    let main = d.trans(goal_lhs, mid3, goal_rhs, t2, close);

    let concl = d.eq(goal_lhs, goal_rhs);
    let ty = {
        let with_m = d.pi_fv(m_fv, nat, concl);
        let with_n = d.pi_fv(n_fv, nat, with_m);
        d.pi_fv(a_fv, fam, with_n)
    };
    let value = {
        let with_m = d.lam_fv(m_fv, nat, main);
        let with_n = d.lam_fv(n_fv, nat, with_m);
        d.lam_fv(a_fv, fam, with_n)
    };
    d.declare_theorem(p.subsets_inclusion_exclusion, ty, value)
}

/// `Nat.Subsets.inclusion_exclusion_pos : ∀ A n m,
/// countRange (unionAt A n) m + ieSumPos A n m true = ieSumPos A n m false`.
fn declare_inclusion_exclusion_pos(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let fam = family_ty(d);

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);

    let tv = d.bool_true();
    let fal = d.bool_false();
    let summand = card_at(d, &p, a, n, m);
    let ie_true = ie_sum(d, &p, a, n, m, tv);
    let ie_false = ie_sum(d, &p, a, n, m, fal);
    let pos_true = ie_sum_pos(d, &p, a, n, m, tv);
    let pos_false = ie_sum_pos(d, &p, a, n, m, fal);
    let union_pred = union_at(d, &p, a, n);
    let union_count = d.const_app(p.count_range, &[union_pred, m]);

    // `ieSum true = meetCard A n empty m + ieSumPos true = m + ieSumPos true`.
    let peel = d.lemma(p.subsets_sum_sel_true_split, &[n, summand]);
    let e = empty_set(d, &p);
    let at_empty = meet_card(d, &p, a, n, e, m);
    let empty_is_all = d.lemma(p.subsets_meet_card_empty, &[a, n, m]);
    let peeled = d.add(at_empty, pos_true);
    let normalised = d.add(m, pos_true);
    let fix_empty = d.congr(at_empty, m, empty_is_all, &|d, x| d.add(x, pos_true));
    let e1 = d.trans(ie_true, peeled, normalised, peel, fix_empty);
    let e2 = d.lemma(p.subsets_sum_sel_false_pos, &[n, summand]);

    let main = d.lemma(p.subsets_inclusion_exclusion, &[a, n, m]);

    // `m + (ieSumPos true + |U|) = m + ieSumPos false`.
    let pt_plus = d.add(pos_true, union_count);
    let assoc = d.lemma(p.add_assoc, &[m, pos_true, union_count]);
    let lhs_flat = d.add(normalised, union_count);
    let lhs_nested = d.add(m, pt_plus);
    let back_assoc = d.symm(lhs_flat, lhs_nested, assoc);
    let back_e1 = d.symm(ie_true, normalised, e1);
    let lift = d.congr(normalised, ie_true, back_e1, &|d, x| d.add(x, union_count));
    let ie_lhs = d.add(ie_true, union_count);
    let ie_rhs = d.add(ie_false, m);
    let fix_false = d.congr(ie_false, pos_false, e2, &|d, x| d.add(x, m));
    let pf_plus_m = d.add(pos_false, m);
    let comm = d.lemma(p.add_comm, &[pos_false, m]);
    let m_plus_pf = d.add(m, pos_false);

    let c1 = d.trans(lhs_nested, lhs_flat, ie_lhs, back_assoc, lift);
    let c2 = d.trans(lhs_nested, ie_lhs, ie_rhs, c1, main);
    let c3 = d.trans(lhs_nested, ie_rhs, pf_plus_m, c2, fix_false);
    let c4 = d.trans(lhs_nested, pf_plus_m, m_plus_pf, c3, comm);

    let cancelled = d.lemma(p.add_left_cancel, &[m, pt_plus, pos_false, c4]);
    let goal_lhs = d.add(union_count, pos_true);
    let flip = d.lemma(p.add_comm, &[union_count, pos_true]);
    let proof = d.trans(goal_lhs, pt_plus, pos_false, flip, cancelled);

    let concl = d.eq(goal_lhs, pos_false);
    let ty = {
        let with_m = d.pi_fv(m_fv, nat, concl);
        let with_n = d.pi_fv(n_fv, nat, with_m);
        d.pi_fv(a_fv, fam, with_n)
    };
    let value = {
        let with_m = d.lam_fv(m_fv, nat, proof);
        let with_n = d.lam_fv(n_fv, nat, with_m);
        d.lam_fv(a_fv, fam, with_n)
    };
    d.declare_theorem(p.subsets_inclusion_exclusion_pos, ty, value)
}

/// `Nat.Subsets.inclusion_exclusion_two : ∀ A m,
/// countRange (setUnion (A 0) (A 1)) m + countRange (setInter (A 0) (A 1)) m
///   = countRange (A 0) m + countRange (A 1) m`.
///
/// `Nat.countRange_union_add_inter`'s statement, DERIVED from the general
/// theorem at `n = 2` rather than re-proved. Three specialisations do all the
/// work and each is a reduction the kernel performs on its own:
///
/// * `unionAt A 2 v` is `if A 0 v then true else A 1 v`, which IS
///   `setUnion (A 0) (A 1) v` — `anyOf`'s base case supplies the `false` that
///   collapses the one-element union;
/// * `ieSumPos A 2 m true` is `(0 + 0) + (0 + meetCard A 2 {0,1} m)`, because
///   the only non-empty even subset of `[0,2)` is `{0,1}`;
/// * `ieSumPos A 2 m false` is `(0 + meetCard A 2 {0} m) + (meetCard A 2 {1} m + 0)`.
///
/// The remaining content is that `meetCard A 2 {0,1} m` counts the
/// intersection, which is a two-branch `Bool` dichotomy on `A 0 v`, and that
/// `meetCard A 2 {i} m` counts `A i` — one `mul_one`/`one_mul` each, no
/// dichotomy at all.
fn declare_inclusion_exclusion_two(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let fam = family_ty(d);

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);

    let zero = d.zero();
    let one = d.num(1);
    let two = d.num(2);
    let tv = d.bool_true();
    let fal = d.bool_false();

    let p0 = d.apply(a, &[zero]);
    let p1 = d.apply(a, &[one]);
    let union_p = d.const_app(p.set_union, &[p0, p1]);
    let inter_p = d.const_app(p.set_inter, &[p0, p1]);

    let c_union = d.const_app(p.count_range, &[union_p, m]);
    let c_inter = d.const_app(p.count_range, &[inter_p, m]);
    let c_zero = d.const_app(p.count_range, &[p0, m]);
    let c_one = d.const_app(p.count_range, &[p1, m]);

    let pos2 = d.lemma(p.subsets_inclusion_exclusion_pos, &[a, two, m]);
    let union_two = union_at(d, &p, a, two);
    let c_union_two = d.const_app(p.count_range, &[union_two, m]);
    let pos_true = ie_sum_pos(d, &p, a, two, m, tv);
    let pos_false = ie_sum_pos(d, &p, a, two, m, fal);

    // The three subsets of `[0,2)` the fold reaches, in the order it reaches
    // them.
    let empty = empty_set(d, &p);
    let s_zero = insert_at(d, &p, zero, empty);
    let s_one = insert_at(d, &p, one, empty);
    let s_both = insert_at(d, &p, one, s_zero);

    // `countRange (unionAt A 2) m = countRange (setUnion (A 0) (A 1)) m`.
    let union_pointwise = {
        let v_fv = d.fresh_fvar();
        let v = d.kernel().fvar(v_fv);
        let at_v = d.apply(union_two, &[v]);
        let body = d.bool_refl(at_v);
        d.lam_fv(v_fv, nat, body)
    };
    let union_same = d.lemma(
        p.count_range_congr,
        &[union_two, union_p, m, union_pointwise],
    );

    // `meetCard A 2 {0} m = countRange (A 0) m` and the same at `{1}` — each
    // one `mul_one`/`one_mul`, because the missing index contributes the
    // factor `1`.
    let singleton_card = |d: &mut NatDev<'_>, s: ExprId, q: ExprId, first: bool| -> ExprId {
        let start = meet_card(d, &p, a, two, s, m);
        let row = {
            let v_fv = d.fresh_fvar();
            let v = d.kernel().fvar(v_fv);
            let body = meet_ind(d, &p, a, two, s, v);
            d.lam_fv(v_fv, nat, body)
        };
        let target = {
            let v_fv = d.fresh_fvar();
            let v = d.kernel().fvar(v_fv);
            let at_v = d.apply(q, &[v]);
            let one_l = d.num(1);
            let zero_l = d.zero();
            let body = d.bool_select_nat(at_v, one_l, zero_l);
            d.lam_fv(v_fv, nat, body)
        };
        let pointwise = {
            let v_fv = d.fresh_fvar();
            let v = d.kernel().fvar(v_fv);
            let at_v = d.apply(q, &[v]);
            let one_l = d.num(1);
            let zero_l = d.zero();
            let y = d.bool_select_nat(at_v, one_l, zero_l);
            let one_a = d.num(1);
            let scaled = d.mul(one_a, y);
            let body = if first {
                // `(1 * y) * 1 = 1 * y = y`.
                let one_b = d.num(1);
                let padded = d.mul(scaled, one_b);
                let drop = d.lemma(p.mul_one, &[scaled]);
                let unit = d.lemma(p.one_mul, &[y]);
                d.trans(padded, scaled, y, drop, unit)
            } else {
                // `(1 * 1) * y = 1 * y = y`.
                d.lemma(p.one_mul, &[y])
            };
            d.lam_fv(v_fv, nat, body)
        };
        let flatten = d.lemma(p.sum_range_congr, &[row, target, m, pointwise]);
        let counted = d.const_app(p.count_range, &[q, m]);
        let as_sum = d.lemma(p.count_range_eq_sum_range, &[q, m]);
        let target_sum = d.sum_range(target, m);
        let back = d.symm(counted, target_sum, as_sum);
        d.trans(start, target_sum, counted, flatten, back)
    };
    let card_zero = singleton_card(d, s_zero, p0, true);
    let card_one = singleton_card(d, s_one, p1, false);

    // `meetCard A 2 {0,1} m = countRange (setInter (A 0) (A 1)) m` — the one
    // place a `Bool` dichotomy is needed.
    let card_both = {
        let start = meet_card(d, &p, a, two, s_both, m);
        let row = {
            let v_fv = d.fresh_fvar();
            let v = d.kernel().fvar(v_fv);
            let body = meet_ind(d, &p, a, two, s_both, v);
            d.lam_fv(v_fv, nat, body)
        };
        let target = {
            let v_fv = d.fresh_fvar();
            let v = d.kernel().fvar(v_fv);
            let at_v = d.apply(inter_p, &[v]);
            let one_l = d.num(1);
            let zero_l = d.zero();
            let body = d.bool_select_nat(at_v, one_l, zero_l);
            d.lam_fv(v_fv, nat, body)
        };
        let pointwise = {
            let v_fv = d.fresh_fvar();
            let v = d.kernel().fvar(v_fv);
            let at_zero = d.apply(p0, &[v]);
            let at_one = d.apply(p1, &[v]);
            let one_y = d.num(1);
            let zero_y = d.zero();
            let y = d.bool_select_nat(at_one, one_y, zero_y);

            let goal_at = |d: &mut NatDev<'_>, x: ExprId| -> ExprId {
                let one_a = d.num(1);
                let zero_a = d.zero();
                let head = d.bool_select_nat(x, one_a, zero_a);
                let one_b = d.num(1);
                let scaled = d.mul(one_b, head);
                let lhs = d.mul(scaled, y);
                let fal_b = d.bool_false();
                let meet = bool_select_bool(d, &p, x, at_one, fal_b);
                let one_c = d.num(1);
                let zero_c = d.zero();
                let rhs = d.bool_select_nat(meet, one_c, zero_c);
                d.eq(lhs, rhs)
            };
            let tv_b = d.bool_true();
            let fal_b = d.bool_false();
            let is_true = d.bool_eq(at_zero, tv_b);
            let is_false = d.bool_eq(at_zero, fal_b);
            let decided = bool_true_or_false(d, &p, at_zero);
            let goal = goal_at(d, at_zero);
            let on_true = {
                let h_fv = d.fresh_fvar();
                let h = d.kernel().fvar(h_fv);
                let back = d.bool_symm(at_zero, tv_b, h);
                let motive = d.bool_eq_motive(tv_b, &|d, x| goal_at(d, x));
                let refl_case = d.lemma(p.one_mul, &[y]);
                let proof = d.bool_transport(tv_b, motive, refl_case, at_zero, back);
                d.lam_fv(h_fv, is_true, proof)
            };
            let on_false = {
                let h_fv = d.fresh_fvar();
                let h = d.kernel().fvar(h_fv);
                let back = d.bool_symm(at_zero, fal_b, h);
                let motive = d.bool_eq_motive(fal_b, &|d, x| goal_at(d, x));
                let refl_case = d.lemma(p.zero_mul, &[y]);
                let proof = d.bool_transport(fal_b, motive, refl_case, at_zero, back);
                d.lam_fv(h_fv, is_false, proof)
            };
            let body = or_elim(d, &p, is_true, is_false, goal, on_true, on_false, decided);
            d.lam_fv(v_fv, nat, body)
        };
        let flatten = d.lemma(p.sum_range_congr, &[row, target, m, pointwise]);
        let as_sum = d.lemma(p.count_range_eq_sum_range, &[inter_p, m]);
        let target_sum = d.sum_range(target, m);
        let back = d.symm(c_inter, target_sum, as_sum);
        d.trans(start, target_sum, c_inter, flatten, back)
    };

    // `ieSumPos A 2 m true = meetCard A 2 {0,1} m`: the fold's own shape is
    // `(0 + 0) + (0 + …)`, so two `zero_add`s.
    let both_card = meet_card(d, &p, a, two, s_both, m);
    let padded_both = d.add(zero, both_card);
    let peel_outer = d.lemma(p.zero_add, &[padded_both]);
    let peel_inner = d.lemma(p.zero_add, &[both_card]);
    let pos_true_is_both = d.trans(pos_true, padded_both, both_card, peel_outer, peel_inner);
    let pos_true_eq = d.trans(pos_true, both_card, c_inter, pos_true_is_both, card_both);

    // `ieSumPos A 2 m false = meetCard A 2 {0} m + meetCard A 2 {1} m`.
    let zero_card = meet_card(d, &p, a, two, s_zero, m);
    let one_card = meet_card(d, &p, a, two, s_one, m);
    let padded_zero = d.add(zero, zero_card);
    let padded_one = d.add(one_card, zero);
    let drop_left = d.lemma(p.zero_add, &[zero_card]);
    let drop_right = d.lemma(p.add_zero, &[one_card]);
    let joined = add_congr(
        d,
        padded_zero,
        zero_card,
        drop_left,
        padded_one,
        one_card,
        drop_right,
    );
    let raw_sum = d.add(zero_card, one_card);
    let counted_sum = d.add(c_zero, c_one);
    let named = add_congr(d, zero_card, c_zero, card_zero, one_card, c_one, card_one);
    let pos_false_eq = d.trans(pos_false, raw_sum, counted_sum, joined, named);

    // Assemble: rewrite both summands of the general statement at `n = 2`.
    let back_union = d.symm(c_union_two, c_union, union_same);
    let back_true = d.symm(pos_true, c_inter, pos_true_eq);
    let goal_lhs = d.add(c_union, c_inter);
    let general_lhs = d.add(c_union_two, pos_true);
    let restated = add_congr(
        d,
        c_union,
        c_union_two,
        back_union,
        c_inter,
        pos_true,
        back_true,
    );
    let s1 = d.trans(goal_lhs, general_lhs, pos_false, restated, pos2);
    let proof = d.trans(goal_lhs, pos_false, counted_sum, s1, pos_false_eq);

    let concl = d.eq(goal_lhs, counted_sum);
    let ty = {
        let with_m = d.pi_fv(m_fv, nat, concl);
        d.pi_fv(a_fv, fam, with_m)
    };
    let value = {
        let with_m = d.lam_fv(m_fv, nat, proof);
        d.lam_fv(a_fv, fam, with_m)
    };
    d.declare_theorem(p.subsets_inclusion_exclusion_two, ty, value)
}

/// Declare the inclusion–exclusion layer.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection, naming the step that
/// failed.
pub(super) fn declare_inclusion_exclusion_all(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let steps: [(
        &str,
        fn(&mut NatDev<'_>, &NatPrelude) -> Result<(), KernelError>,
    ); 10] = [
        ("definitions", declare_definitions),
        ("equations", declare_equations),
        ("noneOf_eq", declare_none_of_eq),
        ("prodPar_even", declare_prod_par_even),
        ("prodRange_one", declare_prod_range_one),
        ("meetCard_empty", declare_meet_card_empty),
        ("sumSel_meetInd", declare_sum_sel_meet_ind),
        ("inclusion_exclusion", declare_inclusion_exclusion),
        ("inclusion_exclusion_pos", declare_inclusion_exclusion_pos),
        ("inclusion_exclusion_two", declare_inclusion_exclusion_two),
    ];
    for (name, step) in steps {
        if let Err(e) = step(d, p) {
            let rendered = d.explain(&e);
            eprintln!("inclusion_exclusion: step `{name}` REJECTED: {rendered}");
            return Err(e);
        }
    }
    Ok(())
}
