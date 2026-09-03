//! Nine basic `Int` addition mirrors of Mathlib v4.30 propositions
//! (`Int.add_comm`, `Int.add_left_cancel`, `Int.add_left_comm`,
//! `Int.add_left_inj`, `Int.add_left_neg`, `Int.add_mul`,
//! `Int.add_neg_cancel_left`, `Int.add_neg_cancel_right`,
//! `Int.add_neg_eq_sub`).
//!
//! Two of the nine (`add_comm`, `add_neg_cancel_right`) were already derived
//! in `algebra.rs` before this file existed -- see `int_theorem_inventory`.
//! The other seven are built here, entirely from already-derived `algebra.rs`
//! laws (`add_comm`, `add_assoc`, `add_zero`, `add_neg`, `mul_comm`,
//! `left_distrib`) plus `sub.rs`'s `Int.sub` definition and `modeq.rs`'s
//! private `cancel_neg_add_left` (already widened to `pub(super)` for
//! `order_add.rs`'s reuse) -- no `Int.rec` case split anywhere in this file.
//!
//! Dispatch position: after `sub::declare_mul_sub` (so `Int.sub` exists for
//! [`declare_add_neg_eq_sub`]) and before `order::declare_difference_lemmas`.

use super::modeq::cancel_neg_add_left;
use super::ops::IntDev;
use crate::KernelError;
use crate::expr::ExprId;
use crate::linarith::int as linarith;
use crate::nat_prelude::NatOps;

/// `Int.add_left_neg : ∀ (a : Int), Eq Int (add (neg a) a) zero`.
///
/// Retired to the `simp` rewrite-chain producer (ADR-1586): `add_comm`
/// (a caller-supplied extra, ordered after the defaults so `add_neg` wins
/// the match race once it becomes available) then `add_neg` (default).
fn declare_add_left_neg(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    let defaults = crate::simp::int::default_rules(&p);
    let extra = [crate::simp::int::rule_add_comm(&p)];
    let rules = crate::simp::int::with_extra(&defaults, &extra);
    crate::simp::int::declare(d, &rules, p.add_left_neg, 1, &|d, v| {
        let a = v[0];
        let neg_a = d.ineg(a);
        let lhs = d.iadd(neg_a, a);
        let zero = d.izero();
        (lhs, zero)
    })
}

/// `Int.add_neg_eq_sub : ∀ (a b : Int), Eq Int (add a (neg b)) (sub a b)`.
///
/// `Int.sub a b` is the plain, non-recursive `Definition
/// (fun a b => add a (neg b))` (`sub.rs`), so the declared statement's right
/// side unfolds to the left side by defeq alone: `Eq.refl` at `add a (neg b)`
/// checks against the stated type without any rewriting.
fn declare_add_neg_eq_sub(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.add_neg_eq_sub, 2, &|d, v| {
        let (a, b) = (v[0], v[1]);
        let neg_b = d.ineg(b);
        let a_neg_b = d.iadd(a, neg_b);
        let a_sub_b = d.isub(a, b);
        let proof = d.irefl(a_neg_b);
        (d.ieq(a_neg_b, a_sub_b), proof)
    })?;
    Ok(())
}

/// `Int.add_left_comm : ∀ (a b c : Int),
/// Eq Int (add a (add b c)) (add b (add a c))`.
///
/// Chain: `a+(b+c) = (a+b)+c = (b+a)+c = b+(a+c)`, via `add_assoc` twice and
/// `add_comm` once (congruence on the shared `+c`).
fn declare_add_left_comm(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    linarith::declare(d, &p, p.add_left_comm, 3, &|d, v| {
        let (a, b, c) = (v[0], v[1], v[2]);
        let bc = d.iadd(b, c);
        let start = d.iadd(a, bc);
        let ac = d.iadd(a, c);
        let fin = d.iadd(b, ac);
        (vec![], d.ieq(start, fin))
    })?;
    Ok(())
}

/// `Int.add_mul : ∀ (a b c : Int),
/// Eq Int (mul (add a b) c) (add (mul a c) (mul b c))`.
///
/// Chain: `(a+b)*c = c*(a+b) = c*a+c*b = a*c+c*b = a*c+b*c`, via `mul_comm`
/// (thrice: to swap onto `left_distrib`'s shape, then back on each summand)
/// and `left_distrib` once. No case split; `Int.left_distrib` only
/// distributes on the left, so this is `add_mul`'s whole content.
fn declare_add_mul(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.add_mul, 3, &|d, v| {
        let (a, b, c) = (v[0], v[1], v[2]);
        let ab = d.iadd(a, b);
        let start = d.imul(ab, c); // (a+b)*c
        let next1 = d.imul(c, ab); // c*(a+b)
        let ca = d.imul(c, a);
        let cb = d.imul(c, b);
        let next2 = d.iadd(ca, cb); // c*a+c*b
        let ac = d.imul(a, c);
        let bc = d.imul(b, c);
        let next3 = d.iadd(ac, cb); // a*c+c*b
        let next4 = d.iadd(ac, bc); // a*c+b*c

        let comm1 = d.const_app(p.mul_comm, &[ab, c]); // Eq(start, next1)
        let ld = d.const_app(p.left_distrib, &[c, a, b]); // Eq(next1, next2)
        let comm_ca = d.const_app(p.mul_comm, &[c, a]); // Eq(ca, ac)
        let step3 = d.icongr(ca, ac, comm_ca, &|d, t| d.iadd(t, cb)); // Eq(next2, next3)
        let comm_cb = d.const_app(p.mul_comm, &[c, b]); // Eq(cb, bc)
        let step4 = d.icongr(cb, bc, comm_cb, &|d, t| d.iadd(ac, t)); // Eq(next3, next4)

        let (_, proof) = d.ichain(
            start,
            &[(next1, comm1), (next2, ld), (next3, step3), (next4, step4)],
        );
        (d.ieq(start, next4), proof)
    })?;
    Ok(())
}

/// `Int.add_neg_cancel_left : ∀ (a b : Int), Eq Int (add a (add (neg a) b)) b`.
///
/// Chain: `a+(-a+b) = (a+(-a))+b = 0+b = b+0 = b`, via `add_assoc`,
/// `add_neg`, and `add_comm`+`add_zero` for the `0+b -> b` step (there is no
/// `zero_add` law in this prelude). The mirror image of `modeq.rs`'s private
/// `cancel_neg_add_left(c, x) : Eq(neg_c + (c+x), x)` -- here the OUTER term
/// is the positive `a` and the inner negation is `neg a`, so that helper
/// cannot be reused directly (it would need `neg (neg a)`, not `a`, on the
/// outside).
fn declare_add_neg_cancel_left(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    linarith::declare(d, &p, p.add_neg_cancel_left, 2, &|d, v| {
        let (a, bb) = (v[0], v[1]);
        let neg_a = d.ineg(a);
        let nega_bb = d.iadd(neg_a, bb);
        let start = d.iadd(a, nega_bb);
        (vec![], d.ieq(start, bb))
    })?;
    Ok(())
}

/// `Int.add_left_cancel : ∀ (a b c : Int),
/// Eq Int (add a b) (add a c) → Eq Int b c`.
///
/// `modeq.rs`'s `cancel_neg_add_left(a, x) : Eq(neg_a+(a+x), x)` applied at
/// `x := b` and `x := c`, bridged by congruence on the hypothesis:
/// `b = neg_a+(a+b) = neg_a+(a+c) = c`.
fn declare_add_left_cancel(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.add_left_cancel, 3, &|d, v| {
        let (a, b, c) = (v[0], v[1], v[2]);
        let ab = d.iadd(a, b);
        let ac = d.iadd(a, c);
        let hyp = d.ieq(ab, ac);
        let concl = d.ieq(b, c);

        let h_fv = d.fresh_fvar();
        let h: ExprId = d.kernel().fvar(h_fv);

        let neg_a = d.ineg(a);
        let na_ab = d.iadd(neg_a, ab); // neg_a+(a+b)
        let na_ac = d.iadd(neg_a, ac); // neg_a+(a+c)

        let l1 = cancel_neg_add_left(d, a, b); // Eq(na_ab, b)
        let l2 = cancel_neg_add_left(d, a, c); // Eq(na_ac, c)
        let symm_l1 = d.isymm(na_ab, b, l1); // Eq(b, na_ab)
        let congr_h = d.icongr(ab, ac, h, &|d, t| d.iadd(neg_a, t)); // Eq(na_ab, na_ac)

        let (_, body) = d.ichain(b, &[(na_ab, symm_l1), (na_ac, congr_h), (c, l2)]);
        let proof = d.lam_fv(h_fv, hyp, body);

        (d.arrow(hyp, concl), proof)
    })?;
    Ok(())
}

/// `Int.add_left_inj : ∀ (i j k : Int),
/// Iff (Eq Int (add i k) (add j k)) (Eq Int i j)`.
///
/// `mpr` is congruence on `i = j`. `mp` rotates the hypothesis through
/// `add_comm` on both sides (`i+k=j+k -> k+i=k+j`) and closes with
/// `add_left_cancel`.
fn declare_add_left_inj(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.add_left_inj, 3, &|d, v| {
        let (i, j, k) = (v[0], v[1], v[2]);
        let ik = d.iadd(i, k);
        let jk = d.iadd(j, k);
        let left_ty = d.ieq(ik, jk);
        let right_ty = d.ieq(i, j);

        let mpr = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let body = d.icongr(i, j, h, &|d, t| d.iadd(t, k));
            d.lam_fv(h_fv, right_ty, body)
        };

        let mp = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let ki = d.iadd(k, i);
            let kj = d.iadd(k, j);

            let comm_i = d.const_app(p.add_comm, &[i, k]); // Eq(ik, ki)
            let comm_j = d.const_app(p.add_comm, &[j, k]); // Eq(jk, kj)
            let symm_comm_i = d.isymm(ik, ki, comm_i); // Eq(ki, ik)

            let (_, h_prime) = d.ichain(ki, &[(ik, symm_comm_i), (jk, h), (kj, comm_j)]);
            // h_prime : Eq(ki, kj)
            let body = d.const_app(p.add_left_cancel, &[k, i, j, h_prime]);
            d.lam_fv(h_fv, left_ty, body)
        };

        let stmt = d.const_app(p.logic.iff, &[left_ty, right_ty]);
        let proof = d.const_app(p.logic.iff_intro, &[left_ty, right_ty, mp, mpr]);
        (stmt, proof)
    })?;
    Ok(())
}

/// Declare all nine `add_basics` mirrors' new theorems, in dependency order:
/// `add_left_cancel` before `add_left_inj` (which calls it), everything else
/// independent of one another. `add_comm` and `add_neg_cancel_right`
/// themselves are NOT declared here -- they already exist in `algebra.rs`.
///
/// # Errors
///
/// Returns the trusted gate's rejection if any constructed term does not
/// check.
pub(super) fn declare_add_basics(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    declare_add_left_neg(d)?;
    declare_add_neg_eq_sub(d)?;
    declare_add_left_comm(d)?;
    declare_add_mul(d)?;
    declare_add_neg_cancel_left(d)?;
    declare_add_left_cancel(d)?;
    declare_add_left_inj(d)?;
    Ok(())
}
