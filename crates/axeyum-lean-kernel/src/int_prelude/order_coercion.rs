//! Four `Int` order/coercion mirrors from Mathlib v4.30:
//! `Int.le_of_ofNat_le_ofNat`, `Int.lt_of_ofNat_lt_ofNat`, `Int.le.elim`,
//! `Int.lt.elim`.
//!
//! The first two are definitional. `Int.le`/`Int.lt` are built by
//! `define_binary_int` (`defs.rs`), and its `ofNat`/`ofNat` branch is
//! literally `NatOps::le`/`NatOps::lt` applied to the two `Nat` fields — so
//! `Int.le (ofNat m) (ofNat n)` is definitionally `Nat.le m n`, and the proof
//! is the hypothesis itself under that defeq (no case split, no lemma).
//!
//! The last two are the CPS elimination form of `le_dest`/`lt_dest`'s
//! `Exists` witness (`order.rs::declare_difference_lemmas`), built by
//! `Exists.elim` (`ops::exists_elim`) with the equation flipped by `isymm` —
//! Mathlib's direction is `a + n = b`, while `le_dest`/`lt_dest` produce
//! `b = a + n`. This is genuinely new: only the `Exists`-flavoured cousins
//! (`le_dest`/`lt_dest`) existed under any name before this file: the CPS
//! shape `∀ {P}, (∀ n, … → P) → P` was absent, matching the brief's own
//! finding that a shape-search for it turns up nothing at ⩾0.75.

use super::ops::{IntDev, exists_elim};
use crate::KernelError;
use crate::env::Declaration;
use crate::expr::ExprId;
use crate::nat_prelude::NatOps;

/// Declare `Int.le_of_ofNat_le_ofNat : ∀ (m n : Nat), le (ofNat m) (ofNat n) → Nat.le m n`
/// and `Int.lt_of_ofNat_lt_ofNat : ∀ (n m : Nat), lt (ofNat n) (ofNat m) → Nat.lt n m`.
///
/// Both hold by defeq alone: `Int.le`/`Int.lt` iota-reduce their `ofNat`/`ofNat`
/// branch straight to the `Nat` comparison, so the hypothesis already has the
/// conclusion's type up to unfolding.
///
/// # Errors
///
/// Returns the trusted gate's rejection if either constructed term does not
/// check.
pub(super) fn declare_ofnat_order_coercions(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    let nat = d.nat_ty();

    // le_of_ofNat_le_ofNat : ∀ (m n : Nat), le (ofNat m) (ofNat n) → Nat.le m n.
    {
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let a = d.of_nat(m);
        let b = d.of_nat(n);
        let hyp_ty = d.ile(a, b);
        let concl = d.le(m, n);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);

        let inner_ty = d.arrow(hyp_ty, concl);
        let inner_value = d.lam_fv(h_fv, hyp_ty, h);
        let ty = {
            let with_n = d.pi_fv(n_fv, nat, inner_ty);
            d.pi_fv(m_fv, nat, with_n)
        };
        let value = {
            let with_n = d.lam_fv(n_fv, nat, inner_value);
            d.lam_fv(m_fv, nat, with_n)
        };
        d.kernel().add_declaration(Declaration::Theorem {
            name: p.le_of_ofnat_le_ofnat,
            uparams: vec![],
            ty,
            value,
        })?;
    }

    // lt_of_ofNat_lt_ofNat : ∀ (n m : Nat), lt (ofNat n) (ofNat m) → Nat.lt n m.
    {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let a = d.of_nat(n);
        let b = d.of_nat(m);
        let hyp_ty = d.ilt(a, b);
        let concl = d.lt(n, m);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);

        let inner_ty = d.arrow(hyp_ty, concl);
        let inner_value = d.lam_fv(h_fv, hyp_ty, h);
        let ty = {
            let with_m = d.pi_fv(m_fv, nat, inner_ty);
            d.pi_fv(n_fv, nat, with_m)
        };
        let value = {
            let with_m = d.lam_fv(m_fv, nat, inner_value);
            d.lam_fv(n_fv, nat, with_m)
        };
        d.kernel().add_declaration(Declaration::Theorem {
            name: p.lt_of_ofnat_lt_ofnat,
            uparams: vec![],
            ty,
            value,
        })?;
    }

    Ok(())
}

/// `fun (i : Nat) => Eq Int b (Int.add a (Int.ofNat (offset i)))` — rebuilt
/// locally to match `order.rs`'s private `shift_predicate` exactly (same
/// construction `le_dest`/`lt_dest`'s own `Exists` conclusion uses), the same
/// re-derivation `euclid.rs::declare_decomposition` already does rather than
/// widen that module's visibility for one caller.
fn shift_predicate(
    d: &mut IntDev<'_>,
    a: ExprId,
    b: ExprId,
    offset: &dyn Fn(&mut IntDev<'_>, ExprId) -> ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let magnitude = offset(d, i);
    let value = d.of_nat(magnitude);
    let shifted = d.iadd(a, value);
    let body = d.ieq(b, shifted);
    d.lam_fv(i_fv, nat, body)
}

/// Declare `Int.le.elim` and `Int.lt.elim`, the CPS elimination forms of
/// `Int.le_dest`/`Int.lt_dest`'s existential witness.
///
/// # Errors
///
/// Returns the trusted gate's rejection if either constructed term does not
/// check.
pub(super) fn declare_dest_elim(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    let nat = d.nat_ty();
    let int_ty = d.int_ty();

    // le.elim : ∀ {a b}, le a b → ∀ {P}, (∀ (n : Nat), a + ofNat n = b → P) → P.
    {
        let a_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let b_fv = d.fresh_fvar();
        let b = d.kernel().fvar(b_fv);
        let hyp_ty = d.ile(a, b);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let prop = d.kernel().sort_zero();
        let p_fv = d.fresh_fvar();
        let p_expr = d.kernel().fvar(p_fv);

        // minor_hyp : ∀ (n : Nat), a + ofNat n = b → P.
        let minor_hyp_ty = {
            let n_fv = d.fresh_fvar();
            let n = d.kernel().fvar(n_fv);
            let value = d.of_nat(n);
            let shifted = d.iadd(a, value);
            let eqn = d.ieq(shifted, b);
            let body = d.arrow(eqn, p_expr);
            d.pi_fv(n_fv, nat, body)
        };
        let hp_fv = d.fresh_fvar();
        let hp = d.kernel().fvar(hp_fv);

        // predicate : fun i => Eq Int b (a + ofNat i) — le_dest's own shape.
        let predicate = shift_predicate(d, a, b, &|_d, i| i);
        let dest = d.const_app(p.le_dest, &[a, b, h]);
        let minor = {
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let value = d.of_nat(i);
            let shifted = d.iadd(a, value);
            let heq_ty = d.ieq(b, shifted); // predicate i
            let heq_fv = d.fresh_fvar();
            let heq = d.kernel().fvar(heq_fv);
            let flipped = d.isymm(b, shifted, heq); // a + ofNat i = b
            let applied = d.apply(hp, &[i, flipped]); // : P
            let with_heq = d.lam_fv(heq_fv, heq_ty, applied);
            d.lam_fv(i_fv, nat, with_heq)
        };
        let body = exists_elim(d, predicate, p_expr, dest, minor);

        let ty = {
            let inner = d.arrow(minor_hyp_ty, p_expr);
            let with_p = d.pi_fv(p_fv, prop, inner);
            let with_h = d.arrow(hyp_ty, with_p);
            let with_b = d.pi_fv(b_fv, int_ty, with_h);
            d.pi_fv(a_fv, int_ty, with_b)
        };
        let value = {
            let with_hp = d.lam_fv(hp_fv, minor_hyp_ty, body);
            let with_p = d.lam_fv(p_fv, prop, with_hp);
            let with_h = d.lam_fv(h_fv, hyp_ty, with_p);
            let with_b = d.lam_fv(b_fv, int_ty, with_h);
            d.lam_fv(a_fv, int_ty, with_b)
        };
        d.kernel().add_declaration(Declaration::Theorem {
            name: p.le_elim,
            uparams: vec![],
            ty,
            value,
        })?;
    }

    // lt.elim : ∀ {a b}, lt a b → ∀ {P}, (∀ (n : Nat), a + ofNat n.succ = b → P) → P.
    {
        let a_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let b_fv = d.fresh_fvar();
        let b = d.kernel().fvar(b_fv);
        let hyp_ty = d.ilt(a, b);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let prop = d.kernel().sort_zero();
        let p_fv = d.fresh_fvar();
        let p_expr = d.kernel().fvar(p_fv);

        // minor_hyp : ∀ (n : Nat), a + ofNat n.succ = b → P.
        let minor_hyp_ty = {
            let n_fv = d.fresh_fvar();
            let n = d.kernel().fvar(n_fv);
            let sn = d.succ(n);
            let value = d.of_nat(sn);
            let shifted = d.iadd(a, value);
            let eqn = d.ieq(shifted, b);
            let body = d.arrow(eqn, p_expr);
            d.pi_fv(n_fv, nat, body)
        };
        let hp_fv = d.fresh_fvar();
        let hp = d.kernel().fvar(hp_fv);

        // predicate : fun i => Eq Int b (a + ofNat (succ i)) — lt_dest's own shape.
        let predicate = shift_predicate(d, a, b, &|d, i| d.succ(i));
        let dest = d.const_app(p.lt_dest, &[a, b, h]);
        let minor = {
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let si = d.succ(i);
            let value = d.of_nat(si);
            let shifted = d.iadd(a, value);
            let heq_ty = d.ieq(b, shifted); // predicate i
            let heq_fv = d.fresh_fvar();
            let heq = d.kernel().fvar(heq_fv);
            let flipped = d.isymm(b, shifted, heq); // a + ofNat (succ i) = b
            let applied = d.apply(hp, &[i, flipped]); // : P
            let with_heq = d.lam_fv(heq_fv, heq_ty, applied);
            d.lam_fv(i_fv, nat, with_heq)
        };
        let body = exists_elim(d, predicate, p_expr, dest, minor);

        let ty = {
            let inner = d.arrow(minor_hyp_ty, p_expr);
            let with_p = d.pi_fv(p_fv, prop, inner);
            let with_h = d.arrow(hyp_ty, with_p);
            let with_b = d.pi_fv(b_fv, int_ty, with_h);
            d.pi_fv(a_fv, int_ty, with_b)
        };
        let value = {
            let with_hp = d.lam_fv(hp_fv, minor_hyp_ty, body);
            let with_p = d.lam_fv(p_fv, prop, with_hp);
            let with_h = d.lam_fv(h_fv, hyp_ty, with_p);
            let with_b = d.lam_fv(b_fv, int_ty, with_h);
            d.lam_fv(a_fv, int_ty, with_b)
        };
        d.kernel().add_declaration(Declaration::Theorem {
            name: p.lt_elim,
            uparams: vec![],
            ty,
            value,
        })?;
    }

    Ok(())
}
