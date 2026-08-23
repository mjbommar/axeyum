//! `Int.ModEq n a b := emod a n = emod b n` — congruence modulo `n`, our own
//! universe's version of the Mathlib `Int.ModEq` family.
//!
//! `refl`/`symm`/`trans` are exactly `Eq.refl`/`Eq.symm`/`Eq.trans` once the
//! definition unfolds — no new proof technique, just `Eq`'s own equivalence
//! laws transported through a definitional layer.
//!
//! ## What is NOT here yet, and why
//!
//! `Int.modEq_iff_dvd : ModEq n a b ↔ n ∣ (b - a)` is the real content this
//! definition exists for, and it needs [`super::dvd::declare_emod_eq_zero_iff_dvd`]
//! (`a%n=0 ↔ n∣a`) plus a fact connecting `emod a n = emod b n` to
//! `emod (b-a) n = 0`. That connecting fact is itself blocked: proving `b-a
//! = n*((b/n)-(a/n))` from `a=n*(a/n)+r, b=n*(b/n)+r` (same remainder `r`)
//! needs `Int.mul` distributing over subtraction and commuting with
//! negation — `n*(x-y) = n*x - n*y` and `n*(-y) = -(n*y)` — and this
//! development has proved neither. (`Int.left_distrib` only distributes over
//! `add`.) Both are short derivations from `Int.neg_one_mul` +
//! `Int.mul_assoc` + `Int.mul_comm`, but they are new lemmas, not composition
//! of existing ones, so they are left for the next slice rather than rushed.
//!
//! ## The structural-vs-well-founded contrast
//!
//! The imported route to this same family is currently blocked at the
//! statement adapter on `Nat.div_rec_lemma`
//! (`docs/autogenesis/241-int-modeq-producer-finding.md`,
//! `242-...`), because Mathlib's `Nat.mod` is defined by well-founded
//! recursion and the adapter cannot yet discharge the associated
//! `Acc`/`WellFounded` obligation. Our `Int.emod` (`int_prelude/division.rs`)
//! has no such blocker: it is a **structural** `Int.rec`/`Nat.rec`
//! definition — two nested pattern matches on constructors, each strictly
//! smaller — so no well-founded recursion, no `Acc` witness, and no
//! termination proof obligation ever enters the picture. The from-scratch
//! route pays for this with more explicit case-splitting up front (four
//! branches for `ediv`/`emod`, the whole `subNatNat` borrow development to
//! support them); what it buys is that every lemma past that point is
//! ordinary structural induction, and "prove `ModEq` is an equivalence
//! relation" here needed nothing beyond `Eq` itself.

use super::defs::DERIVED_HEIGHT;
use super::ops::IntDev;
use crate::BinderInfo;
use crate::KernelError;
use crate::env::{Declaration, ReducibilityHint};
use crate::expr::ExprId;
use crate::nat_prelude::NatOps;

/// `Int.ModEq n a b`, i.e. `d.const_app(p.mod_eq, &[n, a, b])`.
fn imodeq(d: &mut IntDev<'_>, n: ExprId, a: ExprId, b: ExprId) -> ExprId {
    let f = d.int().mod_eq;
    d.const_app(f, &[n, a, b])
}

/// Admit `Int.ModEq : Int → Int → Int → Prop := fun n a b => emod a n = emod b n`.
///
/// # Errors
///
/// Returns the trusted gate's rejection (a malformed statement, or a name
/// conflict).
pub(super) fn declare_modeq_definition(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    let int_ty = d.int_ty();
    let anon = d.anon_name();
    let prop = d.kernel().sort_zero();

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let emod_an = d.iemod(a, n);
    let emod_bn = d.iemod(b, n);
    let body = d.ieq(emod_an, emod_bn);
    let value = {
        let with_b = d.lam_fv(b_fv, int_ty, body);
        let with_a = d.lam_fv(a_fv, int_ty, with_b);
        d.lam_fv(n_fv, int_ty, with_a)
    };
    let ty = {
        let with_b = d.kernel().pi(anon, int_ty, prop, BinderInfo::Default);
        let with_a = d.kernel().pi(anon, int_ty, with_b, BinderInfo::Default);
        d.kernel().pi(anon, int_ty, with_a, BinderInfo::Default)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.mod_eq,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(DERIVED_HEIGHT),
    })
}

/// `Int.ModEq.refl : ∀ n a, ModEq n a a` — `Eq.refl (emod a n)`.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
pub(super) fn declare_modeq_refl(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.mod_eq_refl, 2, &|d, v| {
        let (n, a) = (v[0], v[1]);
        let stmt = imodeq(d, n, a, a);
        let emod_an = d.iemod(a, n);
        let proof = d.irefl(emod_an);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Int.ModEq.symm : ∀ n a b, ModEq n a b → ModEq n b a` — `Eq.symm`.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
pub(super) fn declare_modeq_symm(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.mod_eq_symm, 3, &|d, v| {
        let (n, a, b) = (v[0], v[1], v[2]);
        let h_ty = imodeq(d, n, a, b);
        let target = imodeq(d, n, b, a);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let emod_an = d.iemod(a, n);
        let emod_bn = d.iemod(b, n);
        let body = d.isymm(emod_an, emod_bn, h);
        let proof = d.lam_fv(h_fv, h_ty, body);
        let stmt = d.arrow(h_ty, target);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Int.ModEq.trans : ∀ n a b c, ModEq n a b → ModEq n b c → ModEq n a c` —
/// `Eq.trans`.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
pub(super) fn declare_modeq_trans(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.mod_eq_trans, 4, &|d, v| {
        let (n, a, b, c) = (v[0], v[1], v[2], v[3]);
        let hab_ty = imodeq(d, n, a, b);
        let hbc_ty = imodeq(d, n, b, c);
        let target = imodeq(d, n, a, c);
        let hab_fv = d.fresh_fvar();
        let hab = d.kernel().fvar(hab_fv);
        let hbc_fv = d.fresh_fvar();
        let hbc = d.kernel().fvar(hbc_fv);
        let emod_an = d.iemod(a, n);
        let emod_bn = d.iemod(b, n);
        let emod_cn = d.iemod(c, n);
        let body = d.itrans(emod_an, emod_bn, emod_cn, hab, hbc);
        let with_hbc = d.lam_fv(hbc_fv, hbc_ty, body);
        let proof = d.lam_fv(hab_fv, hab_ty, with_hbc);
        let hbc_to_target = d.arrow(hbc_ty, target);
        let stmt = d.arrow(hab_ty, hbc_to_target);
        (stmt, proof)
    })?;
    Ok(())
}
