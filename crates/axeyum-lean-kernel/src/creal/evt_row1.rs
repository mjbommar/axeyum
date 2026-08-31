//! `CReal.evt_approx_max` — the Extreme Value Theorem's honest row 1.
//!
//! This is the composition ADR-0691/ADR-0692 and
//! `08-ivt-and-evt-measured-against-mathlib.md` name as the missing piece:
//! `creal/sup_laws.rs` already carries the two laws that characterize
//! `CReal.supOn` as a supremum —
//! [`CRealPrelude::sup_on_ub`](super::CRealPrelude::sup_on_ub) (`F x ≤ supOn`
//! for every `x ∈ [a,b]`) and
//! [`CRealPrelude::sup_on_approx_lub`](super::CRealPrelude::sup_on_approx_lub)
//! (`supOn` is approached to within `1/(n+1)` at some point of `[a,b]`) — and
//! nothing in the tree had combined them into the one statement that is
//! actually the constructive substitute for EVT's conclusion. This file adds
//! nothing new to the supremum machinery; it is pure composition of two
//! already-admitted, axiom-free theorems plus `CReal.le_trans`.
//!
//! ## The statement
//!
//! `CReal.evt_approx_max : ∀ F a b, le a b → UniformlyContinuousOn F a b →
//! ∀ n, ∃ x, le a x ∧ le x b ∧ ∀ y, le a y → le y b →
//! le (F y) (add (F x) (ofRat (natDivSucc 1 n)))`
//!
//! For every accuracy index `n` there is a point `x ∈ [a,b]` at which `F`
//! comes within `1/(n+1)` of dominating `F` everywhere else on `[a,b]` — an
//! **approximate maximum**. It is the exact structural mirror of
//! `CReal.ivt_approx`: a witness plus an explicit, computable error bound,
//! never an exact extremum.
//!
//! ## What this is NOT, and must not be read as
//!
//! This is **not** an attained maximum and does not narrow
//! [`CRealPrelude::evt_attained_max_decides_sign`](super::CRealPrelude::evt_attained_max_decides_sign)'s
//! conclusion at all: that theorem proves an EXACT attaining maximiser would
//! decide the sign of an arbitrary real, and `evt_approx_max`'s witness `x`
//! moves with `n` and is never claimed to converge to one. Landing this
//! theorem does not close the row-2 gap; it fills row 1 beside it, which is
//! what makes row 2 legible as a *boundary* (this much is constructive, no
//! further) rather than as a hole (nothing constructive was ever built).
//!
//! `F` must still be assumed `UniformlyContinuousOn [a,b]` with the modulus
//! carried as explicit `Sort 1` data (an argument to `UniformlyContinuousOn`,
//! not an `∃`) — the same restriction `ivt_approx` and every rung of
//! `creal/supremum.rs` and `creal/sup_laws.rs` already carry. Nothing here
//! weakens that hypothesis.
//!
//! ## Proof
//!
//! `sup_on_approx_lub F a b hab u n` gives `x` with `a ≤ x ≤ b` and
//! `supOn ≤ F x + 1/(n+1)`. For an arbitrary `y ∈ [a,b]`, `sup_on_ub` gives
//! `F y ≤ supOn`; `le_trans` chains the two into `F y ≤ F x + 1/(n+1)`. The
//! existential elimination is over `CReal`, not `Nat`, so this file carries
//! its own generic `cexists_elim` — the same helper `creal/ivt.rs` and
//! `creal/inverse_fn.rs` each already duplicate locally, per CLAUDE.md's
//! standing note that a tiny per-file generic helper is preferable to one
//! more proof that must stay in sync with a shared copy.

#![allow(clippy::doc_markdown, clippy::too_many_arguments)]

use super::{CRealPrelude, and_intro, cadd, cle, creal_ty, div_succ, embed};
use crate::KernelError;
use crate::env::Declaration;
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::nat_prelude::NatOps;

/// `Exists elem_ty predicate`, eliminated into `target` (which must not
/// mention the witness) via a `minor : ∀ x, predicate x → target`. Generic in
/// `elem_ty`, unlike [`crate::int_prelude::ops::exists_elim`], because the
/// existential eliminated here ranges over `CReal`, not `Nat`.
fn cexists_elim(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    elem_ty: ExprId,
    predicate: ExprId,
    target: ExprId,
    witness: ExprId,
    minor: ExprId,
) -> ExprId {
    let one = d.level_one();
    let exists_name = p.rat.int.logic.exists_;
    let exists_const = d.kernel().const_(exists_name, vec![one]);
    let exists_ty = d.apply(exists_const, &[elem_ty, predicate]);
    let motive = {
        let fv = d.fresh_fvar();
        d.lam_fv(fv, exists_ty, target)
    };
    let rec_name = p.rat.int.logic.exists_rec;
    let rec = d.kernel().const_(rec_name, vec![one]);
    d.apply(rec, &[elem_ty, predicate, motive, minor, witness])
}

fn declare_evt_approx_max_thm(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = creal_ty(d, p);
    let func_ty = d.arrow(carrier, carrier);
    let logic = p.rat.int.logic;
    let one_level = d.level_one();

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let hab_fv = d.fresh_fvar();
    let hab = d.kernel().fvar(hab_fv);
    let hab_ty = cle(d, p, a, b);
    let u_fv = d.fresh_fvar();
    let u = d.kernel().fvar(u_fv);
    let u_ty = d.const_app(p.uniformly_continuous_on, &[f, a, b]);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    // `1/(n+1)`, and the value `supOn F a b hab u` this whole theorem is
    // about.
    let eps = embed(d, p, div_succ(d, p, 1, n));
    let sup_val = d.const_app(p.sup_on, &[f, a, b, hab, u]);

    // `hex : Exists CReal (fun x => le a x /\ (le x b /\ le sup_val (F x + eps)))`
    // -- exactly `sup_on_approx_lub`'s conclusion at `e := n`.
    let hex_pred = {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let lo = cle(d, p, a, x);
        let hi = cle(d, p, x, b);
        let fx = d.apply(f, &[x]);
        let padded = cadd(d, p, fx, eps);
        let est = cle(d, p, sup_val, padded);
        let tail = d.and(hi, est);
        let body = d.and(lo, tail);
        d.lam_fv(x_fv, carrier, body)
    };
    let hex = d.lemma(p.sup_on_approx_lub, &[f, a, b, hab, u, n]);

    // The goal predicate: `fun x => le a x /\ (le x b /\ forall y, le a y ->
    // le y b -> le (F y) (F x + eps))`.
    let goal_pred = {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let lo = cle(d, p, a, x);
        let hi = cle(d, p, x, b);
        let fx = d.apply(f, &[x]);
        let padded = cadd(d, p, fx, eps);
        let forall_y = {
            let y_fv = d.fresh_fvar();
            let y = d.kernel().fvar(y_fv);
            let hay_ty = cle(d, p, a, y);
            let hyb_ty = cle(d, p, y, b);
            let fy = d.apply(f, &[y]);
            let concl = cle(d, p, fy, padded);
            let out = d.arrow(hyb_ty, concl);
            let out = d.arrow(hay_ty, out);
            d.pi_fv(y_fv, carrier, out)
        };
        let tail = d.and(hi, forall_y);
        let body = d.and(lo, tail);
        d.lam_fv(x_fv, carrier, body)
    };
    let goal = {
        let ex = d.kernel().const_(logic.exists_, vec![one_level]);
        d.apply(ex, &[carrier, goal_pred])
    };

    // `minor : forall x, (le a x /\ (le x b /\ le sup_val (F x + eps))) -> goal`
    let minor = {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let lo = cle(d, p, a, x);
        let hi = cle(d, p, x, b);
        let fx = d.apply(f, &[x]);
        let padded = cadd(d, p, fx, eps);
        let est = cle(d, p, sup_val, padded);
        let tail_ty = d.and(hi, est);
        let hp_ty = d.and(lo, tail_ty);

        let hp_fv = d.fresh_fvar();
        let hp = d.kernel().fvar(hp_fv);
        let hax = d.and_left(lo, tail_ty, hp);
        let h_rest = d.and_right(lo, tail_ty, hp);
        let hxb = d.and_left(hi, est, h_rest);
        let hest = d.and_right(hi, est, h_rest);

        // `forall y, le a y -> le y b -> le (F y) (F x + eps)`, and its proof
        // from `sup_on_ub` at `y` chained through `hest` via `le_trans`.
        let forall_y_ty = {
            let y_fv = d.fresh_fvar();
            let y = d.kernel().fvar(y_fv);
            let hay_ty = cle(d, p, a, y);
            let hyb_ty = cle(d, p, y, b);
            let fy = d.apply(f, &[y]);
            let concl = cle(d, p, fy, padded);
            let out = d.arrow(hyb_ty, concl);
            let out = d.arrow(hay_ty, out);
            d.pi_fv(y_fv, carrier, out)
        };
        let forall_y_proof = {
            let y_fv = d.fresh_fvar();
            let y = d.kernel().fvar(y_fv);
            let hay_ty = cle(d, p, a, y);
            let hyb_ty = cle(d, p, y, b);
            let fy = d.apply(f, &[y]);

            let hay_fv = d.fresh_fvar();
            let hay = d.kernel().fvar(hay_fv);
            let hyb_fv = d.fresh_fvar();
            let hyb = d.kernel().fvar(hyb_fv);

            let hub = d.lemma(p.sup_on_ub, &[f, a, b, hab, u, y, hay, hyb]);
            let body = d.lemma(p.le_trans, &[fy, sup_val, padded, hub, hest]);

            let out = d.lam_fv(hyb_fv, hyb_ty, body);
            let out = d.lam_fv(hay_fv, hay_ty, out);
            d.lam_fv(y_fv, carrier, out)
        };

        let tail_goal_ty = d.and(hi, forall_y_ty);
        let tail_goal = and_intro(d, p, hi, forall_y_ty, hxb, forall_y_proof);
        let whole = and_intro(d, p, lo, tail_goal_ty, hax, tail_goal);

        let ctor = d.kernel().const_(logic.exists_intro, vec![one_level]);
        let witnessed = d.apply(ctor, &[carrier, goal_pred, x, whole]);
        let inner = d.lam_fv(hp_fv, hp_ty, witnessed);
        d.lam_fv(x_fv, carrier, inner)
    };

    let proof = cexists_elim(d, p, carrier, hex_pred, goal, hex, minor);

    let ty = {
        let out = d.pi_fv(n_fv, nat, goal);
        let out = d.pi_fv(u_fv, u_ty, out);
        let out = d.pi_fv(hab_fv, hab_ty, out);
        let out = d.pi_fv(b_fv, carrier, out);
        let out = d.pi_fv(a_fv, carrier, out);
        d.pi_fv(f_fv, func_ty, out)
    };
    let value = {
        let out = d.lam_fv(n_fv, nat, proof);
        let out = d.lam_fv(u_fv, u_ty, out);
        let out = d.lam_fv(hab_fv, hab_ty, out);
        let out = d.lam_fv(b_fv, carrier, out);
        let out = d.lam_fv(a_fv, carrier, out);
        d.lam_fv(f_fv, func_ty, out)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.evt_approx_max,
        uparams: vec![],
        ty,
        value,
    })
}

/// Land `CReal.evt_approx_max`.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
pub(super) fn declare_evt_approx_max(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    declare_evt_approx_max_thm(d, p)
}
