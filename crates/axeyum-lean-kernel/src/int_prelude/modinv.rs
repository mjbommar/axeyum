//! `Int.ModEq.inverse_unique` — the modular inverse Bézout produces
//! ([`super::gcd::declare_modeq_inverse_exists`]) is unique up to `ModEq`.
//!
//! `gcd.rs` already has the existence half (`modEq_inverse_exists`, straight
//! from `gcd_eq_gcd_ab`) and `modeq.rs` already has the cancellation
//! workhorse (`modEq_cancel`, via `gauss_lemma`). This module supplies the
//! one missing piece: given *two* candidate inverses of the same `a` mod `n`,
//! they agree mod `n`.
//!
//! `Coprime a n` is not taken as an extra hypothesis — it is **derived** from
//! `ModEq n (a*b) one` itself. Unfolding that hypothesis through
//! `modEq_iff_dvd` gives a witness `w` with `one - a*b = n*w`, i.e.
//! `a*b + n*w = one` after rearranging — exactly the Bézout shape
//! `coprime_of_bezout_one` consumes. From there, `ModEq n (a*b) (a*c)`
//! (transitivity through the shared `one`) and `modEq_cancel` finish it.

use crate::BinderInfo;
use crate::KernelError;
use crate::expr::ExprId;
use crate::nat_prelude::NatOps;

use super::ops::IntDev;

/// Eliminate `witness : Int.dvd a b` into `target`, given
/// `minor : ∀ (c : Int), Eq Int b (a*c) → target`.
///
/// The same shape as the private `idvd_elim` in `gcd.rs`, built here instead
/// of imported (that one is not `pub(super)`, and this is five lines);
/// `super::dvd::dvd_predicate`/`super::dvd::idvd` — the pieces actually
/// shared — already are.
fn idvd_elim(
    d: &mut IntDev<'_>,
    a: ExprId,
    b: ExprId,
    target: ExprId,
    witness: ExprId,
    minor: ExprId,
) -> ExprId {
    let pred = super::dvd::dvd_predicate(d, a, b);
    let int_ty = d.int_ty();
    let one = d.level_one();
    let anon = d.anon_name();
    let exists_ty = {
        let name = d.int().logic.exists_;
        let e = d.kernel().const_(name, vec![one]);
        d.apply(e, &[int_ty, pred])
    };
    let motive = d.kernel().lam(anon, exists_ty, target, BinderInfo::Default);
    let rec_name = d.int().logic.exists_rec;
    let rec = d.kernel().const_(rec_name, vec![one]);
    d.apply(rec, &[int_ty, pred, motive, minor, witness])
}

/// `Int.modEq_inverse_unique :
/// ∀ n a b c, 0 < n → ModEq n (a*b) one → ModEq n (a*c) one → ModEq n b c`.
///
/// Two candidate inverses `b`, `c` of the same `a` mod `n` agree mod `n`.
///
/// Proof: `h1 : ModEq n (a*b) one` and `h2 : ModEq n (a*c) one` give
/// `ModEq n (a*b) (a*c)` by `modEq_trans h1 (modEq_symm h2)`. Unfolding `h1`
/// through `modEq_iff_dvd` gives a witness `w` with
/// `one - a*b = n*w` (built as `one + (-(a*b))` throughout, folding back to
/// `Int.sub` only at the boundary — the idiom `sub.rs`/`gcd.rs` already use);
/// adding `a*b` to both sides and simplifying the left with
/// `add_assoc`/`add_comm`/`add_neg`/`add_zero` gives `a*b + n*w = one`, which
/// is exactly `coprime_of_bezout_one a n b w`'s hypothesis, closing
/// `Coprime a n`. `modEq_cancel n a b c` then finishes from
/// `ModEq n (a*b) (a*c)`.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not check.
pub(super) fn declare_modeq_inverse_unique(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.mod_eq_inverse_unique, 4, &|d, v| {
        let (n, a, b, c) = (v[0], v[1], v[2], v[3]);
        let p = d.int();
        let zero = d.izero();
        let pos_ty = d.ilt(zero, n);
        let one_i = d.ione();
        let ab = d.imul(a, b);
        let ac = d.imul(a, c);
        let int_ty = d.int_ty();

        let modeq_ab1 = super::modeq::imodeq(d, n, ab, one_i);
        let modeq_ac1 = super::modeq::imodeq(d, n, ac, one_i);
        let modeq_bc = super::modeq::imodeq(d, n, b, c);

        let stmt = {
            let inner = d.arrow(modeq_ac1, modeq_bc);
            let with_h1 = d.arrow(modeq_ab1, inner);
            d.arrow(pos_ty, with_h1)
        };

        let h_pos_fv = d.fresh_fvar();
        let h_pos = d.kernel().fvar(h_pos_fv);
        let h1_fv = d.fresh_fvar();
        let h1 = d.kernel().fvar(h1_fv);
        let h2_fv = d.fresh_fvar();
        let h2 = d.kernel().fvar(h2_fv);

        // ModEq n (a*b) (a*c), via ModEq.trans h1 (ModEq.symm h2).
        let h2s = d.const_app(p.mod_eq_symm, &[n, ac, one_i, h2]);
        let hab_ac = d.const_app(p.mod_eq_trans, &[n, ab, one_i, ac, h1, h2s]);

        // n ∣ (one - a*b), from h1 via `modEq_iff_dvd`.
        let neg_ab = d.ineg(ab);
        let diff = d.iadd(one_i, neg_ab); // one + (-(a*b)) ~ one - a*b
        let dvd_ty = super::dvd::idvd(d, n, diff);
        let iff_ty = d.const_app(p.mod_eq_iff_dvd, &[n, ab, one_i, h_pos]);
        let mp = d.const_app(p.logic.iff_mp, &[modeq_ab1, dvd_ty, iff_ty]);
        let dvd_diff = d.apply(mp, &[h1]);

        // Eliminate the witness `w : diff = n*w` and close everything under it.
        let minor = {
            let w_fv = d.fresh_fvar();
            let w = d.kernel().fvar(w_fv);
            let nw = d.imul(n, w);
            let eq_fv = d.fresh_fvar();
            let eq_h = d.kernel().fvar(eq_fv);
            let eq_ty = d.ieq(diff, nw);

            // diff + a*b = n*w + a*b, by congruence on eq_h.
            let step_congr = d.icongr(diff, nw, eq_h, &|d, t| d.iadd(t, ab));
            let diff_ab = d.iadd(diff, ab);
            let nw_ab = d.iadd(nw, ab);

            // diff + a*b = one, i.e. (one + (-(a*b))) + a*b = one.
            let neg_ab_ab = d.iadd(neg_ab, ab);
            let ab_neg_ab = d.iadd(ab, neg_ab);
            let zero2 = d.izero();
            let comm1 = d.const_app(p.add_comm, &[neg_ab, ab]);
            let negcancel = d.const_app(p.add_neg, &[ab]);
            let (_, negab_ab_eq_zero) =
                d.ichain(neg_ab_ab, &[(ab_neg_ab, comm1), (zero2, negcancel)]);

            let assoc = d.const_app(p.add_assoc, &[one_i, neg_ab, ab]);
            let one_plus_negab_ab = d.iadd(one_i, neg_ab_ab);
            let congr_zero = d.icongr(neg_ab_ab, zero2, negab_ab_eq_zero, &|d, t| d.iadd(one_i, t));
            let one_plus_zero = d.iadd(one_i, zero2);
            let addzero = d.const_app(p.add_zero, &[one_i]);
            let (_, diff_ab_eq_one) = d.ichain(
                diff_ab,
                &[
                    (one_plus_negab_ab, assoc),
                    (one_plus_zero, congr_zero),
                    (one_i, addzero),
                ],
            );

            // n*w + a*b = one (from diff+a*b = n*w+a*b and diff+a*b = one).
            let step_congr_rev = d.isymm(diff_ab, nw_ab, step_congr);
            let nw_ab_eq_one = d.itrans(nw_ab, diff_ab, one_i, step_congr_rev, diff_ab_eq_one);

            // a*b + n*w = one — the Bézout shape `coprime_of_bezout_one` wants.
            let ab_nw = d.iadd(ab, nw);
            let comm_final = d.const_app(p.add_comm, &[ab, nw]);
            let ab_nw_eq_one = d.itrans(ab_nw, nw_ab, one_i, comm_final, nw_ab_eq_one);

            let coprime_an = d.const_app(p.coprime_of_bezout_one, &[a, n, b, w, ab_nw_eq_one]);
            let result = d.const_app(p.mod_eq_cancel, &[n, a, b, c, h_pos, coprime_an, hab_ac]);

            let with_eq = d.lam_fv(eq_fv, eq_ty, result);
            d.lam_fv(w_fv, int_ty, with_eq)
        };

        let eliminated = idvd_elim(d, n, diff, modeq_bc, dvd_diff, minor);
        let with_h2 = d.lam_fv(h2_fv, modeq_ac1, eliminated);
        let with_h1 = d.lam_fv(h1_fv, modeq_ab1, with_h2);
        let proof = d.lam_fv(h_pos_fv, pos_ty, with_h1);
        (stmt, proof)
    })?;
    Ok(())
}
