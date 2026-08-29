//! `Int.dvd a b := ∃ c, b = a * c`, and its basic laws.
//!
//! Mirrors the `Nat` development (`nat_prelude/divisibility.rs`) bit for
//! bit: a checked `Definition` over the logic prelude's `Exists`, and every
//! law a witness-carrying `Exists.intro`/`Exists.rec` construction — no
//! proposition here is admitted as an axiom. `Int.euclidean_decomposition`
//! already uses `Exists`/`Exists.intro` at level 1 (`int_prelude/euclid.rs`'s
//! `int_exists`/`int_exists_intro`); this module needs the same shape but
//! also `Exists.rec` (to *consume* a divisibility witness, not just produce
//! one), so it builds its own thin wrappers rather than importing those.

use super::defs::DERIVED_HEIGHT;
use super::ops::IntDev;
use crate::BinderInfo;
use crate::KernelError;
use crate::env::{Declaration, ReducibilityHint};
use crate::expr::ExprId;
use crate::nat_prelude::NatOps;

/// `fun (c : Int) => Eq Int b (a * c)` — the predicate `Int.dvd a b` existentially
/// quantifies.
pub(super) fn dvd_predicate(d: &mut IntDev<'_>, a: ExprId, b: ExprId) -> ExprId {
    let int_ty = d.int_ty();
    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let ac = d.imul(a, c);
    let body = d.ieq(b, ac);
    d.lam_fv(c_fv, int_ty, body)
}

/// `Int.dvd a b`, i.e. `d.const_app(p.dvd, &[a, b])`.
pub(super) fn idvd(d: &mut IntDev<'_>, a: ExprId, b: ExprId) -> ExprId {
    let f = d.int().dvd;
    d.const_app(f, &[a, b])
}

/// Admit `Int.dvd : Int → Int → Prop := fun a b => ∃ c, b = a * c`.
///
/// # Errors
///
/// Returns the trusted gate's rejection (a malformed statement, or a name
/// conflict).
pub(super) fn declare_dvd_definition(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    let int_ty = d.int_ty();
    let anon = d.anon_name();
    let prop = d.kernel().sort_zero();
    let one = d.level_one();

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let pred = dvd_predicate(d, a, b);
    let exists = d.kernel().const_(p.logic.exists_, vec![one]);
    let body = d.apply(exists, &[int_ty, pred]);
    let value = {
        let inner = d.lam_fv(b_fv, int_ty, body);
        d.lam_fv(a_fv, int_ty, inner)
    };
    let ty = {
        let inner = d.kernel().pi(anon, int_ty, prop, BinderInfo::Default);
        d.kernel().pi(anon, int_ty, inner, BinderInfo::Default)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.dvd,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(DERIVED_HEIGHT),
    })
}

/// `Int.dvd_refl : ∀ a, dvd a a` — witness `c = one`, via `Int.mul_one`.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
pub(super) fn declare_dvd_refl(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.dvd_refl, 1, &|d, v| {
        let a = v[0];
        let one_c = d.ione();
        let product = d.imul(a, one_c);
        let product_eq = {
            let name = d.int().mul_one;
            d.const_app(name, &[a])
        };
        let witness_eq = d.isymm(product, a, product_eq);
        let predicate = dvd_predicate(d, a, a);
        let one_level = d.level_one();
        let intro_name = d.int().logic.exists_intro;
        let intro = d.kernel().const_(intro_name, vec![one_level]);
        let int_ty = d.int_ty();
        let proof = d.apply(intro, &[int_ty, predicate, one_c, witness_eq]);
        let stmt = idvd(d, a, a);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Int.dvd_mul_right : ∀ a b, dvd a (a * b)` — witness `c = b`, by `Eq.refl`.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
pub(super) fn declare_dvd_mul_right(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.dvd_mul_right, 2, &|d, v| {
        let (a, b) = (v[0], v[1]);
        let ab = d.imul(a, b);
        let pred = dvd_predicate(d, a, ab);
        let witness_proof = d.irefl(ab);
        let one_level = d.level_one();
        let intro_name = d.int().logic.exists_intro;
        let intro = d.kernel().const_(intro_name, vec![one_level]);
        let int_ty = d.int_ty();
        let proof = d.apply(intro, &[int_ty, pred, b, witness_proof]);
        let stmt = idvd(d, a, ab);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Int.dvd_mul_left : ∀ a b, dvd a (b * a)` — witness `c = b`, by
/// `Int.mul_comm`.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
pub(super) fn declare_dvd_mul_left(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.dvd_mul_left, 2, &|d, v| {
        let (a, b) = (v[0], v[1]);
        let ba = d.imul(b, a);
        let pred = dvd_predicate(d, a, ba);
        let witness_proof = {
            let name = d.int().mul_comm;
            d.const_app(name, &[b, a])
        };
        let one_level = d.level_one();
        let intro_name = d.int().logic.exists_intro;
        let intro = d.kernel().const_(intro_name, vec![one_level]);
        let int_ty = d.int_ty();
        let proof = d.apply(intro, &[int_ty, pred, b, witness_proof]);
        let stmt = idvd(d, a, ba);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Int.dvd_trans : ∀ a b c, dvd a b → dvd b c → dvd a c` — compose the two
/// existential factors and use `Int.mul_assoc` to expose their product as the
/// new witness.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
pub(super) fn declare_dvd_trans(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.dvd_trans, 3, &|d, v| {
        let (a, b, c) = (v[0], v[1], v[2]);
        let hab_ty = idvd(d, a, b);
        let hbc_ty = idvd(d, b, c);
        let target = idvd(d, a, c);
        let hab_fv = d.fresh_fvar();
        let hab = d.kernel().fvar(hab_fv);
        let hbc_fv = d.fresh_fvar();
        let hbc = d.kernel().fvar(hbc_fv);
        let pred_ab = dvd_predicate(d, a, b);
        let pred_bc = dvd_predicate(d, b, c);
        let int_ty = d.int_ty();
        let one_level = d.level_one();
        let anon = d.anon_name();

        let motive_ab = d.kernel().lam(anon, hab_ty, target, BinderInfo::Default);
        let minor_ab = {
            let q_fv = d.fresh_fvar();
            let q = d.kernel().fvar(q_fv);
            let aq = d.imul(a, q);
            let eq_ab_fv = d.fresh_fvar();
            let eq_ab_ty = d.ieq(b, aq);
            let eq_ab = d.kernel().fvar(eq_ab_fv);
            let motive_bc = d.kernel().lam(anon, hbc_ty, target, BinderInfo::Default);
            let minor_bc = {
                let r_fv = d.fresh_fvar();
                let r = d.kernel().fvar(r_fv);
                let br = d.imul(b, r);
                let eq_bc_fv = d.fresh_fvar();
                let eq_bc_ty = d.ieq(c, br);
                let eq_bc = d.kernel().fvar(eq_bc_fv);
                let aqr = d.imul(aq, r);
                let qr = d.imul(q, r);
                let target_product = d.imul(a, qr);
                let replace_b = d.icongr(b, aq, eq_ab, &|d, x| d.imul(x, r));
                let associate = {
                    let name = d.int().mul_assoc;
                    d.const_app(name, &[a, q, r])
                };
                let (_, witness_eq) = d.ichain(
                    c,
                    &[(br, eq_bc), (aqr, replace_b), (target_product, associate)],
                );
                let predicate = dvd_predicate(d, a, c);
                let intro_name = d.int().logic.exists_intro;
                let intro = d.kernel().const_(intro_name, vec![one_level]);
                let body = d.apply(intro, &[int_ty, predicate, qr, witness_eq]);
                let with_eq = d.lam_fv(eq_bc_fv, eq_bc_ty, body);
                d.lam_fv(r_fv, int_ty, with_eq)
            };
            let exists_rec_name = d.int().logic.exists_rec;
            let exists_rec = d.kernel().const_(exists_rec_name, vec![one_level]);
            let body = d.apply(exists_rec, &[int_ty, pred_bc, motive_bc, minor_bc, hbc]);
            let with_eq = d.lam_fv(eq_ab_fv, eq_ab_ty, body);
            d.lam_fv(q_fv, int_ty, with_eq)
        };
        let exists_rec_name = d.int().logic.exists_rec;
        let exists_rec = d.kernel().const_(exists_rec_name, vec![one_level]);
        let body = d.apply(exists_rec, &[int_ty, pred_ab, motive_ab, minor_ab, hab]);
        let proof = {
            let with_hbc = d.lam_fv(hbc_fv, hbc_ty, body);
            d.lam_fv(hab_fv, hab_ty, with_hbc)
        };
        let hbc_to_target = d.arrow(hbc_ty, target);
        let stmt = d.arrow(hab_ty, hbc_to_target);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Int.dvd_add : ∀ a m n, dvd a m → dvd a n → dvd a (m + n)` — combine the
/// two witnesses `q1,q2` into `q1+q2` via `Int.left_distrib`.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
pub(super) fn declare_dvd_add(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.dvd_add, 3, &|d, v| {
        let (a, m, n) = (v[0], v[1], v[2]);
        let h1_ty = idvd(d, a, m);
        let h2_ty = idvd(d, a, n);
        let mn = d.iadd(m, n);
        let goal = idvd(d, a, mn);
        let arrow2 = d.arrow(h2_ty, goal);
        let stmt = d.arrow(h1_ty, arrow2);

        let p1 = dvd_predicate(d, a, m);
        let p2 = dvd_predicate(d, a, n);
        let one_level = d.level_one();
        let int_ty = d.int_ty();

        let h1_fv = d.fresh_fvar();
        let h1 = d.kernel().fvar(h1_fv);
        let h2_fv = d.fresh_fvar();
        let h2 = d.kernel().fvar(h2_fv);

        let motive_for = |d: &mut IntDev<'_>, pred: ExprId| {
            let exists_name = d.int().logic.exists_;
            let exists = d.kernel().const_(exists_name, vec![one_level]);
            let int_ty = d.int_ty();
            let dom = d.apply(exists, &[int_ty, pred]);
            let anon = d.anon_name();
            d.kernel().lam(anon, dom, goal, BinderInfo::Default)
        };

        let minor1 = {
            let q1_fv = d.fresh_fvar();
            let q1 = d.kernel().fvar(q1_fv);
            let aq1 = d.imul(a, q1);
            let e1_fv = d.fresh_fvar();
            let e1_ty = d.ieq(m, aq1);
            let e1 = d.kernel().fvar(e1_fv);
            let minor2 = {
                let q2_fv = d.fresh_fvar();
                let q2 = d.kernel().fvar(q2_fv);
                let aq2 = d.imul(a, q2);
                let e2_fv = d.fresh_fvar();
                let e2_ty = d.ieq(n, aq2);
                let e2 = d.kernel().fvar(e2_fv);

                let s1 = d.iadd(aq1, n);
                let c1 = d.icongr(m, aq1, e1, &|d, t| d.iadd(t, n));
                let s2 = d.iadd(aq1, aq2);
                let c2 = d.icongr(n, aq2, e2, &|d, t| d.iadd(aq1, t));
                let q12 = d.iadd(q1, q2);
                let aq12 = d.imul(a, q12);
                let h_distrib = {
                    let name = d.int().left_distrib;
                    d.const_app(name, &[a, q1, q2])
                };
                let c3 = d.isymm(aq12, s2, h_distrib);
                let (_, witness_proof) = d.ichain(mn, &[(s1, c1), (s2, c2), (aq12, c3)]);
                let pred = dvd_predicate(d, a, mn);
                let intro_name = d.int().logic.exists_intro;
                let intro = d.kernel().const_(intro_name, vec![one_level]);
                let body = d.apply(intro, &[int_ty, pred, q12, witness_proof]);
                let with_e2 = d.lam_fv(e2_fv, e2_ty, body);
                d.lam_fv(q2_fv, int_ty, with_e2)
            };
            let motive2 = motive_for(d, p2);
            let rec_name = d.int().logic.exists_rec;
            let rec = d.kernel().const_(rec_name, vec![one_level]);
            let inner = d.apply(rec, &[int_ty, p2, motive2, minor2, h2]);
            let with_e1 = d.lam_fv(e1_fv, e1_ty, inner);
            d.lam_fv(q1_fv, int_ty, with_e1)
        };
        let motive1 = motive_for(d, p1);
        let rec_name = d.int().logic.exists_rec;
        let rec = d.kernel().const_(rec_name, vec![one_level]);
        let body = d.apply(rec, &[int_ty, p1, motive1, minor1, h1]);

        let with_h2 = d.lam_fv(h2_fv, h2_ty, body);
        let proof = d.lam_fv(h1_fv, h1_ty, with_h2);
        (stmt, proof)
    })?;
    Ok(())
}

// ---------------------------------------------------------------------------
// `Int.emod_eq_zero_iff_dvd` — the bridge between division and divisibility,
// for a positive divisor.
// ---------------------------------------------------------------------------
//
// `mp` (`a%b=0 → b∣a`) needs only `Int.ediv_add_emod`: with the remainder
// zeroed out, the division algorithm's equation IS the divisibility witness
// (`c := a/b`). `mpr` (`b∣a → a%b=0`) is where `Int.ediv_emod_unique`
// earns its keep: a divisibility witness `c` gives a SECOND
// quotient/remainder decomposition of `a` at divisor `b` (`q=c, r=0`), and
// uniqueness against the canonical one (`q=a/b, r=a%b`) forces `a%b = 0`.
//
// Scoped to `0 < b` for the same reason [`declare_ediv_emod_unique`] is: the
// only proved bound on `Int.emod`'s magnitude is [`declare_emod_lt_of_pos`]
// (`b>0`) — there is no proved analogue for `b<0` (it would need a
// `natAbs`-based bound, not yet built), so a general (`b≠0`) statement is
// honestly out of reach for now. `b=0` is a separate, even easier case
// (`a%0=0 ↔ 0∣a` collapses to `a=0 ↔ a=0`) that this development also has
// not bothered to state yet.

/// `Not (Eq Int b Int.zero)` from `0 < b` — `emod_nonneg`'s hypothesis is
/// stated as inequality-freedom rather than positivity, so this is the small
/// bridge every positive-divisor use of it needs.
pub(super) fn ne_zero_of_pos(d: &mut IntDev<'_>, b: ExprId, h_pos: ExprId) -> ExprId {
    let zero = d.izero();
    let heq0_fv = d.fresh_fvar();
    let heq0 = d.kernel().fvar(heq0_fv);
    let heq0_ty = d.ieq(b, zero);
    let rewritten = d.int_eq_rewrite(b, zero, heq0, h_pos, &|d, x| {
        let zero = d.izero();
        d.ilt(zero, x)
    });
    let lt_irrefl_name = d.int().lt_irrefl;
    let lt_irrefl_term = d.const_app(lt_irrefl_name, &[zero]);
    let false_proof = d.apply(lt_irrefl_term, &[rewritten]);
    d.lam_fv(heq0_fv, heq0_ty, false_proof)
}

/// `Int.emod_eq_zero_iff_dvd : ∀ a b, 0 < b → (a % b = 0 ↔ b ∣ a)`.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
pub(super) fn declare_emod_eq_zero_iff_dvd(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.emod_eq_zero_iff_dvd, 2, &|d, v| {
        let (a, b) = (v[0], v[1]);
        let zero = d.izero();
        let pos_ty = d.ilt(zero, b);
        let ediv_ab = d.iediv(a, b);
        let emod_ab = d.iemod(a, b);
        let zero_eq_ty = d.ieq(emod_ab, zero);
        let dvd_ty = idvd(d, b, a);
        let iff_ty = {
            let name = d.int().logic.iff;
            d.const_app(name, &[zero_eq_ty, dvd_ty])
        };
        let stmt = d.arrow(pos_ty, iff_ty);

        let h_pos_fv = d.fresh_fvar();
        let h_pos = d.kernel().fvar(h_pos_fv);
        let int_ty = d.int_ty();
        let one_level = d.level_one();

        // mp : a%b=0 -> b∣a
        let mp = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let mul_q = d.imul(b, ediv_ab);
            let sum_with_emod = d.iadd(mul_q, emod_ab);
            let full_eq = {
                // `Int.ediv_add_emod a b : Eq Int (b*(a/b)+a%b) a`.
                let name = d.int().ediv_add_emod;
                d.const_app(name, &[a, b])
            };
            let full_eq_rev = d.isymm(sum_with_emod, a, full_eq);
            let sum_with_zero = d.iadd(mul_q, zero);
            let step = d.icongr(emod_ab, zero, h, &|d, x| {
                let mq = d.imul(b, ediv_ab);
                d.iadd(mq, x)
            });
            let add_zero_q = {
                let name = d.int().add_zero;
                d.const_app(name, &[mul_q])
            };
            let (_, chained) =
                d.ichain(sum_with_emod, &[(sum_with_zero, step), (mul_q, add_zero_q)]);
            let a_eq_mulq = d.itrans(a, sum_with_emod, mul_q, full_eq_rev, chained);
            let pred = dvd_predicate(d, b, a);
            let intro_name = d.int().logic.exists_intro;
            let intro = d.kernel().const_(intro_name, vec![one_level]);
            let proof = d.apply(intro, &[int_ty, pred, ediv_ab, a_eq_mulq]);
            d.lam_fv(h_fv, zero_eq_ty, proof)
        };

        // mpr : b∣a -> a%b=0
        let mpr = {
            let hw_fv = d.fresh_fvar();
            let hw = d.kernel().fvar(hw_fv);
            let pred = dvd_predicate(d, b, a);
            let anon = d.anon_name();
            let exists_ty = {
                let name = d.int().logic.exists_;
                let exists = d.kernel().const_(name, vec![one_level]);
                d.apply(exists, &[int_ty, pred])
            };
            let motive = d
                .kernel()
                .lam(anon, exists_ty, zero_eq_ty, BinderInfo::Default);

            let minor = {
                let c_fv = d.fresh_fvar();
                let c = d.kernel().fvar(c_fv);
                let bc = d.imul(b, c);
                let heq_ty = d.ieq(a, bc);
                let heq_fv = d.fresh_fvar();
                let heq = d.kernel().fvar(heq_fv);

                // eq1 : a = b*c + 0
                let bc_plus_zero = d.iadd(bc, zero);
                let add_zero_bc_rev = {
                    let name = d.int().add_zero;
                    let fwd = d.const_app(name, &[bc]);
                    d.isymm(bc_plus_zero, bc, fwd)
                };
                let eq1 = d.itrans(a, bc, bc_plus_zero, heq, add_zero_bc_rev);
                let lower1 = {
                    let name = d.int().le_refl;
                    d.const_app(name, &[zero])
                };
                let upper1 = h_pos;
                let eq2 = {
                    // `Int.ediv_add_emod a b : Eq Int (b*(a/b)+a%b) a` — reversed
                    // from the `a = b*q2+r2` shape `Int.ediv_emod_unique` wants.
                    let name = d.int().ediv_add_emod;
                    let raw = d.const_app(name, &[a, b]);
                    let mul_q2 = d.imul(b, ediv_ab);
                    let sum2 = d.iadd(mul_q2, emod_ab);
                    d.isymm(sum2, a, raw)
                };
                let b_ne_zero = ne_zero_of_pos(d, b, h_pos);
                let lower2 = {
                    let name = d.int().emod_nonneg;
                    d.const_app(name, &[a, b, b_ne_zero])
                };
                let upper2 = {
                    let name = d.int().emod_lt_of_pos;
                    d.const_app(name, &[a, b, h_pos])
                };

                let unique_name = d.int().ediv_emod_unique;
                let and_result = d.const_app(
                    unique_name,
                    &[
                        a, b, c, zero, ediv_ab, emod_ab, h_pos, eq1, lower1, upper1, eq2, lower2,
                        upper2,
                    ],
                );
                let eq_q_ty = d.ieq(c, ediv_ab);
                let eq_r_ty = d.ieq(zero, emod_ab);
                let eq_r = d.and_right(eq_q_ty, eq_r_ty, and_result);
                let body = d.isymm(zero, emod_ab, eq_r);
                let with_heq = d.lam_fv(heq_fv, heq_ty, body);
                d.lam_fv(c_fv, int_ty, with_heq)
            };
            let exists_rec_name = d.int().logic.exists_rec;
            let exists_rec = d.kernel().const_(exists_rec_name, vec![one_level]);
            let body = d.apply(exists_rec, &[int_ty, pred, motive, minor, hw]);
            d.lam_fv(hw_fv, dvd_ty, body)
        };

        let intro_name = d.int().logic.iff_intro;
        let iff_proof = d.const_app(intro_name, &[zero_eq_ty, dvd_ty, mp, mpr]);
        let proof = d.lam_fv(h_pos_fv, pos_ty, iff_proof);
        (stmt, proof)
    })?;
    Ok(())
}

// ---------------------------------------------------------------------------
// `Int.emod_eq_zero_iff_dvd_general` — the sign-general bridge between
// division and divisibility.
// ---------------------------------------------------------------------------
//
// Identical proof shape to [`declare_emod_eq_zero_iff_dvd`], with every
// positive-only ingredient swapped for its sign-general sibling: the
// hypothesis is `b ≠ 0` rather than `0 < b`, the upper bound on the
// remainder comes from `Int.emod_natAbs_bound` rather than
// `Int.emod_lt_of_pos`, and the uniqueness step is
// `Int.ediv_emod_unique_general` rather than `Int.ediv_emod_unique`.
// `Int.emod_nonneg` was ALREADY sign-general (`b ≠ 0`, not `0 < b`), so it
// carries over unchanged. This is the fourth lemma the `int-emod-negative`
// lane's handoff (`docs/plan/status/242-int-emod-negative.md`) named as
// constructible from its two landed pieces but did not itself build.

/// `Int.emod_eq_zero_iff_dvd_general : ∀ a b, Not (Eq Int b zero) →
/// (a % b = 0 ↔ b ∣ a)`.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
pub(super) fn declare_emod_eq_zero_iff_dvd_general(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.emod_eq_zero_iff_dvd_general, 2, &|d, v| {
        let (a, b) = (v[0], v[1]);
        let zero = d.izero();
        let ne_ty = {
            let eq_ty = d.ieq(b, zero);
            d.not(eq_ty)
        };
        let ediv_ab = d.iediv(a, b);
        let emod_ab = d.iemod(a, b);
        let zero_eq_ty = d.ieq(emod_ab, zero);
        let dvd_ty = idvd(d, b, a);
        let iff_ty = {
            let name = d.int().logic.iff;
            d.const_app(name, &[zero_eq_ty, dvd_ty])
        };
        let stmt = d.arrow(ne_ty, iff_ty);

        let h_ne_fv = d.fresh_fvar();
        let h_ne = d.kernel().fvar(h_ne_fv);
        let int_ty = d.int_ty();
        let one_level = d.level_one();

        // mp : a%b=0 -> b∣a — verbatim [`declare_emod_eq_zero_iff_dvd`]'s
        // `mp`, which never used the positivity hypothesis at all (it only
        // needs `Int.ediv_add_emod`, unconditional in `b`).
        let mp = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let mul_q = d.imul(b, ediv_ab);
            let sum_with_emod = d.iadd(mul_q, emod_ab);
            let full_eq = {
                let name = d.int().ediv_add_emod;
                d.const_app(name, &[a, b])
            };
            let full_eq_rev = d.isymm(sum_with_emod, a, full_eq);
            let sum_with_zero = d.iadd(mul_q, zero);
            let step = d.icongr(emod_ab, zero, h, &|d, x| {
                let mq = d.imul(b, ediv_ab);
                d.iadd(mq, x)
            });
            let add_zero_q = {
                let name = d.int().add_zero;
                d.const_app(name, &[mul_q])
            };
            let (_, chained) =
                d.ichain(sum_with_emod, &[(sum_with_zero, step), (mul_q, add_zero_q)]);
            let a_eq_mulq = d.itrans(a, sum_with_emod, mul_q, full_eq_rev, chained);
            let pred = dvd_predicate(d, b, a);
            let intro_name = d.int().logic.exists_intro;
            let intro = d.kernel().const_(intro_name, vec![one_level]);
            let proof = d.apply(intro, &[int_ty, pred, ediv_ab, a_eq_mulq]);
            d.lam_fv(h_fv, zero_eq_ty, proof)
        };

        // mpr : b∣a -> a%b=0
        let mpr = {
            let hw_fv = d.fresh_fvar();
            let hw = d.kernel().fvar(hw_fv);
            let pred = dvd_predicate(d, b, a);
            let anon = d.anon_name();
            let exists_ty = {
                let name = d.int().logic.exists_;
                let exists = d.kernel().const_(name, vec![one_level]);
                d.apply(exists, &[int_ty, pred])
            };
            let motive = d
                .kernel()
                .lam(anon, exists_ty, zero_eq_ty, BinderInfo::Default);

            let minor = {
                let c_fv = d.fresh_fvar();
                let c = d.kernel().fvar(c_fv);
                let bc = d.imul(b, c);
                let heq_ty = d.ieq(a, bc);
                let heq_fv = d.fresh_fvar();
                let heq = d.kernel().fvar(heq_fv);

                // eq1 : a = b*c + 0
                let bc_plus_zero = d.iadd(bc, zero);
                let add_zero_bc_rev = {
                    let name = d.int().add_zero;
                    let fwd = d.const_app(name, &[bc]);
                    d.isymm(bc_plus_zero, bc, fwd)
                };
                let eq1 = d.itrans(a, bc, bc_plus_zero, heq, add_zero_bc_rev);
                let lower1 = {
                    let name = d.int().le_refl;
                    d.const_app(name, &[zero])
                };
                let upper1 = {
                    // This branch's required upper bound is `zero < ofNat
                    // (natAbs b)` (r1 is `zero`, so `unique_hyps_general`'s
                    // `upper1` is literally that). Unlike the positive-only
                    // proof (where `h_pos : 0 < b` already IS this type),
                    // `h_ne : b ≠ 0` is not itself an inequality, so derive
                    // the bound via `Int.emod_nonneg`/`Int.emod_natAbs_bound`
                    // at `a, b` and `Int.lt_of_le_of_lt`
                    // (`0 ≤ emod a b`, `emod a b < ofNat (natAbs b)` ⟹
                    // `0 < ofNat (natAbs b)`).
                    let emod_nonneg_ab = {
                        let n = d.int().emod_nonneg;
                        d.const_app(n, &[a, b, h_ne])
                    };
                    let emod_lt_bound = {
                        let n = d.int().emod_natabs_bound;
                        d.const_app(n, &[a, b, h_ne])
                    };
                    let bound = {
                        let f = d.int().nat_abs;
                        let nat_abs_b = d.const_app(f, &[b]);
                        d.of_nat(nat_abs_b)
                    };
                    let name = d.int().lt_of_le_of_lt;
                    d.const_app(
                        name,
                        &[zero, emod_ab, bound, emod_nonneg_ab, emod_lt_bound],
                    )
                };
                let eq2 = {
                    // `Int.ediv_add_emod a b : Eq Int (b*(a/b)+a%b) a` —
                    // reversed from the `a = b*q2+r2` shape
                    // `Int.ediv_emod_unique_general` wants.
                    let name = d.int().ediv_add_emod;
                    let raw = d.const_app(name, &[a, b]);
                    let mul_q2 = d.imul(b, ediv_ab);
                    let sum2 = d.iadd(mul_q2, emod_ab);
                    d.isymm(sum2, a, raw)
                };
                let lower2 = {
                    let name = d.int().emod_nonneg;
                    d.const_app(name, &[a, b, h_ne])
                };
                let upper2 = {
                    let name = d.int().emod_natabs_bound;
                    d.const_app(name, &[a, b, h_ne])
                };

                let unique_name = d.int().ediv_emod_unique_general;
                let and_result = d.const_app(
                    unique_name,
                    &[
                        a, b, c, zero, ediv_ab, emod_ab, h_ne, eq1, lower1, upper1, eq2, lower2,
                        upper2,
                    ],
                );
                let eq_q_ty = d.ieq(c, ediv_ab);
                let eq_r_ty = d.ieq(zero, emod_ab);
                let eq_r = d.and_right(eq_q_ty, eq_r_ty, and_result);
                let body = d.isymm(zero, emod_ab, eq_r);
                let with_heq = d.lam_fv(heq_fv, heq_ty, body);
                d.lam_fv(c_fv, int_ty, with_heq)
            };
            let exists_rec_name = d.int().logic.exists_rec;
            let exists_rec = d.kernel().const_(exists_rec_name, vec![one_level]);
            let body = d.apply(exists_rec, &[int_ty, pred, motive, minor, hw]);
            d.lam_fv(hw_fv, dvd_ty, body)
        };

        let intro_name = d.int().logic.iff_intro;
        let iff_proof = d.const_app(intro_name, &[zero_eq_ty, dvd_ty, mp, mpr]);
        let proof = d.lam_fv(h_ne_fv, ne_ty, iff_proof);
        (stmt, proof)
    })?;
    Ok(())
}
