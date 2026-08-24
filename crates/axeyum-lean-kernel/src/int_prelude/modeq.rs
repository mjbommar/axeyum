//! `Int.ModEq n a b := emod a n = emod b n` — congruence modulo `n`, our own
//! universe's version of the Mathlib `Int.ModEq` family.
//!
//! `refl`/`symm`/`trans` are exactly `Eq.refl`/`Eq.symm`/`Eq.trans` once the
//! definition unfolds — no new proof technique, just `Eq`'s own equivalence
//! laws transported through a definitional layer.
//!
//! ## `Int.modEq_iff_dvd`, and what it unblocked
//!
//! `Int.modEq_iff_dvd : 0 < n → (ModEq n a b ↔ n ∣ (b - a))` — the bridge
//! from `ModEq` to `Int.dvd` — is declared below
//! ([`declare_modeq_iff_dvd`]), not merely planned: `Int.mul_sub`/`Int.mul_neg`
//! (`sub.rs`) supplied the missing distributivity, and the actual shortest
//! route to it turned out to go through two small "un-subtract" identities
//! private to this module ([`cancel_neg_add`], [`cancel_common_addend`])
//! rather than `mul_sub`/`mul_neg` directly — see the note above
//! [`declare_modeq_iff_dvd`] for the full story of that deviation. Every
//! multiplicative and additive `ModEq` congruence in this module, and the
//! modular inverse in `gcd.rs`, is built on top of this bridge.
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
pub(super) fn imodeq(d: &mut IntDev<'_>, n: ExprId, a: ExprId, b: ExprId) -> ExprId {
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

// ---------------------------------------------------------------------------
// `Int.modEq_iff_dvd`, and the additive `ModEq` congruences it unblocks.
// ---------------------------------------------------------------------------
//
// The blocker the previous slice recorded was `b - a = n*((b/n)-(a/n))`,
// which it traced to two missing distributivity lemmas (`mul_neg`, `mul_sub`,
// now in `sub.rs`). Once `Int.sub` exists, the ACTUAL shortest path turned out
// to route through two small "un-subtract" identities instead
// (`cancel_neg_add`, `cancel_common_addend`, both private to this module) —
// `mul_sub`/`mul_neg` are still built (the brief asked for them by name, and
// they are genuine, reusable ring lemmas), but this derivation does not
// happen to call them, the same kind of honest deviation `division.rs`'s
// `ediv_emod_unique` recorded when its briefed route (`mul_le_mul_of_nonneg_left`
// + `no_int_between`) turned out unnecessary.

/// `Eq Int (add (add x (neg y)) y) x` — the "un-subtract" identity: from
/// `x + (-y) = z` you get `x = z + y`. `Int.add_neg_cancel_right`
/// (`(x+y)+(-y)=x`) is the mirror image; this is the direction it does not
/// cover, and `Int.modEq_iff_dvd` needs both.
pub(super) fn cancel_neg_add(d: &mut IntDev<'_>, x: ExprId, y: ExprId) -> ExprId {
    let p = d.int();
    let neg_y = d.ineg(y);
    let x_negy = d.iadd(x, neg_y);
    let start = d.iadd(x_negy, y);

    let inner = d.iadd(neg_y, y);
    let step1_rhs = d.iadd(x, inner);
    let step1_proof = d.const_app(p.add_assoc, &[x, neg_y, y]);

    let zero = d.izero();
    let step2_rhs = d.iadd(x, zero);
    let neg_y_add_y = {
        let comm = d.const_app(p.add_comm, &[neg_y, y]);
        let y_neg_y = d.iadd(y, neg_y);
        let add_neg_proof = d.const_app(p.add_neg, &[y]);
        d.itrans(inner, y_neg_y, zero, comm, add_neg_proof)
    };
    let step2_proof = d.icongr(inner, zero, neg_y_add_y, &|d, t| d.iadd(x, t));

    let step3_proof = d.const_app(p.add_zero, &[x]);

    let (_, proof) = d.ichain(
        start,
        &[
            (step1_rhs, step1_proof),
            (step2_rhs, step2_proof),
            (x, step3_proof),
        ],
    );
    proof
}

/// `Eq Int (neg (add a b)) (add (neg a) (neg b))` — negation distributes over
/// `add`, via `neg t = mul (neg one) t` and `Int.left_distrib`. Private:
/// [`declare_modeq_add_right`] is the only caller (through
/// [`cancel_common_addend`]).
fn neg_add(d: &mut IntDev<'_>, a: ExprId, b: ExprId) -> ExprId {
    let p = d.int();
    let ab = d.iadd(a, b);
    let start = d.ineg(ab);

    let one = d.ione();
    let neg_one = d.ineg(one);
    let mul_negone_ab = d.imul(neg_one, ab);
    let neg_one_mul_ab = d.const_app(p.neg_one_mul, &[ab]);
    let step1_proof = d.isymm(mul_negone_ab, start, neg_one_mul_ab);

    let mul_na = d.imul(neg_one, a);
    let mul_nb = d.imul(neg_one, b);
    let step2_rhs = d.iadd(mul_na, mul_nb);
    let step2_proof = d.const_app(p.left_distrib, &[neg_one, a, b]);

    let neg_a = d.ineg(a);
    let step3_rhs = d.iadd(neg_a, mul_nb);
    let neg_one_mul_a = d.const_app(p.neg_one_mul, &[a]);
    let step3_proof = d.icongr(mul_na, neg_a, neg_one_mul_a, &|d, x| d.iadd(x, mul_nb));

    let neg_b = d.ineg(b);
    let step4_rhs = d.iadd(neg_a, neg_b);
    let neg_one_mul_b = d.const_app(p.neg_one_mul, &[b]);
    let step4_proof = d.icongr(mul_nb, neg_b, neg_one_mul_b, &|d, x| d.iadd(neg_a, x));

    let (_, proof) = d.ichain(
        start,
        &[
            (mul_negone_ab, step1_proof),
            (step2_rhs, step2_proof),
            (step3_rhs, step3_proof),
            (step4_rhs, step4_proof),
        ],
    );
    proof
}

/// `Eq Int (add (add x r) (neg (add y r))) (add x (neg y))` — `(X+r)-(Y+r) =
/// X-Y`, the common-addend cancellation [`declare_modeq_add_right`] needs.
///
/// `pub(super)`, not private: `wilson.rs`'s difference-of-squares expansion
/// needs exactly this shape and reuses it rather than duplicating a
/// ~40-line derivation.
pub(super) fn cancel_common_addend(d: &mut IntDev<'_>, x: ExprId, y: ExprId, r: ExprId) -> ExprId {
    let p = d.int();
    let xr = d.iadd(x, r);
    let yr = d.iadd(y, r);
    let neg_yr = d.ineg(yr);
    let start = d.iadd(xr, neg_yr);

    let neg_y = d.ineg(y);
    let neg_r = d.ineg(r);
    let n1 = d.iadd(neg_y, neg_r);
    let neg_add_proof = neg_add(d, y, r);
    let stepb_rhs = d.iadd(xr, n1);
    let stepb_proof = d.icongr(neg_yr, n1, neg_add_proof, &|d, t| d.iadd(xr, t));

    let inner_start = d.iadd(r, n1);
    let stepc_rhs = d.iadd(x, inner_start);
    let stepc_proof = d.const_app(p.add_assoc, &[x, r, n1]);

    // Reduce `add r (add (neg y) (neg r))` down to `neg y`.
    let n2 = d.iadd(neg_r, neg_y);
    let addcomm_ynr = d.const_app(p.add_comm, &[neg_y, neg_r]);
    let stepd_rhs = d.iadd(r, n2);
    let stepd_proof = d.icongr(n1, n2, addcomm_ynr, &|d, t| d.iadd(r, t));

    let r_negr = d.iadd(r, neg_r);
    let stepe_rhs = d.iadd(r_negr, neg_y);
    let assoc_e = d.const_app(p.add_assoc, &[r, neg_r, neg_y]);
    let stepe_proof = d.isymm(stepe_rhs, stepd_rhs, assoc_e);

    let zero = d.izero();
    let add_neg_r = d.const_app(p.add_neg, &[r]);
    let stepf_rhs = d.iadd(zero, neg_y);
    let stepf_proof = d.icongr(r_negr, zero, add_neg_r, &|d, t| d.iadd(t, neg_y));

    let stepg_rhs = d.iadd(neg_y, zero);
    let stepg_proof = d.const_app(p.add_comm, &[zero, neg_y]);

    let steph_proof = d.const_app(p.add_zero, &[neg_y]);

    let (_, inner_proof) = d.ichain(
        inner_start,
        &[
            (stepd_rhs, stepd_proof),
            (stepe_rhs, stepe_proof),
            (stepf_rhs, stepf_proof),
            (stepg_rhs, stepg_proof),
            (neg_y, steph_proof),
        ],
    );

    let stepi_proof = d.icongr(inner_start, neg_y, inner_proof, &|d, t| d.iadd(x, t));
    let final_rhs = d.iadd(x, neg_y);

    let (_, proof) = d.ichain(
        start,
        &[
            (stepb_rhs, stepb_proof),
            (stepc_rhs, stepc_proof),
            (final_rhs, stepi_proof),
        ],
    );
    proof
}

/// `Int.modEq_iff_dvd : ∀ n a b, 0 < n → (ModEq n a b ↔ n ∣ (b - a))`.
///
/// Scoped to `0 < n`, not `n ≠ 0`, for the same reason
/// [`super::dvd::declare_emod_eq_zero_iff_dvd`] is: the only proved bound on
/// `Int.emod`'s magnitude is [`super::division::declare_emod_lt_of_pos`]
/// (`n>0`); no proved analogue for a negative modulus exists yet.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
pub(super) fn declare_modeq_iff_dvd(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.mod_eq_iff_dvd, 3, &|d, v| {
        let (n, a, b) = (v[0], v[1], v[2]);
        let zero = d.izero();
        let pos_ty = d.ilt(zero, n);
        let modeq_ty = imodeq(d, n, a, b);
        let sub_ba = d.isub(b, a);
        let dvd_ty = super::dvd::idvd(d, n, sub_ba);
        let iff_ty = {
            let name = d.int().logic.iff;
            d.const_app(name, &[modeq_ty, dvd_ty])
        };
        let stmt = d.arrow(pos_ty, iff_ty);

        let h_pos_fv = d.fresh_fvar();
        let h_pos = d.kernel().fvar(h_pos_fv);
        let int_ty = d.int_ty();
        let one_level = d.level_one();

        let n_ne_zero = super::dvd::ne_zero_of_pos(d, n, h_pos);
        let qa = d.iediv(a, n);
        let ra = d.iemod(a, n);
        let qb = d.iediv(b, n);
        let rb = d.iemod(b, n);
        let mul_n_qa = d.imul(n, qa);
        let sum_a = d.iadd(mul_n_qa, ra);
        let ediv_add_emod_a = d.const_app(p.ediv_add_emod, &[a, n]);
        let a_eq = d.isymm(sum_a, a, ediv_add_emod_a);
        let mul_n_qb = d.imul(n, qb);
        let sum_b = d.iadd(mul_n_qb, rb);
        let ediv_add_emod_b = d.const_app(p.ediv_add_emod, &[b, n]);
        let b_eq = d.isymm(sum_b, b, ediv_add_emod_b);

        // mp : ModEq n a b -> dvd n (b - a). Witness `c := qb - qa`.
        let mp = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);

            let rb_eq_ra = d.isymm(ra, rb, h);
            let sum_b_ra = d.iadd(mul_n_qb, ra);
            let replace_rb = d.icongr(rb, ra, rb_eq_ra, &|d, t| d.iadd(mul_n_qb, t));
            let b_eq2 = d.itrans(b, sum_b, sum_b_ra, b_eq, replace_rb);

            let c = d.isub(qb, qa);
            let mul_n_c = d.imul(n, c);

            // add (mul n c) a = b, via: expand a, reassociate, fold left_distrib,
            // then `cancel_neg_add` collapses `(qb - qa) + qa` back to `qb`.
            let start = d.iadd(mul_n_c, a);
            let step1_rhs = d.iadd(mul_n_c, sum_a);
            let step1_proof = d.icongr(a, sum_a, a_eq, &|d, t| d.iadd(mul_n_c, t));

            let add_mncmnqa = d.iadd(mul_n_c, mul_n_qa);
            let step2_rhs = d.iadd(add_mncmnqa, ra);
            let assoc_proof = d.const_app(p.add_assoc, &[mul_n_c, mul_n_qa, ra]);
            let step2_proof = d.isymm(step2_rhs, step1_rhs, assoc_proof);

            let c_plus_qa = d.iadd(c, qa);
            let mul_n_cqa = d.imul(n, c_plus_qa);
            let step3_rhs = d.iadd(mul_n_cqa, ra);
            let distrib_proof = d.const_app(p.left_distrib, &[n, c, qa]);
            let distrib_rev = d.isymm(mul_n_cqa, add_mncmnqa, distrib_proof);
            let step3_proof = d.icongr(add_mncmnqa, mul_n_cqa, distrib_rev, &|d, t| d.iadd(t, ra));

            let cancel_qbqa = cancel_neg_add(d, qb, qa);
            let step4_rhs = d.iadd(mul_n_qb, ra);
            let step4_proof = d.icongr(c_plus_qa, qb, cancel_qbqa, &|d, t| {
                let m = d.imul(n, t);
                d.iadd(m, ra)
            });

            let (_, mid_proof) = d.ichain(
                start,
                &[
                    (step1_rhs, step1_proof),
                    (step2_rhs, step2_proof),
                    (step3_rhs, step3_proof),
                    (step4_rhs, step4_proof),
                ],
            );
            let b_eq2_rev = d.isymm(b, sum_b_ra, b_eq2);
            let goal_eq = d.itrans(start, sum_b_ra, b, mid_proof, b_eq2_rev);

            // add b (neg a) = mul n c, via `add_neg_cancel_right` on `goal_eq`.
            let neg_a = d.ineg(a);
            let lhs_final = d.iadd(b, neg_a);
            let goal_eq_rev = d.isymm(start, b, goal_eq);
            let mid2_rhs = d.iadd(start, neg_a);
            let mid2_proof = d.icongr(b, start, goal_eq_rev, &|d, t| d.iadd(t, neg_a));
            let final_proof = d.const_app(p.add_neg_cancel_right, &[mul_n_c, a]);
            let (_, diff_proof) =
                d.ichain(lhs_final, &[(mid2_rhs, mid2_proof), (mul_n_c, final_proof)]);

            let pred = super::dvd::dvd_predicate(d, n, sub_ba);
            let intro_name = d.int().logic.exists_intro;
            let intro = d.kernel().const_(intro_name, vec![one_level]);
            let proof_exists = d.apply(intro, &[int_ty, pred, c, diff_proof]);
            d.lam_fv(h_fv, modeq_ty, proof_exists)
        };

        // mpr : dvd n (b - a) -> ModEq n a b, via `Int.ediv_emod_unique`
        // against the two decompositions of `b`: the canonical one (`qb`,
        // `rb`) and the one the witness `c` builds (`c + qa`, `ra`).
        let mpr = {
            let hw_fv = d.fresh_fvar();
            let hw = d.kernel().fvar(hw_fv);
            let pred = super::dvd::dvd_predicate(d, n, sub_ba);
            let anon = d.anon_name();
            let exists_ty = {
                let name = d.int().logic.exists_;
                let exists = d.kernel().const_(name, vec![one_level]);
                d.apply(exists, &[int_ty, pred])
            };
            let motive = d
                .kernel()
                .lam(anon, exists_ty, modeq_ty, BinderInfo::Default);

            let minor = {
                let c_fv = d.fresh_fvar();
                let c = d.kernel().fvar(c_fv);
                let mul_n_c = d.imul(n, c);
                let heq_ty = d.ieq(sub_ba, mul_n_c);
                let heq_fv = d.fresh_fvar();
                let heq = d.kernel().fvar(heq_fv);

                // b = add (mul n c) a, via `cancel_neg_add` on `heq`.
                let neg_a = d.ineg(a);
                let add_b_nega = d.iadd(b, neg_a);
                let cancel = cancel_neg_add(d, b, a);
                let step_congr = d.icongr(add_b_nega, mul_n_c, heq, &|d, t| d.iadd(t, a));
                let add_b_nega_a = d.iadd(add_b_nega, a);
                let cancel_rev = d.isymm(add_b_nega_a, b, cancel);
                let mul_n_c_a = d.iadd(mul_n_c, a);
                let b_eq3 = d.itrans(b, add_b_nega_a, mul_n_c_a, cancel_rev, step_congr);

                let step2 = d.icongr(a, sum_a, a_eq, &|d, t| d.iadd(mul_n_c, t));
                let add_mnc_suma = d.iadd(mul_n_c, sum_a);
                let b_eq4 = d.itrans(b, mul_n_c_a, add_mnc_suma, b_eq3, step2);

                let mul_n_qa = d.imul(n, qa);
                let add_mncmnqa = d.iadd(mul_n_c, mul_n_qa);
                let reassoc_rhs = d.iadd(add_mncmnqa, ra);
                let assoc_proof = d.const_app(p.add_assoc, &[mul_n_c, mul_n_qa, ra]);
                let reassoc_rev = d.isymm(reassoc_rhs, add_mnc_suma, assoc_proof);
                let b_eq5 = d.itrans(b, add_mnc_suma, reassoc_rhs, b_eq4, reassoc_rev);

                let q_prime = d.iadd(c, qa);
                let mul_n_qprime = d.imul(n, q_prime);
                let distrib_proof = d.const_app(p.left_distrib, &[n, c, qa]);
                let distrib_rev = d.isymm(mul_n_qprime, add_mncmnqa, distrib_proof);
                let step_final = d.icongr(add_mncmnqa, mul_n_qprime, distrib_rev, &|d, t| {
                    d.iadd(t, ra)
                });
                let final_rhs = d.iadd(mul_n_qprime, ra);
                let eq1 = d.itrans(b, reassoc_rhs, final_rhs, b_eq5, step_final);

                let lower1 = d.const_app(p.emod_nonneg, &[a, n, n_ne_zero]);
                let upper1 = d.const_app(p.emod_lt_of_pos, &[a, n, h_pos]);
                let lower2 = d.const_app(p.emod_nonneg, &[b, n, n_ne_zero]);
                let upper2 = d.const_app(p.emod_lt_of_pos, &[b, n, h_pos]);
                let and_result = d.const_app(
                    p.ediv_emod_unique,
                    &[
                        b, n, q_prime, ra, qb, rb, h_pos, eq1, lower1, upper1, b_eq, lower2, upper2,
                    ],
                );
                let q_eq_ty = d.ieq(q_prime, qb);
                let r_eq_ty = d.ieq(ra, rb);
                let ra_eq_rb = d.and_right(q_eq_ty, r_eq_ty, and_result);

                let with_heq = d.lam_fv(heq_fv, heq_ty, ra_eq_rb);
                d.lam_fv(c_fv, int_ty, with_heq)
            };

            let exists_rec_name = d.int().logic.exists_rec;
            let exists_rec = d.kernel().const_(exists_rec_name, vec![one_level]);
            let body = d.apply(exists_rec, &[int_ty, pred, motive, minor, hw]);
            d.lam_fv(hw_fv, dvd_ty, body)
        };

        let intro_name = d.int().logic.iff_intro;
        let iff_proof = d.const_app(intro_name, &[modeq_ty, dvd_ty, mp, mpr]);
        let proof = d.lam_fv(h_pos_fv, pos_ty, iff_proof);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Int.ModEq.add_right :
/// ∀ n a b c, 0 < n → ModEq n a b → ModEq n (a+c) (b+c)`.
///
/// Via `modEq_iff_dvd`: `(a+c)` and `(b+c)` differ by exactly `b-a`
/// (`cancel_common_addend`), so the same divisibility witness serves both.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
pub(super) fn declare_modeq_add_right(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.mod_eq_add_right, 4, &|d, v| {
        let (n, a, b, c) = (v[0], v[1], v[2], v[3]);
        let zero = d.izero();
        let pos_ty = d.ilt(zero, n);
        let modeq_ab = imodeq(d, n, a, b);
        let ac = d.iadd(a, c);
        let bc = d.iadd(b, c);
        let modeq_acbc = imodeq(d, n, ac, bc);
        let inner_arrow = d.arrow(modeq_ab, modeq_acbc);
        let stmt = d.arrow(pos_ty, inner_arrow);

        let h_pos_fv = d.fresh_fvar();
        let h_pos = d.kernel().fvar(h_pos_fv);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let int_ty = d.int_ty();
        let one_level = d.level_one();

        let sub_ba = d.isub(b, a);
        let dvd_ba_ty = super::dvd::idvd(d, n, sub_ba);
        let iff_ab = d.const_app(p.mod_eq_iff_dvd, &[n, a, b, h_pos]);
        let mp_ab = d.const_app(p.logic.iff_mp, &[modeq_ab, dvd_ba_ty, iff_ab]);
        let dvd_h = d.apply(mp_ab, &[h]);

        // (b+c) - (a+c) = b - a, so the same witness carries over.
        let cc = cancel_common_addend(d, b, a, c);
        let neg_ac = d.ineg(ac);
        let sub_bcac = d.iadd(bc, neg_ac);

        let pred_old = super::dvd::dvd_predicate(d, n, sub_ba);
        let pred_new = super::dvd::dvd_predicate(d, n, sub_bcac);
        let anon = d.anon_name();
        let exists_ty_old = {
            let name = d.int().logic.exists_;
            let exists = d.kernel().const_(name, vec![one_level]);
            d.apply(exists, &[int_ty, pred_old])
        };
        let dvd_bcac_ty = super::dvd::idvd(d, n, sub_bcac);
        let motive = d
            .kernel()
            .lam(anon, exists_ty_old, dvd_bcac_ty, BinderInfo::Default);
        let minor = {
            let w_fv = d.fresh_fvar();
            let w = d.kernel().fvar(w_fv);
            let mul_n_w = d.imul(n, w);
            let heq_ty = d.ieq(sub_ba, mul_n_w);
            let heq_fv = d.fresh_fvar();
            let heq = d.kernel().fvar(heq_fv);

            let new_heq = d.itrans(sub_bcac, sub_ba, mul_n_w, cc, heq);
            let intro_name = d.int().logic.exists_intro;
            let intro = d.kernel().const_(intro_name, vec![one_level]);
            let proof_exists = d.apply(intro, &[int_ty, pred_new, w, new_heq]);
            let with_heq = d.lam_fv(heq_fv, heq_ty, proof_exists);
            d.lam_fv(w_fv, int_ty, with_heq)
        };
        let exists_rec_name = d.int().logic.exists_rec;
        let exists_rec = d.kernel().const_(exists_rec_name, vec![one_level]);
        let dvd_new = d.apply(exists_rec, &[int_ty, pred_old, motive, minor, dvd_h]);

        let iff_acbc = d.const_app(p.mod_eq_iff_dvd, &[n, ac, bc, h_pos]);
        let mpr_acbc = d.const_app(p.logic.iff_mpr, &[modeq_acbc, dvd_bcac_ty, iff_acbc]);
        let modeq_proof = d.apply(mpr_acbc, &[dvd_new]);

        let with_h = d.lam_fv(h_fv, modeq_ab, modeq_proof);
        let proof = d.lam_fv(h_pos_fv, pos_ty, with_h);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Int.ModEq.add_left :
/// ∀ n a b c, 0 < n → ModEq n a b → ModEq n (c+a) (c+b)`.
///
/// Derived from [`declare_modeq_add_right`] by commuting both sides — once
/// `modEq_iff_dvd` exists these are rewrites, not new divisibility reasoning.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
pub(super) fn declare_modeq_add_left(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.mod_eq_add_left, 4, &|d, v| {
        let (n, a, b, c) = (v[0], v[1], v[2], v[3]);
        let zero = d.izero();
        let pos_ty = d.ilt(zero, n);
        let modeq_ab = imodeq(d, n, a, b);
        let ca = d.iadd(c, a);
        let cb = d.iadd(c, b);
        let modeq_cacb = imodeq(d, n, ca, cb);
        let inner_arrow = d.arrow(modeq_ab, modeq_cacb);
        let stmt = d.arrow(pos_ty, inner_arrow);

        let h_pos_fv = d.fresh_fvar();
        let h_pos = d.kernel().fvar(h_pos_fv);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);

        let add_right = d.const_app(p.mod_eq_add_right, &[n, a, b, c, h_pos]);
        let h_right = d.apply(add_right, &[h]);

        let ac = d.iadd(a, c);
        let bc = d.iadd(b, c);

        let eq1 = d.const_app(p.add_comm, &[a, c]);
        let step1 = d.int_eq_rewrite(ac, ca, eq1, h_right, &|d, x| imodeq(d, n, x, bc));
        let eq2 = d.const_app(p.add_comm, &[b, c]);
        let step2 = d.int_eq_rewrite(bc, cb, eq2, step1, &|d, x| imodeq(d, n, ca, x));

        let with_h = d.lam_fv(h_fv, modeq_ab, step2);
        let proof = d.lam_fv(h_pos_fv, pos_ty, with_h);
        (stmt, proof)
    })?;
    Ok(())
}

// ---------------------------------------------------------------------------
// The multiplicative congruences: `ModEq` is a ring congruence, not merely an
// equivalence relation.
// ---------------------------------------------------------------------------

/// `Int.ModEq.mul_left :
/// ∀ n a b c, 0 < n → ModEq n a b → ModEq n (c*a) (c*b)`.
///
/// The primitive multiplicative congruence, straight from `modEq_iff_dvd`:
/// `h` gives `n ∣ (b-a)`, `dvd_trans` against `dvd_mul_left` scales that to
/// `n ∣ c*(b-a)`, and `mul_sub` rewrites `c*(b-a)` into `c*b - c*a` — exactly
/// the divisibility `modEq_iff_dvd` needs for `ModEq n (c*a) (c*b)`.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
pub(super) fn declare_modeq_mul_left(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.mod_eq_mul_left, 4, &|d, v| {
        let (n, a, b, c) = (v[0], v[1], v[2], v[3]);
        let zero = d.izero();
        let pos_ty = d.ilt(zero, n);
        let modeq_ab = imodeq(d, n, a, b);
        let ca = d.imul(c, a);
        let cb = d.imul(c, b);
        let modeq_cacb = imodeq(d, n, ca, cb);
        let inner_arrow = d.arrow(modeq_ab, modeq_cacb);
        let stmt = d.arrow(pos_ty, inner_arrow);

        let h_pos_fv = d.fresh_fvar();
        let h_pos = d.kernel().fvar(h_pos_fv);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);

        let sub_ba = d.isub(b, a);
        let dvd_ba_ty = super::dvd::idvd(d, n, sub_ba);
        let iff_ab = d.const_app(p.mod_eq_iff_dvd, &[n, a, b, h_pos]);
        let mp_ab = d.const_app(p.logic.iff_mp, &[modeq_ab, dvd_ba_ty, iff_ab]);
        let dvd_h = d.apply(mp_ab, &[h]);

        let cdiff = d.imul(c, sub_ba);
        let step1 = {
            let mul_left_step = d.const_app(p.dvd_mul_left, &[sub_ba, c]);
            d.const_app(p.dvd_trans, &[n, sub_ba, cdiff, dvd_h, mul_left_step])
        };

        let eq_ms = d.const_app(p.mul_sub, &[c, b, a]);
        let diff_cb_ca = d.isub(cb, ca);
        let motive = |d: &mut IntDev<'_>, x: ExprId| super::dvd::idvd(d, n, x);
        let dvd_new = d.int_eq_rewrite(cdiff, diff_cb_ca, eq_ms, step1, &motive);

        let dvd_cacb_ty = super::dvd::idvd(d, n, diff_cb_ca);
        let iff_cacb = d.const_app(p.mod_eq_iff_dvd, &[n, ca, cb, h_pos]);
        let mpr_cacb = d.const_app(p.logic.iff_mpr, &[modeq_cacb, dvd_cacb_ty, iff_cacb]);
        let modeq_proof = d.apply(mpr_cacb, &[dvd_new]);

        let with_h = d.lam_fv(h_fv, modeq_ab, modeq_proof);
        let proof = d.lam_fv(h_pos_fv, pos_ty, with_h);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Int.ModEq.mul_right :
/// ∀ n a b c, 0 < n → ModEq n a b → ModEq n (a*c) (b*c)`.
///
/// Derived from [`declare_modeq_mul_left`] by commuting both products — once
/// the primitive congruence exists this is a rewrite, not new divisibility
/// reasoning (mirrors how [`declare_modeq_add_left`] derives from
/// [`declare_modeq_add_right`]).
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
pub(super) fn declare_modeq_mul_right(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.mod_eq_mul_right, 4, &|d, v| {
        let (n, a, b, c) = (v[0], v[1], v[2], v[3]);
        let zero = d.izero();
        let pos_ty = d.ilt(zero, n);
        let modeq_ab = imodeq(d, n, a, b);
        let ac = d.imul(a, c);
        let bc = d.imul(b, c);
        let modeq_acbc = imodeq(d, n, ac, bc);
        let inner_arrow = d.arrow(modeq_ab, modeq_acbc);
        let stmt = d.arrow(pos_ty, inner_arrow);

        let h_pos_fv = d.fresh_fvar();
        let h_pos = d.kernel().fvar(h_pos_fv);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);

        let mul_left = d.const_app(p.mod_eq_mul_left, &[n, a, b, c, h_pos]);
        let h_left = d.apply(mul_left, &[h]);

        let ca = d.imul(c, a);
        let cb = d.imul(c, b);

        let eq1 = d.const_app(p.mul_comm, &[c, a]);
        let step1 = d.int_eq_rewrite(ca, ac, eq1, h_left, &|d, x| imodeq(d, n, x, cb));
        let eq2 = d.const_app(p.mul_comm, &[c, b]);
        let step2 = d.int_eq_rewrite(cb, bc, eq2, step1, &|d, x| imodeq(d, n, ac, x));

        let with_h = d.lam_fv(h_fv, modeq_ab, step2);
        let proof = d.lam_fv(h_pos_fv, pos_ty, with_h);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Int.ModEq.mul :
/// ∀ n a b c e, 0 < n → ModEq n a b → ModEq n c e → ModEq n (a*c) (b*e)`.
///
/// The two-sided congruence: scale the first hypothesis on the right by `c`
/// ([`declare_modeq_mul_right`]), scale the second on the left by `b`
/// ([`declare_modeq_mul_left`]), and chain through `ModEq.trans`.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
pub(super) fn declare_modeq_mul(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.mod_eq_mul, 5, &|d, v| {
        let (n, a, b, c, e) = (v[0], v[1], v[2], v[3], v[4]);
        let zero = d.izero();
        let pos_ty = d.ilt(zero, n);
        let modeq_ab = imodeq(d, n, a, b);
        let modeq_ce = imodeq(d, n, c, e);
        let ac = d.imul(a, c);
        let bc = d.imul(b, c);
        let be = d.imul(b, e);
        let modeq_target = imodeq(d, n, ac, be);
        let second_to_target = d.arrow(modeq_ce, modeq_target);
        let ab_arrow = d.arrow(modeq_ab, second_to_target);
        let stmt = d.arrow(pos_ty, ab_arrow);

        let h_pos_fv = d.fresh_fvar();
        let h_pos = d.kernel().fvar(h_pos_fv);
        let h1_fv = d.fresh_fvar();
        let h1 = d.kernel().fvar(h1_fv);
        let h2_fv = d.fresh_fvar();
        let h2 = d.kernel().fvar(h2_fv);

        let mul_right = d.const_app(p.mod_eq_mul_right, &[n, a, b, c, h_pos]);
        let first_scaled = d.apply(mul_right, &[h1]);

        let mul_left = d.const_app(p.mod_eq_mul_left, &[n, c, e, b, h_pos]);
        let second_scaled = d.apply(mul_left, &[h2]);

        let body = d.const_app(
            p.mod_eq_trans,
            &[n, ac, bc, be, first_scaled, second_scaled],
        );

        let with_h2 = d.lam_fv(h2_fv, modeq_ce, body);
        let with_h1 = d.lam_fv(h1_fv, modeq_ab, with_h2);
        let proof = d.lam_fv(h_pos_fv, pos_ty, with_h1);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Int.ModEq.pow :
/// ∀ n a b k, 0 < n → ModEq n a b → ModEq n (pow a k) (pow b k)`.
///
/// Induction on `k`: at `zero` both sides are `Int.one` regardless of `a`/`b`
/// (`ModEq.refl`); at `succ j`, `pow _ (succ j)` computes to `mul (pow _ j) _`,
/// so `ModEq.mul` applied to the IH (`ModEq n (a^j) (b^j)`) and the outer
/// hypothesis (`ModEq n a b`) gives exactly `ModEq n (a^j * a) (b^j * b)` —
/// no explicit `pow_succ` rewrite needed, since that equation is definitional
/// and the kernel's defeq check sees through it. `k` is a `Nat` (the
/// exponent), so — like [`super::defs::declare_pow_equations`]'s `pow_succ` —
/// this quantifies over a mix of `Int` and `Nat` and is declared by hand
/// rather than through [`IntDev::int_theorem`].
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
pub(super) fn declare_modeq_pow(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    let int_ty = d.int_ty();
    let nat = d.nat_ty();

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);

    let zero = d.izero();
    let pos_ty = d.ilt(zero, n);
    let modeq_ab = imodeq(d, n, a, b);

    let motive = |d: &mut IntDev<'_>, x: ExprId| {
        let pa = d.ipow(a, x);
        let pb = d.ipow(b, x);
        imodeq(d, n, pa, pb)
    };
    let conclusion_for_k = motive(d, k);

    let h_pos_fv = d.fresh_fvar();
    let h_pos = d.kernel().fvar(h_pos_fv);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let proof_body = d.induct(
        &motive,
        &|d| {
            let one = d.ione();
            d.const_app(p.mod_eq_refl, &[n, one])
        },
        &|d, j, ih| {
            let pa_j = d.ipow(a, j);
            let pb_j = d.ipow(b, j);
            d.const_app(p.mod_eq_mul, &[n, pa_j, pb_j, a, b, h_pos, ih, h])
        },
        k,
    );

    let with_h = d.lam_fv(h_fv, modeq_ab, proof_body);
    let with_h_pos = d.lam_fv(h_pos_fv, pos_ty, with_h);

    let value = {
        let with_k = d.lam_fv(k_fv, nat, with_h_pos);
        let with_b = d.lam_fv(b_fv, int_ty, with_k);
        let with_a = d.lam_fv(a_fv, int_ty, with_b);
        d.lam_fv(n_fv, int_ty, with_a)
    };
    let ty = {
        let inner_arrow = d.arrow(modeq_ab, conclusion_for_k);
        let with_pos = d.arrow(pos_ty, inner_arrow);
        let with_k = d.pi_fv(k_fv, nat, with_pos);
        let with_b = d.pi_fv(b_fv, int_ty, with_k);
        let with_a = d.pi_fv(a_fv, int_ty, with_b);
        d.pi_fv(n_fv, int_ty, with_a)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.mod_eq_pow,
        uparams: vec![],
        ty,
        value,
    })?;
    Ok(())
}

/// `Int.ModEq.cancel :
/// ∀ n c a b, 0 < n → Coprime c n → ModEq n (c*a) (c*b) → ModEq n a b`.
///
/// Cancellation, which is what a modular inverse buys: `modEq_iff_dvd` reads
/// `n ∣ c*(b-a)` off the hypothesis (via `mul_sub`), `Coprime c n` gives
/// `Coprime n c` (`gcd_comm`), and `gauss_lemma` turns `n ∣ c*(b-a)` with
/// `Coprime n c` into `n ∣ (b-a)` — exactly what `modEq_iff_dvd` needs for
/// `ModEq n a b`.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
pub(super) fn declare_modeq_cancel(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.mod_eq_cancel, 4, &|d, v| {
        let (n, c, a, b) = (v[0], v[1], v[2], v[3]);
        let zero = d.izero();
        let pos_ty = d.ilt(zero, n);
        let coprime_ty = d.const_app(p.coprime, &[c, n]);
        let ca = d.imul(c, a);
        let cb = d.imul(c, b);
        let modeq_cacb = imodeq(d, n, ca, cb);
        let modeq_ab = imodeq(d, n, a, b);

        let inner_arrow = d.arrow(modeq_cacb, modeq_ab);
        let cop_arrow = d.arrow(coprime_ty, inner_arrow);
        let stmt = d.arrow(pos_ty, cop_arrow);

        let h_pos_fv = d.fresh_fvar();
        let h_pos = d.kernel().fvar(h_pos_fv);
        let h_cop_fv = d.fresh_fvar();
        let h_cop = d.kernel().fvar(h_cop_fv);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);

        // n ∣ (c*b - c*a), from `h : ModEq n (c*a) (c*b)`.
        let diff_cb_ca = d.isub(cb, ca);
        let dvd_diff_ty = super::dvd::idvd(d, n, diff_cb_ca);
        let iff_cacb = d.const_app(p.mod_eq_iff_dvd, &[n, ca, cb, h_pos]);
        let mp_cacb = d.const_app(p.logic.iff_mp, &[modeq_cacb, dvd_diff_ty, iff_cacb]);
        let dvd_diff = d.apply(mp_cacb, &[h]);

        // c*(b-a) = c*b - c*a, so n ∣ c*(b-a).
        let sub_ba = d.isub(b, a);
        let cdiff = d.imul(c, sub_ba);
        let eq_ms = d.const_app(p.mul_sub, &[c, b, a]);
        let eq_ms_rev = d.isymm(cdiff, diff_cb_ca, eq_ms);
        let motive = |d: &mut IntDev<'_>, x: ExprId| super::dvd::idvd(d, n, x);
        let dvd_cdiff = d.int_eq_rewrite(diff_cb_ca, cdiff, eq_ms_rev, dvd_diff, &motive);

        // Coprime n c, from `h_cop : Coprime c n` via `gcd_comm`.
        let gc = d.const_app(p.gcd, &[c, n]);
        let gc2 = d.const_app(p.gcd, &[n, c]);
        let one_nat = d.num(1);
        let gcd_comm_cn = d.const_app(p.gcd_comm, &[c, n]);
        let gc2_eq_gc = d.symm(gc, gc2, gcd_comm_cn);
        let coprime_nc = d.trans(gc2, gc, one_nat, gc2_eq_gc, h_cop);

        let dvd_ba = d.const_app(p.gauss_lemma, &[n, c, sub_ba, coprime_nc, dvd_cdiff]);

        let modeq_proof = {
            let dvd_ba_ty = super::dvd::idvd(d, n, sub_ba);
            let iff_ab = d.const_app(p.mod_eq_iff_dvd, &[n, a, b, h_pos]);
            let mpr_ab = d.const_app(p.logic.iff_mpr, &[modeq_ab, dvd_ba_ty, iff_ab]);
            d.apply(mpr_ab, &[dvd_ba])
        };

        let with_h = d.lam_fv(h_fv, modeq_cacb, modeq_proof);
        let with_cop = d.lam_fv(h_cop_fv, coprime_ty, with_h);
        let proof = d.lam_fv(h_pos_fv, pos_ty, with_cop);
        (stmt, proof)
    })?;
    Ok(())
}
