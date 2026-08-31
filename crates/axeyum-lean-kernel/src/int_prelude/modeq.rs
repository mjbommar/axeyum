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
/// `add`, via `neg t = mul (neg one) t` and `Int.left_distrib`.
///
/// Was private, with [`declare_modeq_add_right`] its only caller (through
/// [`cancel_common_addend`]). Widened to `pub(super)` for
/// [`super::sum`], whose `sumRange_neg` step is exactly this equation read
/// backwards, and which also declares it as the public theorem `Int.neg_add` —
/// the prelude had the proof and had never stated it.
pub(super) fn neg_add(d: &mut IntDev<'_>, a: ExprId, b: ExprId) -> ExprId {
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

/// `ModEq n a b → Int.dvd n (Int.sub b a)`, UNCONDITIONAL in `n`.
///
/// This is exactly the `mp` half of [`declare_modeq_iff_dvd`]'s derivation,
/// pulled out as its own function once a re-read of that proof showed
/// `h_pos` (and the `n ≠ 0` fact built from it) is used ONLY inside the
/// `mpr` half — this half never touches either, so it holds for every `n`,
/// including `0` and every negative modulus, not just `0 < n`. Every fact in
/// this module that drops `modEq_iff_dvd`'s positivity hypothesis routes
/// through here (and [`dvd_to_modeq`], the converse) instead of
/// re-deriving the bound-free half of the bridge.
///
/// # Panics
///
/// Never — this builds a term, it does not check one; a malformed result is
/// caught by the trusted gate wherever the caller ultimately calls
/// `add_declaration`.
pub(super) fn modeq_to_dvd(
    d: &mut IntDev<'_>,
    n: ExprId,
    a: ExprId,
    b: ExprId,
    h: ExprId,
) -> ExprId {
    let p = d.int();
    let int_ty = d.int_ty();
    let one_level = d.level_one();

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

    // h : Eq(ra, rb) — `ModEq n a b` unfolds to exactly this.
    let rb_eq_ra = d.isymm(ra, rb, h);
    let sum_b_ra = d.iadd(mul_n_qb, ra);
    let replace_rb = d.icongr(rb, ra, rb_eq_ra, &|d, t| d.iadd(mul_n_qb, t));
    let b_eq2 = d.itrans(b, sum_b, sum_b_ra, b_eq, replace_rb);

    let c = d.isub(qb, qa);
    let mul_n_c = d.imul(n, c);

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

    let neg_a = d.ineg(a);
    let lhs_final = d.iadd(b, neg_a);
    let goal_eq_rev = d.isymm(start, b, goal_eq);
    let mid2_rhs = d.iadd(start, neg_a);
    let mid2_proof = d.icongr(b, start, goal_eq_rev, &|d, t| d.iadd(t, neg_a));
    let final_proof = d.const_app(p.add_neg_cancel_right, &[mul_n_c, a]);
    let (_, diff_proof) = d.ichain(lhs_final, &[(mid2_rhs, mid2_proof), (mul_n_c, final_proof)]);

    let sub_ba = d.isub(b, a);
    let pred = super::dvd::dvd_predicate(d, n, sub_ba);
    let intro_name = d.int().logic.exists_intro;
    let intro = d.kernel().const_(intro_name, vec![one_level]);
    d.apply(intro, &[int_ty, pred, c, diff_proof])
}

/// `Int.dvd n (Int.sub b a) → ModEq n a b`, UNCONDITIONAL in `n` — the
/// converse of [`modeq_to_dvd`], but via
/// [`super::modeq_family::declare_modeq_add_mul_left`]'s
/// `modEq_add_mul_left : ∀ n a q, ModEq n (n*q+a) a` (itself unconditional)
/// rather than [`super::division::declare_ediv_emod_unique`], which needs
/// `0<=r<n` and so only applies for `0 < n` (`declare_modeq_iff_dvd`'s
/// `mpr`). A witness `c` with `b-a=n*c` gives `b = n*c+a` directly by
/// [`cancel_neg_add`], and `modEq_add_mul_left` says exactly that
/// `n*c+a ≡ a`, no bound needed.
///
/// # Panics
///
/// Never — see [`modeq_to_dvd`].
pub(super) fn dvd_to_modeq(
    d: &mut IntDev<'_>,
    n: ExprId,
    a: ExprId,
    b: ExprId,
    h: ExprId,
) -> ExprId {
    let p = d.int();
    let int_ty = d.int_ty();
    let one_level = d.level_one();
    let anon = d.anon_name();

    let sub_ba = d.isub(b, a);
    let pred = super::dvd::dvd_predicate(d, n, sub_ba);
    let dvd_ty = super::dvd::idvd(d, n, sub_ba);
    let modeq_ty = imodeq(d, n, a, b);
    let motive = d.kernel().lam(anon, dvd_ty, modeq_ty, BinderInfo::Default);

    let minor = {
        let c_fv = d.fresh_fvar();
        let c = d.kernel().fvar(c_fv);
        let nc = d.imul(n, c);
        let heq_ty = d.ieq(sub_ba, nc);
        let heq_fv = d.fresh_fvar();
        let heq = d.kernel().fvar(heq_fv);

        // b = (b+(-a))+a, which is `sub_ba + a` up to `Int.sub`'s own
        // unfolding (the `state folded, prove unfolded` idiom `sub.rs`
        // documents and `modeq_to_dvd`/the original `modEq_iff_dvd` already
        // rely on).
        let neg_a = d.ineg(a);
        let b_nega = d.iadd(b, neg_a);
        let b_nega_a = d.iadd(b_nega, a);
        let cna = cancel_neg_add(d, b, a); // Eq(b_nega_a, b)
        let cna_rev = d.isymm(b_nega_a, b, cna); // Eq(b, b_nega_a) ~defeq~ Eq(b, sub_ba+a)

        let sub_ba_a = d.iadd(sub_ba, a);
        let nc_a = d.iadd(nc, a);
        let step2 = d.icongr(sub_ba, nc, heq, &|d, t| d.iadd(t, a)); // Eq(sub_ba+a, nc+a)

        let b_eq_nc_a = d.itrans(b, sub_ba_a, nc_a, cna_rev, step2); // Eq(b, nc+a)

        // `modEq_add_mul_left n a c : ModEq n (n*c+a) a`, unconditional.
        let core = d.const_app(p.mod_eq_add_mul_left, &[n, a, c]);
        let b_eq_nc_a_rev = d.isymm(b, nc_a, b_eq_nc_a); // Eq(nc+a, b)
        let motive2 = |d: &mut IntDev<'_>, t: ExprId| imodeq(d, n, t, a);
        let modeq_b_a = d.int_eq_rewrite(nc_a, b, b_eq_nc_a_rev, core, &motive2); // ModEq n b a
        let modeq_a_b = d.const_app(p.mod_eq_symm, &[n, b, a, modeq_b_a]); // ModEq n a b

        let with_heq = d.lam_fv(heq_fv, heq_ty, modeq_a_b);
        d.lam_fv(c_fv, int_ty, with_heq)
    };
    let exists_rec_name = d.int().logic.exists_rec;
    let exists_rec = d.kernel().const_(exists_rec_name, vec![one_level]);
    d.apply(exists_rec, &[int_ty, pred, motive, minor, h])
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

/// `Int.ModEq.add_right : ∀ n a b c, ModEq n a b → ModEq n (a+c) (b+c)`,
/// UNCONDITIONAL in `n` (Mathlib's `Int.ModEq.add_right` carries no
/// positivity hypothesis; see [`modeq_to_dvd`]'s doc for why the old
/// `0 < n`-scoped proof this replaced was never load-bearing here).
///
/// Via [`modeq_to_dvd`]/[`dvd_to_modeq`]: `(a+c)` and `(b+c)` differ by
/// exactly `b-a` (`cancel_common_addend`), so the same divisibility witness
/// serves both, exactly as the old proof did — only the bridge to/from `dvd`
/// changed, not this shape.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
pub(super) fn declare_modeq_add_right(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.mod_eq_add_right, 4, &|d, v| {
        let (n, a, b, c) = (v[0], v[1], v[2], v[3]);
        let modeq_ab = imodeq(d, n, a, b);
        let ac = d.iadd(a, c);
        let bc = d.iadd(b, c);
        let modeq_acbc = imodeq(d, n, ac, bc);
        let stmt = d.arrow(modeq_ab, modeq_acbc);

        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let int_ty = d.int_ty();
        let one_level = d.level_one();

        let dvd_h = modeq_to_dvd(d, n, a, b, h);

        // (b+c) - (a+c) = b - a, so the same witness carries over.
        let cc = cancel_common_addend(d, b, a, c);
        let neg_ac = d.ineg(ac);
        let sub_bcac = d.iadd(bc, neg_ac);
        let sub_ba = d.isub(b, a);

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

        let modeq_proof = dvd_to_modeq(d, n, ac, bc, dvd_new);

        let proof = d.lam_fv(h_fv, modeq_ab, modeq_proof);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Int.ModEq.add_left : ∀ n a b c, ModEq n a b → ModEq n (c+a) (c+b)`,
/// UNCONDITIONAL in `n` — see [`declare_modeq_add_right`].
///
/// Derived from [`declare_modeq_add_right`] by commuting both sides — once
/// the general bridge exists these are rewrites, not new divisibility
/// reasoning.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
pub(super) fn declare_modeq_add_left(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.mod_eq_add_left, 4, &|d, v| {
        let (n, a, b, c) = (v[0], v[1], v[2], v[3]);
        let modeq_ab = imodeq(d, n, a, b);
        let ca = d.iadd(c, a);
        let cb = d.iadd(c, b);
        let modeq_cacb = imodeq(d, n, ca, cb);
        let stmt = d.arrow(modeq_ab, modeq_cacb);

        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);

        let add_right = d.const_app(p.mod_eq_add_right, &[n, a, b, c]);
        let h_right = d.apply(add_right, &[h]);

        let ac = d.iadd(a, c);
        let bc = d.iadd(b, c);

        let eq1 = d.const_app(p.add_comm, &[a, c]);
        let step1 = d.int_eq_rewrite(ac, ca, eq1, h_right, &|d, x| imodeq(d, n, x, bc));
        let eq2 = d.const_app(p.add_comm, &[b, c]);
        let step2 = d.int_eq_rewrite(bc, cb, eq2, step1, &|d, x| imodeq(d, n, ca, x));

        let proof = d.lam_fv(h_fv, modeq_ab, step2);
        (stmt, proof)
    })?;
    Ok(())
}

// ---------------------------------------------------------------------------
// Small ring-algebra helpers the rest of this module's generalizations need
// (double negation, negation distributing over addition, "solve a sum for
// one addend") — each a short, self-contained derivation from `add_zero`,
// `add_neg`, `add_comm`, `add_assoc`, `neg_one_mul` and `left_distrib`, the
// same primitives [`cancel_neg_add`]/[`cancel_common_addend`] above already
// use.
// ---------------------------------------------------------------------------

/// From `h : Eq Int (add x y) izero`, derive `Eq Int x (neg y)`.
fn eq_neg_of_add_eq_zero(d: &mut IntDev<'_>, x: ExprId, y: ExprId, h: ExprId) -> ExprId {
    let p = d.int();
    let izero = d.izero();
    let neg_y = d.ineg(y);

    let x_izero = d.iadd(x, izero);
    let az = d.const_app(p.add_zero, &[x]); // Eq(x+izero, x)
    let step0 = d.isymm(x_izero, x, az); // Eq(x, x+izero)

    let y_negy = d.iadd(y, neg_y);
    let an = d.const_app(p.add_neg, &[y]); // Eq(y+neg_y, izero)
    let izero_eq_y_negy = d.isymm(y_negy, izero, an); // Eq(izero, y+neg_y)

    let x_y_negy = d.iadd(x, y_negy);
    let step1 = d.icongr(izero, y_negy, izero_eq_y_negy, &|d, t| d.iadd(x, t));

    let xy = d.iadd(x, y);
    let xy_negy = d.iadd(xy, neg_y);
    let assoc = d.const_app(p.add_assoc, &[x, y, neg_y]); // Eq(xy_negy, x_y_negy)
    let step2 = d.isymm(xy_negy, x_y_negy, assoc); // Eq(x_y_negy, xy_negy)

    let izero_negy = d.iadd(izero, neg_y);
    let step3 = d.icongr(xy, izero, h, &|d, t| d.iadd(t, neg_y)); // Eq(xy_negy, izero_negy)

    let negy_izero = d.iadd(neg_y, izero);
    let comm = d.const_app(p.add_comm, &[izero, neg_y]); // Eq(izero+neg_y, neg_y+izero)
    let az2 = d.const_app(p.add_zero, &[neg_y]); // Eq(neg_y+izero, neg_y)
    let step4 = d.itrans(izero_negy, negy_izero, neg_y, comm, az2);

    let (_, chained) = d.ichain(
        x,
        &[
            (x_izero, step0),
            (x_y_negy, step1),
            (xy_negy, step2),
            (izero_negy, step3),
            (neg_y, step4),
        ],
    );
    chained
}

/// `Eq Int (neg (neg a)) a` — double negation.
fn ineg_neg(d: &mut IntDev<'_>, a: ExprId) -> ExprId {
    let p = d.int();
    let neg_a = d.ineg(a);
    let nn_a = d.ineg(neg_a);
    let an = d.const_app(p.add_neg, &[a]); // Eq(a+neg_a, izero)
    let a_eq_nna = eq_neg_of_add_eq_zero(d, a, neg_a, an); // Eq(a, nn_a)
    d.isymm(a, nn_a, a_eq_nna) // Eq(nn_a, a)
}

/// `Eq Int (neg (add x y)) (add (neg x) (neg y))` — negation distributes over
/// addition, via `neg t = mul (neg one) t` and `Int.left_distrib`. A local
/// copy of `modeq_family.rs`'s private `neg_add`, kept in this file so the
/// generalizations below don't reach across modules for one small identity.
fn ineg_add(d: &mut IntDev<'_>, x: ExprId, y: ExprId) -> ExprId {
    let p = d.int();
    let xy = d.iadd(x, y);
    let start = d.ineg(xy);

    let one = d.ione();
    let neg_one = d.ineg(one);
    let mul_negone_xy = d.imul(neg_one, xy);
    let neg_one_mul_xy = d.const_app(p.neg_one_mul, &[xy]); // Eq(neg_one*xy, neg(xy))
    let step1_proof = d.isymm(mul_negone_xy, start, neg_one_mul_xy);

    let mul_nx = d.imul(neg_one, x);
    let mul_ny = d.imul(neg_one, y);
    let step2_rhs = d.iadd(mul_nx, mul_ny);
    let step2_proof = d.const_app(p.left_distrib, &[neg_one, x, y]);

    let neg_x = d.ineg(x);
    let step3_rhs = d.iadd(neg_x, mul_ny);
    let neg_one_mul_x = d.const_app(p.neg_one_mul, &[x]);
    let step3_proof = d.icongr(mul_nx, neg_x, neg_one_mul_x, &|d, t| d.iadd(t, mul_ny));

    let neg_y = d.ineg(y);
    let step4_rhs = d.iadd(neg_x, neg_y);
    let neg_one_mul_y = d.const_app(p.neg_one_mul, &[y]);
    let step4_proof = d.icongr(mul_ny, neg_y, neg_one_mul_y, &|d, t| d.iadd(neg_x, t));

    let (_, proof) = d.ichain(
        start,
        &[
            (mul_negone_xy, step1_proof),
            (step2_rhs, step2_proof),
            (step3_rhs, step3_proof),
            (step4_rhs, step4_proof),
        ],
    );
    proof
}

/// `Eq Int (add (neg c) (add c x)) x` — "cancel a left addend":
/// `-c+(c+x)=x`.
pub(super) fn cancel_neg_add_left(d: &mut IntDev<'_>, c: ExprId, x: ExprId) -> ExprId {
    let p = d.int();
    let neg_c = d.ineg(c);
    let cx = d.iadd(c, x);
    let start = d.iadd(neg_c, cx);

    let negc_c = d.iadd(neg_c, c);
    let mid = d.iadd(negc_c, x);
    let assoc = d.const_app(p.add_assoc, &[neg_c, c, x]); // Eq(mid, start)
    let step1 = d.isymm(mid, start, assoc); // Eq(start, mid)

    let c_negc = d.iadd(c, neg_c);
    let izero = d.izero();
    let an = d.const_app(p.add_neg, &[c]); // Eq(c+neg_c, izero)
    let comm = d.const_app(p.add_comm, &[neg_c, c]); // Eq(neg_c+c, c+neg_c)
    let negc_c_eq_zero = d.itrans(negc_c, c_negc, izero, comm, an);

    let zero_x = d.iadd(izero, x);
    let step2 = d.icongr(negc_c, izero, negc_c_eq_zero, &|d, t| d.iadd(t, x));

    let x_zero = d.iadd(x, izero);
    let comm2 = d.const_app(p.add_comm, &[izero, x]);
    let az = d.const_app(p.add_zero, &[x]);
    let zero_x_eq_x = d.itrans(zero_x, x_zero, x, comm2, az);

    let (_, chained) = d.ichain(start, &[(mid, step1), (zero_x, step2), (x, zero_x_eq_x)]);
    chained
}

/// `Int.ModEq.add_left_cancel' :
/// ∀ n a b c, ModEq n (c+a) (c+b) → ModEq n a b`.
///
/// Shift both sides by `-c` using the now-general [`declare_modeq_add_left`],
/// then simplify `-c+(c+x)` back to `x` on each side via
/// [`cancel_neg_add_left`].
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
pub(super) fn declare_modeq_add_left_cancel(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.mod_eq_add_left_cancel, 4, &|d, v| {
        let (n, a, b, c) = (v[0], v[1], v[2], v[3]);
        let ca = d.iadd(c, a);
        let cb = d.iadd(c, b);
        let modeq_cacb = imodeq(d, n, ca, cb);
        let modeq_ab = imodeq(d, n, a, b);
        let stmt = d.arrow(modeq_cacb, modeq_ab);

        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let neg_c = d.ineg(c);

        let shifted = d.const_app(p.mod_eq_add_left, &[n, ca, cb, neg_c]);
        let shifted_h = d.apply(shifted, &[h]);

        let negc_ca = d.iadd(neg_c, ca);
        let negc_cb = d.iadd(neg_c, cb);
        let simp_a = cancel_neg_add_left(d, c, a); // Eq(negc_ca, a)
        let simp_b = cancel_neg_add_left(d, c, b); // Eq(negc_cb, b)

        let step1 = d.int_eq_rewrite(negc_ca, a, simp_a, shifted_h, &|d, t| {
            imodeq(d, n, t, negc_cb)
        });
        let proof_body = d.int_eq_rewrite(negc_cb, b, simp_b, step1, &|d, t| imodeq(d, n, a, t));

        let proof = d.lam_fv(h_fv, modeq_cacb, proof_body);
        (stmt, proof)
    })?;
    Ok(())
}

/// Given `heq : Eq Int x (add (mul n q) r)`, derive
/// `Eq Int (neg x) (add (mul n (neg q)) (neg r))` — "negate a
/// `n*q+r` decomposition", via [`ineg_add`] and `Int.mul_neg`.
fn neg_shift(
    d: &mut IntDev<'_>,
    n: ExprId,
    q: ExprId,
    r: ExprId,
    x: ExprId,
    heq: ExprId,
) -> ExprId {
    let p = d.int();
    let nq = d.imul(n, q);
    let sum = d.iadd(nq, r);
    let neg_x = d.ineg(x);
    let neg_sum = d.ineg(sum);
    let step0 = d.icongr(x, sum, heq, &|d, t| d.ineg(t)); // Eq(neg_x, neg_sum)

    let dist = ineg_add(d, nq, r); // Eq(neg_sum, neg(nq)+neg(r))
    let neg_nq = d.ineg(nq);
    let neg_r = d.ineg(r);
    let neg_nq_negr = d.iadd(neg_nq, neg_r);

    let neg_q = d.ineg(q);
    let n_negq = d.imul(n, neg_q);
    let mul_neg_step = d.const_app(p.mul_neg, &[n, q]); // Eq(n*(-q), neg(n*q))
    let mul_neg_rev = d.isymm(n_negq, neg_nq, mul_neg_step); // Eq(neg_nq, n_negq)
    let final_rhs = d.iadd(n_negq, neg_r);
    let step2 = d.icongr(neg_nq, n_negq, mul_neg_rev, &|d, t| d.iadd(t, neg_r));

    let (_, chained) = d.ichain(
        neg_x,
        &[(neg_sum, step0), (neg_nq_negr, dist), (final_rhs, step2)],
    );
    chained
}

/// `Int.ModEq.neg : ∀ n a b, ModEq n a b → ModEq n (-a) (-b)`, UNCONDITIONAL
/// in `n`.
///
/// Decompose `a = n*qa+ra`, `b = n*qb+ra` (using `h : ra=rb` to align the
/// residues), so `-a = n*(-qa)+(-ra)` and `-b = n*(-qb)+(-ra)`
/// ([`ineg_add`] + `Int.mul_neg`); [`super::modeq_family::declare_modeq_add_mul_left`]'s
/// `modEq n (n*c+x) x` (unconditional) then gives `ModEq n (-a) (-ra)` and
/// `ModEq n (-b) (-ra)` directly, and `trans`+`symm` close the gap — no
/// `dvd` needed for this one.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
pub(super) fn declare_modeq_neg(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.mod_eq_neg, 3, &|d, v| {
        let (n, a, b) = (v[0], v[1], v[2]);
        let modeq_ab = imodeq(d, n, a, b);
        let neg_a = d.ineg(a);
        let neg_b = d.ineg(b);
        let modeq_negab = imodeq(d, n, neg_a, neg_b);
        let stmt = d.arrow(modeq_ab, modeq_negab);

        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv); // Eq(ra, rb)

        let qa = d.iediv(a, n);
        let ra = d.iemod(a, n);
        let qb = d.iediv(b, n);
        let rb = d.iemod(b, n);
        let mul_n_qa = d.imul(n, qa);
        let sum_a = d.iadd(mul_n_qa, ra);
        let ediv_add_emod_a = d.const_app(p.ediv_add_emod, &[a, n]);
        let a_eq = d.isymm(sum_a, a, ediv_add_emod_a); // Eq(a, n*qa+ra)
        let mul_n_qb = d.imul(n, qb);
        let sum_b = d.iadd(mul_n_qb, rb);
        let ediv_add_emod_b = d.const_app(p.ediv_add_emod, &[b, n]);
        let b_eq = d.isymm(sum_b, b, ediv_add_emod_b); // Eq(b, n*qb+rb)

        let rb_eq_ra = d.isymm(ra, rb, h); // Eq(rb, ra)
        let sum_b_ra = d.iadd(mul_n_qb, ra);
        let replace_rb = d.icongr(rb, ra, rb_eq_ra, &|d, t| d.iadd(mul_n_qb, t));
        let b_eq2 = d.itrans(b, sum_b, sum_b_ra, b_eq, replace_rb); // Eq(b, n*qb+ra)

        // -a = n*(-qa)+(-ra), and -b = n*(-qb)+(-ra) (using `b_eq2`, which
        // already carries `ra` in place of `rb`).
        let neg_ra = d.ineg(ra);
        let neg_qa = d.ineg(qa);
        let neg_qb = d.ineg(qb);
        let neg_a_eq = neg_shift(d, n, qa, ra, a, a_eq);
        let neg_b_eq = neg_shift(d, n, qb, ra, b, b_eq2);

        let mn_negqa = d.imul(n, neg_qa);
        let mn_negqa_negra = d.iadd(mn_negqa, neg_ra);
        let mn_negqb = d.imul(n, neg_qb);
        let mn_negqb_negra = d.iadd(mn_negqb, neg_ra);

        // `modEq_add_mul_left n (-ra) (-qa) : ModEq n (n*(-qa)+(-ra)) (-ra)`
        let core_a = d.const_app(p.mod_eq_add_mul_left, &[n, neg_ra, neg_qa]);
        let core_b = d.const_app(p.mod_eq_add_mul_left, &[n, neg_ra, neg_qb]);

        let neg_a_eq_rev = d.isymm(neg_a, mn_negqa_negra, neg_a_eq);
        let motive_a = |d: &mut IntDev<'_>, t: ExprId| imodeq(d, n, t, neg_ra);
        let modeq_nega_negra =
            d.int_eq_rewrite(mn_negqa_negra, neg_a, neg_a_eq_rev, core_a, &motive_a);

        let neg_b_eq_rev = d.isymm(neg_b, mn_negqb_negra, neg_b_eq);
        let motive_b = |d: &mut IntDev<'_>, t: ExprId| imodeq(d, n, t, neg_ra);
        let modeq_negb_negra =
            d.int_eq_rewrite(mn_negqb_negra, neg_b, neg_b_eq_rev, core_b, &motive_b);

        let modeq_negra_negb = d.const_app(p.mod_eq_symm, &[n, neg_b, neg_ra, modeq_negb_negra]);
        let proof_body = d.const_app(
            p.mod_eq_trans,
            &[n, neg_a, neg_ra, neg_b, modeq_nega_negra, modeq_negra_negb],
        );

        let proof = d.lam_fv(h_fv, modeq_ab, proof_body);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Int.neg_modEq_neg : ∀ n a b, ModEq n (-a) (-b) ↔ ModEq n a b`,
/// UNCONDITIONAL in `n`.
///
/// `mpr` is exactly [`declare_modeq_neg`]; `mp` applies it again to a
/// `ModEq n (-a) (-b)` hypothesis and simplifies the resulting
/// `-(-a)`/`-(-b)` back down via [`ineg_neg`].
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
pub(super) fn declare_neg_modeq_neg(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.neg_mod_eq_neg, 3, &|d, v| {
        let (n, a, b) = (v[0], v[1], v[2]);
        let neg_a = d.ineg(a);
        let neg_b = d.ineg(b);
        let modeq_negab = imodeq(d, n, neg_a, neg_b);
        let modeq_ab = imodeq(d, n, a, b);

        let mp = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let stepped = d.const_app(p.mod_eq_neg, &[n, neg_a, neg_b]);
            let hn = d.apply(stepped, &[h]); // ModEq n (-(-a)) (-(-b))
            let nn_a = d.ineg(neg_a);
            let nn_b = d.ineg(neg_b);
            let ea = ineg_neg(d, a); // Eq(nn_a, a)
            let eb = ineg_neg(d, b); // Eq(nn_b, b)
            let motive1 = |d: &mut IntDev<'_>, t: ExprId| imodeq(d, n, t, nn_b);
            let step1 = d.int_eq_rewrite(nn_a, a, ea, hn, &motive1);
            let motive2 = |d: &mut IntDev<'_>, t: ExprId| imodeq(d, n, a, t);
            let body = d.int_eq_rewrite(nn_b, b, eb, step1, &motive2);
            d.lam_fv(h_fv, modeq_negab, body)
        };
        let mpr = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let stepped = d.const_app(p.mod_eq_neg, &[n, a, b]);
            let body = d.apply(stepped, &[h]);
            d.lam_fv(h_fv, modeq_ab, body)
        };

        let iff_ty = {
            let name = d.int().logic.iff;
            d.const_app(name, &[modeq_negab, modeq_ab])
        };
        let intro_name = d.int().logic.iff_intro;
        let iff_proof = d.const_app(intro_name, &[modeq_negab, modeq_ab, mp, mpr]);
        (iff_ty, iff_proof)
    })?;
    Ok(())
}

/// `Eq Int (add x (sub y x)) y` — "x + (y-x) = y", via [`cancel_neg_add`]
/// and `Int.add_comm`.
fn eq_add_sub(d: &mut IntDev<'_>, x: ExprId, y: ExprId) -> ExprId {
    let p = d.int();
    let cna = cancel_neg_add(d, y, x); // Eq((y+(-x))+x, y)
    let neg_x = d.ineg(x);
    let y_negx = d.iadd(y, neg_x);
    let start = d.iadd(y_negx, x); // (y+(-x))+x
    let x_y_negx = d.iadd(x, y_negx); // x+(y-x)
    let comm = d.const_app(p.add_comm, &[y_negx, x]); // Eq(start, x_y_negx)
    let comm_rev = d.isymm(start, x_y_negx, comm); // Eq(x_y_negx, start)
    d.itrans(x_y_negx, start, y, comm_rev, cna) // Eq(x_y_negx, y)
}

/// `Int.ModEq.of_dvd : ∀ m n a b, dvd m n → ModEq n a b → ModEq m a b`,
/// UNCONDITIONAL in both `m` and `n`.
///
/// `ModEq n a b → dvd n (b-a)` ([`modeq_to_dvd`]), `dvd m n` composes via
/// `Int.dvd_trans` to `dvd m (b-a)`, and [`dvd_to_modeq`] closes it back to
/// `ModEq m a b`.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
pub(super) fn declare_modeq_of_dvd(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.mod_eq_of_dvd, 4, &|d, v| {
        let (m, n, a, b) = (v[0], v[1], v[2], v[3]);
        let dvd_mn = super::dvd::idvd(d, m, n);
        let modeq_n_ab = imodeq(d, n, a, b);
        let modeq_m_ab = imodeq(d, m, a, b);
        let inner = d.arrow(modeq_n_ab, modeq_m_ab);
        let stmt = d.arrow(dvd_mn, inner);

        let hd_fv = d.fresh_fvar();
        let hd = d.kernel().fvar(hd_fv);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);

        let dvd_n_ba = modeq_to_dvd(d, n, a, b, h); // dvd n (sub b a)
        let sub_ba = d.isub(b, a);
        let dvd_m_ba = d.const_app(p.dvd_trans, &[m, n, sub_ba, hd, dvd_n_ba]);
        let modeq_proof = dvd_to_modeq(d, m, a, b, dvd_m_ba);

        let with_h = d.lam_fv(h_fv, modeq_n_ab, modeq_proof);
        let proof = d.lam_fv(hd_fv, dvd_mn, with_h);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Int.ModEq.dvd_iff : ∀ n a b, ModEq n a b → (dvd n a ↔ dvd n b)`,
/// UNCONDITIONAL in `n`.
///
/// [`modeq_to_dvd`] applied to `h` and to `symm h` gives `dvd n (b-a)` and
/// `dvd n (a-b)` directly (no separate "negate the dividend" lemma needed);
/// `Int.dvd_add` plus [`eq_add_sub`] (`b = a+(b-a)`, `a = b+(a-b)`) close
/// each direction.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
pub(super) fn declare_modeq_dvd_iff(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.mod_eq_dvd_iff, 3, &|d, v| {
        let (n, a, b) = (v[0], v[1], v[2]);
        let modeq_ab = imodeq(d, n, a, b);
        let dvd_na = super::dvd::idvd(d, n, a);
        let dvd_nb = super::dvd::idvd(d, n, b);
        let iff_ty = {
            let name = d.int().logic.iff;
            d.const_app(name, &[dvd_na, dvd_nb])
        };
        let stmt = d.arrow(modeq_ab, iff_ty);

        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);

        let dvd_ba = modeq_to_dvd(d, n, a, b, h); // dvd n (sub b a)
        let symm_h = d.const_app(p.mod_eq_symm, &[n, a, b, h]); // ModEq n b a
        let dvd_ab = modeq_to_dvd(d, n, b, a, symm_h); // dvd n (sub a b)

        let sub_ba = d.isub(b, a);
        let sub_ab = d.isub(a, b);

        let mp = {
            let ha_fv = d.fresh_fvar();
            let ha = d.kernel().fvar(ha_fv);
            let sum = d.const_app(p.dvd_add, &[n, a, sub_ba, ha, dvd_ba]); // dvd n (a+sub_ba)
            let a_plus_subba = d.iadd(a, sub_ba);
            let eq = eq_add_sub(d, a, b); // Eq(a+sub_ba, b)
            let motive = |d: &mut IntDev<'_>, t: ExprId| super::dvd::idvd(d, n, t);
            let body = d.int_eq_rewrite(a_plus_subba, b, eq, sum, &motive);
            d.lam_fv(ha_fv, dvd_na, body)
        };
        let mpr = {
            let hb_fv = d.fresh_fvar();
            let hb = d.kernel().fvar(hb_fv);
            let sum = d.const_app(p.dvd_add, &[n, b, sub_ab, hb, dvd_ab]); // dvd n (b+sub_ab)
            let b_plus_subab = d.iadd(b, sub_ab);
            let eq = eq_add_sub(d, b, a); // Eq(b+sub_ab, a)
            let motive = |d: &mut IntDev<'_>, t: ExprId| super::dvd::idvd(d, n, t);
            let body = d.int_eq_rewrite(b_plus_subab, a, eq, sum, &motive);
            d.lam_fv(hb_fv, dvd_nb, body)
        };

        let intro_name = d.int().logic.iff_intro;
        let iff_proof = d.const_app(intro_name, &[dvd_na, dvd_nb, mp, mpr]);
        let proof = d.lam_fv(h_fv, modeq_ab, iff_proof);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Int.ModEq.of_mul_left : ∀ n a b m, ModEq (m*n) a b → ModEq n a b`,
/// UNCONDITIONAL in `n` and `m`.
///
/// The special case of [`declare_modeq_of_dvd`] at divisibility witness
/// `Int.dvd_mul_left n m : dvd n (m*n)`.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
pub(super) fn declare_modeq_of_mul_left(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.mod_eq_of_mul_left, 4, &|d, v| {
        let (n, a, b, m) = (v[0], v[1], v[2], v[3]);
        let mn = d.imul(m, n);
        let modeq_mn = imodeq(d, mn, a, b);
        let modeq_n = imodeq(d, n, a, b);
        let stmt = d.arrow(modeq_mn, modeq_n);

        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);

        let dvd_n_mn = d.const_app(p.dvd_mul_left, &[n, m]); // dvd n (m*n)
        let of_dvd = d.const_app(p.mod_eq_of_dvd, &[n, mn, a, b, dvd_n_mn]);
        let body = d.apply(of_dvd, &[h]);

        let proof = d.lam_fv(h_fv, modeq_mn, body);
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

/// `Eq Int (sub y x) (sub du dv)`, from `h : Eq Int (add x du) (add y dv)` —
/// pure abelian-group rearrangement. Cancel `x` off the left (commute, then
/// `add_neg_cancel_right`), leaving `du = (y+dv)+(-x)`; add `-dv` to both
/// sides, reassociate the right side with a `swap_tail`
/// (`add_assoc`/`add_comm`/`add_assoc`) so `dv`'s cancellation lines up with
/// `add_neg_cancel_right` again, then flip.
///
/// [`declare_modeq_of_nat_modeq`] is the only caller: it needs `Y - X = D*U -
/// D*V` from the balanced Bezout-shaped witness equation `X + D*U = Y + D*V`
/// that `Nat.modEq`'s own existential unpacks to.
fn nat_witness_gap(
    d: &mut IntDev<'_>,
    x: ExprId,
    y: ExprId,
    du: ExprId,
    dv: ExprId,
    h: ExprId,
) -> ExprId {
    let p = d.int();
    let neg_x = d.ineg(x);
    let neg_dv = d.ineg(dv);

    // Step 1: reorder the left side, x+du = du+x.
    let x_du = d.iadd(x, du);
    let du_x = d.iadd(du, x);
    let comm1 = d.const_app(p.add_comm, &[x, du]);
    let y_dv = d.iadd(y, dv);
    let h_reordered = {
        let back = d.isymm(x_du, du_x, comm1);
        d.itrans(du_x, x_du, y_dv, back, h)
    };

    // Step 2: cancel x, giving du = (y+dv)+(-x).
    let cancel1 = d.const_app(p.add_neg_cancel_right, &[du, x]); // (du+x)+(-x) = du
    let du_x_negx = d.iadd(du_x, neg_x);
    let r1 = d.iadd(y_dv, neg_x);
    let h3 = {
        let back = d.isymm(du_x_negx, du, cancel1);
        let congr = d.icongr(du_x, y_dv, h_reordered, &|d, t| d.iadd(t, neg_x));
        d.itrans(du, du_x_negx, r1, back, congr)
    };

    // Step 3: add -dv to both sides, then reassociate the right side so its
    // `dv` cancellation matches `add_neg_cancel_right`'s shape.
    let du_negdv = d.iadd(du, neg_dv);
    let r1_negdv = d.iadd(r1, neg_dv);
    let h4 = d.icongr(du, r1, h3, &|d, t| d.iadd(t, neg_dv));

    // swap_tail : (p+b)+c = (p+c)+b, with p = y_dv, b = -x, c = -dv.
    let p_plus_negdv = d.iadd(y_dv, neg_dv);
    let target_swapped = d.iadd(p_plus_negdv, neg_x);
    let swap = {
        let bc = d.iadd(neg_x, neg_dv);
        let cb = d.iadd(neg_dv, neg_x);
        let step_a = d.const_app(p.add_assoc, &[y_dv, neg_x, neg_dv]); // (p+b)+c = p+(b+c)
        let rhs_a = d.iadd(y_dv, bc);
        let comm_bc = d.const_app(p.add_comm, &[neg_x, neg_dv]);
        let step_b = d.icongr(bc, cb, comm_bc, &|d, t| d.iadd(y_dv, t));
        let rhs_b = d.iadd(y_dv, cb);
        let step_c_fwd = d.const_app(p.add_assoc, &[y_dv, neg_dv, neg_x]); // (p+c)+b = p+(c+b)
        let step_c = d.isymm(target_swapped, rhs_b, step_c_fwd);
        let (_, chained) = d.ichain(
            r1_negdv,
            &[(rhs_a, step_a), (rhs_b, step_b), (target_swapped, step_c)],
        );
        chained
    };

    // Cancel dv on the swapped side: (y+dv)+(-dv) = y.
    let cancel2 = d.const_app(p.add_neg_cancel_right, &[y, dv]);
    let y_negx = d.iadd(y, neg_x);
    let congr2 = d.icongr(p_plus_negdv, y, cancel2, &|d, t| d.iadd(t, neg_x));

    let h5 = {
        let (_, chained) = d.ichain(r1_negdv, &[(target_swapped, swap), (y_negx, congr2)]);
        chained
    };

    let h6 = d.itrans(du_negdv, r1_negdv, y_negx, h4, h5);
    d.isymm(du_negdv, y_negx, h6)
}

/// `Int.modEq_of_nat_modEq :
/// ∀ (d a b : Nat), Nat.modEq d a b → 0 < d →
/// Int.ModEq (ofNat d) (ofNat a) (ofNat b)`.
///
/// Transports a `Nat.modEq` congruence (balanced witnesses: `∃ u v, a+d*u =
/// b+d*v`) into `Int.ModEq`. Only the N-to-Z direction is built: the witness
/// equation, read through `Int.ofNat`, is already exactly the shape
/// `modEq_iff_dvd`'s `mpr` consumes (`d ∣ (b-a)`, witness `u-v`), with no
/// magnitude bound on `emod` needed. The reverse direction would need to
/// recover a *balanced* Nat witness pair from an `Int.ModEq` (an `emod`
/// equality), which is a different, harder construction this slice does not
/// attempt.
///
/// Route: eliminate the double existential (`exists_elim` twice) to get
/// `u, v : Nat` and `eq : a+d*u = b+d*v`; lift `eq` to `Int` via
/// `NatOps::nat_rewrite` (`congrArg Int.ofNat`, defeq-transparent through
/// `Int.add`/`Int.mul` on the `ofNat` branches — the same "closes by
/// `Eq.refl`-shaped congruence" pattern `Int.factorial_succ` uses); then
/// `nat_witness_gap` turns that into `(ofNat b) - (ofNat a) = (ofNat d)*u -
/// (ofNat d)*v`, and `Int.mul_sub` folds the right side into `(ofNat d)*(u-v)`
/// — exactly the witness `modEq_iff_dvd`'s `mpr` needs.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
pub(super) fn declare_modeq_of_nat_modeq(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.theorem(p.mod_eq_of_nat_mod_eq, 3, &|d, v| {
        let (dm, a, b) = (v[0], v[1], v[2]);
        let nat = d.nat_ty();

        let modeq_nat_ty = d.mod_eq(dm, a, b);
        let zero_nat = d.zero();
        let pos_ty = d.lt(zero_nat, dm);

        let big_d = d.of_nat(dm);
        let big_a = d.of_nat(a);
        let big_b = d.of_nat(b);
        let concl = imodeq(d, big_d, big_a, big_b);

        let stmt = {
            let inner = d.arrow(pos_ty, concl);
            d.arrow(modeq_nat_ty, inner)
        };

        let modeq_fv = d.fresh_fvar();
        let modeq_hyp = d.kernel().fvar(modeq_fv);
        let pos_fv = d.fresh_fvar();
        let pos_hyp = d.kernel().fvar(pos_fv);

        let outer_pred = d.mod_eq_outer_predicate(dm, a, b);

        let minor1 = {
            let u_fv = d.fresh_fvar();
            let u = d.kernel().fvar(u_fv);
            let inner_ty = d.mod_eq_inner_exists(dm, a, b, u);
            let inner_pred = d.mod_eq_inner_predicate(dm, a, b, u);
            let inner_fv = d.fresh_fvar();
            let inner_hyp = d.kernel().fvar(inner_fv);

            let minor2 = {
                let vv_fv = d.fresh_fvar();
                let vv = d.kernel().fvar(vv_fv);
                let sum_a_nat = d.mod_eq_sum(dm, a, u);
                let sum_b_nat = d.mod_eq_sum(dm, b, vv);
                let eq_ty = d.eq(sum_a_nat, sum_b_nat);
                let eq_fv = d.fresh_fvar();
                let eq_hyp = d.kernel().fvar(eq_fv);

                // Lift the Nat witness equation to Int via congrArg ofNat.
                let of_nat_sum_a = d.of_nat(sum_a_nat);
                let base_proof = d.irefl(of_nat_sum_a);
                let motive = &|d: &mut IntDev<'_>, y: ExprId| {
                    let of_nat_y = d.of_nat(y);
                    d.ieq(of_nat_sum_a, of_nat_y)
                };
                let eq_int = d.nat_rewrite(sum_a_nat, sum_b_nat, eq_hyp, base_proof, motive);

                let big_u = d.of_nat(u);
                let big_v = d.of_nat(vv);
                let du = d.imul(big_d, big_u);
                let dv = d.imul(big_d, big_v);

                // eq_int, up to defeq (Int.add/Int.mul on ofNat branches),
                // has type `Eq Int (add big_a du) (add big_b dv)`.
                let gap = nat_witness_gap(d, big_a, big_b, du, dv, eq_int);

                // du - dv = D*(u-v), by symm(mul_sub).
                let uv_diff = d.isub(big_u, big_v);
                let d_uv = d.imul(big_d, uv_diff);
                let mul_sub_pf = d.const_app(p.mul_sub, &[big_d, big_u, big_v]); // D*(u-v) = D*u-D*v
                let du_dv = d.isub(du, dv);
                let reversed = d.isymm(d_uv, du_dv, mul_sub_pf);

                let b_minus_a = d.isub(big_b, big_a);
                let witness_eq = d.itrans(b_minus_a, du_dv, d_uv, gap, reversed);

                // Build the `Int.dvd` proof: witness `u - v`.
                let predicate = super::dvd::dvd_predicate(d, big_d, b_minus_a);
                let one_level = d.level_one();
                let intro_name = d.int().logic.exists_intro;
                let intro = d.kernel().const_(intro_name, vec![one_level]);
                let int_ty = d.int_ty();
                let dvd_proof = d.apply(intro, &[int_ty, predicate, uv_diff, witness_eq]);
                let dvd_ty = super::dvd::idvd(d, big_d, b_minus_a);

                // ModEq_iff_dvd's mpr.
                let iff_pf = d.const_app(p.mod_eq_iff_dvd, &[big_d, big_a, big_b, pos_hyp]);
                let mpr = d.const_app(p.logic.iff_mpr, &[concl, dvd_ty, iff_pf]);
                let result = d.apply(mpr, &[dvd_proof]);

                let body = d.lam_fv(eq_fv, eq_ty, result);
                d.lam_fv(vv_fv, nat, body)
            };
            let inner_elim = super::ops::exists_elim(d, inner_pred, concl, inner_hyp, minor2);
            let body = d.lam_fv(inner_fv, inner_ty, inner_elim);
            d.lam_fv(u_fv, nat, body)
        };
        let elim_body = super::ops::exists_elim(d, outer_pred, concl, modeq_hyp, minor1);

        let with_pos = d.lam_fv(pos_fv, pos_ty, elim_body);
        let proof = d.lam_fv(modeq_fv, modeq_nat_ty, with_pos);
        (stmt, proof)
    })?;
    Ok(())
}
