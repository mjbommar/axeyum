//! Quadratic residues over `ℤ`, and Euler's criterion's unconditional half.
//!
//! `Int.IsQuadraticResidue p a := ∃ x, ModEq p (x*x) a` — nothing in this
//! kernel named quadratic residues before this file. Two trivial closure
//! facts land alongside the definition: `1` is always a residue
//! (`declare_is_quadratic_residue_one`), and residues are closed under
//! multiplication (`declare_is_quadratic_residue_mul`, needing `0 < p` since
//! it goes through `Int.ModEq.mul`).
//!
//! ## Euler's criterion, the unconditional half
//!
//! `Int.euler_criterion_pm_one` — `p` prime, `p-1 = m+m`, `0 < a < p` ⟹
//! `a^m ≡ 1 [p] ∨ a^m ≡ -1 [p]` — is the real target of this file. Two
//! deliberate scope decisions, both load-bearing:
//!
//! - **The halving is a HYPOTHESIS, not a division.** `(p-1)/2` needs
//!   `Nat.div`, and this development's `Nat.sub` is truncated while
//!   `Nat.div` carries its own well-foundedness cost this chain has not
//!   needed elsewhere. Quantifying over `m` with `p-1 = m+m` given as a
//!   hypothesis says exactly the same thing for any *specific* odd prime
//!   (whoever instantiates this theorem supplies `m := (p-1)/2` and the
//!   witness `p-1 = m+m` however they've derived it) without this file ever
//!   constructing a division. `m+m` rather than `2*m` avoids a further
//!   `Nat.mul`-vs-`Nat.add` bridging step (`2*m = m+m`) that buys nothing
//!   here.
//! - **`Int.self_inverse_mod_prime` (`wilson.rs`) is exactly step 2 of the
//!   classical proof, already landed**: `a*a ≡ 1 [p] ⟹ a ≡ 1 [p] ∨ a ≡ -1
//!   [p]` (its second disjunct is literally `ModEq p a (p - one)`, and
//!   `wilson.rs`'s `neg_one_modeq_p_minus_one` bridges `p - one` to `-1`).
//!   Its own doc records that the `1 ≤ a ≤ p-1` hypotheses are UNUSED in its
//!   proof — but they are still part of its stated type, so applying it to
//!   `a := a₀^m` (which can be far larger than `p`) is not directly
//!   possible: [`reduce_to_canonical_residue`] below reduces `a₀^m` to its
//!   canonical residue `r := emod (a₀^m) p` first (mirroring the bounds
//!   machinery `wilson::declare_inverse_index_fixed_point` already built for
//!   its own residue, `mag := natAbs (emod (a^(p-2)) p)`), then transports
//!   the conclusion back through `ModEq p (a₀^m) r`
//!   (`wilson::emod_modeq_self`).
//!
//! Fermat (`Int.pow_prime_sub_one_modeq_one`) plus `Int.pow_add` supplies
//! `ModEq p ((a^m)*(a^m)) one` from `a^(p-1) ≡ 1` and `p-1 = m+m`; from there
//! `reduce_to_canonical_residue` plus `Int.self_inverse_mod_prime` finishes.
//!
//! The full criterion — that the SIGN decides quadratic-residue-hood — needs
//! a primitive root or a counting argument neither this file nor `wilson.rs`
//! builds; only the unconditional `±1` dichotomy is proved here.

use super::ops::IntDev;
use crate::BinderInfo;
use crate::KernelError;
use crate::env::{Declaration, ReducibilityHint};
use crate::expr::ExprId;
use crate::nat_prelude::NatOps;

use super::defs::DERIVED_HEIGHT;
use super::wilson::{
    emod_modeq_self, int_ne_zero_of_pos, nat_prime_pos, neg_one_modeq_p_minus_one,
    ofnat_pm1_eq_sub_one, pos_of_ne_zero, prime_condition, prime_parts,
};

// ============================================================================
// `Int.IsQuadraticResidue`
// ============================================================================

/// `Exists.{1} Int predicate`.
fn int_exists(d: &mut IntDev<'_>, predicate: ExprId) -> ExprId {
    let int_ty = d.int_ty();
    let one = d.level_one();
    let name = d.int().logic.exists_;
    let exists = d.kernel().const_(name, vec![one]);
    d.apply(exists, &[int_ty, predicate])
}

/// `Exists.intro.{1} Int predicate witness proof`.
pub(super) fn int_exists_intro(
    d: &mut IntDev<'_>,
    predicate: ExprId,
    witness: ExprId,
    proof: ExprId,
) -> ExprId {
    let int_ty = d.int_ty();
    let one = d.level_one();
    let name = d.int().logic.exists_intro;
    let intro = d.kernel().const_(name, vec![one]);
    d.apply(intro, &[int_ty, predicate, witness, proof])
}

/// Eliminate `witness : Exists.{1} Int predicate` into `target`, given
/// `minor : ∀ (a : Int), predicate a → target`. The same shape as
/// `modinv.rs`'s private `idvd_elim`, generalized off `Int.dvd`'s own
/// predicate (that one is not `pub(super)`, and this is nine lines).
pub(super) fn int_exists_elim(
    d: &mut IntDev<'_>,
    predicate: ExprId,
    target: ExprId,
    witness: ExprId,
    minor: ExprId,
) -> ExprId {
    let int_ty = d.int_ty();
    let one = d.level_one();
    let exists_ty = int_exists(d, predicate);
    let anon = d.anon_name();
    let motive = d.kernel().lam(anon, exists_ty, target, BinderInfo::Default);
    let rec_name = d.int().logic.exists_rec;
    let rec = d.kernel().const_(rec_name, vec![one]);
    d.apply(rec, &[int_ty, predicate, motive, minor, witness])
}

/// `fun (x : Int) => ModEq p_modulus (x*x) a`.
pub(super) fn residue_predicate(d: &mut IntDev<'_>, p_modulus: ExprId, a: ExprId) -> ExprId {
    let int_ty = d.int_ty();
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let xx = d.imul(x, x);
    let body = super::modeq::imodeq(d, p_modulus, xx, a);
    d.lam_fv(x_fv, int_ty, body)
}

/// `Int.IsQuadraticResidue p_modulus a`, i.e.
/// `d.const_app(p.is_quadratic_residue, &[p_modulus, a])`.
pub(super) fn is_quadratic_residue(d: &mut IntDev<'_>, p_modulus: ExprId, a: ExprId) -> ExprId {
    let f = d.int().is_quadratic_residue;
    d.const_app(f, &[p_modulus, a])
}

/// Admit `Int.IsQuadraticResidue : Int → Int → Prop :=
/// fun p a => ∃ x, ModEq p (x*x) a`.
///
/// # Errors
///
/// Returns the trusted gate's rejection (a malformed statement, or a name
/// conflict).
pub(super) fn declare_is_quadratic_residue(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    let int_ty = d.int_ty();
    let anon = d.anon_name();
    let prop = d.kernel().sort_zero();
    let one = d.level_one();

    let p_fv = d.fresh_fvar();
    let p_var = d.kernel().fvar(p_fv);
    let a_fv = d.fresh_fvar();
    let a_var = d.kernel().fvar(a_fv);
    let pred = residue_predicate(d, p_var, a_var);
    let exists = d.kernel().const_(p.logic.exists_, vec![one]);
    let body = d.apply(exists, &[int_ty, pred]);
    let value = {
        let inner = d.lam_fv(a_fv, int_ty, body);
        d.lam_fv(p_fv, int_ty, inner)
    };
    let ty = {
        let inner = d.kernel().pi(anon, int_ty, prop, BinderInfo::Default);
        d.kernel().pi(anon, int_ty, inner, BinderInfo::Default)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.is_quadratic_residue,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(DERIVED_HEIGHT),
    })
}

/// `Int.is_quadratic_residue_one : ∀ p, IsQuadraticResidue p one` — witness
/// `x := one`, via `Int.mul_one` reshaping `ModEq.refl p one` into
/// `ModEq p (one*one) one`.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
pub(super) fn declare_is_quadratic_residue_one(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.is_quadratic_residue_one, 1, &|d, v| {
        let p_var = v[0];
        let one_i = d.ione();
        let stmt = is_quadratic_residue(d, p_var, one_i);

        let mul_one_one = d.imul(one_i, one_i);
        let eq_mul_one = d.const_app(p.mul_one, &[one_i]); // Eq Int mul_one_one one_i
        let eq_rev = d.isymm(mul_one_one, one_i, eq_mul_one); // Eq Int one_i mul_one_one
        let refl_pf = d.const_app(p.mod_eq_refl, &[p_var, one_i]); // ModEq p_var one_i one_i
        let sq_modeq = d.int_eq_rewrite(one_i, mul_one_one, eq_rev, refl_pf, &|d, x| {
            super::modeq::imodeq(d, p_var, x, one_i)
        }); // ModEq p_var mul_one_one one_i

        let pred = residue_predicate(d, p_var, one_i);
        let proof = int_exists_intro(d, pred, one_i, sq_modeq);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Eq Int (mul (mul x x) (mul y y)) (mul (mul x y) (mul x y))` — regroup
/// `x²·y²` into `(xy)²`, needed to see the product of two residues' witnesses
/// as a witness for the product. Built as a forward chain from `(x*y)*(x*y)`
/// down to `(x*x)*(y*y)` (`mul_assoc`/`mul_comm` only), then flipped with
/// `isymm` — cheaper than chasing the same identity in the other direction
/// from scratch.
pub(super) fn sq_mul_sq_eq_mul_sq(d: &mut IntDev<'_>, x: ExprId, y: ExprId) -> ExprId {
    let p = d.int();
    let xy = d.imul(x, y);
    let start = d.imul(xy, xy); // (x*y)*(x*y)

    // s1 := x*(y*(x*y))   [mul_assoc x y (x*y)]
    let yxy = d.imul(y, xy);
    let s1 = d.imul(x, yxy);
    let p1 = d.const_app(p.mul_assoc, &[x, y, xy]); // Eq Int start s1

    // s2 := x*((y*x)*y)   [congr: y*(x*y) = (y*x)*y, via symm(mul_assoc y x y)]
    let yx = d.imul(y, x);
    let yx_y = d.imul(yx, y);
    let assoc_yxy = d.const_app(p.mul_assoc, &[y, x, y]); // Eq Int yx_y yxy
    let inner2 = d.isymm(yx_y, yxy, assoc_yxy); // Eq Int yxy yx_y
    let s2 = d.imul(x, yx_y);
    let p2 = d.icongr(yxy, yx_y, inner2, &|d, t| d.imul(x, t)); // Eq Int s1 s2

    // s3 := x*((x*y)*y)   [congr: (y*x)*y = (x*y)*y, via mul_comm y x]
    let xy_y = d.imul(xy, y);
    let comm_yx = d.const_app(p.mul_comm, &[y, x]); // Eq Int yx xy
    let inner3 = d.icongr(yx, xy, comm_yx, &|d, t| d.imul(t, y)); // Eq Int yx_y xy_y
    let s3 = d.imul(x, xy_y);
    let p3 = d.icongr(yx_y, xy_y, inner3, &|d, t| d.imul(x, t)); // Eq Int s2 s3

    // s4 := x*(x*(y*y))   [congr: (x*y)*y = x*(y*y), via mul_assoc x y y]
    let yy = d.imul(y, y);
    let xyy = d.imul(x, yy);
    let assoc_xyy = d.const_app(p.mul_assoc, &[x, y, y]); // Eq Int xy_y xyy
    let s4 = d.imul(x, xyy);
    let p4 = d.icongr(xy_y, xyy, assoc_xyy, &|d, t| d.imul(x, t)); // Eq Int s3 s4

    // s5 := (x*x)*(y*y)   [symm(mul_assoc x x (y*y))]
    let xx = d.imul(x, x);
    let s5 = d.imul(xx, yy);
    let assoc_xxyy = d.const_app(p.mul_assoc, &[x, x, yy]); // Eq Int s5 s4
    let p5 = d.isymm(s5, s4, assoc_xxyy); // Eq Int s4 s5

    let (_, forward) = d.ichain(start, &[(s1, p1), (s2, p2), (s3, p3), (s4, p4), (s5, p5)]);
    // forward : Eq Int start s5, i.e. Eq Int ((x*y)*(x*y)) ((x*x)*(y*y))
    d.isymm(start, s5, forward) // Eq Int s5 start, i.e. Eq Int ((x*x)*(y*y)) ((x*y)*(x*y))
}

/// `Int.is_quadratic_residue_mul :
/// ∀ p a b, 0 < p → IsQuadraticResidue p a → IsQuadraticResidue p b →
///   IsQuadraticResidue p (mul a b)` — residues are closed under
/// multiplication: if `x*x ≡ a` and `y*y ≡ b`, then `(x*y)*(x*y) ≡ a*b`
/// (`Int.ModEq.mul` plus [`sq_mul_sq_eq_mul_sq`]), so `x*y` witnesses
/// `IsQuadraticResidue p (a*b)`.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
pub(super) fn declare_is_quadratic_residue_mul(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.is_quadratic_residue_mul, 3, &|d, v| {
        let (p_var, a, b) = (v[0], v[1], v[2]);
        let zero = d.izero();
        let pos_ty = d.ilt(zero, p_var);
        let res_a_ty = is_quadratic_residue(d, p_var, a);
        let res_b_ty = is_quadratic_residue(d, p_var, b);
        let ab = d.imul(a, b);
        let res_ab_ty = is_quadratic_residue(d, p_var, ab);

        let stmt = {
            let inner = d.arrow(res_b_ty, res_ab_ty);
            let with_a = d.arrow(res_a_ty, inner);
            d.arrow(pos_ty, with_a)
        };

        let pos_fv = d.fresh_fvar();
        let pos_proof = d.kernel().fvar(pos_fv);
        let ra_fv = d.fresh_fvar();
        let res_a = d.kernel().fvar(ra_fv);
        let rb_fv = d.fresh_fvar();
        let res_b = d.kernel().fvar(rb_fv);

        let pred_a = residue_predicate(d, p_var, a);
        let pred_b = residue_predicate(d, p_var, b);
        let pred_ab = residue_predicate(d, p_var, ab);

        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let hx_fv = d.fresh_fvar();
        let hx = d.kernel().fvar(hx_fv);
        let xx = d.imul(x, x);
        let hx_ty = super::modeq::imodeq(d, p_var, xx, a);

        let y_fv = d.fresh_fvar();
        let y = d.kernel().fvar(y_fv);
        let hy_fv = d.fresh_fvar();
        let hy = d.kernel().fvar(hy_fv);
        let yy = d.imul(y, y);
        let hy_ty = super::modeq::imodeq(d, p_var, yy, b);

        // ModEq p_var (xx*yy) (a*b).
        let mulmod = d.const_app(p.mod_eq_mul, &[p_var, xx, a, yy, b, pos_proof, hx, hy]);

        // (xx*yy) = (xy*xy), regrouped.
        let xy = d.imul(x, y);
        let xy_xy = d.imul(xy, xy);
        let xx_yy = d.imul(xx, yy);
        let eq_chain = sq_mul_sq_eq_mul_sq(d, x, y); // Eq Int xx_yy xy_xy
        let rewritten = d.int_eq_rewrite(xx_yy, xy_xy, eq_chain, mulmod, &|d, t| {
            super::modeq::imodeq(d, p_var, t, ab)
        }); // ModEq p_var xy_xy ab

        let witness_result = int_exists_intro(d, pred_ab, xy, rewritten);

        let minor_b = {
            let inner = d.lam_fv(hy_fv, hy_ty, witness_result);
            d.lam_fv(y_fv, d.int_ty(), inner)
        };
        let eliminated_b = int_exists_elim(d, pred_b, res_ab_ty, res_b, minor_b);

        let minor_a = {
            let inner = d.lam_fv(hx_fv, hx_ty, eliminated_b);
            d.lam_fv(x_fv, d.int_ty(), inner)
        };
        let eliminated_a = int_exists_elim(d, pred_a, res_ab_ty, res_a, minor_a);

        let with_res_b = d.lam_fv(rb_fv, res_b_ty, eliminated_a);
        let with_res_a = d.lam_fv(ra_fv, res_a_ty, with_res_b);
        let proof = d.lam_fv(pos_fv, pos_ty, with_res_a);
        (stmt, proof)
    })?;
    Ok(())
}

// ============================================================================
// `Int.euler_criterion_pm_one`
// ============================================================================

/// Given `x : Int` with `ModEq p_var (mul x x) one`, `pos_p : 0 < p_var`, and
/// a primality proof for `pp` (`p_var = ofNat pp`), derive `Not (Eq Int x
/// zero)` — a residue whose square is `≡ 1` cannot itself be `≡ 0`, else
/// `p_var ∣ one`, contradicting `2 ≤ pp`.
fn nonzero_of_sq_modeq_one(
    d: &mut IntDev<'_>,
    pp: ExprId,
    p_var: ExprId,
    pos_p: ExprId,
    prime_proof: ExprId,
    x: ExprId,
    sq_modeq: ExprId,
) -> ExprId {
    let p = d.int();
    let zero_i = d.izero();
    let one_i = d.ione();
    let zero_nat = d.zero();
    let one_nat = d.num(1);
    let two_nat = d.num(2);

    let h0_fv = d.fresh_fvar();
    let h0 = d.kernel().fvar(h0_fv);
    let eq_ty = d.ieq(x, zero_i);

    // x*x = 0, from h0.
    let xx = d.imul(x, x);
    let zero_zero = d.imul(zero_i, zero_i);
    let congr_xx = d.icongr(x, zero_i, h0, &|d, t| d.imul(t, t));
    let mul_zero_pf = d.const_app(p.mul_zero, &[zero_i]);
    let (_, xx_eq_zero) = d.ichain(xx, &[(zero_zero, congr_xx), (zero_i, mul_zero_pf)]);

    // ModEq p_var zero one, from sq_modeq rewritten through xx_eq_zero.
    let modeq_zero_one_ty = super::modeq::imodeq(d, p_var, zero_i, one_i);
    let modeq_zero_one = d.int_eq_rewrite(xx, zero_i, xx_eq_zero, sq_modeq, &|d, t| {
        super::modeq::imodeq(d, p_var, t, one_i)
    });

    // p_var ∣ one, via modEq_iff_dvd.
    let dvd_one_ty = super::dvd::idvd(d, p_var, one_i);
    let iff_ty = d.const_app(p.mod_eq_iff_dvd, &[p_var, zero_i, one_i, pos_p]);
    let mp = d.const_app(p.logic.iff_mp, &[modeq_zero_one_ty, dvd_one_ty, iff_ty]);
    let dvd_one = d.apply(mp, &[modeq_zero_one]);

    // pp ∣ 1 (Nat), hence pp = 1 — contradicting 2 ≤ pp.
    let nat_dvd_one = d.const_app(p.nat_abs_dvd_nat_abs_of_dvd, &[p_var, one_i, dvd_one]);
    let pp_eq_one = d.lemma(p.nat.eq_one_of_dvd_one, &[pp, nat_dvd_one]);

    let (two_le_ty, clause_ty) = prime_parts(d, pp);
    let two_le = d.and_left(two_le_ty, clause_ty, prime_proof);
    let two_le_one = d.nat_rewrite(pp, one_nat, pp_eq_one, two_le, &|d, t| d.le(two_nat, t));
    let le_fn = d.lemma(p.nat.le_of_succ_le_succ, &[one_nat, zero_nat]);
    let one_le_zero = d.apply(le_fn, &[two_le_one]);
    let false_pf = d.lemma(p.nat.not_succ_le_zero, &[zero_nat, one_le_zero]);

    d.lam_fv(h0_fv, eq_ty, false_pf)
}

/// Given `x : Int` with `ModEq p_var (mul x x) one`, reduce to the canonical
/// residue `r := emod x p_var` and everything `Int.self_inverse_mod_prime`
/// needs applied there: `1 ≤ r`, `r ≤ p_var - one`, `ModEq p_var (r*r) one`,
/// plus the bridge `ModEq p_var x r` used to transport the conclusion back to
/// `x`. Mirrors the bounds apparatus `wilson::declare_inverse_index_fixed_point`
/// builds inline for its own residue `mag := natAbs (emod (a^(p-2)) p)`, minus
/// the `-1` index-offset bookkeeping that construction needs and this one
/// does not.
///
/// Returns `(r, lb_r, ub_r, sq_modeq_r, modeq_x_r)`.
#[allow(clippy::too_many_arguments)]
fn reduce_to_canonical_residue(
    d: &mut IntDev<'_>,
    pp: ExprId,
    prime_proof: ExprId,
    p_var: ExprId,
    pos_p: ExprId,
    one_le_pp: ExprId,
    x: ExprId,
    sq_modeq_x: ExprId,
) -> (ExprId, ExprId, ExprId, ExprId, ExprId) {
    let p = d.int();
    let zero_i = d.izero();
    let one_i = d.ione();
    let zero_nat = d.zero();
    let one_nat = d.num(1);

    let r = d.iemod(x, p_var);
    let mag = {
        let f = p.nat_abs;
        d.const_app(f, &[r])
    };
    let ne_p = int_ne_zero_of_pos(d, p_var, pos_p);
    let r_nonneg = d.const_app(p.emod_nonneg, &[x, p_var, ne_p]);
    let r_lt = d.const_app(p.emod_lt_of_pos, &[x, p_var, pos_p]);
    let bridge = d.const_app(p.of_nat_nat_abs_of_nonneg, &[r, r_nonneg]); // Eq Int (ofNat mag) r
    let ofnat_mag = d.of_nat(mag);
    let bridge_rev = d.isymm(ofnat_mag, r, bridge); // Eq Int r ofnat_mag

    // ModEq p_var x r (always).
    let modeq_x_r = emod_modeq_self(d, x, p_var, pos_p);

    // ModEq p_var (r*r) one, via x ≡ r (twice) and trans with sq_modeq_x.
    let modeq_r_x = d.const_app(p.mod_eq_symm, &[p_var, x, r, modeq_x_r]);
    let rr_modeq_xx = d.const_app(
        p.mod_eq_mul,
        &[p_var, r, x, r, x, pos_p, modeq_r_x, modeq_r_x],
    );
    let rr = d.imul(r, r);
    let xx = d.imul(x, x);
    let sq_modeq_r = d.const_app(
        p.mod_eq_trans,
        &[p_var, rr, xx, one_i, rr_modeq_xx, sq_modeq_x],
    );

    // mag < pp (Nat), from r < p_var (Int) rewritten through the bridge.
    let r_lt_ofnat_mag = d.int_eq_rewrite(r, ofnat_mag, bridge_rev, r_lt, &|d, t| d.ilt(t, p_var));
    let mag_lt_pp = r_lt_ofnat_mag; // reused directly as Nat.lt mag pp

    // r ≤ p_var - one.
    let pm1 = d.sub(pp, one_nat);
    let sub_eq_pm1 = ofnat_pm1_eq_sub_one(d, pp, one_le_pp); // Eq Int (isub p_var one) (ofNat pm1)
    let succ_pm1 = d.succ(pm1);
    let cancel1 = d.lemma(p.nat.sub_add_cancel, &[one_nat, pp, one_le_pp]);
    let cancel1_rev = d.symm(succ_pm1, pp, cancel1);
    let mag_lt_succ_pm1 = d.nat_rewrite(pp, succ_pm1, cancel1_rev, mag_lt_pp, &|d, t| d.lt(mag, t));
    let le_fn = d.lemma(p.nat.le_of_lt_succ, &[mag, pm1]);
    let mag_le_pm1 = d.apply(le_fn, &[mag_lt_succ_pm1]); // Nat.le mag pm1
    let sub_big_p_one = d.isub(p_var, one_i);
    let ofnat_pm1 = d.of_nat(pm1);
    let sub_eq_pm1_rev = d.isymm(sub_big_p_one, ofnat_pm1, sub_eq_pm1);
    let ub_ofnat_mag = d.int_eq_rewrite(
        ofnat_pm1,
        sub_big_p_one,
        sub_eq_pm1_rev,
        mag_le_pm1,
        &|d, t| d.ile(ofnat_mag, t),
    );
    let ub_r = d.int_eq_rewrite(ofnat_mag, r, bridge, ub_ofnat_mag, &|d, t| {
        d.ile(t, sub_big_p_one)
    });

    // 1 ≤ r.
    let x_ne_zero = nonzero_of_sq_modeq_one(d, pp, p_var, pos_p, prime_proof, r, sq_modeq_r);
    let mag_ne_zero_nat = {
        let h0_fv = d.fresh_fvar();
        let h0 = d.kernel().fvar(h0_fv);
        let eq_ty = d.eq(mag, zero_nat);
        let congr0 = d.nat_eq_to_int(mag, zero_nat, h0, &|d, y| d.of_nat(y)); // Eq Int ofnat_mag zero_i
        let r_eq_zero = d.itrans(r, ofnat_mag, zero_i, bridge_rev, congr0);
        let false_pf = d.apply(x_ne_zero, &[r_eq_zero]);
        d.lam_fv(h0_fv, eq_ty, false_pf)
    };
    let mag_pos = pos_of_ne_zero(d, mag, mag_ne_zero_nat); // Nat.lt zero mag
    let lb_r = d.int_eq_rewrite(ofnat_mag, r, bridge, mag_pos, &|d, t| d.ile(one_i, t));

    (r, lb_r, ub_r, sq_modeq_r, modeq_x_r)
}

/// `Int.euler_criterion_pm_one :
/// ∀ pp aa m, (2 ≤ pp ∧ ∀ d, d ∣ pp → d = 1 ∨ d = pp) →
///   Eq Nat (pp-1) (m+m) → 0 < aa → aa < pp →
///   Or (ModEq (ofNat pp) (pow (ofNat aa) m) one)
///      (ModEq (ofNat pp) (pow (ofNat aa) m) (neg one))`
///
/// The unconditional half of Euler's criterion: `a^((p-1)/2) ≡ ±1 [p]`,
/// stated with the half-exponent `m` (`p-1 = m+m`) supplied as a hypothesis
/// rather than computed by division — see this module's doc for why. Route:
/// `Int.pow_prime_sub_one_modeq_one` (Fermat) gives `a^(p-1) ≡ 1`; rewriting
/// the exponent through `p-1 = m+m` and splitting via `Int.pow_add` gives
/// `ModEq p ((a^m)*(a^m)) one`; [`reduce_to_canonical_residue`] plus
/// `Int.self_inverse_mod_prime` decides `a^m ≡ ±1 [p]`.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
#[allow(clippy::too_many_lines)]
pub(super) fn declare_euler_criterion_pm_one(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.theorem(p.euler_criterion_pm_one, 3, &|d, v| {
        let (pp, aa, m) = (v[0], v[1], v[2]);
        let prime_ty = prime_condition(d, pp);
        let one_nat = d.num(1);
        let pm1 = d.sub(pp, one_nat);
        let mm = d.add(m, m);
        let half_ty = d.eq(pm1, mm);
        let zero = d.zero();
        let pos_ty = d.lt(zero, aa);
        let ub_ty = d.lt(aa, pp);

        let big_p = d.of_nat(pp);
        let big_a = d.of_nat(aa);
        let x = d.ipow(big_a, m); // a^m
        let one_i = d.ione();
        let neg_one = d.ineg(one_i);
        let modeq_x_one = super::modeq::imodeq(d, big_p, x, one_i);
        let modeq_x_negone = super::modeq::imodeq(d, big_p, x, neg_one);
        let concl = d.or(modeq_x_one, modeq_x_negone);

        let stmt = {
            let inner = d.arrow(ub_ty, concl);
            let with_pos = d.arrow(pos_ty, inner);
            let with_half = d.arrow(half_ty, with_pos);
            d.arrow(prime_ty, with_half)
        };

        let prime_fv = d.fresh_fvar();
        let prime_proof = d.kernel().fvar(prime_fv);
        let half_fv = d.fresh_fvar();
        let half_proof = d.kernel().fvar(half_fv);
        let pos_fv = d.fresh_fvar();
        let pos_proof = d.kernel().fvar(pos_fv);
        let ub_fv = d.fresh_fvar();
        let ub_proof = d.kernel().fvar(ub_fv);

        let one_le_pp = nat_prime_pos(d, pp, prime_proof);
        let pos_big_p = one_le_pp;

        // Fermat: ModEq big_p (pow big_a pm1) one.
        let fermat = d.const_app(
            p.pow_prime_sub_one_modeq_one,
            &[pp, aa, prime_proof, pos_proof, ub_proof],
        );

        // Rewrite the exponent pm1 -> m+m via half_proof.
        let pow_pm1 = d.ipow(big_a, pm1);
        let pow_mm = d.ipow(big_a, mm);
        let congr_exp = d.nat_eq_to_int(pm1, mm, half_proof, &|d, t| d.ipow(big_a, t));
        let fermat_mm = d.int_eq_rewrite(pow_pm1, pow_mm, congr_exp, fermat, &|d, t| {
            super::modeq::imodeq(d, big_p, t, one_i)
        });

        // pow big_a (m+m) = pow big_a m * pow big_a m, via Int.pow_add.
        let pow_add_eq = d.const_app(p.pow_add, &[big_a, m, m]);
        let xx = d.imul(x, x);
        let sq_modeq_x = d.int_eq_rewrite(pow_mm, xx, pow_add_eq, fermat_mm, &|d, t| {
            super::modeq::imodeq(d, big_p, t, one_i)
        });

        // Reduce to the canonical residue r := x mod big_p.
        let (r, lb_r, ub_r, sq_modeq_r, modeq_x_r) = reduce_to_canonical_residue(
            d,
            pp,
            prime_proof,
            big_p,
            pos_big_p,
            one_le_pp,
            x,
            sq_modeq_x,
        );

        let disj = d.const_app(
            p.self_inverse_mod_prime,
            &[big_p, r, prime_proof, pos_big_p, lb_r, ub_r, sq_modeq_r],
        );
        let modeq_r_one_ty = super::modeq::imodeq(d, big_p, r, one_i);
        let p_minus_one = d.isub(big_p, one_i);
        let modeq_r_pm1_ty = super::modeq::imodeq(d, big_p, r, p_minus_one);

        let on_left = &|d: &mut IntDev<'_>, h: ExprId| -> ExprId {
            let combined = d.const_app(p.mod_eq_trans, &[big_p, x, r, one_i, modeq_x_r, h]);
            d.or_inl(modeq_x_one, modeq_x_negone, combined)
        };
        let on_right = &|d: &mut IntDev<'_>, h: ExprId| -> ExprId {
            let x_pm1 = d.const_app(p.mod_eq_trans, &[big_p, x, r, p_minus_one, modeq_x_r, h]);
            let neg_pm1 = neg_one_modeq_p_minus_one(d, big_p, pos_big_p); // ModEq big_p neg_one p_minus_one
            let pm1_neg = d.const_app(p.mod_eq_symm, &[big_p, neg_one, p_minus_one, neg_pm1]);
            let combined = d.const_app(
                p.mod_eq_trans,
                &[big_p, x, p_minus_one, neg_one, x_pm1, pm1_neg],
            );
            d.or_inr(modeq_x_one, modeq_x_negone, combined)
        };

        let result = d.or_elim(
            modeq_r_one_ty,
            modeq_r_pm1_ty,
            concl,
            disj,
            on_left,
            on_right,
        );

        let with_ub = d.lam_fv(ub_fv, ub_ty, result);
        let with_pos = d.lam_fv(pos_fv, pos_ty, with_ub);
        let with_half = d.lam_fv(half_fv, half_ty, with_pos);
        let proof = d.lam_fv(prime_fv, prime_ty, with_half);
        (stmt, proof)
    })?;
    Ok(())
}
