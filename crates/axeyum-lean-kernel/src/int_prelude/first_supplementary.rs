//! **The first supplementary law of quadratic reciprocity**, non-residue half:
//! for an odd prime `p = 2m+1` with `m` ODD (equivalently `p ≡ 3 (mod 4)`),
//! `-1` is not a quadratic residue mod `p`.
//!
//! ## Why this half and not the other
//!
//! The classical statement is a biconditional — `-1` is a residue mod `p`
//! **iff** `p ≡ 1 (mod 4)` — and the two halves have completely different
//! costs in this kernel:
//!
//! - `p ≡ 3 (mod 4) ⟹ not a residue` (this file) is a corollary of Euler's
//!   criterion's non-residue detector
//!   (`Int.euler_criterion_neg_one_imp_not_residue`, `qr_criterion.rs`), which
//!   needs only the NECESSARY direction of Euler's criterion. That direction
//!   is proved.
//! - `p ≡ 1 (mod 4) ⟹ IS a residue` needs a WITNESS. The Euler-criterion
//!   route to it requires the CONVERSE (`a^((p-1)/2) ≡ 1 ⟹ a is a residue`),
//!   which `qr_criterion.rs`'s module doc records as needing a primitive root
//!   or a root-counting argument this kernel cannot state. The route that
//!   avoids the converse entirely is **Wilson's theorem**, which IS proved
//!   here (`Int.wilson`): `(p-1)! ≡ (-1)^m (m!)^2 [p]`, so at even `m` the
//!   witness is `m!` outright. See this module's `## The Wilson route` section
//!   and `docs/plan/status/first-supplementary-law.md` for the precise
//!   remaining gap.
//!
//! ## Route (this file)
//!
//! `-1` is not directly in `euler_criterion_neg_one_imp_not_residue`'s reach:
//! that theorem is stated over a NATURAL `aa` with `0 < aa < pp`. So it is
//! applied at `aa := 2*m` — the canonical representative of `-1` mod `p` — and
//! the conclusion is transported back to `-1` along
//! [`declare_is_quadratic_residue_of_mod_eq`], the (previously missing)
//! statement that `IsQuadraticResidue` respects `ModEq` in its second
//! argument.
//!
//! The three side conditions all come from `m` being odd rather than from
//! primality, which matters because `m = 0` would make every one of them
//! false (`p` would be `1`):
//!
//! - `0 < 2*m` and `2 < p` both reduce to `1 ≤ m`, which
//!   [`one_le_of_odd`] extracts from `Nat.Odd m`'s own witness (`m = succ
//!   (k+k)`) with no arithmetic at all.
//! - `2*m < p` is `Nat.lt_succ_self` at `2*m`, since `p` is literally
//!   `succ (mul 2 m)`.
//! - `p - 1 = m + m` is `second_supplementary::two_mul_eq_add_self`, accepted
//!   at the stated `sub p 1` because `Nat.sub` recurses on its SECOND argument
//!   (`sub x (succ j) ≡ pred (sub x j)`), so `sub (succ (mul 2 m)) 1` iota-
//!   reduces to `mul 2 m` with no rewrite.
//!
//! ## The Wilson route (not built here)
//!
//! `(p-1)! = m! · ∏_{j=m+1}^{2m} j` and each `j` in the upper half is
//! `≡ -(p-j)` with `p-j` running over `1..m`, so `(p-1)! ≡ (-1)^m (m!)^2`.
//! Every ingredient except ONE is already in this prelude:
//! `Int.prodRange_permute` supplies the reversal, `Int.modEq_prodRange_lt` the
//! pointwise congruence, and `Int.prodRange_scaledIndexEqPowMulFactorial` at
//! `a := -1` collapses `∏ (-1)·(k+1)` to `(-1)^m · m!` in one step. The
//! missing piece is a `prodRange` SPLIT —
//! `prodRange f (add a b) = prodRange f a * prodRange (fun k => f (add a k)) b`
//! — which nothing in `prod.rs` provides (`prodRange_shiftFront` peels one
//! front term, `prodRange_succ` one back term; neither splits at a symbolic
//! point).

use super::euler::{int_exists_elim, int_exists_intro, is_quadratic_residue, residue_predicate};
use super::modeq::imodeq;
use super::ops::{IntDev, exists_elim};
use super::second_supplementary::{odd_predicate, two_mul_eq_add_self};
use super::wilson::{ofnat_pm1_eq_sub_one, prime_condition};
use crate::KernelError;
use crate::expr::ExprId;
use crate::nat_prelude::NatOps;

// ============================================================================
// `Int.isQuadraticResidue_of_modEq`
// ============================================================================

/// `Int.isQuadraticResidue_of_modEq :
///   ∀ (n a b : Int), ModEq n a b → IsQuadraticResidue n a →
///     IsQuadraticResidue n b`
///
/// The witness is unchanged: `x*x ≡ a` and `a ≡ b` compose by
/// `Int.ModEq.trans`. Needed because every quadratic-residue theorem in
/// `qr_criterion.rs` is stated over a NATURAL representative `ofNat aa`, while
/// the supplementary laws are about `-1`.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_is_quadratic_residue_of_mod_eq(
    d: &mut IntDev<'_>,
) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.is_quadratic_residue_of_mod_eq, 3, &|d, v| {
        let (n, a, b) = (v[0], v[1], v[2]);
        let int_ty = d.int_ty();
        let modeq_ty = imodeq(d, n, a, b);
        let res_a_ty = is_quadratic_residue(d, n, a);
        let res_b_ty = is_quadratic_residue(d, n, b);

        let stmt = {
            let inner = d.arrow(res_a_ty, res_b_ty);
            d.arrow(modeq_ty, inner)
        };

        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let ra_fv = d.fresh_fvar();
        let res_a = d.kernel().fvar(ra_fv);

        let pred_a = residue_predicate(d, n, a);
        let pred_b = residue_predicate(d, n, b);

        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let hx_fv = d.fresh_fvar();
        let hx = d.kernel().fvar(hx_fv);
        let xx = d.imul(x, x);
        let hx_ty = imodeq(d, n, xx, a);

        let composed = d.const_app(p.mod_eq_trans, &[n, xx, a, b, hx, h]);
        let intro = int_exists_intro(d, pred_b, x, composed);

        let minor = {
            let inner = d.lam_fv(hx_fv, hx_ty, intro);
            d.lam_fv(x_fv, int_ty, inner)
        };
        let eliminated = int_exists_elim(d, pred_a, res_b_ty, res_a, minor);

        let with_res_a = d.lam_fv(ra_fv, res_a_ty, eliminated);
        let proof = d.lam_fv(h_fv, modeq_ty, with_res_a);
        (stmt, proof)
    })?;
    Ok(())
}

// ============================================================================
// Side conditions, all from `Nat.Odd m` rather than from primality
// ============================================================================

/// `Le 1 m` from `Nat.Odd m`.
///
/// `Odd m`'s witness is an EQUATION `m = succ (k+k)`, so `Le 1 m` is
/// `succ_le_succ` of `zero_le (k+k)` transported backwards along it. Taking
/// this from oddness rather than from primality is what keeps the `m = 0`
/// boundary out of the theorem: at `m = 0` the modulus is `1`, and all three
/// side conditions below would be false.
fn one_le_of_odd(d: &mut IntDev<'_>, m: ExprId, odd_proof: ExprId) -> ExprId {
    let np = d.prelude();
    let nat = d.nat_ty();
    let one_nat = d.num(1);
    let target = d.le(one_nat, m);
    let pred = odd_predicate(d, m);

    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let kk = d.add(k, k);
    let skk = d.succ(kk);
    let hyp = d.eq(m, skk);
    let hk_fv = d.fresh_fvar();
    let hk = d.kernel().fvar(hk_fv);

    let zero = d.zero();
    let zle = d.lemma(np.zero_le, &[kk]);
    let base = d.lemma(np.succ_le_succ, &[zero, kk, zle]);
    let back = d.symm(m, skk, hk);
    let proof = d.nat_rewrite(skk, m, back, base, &|d, x| {
        let one_nat = d.num(1);
        d.le(one_nat, x)
    });

    let inner = d.lam_fv(hk_fv, hyp, proof);
    let minor = d.lam_fv(k_fv, nat, inner);
    exists_elim(d, pred, target, odd_proof, minor)
}

/// `Le 2 (mul 2 m)` from `Le 1 m`.
///
/// `add 1 1` iota-reduces to `2` (`Nat.add` recurses on its RIGHT argument),
/// so `add_le_add_right` then `add_le_add_left` bracket `Le 2 (add m m)` with
/// no numeral arithmetic; `two_mul_eq_add_self` carries it back to `mul 2 m`.
fn two_le_two_mul(d: &mut IntDev<'_>, m: ExprId, one_le_m: ExprId) -> ExprId {
    let np = d.prelude();
    let one_nat = d.num(1);
    let two_nat = d.num(2);

    // `Le (add 1 1) (add m 1)` -- and `add 1 1` is defeq `2`.
    let step_r = d.lemma(np.add_le_add_right, &[one_nat, one_nat, m, one_le_m]);
    // `Le (add m 1) (add m m)`.
    let step_l = d.lemma(np.add_le_add_left, &[m, one_nat, m, one_le_m]);
    let m_plus_one = d.add(m, one_nat);
    let mm = d.add(m, m);
    let chained = d.lemma(np.le_trans, &[two_nat, m_plus_one, mm, step_r, step_l]);

    // Back from `add m m` to `mul 2 m`.
    let two_mul = d.mul(two_nat, m);
    let forward = two_mul_eq_add_self(d, m);
    let back = d.symm(two_mul, mm, forward);
    d.nat_rewrite(mm, two_mul, back, chained, &|d, x| {
        let two_nat = d.num(2);
        d.le(two_nat, x)
    })
}

/// `Lt zero (of_nat (succ j))`, mirroring `wilson::declare_factorial_pos`'s
/// own inline construction (`Int.lt_ofNat_add zero j` transported past
/// `add_comm`/`add_zero`).
fn pos_of_nat_succ(d: &mut IntDev<'_>, j: ExprId) -> ExprId {
    let p = d.int();
    let zero_i = d.izero();
    let sj = d.succ(j);
    let sj_i = d.of_nat(sj);
    let base_lt = d.const_app(p.lt_of_nat_add, &[zero_i, j]);
    let sum = d.iadd(zero_i, sj_i);
    let sj0 = d.iadd(sj_i, zero_i);
    let comm = d.const_app(p.add_comm, &[zero_i, sj_i]);
    let addz = d.const_app(p.add_zero, &[sj_i]);
    let (_, sum_eq) = d.ichain(sum, &[(sj0, comm), (sj_i, addz)]);
    let motive = d.ieq_motive(sum, &|d, x| d.ilt(zero_i, x));
    d.itransport(sum, motive, base_lt, sj_i, sum_eq)
}

/// `ModEq (ofNat (succ (mul 2 m))) (neg one) (ofNat (mul 2 m))` — `-1`'s
/// canonical natural representative mod `p = 2m+1`.
///
/// `wilson::neg_one_modeq_p_minus_one` gives `ModEq p (-1) (p - 1)` over `Int`;
/// `wilson::ofnat_pm1_eq_sub_one` rewrites `p - 1` to `ofNat (sub pp 1)`, and
/// `sub (succ (mul 2 m)) 1` iota-reduces to `mul 2 m` so the result is accepted
/// at the stated `ofNat (mul 2 m)` with no further step.
fn neg_one_modeq_two_mul(
    d: &mut IntDev<'_>,
    m: ExprId,
    pos_pi: ExprId,
    one_le_pp: ExprId,
) -> ExprId {
    let two_nat = d.num(2);
    let one_nat = d.num(1);
    let mul2m = d.mul(two_nat, m);
    let pp = d.succ(mul2m);
    let pi = d.of_nat(pp);
    let one_i = d.ione();
    let _neg_one = d.ineg(one_i);

    let base = super::wilson::neg_one_modeq_p_minus_one(d, pi, pos_pi);
    let bridge = ofnat_pm1_eq_sub_one(d, pp, one_le_pp);
    let pm1_int = d.isub(pi, one_i);
    let pm1_nat = d.sub(pp, one_nat);
    let ofnat_pm1 = d.of_nat(pm1_nat);
    d.int_eq_rewrite(pm1_int, ofnat_pm1, bridge, base, &|d, t| {
        let one_i = d.ione();
        let neg_one = d.ineg(one_i);
        imodeq(d, pi, neg_one, t)
    })
}

// ============================================================================
// `Int.firstSupplementaryLawNotResidue`
// ============================================================================

/// `Int.firstSupplementaryLawNotResidue :
///   ∀ m, (2 ≤ succ (mul 2 m) ∧ ∀ d, d ∣ succ (mul 2 m) → d = 1 ∨ d = succ (mul 2 m)) →
///     Nat.Odd m →
///     Not (IsQuadraticResidue (ofNat (succ (mul 2 m))) (neg one))`
///
/// See the module doc for the route and for why only this half is reachable.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
#[allow(clippy::too_many_lines)]
pub(super) fn declare_first_supplementary_law_not_residue(
    d: &mut IntDev<'_>,
) -> Result<(), KernelError> {
    let p = d.int();
    d.theorem(p.first_supplementary_law_not_residue, 1, &|d, v| {
        let m = v[0];
        let np = d.prelude();
        let one_nat = d.num(1);
        let two_nat = d.num(2);
        let zero_nat = d.zero();
        let mul2m = d.mul(two_nat, m);
        let pp = d.succ(mul2m);
        let pi = d.of_nat(pp);
        let ofnat2m = d.of_nat(mul2m);
        let one_i = d.ione();
        let neg_one = d.ineg(one_i);

        let prime_ty = prime_condition(d, pp);
        let odd_ty = d.const_app(np.odd, &[m]);
        let qr_neg_one = is_quadratic_residue(d, pi, neg_one);
        let concl = d.not(qr_neg_one);

        let stmt = {
            let inner = d.arrow(odd_ty, concl);
            d.arrow(prime_ty, inner)
        };

        let prime_fv = d.fresh_fvar();
        let prime = d.kernel().fvar(prime_fv);
        let odd_fv = d.fresh_fvar();
        let odd = d.kernel().fvar(odd_fv);

        // --- side conditions, all from `Odd m` ------------------------------
        let one_le_m = one_le_of_odd(d, m, odd);
        let two_le_2m = two_le_two_mul(d, m, one_le_m);
        // `Lt 2 pp` is `Le (succ 2) (succ (mul 2 m))`.
        let lt_two_pp = d.lemma(np.succ_le_succ, &[two_nat, mul2m, two_le_2m]);
        // `Lt 0 (mul 2 m)` is `Le 1 (mul 2 m)`, via `1 ≤ 2 ≤ 2*m`.
        let one_le_two = d.lemma(np.le_succ, &[one_nat]);
        let pos_2m = d.lemma(
            np.le_trans,
            &[one_nat, two_nat, mul2m, one_le_two, two_le_2m],
        );
        // `Lt (mul 2 m) pp` is `lt_succ_self` at `mul 2 m`.
        let ub_2m = d.lemma(np.lt_succ_self, &[mul2m]);
        // `Eq Nat (sub pp 1) (add m m)`: `sub (succ X) 1` iota-reduces to `X`.
        let half = two_mul_eq_add_self(d, m);

        // --- `-1`'s natural representative, and its half-power ---------------
        let zero_le_2m = d.lemma(np.zero_le, &[mul2m]);
        let one_le_pp = d.lemma(np.succ_le_succ, &[zero_nat, mul2m, zero_le_2m]);
        let pos_pi = pos_of_nat_succ(d, mul2m);
        let neg_one_to_2m = neg_one_modeq_two_mul(d, m, pos_pi, one_le_pp);
        let two_m_to_neg_one =
            d.const_app(p.mod_eq_symm, &[pi, neg_one, ofnat2m, neg_one_to_2m]);

        // `(2m)^m ≡ (-1)^m [p]`, then `(-1)^m = -1` since `m` is odd.
        let pow_congr = d.const_app(
            p.mod_eq_pow,
            &[pi, ofnat2m, neg_one, m, pos_pi, two_m_to_neg_one],
        );
        let pow_2m = d.ipow(ofnat2m, m);
        let pow_neg_one_m = d.ipow(neg_one, m);
        let sign = d.const_app(p.pow_neg_one_of_odd, &[m, odd]);
        let half_power = d.int_eq_rewrite(pow_neg_one_m, neg_one, sign, pow_congr, &|d, t| {
            imodeq(d, pi, pow_2m, t)
        });

        // --- Euler's criterion's non-residue detector, at `aa := 2m` ---------
        let not_res_2m = d.const_app(
            p.euler_criterion_neg_one_imp_not_residue,
            &[
                pp,
                mul2m,
                m,
                prime,
                lt_two_pp,
                half,
                pos_2m,
                ub_2m,
                half_power,
            ],
        );

        // --- transport the conclusion from `ofNat (2m)` back to `-1` ---------
        let qr_2m = is_quadratic_residue(d, pi, ofnat2m);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let moved = d.const_app(
            p.is_quadratic_residue_of_mod_eq,
            &[pi, neg_one, ofnat2m, neg_one_to_2m, h],
        );
        let _ = qr_2m;
        let contradiction = d.apply(not_res_2m, &[moved]);
        let body = d.lam_fv(h_fv, qr_neg_one, contradiction);

        let with_odd = d.lam_fv(odd_fv, odd_ty, body);
        let proof = d.lam_fv(prime_fv, prime_ty, with_odd);
        (stmt, proof)
    })?;
    Ok(())
}

/// Declare everything in this module.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_first_supplementary_all(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    declare_is_quadratic_residue_of_mod_eq(d)?;
    declare_first_supplementary_law_not_residue(d)
}
