//! Euler's criterion, the necessary (residue ⟹ `≡ 1`) direction, and its
//! contrapositive non-residue detector.
//!
//! `euler.rs` already proves the definition `Int.IsQuadraticResidue` and the
//! UNCONDITIONAL half of Euler's criterion, `euler_criterion_pm_one`: for an
//! odd prime `p` and `0 < a < p`, `a^((p-1)/2) ≡ ±1 [p]`, without deciding
//! which sign holds or relating either sign to residue-hood. This module
//! closes the gap in the direction Fermat's little theorem *can* decide:
//!
//! - [`declare_euler_criterion_residue_imp_one`][]: if `a` is a quadratic
//!   residue mod `p`, its half-power is `≡ 1` (not merely `≡ ±1`).
//! - [`declare_euler_criterion_neg_one_imp_not_residue`][]: contrapositive-ish
//!   corollary — for an ODD prime (`2 < p`), a half-power `≡ -1` rules out
//!   `a` being a residue, since a residue's half-power is forced to be `≡ 1`,
//!   and `1 ≡ -1 [p]` would force `p ∣ 2`, contradicting `p > 2`.
//!
//! ## What this does NOT reach
//!
//! The full biconditional (`a^((p-1)/2) ≡ 1 → a is a residue`) needs a
//! primitive root or a root-counting argument (`x^m - 1` has at most `m`
//! roots mod `p`, and the `m` squares of `1..m` already witness `m` distinct
//! residues, so they must be exactly the roots) — this kernel has no
//! `List`/`Finset`/polynomial machinery to state either, and `euler.rs`'s
//! module doc already records this gap. **So the second supplementary law of
//! quadratic reciprocity — `2` is a residue mod `p` iff `p ≡ ±1 (mod 8)` — is
//! NOT reachable from these two theorems alone.** Even granting the full
//! converse, the remaining piece is a genuinely different argument: evaluating
//! `2^((p-1)/2) mod p` as a function of `p mod 8`, classically done via
//! Gauss's lemma (counting how many of `2, 4, …, 2·(p-1)/2`, reduced to
//! `(-p/2, p/2]`, land negative) — a `Nat.countRange`-shaped argument this
//! prelude does not build. See `docs/plan/status/quadratic-residue-two.md` for
//! the precise handoff.
//!
//! ## Route
//!
//! [`declare_euler_criterion_residue_imp_one`]'s witness `x` (from
//! `IsQuadraticResidue`'s existential, `x*x ≡ a`) need not lie in Fermat's
//! required range `(0, p)`, so it is first reduced to its canonical residue
//! `r := emod x p` ([`reduce_witness_to_residue`], generalizing
//! `euler::reduce_to_canonical_residue` from the fixed target `one` to an
//! arbitrary in-range `a`). Fermat then gives `r^(p-1) ≡ 1`, hence (rewriting
//! the exponent via the caller's `p-1 = m+m` hypothesis) `r^(m+m) ≡ 1`.
//! `Int.ModEq.pow` transports that along `x ≡ r` to `x^(m+m) ≡ 1`. Finally,
//! [`pow_mul_self`] (`(x*x)^m = x^m * x^m`, by induction on `m`, its successor
//! step exactly [`euler::sq_mul_sq_eq_mul_sq`] at `X := x^j`, `Y := x`)
//! combined with `Int.pow_add` (`x^(m+m) = x^m * x^m`) identifies `x^(m+m)`
//! with `(x*x)^m`; `Int.ModEq.pow` along `x*x ≡ a` finally relates that to
//! `a^m`.

use super::euler::{int_exists_elim, is_quadratic_residue, residue_predicate, sq_mul_sq_eq_mul_sq};
use super::ops::IntDev;
use crate::KernelError;
use crate::expr::ExprId;
use crate::nat_prelude::NatOps;

use super::wilson::{
    emod_modeq_self, int_ne_zero_of_pos, nat_prime_pos, pos_of_ne_zero, prime_condition,
};

// ============================================================================
// Shared algebra: `(x*x)^k = x^k * x^k`, by induction on `k`.
// ============================================================================

/// `Eq Int (pow (mul x x) k) (mul (pow x k) (pow x k))`, for a symbolic `k`.
///
/// Induction on `k` (`d.induct`): the base case discharges `pow_zero` twice
/// plus `mul_one`; the successor case reduces — via `pow_succ` on both sides
/// and the induction hypothesis — to exactly
/// [`euler::sq_mul_sq_eq_mul_sq`]`(pow x j, x)`, i.e.
/// `(X*X)*(Y*Y) = (X*Y)*(X*Y)` at `X := pow x j`, `Y := x`.
pub(super) fn pow_mul_self(d: &mut IntDev<'_>, x: ExprId, k: ExprId) -> ExprId {
    let p = d.int();
    let xx = d.imul(x, x);
    let one_i = d.ione();

    let motive = |d: &mut IntDev<'_>, kk: ExprId| -> ExprId {
        let lhs = d.ipow(xx, kk);
        let xk = d.ipow(x, kk);
        let rhs = d.imul(xk, xk);
        d.ieq(lhs, rhs)
    };

    let base = |d: &mut IntDev<'_>| -> ExprId {
        let zero_nat = d.zero();
        let lhs = d.ipow(xx, zero_nat);
        let pow_zero_xx = d.const_app(p.pow_zero, &[xx]); // Eq Int lhs one_i

        let x0 = d.ipow(x, zero_nat);
        let pow_zero_x = d.const_app(p.pow_zero, &[x]); // Eq Int x0 one_i
        let rhs0 = d.imul(x0, x0);
        let mid = d.imul(one_i, x0);
        let step_a = d.icongr(x0, one_i, pow_zero_x, &|d, t| d.imul(t, x0)); // Eq Int rhs0 mid
        let one_one = d.imul(one_i, one_i);
        let step_b = d.icongr(x0, one_i, pow_zero_x, &|d, t| d.imul(one_i, t)); // Eq Int mid one_one
        let mul_one_i_one_i = d.const_app(p.mul_one, &[one_i]); // Eq Int one_one one_i
        let (_, rhs_to_one) = d.ichain(
            rhs0,
            &[(mid, step_a), (one_one, step_b), (one_i, mul_one_i_one_i)],
        );
        let rhs_to_one_rev = d.isymm(rhs0, one_i, rhs_to_one); // Eq Int one_i rhs0

        d.itrans(lhs, one_i, rhs0, pow_zero_xx, rhs_to_one_rev)
    };

    let step = |d: &mut IntDev<'_>, j: ExprId, ih: ExprId| -> ExprId {
        // ih : Eq Int (pow xx j) (mul (pow x j) (pow x j))
        let sj = d.succ(j);
        let pow_xx_sj = d.ipow(xx, sj);
        let pow_xx_j = d.ipow(xx, j);
        let t1 = d.imul(pow_xx_j, xx);
        let p1 = d.const_app(p.pow_succ, &[xx, j]); // Eq Int pow_xx_sj t1

        let pow_x_j = d.ipow(x, j);
        let sq_pow_x_j = d.imul(pow_x_j, pow_x_j);
        let t2 = d.imul(sq_pow_x_j, xx);
        let p2 = d.icongr(pow_xx_j, sq_pow_x_j, ih, &|d, t| d.imul(t, xx)); // Eq Int t1 t2

        // t2 = (X*X)*(Y*Y) with X := pow_x_j, Y := x (xx = mul x x).
        let xy = d.imul(pow_x_j, x);
        let t3 = d.imul(xy, xy);
        let p3 = sq_mul_sq_eq_mul_sq(d, pow_x_j, x); // Eq Int t2 t3

        let pow_x_sj = d.ipow(x, sj);
        let pow_succ_x_j = d.const_app(p.pow_succ, &[x, j]); // Eq Int pow_x_sj xy
        let t4 = d.imul(pow_x_sj, pow_x_sj);
        let mid = d.imul(xy, pow_x_sj);
        let m1 = d.icongr(pow_x_sj, xy, pow_succ_x_j, &|d, t| d.imul(t, pow_x_sj)); // Eq Int t4 mid
        let m2 = d.icongr(pow_x_sj, xy, pow_succ_x_j, &|d, t| d.imul(xy, t)); // Eq Int mid t3
        let t4_to_t3 = d.itrans(t4, mid, t3, m1, m2);
        let p4 = d.isymm(t4, t3, t4_to_t3); // Eq Int t3 t4

        let (_, chain_proof) = d.ichain(pow_xx_sj, &[(t1, p1), (t2, p2), (t3, p3), (t4, p4)]);
        chain_proof
    };

    d.induct(&motive, &base, &step, k)
}

// ============================================================================
// Reduce a residue witness into Fermat's range.
// ============================================================================

/// Given `x : Int` with `sq_modeq_x_a : ModEq p_var (mul x x) big_a` and
/// `0 < aa < pp`, derive `Not (Eq Int x zero)`: a witness whose square is
/// `≡ a mod p` cannot itself be `≡ 0`, else `p ∣ a`, contradicting
/// `0 < a < p` via `Nat.le_of_dvd` + `Nat.lt_irrefl`. The general-`a` sibling
/// of `euler::nonzero_of_sq_modeq_one` (which instead contradicts primality,
/// since it targets `a := one`).
#[allow(clippy::too_many_arguments)]
fn nonzero_of_sq_modeq_a(
    d: &mut IntDev<'_>,
    pp: ExprId,
    p_var: ExprId,
    pos_p: ExprId,
    aa: ExprId,
    big_a: ExprId,
    pos_aa: ExprId,
    ub_aa: ExprId,
    x: ExprId,
    sq_modeq_x_a: ExprId,
) -> ExprId {
    let p = d.int();
    let zero_i = d.izero();

    let h0_fv = d.fresh_fvar();
    let h0 = d.kernel().fvar(h0_fv);
    let eq_ty = d.ieq(x, zero_i);

    let xx = d.imul(x, x);
    let zero_zero = d.imul(zero_i, zero_i);
    let congr_xx = d.icongr(x, zero_i, h0, &|d, t| d.imul(t, t));
    let mul_zero_pf = d.const_app(p.mul_zero, &[zero_i]);
    let (_, xx_eq_zero) = d.ichain(xx, &[(zero_zero, congr_xx), (zero_i, mul_zero_pf)]);

    let modeq_zero_a_ty = super::modeq::imodeq(d, p_var, zero_i, big_a);
    let modeq_zero_a = d.int_eq_rewrite(xx, zero_i, xx_eq_zero, sq_modeq_x_a, &|d, t| {
        super::modeq::imodeq(d, p_var, t, big_a)
    });

    let dvd_a_ty = super::dvd::idvd(d, p_var, big_a);
    let iff_ty = d.const_app(p.mod_eq_iff_dvd, &[p_var, zero_i, big_a, pos_p]);
    let mp = d.const_app(p.logic.iff_mp, &[modeq_zero_a_ty, dvd_a_ty, iff_ty]);
    let dvd_a = d.apply(mp, &[modeq_zero_a]);

    let nat_dvd_a = d.const_app(p.nat_abs_dvd_nat_abs_of_dvd, &[p_var, big_a, dvd_a]);
    let le_pp_aa = d.lemma(p.nat.le_of_dvd, &[pp, aa, pos_aa, nat_dvd_a]);
    let lt_aa_aa = d.lemma(p.nat.lt_of_lt_of_le, &[aa, pp, aa, ub_aa, le_pp_aa]);
    let false_pf = d.lemma(p.nat.lt_irrefl, &[aa, lt_aa_aa]);

    d.lam_fv(h0_fv, eq_ty, false_pf)
}

/// Reduce a quadratic-residue witness `x` (`sq_modeq_x_a : ModEq p_var (x*x)
/// big_a`) to its canonical residue `r := emod x p_var`, in Fermat's range.
///
/// Returns `(r, mag, mag_pos, mag_lt_pp, sq_modeq_r_a, modeq_x_r, bridge)`
/// where `mag := natAbs r`, `mag_pos : 0 < mag`, `mag_lt_pp : mag < pp`,
/// `sq_modeq_r_a : ModEq p_var (r*r) big_a`, `modeq_x_r : ModEq p_var x r`,
/// and `bridge : Eq Int (ofNat mag) r`.
///
/// Mirrors `euler::reduce_to_canonical_residue`, generalized from the fixed
/// target `one` to an arbitrary in-range `aa` (the nonzero step goes through
/// [`nonzero_of_sq_modeq_a`] rather than a primality contradiction), and
/// omits the `p-1` upper-bound machinery that function needs for
/// `self_inverse_mod_prime`: Fermat only needs `0 < mag < pp`.
#[allow(clippy::too_many_arguments)]
fn reduce_witness_to_residue(
    d: &mut IntDev<'_>,
    pp: ExprId,
    p_var: ExprId,
    pos_p: ExprId,
    aa: ExprId,
    big_a: ExprId,
    pos_aa: ExprId,
    ub_aa: ExprId,
    x: ExprId,
    sq_modeq_x_a: ExprId,
) -> (ExprId, ExprId, ExprId, ExprId, ExprId, ExprId, ExprId) {
    let p = d.int();
    let r = d.iemod(x, p_var);
    let mag = d.const_app(p.nat_abs, &[r]);
    let ne_p = int_ne_zero_of_pos(d, p_var, pos_p);
    let r_nonneg = d.const_app(p.emod_nonneg, &[x, p_var, ne_p]);
    let r_lt = d.const_app(p.emod_lt_of_pos, &[x, p_var, pos_p]);
    let bridge = d.const_app(p.of_nat_nat_abs_of_nonneg, &[r, r_nonneg]); // Eq Int (ofNat mag) r
    let ofnat_mag = d.of_nat(mag);
    let bridge_rev = d.isymm(ofnat_mag, r, bridge); // Eq Int r ofnat_mag

    let modeq_x_r = emod_modeq_self(d, x, p_var, pos_p); // ModEq p_var x r
    let modeq_r_x = d.const_app(p.mod_eq_symm, &[p_var, x, r, modeq_x_r]);
    let rr_modeq_xx = d.const_app(
        p.mod_eq_mul,
        &[p_var, r, x, r, x, pos_p, modeq_r_x, modeq_r_x],
    );
    let rr = d.imul(r, r);
    let xx = d.imul(x, x);
    let sq_modeq_r_a = d.const_app(
        p.mod_eq_trans,
        &[p_var, rr, xx, big_a, rr_modeq_xx, sq_modeq_x_a],
    );

    // mag < pp
    let mag_lt_pp = d.int_eq_rewrite(r, ofnat_mag, bridge_rev, r_lt, &|d, t| d.ilt(t, p_var));

    // mag ≠ 0
    let x_ne_zero = nonzero_of_sq_modeq_a(
        d,
        pp,
        p_var,
        pos_p,
        aa,
        big_a,
        pos_aa,
        ub_aa,
        r,
        sq_modeq_r_a,
    );
    let mag_ne_zero_nat = {
        let h0_fv = d.fresh_fvar();
        let h0 = d.kernel().fvar(h0_fv);
        let zero_nat = d.zero();
        let eq_ty = d.eq(mag, zero_nat);
        let zero_i = d.izero();
        let congr0 = d.nat_eq_to_int(mag, zero_nat, h0, &|d, y| d.of_nat(y)); // Eq Int ofnat_mag zero_i
        let r_eq_zero = d.itrans(r, ofnat_mag, zero_i, bridge_rev, congr0);
        let false_pf = d.apply(x_ne_zero, &[r_eq_zero]);
        d.lam_fv(h0_fv, eq_ty, false_pf)
    };
    let mag_pos = pos_of_ne_zero(d, mag, mag_ne_zero_nat);

    (r, mag, mag_pos, mag_lt_pp, sq_modeq_r_a, modeq_x_r, bridge)
}

// ============================================================================
// `Int.euler_criterion_residue_imp_one`
// ============================================================================

/// `Int.euler_criterion_residue_imp_one :
/// ∀ pp aa m, (2 ≤ pp ∧ ∀ d, d ∣ pp → d = 1 ∨ d = pp) →
///   Eq Nat (pp-1) (m+m) → 0 < aa → aa < pp →
///   IsQuadraticResidue (ofNat pp) (ofNat aa) →
///   ModEq (ofNat pp) (pow (ofNat aa) m) one`
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
#[allow(clippy::too_many_lines)]
pub(super) fn declare_euler_criterion_residue_imp_one(
    d: &mut IntDev<'_>,
) -> Result<(), KernelError> {
    let p = d.int();
    d.theorem(p.euler_criterion_residue_imp_one, 3, &|d, v| {
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
        let qr_ty = is_quadratic_residue(d, big_p, big_a);
        let one_i = d.ione();
        let am = d.ipow(big_a, m);
        let concl = super::modeq::imodeq(d, big_p, am, one_i);

        let stmt = {
            let inner = d.arrow(qr_ty, concl);
            let with_ub = d.arrow(ub_ty, inner);
            let with_pos = d.arrow(pos_ty, with_ub);
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
        let qr_fv = d.fresh_fvar();
        let qr_proof = d.kernel().fvar(qr_fv);

        let pos_p = nat_prime_pos(d, pp, prime_proof);

        let pred = residue_predicate(d, big_p, big_a);
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let hx_fv = d.fresh_fvar();
        let hx = d.kernel().fvar(hx_fv);
        let xx_for_hx = d.imul(x, x);
        let hx_ty = super::modeq::imodeq(d, big_p, xx_for_hx, big_a);

        // --- body given (x, hx) ------------------------------------------
        let (r, mag, mag_pos, mag_lt_pp, _sq_modeq_r_a, modeq_x_r, bridge) =
            reduce_witness_to_residue(d, pp, big_p, pos_p, aa, big_a, pos_proof, ub_proof, x, hx);

        // Fermat on r's magnitude, transported to r.
        let fermat_mag = d.const_app(
            p.pow_prime_sub_one_modeq_one,
            &[pp, mag, prime_proof, mag_pos, mag_lt_pp],
        ); // ModEq big_p (pow (ofNat mag) pm1) one_i
        let ofnat_mag = d.of_nat(mag);
        let pow_pm1_r = d.ipow(r, pm1);
        let fermat_r = d.int_eq_rewrite(ofnat_mag, r, bridge, fermat_mag, &|d, t| {
            let pt = d.ipow(t, pm1);
            super::modeq::imodeq(d, big_p, pt, one_i)
        }); // ModEq big_p (pow r pm1) one_i

        // Rewrite exponent pm1 -> m+m.
        let pow_mm_r = d.ipow(r, mm);
        let congr_exp = d.nat_eq_to_int(pm1, mm, half_proof, &|d, t| d.ipow(r, t));
        let fermat_r_mm = d.int_eq_rewrite(pow_pm1_r, pow_mm_r, congr_exp, fermat_r, &|d, t| {
            super::modeq::imodeq(d, big_p, t, one_i)
        }); // ModEq big_p (pow r mm) one_i

        // Transport along x ≡ r (same exponent mm on both sides).
        let pow_mm_x = d.ipow(x, mm);
        let modeq_pow_x_r_mm = d.const_app(p.mod_eq_pow, &[big_p, x, r, mm, pos_p, modeq_x_r]);
        let modeq_x_mm_one = d.const_app(
            p.mod_eq_trans,
            &[
                big_p,
                pow_mm_x,
                pow_mm_r,
                one_i,
                modeq_pow_x_r_mm,
                fermat_r_mm,
            ],
        ); // ModEq big_p (pow x mm) one_i

        // Identify pow x mm with pow (x*x) m via pow_add and pow_mul_self.
        let pow_add_x = d.const_app(p.pow_add, &[x, m, m]); // Eq Int pow_mm_x (mul (pow x m)(pow x m))
        let xm = d.ipow(x, m);
        let prod_xm = d.imul(xm, xm);
        let xx = d.imul(x, x);
        let pow_xx_m = d.ipow(xx, m);
        let pms = pow_mul_self(d, x, m); // Eq Int pow_xx_m prod_xm
        let pms_rev = d.isymm(pow_xx_m, prod_xm, pms); // Eq Int prod_xm pow_xx_m
        let eq_powxmm_powxxm = d.itrans(pow_mm_x, prod_xm, pow_xx_m, pow_add_x, pms_rev);

        let modeq_xx_m_one = d.int_eq_rewrite(
            pow_mm_x,
            pow_xx_m,
            eq_powxmm_powxxm,
            modeq_x_mm_one,
            &|d, t| super::modeq::imodeq(d, big_p, t, one_i),
        ); // ModEq big_p (pow xx m) one_i

        // Transport along x*x ≡ a (same exponent m on both sides).
        let modeq_pow_xx_a_m = d.const_app(p.mod_eq_pow, &[big_p, xx, big_a, m, pos_p, hx]);
        let symm_modeq = d.const_app(p.mod_eq_symm, &[big_p, pow_xx_m, am, modeq_pow_xx_a_m]);
        let result = d.const_app(
            p.mod_eq_trans,
            &[big_p, am, pow_xx_m, one_i, symm_modeq, modeq_xx_m_one],
        ); // ModEq big_p am one_i, i.e. `concl`

        let minor = {
            let inner = d.lam_fv(hx_fv, hx_ty, result);
            d.lam_fv(x_fv, d.int_ty(), inner)
        };
        let eliminated = int_exists_elim(d, pred, concl, qr_proof, minor);

        let with_qr = d.lam_fv(qr_fv, qr_ty, eliminated);
        let with_ub = d.lam_fv(ub_fv, ub_ty, with_qr);
        let with_pos = d.lam_fv(pos_fv, pos_ty, with_ub);
        let with_half = d.lam_fv(half_fv, half_ty, with_pos);
        let proof = d.lam_fv(prime_fv, prime_ty, with_half);
        (stmt, proof)
    })?;
    Ok(())
}

// ============================================================================
// `Int.euler_criterion_neg_one_imp_not_residue`
// ============================================================================

/// `Int.euler_criterion_neg_one_imp_not_residue :
/// ∀ pp aa m, (2 ≤ pp ∧ ∀ d, d ∣ pp → d = 1 ∨ d = pp) → Lt 2 pp →
///   Eq Nat (pp-1) (m+m) → 0 < aa → aa < pp →
///   ModEq (ofNat pp) (pow (ofNat aa) m) (neg one) →
///   Not (IsQuadraticResidue (ofNat pp) (ofNat aa))`
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
#[allow(clippy::too_many_lines)]
pub(super) fn declare_euler_criterion_neg_one_imp_not_residue(
    d: &mut IntDev<'_>,
) -> Result<(), KernelError> {
    let p = d.int();
    d.theorem(p.euler_criterion_neg_one_imp_not_residue, 3, &|d, v| {
        let (pp, aa, m) = (v[0], v[1], v[2]);
        let prime_ty = prime_condition(d, pp);
        let one_nat = d.num(1);
        let two_nat = d.succ(one_nat);
        let odd_ty = d.lt(two_nat, pp);
        let pm1 = d.sub(pp, one_nat);
        let mm = d.add(m, m);
        let half_ty = d.eq(pm1, mm);
        let zero = d.zero();
        let pos_ty = d.lt(zero, aa);
        let ub_ty = d.lt(aa, pp);

        let big_p = d.of_nat(pp);
        let big_a = d.of_nat(aa);
        let one_i = d.ione();
        let neg_one = d.ineg(one_i);
        let am = d.ipow(big_a, m);
        let hyp_ty = super::modeq::imodeq(d, big_p, am, neg_one);
        let qr_ty = is_quadratic_residue(d, big_p, big_a);
        let not_qr_ty = d.not(qr_ty);

        let stmt = {
            let inner = d.arrow(hyp_ty, not_qr_ty);
            let with_ub = d.arrow(ub_ty, inner);
            let with_pos = d.arrow(pos_ty, with_ub);
            let with_half = d.arrow(half_ty, with_pos);
            let with_odd = d.arrow(odd_ty, with_half);
            d.arrow(prime_ty, with_odd)
        };

        let prime_fv = d.fresh_fvar();
        let prime_proof = d.kernel().fvar(prime_fv);
        let odd_fv = d.fresh_fvar();
        let odd_proof = d.kernel().fvar(odd_fv);
        let half_fv = d.fresh_fvar();
        let half_proof = d.kernel().fvar(half_fv);
        let pos_fv = d.fresh_fvar();
        let pos_proof = d.kernel().fvar(pos_fv);
        let ub_fv = d.fresh_fvar();
        let ub_proof = d.kernel().fvar(ub_fv);
        let hyp_fv = d.fresh_fvar();
        let hyp_proof = d.kernel().fvar(hyp_fv);
        let qr_fv = d.fresh_fvar();
        let qr_proof = d.kernel().fvar(qr_fv);

        // Under qr_proof: theorem 1 gives am ≡ one; combined with hyp_proof
        // (am ≡ neg_one) gives one ≡ neg_one.
        let forward = d.const_app(
            p.euler_criterion_residue_imp_one,
            &[
                pp,
                aa,
                m,
                prime_proof,
                half_proof,
                pos_proof,
                ub_proof,
                qr_proof,
            ],
        ); // ModEq big_p am one_i
        let symm_forward = d.const_app(p.mod_eq_symm, &[big_p, am, one_i, forward]); // ModEq big_p one_i am
        let modeq_one_negone_ty = super::modeq::imodeq(d, big_p, one_i, neg_one);
        let modeq_one_negone = d.const_app(
            p.mod_eq_trans,
            &[big_p, one_i, am, neg_one, symm_forward, hyp_proof],
        ); // ModEq big_p one_i neg_one

        let pos_p = nat_prime_pos(d, pp, prime_proof);

        // p_var ∣ (neg_one - one_i), which reduces to -2; natAbs gives p ∣ 2.
        let sub_ty = d.isub(neg_one, one_i);
        let dvd_sub_ty = super::dvd::idvd(d, big_p, sub_ty);
        let iff_ty = d.const_app(p.mod_eq_iff_dvd, &[big_p, one_i, neg_one, pos_p]);
        let mp = d.const_app(p.logic.iff_mp, &[modeq_one_negone_ty, dvd_sub_ty, iff_ty]);
        let dvd_sub = d.apply(mp, &[modeq_one_negone]);

        let nat_dvd_2 = d.const_app(p.nat_abs_dvd_nat_abs_of_dvd, &[big_p, sub_ty, dvd_sub]);
        let pos_2 = d.lemma(p.nat.zero_lt_succ, &[one_nat]); // Lt 0 two_nat
        let le_pp_2 = d.lemma(p.nat.le_of_dvd, &[pp, two_nat, pos_2, nat_dvd_2]);
        let lt_2_2 = d.lemma(
            p.nat.lt_of_lt_of_le,
            &[two_nat, pp, two_nat, odd_proof, le_pp_2],
        );
        let false_pf = d.lemma(p.nat.lt_irrefl, &[two_nat, lt_2_2]);

        let body = d.lam_fv(qr_fv, qr_ty, false_pf);
        let with_hyp = d.lam_fv(hyp_fv, hyp_ty, body);
        let with_ub = d.lam_fv(ub_fv, ub_ty, with_hyp);
        let with_pos = d.lam_fv(pos_fv, pos_ty, with_ub);
        let with_half = d.lam_fv(half_fv, half_ty, with_pos);
        let with_odd = d.lam_fv(odd_fv, odd_ty, with_half);
        let proof = d.lam_fv(prime_fv, prime_ty, with_odd);
        (stmt, proof)
    })?;
    Ok(())
}
