//! `Nat.Coprime.mul_add_mul_ne_mul : ∀ m n a b, Coprime m n → a ≠ 0 → b ≠ 0
//! → a*m + b*n ≠ m*n` -- an `ml430` mirror
//! (`F:ml430-nat-coprime-mul-add-mul-ne-mul-51b56f70`).
//!
//! Genuinely needs the `m = 0` / `n = 0` degenerate cases split out: at
//! `m = 0` the hypothesis forces `n = 1` (`Coprime 0 n` unfolds to `n = 1`
//! via `gcd_zero_left`), and the equation collapses to `mul b n = 0`, i.e.
//! `b = 0` -- contradicting `b ≠ 0` -- with no use of `a`'s hypothesis or
//! `n`'s value beyond `1`. The `n = 0` case is symmetric and even more
//! direct (`add`/`mul` by the literal `0` on the right are pure `δ/ι`, so
//! the equation reduces to `mul a m = 0` with no rewrite at all). Both are
//! split via [`super::ops::cases_zero_succ`], with the outer hypotheses
//! folded into the per-branch motive (that helper's own doc explains why:
//! nothing specializes an outer hypothesis into a branch automatically).
//!
//! The `m, n ≥ 1` (`succ`-shaped) case is the real content, Gauss's lemma
//! run in both directions:
//!
//! - `m ∣ m*n` (`dvd_mul`) and `m ∣ a*m` (`dvd_mul_left`) combine via
//!   `dvd_add_iff_right` (transported along the assumed equation) to `m ∣
//!   b*n`; `gauss_lemma` (needing `b*n` commuted to `n*b`) gives `m ∣ b`;
//!   `le_of_dvd` (needing `b ≠ 0` promoted to `1 ≤ b` via
//!   `zero_lt_of_ne_zero`) gives `m ≤ b`.
//! - Symmetrically, `n ∣ m*n` (`dvd_mul_left`) and `n ∣ b*n` (`dvd_mul_left`
//!   again) combine via `dvd_add_iff_left` to `n ∣ a*m`; `gauss_lemma` at
//!   the SYMMETRIC coprimality (`coprime_symmetric`) gives `n ∣ a`;
//!   `le_of_dvd` gives `n ≤ a`.
//! - Writing `X := m*n`: `m ≤ b` and `n ≤ a` lift (via `mul_le_mul_left`,
//!   twice, each needing one `mul_comm` to land on the right operand order)
//!   to `X ≤ a*m` and `X ≤ b*n`, combined (`add_le_add_left`/`_right`,
//!   `le_trans`) into `X + X ≤ a*m + b*n`, which the assumed equation
//!   transports to `X + X ≤ X`. Since `X ≥ 1` (`one_le_mul` from `m, n ≥
//!   1`), `add_le_add_left` gives `X + 1 ≤ X + X` -- defeq `succ X ≤ X + X`
//!   -- and `le_trans` closes on `succ X ≤ X`, i.e. `Lt X X`, refuted by
//!   `lt_irrefl`.

use super::NatPrelude;
use super::ops::{NatDev, NatOps, cases_zero_succ};
use crate::KernelError;
use crate::expr::ExprId;

/// `Nat.Coprime.mul_add_mul_ne_mul`. See the module doc.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_coprime_mul_add_mul_ne_mul(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.coprime_mul_add_mul_ne_mul, 4, &|d, v| {
        let (m, n, a, b) = (v[0], v[1], v[2], v[3]);
        let false_ty = d.kernel().const_(p.logic.false_, vec![]);

        // `fun mv => Coprime mv n -> a<>0 -> b<>0 -> (a*mv+b*n = mv*n -> False)`.
        let goal_at_m = |d: &mut NatDev<'_>, mv: ExprId| -> ExprId {
            let g = d.gcd(mv, n);
            let one = d.num(1);
            let cop_ty = d.eq(g, one);

            let zero = d.zero();
            let a_eq0 = d.eq(a, zero);
            let ane_ty = d.arrow(a_eq0, false_ty);
            let b_eq0 = d.eq(b, zero);
            let bne_ty = d.arrow(b_eq0, false_ty);

            let am = d.mul(a, mv);
            let bn = d.mul(b, n);
            let sum = d.add(am, bn);
            let mvn = d.mul(mv, n);
            let heq_ty = d.eq(sum, mvn);
            let not_ty = d.arrow(heq_ty, false_ty);

            let inner = d.arrow(bne_ty, not_ty);
            let inner2 = d.arrow(ane_ty, inner);
            d.arrow(cop_ty, inner2)
        };

        let at_m_zero = |d: &mut NatDev<'_>| -> ExprId {
            let zero = d.zero();
            let g0 = d.gcd(zero, n);
            let one = d.num(1);
            let cop_ty = d.eq(g0, one);
            let cop_fv = d.fresh_fvar();
            let cop = d.kernel().fvar(cop_fv);

            let a_eq0 = d.eq(a, zero);
            let ane_ty = d.arrow(a_eq0, false_ty);
            let ane_fv = d.fresh_fvar();
            let _ane = d.kernel().fvar(ane_fv);

            let b_eq0 = d.eq(b, zero);
            let bne_ty = d.arrow(b_eq0, false_ty);
            let bne_fv = d.fresh_fvar();
            let bne = d.kernel().fvar(bne_fv);

            let a0 = d.mul(a, zero);
            let bn = d.mul(b, n);
            let sum = d.add(a0, bn);
            let mul0n = d.mul(zero, n);
            let heq_ty = d.eq(sum, mul0n);
            let heq_fv = d.fresh_fvar();
            let heq = d.kernel().fvar(heq_fv);

            // n = 1, from `Coprime 0 n` (= gcd 0 n = 1) and `gcd_zero_left`.
            let gzl = d.lemma(p.gcd_zero_left, &[n]); // Eq(gcd 0 n, n)
            let n_eq_g0 = d.symm(g0, n, gzl); // Eq(n, gcd 0 n)
            let n_eq_1 = d.trans(n, g0, one, n_eq_g0, cop); // Eq(n, 1)

            // mul b n = 0: chain from `heq` (whose LHS is defeq to
            // `add(0, mul b n)` since `mul a 0 ≡ 0`) via `zero_add`/`zero_mul`.
            let zero_add_bn = d.lemma(p.zero_add, &[bn]); // Eq(add(0,bn), bn)
            let zero_bn = d.add(zero, bn);
            let bn_eq_zero_bn = d.symm(zero_bn, bn, zero_add_bn); // Eq(bn, add(0,bn))
            let zm = d.lemma(p.zero_mul, &[n]); // Eq(mul 0 n, 0)
            let (_, bn_eq_zero) =
                d.chain(bn, &[(zero_bn, bn_eq_zero_bn), (mul0n, heq), (zero, zm)]);

            // Substitute n = 1: mul b n = mul b 1.
            let b1 = d.mul(b, one);
            let congr_bn_b1 = d.congr(n, one, n_eq_1, &|d, x| d.mul(b, x));
            let b1_eq_bn = d.symm(bn, b1, congr_bn_b1);
            let b1_eq_zero = d.trans(b1, bn, zero, b1_eq_bn, bn_eq_zero);

            let mo = d.lemma(p.mul_one, &[b]); // Eq(mul b 1, b)
            let b_eq_b1 = d.symm(b1, b, mo);
            let b_eq_zero = d.trans(b, b1, zero, b_eq_b1, b1_eq_zero);

            let contra = d.apply(bne, &[b_eq_zero]);

            let with_heq = d.lam_fv(heq_fv, heq_ty, contra);
            let with_bne = d.lam_fv(bne_fv, bne_ty, with_heq);
            let with_ane = d.lam_fv(ane_fv, ane_ty, with_bne);
            d.lam_fv(cop_fv, cop_ty, with_ane)
        };

        let at_m_succ = |d: &mut NatDev<'_>, m_pred: ExprId| -> ExprId {
            let sm = d.succ(m_pred);

            // `fun nv => Coprime sm nv -> a<>0 -> b<>0 -> (a*sm+b*nv = sm*nv -> False)`.
            let goal_at_n = |d: &mut NatDev<'_>, nv: ExprId| -> ExprId {
                let g = d.gcd(sm, nv);
                let one = d.num(1);
                let cop_ty = d.eq(g, one);
                let zero = d.zero();
                let a_eq0 = d.eq(a, zero);
                let ane_ty = d.arrow(a_eq0, false_ty);
                let b_eq0 = d.eq(b, zero);
                let bne_ty = d.arrow(b_eq0, false_ty);
                let asm = d.mul(a, sm);
                let bnv = d.mul(b, nv);
                let sum = d.add(asm, bnv);
                let smnv = d.mul(sm, nv);
                let heq_ty = d.eq(sum, smnv);
                let not_ty = d.arrow(heq_ty, false_ty);
                let inner = d.arrow(bne_ty, not_ty);
                let inner2 = d.arrow(ane_ty, inner);
                d.arrow(cop_ty, inner2)
            };

            let at_n_zero = |d: &mut NatDev<'_>| -> ExprId {
                let zero = d.zero();
                let g0 = d.gcd(sm, zero);
                let one = d.num(1);
                let cop_ty = d.eq(g0, one);
                let cop_fv = d.fresh_fvar();
                let cop = d.kernel().fvar(cop_fv);

                let a_eq0 = d.eq(a, zero);
                let ane_ty = d.arrow(a_eq0, false_ty);
                let ane_fv = d.fresh_fvar();
                let ane = d.kernel().fvar(ane_fv);

                let b_eq0 = d.eq(b, zero);
                let bne_ty = d.arrow(b_eq0, false_ty);
                let bne_fv = d.fresh_fvar();
                let _bne = d.kernel().fvar(bne_fv);

                let asm = d.mul(a, sm);
                let b0 = d.mul(b, zero);
                let sum = d.add(asm, b0);
                let sm0 = d.mul(sm, zero);
                let heq_ty = d.eq(sum, sm0);
                let heq_fv = d.fresh_fvar();
                let heq = d.kernel().fvar(heq_fv);

                // sm = 1, from `Coprime sm 0` and `gcd_comm`/`gcd_zero_left`.
                let gc = d.lemma(p.gcd_comm, &[sm, zero]); // Eq(gcd sm 0, gcd 0 sm)
                let g0sm = d.gcd(zero, sm);
                let gzl = d.lemma(p.gcd_zero_left, &[sm]); // Eq(gcd 0 sm, sm)
                let g0_eq_sm = d.trans(g0, g0sm, sm, gc, gzl); // Eq(gcd sm 0, sm)
                let sm_eq_g0 = d.symm(g0, sm, g0_eq_sm); // Eq(sm, gcd sm 0)
                let sm_eq_1 = d.trans(sm, g0, one, sm_eq_g0, cop); // Eq(sm, 1)

                // `heq`'s type is defeq to `Eq(mul a sm, 0)`: `mul b 0 ≡ 0`
                // and `add(X,0) ≡ X` are both pure `δ/ι` (right-zero base
                // cases), so no rewrite is needed to see it that way.
                let a1 = d.mul(a, one);
                let congr_asm_a1 = d.congr(sm, one, sm_eq_1, &|d, x| d.mul(a, x));
                let a1_eq_asm = d.symm(asm, a1, congr_asm_a1);
                let a1_eq_zero = d.trans(a1, asm, zero, a1_eq_asm, heq);

                let mo = d.lemma(p.mul_one, &[a]); // Eq(mul a 1, a)
                let a_eq_a1 = d.symm(a1, a, mo);
                let a_eq_zero = d.trans(a, a1, zero, a_eq_a1, a1_eq_zero);

                let contra = d.apply(ane, &[a_eq_zero]);

                let with_heq = d.lam_fv(heq_fv, heq_ty, contra);
                let with_bne = d.lam_fv(bne_fv, bne_ty, with_heq);
                let with_ane = d.lam_fv(ane_fv, ane_ty, with_bne);
                d.lam_fv(cop_fv, cop_ty, with_ane)
            };

            let at_n_succ = |d: &mut NatDev<'_>, n_pred: ExprId| -> ExprId {
                let sn = d.succ(n_pred);
                let g = d.gcd(sm, sn);
                let one = d.num(1);
                let cop_ty = d.eq(g, one);
                let cop_fv = d.fresh_fvar();
                let cop = d.kernel().fvar(cop_fv);

                let zero = d.zero();
                let a_eq0 = d.eq(a, zero);
                let ane_ty = d.arrow(a_eq0, false_ty);
                let ane_fv = d.fresh_fvar();
                let ane = d.kernel().fvar(ane_fv);

                let b_eq0 = d.eq(b, zero);
                let bne_ty = d.arrow(b_eq0, false_ty);
                let bne_fv = d.fresh_fvar();
                let bne = d.kernel().fvar(bne_fv);

                let asm = d.mul(a, sm);
                let bsn = d.mul(b, sn);
                let sum = d.add(asm, bsn);
                let x = d.mul(sm, sn);
                let heq_ty = d.eq(sum, x);
                let heq_fv = d.fresh_fvar();
                let heq = d.kernel().fvar(heq_fv);

                let m_pos = d.zero_lt_succ(m_pred); // Le 1 sm
                let n_pos = d.zero_lt_succ(n_pred); // Le 1 sn
                let a_pos = d.lemma(p.zero_lt_of_ne_zero, &[a, ane]); // Le 1 a
                let b_pos = d.lemma(p.zero_lt_of_ne_zero, &[b, bne]); // Le 1 b

                // --- m | b, via Gauss's lemma. ---------------------------
                let dvd_sm_x = d.lemma(p.dvd_mul, &[sm, sn]); // dvd sm (sm*sn) = dvd sm x
                let x_eq_sum = d.symm(sum, x, heq); // Eq(x, sum)
                let motive_x = d.eq_motive(x, &|d, t| d.dvd(sm, t));
                let dvd_sm_sum = d.transport(x, motive_x, dvd_sm_x, sum, x_eq_sum); // dvd sm sum

                let dvd_sm_asm = d.lemma(p.dvd_mul_left, &[sm, a]); // dvd sm (mul a sm) = dvd sm asm
                let iff_r = d.lemma(p.dvd_add_iff_right, &[sm, asm, bsn, dvd_sm_asm]);
                // iff_r : Iff (dvd sm bsn) (dvd sm sum)
                let dvd_sm_bsn = {
                    let dvd_bsn_ty = d.dvd(sm, bsn);
                    let dvd_sm_sum_ty = d.dvd(sm, sum);
                    let mpr = d.const_app(p.logic.iff_mpr, &[dvd_bsn_ty, dvd_sm_sum_ty, iff_r]);
                    d.apply(mpr, &[dvd_sm_sum])
                };

                let nb = d.mul(sn, b);
                let comm_bn = d.lemma(p.mul_comm, &[b, sn]); // Eq(bsn, nb)
                let motive_dvd = d.eq_motive(bsn, &|d, t| d.dvd(sm, t));
                let dvd_sm_nb = d.transport(bsn, motive_dvd, dvd_sm_bsn, nb, comm_bn);

                let dvd_sm_b = d.lemma(p.gauss_lemma, &[sm, sn, b, cop, dvd_sm_nb]); // dvd sm b
                let h_b_ge_sm = d.lemma(p.le_of_dvd, &[sm, b, b_pos, dvd_sm_b]); // Le sm b

                // --- n | a, via Gauss's lemma (symmetric coprimality). ---
                let cop_sym = d.lemma(p.coprime_symmetric, &[sm, sn, cop]); // Eq(gcd sn sm, 1)

                let dvd_sn_x = d.lemma(p.dvd_mul_left, &[sn, sm]); // dvd sn (mul sm sn) = dvd sn x
                let motive_x_sn = d.eq_motive(x, &|d, t| d.dvd(sn, t));
                let dvd_sn_sum = d.transport(x, motive_x_sn, dvd_sn_x, sum, x_eq_sum);

                let dvd_sn_bsn = d.lemma(p.dvd_mul_left, &[sn, b]); // dvd sn (mul b sn) = dvd sn bsn
                let iff_l = d.lemma(p.dvd_add_iff_left, &[sn, asm, bsn, dvd_sn_bsn]);
                // iff_l : Iff (dvd sn asm) (dvd sn sum)
                let dvd_sn_asm = {
                    let dvd_asm_ty = d.dvd(sn, asm);
                    let dvd_sn_sum_ty = d.dvd(sn, sum);
                    let mpr = d.const_app(p.logic.iff_mpr, &[dvd_asm_ty, dvd_sn_sum_ty, iff_l]);
                    d.apply(mpr, &[dvd_sn_sum])
                };

                let ma = d.mul(sm, a);
                let comm_am = d.lemma(p.mul_comm, &[a, sm]); // Eq(asm, ma)
                let motive_dvd2 = d.eq_motive(asm, &|d, t| d.dvd(sn, t));
                let dvd_sn_ma = d.transport(asm, motive_dvd2, dvd_sn_asm, ma, comm_am);

                let dvd_sn_a = d.lemma(p.gauss_lemma, &[sn, sm, a, cop_sym, dvd_sn_ma]); // dvd sn a
                let h_a_ge_sn = d.lemma(p.le_of_dvd, &[sn, a, a_pos, dvd_sn_a]); // Le sn a

                // --- Arithmetic contradiction. ----------------------------
                // L1' : Le x asm.
                let l1 = d.lemma(p.mul_le_mul_left, &[sm, sn, a, h_a_ge_sn]); // Le(x, mul sm a)
                let sma = d.mul(sm, a);
                let comm_sma = d.lemma(p.mul_comm, &[sm, a]); // Eq(sma, asm)
                let motive_l1 = d.eq_motive(sma, &|d, t| d.le(x, t));
                let l1p = d.transport(sma, motive_l1, l1, asm, comm_sma); // Le(x, asm)

                // L2 : Le x bsn.
                let l2raw = d.lemma(p.mul_le_mul_left, &[sn, sm, b, h_b_ge_sm]); // Le(mul sn sm, mul sn b)
                let nsm = d.mul(sn, sm);
                let comm_nsm = d.lemma(p.mul_comm, &[sn, sm]); // Eq(nsm, x)
                let sn_b = d.mul(sn, b);
                let motive_l2a = d.eq_motive(nsm, &|d, t| d.le(t, sn_b));
                let l2mid = d.transport(nsm, motive_l2a, l2raw, x, comm_nsm); // Le(x, mul sn b)
                let nbv = d.mul(sn, b);
                let comm_nb = d.lemma(p.mul_comm, &[sn, b]); // Eq(nbv, bsn)
                let motive_l2b = d.eq_motive(nbv, &|d, t| d.le(x, t));
                let l2 = d.transport(nbv, motive_l2b, l2mid, bsn, comm_nb); // Le(x, bsn)

                // Le(add(x,x), add(asm,x))
                let step_a = d.lemma(p.add_le_add_right, &[x, x, asm, l1p]);
                // Le(add(asm,x), add(asm,bsn)) = Le(add(asm,x), sum)
                let step_b = d.lemma(p.add_le_add_left, &[asm, x, bsn, l2]);
                let xx = d.add(x, x);
                let asm_x = d.add(asm, x);
                let combined = d.lemma(p.le_trans, &[xx, asm_x, sum, step_a, step_b]); // Le(xx, sum)

                let motive_final = d.eq_motive(sum, &|d, t| d.le(xx, t));
                let final_le = d.transport(sum, motive_final, combined, x, heq); // Le(xx, x)

                let x_pos = d.lemma(p.one_le_mul, &[sm, sn, m_pos, n_pos]); // Le 1 x
                let growth = d.lemma(p.add_le_add_left, &[x, one, x, x_pos]); // Le(add(x,1), xx)
                let succ_x = d.succ(x);
                let chain2 = d.lemma(p.le_trans, &[succ_x, xx, x, growth, final_le]); // Le(succ x, x) = Lt x x

                let contra = d.lemma(p.lt_irrefl, &[x, chain2]);

                let with_heq = d.lam_fv(heq_fv, heq_ty, contra);
                let with_bne = d.lam_fv(bne_fv, bne_ty, with_heq);
                let with_ane = d.lam_fv(ane_fv, ane_ty, with_bne);
                d.lam_fv(cop_fv, cop_ty, with_ane)
            };

            cases_zero_succ(d, n, &goal_at_n, &at_n_zero, &at_n_succ)
        };

        let proof = cases_zero_succ(d, m, &goal_at_m, &at_m_zero, &at_m_succ);
        (goal_at_m(d, m), proof)
    })?;
    Ok(())
}
