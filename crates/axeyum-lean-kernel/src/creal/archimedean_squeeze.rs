//! The **Archimedean squeeze bridge**: turning an abstract `∀ e : Nat`
//! accuracy family into `CReal.le`'s own seq-level `∀ n` shape.
//!
//! `CReal.le x y := ∀ n, seq x n − seq y n ≤ 2/(n+1)` is a genuine statement
//! about *raw representative sequences*, sampled at the index the goal names.
//! Many analysis arguments instead produce a bound *for every accuracy `e`*
//! — `∀ e, le x (add y (ofRat (1/(e+1))))` — and the two shapes are indexed
//! differently: the hypothesis's `e` and the goal's `n` do not obviously line
//! up, and the representative sequences are only `Regular`, not exact.
//!
//! ## The route, worked on paper first
//!
//! Fix the goal index `n`. The bridge introduces a **second**, independent
//! index `j` — an Archimedean witness, not the goal index — and instantiates
//! the hypothesis at accuracy `e := j`, then reads its own `∀ m` binder at
//! `m := j` too (the *same* `j` both times, which is what makes the two
//! error terms it contributes shrink together). That gives, at `j`:
//!
//! ```text
//! x_j − (y_{2j+1} + 1/(j+1)) ≤ 2/(j+1)        (the hypothesis, at e=j, m=j)
//! ```
//!
//! (`CReal.add`'s sample at `m` is `y`'s sample at Bishop's shifted index
//! `2m+1`, per `creal.rs`'s `add`.) Rearranging (`Rat.le_of_sub_le` then
//! `Rat.sub_le_of_le` around one `Rat.add_assoc`) gives the clean form:
//!
//! ```text
//! x_j − y_{2j+1} ≤ 3/(j+1)                                          (B)
//! ```
//!
//! Two `CReal.regular` round trips connect this to the goal's own index `n`:
//!
//! ```text
//! x_n − x_j           ≤ 1/(n+1) + 1/(j+1)      (regularity of x at n, j)  (A)
//! y_{2j+1} − y_n       ≤ 1/(2j+2) + 1/(n+1)     (regularity of y at 2j+1, n) (C)
//! ```
//!
//! Telescoping `(x_n−x_j) + (x_j−y_{2j+1}) + (y_{2j+1}−y_n) = x_n − y_n`
//! (`Rat.sub_add_sub`, twice) and summing (A)+(B)+(C):
//!
//! ```text
//! x_n − y_n ≤ [1/(n+1)+1/(j+1)] + [3/(j+1)] + [1/(2j+2)+1/(n+1)]
//!           = 2/(n+1) + 4/(j+1) + 1/(2j+2)
//! ```
//!
//! `1/(2j+2)` does not fuse into a `k/(j+1)` term for an integer `k` (it is
//! *half* of `1/(j+1)`, not a whole multiple), so it is **weakened**, not
//! fused: `1/(2j+2) ≤ 1/(j+1)`, from `1/(2j+2)+1/(2j+2) = 1/(j+1)`
//! (`Rat.natDivSucc_add` then `Rat.natDivSucc_halve`) and `a ≤ a+a` for
//! `a ≥ 0` — no lemma antitone in `Rat.natDivSucc`'s index is needed, exactly
//! as `creal.rs`'s own `shifted_bound_le` avoids one for the same reason.
//! That gives, for every `j`:
//!
//! ```text
//! x_n − y_n ≤ 2/(n+1) + 5/(j+1)
//! ```
//!
//! and `Rat.le_of_le_add_natDivSucc` (the Archimedean property of `ℚ`, `k =
//! 5`) closes it to `x_n − y_n ≤ 2/(n+1)` — `CReal.le x y` at the arbitrary
//! index `n` the goal named, so `CReal.le x y` outright.
//!
//! Concretely, at `n = 0` (goal bound `2/(0+1) = 2`): the sum before
//! weakening is `2 + 4/(j+1) + 1/(2j+2)`, e.g. `4.25` at `j=1`, `3.125` at
//! `j=3`, `2.045` at `j=99` — converging to `2` as required, and the weakened
//! bound `2 + 5/(j+1)` (`7` at `j=1`, `2.05` at `j=99`) converges to the same
//! place, just from slightly further out.
//!
//! `CReal.equiv_zero_of_small` is then a thin wrapper: `le v zero` and
//! `le zero v` each reduce to one call of the bridge above (`y := zero`,
//! resp. `x := zero`), with the `add zero`/`add v (neg v)` bookkeeping done
//! by `le_congr` against `add_zero`/`add_comm`/`add_neg`, and
//! `equiv_of_le_le` closes the two into one `Equiv`.
//!
//! ## Generalizing from rate `1` to an arbitrary rate `K`
//!
//! `CReal.le_of_forall_le_add_rate`/`CReal.equiv_zero_of_rate` are the same
//! two bridges with the hypothesis's accuracy family `1/(e+1)` replaced by
//! `K/(e+1)` for an arbitrary bound `K : Nat`. Only **term B** above touches
//! `K` — it fuses `K/(j+1) + 2/(j+1)` to `(K+2)/(j+1)` instead of `3/(j+1)`.
//! Terms A and C are `CReal.regular`'s own rate-1 Cauchy modulus, which is a
//! property of the *representation*, not of the hypothesis, so they and
//! [`half_shift_le`] are untouched by the generalization. Re-fusing the
//! sorted sum through the same shape as before gives
//! `2/(n+1) + (K+4)/(j+1)`, and `Rat.le_of_le_add_natDivSucc` closes it at
//! `k := K+4` — already general in its own `k` parameter, so nothing there
//! needed to change either.
//!
//! `K+4` is built as a `Nat` expression via `Rat.natDivSucc_add`'s own
//! `Nat.add` (never reconstructed as a separate "clean" term and rewritten
//! into place by defeq): every fusion step below reuses the exact `ExprId`
//! the previous `nat_div_succ_add` instantiation produced, so no step needs
//! the kernel to reduce a `Nat.add` containing the free `K` — the concern
//! this crate's `Nat.add`-recurses-on-the-right gotcha would otherwise raise
//! never arises, because the two sides of every rewrite here are the *same*
//! term, not two different-looking terms asserted equal by computation.
//!
//! `CReal.le_of_forall_le_add_small`/`CReal.equiv_zero_of_small` are kept
//! under their original names and signatures as thin `K := 1` wrappers over
//! the rate lemmas, so every existing caller (`fermat.rs`, `monotone.rs`,
//! `deriv_unique.rs`, `integral.rs`) is unaffected.

use super::{
    CRealPrelude, cadd, cle, creal_ty, div_succ, div_succ_k, embed, equiv, halves, modulus, sample,
    shift,
};
use crate::KernelError;
use crate::env::Declaration;
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::nat_prelude::NatOps;
use crate::rat_prelude::group::{rsub, rsum, rsum_append, rsum_perm};
use crate::rat_prelude::ops::{radd, rat_eq_rewrite, rchain, rcongr, rle, rsymm, rzero};

/// Admit `CReal.le_of_forall_le_add_rate`/`CReal.equiv_zero_of_rate` (the
/// general rate-`K` bridges) and `CReal.le_of_forall_le_add_small`/
/// `CReal.equiv_zero_of_small` (their `K := 1` instances, kept under the
/// original names so every existing caller is unaffected).
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
pub(super) fn declare_archimedean_squeeze(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    declare_le_of_forall_le_add_rate(d, p)?;
    declare_le_of_forall_le_add_small(d, p)?;
    declare_equiv_zero_of_rate(d, p)?;
    declare_equiv_zero_of_small(d, p)
}

/// `1/(2j+2) ≤ 1/(j+1)` — half of a `natDivSucc` term is at most itself,
/// from `1/(2j+2)+1/(2j+2) = 1/(j+1)` (`natDivSucc_add` + `natDivSucc_halve`)
/// and `a ≤ a+a` for `a ≥ 0`. No lemma antitone in the index is needed.
///
/// This is `CReal.regular`'s own rate-1 Cauchy modulus, not the hypothesis's
/// accuracy family — it does **not** generalize with `K` and is shared,
/// unchanged, by [`declare_le_of_forall_le_add_rate`] at every rate.
fn half_shift_le(d: &mut IntDev<'_>, p: CRealPrelude, j: ExprId) -> ExprId {
    let rat = p.rat;
    let s = shift(d, j);
    let d1 = div_succ(d, p, 1, s);
    let b1 = div_succ(d, p, 1, j);
    let two_s = div_succ(d, p, 2, s);
    let one_nat = d.num(1);

    // d1 + d1 = two_s = b1.
    let fuse = d.lemma(rat.nat_div_succ_add, &[one_nat, one_nat, s]);
    let halve = d.lemma(rat.nat_div_succ_halve, &[j]);
    let dd = radd(d, d1, d1);
    let (_, combined) = rchain(d, dd, &[(two_s, fuse), (b1, halve)]);

    // d1 ≤ d1 + d1, from `d1 + 0 ≤ d1 + d1` (add_le_add refl/nonneg) folded
    // through `add_zero`.
    let nonneg = d.lemma(rat.zero_le_nat_div_succ, &[one_nat, s]);
    let refl = d.lemma(rat.le_refl, &[d1]);
    let zero = rzero(d, rat);
    let padded = d.lemma(rat.add_le_add, &[d1, d1, zero, d1, refl, nonneg]);
    let with_zero = radd(d, d1, zero);
    let trim = d.lemma(rat.add_zero, &[d1]);
    let trimmed = rat_eq_rewrite(d, with_zero, d1, trim, padded, &|d, t| rle(d, rat, t, dd));

    // Rewrite the RHS `d1 + d1` into `b1`.
    rat_eq_rewrite(d, dd, b1, combined, trimmed, &|d, t| rle(d, rat, d1, t))
}

/// `CReal.le_of_forall_le_add_rate : ∀ k x y,
/// (∀ e, le x (add y (ofRat (natDivSucc k e)))) → le x y`.
///
/// The rate-`K` generalization: identical to the `K = 1` derivation term for
/// term, except that the numerator that used to be the literal `1` in the
/// hypothesis (and every quantity term B alone contributes) is now the bound
/// variable `k`. Terms A and C — `CReal.regular`'s own rate-1 modulus — and
/// [`half_shift_le`] are untouched. See this module's doc comment for the
/// worked-out arithmetic.
///
/// Every `Nat.add` built below reuses the exact [`ExprId`] the previous
/// `Rat.natDivSucc_add` instantiation produced for its combined index, so no
/// step asks the kernel to reduce a `Nat.add` containing the free `k` — both
/// sides of every rewrite are the *same* term, not two different-looking
/// terms asserted equal by computation.
fn declare_le_of_forall_le_add_rate(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let rat = p.rat;
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let one_nat = d.num(1);
    let two_nat = d.num(2);

    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let y_fv = d.fresh_fvar();
    let y = d.kernel().fvar(y_fv);

    // The hypothesis: ∀ e, le x (add y (ofRat (natDivSucc k e))).
    let hyp_ty = {
        let e_fv = d.fresh_fvar();
        let e = d.kernel().fvar(e_fv);
        let qe_rat = div_succ_k(d, p, k, e);
        let qe = embed(d, p, qe_rat);
        let sum = cadd(d, p, y, qe);
        let body = cle(d, p, x, sum);
        d.pi_fv(e_fv, nat, body)
    };
    let hyp_fv = d.fresh_fvar();
    let hyp = d.kernel().fvar(hyp_fv);

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let head = sample(d, p, x, n);
    let tail = sample(d, p, y, n);
    let target = rsub(d, rat, head, tail);
    let a1 = div_succ(d, p, 1, n);
    let goal_bound = div_succ(d, p, 2, n);

    // The Nat indices carried through term B's fusions -- computed once,
    // independent of `j`, since only `k` (not `j`) feeds them.
    //
    // c1_idx = k+2   (was the literal `3`)
    // bc1_idx = 1 + c1_idx = k+3   (was the literal `4`)
    // k4_idx = 1 + bc1_idx = k+4   (was the literal `5`)
    let c1_idx = NatOps::add(d, k, two_nat);
    let bc1_idx = NatOps::add(d, one_nat, c1_idx);
    let k4_idx = NatOps::add(d, one_nat, bc1_idx);

    let hypothesis_over_j = {
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let xj = sample(d, p, x, j);
        let s = shift(d, j);
        let ys = sample(d, p, y, s);
        let b1 = div_succ(d, p, 1, j);
        let c1 = div_succ_k(d, p, c1_idx, j);

        // --- Term B: xj − ys ≤ (k+2)/(j+1), from the hypothesis at e=j, m=j. ---
        // `CReal.add`'s sample at `j` is `seq y (shift j) + seq qj (shift j)`,
        // and `seq (ofRat qj_rat) _` reduces to the raw rational `qj_rat` —
        // NOT the `CReal` value `embed(qj_rat)` — so every Rat-level sum
        // below is built from `qj_rat`, never from a `CReal.ofRat` term.
        let qj_rat = div_succ_k(d, p, k, j);
        let hyp_j = d.apply(hyp, &[j]);
        let hyp_j_at_j = d.apply(hyp_j, &[j]);
        // hyp_j_at_j : Rat.le (xj − (ys+qj_rat)) (2/(j+1))
        let sum_ys_qj = radd(d, ys, qj_rat);
        let bb0 = div_succ(d, p, 2, j);
        let step1 = d.lemma(rat.le_of_sub_le, &[xj, sum_ys_qj, bb0, hyp_j_at_j]);
        // step1 : xj ≤ (ys+qj_rat)+bb0
        let assoc = d.lemma(rat.add_assoc, &[ys, qj_rat, bb0]);
        // assoc : (ys+qj_rat)+bb0 = ys+(qj_rat+bb0)
        let qj_bb0 = radd(d, qj_rat, bb0);
        let regrouped_sum = radd(d, ys, qj_bb0);
        let sum_ys_qj_bb0 = radd(d, sum_ys_qj, bb0);
        let step1b = rat_eq_rewrite(d, sum_ys_qj_bb0, regrouped_sum, assoc, step1, &|d, t| {
            rle(d, rat, xj, t)
        });
        // step1b : xj ≤ ys+(qj_rat+bb0)
        let rb0 = d.lemma(rat.sub_le_of_le, &[xj, ys, qj_bb0, step1b]);
        // rb0 : xj − ys ≤ qj_rat+bb0
        let fuse_b = d.lemma(rat.nat_div_succ_add, &[k, two_nat, j]);
        // fuse_b : qj_rat + bb0 = c1 ((k+2)/(j+1))
        let ub = rsub(d, rat, xj, ys);
        let rb = rat_eq_rewrite(d, qj_bb0, c1, fuse_b, rb0, &|d, t| rle(d, rat, ub, t));

        // --- Term A: x_n − x_j ≤ modulus(n, j) -- rate 1, independent of `k`. ---
        let wa = d.lemma(p.regular, &[x, n, j]);
        let ua = rsub(d, rat, head, xj);
        let ba = modulus(d, p, n, j);
        let (_, ra) = halves(d, p, ua, ba, wa);

        // --- Term C: y_s − y_n ≤ modulus(s, n), weakened to b1 + a1 -- also
        // rate 1, independent of `k`. ---
        let wc = d.lemma(p.regular, &[y, s, n]);
        let uc = rsub(d, rat, ys, tail);
        let bc = modulus(d, p, s, n);
        let (_, rc) = halves(d, p, uc, bc, wc);
        let half_le = half_shift_le(d, p, j);
        // half_le : d1 ≤ b1, where d1 = div_succ(1, s)
        let refl_a1 = d.lemma(rat.le_refl, &[a1]);
        let bc_weak = radd(d, b1, a1);
        let d1_s = div_succ(d, p, 1, s);
        let weaken_c = d.lemma(rat.add_le_add, &[d1_s, b1, a1, a1, half_le, refl_a1]);
        let rc2 = d.lemma(rat.le_trans, &[uc, bc, bc_weak, rc, weaken_c]);

        // --- Combine: (uA + (uB + uC)) ≤ (bA + (c1 + bc_weak)). ---
        let sbc = d.lemma(rat.add_le_add, &[ub, c1, uc, bc_weak, rb, rc2]);
        let ub_uc = radd(d, ub, uc);
        let c1_bc_weak = radd(d, c1, bc_weak);
        let sall = d.lemma(rat.add_le_add, &[ua, ba, ub_uc, c1_bc_weak, ra, sbc]);
        // sall : (ua+(ub+uc)) ≤ (ba+(c1+bc_weak))
        let q123 = radd(d, ua, ub_uc);
        let ball = radd(d, ba, c1_bc_weak);

        // Quantity: ua+(ub+uc) = target.
        let mid = rsub(d, rat, xj, tail);
        let step_a = d.lemma(rat.sub_add_sub, &[xj, ys, tail]);
        // step_a : (xj−ys)+(ys−tail) = xj−tail  i.e. ub+uc = mid
        let step_b = d.lemma(rat.sub_add_sub, &[head, xj, tail]);
        // step_b : (head−xj)+(xj−tail) = head−tail  i.e. ua+mid = target
        let staged = radd(d, ua, mid);
        let after_a = rcongr(d, ub_uc, mid, step_a, &|d, t| radd(d, ua, t));
        let (_, quantity_chain) = rchain(d, q123, &[(staged, after_a), (target, step_b)]);
        let at_quantity = rat_eq_rewrite(d, q123, target, quantity_chain, sall, &|d, t| {
            rle(d, rat, t, ball)
        });
        // at_quantity : target ≤ ball

        // Bound: ba+(c1+bc_weak) = goal_bound + (k+4)/(j+1). Sorted order and
        // permutation exactly mirror the `K = 1` derivation; only the atom
        // that used to be the literal `3/(j+1)` is `c1`, at the symbolic
        // index `c1_idx = k+2`.
        let flat_atoms = [a1, b1, c1, b1, a1];
        let sorted_atoms = [a1, a1, b1, b1, c1];
        let flat = rsum(d, rat, &flat_atoms);
        let sorted = rsum(d, rat, &sorted_atoms);
        let flatten = rsum_append(d, rat, &flat_atoms[..2], &flat_atoms[2..]);
        let permute = rsum_perm(d, rat, &flat_atoms, &sorted_atoms);

        // sorted = a1+(a1+(b1+(b1+c1))). Innermost pair (b1+c1) -> (k+3)/(j+1).
        let bc1 = div_succ_k(d, p, bc1_idx, j);
        let fuse_inner = d.lemma(rat.nat_div_succ_add, &[one_nat, c1_idx, j]);
        let bc_pair = radd(d, b1, c1);
        let after_inner = rcongr(d, bc_pair, bc1, fuse_inner, &|d, t| {
            let level1 = radd(d, b1, t);
            let level2 = radd(d, a1, level1);
            radd(d, a1, level2)
        });
        let sorted_1 = {
            let level1 = radd(d, b1, bc1);
            let level2 = radd(d, a1, level1);
            radd(d, a1, level2)
        };

        // (b1+bc1) -> (k+4)/(j+1).
        let k4 = div_succ_k(d, p, k4_idx, j);
        let fuse_mid = d.lemma(rat.nat_div_succ_add, &[one_nat, bc1_idx, j]);
        let b_four = radd(d, b1, bc1);
        let after_mid = rcongr(d, b_four, k4, fuse_mid, &|d, t| {
            let level2 = radd(d, a1, t);
            radd(d, a1, level2)
        });
        let sorted_2 = {
            let level2 = radd(d, a1, k4);
            radd(d, a1, level2)
        };

        // Regroup a1+(a1+k4) -> (a1+a1)+k4.
        let forward = d.lemma(rat.add_assoc, &[a1, a1, k4]);
        let aa = radd(d, a1, a1);
        let flat_pair = radd(d, aa, k4);
        let regroup = rsymm(d, flat_pair, sorted_2, forward);

        // (a1+a1) -> goal_bound -- rate 1, independent of `k`.
        let fuse_head = d.lemma(rat.nat_div_succ_add, &[one_nat, one_nat, n]);
        let after_head = rcongr(d, aa, goal_bound, fuse_head, &|d, t| radd(d, t, k4));
        let final_target = radd(d, goal_bound, k4);

        let (_, bound_chain) = rchain(
            d,
            ball,
            &[
                (flat, flatten),
                (sorted, permute),
                (sorted_1, after_inner),
                (sorted_2, after_mid),
                (flat_pair, regroup),
                (final_target, after_head),
            ],
        );
        let moved = rat_eq_rewrite(d, ball, final_target, bound_chain, at_quantity, &|d, t| {
            rle(d, rat, target, t)
        });
        // moved : target ≤ goal_bound + (k+4)/(j+1)
        d.lam_fv(j_fv, nat, moved)
    };

    let at_index = d.lemma(
        rat.le_of_le_add_nat_div_succ,
        &[target, goal_bound, k4_idx, hypothesis_over_j],
    );
    let value = {
        let over_n = d.lam_fv(n_fv, nat, at_index);
        let with_hyp = d.lam_fv(hyp_fv, hyp_ty, over_n);
        let with_y = d.lam_fv(y_fv, carrier, with_hyp);
        let with_x = d.lam_fv(x_fv, carrier, with_y);
        d.lam_fv(k_fv, nat, with_x)
    };
    let ty = {
        let conclusion = cle(d, p, x, y);
        let after_hyp = d.arrow(hyp_ty, conclusion);
        let with_y = d.pi_fv(y_fv, carrier, after_hyp);
        let with_x = d.pi_fv(x_fv, carrier, with_y);
        d.pi_fv(k_fv, nat, with_x)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.le_of_forall_le_add_rate,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CReal.le_of_forall_le_add_small : ∀ x y,
/// (∀ e, le x (add y (ofRat (natDivSucc 1 e)))) → le x y`.
///
/// The `K := 1` instance of [`declare_le_of_forall_le_add_rate`], kept under
/// the original name and signature so every existing caller (`fermat.rs`,
/// `monotone.rs`, `deriv_unique.rs`, `integral.rs`) is unaffected by the
/// generalization.
fn declare_le_of_forall_le_add_small(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let one_nat = d.num(1);

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let y_fv = d.fresh_fvar();
    let y = d.kernel().fvar(y_fv);

    // The hypothesis: ∀ e, le x (add y (ofRat (natDivSucc 1 e))).
    let hyp_ty = {
        let e_fv = d.fresh_fvar();
        let e = d.kernel().fvar(e_fv);
        let qe_rat = div_succ(d, p, 1, e);
        let qe = embed(d, p, qe_rat);
        let sum = cadd(d, p, y, qe);
        let body = cle(d, p, x, sum);
        d.pi_fv(e_fv, nat, body)
    };
    let hyp_fv = d.fresh_fvar();
    let hyp = d.kernel().fvar(hyp_fv);

    let value = {
        let body = d.lemma(p.le_of_forall_le_add_rate, &[one_nat, x, y, hyp]);
        let with_hyp = d.lam_fv(hyp_fv, hyp_ty, body);
        let with_y = d.lam_fv(y_fv, carrier, with_hyp);
        d.lam_fv(x_fv, carrier, with_y)
    };
    let ty = {
        let conclusion = cle(d, p, x, y);
        let after_hyp = d.arrow(hyp_ty, conclusion);
        let with_y = d.pi_fv(y_fv, carrier, after_hyp);
        d.pi_fv(x_fv, carrier, with_y)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.le_of_forall_le_add_small,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CReal.equiv_zero_of_rate : ∀ k v,
/// (∀ e, le (abs v) (ofRat (natDivSucc k e))) → Equiv v zero`.
///
/// The rate-`K` generalization of [`declare_equiv_zero_of_small`]: the same
/// two-sided-bound argument, through [`declare_le_of_forall_le_add_rate`] at
/// the same `k` instead of the hard-coded `k := 1`.
fn declare_equiv_zero_of_rate(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let zero_real = d.kernel().const_(p.zero, vec![]);

    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let v_fv = d.fresh_fvar();
    let v = d.kernel().fvar(v_fv);
    let abs_v = d.const_app(p.abs, &[v]);

    let hyp_ty = {
        let e_fv = d.fresh_fvar();
        let e = d.kernel().fvar(e_fv);
        let qe_rat = div_succ_k(d, p, k, e);
        let qe = embed(d, p, qe_rat);
        let body = cle(d, p, abs_v, qe);
        d.pi_fv(e_fv, nat, body)
    };
    let hyp_fv = d.fresh_fvar();
    let hyp = d.kernel().fvar(hyp_fv);

    // le v zero: ∀ e, le v (add zero (ofRat (natDivSucc k e))).
    let hyp_v_zero = {
        let e_fv = d.fresh_fvar();
        let e = d.kernel().fvar(e_fv);
        let qe_rat = div_succ_k(d, p, k, e);
        let qe = embed(d, p, qe_rat);
        let he = d.apply(hyp, &[e]);
        // he : le (abs v) qe
        let self_le = d.lemma(p.le_abs_self, &[v]);
        // self_le : le v (abs v)
        let step1 = d.lemma(p.le_trans, &[v, abs_v, qe, self_le, he]);
        // step1 : le v qe
        let comm = d.lemma(p.add_comm, &[zero_real, qe]);
        // comm : Equiv (add zero qe) (add qe zero)
        let az = d.lemma(p.add_zero, &[qe]);
        // az : Equiv (add qe zero) qe
        let zero_qe = cadd(d, p, zero_real, qe);
        let qe_zero = cadd(d, p, qe, zero_real);
        let eq1 = d.lemma(p.equiv_trans, &[zero_qe, qe_zero, qe, comm, az]);
        // eq1 : Equiv (add zero qe) qe
        let eq1_sym = d.lemma(p.equiv_symm, &[zero_qe, qe, eq1]);
        // eq1_sym : Equiv qe (add zero qe)
        let refl_v = d.lemma(p.equiv_refl, &[v]);
        let step2 = d.lemma(p.le_congr, &[v, v, qe, zero_qe, refl_v, eq1_sym, step1]);
        // step2 : le v (add zero qe)
        d.lam_fv(e_fv, nat, step2)
    };
    let le_v_zero = d.lemma(p.le_of_forall_le_add_rate, &[k, v, zero_real, hyp_v_zero]);

    // le zero v: ∀ e, le zero (add v (ofRat (natDivSucc k e))).
    let hyp_zero_v = {
        let e_fv = d.fresh_fvar();
        let e = d.kernel().fvar(e_fv);
        let qe_rat = div_succ_k(d, p, k, e);
        let qe = embed(d, p, qe_rat);
        let he = d.apply(hyp, &[e]);
        // he : le (abs v) qe
        let neg_le = d.lemma(p.neg_le_abs, &[v]);
        // neg_le : le (neg v) (abs v)
        let neg_v = d.const_app(p.neg, &[v]);
        let step1 = d.lemma(p.le_trans, &[neg_v, abs_v, qe, neg_le, he]);
        // step1 : le (neg v) qe
        let refl_v = d.lemma(p.le_refl, &[v]);
        let widen = d.lemma(p.add_le_add, &[v, v, neg_v, qe, refl_v, step1]);
        // widen : (add v (neg v)) ≤ (add v qe)
        let an = d.lemma(p.add_neg, &[v]);
        // an : Equiv (add v (neg v)) zero
        let v_neg_v = cadd(d, p, v, neg_v);
        let an_sym = d.lemma(p.equiv_symm, &[v_neg_v, zero_real, an]);
        // an_sym : Equiv zero (add v (neg v))
        let z_le = d.lemma(p.le_of_equiv, &[zero_real, v_neg_v, an_sym]);
        // z_le : le zero (add v (neg v))
        let sum = cadd(d, p, v, qe);
        let step2 = d.lemma(p.le_trans, &[zero_real, v_neg_v, sum, z_le, widen]);
        // step2 : le zero (add v qe)
        d.lam_fv(e_fv, nat, step2)
    };
    let le_zero_v = d.lemma(p.le_of_forall_le_add_rate, &[k, zero_real, v, hyp_zero_v]);

    let body = d.lemma(p.equiv_of_le_le, &[v, zero_real, le_v_zero, le_zero_v]);

    let value = {
        let with_hyp = d.lam_fv(hyp_fv, hyp_ty, body);
        let with_v = d.lam_fv(v_fv, carrier, with_hyp);
        d.lam_fv(k_fv, nat, with_v)
    };
    let ty = {
        let conclusion = equiv(d, p, v, zero_real);
        let after_hyp = d.arrow(hyp_ty, conclusion);
        let with_v = d.pi_fv(v_fv, carrier, after_hyp);
        d.pi_fv(k_fv, nat, with_v)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.equiv_zero_of_rate,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CReal.equiv_zero_of_small : ∀ v,
/// (∀ e, le (abs v) (ofRat (natDivSucc 1 e))) → Equiv v zero`.
///
/// The `K := 1` instance of [`declare_equiv_zero_of_rate`], kept under the
/// original name and signature so every existing caller is unaffected.
fn declare_equiv_zero_of_small(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let zero_real = d.kernel().const_(p.zero, vec![]);
    let one_nat = d.num(1);

    let v_fv = d.fresh_fvar();
    let v = d.kernel().fvar(v_fv);
    let abs_v = d.const_app(p.abs, &[v]);

    let hyp_ty = {
        let e_fv = d.fresh_fvar();
        let e = d.kernel().fvar(e_fv);
        let qe_rat = div_succ(d, p, 1, e);
        let qe = embed(d, p, qe_rat);
        let body = cle(d, p, abs_v, qe);
        d.pi_fv(e_fv, nat, body)
    };
    let hyp_fv = d.fresh_fvar();
    let hyp = d.kernel().fvar(hyp_fv);

    let value = {
        let body = d.lemma(p.equiv_zero_of_rate, &[one_nat, v, hyp]);
        let with_hyp = d.lam_fv(hyp_fv, hyp_ty, body);
        d.lam_fv(v_fv, carrier, with_hyp)
    };
    let ty = {
        let conclusion = equiv(d, p, v, zero_real);
        let after_hyp = d.arrow(hyp_ty, conclusion);
        d.pi_fv(v_fv, carrier, after_hyp)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.equiv_zero_of_small,
        uparams: vec![],
        ty,
        value,
    })
}
