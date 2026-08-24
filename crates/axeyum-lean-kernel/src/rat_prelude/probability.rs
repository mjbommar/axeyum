//! The first probability facts over `ℚ`: `Rat.IsDistribution`, and the two
//! properties that make it usable.
//!
//! A finite probability distribution needs no analysis — `ℚ` is enough — so
//! this is the natural next rung once [`super::sum`] gives `Rat.sumRange` and
//! its monotonicity (`sumRange_le`/`sumRange_nonneg`).
//!
//! `Rat.IsDistribution p n := (∀ k, k < n → 0 ≤ p k) ∧ sumRange p n = 1`, a
//! `Prop`-valued `Definition` over [`super::sum`]'s `bounded_nonneg` and the
//! carrier's own `Eq`, in the same style `Int.dvd` uses for its own
//! `∃`-valued `Definition` (`int_prelude/dvd.rs::declare_dvd_definition`).
//!
//! [`declare_prob_le_one`] needs "one term never exceeds the sum of a
//! nonnegative sequence" (`term_le_sum_range`, private — nothing else needs
//! it yet), proved by an ordinary bounded induction that case-splits the new
//! index against the boundary (`Nat.lt_or_eq_of_le`), exactly the shape
//! `sumRange_le` and `sumRange_nonneg` are themselves proved by, one level
//! up.
//!
//! [`declare_prob_complement`] states the complementary-mass fact over a
//! **prefix**, quantifying over the split point `m` and the tail length `j`
//! directly (`n := m + j`) rather than over `m ≤ n`, so the proof
//! (`sum_range_split`, private) never needs `Nat` subtraction — induction on
//! `j` alone, `m` and `p` held fixed, aligns with `Rat.add`'s own recursion
//! (`Nat.add m (succ j) ≡ succ (Nat.add m j)`) for free.

use super::RatPrelude;
use super::ops::{
    nat_eq_to_rat, radd, rat_eq_rewrite, rat_ty, rle, rone, rsum_range, rsymm, rtrans, rzero,
};
use super::sum::bounded_nonneg;
use crate::BinderInfo;
use crate::KernelError;
use crate::env::{Declaration, ReducibilityHint};
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::nat_prelude::NatOps;

/// Delta height for `Rat.IsDistribution`: above `Rat.sumRange`
/// ([`super::sum::SUM_HEIGHT`]-equivalent, 34) and everything else this
/// prelude has declared so far.
const PROB_HEIGHT: u16 = 35;

/// Declare `Rat.IsDistribution` and everything this file proves about it.
///
/// # Errors
///
/// Returns the trusted gate's rejection — an `Err` means the kernel
/// **refused** a proof, not that a script gave up.
pub(super) fn declare_probability(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    declare_is_distribution(d, p)?;
    declare_prob_le_one(d, p)?;
    declare_prob_complement(d, p)?;
    Ok(())
}

/// `Rat.IsDistribution p n`, i.e. `d.const_app(p.is_distribution, &[pf,
/// n])`.
fn is_distribution(d: &mut IntDev<'_>, p: RatPrelude, pf: ExprId, n: ExprId) -> ExprId {
    d.const_app(p.is_distribution, &[pf, n])
}

/// `(∀ k, Lt k n → le zero (pf k)) ∧ sumRange pf n = one` — the body
/// [`declare_is_distribution`] admits `Rat.IsDistribution` as, rebuilt here so
/// callers that need to case on the components (`d.and_left`/`d.and_right`)
/// can reconstruct the exact left/right `Prop`s without re-declaring
/// anything.
fn is_distribution_parts(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    pf: ExprId,
    n: ExprId,
) -> (ExprId, ExprId) {
    let nonneg_part = bounded_nonneg(d, p, pf, n);
    let sum_part = {
        let sum = rsum_range(d, p, pf, n);
        let one_r = rone(d, p);
        super::ops::req(d, sum, one_r)
    };
    (nonneg_part, sum_part)
}

/// Admit `Rat.IsDistribution : (Nat → Rat) → Nat → Prop := fun p n => (∀ k,
/// Lt k n → le zero (p k)) ∧ sumRange p n = one`.
fn declare_is_distribution(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = rat_ty(d);
    let fn_ty = d.arrow(nat, carrier);
    let anon = d.anon_name();
    let prop = d.kernel().sort_zero();

    let pf_fv = d.fresh_fvar();
    let pf = d.kernel().fvar(pf_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let (nonneg_part, sum_part) = is_distribution_parts(d, p, pf, n);
    let body = d.and(nonneg_part, sum_part);
    let value = {
        let inner = d.lam_fv(n_fv, nat, body);
        d.lam_fv(pf_fv, fn_ty, inner)
    };
    let ty = {
        let inner = d.kernel().pi(anon, nat, prop, BinderInfo::Default);
        d.kernel().pi(anon, fn_ty, inner, BinderInfo::Default)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.is_distribution,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(PROB_HEIGHT),
    })
}

/// `∀ n, (∀ i, Lt i n → le zero (pf i)) → ∀ k, Lt k n → le (pf k) (sumRange
/// pf n)`, specialised at `n`, as a raw `(statement, proof)` pair — a single
/// term of a nonnegative finite sequence never exceeds the sum of all its
/// terms up to the bound.
///
/// Induction on `n`. The successor step case-splits the new index `k < succ
/// m` into `k < m` (chase the inductive hypothesis, then `f m ≤ sumRange f
/// m ≤ sumRange f (succ m)`) or `k = m` (transport `f m ≤ sumRange f (succ
/// m)` along the equality) via `Nat.lt_or_eq_of_le`/`Nat.le_of_lt_succ` —
/// there is no way around this split; it is the classical proof. Kept
/// private: only [`declare_prob_le_one`] needs it.
fn term_le_sum_range(d: &mut IntDev<'_>, p: RatPrelude, pf: ExprId, n: ExprId) -> (ExprId, ExprId) {
    let nat = d.nat_ty();

    let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let hyp = bounded_nonneg(d, p, pf, x);
        let sum = rsum_range(d, p, pf, x);
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let k_lt = d.lt(k, x);
        let fk = d.apply(pf, &[k]);
        let concl = rle(d, p, fk, sum);
        let inner = d.arrow(k_lt, concl);
        let with_k = d.pi_fv(k_fv, nat, inner);
        d.arrow(hyp, with_k)
    };
    let stmt = motive(d, n);

    let proof = d.induct(
        &motive,
        &|d| {
            let zero_n = d.zero();
            let hyp_ty = bounded_nonneg(d, p, pf, zero_n);
            let h_fv = d.fresh_fvar();
            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let k_lt = d.lt(k, zero_n);
            let hi_fv = d.fresh_fvar();
            let hi = d.kernel().fvar(hi_fv);
            let sum0 = rsum_range(d, p, pf, zero_n);
            let fk = d.apply(pf, &[k]);
            let concl = rle(d, p, fk, sum0);
            let np = d.prelude();
            let impossible = d.lemma(np.not_lt_zero, &[k, hi]);
            let body = d.absurd(concl, impossible);
            let with_hi = d.lam_fv(hi_fv, k_lt, body);
            let with_k = d.lam_fv(k_fv, nat, with_hi);
            d.lam_fv(h_fv, hyp_ty, with_k)
        },
        &|d, m, ih| {
            let sm = d.succ(m);
            let hyp_ty = bounded_nonneg(d, p, pf, sm);
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);

            let np = d.prelude();
            let h_at_m = {
                let i_fv = d.fresh_fvar();
                let i = d.kernel().fvar(i_fv);
                let hi_ty = d.lt(i, m);
                let hi_fv = d.fresh_fvar();
                let hi = d.kernel().fvar(hi_fv);
                let le_succ_m = d.lemma(np.le_succ, &[m]);
                let lifted = d.lemma(np.lt_of_lt_of_le, &[i, m, sm, hi, le_succ_m]);
                let applied = d.apply(h, &[i, lifted]);
                let with_hi = d.lam_fv(hi_fv, hi_ty, applied);
                d.lam_fv(i_fv, nat, with_hi)
            };
            let ih_applied = d.apply(ih, &[h_at_m]);

            let lt_m_sm = d.lemma(np.lt_succ_self, &[m]);
            let f_m_nonneg = d.apply(h, &[m, lt_m_sm]);

            let sum_m = rsum_range(d, p, pf, m);
            let f_m = d.apply(pf, &[m]);
            let sum_sm = radd(d, sum_m, f_m);

            // sum_m ≤ sum_m + f_m, since 0 ≤ f_m.
            let sum_m_le_sum_sm = {
                let le_refl_sum_m = d.lemma(p.le_refl, &[sum_m]);
                let zero_r = rzero(d, p);
                let h_add = d.lemma(
                    p.add_le_add,
                    &[sum_m, sum_m, zero_r, f_m, le_refl_sum_m, f_m_nonneg],
                );
                let zero_r2 = rzero(d, p);
                let sum_m_plus_zero = radd(d, sum_m, zero_r2);
                let eq_add_zero = d.lemma(p.add_zero, &[sum_m]);
                let motive_le = |d: &mut IntDev<'_>, t: ExprId| -> ExprId { rle(d, p, t, sum_sm) };
                rat_eq_rewrite(d, sum_m_plus_zero, sum_m, eq_add_zero, h_add, &motive_le)
            };

            // f_m ≤ sum_m + f_m, since 0 ≤ sum_m.
            let f_m_le_sum_sm = {
                let sum_m_nonneg = d.lemma(p.sum_range_nonneg, &[pf, m, h_at_m]);
                let le_refl_f_m = d.lemma(p.le_refl, &[f_m]);
                let zero_r = rzero(d, p);
                let h_add2 = d.lemma(
                    p.add_le_add,
                    &[zero_r, sum_m, f_m, f_m, sum_m_nonneg, le_refl_f_m],
                );
                let zero_r2 = rzero(d, p);
                let zero_plus_fm = radd(d, zero_r2, f_m);
                let eq_zero_add = d.lemma(p.zero_add, &[f_m]);
                let motive_le = |d: &mut IntDev<'_>, t: ExprId| -> ExprId { rle(d, p, t, sum_sm) };
                rat_eq_rewrite(d, zero_plus_fm, f_m, eq_zero_add, h_add2, &motive_le)
            };

            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let k_lt_sm = d.lt(k, sm);
            let klt_fv = d.fresh_fvar();
            let klt = d.kernel().fvar(klt_fv);

            let k_le_m = d.lemma(np.le_of_lt_succ, &[k, m, klt]);
            let disj = d.lemma(np.lt_or_eq_of_le, &[k, m, k_le_m]);
            let lt_ty = d.lt(k, m);
            let eq_ty = d.eq(k, m);

            let fk = d.apply(pf, &[k]);
            let target = rle(d, p, fk, sum_sm);
            let body = d.or_elim(
                lt_ty,
                eq_ty,
                target,
                disj,
                &|d, hlt| {
                    let fk_le_summ = d.apply(ih_applied, &[k, hlt]);
                    d.lemma(
                        p.le_trans,
                        &[fk, sum_m, sum_sm, fk_le_summ, sum_m_le_sum_sm],
                    )
                },
                &|d, heq| {
                    let f_m2 = d.apply(pf, &[m]);
                    let rewritten = nat_eq_to_rat(d, k, m, heq, &|d, x| d.apply(pf, &[x]));
                    let flipped = rsymm(d, fk, f_m2, rewritten);
                    let motive_le =
                        |d: &mut IntDev<'_>, t: ExprId| -> ExprId { rle(d, p, t, sum_sm) };
                    rat_eq_rewrite(d, f_m2, fk, flipped, f_m_le_sum_sm, &motive_le)
                },
            );

            let with_klt = d.lam_fv(klt_fv, k_lt_sm, body);
            let with_k = d.lam_fv(k_fv, nat, with_klt);
            d.lam_fv(h_fv, hyp_ty, with_k)
        },
        n,
    );
    (stmt, proof)
}

/// `Rat.prob_le_one : ∀ p n, IsDistribution p n → ∀ k, Lt k n → le (p k)
/// one` — every individual probability is at most `1`. The first genuinely
/// probabilistic statement in this repository.
fn declare_prob_le_one(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = rat_ty(d);
    let fn_ty = d.arrow(nat, carrier);

    let pf_fv = d.fresh_fvar();
    let pf = d.kernel().fvar(pf_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let klt_fv = d.fresh_fvar();
    let klt = d.kernel().fvar(klt_fv);

    let dist_ty = is_distribution(d, p, pf, n);
    let klt_ty = d.lt(k, n);
    let fk = d.apply(pf, &[k]);
    let one_r = rone(d, p);
    let concl = rle(d, p, fk, one_r);

    let (nonneg_part, sum_part) = is_distribution_parts(d, p, pf, n);
    let h_nonneg = d.and_left(nonneg_part, sum_part, h);
    let h_sum = d.and_right(nonneg_part, sum_part, h);

    let (_term_stmt, term_proof) = term_le_sum_range(d, p, pf, n);
    let bounded_result = d.apply(term_proof, &[h_nonneg]);
    let fk_le_sum = d.apply(bounded_result, &[k, klt]);

    let sum_n = rsum_range(d, p, pf, n);
    let motive_le = |d: &mut IntDev<'_>, t: ExprId| -> ExprId { rle(d, p, fk, t) };
    let fk_le_one = rat_eq_rewrite(d, sum_n, one_r, h_sum, fk_le_sum, &motive_le);

    let value = {
        let with_klt = d.lam_fv(klt_fv, klt_ty, fk_le_one);
        let with_k = d.lam_fv(k_fv, nat, with_klt);
        let with_h = d.lam_fv(h_fv, dist_ty, with_k);
        let with_n = d.lam_fv(n_fv, nat, with_h);
        d.lam_fv(pf_fv, fn_ty, with_n)
    };
    let ty = {
        let inner = d.arrow(klt_ty, concl);
        let with_k = d.pi_fv(k_fv, nat, inner);
        let with_h = d.arrow(dist_ty, with_k);
        let with_n = d.pi_fv(n_fv, nat, with_h);
        d.pi_fv(pf_fv, fn_ty, with_n)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.prob_le_one,
        uparams: vec![],
        ty,
        value,
    })
}

/// `fun k => pf (m + k)` — the tail of `pf` starting at `m`.
fn shifted(d: &mut IntDev<'_>, pf: ExprId, m: ExprId) -> ExprId {
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let idx = d.add(m, k);
    let body = d.apply(pf, &[idx]);
    let nat = d.nat_ty();
    d.lam_fv(k_fv, nat, body)
}

/// `Eq Rat (sumRange pf (m+j)) (sumRange pf m + sumRange (shifted pf m) j)`,
/// proved by induction on `j` (`m`, `pf` fixed) — no `Nat` subtraction is
/// needed since the split point `m` and the tail length `j` are the two
/// things quantified, and their sum IS the bound `sumRange` is taken over:
/// `Nat.add m (succ j) ≡ succ (Nat.add m j)` definitionally, matching
/// `sumRange`'s own `succ`-case ι-reduction at every step. Kept private: only
/// [`declare_prob_complement`] needs it.
fn sum_range_split(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    pf: ExprId,
    m: ExprId,
    j: ExprId,
) -> (ExprId, ExprId) {
    let g = shifted(d, pf, m);
    let sum_p_m = rsum_range(d, p, pf, m);

    let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let bound = d.add(m, x);
        let lhs = rsum_range(d, p, pf, bound);
        let tail = rsum_range(d, p, g, x);
        let rhs = radd(d, sum_p_m, tail);
        super::ops::req(d, lhs, rhs)
    };
    let stmt = motive(d, j);

    let proof = d.induct(
        &motive,
        &|d| {
            let zero_r = rzero(d, p);
            let rhs = radd(d, sum_p_m, zero_r);
            let h = d.lemma(p.add_zero, &[sum_p_m]);
            // h : Eq Rat rhs sum_p_m (`add_zero`); flip to Eq Rat sum_p_m rhs.
            rsymm(d, rhs, sum_p_m, h)
        },
        &|d, k, ih| {
            let mk = d.add(m, k);
            let p_mk = d.apply(pf, &[mk]);
            let sum_g_k = rsum_range(d, p, g, k);

            let sum_pf_mk = rsum_range(d, p, pf, mk);
            let start = radd(d, sum_pf_mk, p_mk);
            let sum_p_m_g_k = radd(d, sum_p_m, sum_g_k);
            let mid = radd(d, sum_p_m_g_k, p_mk);
            let sum_pf_mk2 = rsum_range(d, p, pf, mk);
            let sum_p_m_g_k2 = radd(d, sum_p_m, sum_g_k);
            let h1 = super::ops::rcongr(d, sum_pf_mk2, sum_p_m_g_k2, ih, &|d, t| radd(d, t, p_mk));

            let sum_g_k_p_mk = radd(d, sum_g_k, p_mk);
            let end = radd(d, sum_p_m, sum_g_k_p_mk);
            let h2 = d.lemma(p.add_assoc, &[sum_p_m, sum_g_k, p_mk]);

            let (_e, chained) = super::ops::rchain(d, start, &[(mid, h1), (end, h2)]);
            chained
        },
        j,
    );
    (stmt, proof)
}

/// `Rat.prob_complement : ∀ p m j, IsDistribution p (m+j) → sumRange p m +
/// sumRange (fun k => p (m+k)) j = one` — the mass of a prefix of length `m`
/// and its complementary tail (length `j`) sum to `1`.
///
/// The general "sum over an arbitrary sub-range" needs machinery
/// ([`Nat` subtraction reasoning about an arbitrary `m ≤ n`]) this slice does
/// not build; this is the prefix form the task allows, via
/// [`sum_range_split`].
fn declare_prob_complement(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = rat_ty(d);
    let fn_ty = d.arrow(nat, carrier);

    let pf_fv = d.fresh_fvar();
    let pf = d.kernel().fvar(pf_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let j_fv = d.fresh_fvar();
    let j = d.kernel().fvar(j_fv);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let bound = d.add(m, j);
    let dist_ty = is_distribution(d, p, pf, bound);

    let (nonneg_part, sum_part) = is_distribution_parts(d, p, pf, bound);
    let h_sum = d.and_right(nonneg_part, sum_part, h);

    let (_split_stmt, split_proof) = sum_range_split(d, p, pf, m, j);
    let g = shifted(d, pf, m);
    let sum_pf_m = rsum_range(d, p, pf, m);
    let sum_g_j = rsum_range(d, p, g, j);
    let target = radd(d, sum_pf_m, sum_g_j);
    let sum_bound = rsum_range(d, p, pf, bound);

    let split_rev = rsymm(d, sum_bound, target, split_proof);
    let one_r = rone(d, p);
    let final_proof = rtrans(d, target, sum_bound, one_r, split_rev, h_sum);
    let one_r2 = rone(d, p);
    let concl = super::ops::req(d, target, one_r2);

    let value = {
        let with_h = d.lam_fv(h_fv, dist_ty, final_proof);
        let with_j = d.lam_fv(j_fv, nat, with_h);
        let with_m = d.lam_fv(m_fv, nat, with_j);
        d.lam_fv(pf_fv, fn_ty, with_m)
    };
    let ty = {
        let inner = d.arrow(dist_ty, concl);
        let with_j = d.pi_fv(j_fv, nat, inner);
        let with_m = d.pi_fv(m_fv, nat, with_j);
        d.pi_fv(pf_fv, fn_ty, with_m)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.prob_complement,
        uparams: vec![],
        ty,
        value,
    })
}
