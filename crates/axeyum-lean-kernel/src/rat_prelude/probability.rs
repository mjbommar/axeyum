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
    nat_eq_to_rat, radd, rat_eq_rewrite, rat_ty, rchain, rcongr, req, rle, rmul, rone, rsum_range,
    rsymm, rtrans, rzero,
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

/// Delta height for `Rat.expectation` and `Rat.uniform`: above
/// `Rat.IsDistribution` ([`PROB_HEIGHT`], 35). Neither calls the other, so
/// they share one height, both above everything else this prelude has
/// declared so far.
const EXPECTATION_HEIGHT: u16 = 36;

/// Declare `Rat.IsDistribution`, `Rat.expectation`, `Rat.uniform`, and
/// everything this file proves about them.
///
/// # Errors
///
/// Returns the trusted gate's rejection — an `Err` means the kernel
/// **refused** a proof, not that a script gave up.
pub(super) fn declare_probability(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    declare_is_distribution(d, p)?;
    declare_prob_le_one(d, p)?;
    declare_prob_complement(d, p)?;
    declare_expectation(d, p)?;
    declare_expectation_add(d, p)?;
    declare_expectation_smul(d, p)?;
    declare_expectation_const(d, p)?;
    declare_uniform(d, p)?;
    declare_uniform_is_distribution(d, p)?;
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

// --- expectation and its linearity -----------------------------------------

/// `Rat.expectation X p n`, i.e. `d.const_app(p.expectation, &[x, pf, n])`.
fn expectation(d: &mut IntDev<'_>, p: RatPrelude, x: ExprId, pf: ExprId, n: ExprId) -> ExprId {
    d.const_app(p.expectation, &[x, pf, n])
}

/// `fun (_ : Nat) => c`.
fn const_fn(d: &mut IntDev<'_>, c: ExprId) -> ExprId {
    let k_fv = d.fresh_fvar();
    let nat = d.nat_ty();
    d.lam_fv(k_fv, nat, c)
}

/// `fun k => x k * pf k` — the summand [`declare_expectation`] admits
/// `Rat.expectation` as, rebuilt here (mirroring
/// [`super::probability::is_distribution_parts`]'s own reason: callers need
/// the exact literal shape `Rat.expectation` unfolds to, not a re-declared
/// stand-in).
fn weighted(d: &mut IntDev<'_>, x: ExprId, pf: ExprId) -> ExprId {
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let xk = d.apply(x, &[k]);
    let pk = d.apply(pf, &[k]);
    let body = rmul(d, xk, pk);
    let nat = d.nat_ty();
    d.lam_fv(k_fv, nat, body)
}

/// `fun k => x k + y k`.
fn combined(d: &mut IntDev<'_>, x: ExprId, y: ExprId) -> ExprId {
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let xk = d.apply(x, &[k]);
    let yk = d.apply(y, &[k]);
    let body = radd(d, xk, yk);
    let nat = d.nat_ty();
    d.lam_fv(k_fv, nat, body)
}

/// `fun k => x k * pf k + y k * pf k`.
fn split_weighted(d: &mut IntDev<'_>, x: ExprId, y: ExprId, pf: ExprId) -> ExprId {
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let xk = d.apply(x, &[k]);
    let yk = d.apply(y, &[k]);
    let pk = d.apply(pf, &[k]);
    let xkpk = rmul(d, xk, pk);
    let ykpk = rmul(d, yk, pk);
    let body = radd(d, xkpk, ykpk);
    let nat = d.nat_ty();
    d.lam_fv(k_fv, nat, body)
}

/// `fun k => a * x k`.
fn scale_fn(d: &mut IntDev<'_>, a: ExprId, x: ExprId) -> ExprId {
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let xk = d.apply(x, &[k]);
    let body = rmul(d, a, xk);
    let nat = d.nat_ty();
    d.lam_fv(k_fv, nat, body)
}

/// `fun k => a * (x k * pf k)`.
fn scale_weighted(d: &mut IntDev<'_>, a: ExprId, x: ExprId, pf: ExprId) -> ExprId {
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let xk = d.apply(x, &[k]);
    let pk = d.apply(pf, &[k]);
    let xkpk = rmul(d, xk, pk);
    let body = rmul(d, a, xkpk);
    let nat = d.nat_ty();
    d.lam_fv(k_fv, nat, body)
}

/// Admit `Rat.expectation : (Nat → Rat) → (Nat → Rat) → Nat → Rat := fun X p
/// n => sumRange (fun k => X k * p k) n`.
fn declare_expectation(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = rat_ty(d);
    let fn_ty = d.arrow(nat, carrier);

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let pf_fv = d.fresh_fvar();
    let pf = d.kernel().fvar(pf_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let summand = weighted(d, x, pf);
    let body = rsum_range(d, p, summand, n);
    let value = {
        let with_n = d.lam_fv(n_fv, nat, body);
        let with_pf = d.lam_fv(pf_fv, fn_ty, with_n);
        d.lam_fv(x_fv, fn_ty, with_pf)
    };
    let ty = {
        let inner = d.arrow(nat, carrier);
        let over_pf = d.arrow(fn_ty, inner);
        d.arrow(fn_ty, over_pf)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.expectation,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(EXPECTATION_HEIGHT),
    })
}

/// `Rat.expectation_add : ∀ X Y p n,
/// expectation (fun k => X k + Y k) p n = expectation X p n + expectation Y p n`.
///
/// The additive half of linearity. [`RatPrelude::right_distrib`] distributes
/// the summand pointwise (via `sumRange_congr`), then
/// [`RatPrelude::sum_range_add`] splits the sum — no rearrangement lemma
/// needed, since the two scalar-free sums land directly on the goal's two
/// sides.
fn declare_expectation_add(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = rat_ty(d);
    let fn_ty = d.arrow(nat, carrier);

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let y_fv = d.fresh_fvar();
    let y = d.kernel().fvar(y_fv);
    let pf_fv = d.fresh_fvar();
    let pf = d.kernel().fvar(pf_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let xy = combined(d, x, y);
    let lhs = expectation(d, p, xy, pf, n);
    let ex = expectation(d, p, x, pf, n);
    let ey = expectation(d, p, y, pf, n);
    let rhs = radd(d, ex, ey);
    let stmt = req(d, lhs, rhs);

    // sumRange (fun k => (X k+Y k)*p k) n = sumRange (fun k => X k*p k + Y k*p k) n
    let combined_summand = weighted(d, xy, pf);
    let target_summand = split_weighted(d, x, y, pf);
    let pointwise = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let xk = d.apply(x, &[k]);
        let yk = d.apply(y, &[k]);
        let pk = d.apply(pf, &[k]);
        let body = d.lemma(p.right_distrib, &[xk, yk, pk]);
        d.lam_fv(k_fv, nat, body)
    };
    let congr_step = d.lemma(
        p.sum_range_congr,
        &[combined_summand, target_summand, n, pointwise],
    );

    // sumRange (fun k => X k*p k + Y k*p k) n = sumRange fX n + sumRange fY n
    let fx = weighted(d, x, pf);
    let fy = weighted(d, y, pf);
    let add_step = d.lemma(p.sum_range_add, &[fx, fy, n]);

    let sum_combined = rsum_range(d, p, combined_summand, n);
    let sum_target = rsum_range(d, p, target_summand, n);
    let (_e, proof) = rchain(
        d,
        sum_combined,
        &[(sum_target, congr_step), (rhs, add_step)],
    );

    let value = {
        let with_n = d.lam_fv(n_fv, nat, proof);
        let with_pf = d.lam_fv(pf_fv, fn_ty, with_n);
        let with_y = d.lam_fv(y_fv, fn_ty, with_pf);
        d.lam_fv(x_fv, fn_ty, with_y)
    };
    let ty = {
        let with_n = d.pi_fv(n_fv, nat, stmt);
        let with_pf = d.pi_fv(pf_fv, fn_ty, with_n);
        let with_y = d.pi_fv(y_fv, fn_ty, with_pf);
        d.pi_fv(x_fv, fn_ty, with_y)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.expectation_add,
        uparams: vec![],
        ty,
        value,
    })
}

/// `Rat.expectation_smul : ∀ a X p n,
/// expectation (fun k => a * X k) p n = a * expectation X p n`.
///
/// The scalar half of linearity. [`RatPrelude::mul_assoc`] regroups the
/// summand pointwise, then [`RatPrelude::mul_sum_range`] pulls the constant
/// back out of the sum.
fn declare_expectation_smul(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = rat_ty(d);
    let fn_ty = d.arrow(nat, carrier);

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let pf_fv = d.fresh_fvar();
    let pf = d.kernel().fvar(pf_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let scaled_x = scale_fn(d, a, x);
    let lhs = expectation(d, p, scaled_x, pf, n);
    let ex = expectation(d, p, x, pf, n);
    let rhs = rmul(d, a, ex);
    let stmt = req(d, lhs, rhs);

    // sumRange (fun k => (a*X k)*p k) n = sumRange (fun k => a*(X k*p k)) n
    let combined_summand = weighted(d, scaled_x, pf);
    let regrouped_summand = scale_weighted(d, a, x, pf);
    let pointwise = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let xk = d.apply(x, &[k]);
        let pk = d.apply(pf, &[k]);
        let body = d.lemma(p.mul_assoc, &[a, xk, pk]);
        d.lam_fv(k_fv, nat, body)
    };
    let congr_step = d.lemma(
        p.sum_range_congr,
        &[combined_summand, regrouped_summand, n, pointwise],
    );

    // sumRange (fun k => a*(X k*p k)) n = a * sumRange (fun k => X k*p k) n
    let fx = weighted(d, x, pf);
    let mul_step = d.lemma(p.mul_sum_range, &[a, fx, n]);
    let sum_fx = rsum_range(d, p, fx, n);
    let a_sum_fx = rmul(d, a, sum_fx);
    let sum_regrouped = rsum_range(d, p, regrouped_summand, n);
    let mul_step_rev = rsymm(d, a_sum_fx, sum_regrouped, mul_step);

    let sum_combined = rsum_range(d, p, combined_summand, n);
    let (_e, proof) = rchain(
        d,
        sum_combined,
        &[(sum_regrouped, congr_step), (a_sum_fx, mul_step_rev)],
    );

    let value = {
        let with_n = d.lam_fv(n_fv, nat, proof);
        let with_pf = d.lam_fv(pf_fv, fn_ty, with_n);
        let with_x = d.lam_fv(x_fv, fn_ty, with_pf);
        d.lam_fv(a_fv, carrier, with_x)
    };
    let ty = {
        let with_n = d.pi_fv(n_fv, nat, stmt);
        let with_pf = d.pi_fv(pf_fv, fn_ty, with_n);
        let with_x = d.pi_fv(x_fv, fn_ty, with_pf);
        d.pi_fv(a_fv, carrier, with_x)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.expectation_smul,
        uparams: vec![],
        ty,
        value,
    })
}

/// `Rat.expectation_const : ∀ c p n, IsDistribution p n →
/// expectation (fun _ => c) p n = c`.
///
/// The first theorem in this file that *uses* `IsDistribution`'s
/// `sumRange p n = one` component rather than only carrying it.
fn declare_expectation_const(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = rat_ty(d);
    let fn_ty = d.arrow(nat, carrier);

    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let pf_fv = d.fresh_fvar();
    let pf = d.kernel().fvar(pf_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let const_c = const_fn(d, c);
    let lhs = expectation(d, p, const_c, pf, n);
    let dist_ty = is_distribution(d, p, pf, n);
    let stmt_body = req(d, lhs, c);
    let stmt = d.arrow(dist_ty, stmt_body);

    let (nonneg_part, sum_part) = is_distribution_parts(d, p, pf, n);
    let h_sum = d.and_right(nonneg_part, sum_part, h);

    let summand = weighted(d, const_c, pf);
    let sum_summand = rsum_range(d, p, summand, n);
    let sum_pf = rsum_range(d, p, pf, n);
    let c_sum_pf = rmul(d, c, sum_pf);

    let mul_step = d.lemma(p.mul_sum_range, &[c, pf, n]);
    let mul_step_rev = rsymm(d, c_sum_pf, sum_summand, mul_step);

    let one_r = rone(d, p);
    let c_one = rmul(d, c, one_r);
    let congr_c = rcongr(d, sum_pf, one_r, h_sum, &|d, t| rmul(d, c, t));
    let mul_one_step = d.lemma(p.mul_one, &[c]);

    let (_e, chained) = rchain(
        d,
        sum_summand,
        &[
            (c_sum_pf, mul_step_rev),
            (c_one, congr_c),
            (c, mul_one_step),
        ],
    );

    let value = {
        let with_h = d.lam_fv(h_fv, dist_ty, chained);
        let with_n = d.lam_fv(n_fv, nat, with_h);
        let with_pf = d.lam_fv(pf_fv, fn_ty, with_n);
        d.lam_fv(c_fv, carrier, with_pf)
    };
    let ty = {
        let with_h = d.arrow(dist_ty, stmt_body);
        let with_n = d.pi_fv(n_fv, nat, with_h);
        let with_pf = d.pi_fv(pf_fv, fn_ty, with_n);
        d.pi_fv(c_fv, carrier, with_pf)
    };
    let _ = stmt;
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.expectation_const,
        uparams: vec![],
        ty,
        value,
    })
}

// --- the uniform distribution ------------------------------------------------

/// `Rat.natDivSucc n 0` — `n` seen as a rational.
fn nat_as_rat(d: &mut IntDev<'_>, p: RatPrelude, n: ExprId) -> ExprId {
    let zero_nat = d.num(0);
    d.const_app(p.nat_div_succ, &[n, zero_nat])
}

/// `And.intro left right lp rp : And left right`.
fn and_intro(d: &mut IntDev<'_>, left: ExprId, right: ExprId, lp: ExprId, rp: ExprId) -> ExprId {
    let intro = d.int().logic.and_intro;
    d.const_app(intro, &[left, right, lp, rp])
}

/// `Eq Rat (Rat.natDivSucc Nat.zero Nat.zero) Rat.zero` — `Rat.self_normalize`
/// applied to `Rat.zero` itself: `num`/`den` are structure projections of
/// `Rat.zero`'s direct `Rat.mk`, so they reduce to exactly `natDivSucc`'s own
/// inputs (`0`, `1`), and `normalize`'s `1 ≤ den` argument is proof-irrelevant
/// — no gcd/cross-multiplication reasoning needed. The zero-companion of
/// `CReal.ratUnitEqOne`'s technique for `Rat.one`, reproduced here (not
/// reused: `Rat` cannot depend on `CReal`).
fn nat_div_succ_zero_eq_zero(d: &mut IntDev<'_>, p: RatPrelude) -> ExprId {
    let zero_r = rzero(d, p);
    d.lemma(p.self_normalize, &[zero_r])
}

/// `Eq Rat (Rat.natDivSucc 1 Nat.zero) Rat.one` — `CReal.ratUnitEqOne`'s own
/// technique, reproduced here for the same reason.
fn nat_div_succ_one_eq_one(d: &mut IntDev<'_>, p: RatPrelude) -> ExprId {
    let one_r = rone(d, p);
    d.lemma(p.self_normalize, &[one_r])
}

/// `Eq Rat (Rat.mul Rat.zero c) Rat.zero`, via `mul_comm` then `mul_zero` —
/// there is no standalone `zero_mul` law in this prelude.
fn rat_zero_mul(d: &mut IntDev<'_>, p: RatPrelude, c: ExprId) -> ExprId {
    let zero_r = rzero(d, p);
    let lhs = rmul(d, zero_r, c);
    let flipped = rmul(d, c, zero_r);
    let step1 = d.lemma(p.mul_comm, &[zero_r, c]);
    let step2 = d.lemma(p.mul_zero, &[c]);
    rtrans(d, lhs, flipped, zero_r, step1, step2)
}

/// `Eq Rat (sumRange (fun _ => c) j) (Rat.mul (natDivSucc j 0) c)` — `j`
/// copies of a constant `c` sum to `j` (seen as a rational) times `c`.
/// Induction on `j`, `c` fixed; [`declare_uniform_is_distribution`]
/// specialises at `j = n`, `c = inv (natDivSucc n 0)`, and closes with
/// `mul_inv_cancel`.
fn sum_range_const(d: &mut IntDev<'_>, p: RatPrelude, c: ExprId, j: ExprId) -> (ExprId, ExprId) {
    let constf = const_fn(d, c);

    let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let lhs = rsum_range(d, p, constf, x);
        let nx = nat_as_rat(d, p, x);
        let rhs = rmul(d, nx, c);
        req(d, lhs, rhs)
    };
    let stmt = motive(d, j);

    let proof = d.induct(
        &motive,
        &|d| {
            let zero_r = rzero(d, p);
            let zero_n = d.zero();
            let nz = nat_as_rat(d, p, zero_n);
            let nz_c = rmul(d, nz, c);
            let zero_c = rmul(d, zero_r, c);

            let zero_mul_c = rat_zero_mul(d, p, c); // Eq(zero*c, zero)
            let step1 = rsymm(d, zero_c, zero_r, zero_mul_c); // Eq(zero, zero*c)

            let nz_eq_zero = nat_div_succ_zero_eq_zero(d, p); // ~ Eq(nz, zero)
            let zero_eq_nz = rsymm(d, nz, zero_r, nz_eq_zero); // ~ Eq(zero, nz)
            let step2 = rcongr(d, zero_r, nz, zero_eq_nz, &|d, t| rmul(d, t, c)); // Eq(zero*c, nz*c)

            let (_e, chained) = rchain(d, zero_r, &[(zero_c, step1), (nz_c, step2)]);
            chained
        },
        &|d, m, ih| {
            let nm = nat_as_rat(d, p, m);
            let ih_rhs = rmul(d, nm, c);
            let prior_sum = rsum_range(d, p, constf, m);
            let start = radd(d, prior_sum, c);

            let h1 = rcongr(d, prior_sum, ih_rhs, ih, &|d, t| radd(d, t, c));
            let after_ih = radd(d, ih_rhs, c);

            let one_nat = d.num(1);
            let zero_nat = d.num(0);
            let unit = d.const_app(p.nat_div_succ, &[one_nat, zero_nat]);
            let unit_c = rmul(d, unit, c);

            // c = unit*c, via unit = one [self_normalize] then mul_comm/mul_one.
            let unit_mul_c_eq_c = {
                let one_r = rone(d, p);
                let unit_eq_one = nat_div_succ_one_eq_one(d, p); // ~ Eq(unit, one)
                let step_a = rcongr(d, unit, one_r, unit_eq_one, &|d, t| rmul(d, t, c));
                let one_c = rmul(d, one_r, c);
                let c_one = rmul(d, c, one_r);
                let step_b = d.lemma(p.mul_comm, &[one_r, c]);
                let step_c = d.lemma(p.mul_one, &[c]);
                let (_e, ch) = rchain(d, unit_c, &[(one_c, step_a), (c_one, step_b), (c, step_c)]);
                ch
            };
            let c_eq_unit_c = rsymm(d, unit_c, c, unit_mul_c_eq_c);
            let h2 = rcongr(d, c, unit_c, c_eq_unit_c, &|d, t| radd(d, ih_rhs, t));
            let after_h2 = radd(d, ih_rhs, unit_c);

            // nm*c + unit*c = (nm+unit)*c
            let nm_plus_unit = radd(d, nm, unit);
            let nm_plus_unit_c = rmul(d, nm_plus_unit, c);
            let right_distrib_step = d.lemma(p.right_distrib, &[nm, unit, c]);
            let h3 = rsymm(d, nm_plus_unit_c, after_h2, right_distrib_step);

            // (nm+unit)*c = natDivSucc(succ m, 0)*c, via natDivSucc_add and
            // `Nat.add m 1` defeq `Nat.succ m`.
            let sm = d.succ(m);
            let nsm = nat_as_rat(d, p, sm);
            let add_eq = d.lemma(p.nat_div_succ_add, &[m, one_nat, zero_nat]);
            let h4 = rcongr(d, nm_plus_unit, nsm, add_eq, &|d, t| rmul(d, t, c));
            let target = rmul(d, nsm, c);

            let (_e, chained) = rchain(
                d,
                start,
                &[
                    (after_ih, h1),
                    (after_h2, h2),
                    (nm_plus_unit_c, h3),
                    (target, h4),
                ],
            );
            chained
        },
        j,
    );
    (stmt, proof)
}

/// Admit `Rat.uniform : Nat → Nat → Rat := fun n k => Rat.inv (Rat.natDivSucc
/// n 0)` — the uniform distribution on `n` outcomes, `k` unused.
fn declare_uniform(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = rat_ty(d);

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let k_fv = d.fresh_fvar();

    let n_as_rat = nat_as_rat(d, p, n);
    let body = d.const_app(p.inv, &[n_as_rat]);
    let value = {
        let with_k = d.lam_fv(k_fv, nat, body);
        d.lam_fv(n_fv, nat, with_k)
    };
    let ty = {
        let over_k = d.arrow(nat, carrier);
        d.arrow(nat, over_k)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.uniform,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(EXPECTATION_HEIGHT),
    })
}

/// `Rat.uniform_is_distribution : ∀ n, Nat.lt Nat.zero n →
/// IsDistribution (uniform n) n`.
///
/// **The negative control [`RatPrelude::is_distribution`] needs**: without an
/// instance, every `IsDistribution` theorem is vacuously true. `0 < n`
/// rather than `n ≠ 0` because that is exactly the hypothesis
/// [`RatPrelude::nat_div_succ_pos`] wants, and `Nat.lt Nat.zero n` is
/// definitionally `Nat.le 1 n` — no conversion lemma needed, the hypothesis
/// is passed straight through.
fn declare_uniform_is_distribution(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let zero_n = d.zero();
    let pos_ty = d.lt(zero_n, n);

    let uniform_n = d.const_app(p.uniform, &[n]);
    let dist_ty = is_distribution(d, p, uniform_n, n);

    let n_as_rat = nat_as_rat(d, p, n);
    let n_pos = d.lemma(p.nat_div_succ_pos, &[n, zero_n, h]);
    let c = d.const_app(p.inv, &[n_as_rat]);

    let (nonneg_ty, sum_ty) = is_distribution_parts(d, p, uniform_n, n);

    let nonneg_proof = {
        let inv_pos = d.lemma(p.inv_pos, &[n_as_rat, n_pos]);
        let zero_r = rzero(d, p);
        let le_proof = d.lemma(p.le_of_lt, &[zero_r, c, inv_pos]);
        let k_fv = d.fresh_fvar();
        let klt_fv = d.fresh_fvar();
        let klt_ty = {
            let k = d.kernel().fvar(k_fv);
            d.lt(k, n)
        };
        let with_klt = d.lam_fv(klt_fv, klt_ty, le_proof);
        d.lam_fv(k_fv, nat, with_klt)
    };

    let sum_proof = {
        let (_stmt_sc, proof_sc) = sum_range_const(d, p, c, n);
        let constant_summand = const_fn(d, c);
        let a = rsum_range(d, p, constant_summand, n);
        let b = rmul(d, n_as_rat, c);
        let one_r = rone(d, p);
        let mul_inv = d.lemma(p.mul_inv_cancel, &[n_as_rat, n_pos]);
        rtrans(d, a, b, one_r, proof_sc, mul_inv)
    };

    let body = and_intro(d, nonneg_ty, sum_ty, nonneg_proof, sum_proof);

    let value = {
        let with_h = d.lam_fv(h_fv, pos_ty, body);
        d.lam_fv(n_fv, nat, with_h)
    };
    let ty = {
        let with_h = d.arrow(pos_ty, dist_ty);
        d.pi_fv(n_fv, nat, with_h)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.uniform_is_distribution,
        uparams: vec![],
        ty,
        value,
    })
}
