//! The irrationality of `√2` — Euclid Book X, the oldest surviving theorem of
//! pure mathematics — stated the way this kernel can actually check it: purely
//! over `Nat`, with no real `sqrt` and no rational embedding.
//!
//! `CReal.sqrt` does not exist in this kernel, and adding "therefore √2 is
//! irrational" would need it plus a rational embedding. The content of the
//! classical theorem is entirely captured by
//!
//! Corrected 2026-08-31, kernel-measured: `CReal.sqrt` now exists (landed
//! 2026-08-23, `creal/sqrt.rs`, total, axiom-free). This file's route below
//! is unaffected -- it deliberately proves the `Nat`-only statement rather
//! than composing `CReal.sqrt` with a rational embedding, so nothing here
//! needed to change.
//! <!-- was-absent: CReal.sqrt -- landed 2026-08-23, this file's Nat-only route is unaffected -->
//!
//! ```text
//! Nat.no_rational_sqrt_two : ∀ p q, q ≠ 0 → p·p ≠ 2·(q·q)
//! ```
//!
//! (`p/q = √2 ⟺ p² = 2q²`, so no such `p,q` is exactly "`√2` is irrational"
//! restated without ever introducing `Real` or `Rat`.) The `q ≠ 0` hypothesis
//! is load-bearing: `p = q = 0` satisfies `p·p = 2·(q·q)` without it.
//!
//! ## Route: `euclid_lemma`-flavoured evenness, then infinite descent
//!
//! [`Nat.even_of_even_sq`] (`2 ∣ p·p → 2 ∣ p`) is proved via `gcd p 2 ∈ {1,2}`
//! (the two divisors of the literal `2`, `dvd_two_pow_classify` at `k=1`'s
//! shape spelled out directly rather than reproduced, since the existing
//! spelling — `perfect.rs`'s `divisors_of_two` — is `fn`-private to its own
//! file) plus `gauss_lemma`: if `gcd(2,p)=1`, `gauss_lemma` cancels the coprime
//! factor `p` from `2 ∣ p·p` directly, giving `2 ∣ p`; if `gcd(2,p)=2`, `2 ∣ p`
//! is `gcd_dvd_right` after substituting. This never needs to assemble the
//! `Prime` predicate `euclid_lemma` itself requires (`2 ≤ x ∧ ∀ d, d∣x→d=1∨d=x`)
//! for the literal `2` — a small variant of the same `euclid_lemma`/`primes.rs`
//! family, one layer down.
//!
//! `Nat.no_rational_sqrt_two` then follows by **infinite descent**
//! (`WellFounded.fix` over `lt_well_founded`, the same combinator `Nat.gcd`
//! and `Nat.exists_prime_factorization` use), recursing on `q`: given
//! `p·p = 2·(q·q)`, evenness gives `p = 2·r`; substituting and cancelling a
//! factor of `2` gives `q·q = 2·(r·r)` — the same shape, one step down. `r < q`
//! is derived from that very equation (`q·q = 2·(r·r) > r·r` whenever `r ≠ 0`,
//! so `q > r`, via the monotonicity contrapositive `lt_or_ge` +
//! `mul_le_mul_left`); `r = 0` is a direct contradiction against `q ≠ 0`
//! (`q·q = 2·(0·0) = 0`). No case ever needs a *second* recursive step beyond
//! the one `WellFounded.fix`'s own hypothesis already supplies.

use super::NatPrelude;
use super::helpers::transport_dvd_left;
use super::ops::{NatDev, NatOps, two_divisor_dichotomy};
use super::steps::absurd;
use super::steps::dvd_elim;
use super::steps::dvd_intro;
use crate::BinderInfo;
use crate::KernelError;
use crate::expr::ExprId;

// ============================================================================
// Small shared combinators (local copies of the per-file convention this
// prelude already uses for `Exists`/`Or`/`False` elimination — see
// `perfect.rs`'s `dvd_elim`/`dvd_intro`/`absurd` and `primes.rs`'s `or_cases`).
// ============================================================================

/// Non-dependent `Or.rec`: `left_case : arrow(left_ty,goal)`,
/// `right_case : arrow(right_ty,goal)`, `or_proof : Or(left_ty,right_ty) ⊢ goal`.
#[allow(clippy::too_many_arguments)]
fn or_elim(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    left_ty: ExprId,
    right_ty: ExprId,
    goal: ExprId,
    left_case: ExprId,
    right_case: ExprId,
    or_proof: ExprId,
) -> ExprId {
    let anon = d.anon_name();
    let or_ty = d.const_app(p.logic.or, &[left_ty, right_ty]);
    let motive = d.kernel().lam(anon, or_ty, goal, BinderInfo::Default);
    let or_rec = d.kernel().const_(p.logic.or_rec, vec![]);
    d.apply(
        or_rec,
        &[left_ty, right_ty, motive, left_case, right_case, or_proof],
    )
}

// ============================================================================
// `Nat.even_of_even_sq : ∀ n, dvd 2 (mul n n) → dvd 2 n`.
// ============================================================================

/// `Nat.even_of_even_sq : ∀ n, dvd 2 (mul n n) → dvd 2 n`.
///
/// Case on `gcd(2,n) ∈ {1,2}` ([`two_divisor_dichotomy`](super::ops::two_divisor_dichotomy) applied to
/// `gcd_dvd_left 2 n : dvd (gcd 2 n) 2`): if `gcd(2,n)=1`, `gauss_lemma 2 n n`
/// cancels the coprime factor `n` from `2 ∣ n·n` directly, giving `2 ∣ n`; if
/// `gcd(2,n)=2`, `2 ∣ n` is `gcd_dvd_right 2 n` after substituting.
pub(super) fn declare_even_of_even_sq(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.even_of_even_sq, 1, &|d, values| {
        let n = values[0];
        let two = d.num(2);
        let nn = d.mul(n, n);
        let hyp_ty = d.dvd(two, nn);
        let goal = d.dvd(two, n);

        let c = d.gcd(two, n);
        let dvd_c2 = d.lemma(p.gcd_dvd_left, &[two, n]);
        let dichotomy = two_divisor_dichotomy(d, &p, c, dvd_c2);

        let one = d.num(1);
        let left_ty = d.eq(c, one);
        let right_ty = d.eq(c, two);

        let hyp_fv = d.fresh_fvar();
        let hyp = d.kernel().fvar(hyp_fv);

        let left_branch = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let result = d.lemma(p.gauss_lemma, &[two, n, n, h, hyp]);
            d.lam_fv(h_fv, left_ty, result)
        };
        let right_branch = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let gcd_dvd_n = d.lemma(p.gcd_dvd_right, &[two, n]);
            let result = transport_dvd_left(d, c, two, h, n, gcd_dvd_n);
            d.lam_fv(h_fv, right_ty, result)
        };
        let case_result = or_elim(
            d,
            &p,
            left_ty,
            right_ty,
            goal,
            left_branch,
            right_branch,
            dichotomy,
        );
        let proof = d.lam_fv(hyp_fv, hyp_ty, case_result);
        let stmt = d.arrow(hyp_ty, goal);
        (stmt, proof)
    })?;
    Ok(())
}

// ============================================================================
// `Nat.no_rational_sqrt_two : ∀ p q, q ≠ 0 → p·p ≠ 2·(q·q)`.
// ============================================================================

/// `(mul two r)·(mul two r) = mul two (mul two (mul r r))` — pure
/// associativity/commutativity, no cancellation. Returns `(target, proof)`.
fn double_sq_expand(d: &mut NatDev<'_>, p: &NatPrelude, r: ExprId) -> (ExprId, ExprId) {
    let p = *p;
    let two = d.num(2);
    let a = d.mul(two, r);
    let start = d.mul(a, a);

    // (two*r)*a = two*(r*a)
    let step1 = d.lemma(p.mul_assoc, &[two, r, a]);
    let ra = d.mul(r, a);
    let x1 = d.mul(two, ra);

    // r*a = a*r (mul_comm), wrapped under the outer `two*_`.
    let comm = d.lemma(p.mul_comm, &[r, a]);
    let ar = d.mul(a, r);
    let step2 = d.congr(ra, ar, comm, &|d, t| d.mul(two, t));
    let x2 = d.mul(two, ar);

    // a*r = (two*r)*r = two*(r*r), wrapped under the outer `two*_`.
    let assoc2 = d.lemma(p.mul_assoc, &[two, r, r]);
    let rr = d.mul(r, r);
    let two_rr = d.mul(two, rr);
    let target = d.mul(two, two_rr);
    let step3 = d.congr(ar, two_rr, assoc2, &|d, t| d.mul(two, t));

    let (_e, proof) = d.chain(start, &[(x1, step1), (x2, step2), (target, step3)]);
    (target, proof)
}

/// Given `hle : le (mul two (mul a a)) (mul a a)` and `a_ne_zero : arrow(Eq a
/// zero, False)`, derive `False`. `2·(a·a) ≤ a·a` forces `a·a = 0` (via
/// `2·(a·a) = (a·a)+(a·a)`, `le_of_add_le_add_left`, `le_antisymm` against
/// `zero_le`), hence `a = 0` (`mul_eq_zero`), contradicting `a_ne_zero`.
fn contradiction_from_double_le(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    a: ExprId,
    hle: ExprId,
    a_ne_zero: ExprId,
) -> ExprId {
    let p = *p;
    let two = d.num(2);
    let one = d.num(1);
    let zero = d.zero();
    let aa = d.mul(a, a);

    // two*aa = aa+aa
    let succ_mul_step = d.lemma(p.succ_mul, &[one, aa]);
    let one_mul_aa = d.lemma(p.one_mul, &[aa]);
    let one_aa = d.mul(one, aa);
    let add_congr = d.congr(one_aa, aa, one_mul_aa, &|d, t| d.add(t, aa));
    let add_aa_aa = d.add(aa, aa);
    let two_aa = d.mul(two, aa);
    let add_one_aa_aa = d.add(one_aa, aa);
    let (_e, two_mul_eq) = d.chain(
        two_aa,
        &[(add_one_aa_aa, succ_mul_step), (add_aa_aa, add_congr)],
    );

    let motive1 = d.eq_motive(two_aa, &|d, x| d.le(x, aa));
    let hle2 = d.transport(two_aa, motive1, hle, add_aa_aa, two_mul_eq);

    let add_zero_aa = d.lemma(p.add_zero, &[aa]);
    let aa_zero = d.add(aa, zero);
    let rev = d.symm(aa_zero, aa, add_zero_aa);
    let motive2 = d.eq_motive(aa, &|d, x| d.le(add_aa_aa, x));
    let hle3 = d.transport(aa, motive2, hle2, aa_zero, rev);

    let le_aa_zero = d.lemma(p.le_of_add_le_add_left, &[aa, aa, zero, hle3]);
    let zero_le_aa = d.lemma(p.zero_le, &[aa]);
    let aa_eq_zero = d.lemma(p.le_antisymm, &[aa, zero, le_aa_zero, zero_le_aa]);
    let or_a = d.lemma(p.mul_eq_zero, &[a, a, aa_eq_zero]);

    let a_zero_ty = d.eq(a, zero);
    let false_ty = d.kernel().const_(p.logic.false_, vec![]);
    let left_branch = {
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let result = d.apply(a_ne_zero, &[h]);
        d.lam_fv(h_fv, a_zero_ty, result)
    };
    let right_branch = {
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let result = d.apply(a_ne_zero, &[h]);
        d.lam_fv(h_fv, a_zero_ty, result)
    };
    or_elim(
        d,
        &p,
        a_zero_ty,
        a_zero_ty,
        false_ty,
        left_branch,
        right_branch,
        or_a,
    )
}

/// Given `heq : Eq (mul big big) (mul two (mul small small))` and
/// `small_ne_zero`, derive `lt small big`. Case on `lt_or_ge small big`; the
/// `ge` branch derives `le (mul big big) (mul small small)` by monotonicity
/// (`mul_le_mul_left` twice, bridged by `mul_comm`/`le_trans`), substitutes
/// `heq` to get `le (mul two (mul small small)) (mul small small)`, and
/// [`contradiction_from_double_le`] closes it.
fn lt_of_double_sq(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    big: ExprId,
    small: ExprId,
    heq: ExprId,
    small_ne_zero: ExprId,
) -> ExprId {
    let p = *p;
    let two = d.num(2);
    let dichotomy = d.lemma(p.lt_or_ge, &[small, big]);
    let lt_ty = d.lt(small, big);
    let ge_ty = d.le(big, small);

    let left_branch = {
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        d.lam_fv(h_fv, lt_ty, h)
    };
    let right_branch = {
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);

        let le1 = d.lemma(p.mul_le_mul_left, &[big, big, small, h]);
        let comm1 = d.lemma(p.mul_comm, &[big, small]);
        let big_small = d.mul(big, small);
        let big_big = d.mul(big, big);
        let motive_a = d.eq_motive(big_small, &|d, x| d.le(big_big, x));
        let small_big = d.mul(small, big);
        let le1p = d.transport(big_small, motive_a, le1, small_big, comm1);

        let le2 = d.lemma(p.mul_le_mul_left, &[small, big, small, h]);
        let small_small = d.mul(small, small);
        let le_final = d.lemma(p.le_trans, &[big_big, small_big, small_small, le1p, le2]);

        let motive_b = d.eq_motive(big_big, &|d, x| d.le(x, small_small));
        let two_small_small = d.mul(two, small_small);
        let hle = d.transport(big_big, motive_b, le_final, two_small_small, heq);
        let false_proof = contradiction_from_double_le(d, &p, small, hle, small_ne_zero);
        let goal = d.lt(small, big);
        let result = absurd(d, goal, false_proof);
        d.lam_fv(h_fv, ge_ty, result)
    };
    or_elim(
        d,
        &p,
        lt_ty,
        ge_ty,
        lt_ty,
        left_branch,
        right_branch,
        dichotomy,
    )
}

/// `Nat.no_rational_sqrt_two : ∀ p q, q ≠ 0 → p·p ≠ 2·(q·q)`.
///
/// Infinite descent by `WellFounded.fix` over `lt_well_founded`, recursing on
/// `q`. Given `p·p = 2·(q·q)`: `p` is even ([`declare_even_of_even_sq`]), so
/// `p = 2·r`; substituting and cancelling a factor of `2`
/// (`mul_left_cancel_of_pos`) gives `q·q = 2·(r·r)`. Case on `r`: `r = 0`
/// forces `q·q = 0` hence `q = 0`, contradicting `q ≠ 0` directly; `r = succ
/// j` is nonzero, `r < q` follows from `q·q = 2·(r·r)` itself
/// ([`lt_of_double_sq`]), and the well-founded hypothesis applied at `r`
/// (with `P := q`) contradicts `q·q = 2·(r·r)` in one step.
pub(super) fn declare_no_rational_sqrt_two(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let zero_level = d.kernel().level_zero();
    let one = d.level_one();

    // C(x) := ∀ P, arrow(Eq x 0 → False, arrow(Eq (P*P) (2*(x*x)), False))
    let c_at = |d: &mut NatDev<'_>, x: ExprId| -> ExprId {
        let two = d.num(2);
        let zero = d.zero();
        let p_fv = d.fresh_fvar();
        let pv = d.kernel().fvar(p_fv);
        let xx = d.mul(x, x);
        let pp = d.mul(pv, pv);
        let false_ty = d.kernel().const_(p.logic.false_, vec![]);
        let two_xx = d.mul(two, xx);
        let heq_ty = d.eq(pp, two_xx);
        let not_heq = d.arrow(heq_ty, false_ty);
        let x_zero_eq = d.eq(x, zero);
        let x_ne_zero = d.arrow(x_zero_eq, false_ty);
        let body = d.arrow(x_ne_zero, not_heq);
        d.pi_fv(p_fv, nat, body)
    };

    let relation = d.kernel().const_(p.lt, vec![]);
    let family = {
        let q_fv = d.fresh_fvar();
        let qv = d.kernel().fvar(q_fv);
        let body = c_at(d, qv);
        d.lam_fv(q_fv, nat, body)
    };
    let well_founded = d.kernel().const_(p.lt_well_founded, vec![]);

    let ih_ty_at = |d: &mut NatDev<'_>, q: ExprId| -> ExprId {
        let x_fv = d.fresh_fvar();
        let xv = d.kernel().fvar(x_fv);
        let rel = d.lt(xv, q);
        let cx = c_at(d, xv);
        let body = d.arrow(rel, cx);
        d.pi_fv(x_fv, nat, body)
    };

    let step = {
        let q_fv = d.fresh_fvar();
        let qv = d.kernel().fvar(q_fv);
        let wf_ih_ty = ih_ty_at(d, qv);
        let wf_ih_fv = d.fresh_fvar();
        let wf_ih = d.kernel().fvar(wf_ih_fv);

        let two = d.num(2);
        let zero = d.zero();
        let qq = d.mul(qv, qv);
        let false_ty = d.kernel().const_(p.logic.false_, vec![]);

        let p_fv = d.fresh_fvar();
        let pv = d.kernel().fvar(p_fv);
        let pp = d.mul(pv, pv);

        let qv_zero_eq = d.eq(qv, zero);
        let hq_ty = d.arrow(qv_zero_eq, false_ty);
        let hq_fv = d.fresh_fvar();
        let hq = d.kernel().fvar(hq_fv);

        let two_qq = d.mul(two, qq);
        let heq_ty = d.eq(pp, two_qq);
        let heq_fv = d.fresh_fvar();
        let heq = d.kernel().fvar(heq_fv);

        let dvd_p_sq = dvd_intro(d, two, pp, qq, heq);
        let dvd_p = d.lemma(p.even_of_even_sq, &[pv, dvd_p_sq]);

        let body_false = dvd_elim(d, two, pv, false_ty, dvd_p, &|d, r, eq_p| {
            let rr = d.mul(r, r);
            let a = d.mul(two, r);
            let sq_eq = d.congr(pv, a, eq_p, &|d, t| d.mul(t, t));
            let (target, expand_proof) = double_sq_expand(d, &p, r);
            let a_sq = d.mul(a, a);
            let combined = d.trans(pp, a_sq, target, sq_eq, expand_proof);
            let combined2 = {
                let rev = d.symm(pp, target, combined);
                d.trans(target, pp, two_qq, rev, heq)
            };
            let one_ = d.num(1);
            let one_le_two = d.lemma(p.le_succ, &[one_]);
            let two_rr = d.mul(two, rr);
            let cancel = d.lemma(
                p.mul_left_cancel_of_pos,
                &[two, two_rr, qq, one_le_two, combined2],
            );
            let new_eq = d.symm(two_rr, qq, cancel);

            let goal_motive = |d: &mut NatDev<'_>, x: ExprId| -> ExprId {
                let xx = d.mul(x, x);
                let two_xx = d.mul(two, xx);
                let eq_ty = d.eq(qq, two_xx);
                d.arrow(eq_ty, false_ty)
            };
            let base = |d: &mut NatDev<'_>| -> ExprId {
                let zero = d.zero();
                let zero_zero = d.mul(zero, zero);
                let two_zero_zero = d.mul(two, zero_zero);
                let eq_ty = d.eq(qq, two_zero_zero);
                let h_fv = d.fresh_fvar();
                let h = d.kernel().fvar(h_fv);

                let zz = d.lemma(p.zero_mul, &[zero]);
                let step1 = d.congr(zero_zero, zero, zz, &|d, t| d.mul(two, t));
                let two_zero = d.mul(two, zero);
                let step2 = d.lemma(p.mul_zero, &[two]);
                let (_e, rhs_zero) = d.chain(two_zero_zero, &[(two_zero, step1), (zero, step2)]);
                let qq_eq_zero = d.trans(qq, two_zero_zero, zero, h, rhs_zero);
                let or_qz = d.lemma(p.mul_eq_zero, &[qv, qv, qq_eq_zero]);

                let q_zero_ty = d.eq(qv, zero);
                let left_branch2 = {
                    let hh_fv = d.fresh_fvar();
                    let hh = d.kernel().fvar(hh_fv);
                    let res = d.apply(hq, &[hh]);
                    d.lam_fv(hh_fv, q_zero_ty, res)
                };
                let right_branch2 = {
                    let hh_fv = d.fresh_fvar();
                    let hh = d.kernel().fvar(hh_fv);
                    let res = d.apply(hq, &[hh]);
                    d.lam_fv(hh_fv, q_zero_ty, res)
                };
                let false_proof = or_elim(
                    d,
                    &p,
                    q_zero_ty,
                    q_zero_ty,
                    false_ty,
                    left_branch2,
                    right_branch2,
                    or_qz,
                );
                d.lam_fv(h_fv, eq_ty, false_proof)
            };
            let step_r = |d: &mut NatDev<'_>, j: ExprId, _ih: ExprId| -> ExprId {
                let rj = d.succ(j);
                let rj_rj = d.mul(rj, rj);
                let two_rj_rj = d.mul(two, rj_rj);
                let eq_ty = d.eq(qq, two_rj_rj);
                let h_fv = d.fresh_fvar();
                let h = d.kernel().fvar(h_fv);

                let r_ne_zero = {
                    let hh_fv = d.fresh_fvar();
                    let hh = d.kernel().fvar(hh_fv);
                    let zero_ = d.zero();
                    let eq_ty2 = d.eq(rj, zero_);
                    let res = d.lemma(p.succ_ne_zero, &[j, hh]);
                    d.lam_fv(hh_fv, eq_ty2, res)
                };
                let lt_rj_q = lt_of_double_sq(d, &p, qv, rj, h, r_ne_zero);
                let inner = d.apply(wf_ih, &[rj, lt_rj_q]);
                let inner2 = d.apply(inner, &[qv]);
                let inner3 = d.apply(inner2, &[r_ne_zero]);
                let false_proof = d.apply(inner3, &[h]);
                d.lam_fv(h_fv, eq_ty, false_proof)
            };
            let cases_result = d.induct(&goal_motive, &base, &step_r, r);
            d.apply(cases_result, &[new_eq])
        });

        let inner = d.lam_fv(heq_fv, heq_ty, body_false);
        let inner = d.lam_fv(hq_fv, hq_ty, inner);
        let inner = d.lam_fv(p_fv, nat, inner);
        let with_ih = d.lam_fv(wf_ih_fv, wf_ih_ty, inner);
        d.lam_fv(q_fv, nat, with_ih)
    };

    let fix = d
        .kernel()
        .const_(p.logic.well_founded_fix, vec![one, zero_level]);
    let all_q = d.apply(fix, &[nat, relation, family, well_founded, step]);

    d.theorem(p.no_rational_sqrt_two, 2, &|d, values| {
        let (pv, qv) = (values[0], values[1]);
        let two = d.num(2);
        let false_ty = d.kernel().const_(p.logic.false_, vec![]);
        let inst_q = d.apply(all_q, &[qv]);
        let proof = d.apply(inst_q, &[pv]);

        let zero_ = d.zero();
        let qv_zero_eq = d.eq(qv, zero_);
        let hq_ty = d.arrow(qv_zero_eq, false_ty);
        let pv_pv = d.mul(pv, pv);
        let qv_qv = d.mul(qv, qv);
        let two_qv_qv = d.mul(two, qv_qv);
        let heq_ty0 = d.eq(pv_pv, two_qv_qv);
        let heq_ty = d.arrow(heq_ty0, false_ty);
        let stmt = d.arrow(hq_ty, heq_ty);
        (stmt, proof)
    })?;
    Ok(())
}
