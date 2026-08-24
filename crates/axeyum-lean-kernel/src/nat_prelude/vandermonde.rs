//! Vandermonde's convolution over ℕ:
//!
//!   `Nat.choose_add_convolution : ∀ m n k,`
//!     `choose (add m n) k = sumRange (fun i => choose m i * choose n (sub k i)) (succ k)`
//!
//! # Hand check before writing any kernel code
//!
//! `m = n = k = 1`: LHS `= choose 2 1 = 2`. RHS `= choose 1 0 * choose 1 1 +
//! choose 1 1 * choose 1 0 = 1*1 + 1*1 = 2`. Matches.
//!
//! `m = 2, n = 1, k = 2`: LHS `= choose 3 2 = 3`. RHS (three terms, `i =
//! 0,1,2`) `= choose 2 0 * choose 1 2 + choose 2 1 * choose 1 1 + choose 2 2 *
//! choose 1 0 = 1*0 + 2*1 + 1*1 = 0 + 2 + 1 = 3`. Matches (the `i=0` term
//! vanishes because `choose 1 2 = 0`, not because of `Nat.sub` truncation —
//! every `sub k i` here has `i ≤ k` by construction, so it is never
//! truncated in this statement).
//!
//! Both check out, so the identity is proved as stated.
//!
//! # `sumRange_diagonal`: a red herring for this shape
//!
//! [`super::diagonal::declare_sum_range_diagonal`]'s headline relates a
//! DOUBLE sum grouped by antidiagonal to the same double sum grouped by row,
//! for a range of antidiagonals `0..n`. Vandermonde's convolution is a
//! SINGLE sum at one fixed `k` — there is no outer `n`-indexed family of
//! antidiagonals to reindex here, so `sumRange_diagonal` does not apply and
//! is not used below.
//!
//! # Proof shape: induction on `m`, not on `n` or on `m+n`
//!
//! [`super::binomial::declare_combinatorial_identities`]'s module doc records
//! an EARLIER, abandoned exploration that inducts on `n` (the SECOND
//! convolution operand) with `k` generalized, and observes that this route
//! needs `succ_sub_of_le` to give the truncated difference `sub (succ n') i`
//! a successor shape — a genuine side-condition-carrying obstruction, because
//! `Nat.sub` recurses on its SECOND argument, so `sub (succ n') i` does not
//! reduce for a bound `i` the way `sub n' (succ i)` does.
//!
//! Inducting on `m` (the FIRST operand) instead avoids that obstruction
//! entirely. Every successor shape this proof needs comes from one of two
//! UNCONDITIONAL sources, never from bounding a subtraction:
//!
//!   * `Nat.succ_add` turns `add (succ m') n` into `succ (add m' n)` — the
//!     outer `choose`'s first argument gets a `succ` for free, so Pascal's
//!     rule (`choose_succ_succ`) applies directly to the LHS without any
//!     side condition.
//!   * `Nat.succ_sub_succ : sub (succ a) (succ b) = sub a b` is already
//!     unconditional (no `Le`/`Lt` hypothesis) — unlike `succ_sub_of_le`,
//!     which supplies a successor shape for the FIRST argument of `sub`,
//!     `succ_sub_succ` only ever needs BOTH arguments already `succ`-shaped,
//!     which is exactly the shape a `sum_range_shift_front` peel produces.
//!
//! So `succ_sub_of_le` is not used here — the module built for the earlier,
//! abandoned route is a red herring for the route this file actually takes.
//!
//! Structure: outer induction on `m`, with `n` and `k` BOTH generalized
//! inside the motive (`n` because the statement quantifies over it after
//! `m`, `k` because the induction hypothesis is needed at two different `k`
//! values — mirroring [`super::choose::declare_choose_symm`], which
//! generalizes its own second index the same way for the same reason).
//!
//! * **Base case `m = 0`.** `add zero n = n` (`zero_add`), so the goal
//!   reduces to `choose n k = sumRange (fun i => choose 0 i * choose n (sub k
//!   i)) (succ k)`. `sum_range_shift_front` peels the `i = 0` term, which
//!   collapses to `choose n k` via [`conv_front_term_eq`]; the remaining tail
//!   is pointwise `0 * (…)` via `zero_choose_succ` (`choose 0 (succ j) =
//!   0`), and a sum of pointwise-zero terms is `zero`
//!   ([`sum_range_const_zero`]).
//! * **Successor case `m = succ m'`.** `add (succ m') n = succ (add m' n)`
//!   (`succ_add`), then case-split the OWN `k` (a second, inner induction
//!   used only for its case split, ignoring its own hypothesis — the same
//!   technique `declare_choose_symm`'s `k_cases` uses):
//!   - `k = 0`: both sides reduce directly to `1` via `choose_zero_right`,
//!     no induction hypothesis needed ([`zero_k_case_proof`]).
//!   - `k = succ k'`: Pascal's rule splits the LHS into `choose (add m' n)
//!     k' + choose (add m' n) (succ k')`, matched against the induction
//!     hypothesis at `k'` and at `succ k'`. The RHS is front-peeled
//!     (`sum_range_shift_front`) and its tail is Pascal-expanded
//!     (`choose_succ_succ` on the `m'`-side, `succ_sub_succ` on the
//!     `n`-side) and split (`right_distrib`, `sum_range_add`) into a term
//!     matching the `k'` hypothesis and a shared "second term" that also
//!     appears in the induction hypothesis's OWN front-peel at `succ k'`.
//!     Matching the two decompositions up needs one three-term reassociation
//!     (`add_left_comm`, built locally — see its doc comment)
//!     ([`succ_k_case_proof`]).

use super::NatPrelude;
use super::ops::{NatDev, NatOps};
use crate::KernelError;
use crate::expr::ExprId;

// ============================================================================
// Shared term builders.
// ============================================================================

/// `fun i => choose a i * choose b (sub k i)` — one convolution row's
/// summand, parameterized so every use site (the statement itself, both
/// induction-hypothesis instantiations, and the front/tail decompositions)
/// builds it identically.
fn conv_summand(d: &mut NatDev<'_>, a: ExprId, b: ExprId, k: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let choose_a_i = d.choose(a, i);
    let ki = d.sub(k, i);
    let choose_b_ki = d.choose(b, ki);
    let body = d.mul(choose_a_i, choose_b_ki);
    d.lam_fv(i_fv, nat, body)
}

/// `fun j => f (succ j)`, the index-shifted function `sumRange_shiftFront`
/// pairs with its own front term.
fn shifted_fn(d: &mut NatDev<'_>, f: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let j_fv = d.fresh_fvar();
    let j = d.kernel().fvar(j_fv);
    let sj = d.succ(j);
    let body = d.apply(f, &[sj]);
    d.lam_fv(j_fv, nat, body)
}

/// `fun _ => zero`.
fn const_zero_fn(d: &mut NatDev<'_>) -> ExprId {
    let nat = d.nat_ty();
    let x_fv = d.fresh_fvar();
    let zero = d.zero();
    d.lam_fv(x_fv, nat, zero)
}

/// `x + (y + z) = y + (x + z)` — the additive three-term swap the final
/// assembly needs (`front + (row + second) = row + (front + second)`).
/// Proved the same way `binomial.rs`'s private `add_left_comm` is (assoc,
/// comm-on-the-pair, assoc); duplicated locally rather than exposed from
/// `binomial.rs`, since this module must not edit that file.
fn add_left_comm(d: &mut NatDev<'_>, p: &NatPrelude, x: ExprId, y: ExprId, z: ExprId) -> ExprId {
    let p = *p;
    let yz = d.add(y, z);
    let start = d.add(x, yz);
    let xy = d.add(x, y);
    let xy_z = d.add(xy, z);
    let h_assoc1 = d.lemma(p.add_assoc, &[x, y, z]); // xy_z = start
    let h1 = d.symm(xy_z, start, h_assoc1); // start = xy_z
    let yx = d.add(y, x);
    let yx_z = d.add(yx, z);
    let h_comm = d.lemma(p.add_comm, &[x, y]); // xy = yx
    let h2 = d.congr(xy, yx, h_comm, &|d, t| d.add(t, z)); // xy_z = yx_z
    let xz = d.add(x, z);
    let target = d.add(y, xz);
    let h3 = d.lemma(p.add_assoc, &[y, x, z]); // yx_z = target
    let (_e, proof) = d.chain(start, &[(xy_z, h1), (yx_z, h2), (target, h3)]);
    proof
}

/// `choose a 0 * choose b (sub k 0) = choose b k` — the front term of ANY
/// convolution row collapses the same way regardless of `a`: `choose_a_0 =
/// 1` (`choose_zero_right`, generic in `a`) and `sub k 0 = k` (`sub_zero`).
/// Used for the base case's own front term (`a = zero`) and for both
/// front-peels in the successor case's `k = succ k'` branch (`a = succ m'`
/// on the LHS side, `a = m'` on the induction-hypothesis side) — the shared
/// value `choose n (succ k')` those two peels produce is exactly what makes
/// the final assembly's cancellation work.
fn conv_front_term_eq(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    a: ExprId,
    b: ExprId,
    k: ExprId,
) -> ExprId {
    let p = *p;
    let zero = d.zero();
    let choose_a0 = d.choose(a, zero);
    let sub_k0 = d.sub(k, zero);
    let choose_b_subk0 = d.choose(b, sub_k0);
    let lhs = d.mul(choose_a0, choose_b_subk0);

    let h_czr = d.lemma(p.choose_zero_right, &[a]); // choose a 0 = 1
    let one = d.num(1);
    let mid1 = d.mul(one, choose_b_subk0);
    let h1 = d.congr(choose_a0, one, h_czr, &|d, x| d.mul(x, choose_b_subk0));

    let h_sz = d.lemma(p.sub_zero, &[k]); // sub k 0 = k
    let choose_bk = d.choose(b, k);
    let mid2 = d.mul(one, choose_bk);
    let h2 = d.congr(sub_k0, k, h_sz, &|d, x| {
        let cb = d.choose(b, x);
        d.mul(one, cb)
    });

    let h_om = d.lemma(p.one_mul, &[choose_bk]); // 1 * choose b k = choose b k

    let (_e, proof) = d.chain(lhs, &[(mid1, h1), (mid2, h2), (choose_bk, h_om)]);
    proof
}

/// `sumRange (fun _ => zero) n = zero`, by trivial induction on `n`.
fn sum_range_const_zero(d: &mut NatDev<'_>, cz: ExprId, n: ExprId) -> ExprId {
    let motive = |d: &mut NatDev<'_>, x: ExprId| -> ExprId {
        let sr = d.sum_range(cz, x);
        let zero = d.zero();
        d.eq(sr, zero)
    };
    d.induct(
        &motive,
        &|d| {
            let zero = d.zero();
            d.refl(zero)
        },
        &|d, j, ih| {
            let sr_j = d.sum_range(cz, j);
            let cz_j = d.apply(cz, &[j]);
            let zero = d.zero();
            // Eq(add(sr_j, cz_j), add(zero, cz_j)); `add(zero, cz_j)` is
            // definitionally `zero` (`cz_j` beta-reduces to `zero`, and
            // `add zero zero` ι-reduces to `zero`), so this already has the
            // goal's type up to defeq.
            d.congr(sr_j, zero, ih, &|d, t| d.add(t, cz_j))
        },
        n,
    )
}

// ============================================================================
// Base case: `m = 0`.
// ============================================================================

/// Proves `choose (add zero n) k = sumRange (conv_summand zero n k) (succ
/// k)` for the given (fixed, universally-quantified-outside) `n`, `k`.
fn base_case_proof(d: &mut NatDev<'_>, p: &NatPrelude, n: ExprId, k: ExprId) -> ExprId {
    let p = *p;
    let zero = d.zero();
    let add_0n = d.add(zero, n);
    let lhs = d.choose(add_0n, k);

    let h_za = d.lemma(p.zero_add, &[n]); // add zero n = n
    let choose_nk = d.choose(n, k);
    let h_lhs = d.congr(add_0n, n, h_za, &|d, x| d.choose(x, k));
    // h_lhs : lhs = choose_nk

    let f = conv_summand(d, zero, n, k);
    let sk = d.succ(k);
    let rhs = d.sum_range(f, sk);

    let h_sf = d.lemma(p.sum_range_shift_front, &[f, k]);
    // h_sf : rhs = add(f 0, sumRange (shifted f) k)
    let f0 = d.apply(f, &[zero]);
    let shifted = shifted_fn(d, f);
    let tail = d.sum_range(shifted, k);
    let stage1 = d.add(f0, tail);

    let h_f0 = conv_front_term_eq(d, &p, zero, n, k); // f0 = choose_nk
    let stage2 = d.add(choose_nk, tail);
    let h1 = d.congr(f0, choose_nk, h_f0, &|d, x| d.add(x, tail));

    // tail = zero: pointwise `shifted i = 0 * choose n (sub k (succ i))`
    // via `zero_choose_succ`, then `zero_mul`, then `sum_range_congr`
    // against the constant-zero function, then `sum_range_const_zero`.
    let cz = const_zero_fn(d);
    let nat = d.nat_ty();
    let pointwise = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let si = d.succ(i);
        let choose_0_si = d.choose(zero, si);
        let sub_k_si = d.sub(k, si);
        let y = d.choose(n, sub_k_si);
        let lhs_pw = d.mul(choose_0_si, y);
        let h_zc = d.lemma(p.zero_choose_succ, &[i]); // choose 0 (succ i) = zero
        let mid_pw = d.mul(zero, y);
        let h_a = d.congr(choose_0_si, zero, h_zc, &|d, x| d.mul(x, y));
        let h_zm = d.lemma(p.zero_mul, &[y]); // zero * y = zero
        let (_e, proof) = d.chain(lhs_pw, &[(mid_pw, h_a), (zero, h_zm)]);
        d.lam_fv(i_fv, nat, proof)
    };
    let h_congr_tail = d.lemma(p.sum_range_congr, &[shifted, cz, k, pointwise]);
    let sr_cz_k = d.sum_range(cz, k);
    let h_czk = sum_range_const_zero(d, cz, k);
    let (_e2, tail_to_zero) = d.chain(tail, &[(sr_cz_k, h_congr_tail), (zero, h_czk)]);

    let stage3 = d.add(choose_nk, zero);
    let h2 = d.congr(tail, zero, tail_to_zero, &|d, x| d.add(choose_nk, x));

    let h3 = d.lemma(p.add_zero, &[choose_nk]); // choose_nk + zero = choose_nk

    let (_e3, rhs_to_choose_nk) = d.chain(
        rhs,
        &[(stage1, h_sf), (stage2, h1), (stage3, h2), (choose_nk, h3)],
    );

    let rev = d.symm(rhs, choose_nk, rhs_to_choose_nk); // choose_nk = rhs
    d.trans(lhs, choose_nk, rhs, h_lhs, rev)
}

// ============================================================================
// Successor case, `k = 0` branch.
// ============================================================================

/// Proves `choose (add (succ mp) n) zero = sumRange (conv_summand (succ mp)
/// n zero) (succ zero)`, with no use of the outer induction hypothesis:
/// both sides reduce directly to `1`.
fn zero_k_case_proof(d: &mut NatDev<'_>, p: &NatPrelude, mp: ExprId, n: ExprId) -> ExprId {
    let p = *p;
    let smp = d.succ(mp);
    let add_ = d.add(smp, n);
    let zero = d.zero();
    let lhs = d.choose(add_, zero);
    let one = d.num(1);
    let h_lhs = d.lemma(p.choose_zero_right, &[add_]); // lhs = 1

    let f = conv_summand(d, smp, n, zero);
    let sz = d.succ(zero);
    let rhs = d.sum_range(f, sz);

    let sr_zero = d.sum_range(f, zero);
    let f0 = d.apply(f, &[zero]);
    let stage1 = d.add(sr_zero, f0);
    let h1 = d.lemma(p.sum_range_succ, &[f, zero]); // rhs = stage1

    let h_srz = d.lemma(p.sum_range_zero, &[f]); // sr_zero = zero
    let stage2 = d.add(zero, f0);
    let h2 = d.congr(sr_zero, zero, h_srz, &|d, x| d.add(x, f0));

    let h3 = d.lemma(p.zero_add, &[f0]); // stage2 = f0

    let choose_n_zero = d.choose(n, zero);
    let h4 = conv_front_term_eq(d, &p, smp, n, zero); // f0 = choose_n_zero

    let h5 = d.lemma(p.choose_zero_right, &[n]); // choose_n_zero = 1

    let (_e, rhs_to_one) = d.chain(
        rhs,
        &[
            (stage1, h1),
            (stage2, h2),
            (f0, h3),
            (choose_n_zero, h4),
            (one, h5),
        ],
    );

    let rev = d.symm(rhs, one, rhs_to_one); // one = rhs
    d.trans(lhs, one, rhs, h_lhs, rev)
}

// ============================================================================
// Successor case, `k = succ kp` branch — the main assembly.
// ============================================================================

/// Proves `choose (add (succ mp) n) (succ kp) = sumRange (conv_summand
/// (succ mp) n (succ kp)) (succ (succ kp))`, given `ih : ∀ n' k', choose (add
/// mp n') k' = sumRange (conv_summand mp n' k') (succ k')`.
///
/// See the module doc's "Successor case" bullet for the shape; this is
/// [`super::binomial`]'s `a_side_lemma`/`b_side_lemma` assembly pattern
/// (Pascal-expand a front-peeled tail, split via `right_distrib` and
/// `sum_range_add`, match the pieces against two induction-hypothesis
/// instances), written out directly rather than factored into named helpers,
/// since every intermediate term here is used exactly once.
fn succ_k_case_proof(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    mp: ExprId,
    n: ExprId,
    kp: ExprId,
    ih: ExprId,
) -> ExprId {
    let p = *p;
    let nat = d.nat_ty();
    let smp = d.succ(mp);
    let skp = d.succ(kp);
    let add_smp_n = d.add(smp, n);
    let lhs0 = d.choose(add_smp_n, skp);

    // Step 1: add (succ mp) n = succ (add mp n).
    let h_sa = d.lemma(p.succ_add, &[mp, n]);
    let add_mp_n = d.add(mp, n);
    let s_add_mp_n = d.succ(add_mp_n);
    let lhs1 = d.choose(s_add_mp_n, skp);
    let h1 = d.congr(add_smp_n, s_add_mp_n, h_sa, &|d, x| d.choose(x, skp));

    // Step 2: Pascal's rule at (add mp n, kp).
    let h_pascal = d.lemma(p.choose_succ_succ, &[add_mp_n, kp]);
    let a_term = d.choose(add_mp_n, kp);
    let b_term = d.choose(add_mp_n, skp);
    let lhs2 = d.add(a_term, b_term);

    // Step 3: rewrite both summands via the induction hypothesis.
    let ih_kp = d.apply(ih, &[n, kp]); // a_term = rhs_kp
    let g1_fn = conv_summand(d, mp, n, kp);
    let rhs_kp = d.sum_range(g1_fn, skp);
    let lhs3a = d.add(rhs_kp, b_term);
    let ha = d.congr(a_term, rhs_kp, ih_kp, &|d, x| d.add(x, b_term));

    let ih_skp = d.apply(ih, &[n, skp]); // b_term = rhs_skp
    let f_ih = conv_summand(d, mp, n, skp);
    let sskp = d.succ(skp);
    let rhs_skp = d.sum_range(f_ih, sskp);
    let hb = d.congr(b_term, rhs_skp, ih_skp, &|d, x| d.add(rhs_kp, x));

    // The original RHS.
    let f_top = conv_summand(d, smp, n, skp);
    let rhs_target = d.sum_range(f_top, sskp);

    // `g2_fn`, the shared "second term" summand both the top-side and
    // ih-side decompositions land on. Built once so both sides literally
    // share the same `sumRange (g2_fn) skp` expression.
    let g2_fn = {
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let sj = d.succ(j);
        let c1 = d.choose(mp, sj);
        let sub_kp_j = d.sub(kp, j);
        let c2 = d.choose(n, sub_kp_j);
        let body = d.mul(c1, c2);
        d.lam_fv(j_fv, nat, body)
    };
    let second_term = d.sum_range(g2_fn, skp);

    // --- Top side: rhs_target = choose n (succ kp) + (rhs_kp + second_term) ---
    let h_sf_top = d.lemma(p.sum_range_shift_front, &[f_top, skp]);
    let zero = d.zero();
    let f_top0 = d.apply(f_top, &[zero]);
    let shifted_top = shifted_fn(d, f_top);
    let tail_top = d.sum_range(shifted_top, skp);
    let stage_t1 = d.add(f_top0, tail_top);

    let choose_n_skp = d.choose(n, skp);
    let front_top = conv_front_term_eq(d, &p, smp, n, skp); // f_top0 = choose_n_skp
    let stage_t2 = d.add(choose_n_skp, tail_top);
    let h_t1 = d.congr(f_top0, choose_n_skp, front_top, &|d, x| d.add(x, tail_top));

    // Pointwise: shifted_top j = g1_fn j + g2_fn j, via choose_succ_succ,
    // succ_sub_succ, and right_distrib.
    let combined_g1g2 = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let g1i = d.apply(g1_fn, &[i]);
        let g2i = d.apply(g2_fn, &[i]);
        let body = d.add(g1i, g2i);
        d.lam_fv(i_fv, nat, body)
    };
    let pointwise_top = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let si = d.succ(i);
        let choose_smp_si = d.choose(smp, si);
        let sub_skp_si = d.sub(skp, si);
        let choose_n_sub = d.choose(n, sub_skp_si);
        let lhs_pw = d.mul(choose_smp_si, choose_n_sub);

        let h_pascal_i = d.lemma(p.choose_succ_succ, &[mp, i]); // choose_smp_si = choose mp i + choose mp si
        let choose_mp_i = d.choose(mp, i);
        let choose_mp_si = d.choose(mp, si);
        let sum_choose = d.add(choose_mp_i, choose_mp_si);
        let mid1 = d.mul(sum_choose, choose_n_sub);
        let ha_pw = d.congr(choose_smp_si, sum_choose, h_pascal_i, &|d, x| {
            d.mul(x, choose_n_sub)
        });

        let h_sss_i = d.lemma(p.succ_sub_succ, &[kp, i]); // sub_skp_si = sub kp i
        let sub_kp_i = d.sub(kp, i);
        let choose_n_subkpi = d.choose(n, sub_kp_i);
        let mid2 = d.mul(sum_choose, choose_n_subkpi);
        let hb_pw = d.congr(sub_skp_si, sub_kp_i, h_sss_i, &|d, x| {
            let c = d.choose(n, x);
            d.mul(sum_choose, c)
        });

        let h_rd = d.lemma(
            p.right_distrib,
            &[choose_mp_i, choose_mp_si, choose_n_subkpi],
        );
        let term1 = d.mul(choose_mp_i, choose_n_subkpi);
        let term2 = d.mul(choose_mp_si, choose_n_subkpi);
        let target_pw = d.add(term1, term2);

        let (_e, proof) = d.chain(lhs_pw, &[(mid1, ha_pw), (mid2, hb_pw), (target_pw, h_rd)]);
        d.lam_fv(i_fv, nat, proof)
    };
    let h_pw_top = d.lemma(
        p.sum_range_congr,
        &[shifted_top, combined_g1g2, skp, pointwise_top],
    );
    let h_sra_top = d.lemma(p.sum_range_add, &[g1_fn, g2_fn, skp]);
    let sum_combined = d.sum_range(combined_g1g2, skp);
    let sum_g1_skp = d.sum_range(g1_fn, skp); // == rhs_kp, same construction
    let tail_top_split = d.add(sum_g1_skp, second_term);
    let (_e2, tail_top_to_split) = d.chain(
        tail_top,
        &[(sum_combined, h_pw_top), (tail_top_split, h_sra_top)],
    );

    let stage_t3 = d.add(choose_n_skp, tail_top_split);
    let h_t2 = d.congr(tail_top, tail_top_split, tail_top_to_split, &|d, x| {
        d.add(choose_n_skp, x)
    });

    // choose_n_skp + (rhs_kp + second_term) = rhs_kp + (choose_n_skp + second_term)
    let h_alc = add_left_comm(d, &p, choose_n_skp, rhs_kp, second_term);
    let stage_t4 = {
        let inner = d.add(choose_n_skp, second_term);
        d.add(rhs_kp, inner)
    };

    // --- ih side: rhs_skp = choose n (succ kp) + second_term ---
    let h_sf_ih = d.lemma(p.sum_range_shift_front, &[f_ih, skp]);
    let f_ih0 = d.apply(f_ih, &[zero]);
    let shifted_ih = shifted_fn(d, f_ih);
    let tail_ih = d.sum_range(shifted_ih, skp);
    let stage_i1 = d.add(f_ih0, tail_ih);

    let front_ih = conv_front_term_eq(d, &p, mp, n, skp); // f_ih0 = choose_n_skp
    let stage_i2 = d.add(choose_n_skp, tail_ih);
    let h_i1 = d.congr(f_ih0, choose_n_skp, front_ih, &|d, x| d.add(x, tail_ih));

    let pointwise_ih = {
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let sj = d.succ(j);
        let choose_mp_sj = d.choose(mp, sj);
        let sub_skp_sj = d.sub(skp, sj);

        let h_sss = d.lemma(p.succ_sub_succ, &[kp, j]); // sub_skp_sj = sub kp j
        let sub_kp_j = d.sub(kp, j);
        let hh = d.congr(sub_skp_sj, sub_kp_j, h_sss, &|d, x| {
            let c = d.choose(n, x);
            d.mul(choose_mp_sj, c)
        });
        d.lam_fv(j_fv, nat, hh)
    };
    let h_pw_ih = d.lemma(p.sum_range_congr, &[shifted_ih, g2_fn, skp, pointwise_ih]);
    // h_pw_ih : tail_ih = second_term

    let stage_i3 = d.add(choose_n_skp, second_term);
    let h_i2 = d.congr(tail_ih, second_term, h_pw_ih, &|d, x| {
        d.add(choose_n_skp, x)
    });

    let (_e3, rhs_skp_to_stage_i3) = d.chain(
        rhs_skp,
        &[(stage_i1, h_sf_ih), (stage_i2, h_i1), (stage_i3, h_i2)],
    );
    // rhs_skp = choose_n_skp + second_term = stage_i3

    let stage_t5 = d.add(rhs_kp, rhs_skp);
    let h_t3 = {
        let rev = d.symm(rhs_skp, stage_i3, rhs_skp_to_stage_i3); // stage_i3 = rhs_skp
        d.congr(stage_i3, rhs_skp, rev, &|d, x| d.add(rhs_kp, x))
    };

    let (_e4, rhs_target_to_stage_t5) = d.chain(
        rhs_target,
        &[
            (stage_t1, h_sf_top),
            (stage_t2, h_t1),
            (stage_t3, h_t2),
            (stage_t4, h_alc),
            (stage_t5, h_t3),
        ],
    );
    // stage_t5 = add(rhs_kp, rhs_skp), the same term `lhs3a`/`hb`'s target
    // reaches via the induction hypothesis.
    let h_final = d.symm(rhs_target, stage_t5, rhs_target_to_stage_t5); // stage_t5 = rhs_target

    let (_e5, final_proof) = d.chain(
        lhs0,
        &[
            (lhs1, h1),
            (lhs2, h_pascal),
            (lhs3a, ha),
            (stage_t5, hb),
            (rhs_target, h_final),
        ],
    );
    final_proof
}

// ============================================================================
// The headline theorem.
// ============================================================================

/// `Nat.choose_add_convolution : ∀ m n k, choose (add m n) k = sumRange (fun
/// i => choose m i * choose n (sub k i)) (succ k)` — Vandermonde's
/// convolution, by induction on `m` with `n` and `k` both generalized inside
/// the motive. See the module doc for the proof shape.
pub(super) fn declare_choose_add_convolution(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();

    let stmt_at = |d: &mut NatDev<'_>, m: ExprId| -> ExprId {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let add_mn = d.add(m, n);
        let lhs = d.choose(add_mn, k);
        let f = conv_summand(d, m, n, k);
        let sk = d.succ(k);
        let rhs = d.sum_range(f, sk);
        let eqn = d.eq(lhs, rhs);
        let inner = d.pi_fv(k_fv, nat, eqn);
        d.pi_fv(n_fv, nat, inner)
    };

    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let stmt_m = stmt_at(d, m);

    let proof = d.induct(
        &stmt_at,
        &|d| {
            let n_fv = d.fresh_fvar();
            let n = d.kernel().fvar(n_fv);
            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let body = base_case_proof(d, &p, n, k);
            let with_k = d.lam_fv(k_fv, nat, body);
            d.lam_fv(n_fv, nat, with_k)
        },
        &|d, mp, ih| {
            let n_fv = d.fresh_fvar();
            let n = d.kernel().fvar(n_fv);
            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let inner_motive = |d: &mut NatDev<'_>, x: ExprId| -> ExprId {
                let smp = d.succ(mp);
                let add_ = d.add(smp, n);
                let lhs = d.choose(add_, x);
                let f = conv_summand(d, smp, n, x);
                let sx = d.succ(x);
                let rhs = d.sum_range(f, sx);
                d.eq(lhs, rhs)
            };
            let k_cases = d.induct(
                &inner_motive,
                &|d| zero_k_case_proof(d, &p, mp, n),
                &|d, kp, _inner_ih| succ_k_case_proof(d, &p, mp, n, kp, ih),
                k,
            );
            let with_k = d.lam_fv(k_fv, nat, k_cases);
            d.lam_fv(n_fv, nat, with_k)
        },
        m,
    );

    let ty = d.pi_fv(m_fv, nat, stmt_m);
    let value = d.lam_fv(m_fv, nat, proof);
    d.declare_theorem(p.choose_add_convolution, ty, value)?;
    Ok(())
}

// ============================================================================
// Corollary: the sum-of-squares identity.
// ============================================================================

/// `Nat.sum_choose_sq : ∀ n, sumRange (fun i => choose n i * choose n i)
/// (succ n) = choose (add n n) n` — the `m = n = k = n` instance of
/// Vandermonde's convolution: `choose n (sub n i) = choose n i` for `i ≤ n`
/// (`choose_symm`), so the convolution's summand `choose n i * choose n (sub
/// n i)` collapses to `choose n i * choose n i` pointwise below the sum's own
/// bound (`sum_range_congr_lt`, not the unconditional `sum_range_congr` —
/// `choose_symm` needs `Le i n`, which only the bound `i < succ n` supplies).
pub(super) fn declare_sum_choose_sq(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();

    d.theorem(p.sum_choose_sq, 1, &|d, v| {
        let n = v[0];
        let sn = d.succ(n);

        let h_conv = d.lemma(p.choose_add_convolution, &[n, n, n]);
        // h_conv : choose (add n n) n = sumRange (conv_summand n n n) (succ n)
        let add_nn = d.add(n, n);
        let lhs_target = d.choose(add_nn, n);
        let f = conv_summand(d, n, n, n);
        let sum_f = d.sum_range(f, sn);

        let sq_fn = {
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let ci = d.choose(n, i);
            let body = d.mul(ci, ci);
            d.lam_fv(i_fv, nat, body)
        };

        let pointwise = {
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let hyp_ty = d.lt(i, sn);
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);

            let choose_n_i = d.choose(n, i);
            let sub_n_i = d.sub(n, i);
            let choose_n_subni = d.choose(n, sub_n_i);
            // lhs_pw (= mul(choose_n_i, choose_n_subni)) is the beta-reduced
            // form of `apply(f,[i])`; not built explicitly, since the congr
            // below is used at that defeq-bridged type.

            let h_le = d.lemma(p.le_of_lt_succ, &[i, n, h]); // Le i n
            let h_symm = d.lemma(p.choose_symm, &[n, i, h_le]); // choose n i = choose n (sub n i)
            let h_rev = d.symm(choose_n_i, choose_n_subni, h_symm); // choose n (sub n i) = choose n i
            let body = d.congr(choose_n_subni, choose_n_i, h_rev, &|d, x| {
                d.mul(choose_n_i, x)
            });
            // body : lhs_pw = choose_n_i * choose_n_i, matching sq_fn i by beta

            let with_h = d.lam_fv(h_fv, hyp_ty, body);
            d.lam_fv(i_fv, nat, with_h)
        };
        let h_pw = d.lemma(p.sum_range_congr_lt, &[f, sq_fn, sn, pointwise]);
        // h_pw : sumRange f (succ n) = sumRange sq_fn (succ n)

        let sum_sq = d.sum_range(sq_fn, sn);
        let (_e, conv_to_sum_sq) = d.chain(lhs_target, &[(sum_f, h_conv), (sum_sq, h_pw)]);
        // conv_to_sum_sq : choose (add n n) n = sumRange sq_fn (succ n)

        let stmt = d.eq(sum_sq, lhs_target);
        let proof = d.symm(lhs_target, sum_sq, conv_to_sum_sq);
        (stmt, proof)
    })?;
    Ok(())
}

/// Declare every theorem in this module.
pub(super) fn declare_vandermonde_all(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    declare_choose_add_convolution(d, p)?;
    declare_sum_choose_sq(d, p)?;
    Ok(())
}
