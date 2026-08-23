//! Toward the binomial theorem over ℕ (`Nat.add_pow`).
//!
//! [`super::choose`] gives us `Nat.choose` and Pascal's rule
//! (`choose_succ_succ`, closing by `refl` alone for generic `n,k`). This
//! module builds the finite-sum reindexing toolkit the theorem's induction
//! needs beyond what [`super::algebra`] already has —
//! [`sum_range_add`](declare_sum_range_add), a FRONT-peeling counterpart to
//! the defining (back-peeling) `sum_range_succ`
//! ([`sum_range_shift_front`](declare_sum_range_shift_front)), and a bounded
//! pointwise congruence ([`sum_range_congr_lt`](declare_sum_range_congr_lt))
//! — then checks the theorem's STATEMENT shape at `n=0` and `n=1` before
//! attempting the general induction.
//!
//! # Where the general theorem stalls
//!
//! The classical inductive step splits `(a+b)^(n+1) = (a+b)*S(n)` (`S(n)` the
//! sum-form of `(a+b)^n`) into `a*S(n) + b*S(n)`, then matches each piece
//! against a front-peel of `S(n+1)`'s OWN sum, using Pascal's rule to combine
//! the peeled tail. Reindexing the `a`-shifted piece is unconditional (an
//! `a`-exponent bump via `pow_succ` needs no side condition) and closes
//! cleanly with `sum_range_congr` plus `mul_sum_range`. Reindexing the
//! `b`-shifted piece needs `succ (n - succ k) = n - k`, which is only true
//! for `k < n` — [`super::choose::sub_succ_of_lt`] proves exactly this
//! (built for `choose_symm`'s own case split), and `sum_range_congr_lt`
//! exists so it can be applied under a sum bounded by `n` (where every index
//! satisfies `k < n` uniformly).
//!
//! What is NOT done: the final assembly wiring `a*S(n)`, `b*S(n)`, and the
//! front-peeled, Pascal-split, boundary-adjusted (`choose_zero_right`,
//! `choose_succ_self_eq_zero`) pieces of `S(n+1)` into one proof term. Each
//! individual identity above was checked by hand to be true and provable
//! from lemmas already in this prelude (`right_distrib` splits the
//! Pascal-summed term; `one_mul`/`zero_mul`/`add_zero` collapse the two
//! boundary terms), but composing roughly a dozen such steps into a single
//! well-typed kernel term — with the same term reconstructed identically at
//! every use site, since this development has no tactic/rewrite engine — is
//! sized larger than fits in this slice. `add_pow_zero`/`add_pow_one` below
//! already exercise the same algebra at the smallest instances, so the gap
//! is scale, not an unresolved mathematical question.

use super::NatPrelude;
use super::ops::{NatDev, NatOps};
use crate::KernelError;
use crate::expr::ExprId;

/// `fun k => f (succ k)`, the index-shifted function used by
/// [`sum_range_shift_front`](declare_sum_range_shift_front).
fn shifted_fn(d: &mut NatDev<'_>, f: ExprId) -> ExprId {
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let sk = d.succ(k);
    let body = d.apply(f, &[sk]);
    let nat = d.nat_ty();
    d.lam_fv(k_fv, nat, body)
}

/// `(a+b)+(c+d) = (a+c)+(b+d)`, returned as a `(target, proof)` chain step
/// (the proof's source is `add(add(a,b),add(c,d))`).
fn add_add_add_comm(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    a: ExprId,
    b: ExprId,
    c: ExprId,
    dd: ExprId,
) -> (ExprId, ExprId) {
    let p = *p;
    let cd = d.add(c, dd);
    let bd = d.add(b, dd);
    let ab = d.add(a, b);
    let start = d.add(ab, cd);

    // start = a + (b + (c+d))
    let bcd = d.add(b, cd);
    let s1 = d.add(a, bcd);
    let h1 = d.lemma(p.add_assoc, &[a, b, cd]);

    // b+(c+d) -> (b+c)+d
    let bc = d.add(b, c);
    let bc_d = d.add(bc, dd);
    let s2 = d.add(a, bc_d);
    let h_bcd = d.lemma(p.add_assoc, &[b, c, dd]); // (b+c)+d = b+(c+d)
    let h2_inner = d.symm(bc_d, bcd, h_bcd); // b+(c+d) = (b+c)+d
    let h2 = d.congr(bcd, bc_d, h2_inner, &|d, t| d.add(a, t));

    // (b+c) -> (c+b)
    let cb = d.add(c, b);
    let cb_d = d.add(cb, dd);
    let s3 = d.add(a, cb_d);
    let h_comm = d.lemma(p.add_comm, &[b, c]); // b+c = c+b
    let h3 = d.congr(bc, cb, h_comm, &|d, t| {
        let td = d.add(t, dd);
        d.add(a, td)
    });

    // (c+b)+d -> c+(b+d)
    let c_bd = d.add(c, bd);
    let s4 = d.add(a, c_bd);
    let h_assoc2 = d.lemma(p.add_assoc, &[c, b, dd]); // (c+b)+d = c+(b+d)
    let h4 = d.congr(cb_d, c_bd, h_assoc2, &|d, t| d.add(a, t));

    // a+(c+(b+d)) -> (a+c)+(b+d)
    let ac = d.add(a, c);
    let target = d.add(ac, bd);
    let a_c_bd = d.add(a, c_bd);
    let h_assoc3 = d.lemma(p.add_assoc, &[a, c, bd]); // (a+c)+(b+d) = a+(c+(b+d)), i.e. Eq(target, a_c_bd)
    let h5 = d.symm(target, a_c_bd, h_assoc3); // Eq(a_c_bd, target)

    let (_e, proof) = d.chain(
        start,
        &[(s1, h1), (s2, h2), (s3, h3), (s4, h4), (target, h5)],
    );
    (target, proof)
}

/// `sumRange_add : ∀ f g n, sumRange (fun i => f i + g i) n = sumRange f n + sumRange g n`.
///
/// Proved by induction on `n`; the successor case needs the four-term
/// rearrangement `(A+B)+(C+D) = (A+C)+(B+D)` ([`add_add_add_comm`]), since the
/// induction hypothesis rewrites the *inner* pair while `sum_range_succ`
/// produces the *outer* one.
fn declare_sum_range_add(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let fn_ty = d.arrow(nat, nat);
    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let combined_fn = |d: &mut NatDev<'_>, f: ExprId, g: ExprId| -> ExprId {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let fi = d.apply(f, &[i]);
        let gi = d.apply(g, &[i]);
        let body = d.add(fi, gi);
        let nat = d.nat_ty();
        d.lam_fv(i_fv, nat, body)
    };

    let motive = |d: &mut NatDev<'_>, x: ExprId| -> ExprId {
        let combined = combined_fn(d, f, g);
        let lhs = d.sum_range(combined, x);
        let sf = d.sum_range(f, x);
        let sg = d.sum_range(g, x);
        let rhs = d.add(sf, sg);
        d.eq(lhs, rhs)
    };
    let stmt = motive(d, n);

    let proof = d.induct(
        &motive,
        &|d| {
            let zero = d.zero();
            d.refl(zero)
        },
        &|d, j, ih| {
            let combined = combined_fn(d, f, g);
            let combined_j = d.apply(combined, &[j]);
            let prior_combined = d.sum_range(combined, j);
            let start = d.add(prior_combined, combined_j);

            let sf_j = d.sum_range(f, j);
            let sg_j = d.sum_range(g, j);
            let sfg = d.add(sf_j, sg_j);
            let h1 = d.congr(prior_combined, sfg, ih, &|d, t| d.add(t, combined_j));
            let after_ih = d.add(sfg, combined_j);

            let fj = d.apply(f, &[j]);
            let gj = d.apply(g, &[j]);
            let fg_j = d.add(fj, gj);
            let h_bridge = d.refl(fg_j); // combined_j ≡ fg_j by beta
            let after_bridge = d.add(sfg, fg_j);
            let h2 = d.congr(combined_j, fg_j, h_bridge, &|d, t| d.add(sfg, t));

            let end = add_add_add_comm(d, &p, sf_j, sg_j, fj, gj);
            let (_e, proof) = d.chain(start, &[(after_ih, h1), (after_bridge, h2), end]);
            proof
        },
        n,
    );

    let ty = {
        let over_n = d.pi_fv(n_fv, nat, stmt);
        let over_g = d.pi_fv(g_fv, fn_ty, over_n);
        d.pi_fv(f_fv, fn_ty, over_g)
    };
    let value = {
        let over_n = d.lam_fv(n_fv, nat, proof);
        let over_g = d.lam_fv(g_fv, fn_ty, over_n);
        d.lam_fv(f_fv, fn_ty, over_g)
    };
    d.declare_theorem(p.sum_range_add, ty, value)
}

/// `sumRange_shiftFront : ∀ f n, sumRange f (succ n) = f 0 + sumRange (fun k => f (succ k)) n`
/// — peeling the FRONT term off a finite sum. `sum_range_succ` (the defining
/// equation) already peels the BACK term for free; this direction needs
/// induction, because the front term stays fixed while the bound moves.
fn declare_sum_range_shift_front(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let fn_ty = d.arrow(nat, nat);
    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let motive = |d: &mut NatDev<'_>, x: ExprId| -> ExprId {
        let sx = d.succ(x);
        let lhs = d.sum_range(f, sx);
        let zero = d.zero();
        let f0 = d.apply(f, &[zero]);
        let shifted = shifted_fn(d, f);
        let sr = d.sum_range(shifted, x);
        let rhs = d.add(f0, sr);
        d.eq(lhs, rhs)
    };
    let stmt = motive(d, n);

    let proof = d.induct(
        &motive,
        &|d| {
            let zero = d.zero();
            let f0 = d.apply(f, &[zero]);
            d.lemma(p.zero_add, &[f0])
        },
        &|d, j, ih| {
            let sj = d.succ(j);
            let f_prior_succ = d.sum_range(f, sj);
            let f_sj = d.apply(f, &[sj]);
            let start = d.add(f_prior_succ, f_sj);

            let zero = d.zero();
            let f0 = d.apply(f, &[zero]);
            let shifted = shifted_fn(d, f);
            let shifted_j = d.sum_range(shifted, j);
            let mid1 = d.add(f0, shifted_j);
            let h1 = d.congr(f_prior_succ, mid1, ih, &|d, t| d.add(t, f_sj));
            let after_ih = d.add(mid1, f_sj);

            let inner = d.add(shifted_j, f_sj);
            let end = d.add(f0, inner);
            let h2 = d.lemma(p.add_assoc, &[f0, shifted_j, f_sj]);

            let (_e, proof) = d.chain(start, &[(after_ih, h1), (end, h2)]);
            proof
        },
        n,
    );

    let ty = {
        let over_n = d.pi_fv(n_fv, nat, stmt);
        d.pi_fv(f_fv, fn_ty, over_n)
    };
    let value = {
        let over_n = d.lam_fv(n_fv, nat, proof);
        d.lam_fv(f_fv, fn_ty, over_n)
    };
    d.declare_theorem(p.sum_range_shift_front, ty, value)
}

/// `fun i => Lt i bound -> Eq (f i) (g i)`.
fn bounded_pointwise(d: &mut NatDev<'_>, f: ExprId, g: ExprId, bound: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let hyp = d.lt(i, bound);
    let fi = d.apply(f, &[i]);
    let gi = d.apply(g, &[i]);
    let eqn = d.eq(fi, gi);
    let body = d.arrow(hyp, eqn);
    d.pi_fv(i_fv, nat, body)
}

/// `sumRange_congr_lt : ∀ f g n, (∀ i, Lt i n → f i = g i) → sumRange f n = sumRange g n`
/// — [`super::algebra::declare_finite_sum_theorems`]'s `sum_range_congr` with
/// the hypothesis weakened to indices below the bound, which is what a sum
/// with only-conditionally-true summand identities (e.g. involving truncated
/// subtraction) can actually supply.
fn declare_sum_range_congr_lt(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let fn_ty = d.arrow(nat, nat);
    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let motive = |d: &mut NatDev<'_>, x: ExprId| -> ExprId {
        let hyp = bounded_pointwise(d, f, g, x);
        let lhs = d.sum_range(f, x);
        let rhs = d.sum_range(g, x);
        let eqn = d.eq(lhs, rhs);
        d.arrow(hyp, eqn)
    };
    let stmt = motive(d, n);

    let proof = d.induct(
        &motive,
        &|d| {
            let zero = d.zero();
            let hyp_ty = bounded_pointwise(d, f, g, zero);
            let h_fv = d.fresh_fvar();
            let body = d.refl(zero);
            d.lam_fv(h_fv, hyp_ty, body)
        },
        &|d, j, ih| {
            let sj = d.succ(j);
            let hyp_ty = bounded_pointwise(d, f, g, sj);
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);

            // h_lt_j : ∀ i, Lt i j → f i = g i, weakened from `h` via `i<j → i<succ j`.
            let h_lt_j = {
                let i_fv = d.fresh_fvar();
                let i = d.kernel().fvar(i_fv);
                let hi_ty = d.lt(i, j);
                let hi_fv = d.fresh_fvar();
                let hi = d.kernel().fvar(hi_fv);
                let le_succ_j = d.lemma(p.le_succ, &[j]);
                let lifted = d.lemma(p.lt_of_lt_of_le, &[i, j, sj, hi, le_succ_j]);
                let applied = d.apply(h, &[i, lifted]);
                let with_hi = d.lam_fv(hi_fv, hi_ty, applied);
                d.lam_fv(i_fv, nat, with_hi)
            };
            let sub1 = d.apply(ih, &[h_lt_j]);

            let lt_j_sj = d.lemma(p.lt_succ_self, &[j]);
            let sub2 = d.apply(h, &[j, lt_j_sj]);

            let f_prior = d.sum_range(f, j);
            let g_prior = d.sum_range(g, j);
            let fj = d.apply(f, &[j]);
            let gj = d.apply(g, &[j]);
            let start = d.add(f_prior, fj);
            let mid = d.add(g_prior, fj);
            let h1 = d.congr(f_prior, g_prior, sub1, &|d, t| d.add(t, fj));
            let end = d.add(g_prior, gj);
            let h2 = d.congr(fj, gj, sub2, &|d, t| d.add(g_prior, t));
            let (_e, body) = d.chain(start, &[(mid, h1), (end, h2)]);

            d.lam_fv(h_fv, hyp_ty, body)
        },
        n,
    );

    let ty = {
        let over_n = d.pi_fv(n_fv, nat, stmt);
        let over_g = d.pi_fv(g_fv, fn_ty, over_n);
        d.pi_fv(f_fv, fn_ty, over_g)
    };
    let value = {
        let over_n = d.lam_fv(n_fv, nat, proof);
        let over_g = d.lam_fv(g_fv, fn_ty, over_n);
        d.lam_fv(f_fv, fn_ty, over_g)
    };
    d.declare_theorem(p.sum_range_congr_lt, ty, value)
}

/// `fun k => (choose row k * a^k) * b^(row-k)` — the summand of the binomial
/// expansion at `row`, at a POINT (not the lambda; see [`binom_term_fn`]).
fn binom_term(d: &mut NatDev<'_>, a: ExprId, b: ExprId, row: ExprId, k: ExprId) -> ExprId {
    let c = d.choose(row, k);
    let ak = d.pow(a, k);
    let c_ak = d.mul(c, ak);
    let sub_rk = d.sub(row, k);
    let b_pow = d.pow(b, sub_rk);
    d.mul(c_ak, b_pow)
}

/// `fun k => choose row k * a^k * b^(row-k)`, as a lambda.
fn binom_term_fn(d: &mut NatDev<'_>, a: ExprId, b: ExprId, row: ExprId) -> ExprId {
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let body = binom_term(d, a, b, row, k);
    let nat = d.nat_ty();
    d.lam_fv(k_fv, nat, body)
}

/// `sumRange (fun k => choose row k * a^k * b^(row-k)) (succ row)` — the
/// sum-form of `(a+b)^row`.
fn binom_sum(d: &mut NatDev<'_>, a: ExprId, b: ExprId, row: ExprId) -> ExprId {
    let t = binom_term_fn(d, a, b, row);
    let srow = d.succ(row);
    d.sum_range(t, srow)
}

/// `n=0` and `n=1` sanity instances of `add_pow`'s statement shape, proved
/// directly (no induction) — the smallest cases that already exercise the
/// same collapsing algebra (`one_mul`, `zero_add`, `add_comm`) the general
/// induction step needs, catching an off-by-one in the statement (the sum
/// bound, the exponent orientation) before it is spent on a much larger proof.
fn declare_add_pow_sanity(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;

    // add_pow_zero : ∀ a b, (a+b)^0 = sumRange (fun k => choose 0 k*a^k*b^(0-k)) 1
    //
    // Every factor of the single term (k=0) collapses by pure computation —
    // `choose 0 0`, `a^0`, `b^(0-0)`, and `mul 1 1` are all literal — so this
    // closes by `refl` alone, with no lemma at all.
    d.theorem(p.add_pow_zero, 2, &|d, v| {
        let (a, b) = (v[0], v[1]);
        let ab = d.add(a, b);
        let zero = d.zero();
        let lhs = d.pow(ab, zero);
        let rhs = binom_sum(d, a, b, zero);
        (d.eq(lhs, rhs), d.refl(lhs))
    })?;

    // add_pow_one : ∀ a b, (a+b)^1 = sumRange (fun k => choose 1 k*a^k*b^(1-k)) 2
    d.theorem(p.add_pow_one, 2, &|d, v| {
        let (a, b) = (v[0], v[1]);
        let ab = d.add(a, b);
        let one = d.num(1);
        let lhs = d.pow(ab, one);
        let rhs = binom_sum(d, a, b, one);

        // lhs ~ mul(1,ab) [refl, pow_succ+pow_zero] -> ab [one_mul]
        let mul1_ab = d.mul(one, ab);
        let h_lhs1 = d.refl(mul1_ab);
        let h_lhs2 = d.lemma(p.one_mul, &[ab]);
        let lhs_to_ab = d.trans(lhs, mul1_ab, ab, h_lhs1, h_lhs2);

        // t0 = choose(1,0)*a^0*b^(1-0) ~ mul(1,mul(1,b)) [refl] -> mul(1,b) -> b
        let zero = d.zero();
        let t0 = binom_term(d, a, b, one, zero);
        let mul1_b = d.mul(one, b);
        let one_mul1b = d.mul(one, mul1_b);
        let h_bridge0 = d.refl(one_mul1b);
        let h_om1b = d.lemma(p.one_mul, &[mul1_b]);
        let h_om2b = d.lemma(p.one_mul, &[b]);
        let (_e0, t0_to_b) = d.chain(t0, &[(one_mul1b, h_bridge0), (mul1_b, h_om1b), (b, h_om2b)]);

        // t1 = choose(1,1)*a^1*b^(1-1) ~ add(zero,mul(1,mul(1,a))) [refl] -> mul(1,mul(1,a)) -> mul(1,a) -> a
        let t1 = binom_term(d, a, b, one, one);
        let mul1_a = d.mul(one, a);
        let one_mul1a = d.mul(one, mul1_a);
        let zero_plus = d.add(zero, one_mul1a);
        let h_bridge1 = d.refl(zero_plus);
        let h_za = d.lemma(p.zero_add, &[one_mul1a]);
        let h_om1a = d.lemma(p.one_mul, &[mul1_a]);
        let h_om2a = d.lemma(p.one_mul, &[a]);
        let (_e1, t1_to_a) = d.chain(
            t1,
            &[
                (zero_plus, h_bridge1),
                (one_mul1a, h_za),
                (mul1_a, h_om1a),
                (a, h_om2a),
            ],
        );

        // start := add(add(zero,t0),t1), def-eq `rhs` (pure ι/δ), -> ab
        let zero_t0 = d.add(zero, t0);
        let h_zt0 = d.lemma(p.zero_add, &[t0]);
        let zt0_to_b = d.trans(zero_t0, t0, b, h_zt0, t0_to_b);

        let start = d.add(zero_t0, t1);
        let add_b_t1 = d.add(b, t1);
        let h_start1 = d.congr(zero_t0, b, zt0_to_b, &|d, t| d.add(t, t1));
        let add_b_a = d.add(b, a);
        let h_start2 = d.congr(t1, a, t1_to_a, &|d, t| d.add(b, t));
        let h_comm = d.lemma(p.add_comm, &[b, a]);
        let (_e2, start_to_ab) = d.chain(
            start,
            &[(add_b_t1, h_start1), (add_b_a, h_start2), (ab, h_comm)],
        );

        let ab_to_start = d.symm(start, ab, start_to_ab);
        let final_proof = d.trans(lhs, ab, start, lhs_to_ab, ab_to_start);
        (d.eq(lhs, rhs), final_proof)
    })?;
    Ok(())
}

/// Declare `Nat.choose`'s finite-sum toolkit and the `n=0`/`n=1` sanity
/// instances of the binomial theorem. See the module docs for exactly where
/// the general theorem (not yet declared) stalls.
pub(super) fn declare_binomial_theorem(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    declare_sum_range_add(d, p)?;
    declare_sum_range_shift_front(d, p)?;
    declare_sum_range_congr_lt(d, p)?;
    declare_add_pow_sanity(d, p)?;
    Ok(())
}
