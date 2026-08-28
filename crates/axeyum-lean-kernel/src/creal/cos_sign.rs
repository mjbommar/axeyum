//! Toward `cos (8/5) < 0` — π's rung 2 (`docs/plan/status/169-pi.md`).
//!
//! This file carries the general theorems that rung 2 needs and that nothing
//! in the tree had. Neither mentions cosine.
//!
//! ## 1. [`declare_converges_upper_bound_shift`] — `CReal.converges_upper_bound_shift`
//!
//! `∀ s f L b, (∀ n, le (f (Nat.add n s)) b) → Converges f L → le L b`: the
//! EVENTUAL upper bound, the mirror of
//! [`CRealPrelude::converges_lower_bound_shift`].
//! `creal/alternating.rs::declare_alternating_upper_bound`'s own doc comment
//! records that "this development has no `converges_upper_bound_shift`" and
//! then performs the negation route INLINE, privately, on its own concrete
//! sequence — hiding place 2 of `CLAUDE.md`'s retrieval section, one
//! declaration away from being reusable. It is that route, lifted to a named,
//! general theorem: `neg_le_neg` turns the eventual upper bound into an
//! eventual LOWER bound on the negated sequence, `converges_neg` supplies the
//! negated limit, [`CRealPrelude::converges_lower_bound_shift`] closes `le
//! (neg b) (neg L)`, and one more `neg_le_neg` plus `double_neg` on each side
//! (`le_congr`) flips it back.
//!
//! ## 2. [`declare_alternating_upper_bound_tail`] — `CReal.alternatingUpperBoundTail`
//!
//! The Leibniz upper bound requiring antitonicity only **from index 1**:
//!
//! ```text
//! ∀ a, (∀ k, le zero (a k)) → (∀ k, le (a (succ (succ k))) (a (succ k))) →
//!   ∀ L, Converges (sumRange (fun k => mul (pow (neg one) k) (a k))) L →
//!     le L (sumRange (fun k => mul (pow (neg one) k) (a k)) 3)
//! ```
//!
//! [`CRealPrelude::alternating_upper_bound`] cannot be pointed at cosine's
//! series at `8/5`, and the reason is arithmetic rather than formal: its
//! `hdec` premise is the GLOBAL `∀ k, a (succ k) ≤ a k`, and cosine's
//! magnitude sequence `a k = (8/5)^{2k}/(2k)!` has `a 0 = 1 < a 1 = 32/25`.
//! The tail from `k = 1` is antitone (`a (k+1)/a k = (64/25)/((2k+1)(2k+2)) ≤
//! (64/25)/12 < 1` for `k ≥ 1`), which is exactly this theorem's hypothesis.
//!
//! **The route is a CLAMP, not a shift**, and that choice is the whole reason
//! this is tractable. `169-pi.md` proposed re-indexing the series by one
//! (`b k := a (k+1)`, limit `T = 1 − cos(8/5)`); that needs a `Converges`
//! witness for a series this development does not have one for, and building
//! it runs into `Converges`'s own index-`0` obligation, which no "eventually
//! equal" bridge can discharge for an arbitrary sequence. Instead, define
//!
//! ```text
//! â k := a (Nat.succ (Nat.pred k))
//! ```
//!
//! — `a` with its index-`0` value REPLACED by its index-`1` value, chosen in
//! that spelling because `Nat.pred` makes both halves free: `â 0 ≡ a 1` and
//! `â (succ j) ≡ a (succ j)`, both by `ι` alone. `â` IS globally antitone (at
//! `k = 0` by `le_refl`, and at `k = succ j` by the tail hypothesis), so
//! [`CRealPrelude::alternating_bracket_upper`] applies to it unchanged. Its
//! partial sums differ from `a`'s by the single CONSTANT `c := a 1 − a 0` at
//! every index `≥ 1` ([`sum_shift_identity`], one induction), so the constant
//! cancels off both sides of the bracket's conclusion and what survives is a
//! statement about `a`'s OWN partial sums — whose `Converges` witness is the
//! hypothesis in hand. [`declare_converges_upper_bound_shift`] then closes the
//! limit at shift `s := 2`.

use super::convergence::converges_applied;
use super::trig::{
    cabs, cadd, cle, cmul, cneg, cpow, czero, double_neg, echain, erefl, esymm, one_c,
};
use super::{CRealPrelude, creal_ty};
use crate::KernelError;
use crate::env::Declaration;
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::nat_prelude::{NatOps, NatPrelude};

// ---------------------------------------------------------------------------
// `CReal.converges_upper_bound_shift`.
// ---------------------------------------------------------------------------

/// `CReal.converges_upper_bound_shift`. See
/// [`CRealPrelude::converges_upper_bound_shift`] and this module's own
/// documentation.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
pub(super) fn declare_converges_upper_bound_shift(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = creal_ty(d, p);
    let seq_ty = d.arrow(nat, carrier);

    let s_fv = d.fresh_fvar();
    let s = d.kernel().fvar(s_fv);
    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let l_fv = d.fresh_fvar();
    let l = d.kernel().fvar(l_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);

    let upper_ty = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let shifted = NatOps::add(d, n, s);
        let f_at = d.apply(f, &[shifted]);
        let claim = cle(d, p, f_at, b);
        d.pi_fv(n_fv, nat, claim)
    };
    let h1_fv = d.fresh_fvar();
    let h1 = d.kernel().fvar(h1_fv);

    let converges_fl = converges_applied(d, p, f, l);
    let h2_fv = d.fresh_fvar();
    let h2 = d.kernel().fvar(h2_fv);

    let target_ty = cle(d, p, l, b);

    // shift_hyp : ∀ n, le (neg b) (neg (f (add n s))) -- exactly the shape
    // `converges_lower_bound_shift` wants for the NEGATED sequence.
    let neg_b = cneg(d, p, b);
    let shift_hyp = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let shifted = NatOps::add(d, n, s);
        let f_at = d.apply(f, &[shifted]);
        let at_n = d.apply(h1, &[n]);
        let flipped = d.lemma(p.neg_le_neg, &[f_at, b, at_n]);
        d.lam_fv(n_fv, nat, flipped)
    };

    let neg_f_lam = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let f_n = d.apply(f, &[n]);
        let neg_f_n = cneg(d, p, f_n);
        d.lam_fv(n_fv, nat, neg_f_n)
    };
    let neg_l = cneg(d, p, l);
    let converges_neg_hyp = d.const_app(p.converges_neg, &[f, l, h2]);
    let lower = d.const_app(
        p.converges_lower_bound_shift,
        &[s, neg_b, neg_f_lam, neg_l, shift_hyp, converges_neg_hyp],
    );
    // lower : le (neg b) (neg L)

    let flipped_back = d.lemma(p.neg_le_neg, &[neg_b, neg_l, lower]);
    // flipped_back : le (neg (neg L)) (neg (neg b))
    let nn_l = cneg(d, p, neg_l);
    let nn_b = cneg(d, p, neg_b);
    let dn_l = double_neg(d, p, l);
    let dn_b = double_neg(d, p, b);
    let result = d.lemma(p.le_congr, &[nn_l, l, nn_b, b, dn_l, dn_b, flipped_back]);

    let value = {
        let with_h2 = d.lam_fv(h2_fv, converges_fl, result);
        let with_h1 = d.lam_fv(h1_fv, upper_ty, with_h2);
        let with_b = d.lam_fv(b_fv, carrier, with_h1);
        let with_l = d.lam_fv(l_fv, carrier, with_b);
        let with_f = d.lam_fv(f_fv, seq_ty, with_l);
        d.lam_fv(s_fv, nat, with_f)
    };
    let ty = {
        let after_h2 = d.arrow(converges_fl, target_ty);
        let after_h1 = d.arrow(upper_ty, after_h2);
        let with_b = d.pi_fv(b_fv, carrier, after_h1);
        let with_l = d.pi_fv(l_fv, carrier, with_b);
        let with_f = d.pi_fv(f_fv, seq_ty, with_l);
        d.pi_fv(s_fv, nat, with_f)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.converges_upper_bound_shift,
        uparams: vec![],
        ty,
        value,
    })
}

// ---------------------------------------------------------------------------
// Local term builders -- the `a`-generic Leibniz shapes, and the small ring
// identities this file needs and `CRealPrelude` does not name.
// ---------------------------------------------------------------------------

/// `λ k, mul (pow (neg one) k) (a k)` -- the signed term. Identical in shape
/// to `creal/alternating.rs`'s own private `build_t_lam`, so the closures this
/// file builds are alpha-equivalent (hence defeq) to the ones
/// [`CRealPrelude::alternating_bracket_upper`]'s stored type mentions once `a`
/// is substituted.
pub(super) fn build_t_lam(d: &mut IntDev<'_>, p: CRealPrelude, a_fn: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let one_cc = one_c(d, p);
    let neg_one = cneg(d, p, one_cc);
    let sign_k = cpow(d, p, neg_one, k);
    let a_k = d.apply(a_fn, &[k]);
    let body = cmul(d, p, sign_k, a_k);
    d.lam_fv(k_fv, nat, body)
}

/// `sumRange t n`.
pub(super) fn sum_at(d: &mut IntDev<'_>, p: CRealPrelude, t_lam: ExprId, n: ExprId) -> ExprId {
    d.const_app(p.sum_range, &[t_lam, n])
}

/// `E x := sumRange t (add x x)`.
fn e_of(d: &mut IntDev<'_>, p: CRealPrelude, t_lam: ExprId, x: ExprId) -> ExprId {
    let dbl = d.add(x, x);
    sum_at(d, p, t_lam, dbl)
}

/// `O x := sumRange t (succ (add x x))`.
fn o_of(d: &mut IntDev<'_>, p: CRealPrelude, t_lam: ExprId, x: ExprId) -> ExprId {
    let dbl = d.add(x, x);
    let s = d.succ(dbl);
    sum_at(d, p, t_lam, s)
}

/// `Equiv (add zero x) x` -- `add_comm` then `add_zero`. There is no
/// `CReal.zero_add`.
fn zero_add_c(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId) -> ExprId {
    let zero_c = czero(d, p);
    let lhs = cadd(d, p, zero_c, x);
    let mid = cadd(d, p, x, zero_c);
    let comm = d.lemma(p.add_comm, &[zero_c, x]);
    let az = d.lemma(p.add_zero, &[x]);
    echain(d, p, lhs, &[(mid, comm), (x, az)])
}

/// `Equiv (mul one x) x` -- `mul_comm` then `mul_one`. There is no
/// `CReal.one_mul`.
fn one_mul_c(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId) -> ExprId {
    let one_cc = one_c(d, p);
    let lhs = cmul(d, p, one_cc, x);
    let mid = cmul(d, p, x, one_cc);
    let comm = d.lemma(p.mul_comm, &[one_cc, x]);
    let mo = d.lemma(p.mul_one, &[x]);
    echain(d, p, lhs, &[(mid, comm), (x, mo)])
}

/// `(target, proof)` with `target = add (add x z) y` and
/// `proof : Equiv (add (add x y) z) target` -- the additive right-commutation
/// this file uses to slide the clamp constant past a newly-added term.
fn add_right_comm_c(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    x: ExprId,
    y: ExprId,
    z: ExprId,
) -> (ExprId, ExprId) {
    let xy = cadd(d, p, x, y);
    let start = cadd(d, p, xy, z);
    let yz = cadd(d, p, y, z);
    let mid1 = cadd(d, p, x, yz);
    let assoc1 = d.lemma(p.add_assoc, &[x, y, z]); // Equiv start mid1
    let zy = cadd(d, p, z, y);
    let mid2 = cadd(d, p, x, zy);
    let comm = d.lemma(p.add_comm, &[y, z]); // Equiv yz zy
    let refl_x = erefl(d, p, x);
    let cg = d.lemma(p.add_congr, &[x, x, yz, zy, refl_x, comm]); // Equiv mid1 mid2
    let xz = cadd(d, p, x, z);
    let target = cadd(d, p, xz, y);
    let assoc2 = d.lemma(p.add_assoc, &[x, z, y]); // Equiv target mid2
    let assoc2_symm = esymm(d, p, target, mid2, assoc2); // Equiv mid2 target
    let proof = echain(
        d,
        p,
        start,
        &[(mid1, assoc1), (mid2, cg), (target, assoc2_symm)],
    );
    (target, proof)
}

/// `Equiv (add (add w c) (neg c)) w` -- the collapse [`le_cancel_right`] uses
/// on each side.
fn add_then_sub(d: &mut IntDev<'_>, p: CRealPrelude, w: ExprId, c: ExprId) -> ExprId {
    let neg_c = cneg(d, p, c);
    let wc = cadd(d, p, w, c);
    let start = cadd(d, p, wc, neg_c);
    let c_negc = cadd(d, p, c, neg_c);
    let mid = cadd(d, p, w, c_negc);
    let assoc = d.lemma(p.add_assoc, &[w, c, neg_c]); // Equiv start mid
    let zero_c = czero(d, p);
    let an = d.lemma(p.add_neg, &[c]); // Equiv c_negc zero
    let refl_w = erefl(d, p, w);
    let w_zero = cadd(d, p, w, zero_c);
    let cg = d.lemma(p.add_congr, &[w, w, c_negc, zero_c, refl_w, an]); // Equiv mid w_zero
    let az = d.lemma(p.add_zero, &[w]); // Equiv w_zero w
    echain(d, p, start, &[(mid, assoc), (w_zero, cg), (w, az)])
}

/// From `h : le (add x c) (add y c)`, gives `le x y`. `CRealPrelude` has no
/// additive cancellation for `le`; this adds `neg c` to both sides
/// (`add_le_add` against `le_refl`) and collapses via [`add_then_sub`].
fn le_cancel_right(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    x: ExprId,
    y: ExprId,
    c: ExprId,
    h: ExprId,
) -> ExprId {
    let neg_c = cneg(d, p, c);
    let refl_neg = d.lemma(p.le_refl, &[neg_c]);
    let xc = cadd(d, p, x, c);
    let yc = cadd(d, p, y, c);
    let grown = d.lemma(p.add_le_add, &[xc, yc, neg_c, neg_c, h, refl_neg]);
    // grown : le (add xc neg_c) (add yc neg_c)
    let lhs = cadd(d, p, xc, neg_c);
    let rhs = cadd(d, p, yc, neg_c);
    let cx = add_then_sub(d, p, x, c);
    let cy = add_then_sub(d, p, y, c);
    d.lemma(p.le_congr, &[lhs, x, rhs, y, cx, cy, grown])
}

/// `Eq Nat (add (add a b) (add c e)) (add (add a c) (add b e))` -- reproduced
/// in shape from `creal/alternating.rs`'s own private helper of the same name,
/// which this file cannot reach.
fn add_regroup_four(
    d: &mut IntDev<'_>,
    np: NatPrelude,
    a: ExprId,
    b: ExprId,
    c: ExprId,
    e: ExprId,
) -> ExprId {
    let ab = d.add(a, b);
    let ce = d.add(c, e);
    let start = d.add(ab, ce);

    let abc = d.add(ab, c);
    let step1 = d.add(abc, e);
    let h1 = {
        let fwd = d.lemma(np.add_assoc, &[ab, c, e]);
        d.symm(step1, start, fwd)
    };

    let ac = d.add(a, c);
    let acb = d.add(ac, b);
    let step2 = d.add(acb, e);
    let h2 = {
        let h_comm = d.lemma(np.add_right_comm, &[a, b, c]);
        d.congr(abc, acb, h_comm, &|d, x| d.add(x, e))
    };

    let be = d.add(b, e);
    let target = d.add(ac, be);
    let h3 = d.lemma(np.add_assoc, &[ac, b, e]);

    let (_end, proof) = d.chain(start, &[(step1, h1), (step2, h2), (target, h3)]);
    proof
}

/// `Eq Nat (add (add k k) (add m m)) (add (add m k) (add m k))`.
fn kk_mm_regroup(d: &mut IntDev<'_>, np: NatPrelude, k: ExprId, m: ExprId) -> ExprId {
    let step = add_regroup_four(d, np, k, k, m, m);
    let km = d.add(k, m);
    let mk = d.add(m, k);
    let comm = d.lemma(np.add_comm, &[k, m]);
    let swap = d.congr(km, mk, comm, &|d, x| d.add(x, x));
    let kk = d.add(k, k);
    let mm = d.add(m, m);
    let start = d.add(kk, mm);
    let mid = d.add(km, km);
    let end = d.add(mk, mk);
    let (_, proof) = d.chain(start, &[(mid, step), (end, swap)]);
    proof
}

// ---------------------------------------------------------------------------
// `CReal.alternatingUpperBoundTail`.
// ---------------------------------------------------------------------------

/// `CReal.alternatingUpperBoundTail`. See
/// [`CRealPrelude::alternating_upper_bound_tail`] and this module's own
/// documentation for the clamp `â k := a (succ (pred k))` and why it is used
/// in place of `169-pi.md`'s proposed index shift.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
#[allow(clippy::too_many_lines)]
pub(super) fn declare_alternating_upper_bound_tail(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = creal_ty(d, p);
    let fn_ty = d.arrow(nat, carrier);
    let np = p.rat.int.nat;

    let a_fv = d.fresh_fvar();
    let a_fn = d.kernel().fvar(a_fv);

    let hnn_fv = d.fresh_fvar();
    let hnn = d.kernel().fvar(hnn_fv);
    let hnn_ty = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let zero_c = czero(d, p);
        let a_k = d.apply(a_fn, &[k]);
        let body = cle(d, p, zero_c, a_k);
        d.pi_fv(k_fv, nat, body)
    };

    let htail_fv = d.fresh_fvar();
    let htail = d.kernel().fvar(htail_fv);
    let htail_ty = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let sk = d.succ(k);
        let ssk = d.succ(sk);
        let a_ssk = d.apply(a_fn, &[ssk]);
        let a_sk = d.apply(a_fn, &[sk]);
        let body = cle(d, p, a_ssk, a_sk);
        d.pi_fv(k_fv, nat, body)
    };

    let t_lam = build_t_lam(d, p, a_fn);
    let f_expr = d.const_app(p.sum_range, &[t_lam]);

    let l_fv = d.fresh_fvar();
    let l = d.kernel().fvar(l_fv);
    let converges_ty = converges_applied(d, p, f_expr, l);
    let hconv_fv = d.fresh_fvar();
    let hconv = d.kernel().fvar(hconv_fv);

    // The clamp: `â k := a (succ (pred k))`. `â 0 ≡ a 1` and `â (succ j) ≡ a
    // (succ j)`, both by `ι` on `Nat.pred`'s own recursor.
    let a_hat = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let pk = d.pred(k);
        let spk = d.succ(pk);
        let body = d.apply(a_fn, &[spk]);
        d.lam_fv(k_fv, nat, body)
    };
    let t_hat = build_t_lam(d, p, a_hat);

    let hnn_hat = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let pk = d.pred(k);
        let spk = d.succ(pk);
        let at = d.apply(hnn, &[spk]);
        d.lam_fv(k_fv, nat, at)
    };

    // `∀ k, le (â (succ k)) (â k)` -- GLOBAL antitonicity for the clamp, by
    // cases on `k`: at `0` both sides are `a 1` (`le_refl`), at `succ j` this
    // is exactly `htail j`.
    let hdec_hat = {
        let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
            let sx = d.succ(x);
            let psx = d.pred(sx);
            let spsx = d.succ(psx);
            let lhs = d.apply(a_fn, &[spsx]);
            let px = d.pred(x);
            let spx = d.succ(px);
            let rhs = d.apply(a_fn, &[spx]);
            cle(d, p, lhs, rhs)
        };
        let base = |d: &mut IntDev<'_>| -> ExprId {
            let one_nat = d.num(1);
            let a_one = d.apply(a_fn, &[one_nat]);
            d.lemma(p.le_refl, &[a_one])
        };
        let step = |d: &mut IntDev<'_>, j: ExprId, _ih: ExprId| -> ExprId { d.apply(htail, &[j]) };
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let body = d.induct(&motive, &base, &step, k);
        d.lam_fv(k_fv, nat, body)
    };

    // The clamp constant `c := a 1 - a 0`.
    let zero_nat = d.num(0);
    let one_nat = d.num(1);
    let a0 = d.apply(a_fn, &[zero_nat]);
    let a1 = d.apply(a_fn, &[one_nat]);
    let neg_a0 = cneg(d, p, a0);
    let c = cadd(d, p, a1, neg_a0);

    // `∀ n, Equiv (sumRange t̂ (succ n)) (add (sumRange t (succ n)) c)` -- the
    // clamp changes the partial sums by exactly `c`, at every index `>= 1`.
    let shift_id_lam = {
        let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
            let sx = d.succ(x);
            let lhs = sum_at(d, p, t_hat, sx);
            let rhs0 = sum_at(d, p, t_lam, sx);
            let rhs = cadd(d, p, rhs0, c);
            d.const_app(p.equiv, &[lhs, rhs])
        };
        let base = |d: &mut IntDev<'_>| -> ExprId {
            let zero_c = czero(d, p);
            let one_cc = one_c(d, p);
            let m1 = cmul(d, p, one_cc, a1);
            let lhs = cadd(d, p, zero_c, m1);
            let m0 = cmul(d, p, one_cc, a0);
            let n_term = cadd(d, p, zero_c, m0);
            let rhs = cadd(d, p, n_term, c);

            let za = zero_add_c(d, p, m1);
            let om = one_mul_c(d, p, a1);
            let hl = echain(d, p, lhs, &[(m1, za), (a1, om)]);

            let za0 = zero_add_c(d, p, m0);
            let om0 = one_mul_c(d, p, a0);
            let hn = echain(d, p, n_term, &[(m0, za0), (a0, om0)]);

            let refl_c = erefl(d, p, c);
            let add_a0_c = cadd(d, p, a0, c);
            let r2 = d.lemma(p.add_congr, &[n_term, a0, c, c, hn, refl_c]);

            let a0_a1 = cadd(d, p, a0, a1);
            let b1 = cadd(d, p, a0_a1, neg_a0);
            let assoc = d.lemma(p.add_assoc, &[a0, a1, neg_a0]);
            let assoc_s = esymm(d, p, b1, add_a0_c, assoc);
            let a1_a0 = cadd(d, p, a1, a0);
            let comm = d.lemma(p.add_comm, &[a0, a1]);
            let refl_neg = erefl(d, p, neg_a0);
            let b2 = cadd(d, p, a1_a0, neg_a0);
            let cg = d.lemma(p.add_congr, &[a0_a1, a1_a0, neg_a0, neg_a0, comm, refl_neg]);
            let a0_nega0 = cadd(d, p, a0, neg_a0);
            let b3 = cadd(d, p, a1, a0_nega0);
            let assoc2 = d.lemma(p.add_assoc, &[a1, a0, neg_a0]);
            let an = d.lemma(p.add_neg, &[a0]);
            let refl_a1 = erefl(d, p, a1);
            let a1_zero = cadd(d, p, a1, zero_c);
            let cg2 = d.lemma(p.add_congr, &[a1, a1, a0_nega0, zero_c, refl_a1, an]);
            let az = d.lemma(p.add_zero, &[a1]);
            let r3 = echain(
                d,
                p,
                add_a0_c,
                &[
                    (b1, assoc_s),
                    (b2, cg),
                    (b3, assoc2),
                    (a1_zero, cg2),
                    (a1, az),
                ],
            );
            let hr = echain(d, p, rhs, &[(add_a0_c, r2), (a1, r3)]);
            let hr_s = esymm(d, p, rhs, a1, hr);
            echain(d, p, lhs, &[(a1, hl), (rhs, hr_s)])
        };
        let step = |d: &mut IntDev<'_>, j: ExprId, ih: ExprId| -> ExprId {
            let sj = d.succ(j);
            let x = sum_at(d, p, t_hat, sj);
            let y = sum_at(d, p, t_lam, sj);
            let one_cc = one_c(d, p);
            let neg_one = cneg(d, p, one_cc);
            let sign = cpow(d, p, neg_one, sj);
            let a_sj = d.apply(a_fn, &[sj]);
            let v = cmul(d, p, sign, a_sj);

            let y_c = cadd(d, p, y, c);
            let refl_v = erefl(d, p, v);
            let x_v = cadd(d, p, x, v);
            let yc_v = cadd(d, p, y_c, v);
            let s1 = d.lemma(p.add_congr, &[x, y_c, v, v, ih, refl_v]);
            let (target, s2) = add_right_comm_c(d, p, y, c, v);
            echain(d, p, x_v, &[(yc_v, s1), (target, s2)])
        };
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let body = d.induct(&motive, &base, &step, n);
        d.lam_fv(n_fv, nat, body)
    };

    // `∀ n, le (sumRange t̂ (add n 2)) (Ô 1)` -- the clamp's bracket at base
    // `m := 1`, bridged over an arbitrary `n` by the computed parity split.
    let m = d.num(1);
    let m_m = d.add(m, m);
    let o_m = o_of(d, p, t_hat, m);
    let direct_hyp_lam = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let two_nat = d.num(2);
        let k = d.div(n, two_nat);
        let kk = d.add(k, k);
        let skk = d.succ(kk);
        let left_ty = d.eq(n, kk);
        let right_ty = d.eq(n, skk);
        let even_or_odd_n = d.lemma(np.even_or_odd, &[n]);
        let n_mm = d.add(n, m_m);
        let s_n_mm = sum_at(d, p, t_hat, n_mm);
        let direct_target = cle(d, p, s_n_mm, o_m);

        let mk = d.add(m, k);
        let e_mk = e_of(d, p, t_hat, mk);
        let o_mk = o_of(d, p, t_hat, mk);
        let upper_left_ty = cle(d, p, e_mk, o_m);
        let upper_right_ty = cle(d, p, o_mk, o_m);
        let upper_at_mk = d.const_app(
            p.alternating_bracket_upper,
            &[a_hat, hnn_hat, hdec_hat, m, k],
        );
        let upper_left = d.and_left(upper_left_ty, upper_right_ty, upper_at_mk);
        let upper_right = d.and_right(upper_left_ty, upper_right_ty, upper_at_mk);

        let rhs0 = d.add(mk, mk);
        let rhs1 = d.succ(rhs0);
        let core_eq = kk_mm_regroup(d, np, k, m);
        let lhs0 = d.add(kk, m_m);

        let on_left = |d: &mut IntDev<'_>, heq: ExprId| -> ExprId {
            let symm_heq = d.symm(n, kk, heq);
            let congr_step = d.congr(kk, n, symm_heq, &|d, x| d.add(x, m_m));
            let symm_core = d.symm(lhs0, rhs0, core_eq);
            let h_final = d.trans(rhs0, lhs0, n_mm, symm_core, congr_step);
            let motive = d.eq_motive(rhs0, &|d, x| {
                let sx = sum_at(d, p, t_hat, x);
                cle(d, p, sx, o_m)
            });
            d.transport(rhs0, motive, upper_left, n_mm, h_final)
        };

        let on_right = |d: &mut IntDev<'_>, heq: ExprId| -> ExprId {
            let succ_add_eq = d.lemma(np.succ_add, &[kk, m_m]);
            let mid = d.succ(lhs0);
            let succ_congr = d.congr(lhs0, rhs0, core_eq, &|d, x| d.succ(x));
            let lhs1 = d.add(skk, m_m);
            let (_, chain_proof) = d.chain(lhs1, &[(mid, succ_add_eq), (rhs1, succ_congr)]);
            let symm_heq = d.symm(n, skk, heq);
            let congr_step = d.congr(skk, n, symm_heq, &|d, x| d.add(x, m_m));
            let symm_chain = d.symm(lhs1, rhs1, chain_proof);
            let h_final = d.trans(rhs1, lhs1, n_mm, symm_chain, congr_step);
            let motive = d.eq_motive(rhs1, &|d, x| {
                let sx = sum_at(d, p, t_hat, x);
                cle(d, p, sx, o_m)
            });
            d.transport(rhs1, motive, upper_right, n_mm, h_final)
        };

        let or_body = d.or_elim(
            left_ty,
            right_ty,
            direct_target,
            even_or_odd_n,
            &on_left,
            &on_right,
        );
        d.lam_fv(n_fv, nat, or_body)
    };

    // Transport the clamp's bound back onto `a`'s OWN partial sums: the
    // constant `c` sits on both sides and cancels.
    let two_nat = d.num(2);
    let three_nat = d.num(3);
    let b_term = sum_at(d, p, t_lam, three_nat);
    let upper_lam = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let sn = d.succ(n);
        let ssn = d.succ(sn);
        let hyp = d.apply(direct_hyp_lam, &[n]);
        let a_side = sum_at(d, p, t_hat, ssn);
        let a_prime = sum_at(d, p, t_lam, ssn);
        let a_shift = cadd(d, p, a_prime, c);
        let b_shift = cadd(d, p, b_term, c);
        let id_n = d.apply(shift_id_lam, &[sn]);
        let id_b = d.apply(shift_id_lam, &[two_nat]);
        let moved = d.lemma(
            p.le_congr,
            &[a_side, a_shift, o_m, b_shift, id_n, id_b, hyp],
        );
        let cancelled = le_cancel_right(d, p, a_prime, b_term, c, moved);
        d.lam_fv(n_fv, nat, cancelled)
    };

    let result = d.const_app(
        p.converges_upper_bound_shift,
        &[two_nat, f_expr, l, b_term, upper_lam, hconv],
    );

    let target_ty = cle(d, p, l, b_term);
    let value = {
        let with_hconv = d.lam_fv(hconv_fv, converges_ty, result);
        let with_l = d.lam_fv(l_fv, carrier, with_hconv);
        let with_htail = d.lam_fv(htail_fv, htail_ty, with_l);
        let with_hnn = d.lam_fv(hnn_fv, hnn_ty, with_htail);
        d.lam_fv(a_fv, fn_ty, with_hnn)
    };
    let ty = {
        let after_hconv = d.arrow(converges_ty, target_ty);
        let with_l = d.pi_fv(l_fv, carrier, after_hconv);
        let with_htail = d.arrow(htail_ty, with_l);
        let with_hnn = d.arrow(hnn_ty, with_htail);
        d.pi_fv(a_fv, fn_ty, with_hnn)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.alternating_upper_bound_tail,
        uparams: vec![],
        ty,
        value,
    })
}

// ---------------------------------------------------------------------------
// π rung 2, items 1-2 of `docs/plan/status/174-pi-rung2.md`'s four-item
// list: `CReal.cosWideTailNonneg` and `CReal.cosWideTailAntitone`, the
// `hnn`/`htail` premises [`declare_alternating_upper_bound_tail`]'s
// `CReal.alternatingUpperBoundTail` needs when instantiated at cosine's
// magnitude sequence `a j := mul (expTerm (add j j)) (pow R (add j j))`,
// `R := ofRat (natDivSucc 8 4) = 8/5`.
//
// Items 3-4 (the `Converges` witness at `cosFnWide R` and the final numeric
// evaluation) are NOT built here. See `docs/plan/status/174-pi-rung2.md` for
// why: bridging `cosFnWideUniformConverges`'s `UniformConvergesOn`-shaped
// `close_within` output down to `Converges`'s own `Within`-on-rationals
// shape has no existing lemma anywhere in this tree (confirmed by reading
// `CReal.within_of_two_sided_le`, the one general "real inequality -> Within
// at a chosen index" bridge that exists, plus `CReal.add`'s own Bishop index
// shift) and is a separate, substantial undertaking on the order of
// `CReal.converges_add`'s own construction.
// ---------------------------------------------------------------------------

/// `Rat.natDivSucc 8 4 = 8/5` -- reproduced verbatim from
/// `trig_fn.rs`'s own private `r_domain_rat` (Rust privacy: sibling module).
fn r_wide_rat(d: &mut IntDev<'_>, p: CRealPrelude) -> ExprId {
    let n8 = d.num(8);
    let n4 = d.num(4);
    d.const_app(p.rat.nat_div_succ, &[n8, n4])
}

/// `CReal.ofRat (Rat.natDivSucc 8 4)` -- `R := 8/5` as a `CReal`.
fn r_wide(d: &mut IntDev<'_>, p: CRealPrelude) -> ExprId {
    let rr = r_wide_rat(d, p);
    d.const_app(p.of_rat, &[rr])
}

/// `le zero R` -- reproduced verbatim from `trig_fn.rs::declare_cos_fn_wide`'s
/// own private `hab0`/`hab_zero_r` (Rust privacy: sibling module).
fn hab_zero_r_wide(d: &mut IntDev<'_>, p: CRealPrelude) -> ExprId {
    let rat = p.rat;
    let zero_r = crate::rat_prelude::ops::rzero(d, rat);
    let r_rat = r_wide_rat(d, p);
    let n8 = d.num(8);
    let n4 = d.num(4);
    let nn = d.lemma(rat.zero_le_nat_div_succ, &[n8, n4]);
    d.lemma(p.of_rat_le, &[zero_r, r_rat, nn])
}

/// `le (pow R 2) (ofNat 3)`, `R := r_wide`: `R = 8/5`, `(8/5)^2 = 64/25 <=
/// 3`. `pow R 2` is DEFEQ to `mul (mul one R) R` (`pow_succ`/`pow_zero`
/// close by `Eq.refl` alone), so the numeric content reduces to `mul R R <=
/// ofNat 3`, closed by `Rat.ble`'s own COMPUTATION on these small literals
/// (`Rat.ble (8/5 * 8/5) (3/1)` reduces to `Bool.true` by iota alone) rather
/// than a hand-rolled `Rat.normalize_cross` battery.
fn pow_r2_le_3(d: &mut IntDev<'_>, p: CRealPrelude, r: ExprId) -> ExprId {
    let rat = p.rat;
    let q = r_wide_rat(d, p);
    let three_nat = d.num(3);
    let zero_nat = d.zero();
    let three_rat = d.const_app(rat.nat_div_succ, &[three_nat, zero_nat]);

    let qq = crate::rat_prelude::ops::rmul(d, q, q);
    let true_c = d.bool_true();
    let ble_val = d.const_app(rat.ble, &[qq, three_rat]);
    let _ = ble_val; // documents the fact being decided; the proof below is `Eq.refl true`
    let refl_true = d.bool_refl(true_c);
    let rat_le = d.lemma(rat.le_of_ble_eq_true, &[qq, three_rat, refl_true]);
    let creal_le = d.lemma(p.of_rat_le, &[qq, three_rat, rat_le]);
    // creal_le : le (ofRat qq) (ofRat three_rat), ofRat three_rat defeq ofNat 3

    let of_rat_mul_eq = d.lemma(p.of_rat_mul, &[q, q]);
    // of_rat_mul_eq : Equiv (mul (ofRat q) (ofRat q)) (ofRat qq) = Equiv rr (ofRat qq)
    let rr = cmul(d, p, r, r);
    let of_rat_qq = d.const_app(p.of_rat, &[qq]);
    let of_rat3 = d.const_app(p.of_rat, &[three_rat]);
    let ha = esymm(d, p, rr, of_rat_qq, of_rat_mul_eq); // Equiv (ofRat qq) rr
    let hb = erefl(d, p, of_rat3);
    let le_rr_3 = d.lemma(
        p.le_congr,
        &[of_rat_qq, rr, of_rat3, of_rat3, ha, hb, creal_le],
    );
    // le_rr_3 : le rr (ofRat three_rat)

    let one_cc = one_c(d, p);
    let one_r = cmul(d, p, one_cc, r);
    let rr_alt = cmul(d, p, one_r, r); // defeq (pow R 2)
    let om = one_mul_c(d, p, r); // Equiv one_r r
    let refl_r = erefl(d, p, r);
    let congr1 = d.lemma(p.mul_congr, &[one_r, r, r, r, om, refl_r]); // Equiv rr_alt rr
    let ha2 = esymm(d, p, rr_alt, rr, congr1); // Equiv rr rr_alt
    let hb2 = erefl(d, p, of_rat3);
    d.lemma(
        p.le_congr,
        &[rr, rr_alt, of_rat3, of_rat3, ha2, hb2, le_rr_3],
    )
    // : le rr_alt (ofRat three_rat), rr_alt defeq (pow R 2)
}

/// `(target, proof)` with `target = mul b (mul a c)` and
/// `proof : Equiv (mul a (mul b c)) target` -- moves a factor `a` past `b`
/// in a three-factor product. Mirrors [`add_right_comm_c`]'s additive shape
/// verbatim, substituting `mul_comm`/`mul_assoc`/`mul_congr` for their
/// additive counterparts.
fn mul_left_comm_c(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    a: ExprId,
    b: ExprId,
    c: ExprId,
) -> (ExprId, ExprId) {
    let bc = cmul(d, p, b, c);
    let start = cmul(d, p, a, bc);
    let ab = cmul(d, p, a, b);
    let mid1 = cmul(d, p, ab, c);
    let assoc1_fwd = d.lemma(p.mul_assoc, &[a, b, c]); // Equiv mid1 start
    let assoc1 = esymm(d, p, mid1, start, assoc1_fwd); // Equiv start mid1
    let ba = cmul(d, p, b, a);
    let mid2 = cmul(d, p, ba, c);
    let comm = d.lemma(p.mul_comm, &[a, b]); // Equiv ab ba
    let refl_c = erefl(d, p, c);
    let cg = d.lemma(p.mul_congr, &[ab, ba, c, c, comm, refl_c]); // Equiv mid1 mid2
    let ac = cmul(d, p, a, c);
    let target = cmul(d, p, b, ac);
    let assoc2 = d.lemma(p.mul_assoc, &[b, a, c]); // Equiv mid2 target
    let proof = echain(d, p, start, &[(mid1, assoc1), (mid2, cg), (target, assoc2)]);
    (target, proof)
}

/// `Eq Nat (succ (succ (add n n))) (add (succ n) (succ n))` -- reproduced
/// from `trig.rs::cos_magnitude_dec`'s own private bridge (Rust privacy:
/// sibling module), generalized from its hardcoded `k` to an arbitrary `n`
/// so this file can instantiate it at `n := succ k` too.
fn dbl_succ_bridge(d: &mut IntDev<'_>, np: NatPrelude, n: ExprId) -> ExprId {
    let sn = d.succ(n);
    let nn = d.add(n, n);
    let snn = d.succ(nn);
    let ssnn = d.succ(snn);
    let sn_n = d.add(sn, n);
    let bridge = d.lemma(np.succ_add, &[n, n]); // Eq sn_n snn
    let bridge_succ = d.congr(sn_n, snn, bridge, &|d, x| d.succ(x)); // Eq (succ sn_n) ssnn
    let succ_sn_n = d.succ(sn_n);
    d.symm(succ_sn_n, ssnn, bridge_succ) // Eq ssnn (succ sn_n), defeq (add (succ n)(succ n))
}

/// `Nat.le 2 (add (succ n) (succ n))` -- the tail bound's Nat-side fact:
/// `idx1 := add (succ n)(succ n)` is `2n+2`, always `>= 2`. One `succ` is
/// free (`Nat.add`'s own iota on its right argument); the second needs
/// `Nat.add_comm` to see the LEFT `succ`, since `Nat.add` cannot peel a
/// `succ` off its left argument by iota alone.
fn two_le_double_succ(d: &mut IntDev<'_>, np: NatPrelude, n: ExprId) -> ExprId {
    let sn = d.succ(n);
    let nn = d.add(n, n);
    let one_nat = d.num(1);
    let h1 = crate::rat_prelude::ops::one_le_succ(d, nn); // Nat.le 1 (succ nn)
    let n_sn = d.add(n, sn);
    let sn_n = d.add(sn, n);
    let comm = d.lemma(np.add_comm, &[sn, n]); // Eq sn_n n_sn
    let comm_rev = d.symm(sn_n, n_sn, comm); // Eq n_sn sn_n
    let motive = d.eq_motive(n_sn, &|d, x| {
        let one_nat = d.num(1);
        NatOps::le(d, one_nat, x)
    });
    let h1_sn_n = d.transport(n_sn, motive, h1, sn_n, comm_rev); // Nat.le 1 sn_n
    d.lemma(np.succ_le_succ, &[one_nat, sn_n, h1_sn_n]) // Nat.le 2 (succ sn_n), defeq idx1
}

/// Given `h2m : Nat.le 2 m`, returns a proof of
/// `le (mul (expTerm (succ (succ m))) (pow R (succ (succ m))))
///     (mul (expTerm m) (pow R m))`
/// -- the core numeric/algebraic content of
/// [`declare_cos_wide_tail_antitone`], generic in the Nat `m` that file
/// always instantiates at `m := add (succ k) (succ k)`. Reduces (via two
/// [`CRealPrelude::exp_term_succ_scale`] applications) to `R² <=
/// (m+1)(m+2)`, closed from `m >= 2` by `(m+1) >= 3`, `(m+2) >= 1` and
/// `R² <= 3` ([`pow_r2_le_3`]).
#[allow(clippy::too_many_lines)]
fn exp_pow_ratio_le(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    r: ExprId,
    hr0: ExprId,
    m: ExprId,
    h2m: ExprId,
) -> ExprId {
    let np = p.rat.int.nat;
    let exp_term_c = d.kernel().const_(p.exp_term, vec![]);
    let sm = d.succ(m);
    let ssm = d.succ(sm);
    let two_nat = d.num(2);
    let three_nat = d.num(3);
    let one_nat = d.num(1);

    // --- Nat side: 3 <= sm, 1 <= ssm, 3 <= K := sm*ssm.
    let h3sm = d.lemma(np.succ_le_succ, &[two_nat, m, h2m]); // Nat.le 3 sm
    let h1ssm = crate::rat_prelude::ops::one_le_succ(d, sm); // Nat.le 1 ssm
    let k_nat = d.mul(sm, ssm);
    let sm1 = d.mul(sm, one_nat);
    let scaled = d.lemma(np.mul_le_mul_left, &[sm, one_nat, ssm, h1ssm]); // Le sm1 k_nat
    let mul_one_eq = d.lemma(np.mul_one, &[sm]); // Eq sm1 sm
    let motive_a = d.eq_motive(sm1, &|d, x| NatOps::le(d, x, k_nat));
    let h_sm_le_k = d.transport(sm1, motive_a, scaled, sm, mul_one_eq); // Nat.le sm k_nat
    let h3k = d.lemma(np.le_trans, &[three_nat, sm, k_nat, h3sm, h_sm_le_k]); // Nat.le 3 k_nat

    // --- cast to CReal, chain with R^2 <= 3.
    let of_nat3 = d.const_app(p.of_nat, &[three_nat]);
    let of_nat_k = d.const_app(p.of_nat, &[k_nat]);
    let h3k_creal = d.lemma(p.of_nat_le, &[three_nat, k_nat, h3k]); // le (ofNat 3) (ofNat k_nat)
    let pow2 = cpow(d, p, r, two_nat);
    let pow_r2_3 = pow_r2_le_3(d, p, r); // le pow2 of_nat3
    let pow_r2_k = d.lemma(p.le_trans, &[pow2, of_nat3, of_nat_k, pow_r2_3, h3k_creal]);
    // pow_r2_k : le pow2 of_nat_k

    // --- CORE: le (mul e_ssm pow2) (expTerm m).
    let e_ssm = d.apply(exp_term_c, &[ssm]);
    let e_sm = d.apply(exp_term_c, &[sm]);
    let e_m = d.apply(exp_term_c, &[m]);
    let e_ssm_nn = d.lemma(p.exp_term_nonneg, &[ssm]);
    let h_scaled = d.lemma(
        p.mul_le_mul_of_nonneg_left,
        &[e_ssm, pow2, of_nat_k, e_ssm_nn, pow_r2_k],
    );
    // h_scaled : le (mul e_ssm pow2) (mul e_ssm of_nat_k)

    // equality chain: mul e_ssm of_nat_k ~ expTerm m.
    let start = cmul(d, p, e_ssm, of_nat_k);
    let commute1 = d.lemma(p.mul_comm, &[e_ssm, of_nat_k]); // Equiv start (mul of_nat_k e_ssm)
    let s1 = cmul(d, p, of_nat_k, e_ssm);

    let of_nat_mul_eq = d.lemma(p.of_nat_mul, &[sm, ssm]); // Equiv of_nat_k (mul (ofNat sm) (ofNat ssm))
    let of_nat_sm = d.const_app(p.of_nat, &[sm]);
    let of_nat_ssm = d.const_app(p.of_nat, &[ssm]);
    let sm_ssm = cmul(d, p, of_nat_sm, of_nat_ssm);
    let refl_essm = erefl(d, p, e_ssm);
    let leg2 = d.lemma(
        p.mul_congr,
        &[of_nat_k, sm_ssm, e_ssm, e_ssm, of_nat_mul_eq, refl_essm],
    );
    // leg2 : Equiv s1 (mul sm_ssm e_ssm)
    let s2 = cmul(d, p, sm_ssm, e_ssm);

    let assoc = d.lemma(p.mul_assoc, &[of_nat_sm, of_nat_ssm, e_ssm]);
    // assoc : Equiv s2 (mul of_nat_sm (mul of_nat_ssm e_ssm))
    let ssm_essm = cmul(d, p, of_nat_ssm, e_ssm);
    let s3 = cmul(d, p, of_nat_sm, ssm_essm);

    let e_scale_1 = d.lemma(p.exp_term_succ_scale, &[sm]); // Equiv ssm_essm e_sm
    let refl_ofnatsm = erefl(d, p, of_nat_sm);
    let leg4 = d.lemma(
        p.mul_congr,
        &[
            of_nat_sm,
            of_nat_sm,
            ssm_essm,
            e_sm,
            refl_ofnatsm,
            e_scale_1,
        ],
    );
    // leg4 : Equiv s3 (mul of_nat_sm e_sm)
    let s4 = cmul(d, p, of_nat_sm, e_sm);

    let e_scale_2 = d.lemma(p.exp_term_succ_scale, &[m]); // Equiv s4 e_m

    let chain_equiv = echain(
        d,
        p,
        start,
        &[
            (s1, commute1),
            (s2, leg2),
            (s3, assoc),
            (s4, leg4),
            (e_m, e_scale_2),
        ],
    );
    // chain_equiv : Equiv start e_m

    let essm_pow2 = cmul(d, p, e_ssm, pow2);
    let refl_lhs = erefl(d, p, essm_pow2);
    let core = d.lemma(
        p.le_congr,
        &[
            essm_pow2,
            essm_pow2,
            start,
            e_m,
            refl_lhs,
            chain_equiv,
            h_scaled,
        ],
    );
    // core : le essm_pow2 e_m

    // --- scale by pow R m on the left, then repack the LHS/RHS shapes.
    let pow_m = cpow(d, p, r, m);
    let pow_m_nn = d.lemma(p.pow_nonneg, &[r, hr0, m]);
    let scaled_core = d.lemma(
        p.mul_le_mul_of_nonneg_left,
        &[pow_m, essm_pow2, e_m, pow_m_nn, core],
    );
    // scaled_core : le (mul pow_m essm_pow2) (mul pow_m e_m)

    let (comm_target, comm_proof) = mul_left_comm_c(d, p, pow_m, e_ssm, pow2);
    // comm_proof : Equiv (mul pow_m essm_pow2) comm_target
    let mul_pow_m_pow2 = cmul(d, p, pow_m, pow2);
    let pow_add_eq = d.lemma(p.pow_add, &[r, m, two_nat]);
    // pow_add_eq : Equiv (pow R (add m 2)) mul_pow_m_pow2, defeq Equiv (pow R ssm) mul_pow_m_pow2
    let pow_r_ssm = cpow(d, p, r, ssm);
    let pow_add_rev = esymm(d, p, pow_r_ssm, mul_pow_m_pow2, pow_add_eq);
    // pow_add_rev : Equiv mul_pow_m_pow2 pow_r_ssm
    let refl_essm2 = erefl(d, p, e_ssm);
    let leg_b = d.lemma(
        p.mul_congr,
        &[
            e_ssm,
            e_ssm,
            mul_pow_m_pow2,
            pow_r_ssm,
            refl_essm2,
            pow_add_rev,
        ],
    );
    // leg_b : Equiv comm_target target_lhs
    let target_lhs = cmul(d, p, e_ssm, pow_r_ssm);
    let mul_pow_m_essm_pow2 = cmul(d, p, pow_m, essm_pow2);
    let lhs_equiv = echain(
        d,
        p,
        mul_pow_m_essm_pow2,
        &[(comm_target, comm_proof), (target_lhs, leg_b)],
    );
    // lhs_equiv : Equiv mul_pow_m_essm_pow2 target_lhs

    let rhs_equiv = d.lemma(p.mul_comm, &[pow_m, e_m]); // Equiv (mul pow_m e_m) (mul e_m pow_m)
    let target_rhs = cmul(d, p, e_m, pow_m);
    let mul_pow_m_em = cmul(d, p, pow_m, e_m);

    d.lemma(
        p.le_congr,
        &[
            mul_pow_m_essm_pow2,
            target_lhs,
            mul_pow_m_em,
            target_rhs,
            lhs_equiv,
            rhs_equiv,
            scaled_core,
        ],
    )
    // : le target_lhs target_rhs = le (mul e_ssm (pow R ssm)) (mul e_m pow_m)
}

/// `CReal.cosWideTailNonneg` -- π rung 2's `hnn` premise:
/// `∀ k, le zero (mul (expTerm (add k k)) (pow R (add k k)))`,
/// `R := ofRat (natDivSucc 8 4) = 8/5`. Direct: [`CRealPrelude::mul_nonneg`]
/// against [`CRealPrelude::exp_term_nonneg`] and [`CRealPrelude::pow_nonneg`].
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
pub(super) fn declare_cos_wide_tail_nonneg(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let r = r_wide(d, p);
    let hr0 = hab_zero_r_wide(d, p);
    let exp_term_c = d.kernel().const_(p.exp_term, vec![]);

    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let dbl = d.add(k, k);
    let x = d.apply(exp_term_c, &[dbl]);
    let y = cpow(d, p, r, dbl);
    let e_nn = d.lemma(p.exp_term_nonneg, &[dbl]);
    let pow_nn = d.lemma(p.pow_nonneg, &[r, hr0, dbl]);
    let body = d.lemma(p.mul_nonneg, &[x, y, e_nn, pow_nn]);
    let value = d.lam_fv(k_fv, nat, body);
    let ty = d.kernel().infer(value)?;
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.cos_wide_tail_nonneg,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CReal.cosWideTailAntitone` -- π rung 2's `htail` premise:
/// `∀ k, le (a (succ (succ k))) (a (succ k))` for `a j := mul (expTerm (add j
/// j)) (pow R (add j j))`, `R := 8/5`. See this file's own module
/// documentation and [`exp_pow_ratio_le`] for the route: reduces to `R² <=
/// (m+1)(m+2)` at `m := add (succ k) (succ k) >= 2`.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
pub(super) fn declare_cos_wide_tail_antitone(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let np = p.rat.int.nat;
    let r = r_wide(d, p);
    let hr0 = hab_zero_r_wide(d, p);

    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let sk = d.succ(k);
    let idx1 = d.add(sk, sk);
    let h2_idx1 = two_le_double_succ(d, np, k);
    let goal_prime = exp_pow_ratio_le(d, p, r, hr0, idx1, h2_idx1);

    let bridge = dbl_succ_bridge(d, np, sk); // Eq (succ (succ idx1)) idx2
    let s_idx1 = d.succ(idx1);
    let ss_idx1 = d.succ(s_idx1);
    let ssk = d.succ(sk);
    let idx2 = d.add(ssk, ssk);

    let exp_term_c = d.kernel().const_(p.exp_term, vec![]);
    let e_idx1 = d.apply(exp_term_c, &[idx1]);
    let p_idx1 = cpow(d, p, r, idx1);
    let rhs_fixed = cmul(d, p, e_idx1, p_idx1);
    let motive = d.eq_motive(ss_idx1, &|d, x| {
        let e = d.kernel().const_(p.exp_term, vec![]);
        let ex = d.apply(e, &[x]);
        let px = cpow(d, p, r, x);
        let lhs = cmul(d, p, ex, px);
        cle(d, p, lhs, rhs_fixed)
    });
    let result = d.transport(ss_idx1, motive, goal_prime, idx2, bridge);

    let value = d.lam_fv(k_fv, nat, result);
    let ty = d.kernel().infer(value)?;
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.cos_wide_tail_antitone,
        uparams: vec![],
        ty,
        value,
    })
}

// ---------------------------------------------------------------------------
// pi rung 2, items 3-4 (`docs/plan/status/174-pi-rung2.md`,
// `docs/plan/status/175-pi-r2b.md`, `docs/plan/status/176-cw-bridge.md`):
// `CReal.cosWideSeriesConverges` (the `Converges` witness
// `alternatingUpperBoundTail` needs) and `CReal.cosWideNonpositive` -- `le
// (cosFnWide R) zero`, the rung's actual target.
// ---------------------------------------------------------------------------

/// `a j := mul (expTerm (add j j)) (pow R (add j j))` -- cosine's magnitude
/// sequence at `R := 8/5`, as a standalone lambda. Built with the EXACT same
/// calls [`declare_cos_wide_tail_nonneg`]/[`declare_cos_wide_tail_antitone`]
/// use inline, so this file's structural-hashing convention (every builder
/// call is interned, so identical calls give the identical `ExprId`) makes
/// `a_wide_lam(d, p, r)` applied at a `k` beta-reduce to the SAME term those
/// two theorems' own stated types already mention -- letting
/// [`declare_alternating_upper_bound_tail`]'s `a` slot be instantiated at
/// this lambda and cite both directly, with no transport.
fn a_wide_lam(d: &mut IntDev<'_>, p: CRealPrelude, r: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let exp_term_c = d.kernel().const_(p.exp_term, vec![]);
    let j_fv = d.fresh_fvar();
    let j = d.kernel().fvar(j_fv);
    let dbl = d.add(j, j);
    let e = d.apply(exp_term_c, &[dbl]);
    let pw = cpow(d, p, r, dbl);
    let body = cmul(d, p, e, pw);
    d.lam_fv(j_fv, nat, body)
}

/// `λ n pt, sumRange (fun j => cosFnTerm j pt) n` -- reproduced verbatim from
/// `trig_fn.rs`'s own private `cos_fn_partial_sums_fn` (Rust privacy: each is
/// a sibling module). Structural hashing makes this the IDENTICAL `ExprId`
/// to what `CReal.cosFnWideUniformConverges`'s own stored type mentions as
/// its `F` argument.
fn cos_fn_partial_sums_fn_local(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    carrier: ExprId,
    nat: ExprId,
) -> ExprId {
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let pt_fv = d.fresh_fvar();
    let pt = d.kernel().fvar(pt_fv);
    let f_pt = {
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let body = d.const_app(p.cos_fn_term, &[j, pt]);
        d.lam_fv(j_fv, nat, body)
    };
    let body = d.const_app(p.sum_range, &[f_pt, n]);
    let with_pt = d.lam_fv(pt_fv, carrier, body);
    d.lam_fv(n_fv, nat, with_pt)
}

/// `CReal.cosWideSeriesConverges : Converges (sumRange t) (cosFnWide R)` --
/// pi rung 2 item 3. Composes `CReal.converges_of_abs_diff_le` with
/// `CReal.cosFnWideUniformConverges`'s own `.spec` at the fixed point `x :=
/// R` -- `docs/plan/status/176-cw-bridge.md`'s predicted route, no transport
/// for the `close_within` shape itself -- bridged, per index, from
/// `cosFnTerm`'s `mul (cosTerm j) (pow R (2j))` shape to `t`'s `mul (pow
/// (neg one) j) (mul (expTerm (2j)) (pow R (2j)))` shape by exactly ONE
/// `mul_assoc` (both `cosTerm` and `cosFnTerm` are `Definition`s, so this
/// unfolds by delta alone, no bridging lemma needed beyond `mul_assoc`
/// itself), lifted across the whole partial sum by `CReal.sumRange_congr`.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
pub(super) fn declare_cos_wide_series_converges(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = creal_ty(d, p);
    let r = r_wide(d, p);
    let hr0 = hab_zero_r_wide(d, p);
    let hrr = d.lemma(p.le_refl, &[r]);
    let zero_c = czero(d, p);

    let a_wide = a_wide_lam(d, p, r);
    let t_lam = build_t_lam(d, p, a_wide);

    let big_f = cos_fn_partial_sums_fn_local(d, p, carrier, nat);
    let cos_fn_wide_c = d.kernel().const_(p.cos_fn_wide, vec![]);
    let u = d.kernel().const_(p.cos_fn_wide_uniform_converges, vec![]);
    let g_r = d.apply(cos_fn_wide_c, &[r]);
    let neg_g_r = cneg(d, p, g_r);

    let rate = d.const_app(p.uconv_rate, &[big_f, cos_fn_wide_c, zero_c, r, u]);
    let spec = d.const_app(p.uconv_spec, &[big_f, cos_fn_wide_c, zero_c, r, u]);

    let f_expr = d.const_app(p.sum_range, &[t_lam]);

    let hyp_lam = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let spec_n = d.apply(spec, &[n, r, hr0, hrr]);

        let cos_fn_term_at_r = {
            let j_fv = d.fresh_fvar();
            let j = d.kernel().fvar(j_fv);
            let body = d.const_app(p.cos_fn_term, &[j, r]);
            d.lam_fv(j_fv, nat, body)
        };

        // `Equiv (cosFnTerm j R) (t j)` at a symbolic `j` -- exactly one
        // `mul_assoc`, both sides reached by delta+beta alone.
        let per_j = {
            let j_fv = d.fresh_fvar();
            let j = d.kernel().fvar(j_fv);
            let jj = d.add(j, j);
            let one_cc = one_c(d, p);
            let neg_one = cneg(d, p, one_cc);
            let sign_j = cpow(d, p, neg_one, j);
            let exp_term_c = d.kernel().const_(p.exp_term, vec![]);
            let e_jj = d.apply(exp_term_c, &[jj]);
            let pow_r_jj = cpow(d, p, r, jj);
            let body = d.lemma(p.mul_assoc, &[sign_j, e_jj, pow_r_jj]);
            d.lam_fv(j_fv, nat, body)
        };

        let heq_sum = d.lemma(p.sum_range_congr, &[cos_fn_term_at_r, t_lam, n, per_j]);
        // heq_sum : Equiv (sumRange cos_fn_term_at_r n) (sumRange t_lam n)

        let f_n_r = d.const_app(p.sum_range, &[cos_fn_term_at_r, n]);
        let t_n = d.const_app(p.sum_range, &[t_lam, n]);

        let refl_neg_g = erefl(d, p, neg_g_r);
        let add_congr_h = d.lemma(
            p.add_congr,
            &[f_n_r, t_n, neg_g_r, neg_g_r, heq_sum, refl_neg_g],
        );
        let diff_orig = d.const_app(p.add, &[f_n_r, neg_g_r]);
        let diff_new = d.const_app(p.add, &[t_n, neg_g_r]);
        let abs_congr_h = d.lemma(p.abs_congr, &[diff_orig, diff_new, add_congr_h]);

        let q_n = d.const_app(p.rat.nat_div_succ, &[rate, n]);
        let target = d.const_app(p.of_rat, &[q_n]);
        let refl_target = erefl(d, p, target);

        let abs_orig = cabs(d, p, diff_orig);
        let abs_new = cabs(d, p, diff_new);

        let close_within_new = d.lemma(
            p.le_congr,
            &[
                abs_orig,
                abs_new,
                target,
                target,
                abs_congr_h,
                refl_target,
                spec_n,
            ],
        );
        d.lam_fv(n_fv, nat, close_within_new)
    };

    let value = d.lemma(p.converges_of_abs_diff_le, &[f_expr, g_r, rate, hyp_lam]);
    let ty = d.kernel().infer(value)?;
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.cos_wide_series_converges,
        uparams: vec![],
        ty,
        value,
    })
}

/// `Rat.normalize (Int.ofNat 1) (Nat.factorial n) (Nat.one_le_factorial n)`
/// -- reproduced verbatim from `exponential.rs`'s own private
/// `inv_factorial` (Rust privacy: sibling module). `CReal.expTerm n :=
/// embed (inv_factorial n)` by DEFINITION, so this is the exact `Rat` value
/// `expTerm n` unfolds to.
fn inv_factorial_local(d: &mut IntDev<'_>, n: ExprId) -> ExprId {
    let one_nat = d.num(1);
    let one_int = d.of_nat(one_nat);
    let denominator = d.factorial(n);
    let np = d.prelude();
    let positive = d.lemma(np.one_le_factorial, &[n]);
    crate::rat_prelude::ops::normalize(d, one_int, denominator, positive)
}

/// `(aj_rat, proof)` with `aj_rat := Rat.mul (inv_factorial dbl) (Rat.pow
/// r_rat dbl)` and `proof : Equiv (mul (expTerm dbl) (pow r dbl)) (ofRat
/// aj_rat)` -- `dbl` a CONCRETE `Nat` literal (0, 2 or 4 at every call
/// site). `expTerm dbl` is DEFEQ to `ofRat (inv_factorial dbl)` (both
/// unfold by delta, so `Equiv.refl` alone closes that leg once cast through
/// the defeq); `pow r dbl ~ ofRat (Rat.pow r_rat dbl)` is
/// [`CRealPrelude::of_rat_pow`]; [`CRealPrelude::of_rat_mul`] folds the
/// product.
fn a_wide_term_as_rat(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    r: ExprId,
    r_rat: ExprId,
    dbl: ExprId,
) -> (ExprId, ExprId) {
    let exp_term_c = d.kernel().const_(p.exp_term, vec![]);
    let e_dbl = d.apply(exp_term_c, &[dbl]);
    let e_refl = erefl(d, p, e_dbl);
    let inv_fact = inv_factorial_local(d, dbl);

    let pow_r_dbl = cpow(d, p, r, dbl);
    let rpow_val = crate::rat_prelude::ops::rpow(d, p.rat, r_rat, dbl);
    let pow_eq = d.lemma(p.of_rat_pow, &[r_rat, dbl]);
    // pow_eq : Equiv pow_r_dbl (ofRat rpow_val)

    let of_rat_inv_fact = d.const_app(p.of_rat, &[inv_fact]);
    let of_rat_rpow = d.const_app(p.of_rat, &[rpow_val]);
    let mul_cg = d.lemma(
        p.mul_congr,
        &[e_dbl, of_rat_inv_fact, pow_r_dbl, of_rat_rpow, e_refl, pow_eq],
    );
    let a_j = cmul(d, p, e_dbl, pow_r_dbl);

    let of_rat_mul_eq = d.lemma(p.of_rat_mul, &[inv_fact, rpow_val]);
    let aj_rat = crate::rat_prelude::ops::rmul(d, inv_fact, rpow_val);
    let of_rat_aj = d.const_app(p.of_rat, &[aj_rat]);

    let mid = cmul(d, p, of_rat_inv_fact, of_rat_rpow);
    let proof = echain(d, p, a_j, &[(mid, mul_cg), (of_rat_aj, of_rat_mul_eq)]);
    (aj_rat, proof)
}

/// `(t_j, qj_rat, proof)` with `t_j := mul (pow (neg one) j_nat) (mul
/// (expTerm dbl_nat) (pow r dbl_nat))` (`t_lam` applied at `j_nat`, delta+
/// beta reduced) and `proof : Equiv t_j (ofRat qj_rat)`. `sign_equiv :
/// Equiv (pow (neg one) j_nat) sign_target` and `sign_rat` is the `Rat`
/// value `sign_target` defeq-embeds (`Rat.one` for an even `j_nat`,
/// `Rat.neg Rat.one` for odd).
fn cos_wide_term_as_rat(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    r: ExprId,
    r_rat: ExprId,
    j_nat: ExprId,
    dbl_nat: ExprId,
    sign_equiv: ExprId,
    sign_target: ExprId,
    sign_rat: ExprId,
) -> (ExprId, ExprId, ExprId) {
    let (aj_rat, a_proof) = a_wide_term_as_rat(d, p, r, r_rat, dbl_nat);

    let one_cc = one_c(d, p);
    let neg_one = cneg(d, p, one_cc);
    let sign_src = cpow(d, p, neg_one, j_nat);
    let exp_term_c = d.kernel().const_(p.exp_term, vec![]);
    let e_dbl = d.apply(exp_term_c, &[dbl_nat]);
    let pow_r_dbl = cpow(d, p, r, dbl_nat);
    let a_j = cmul(d, p, e_dbl, pow_r_dbl);
    let of_rat_aj = d.const_app(p.of_rat, &[aj_rat]);

    let mul_cg = d.lemma(
        p.mul_congr,
        &[sign_src, sign_target, a_j, of_rat_aj, sign_equiv, a_proof],
    );
    let t_j = cmul(d, p, sign_src, a_j);

    let of_rat_mul_eq = d.lemma(p.of_rat_mul, &[sign_rat, aj_rat]);
    let qj_rat = crate::rat_prelude::ops::rmul(d, sign_rat, aj_rat);
    let of_rat_qj = d.const_app(p.of_rat, &[qj_rat]);

    let mid = cmul(d, p, sign_target, of_rat_aj);
    let proof = echain(d, p, t_j, &[(mid, mul_cg), (of_rat_qj, of_rat_mul_eq)]);
    (t_j, qj_rat, proof)
}

/// `CReal.cosWideNonpositive : le (cosFnWide R) zero` -- pi rung 2's target,
/// `R := 8/5`. [`CRealPrelude::alternating_upper_bound_tail`] (at `a :=
/// a_wide`, `hnn := cosWideTailNonneg`, `htail := cosWideTailAntitone`,
/// `hconv := cosWideSeriesConverges`) gives `le (cosFnWide R) (sumRange t
/// 3)`; the numeric leaf `le (sumRange t 3) zero` -- `1 - 32/25 + 512/1875 =
/// -13/1875 <= 0` -- closes by `Rat.ble`'s own COMPUTATION (`Eq.refl` at
/// `Bool.true`), the same cheap technique [`pow_r2_le_3`] used, on the
/// natural (un-common-denominated) sum. [`CRealPrelude::le_trans`] composes
/// the two.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
#[allow(clippy::too_many_lines)]
pub(super) fn declare_cos_wide_nonpositive(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let rat = p.rat;
    let r = r_wide(d, p);
    let r_rat = r_wide_rat(d, p);
    let zero_c = czero(d, p);

    let a_wide = a_wide_lam(d, p, r);
    let t_lam = build_t_lam(d, p, a_wide);

    let zero_nat = d.zero();
    let one_nat = d.num(1);
    let two_nat = d.num(2);
    let three_nat = d.num(3);
    let four_nat = d.num(4);

    let one_cc = one_c(d, p);
    let neg_one = cneg(d, p, one_cc);
    let rone_val = crate::rat_prelude::ops::rone(d, rat);
    let neg_rone_val = crate::rat_prelude::ops::rneg(d, rone_val);

    // sign(0) : Equiv (pow neg_one 0) one -- `negOnePowDouble` at k := 0.
    let sign0 = d.lemma(p.neg_one_pow_double, &[zero_nat]);
    // sign(1) : Equiv (pow neg_one 1) neg_one -- defeq to `mul one neg_one`.
    let sign1 = one_mul_c(d, p, neg_one);
    // sign(2) : Equiv (pow neg_one 2) one -- `negOnePowDouble` at k := 1.
    let sign2 = d.lemma(p.neg_one_pow_double, &[one_nat]);

    let (t0, q0, p0) = cos_wide_term_as_rat(
        d, p, r, r_rat, zero_nat, zero_nat, sign0, one_cc, rone_val,
    );
    let (t1, q1, p1) = cos_wide_term_as_rat(
        d,
        p,
        r,
        r_rat,
        one_nat,
        two_nat,
        sign1,
        neg_one,
        neg_rone_val,
    );
    let (t2, q2, p2) = cos_wide_term_as_rat(
        d, p, r, r_rat, two_nat, four_nat, sign2, one_cc, rone_val,
    );

    // w := add (add (add zero_c t0) t1) t2 -- defeq to `sumRange t_lam 3`.
    let s0 = cadd(d, p, zero_c, t0);
    let s0_eq = zero_add_c(d, p, t0); // Equiv s0 t0
    let of_rat_q0 = d.const_app(p.of_rat, &[q0]);
    let s0_rat_eq = echain(d, p, s0, &[(t0, s0_eq), (of_rat_q0, p0)]);

    let s1 = cadd(d, p, s0, t1);
    let of_rat_q1 = d.const_app(p.of_rat, &[q1]);
    let add_cg1 = d.lemma(
        p.add_congr,
        &[s0, of_rat_q0, t1, of_rat_q1, s0_rat_eq, p1],
    );
    let sum01 = cadd(d, p, of_rat_q0, of_rat_q1);
    let of_rat_add1 = d.lemma(p.of_rat_add, &[q0, q1]);
    let q01 = crate::rat_prelude::ops::radd(d, q0, q1);
    let of_rat_q01 = d.const_app(p.of_rat, &[q01]);
    let s1_rat_eq = echain(d, p, s1, &[(sum01, add_cg1), (of_rat_q01, of_rat_add1)]);

    let s2 = cadd(d, p, s1, t2); // = w, defeq `sumRange t_lam 3`
    let of_rat_q2 = d.const_app(p.of_rat, &[q2]);
    let add_cg2 = d.lemma(
        p.add_congr,
        &[s1, of_rat_q01, t2, of_rat_q2, s1_rat_eq, p2],
    );
    let sum012 = cadd(d, p, of_rat_q01, of_rat_q2);
    let of_rat_add2 = d.lemma(p.of_rat_add, &[q01, q2]);
    let q_final = crate::rat_prelude::ops::radd(d, q01, q2);
    let of_rat_qfinal = d.const_app(p.of_rat, &[q_final]);
    let w_rat_eq = echain(d, p, s2, &[(sum012, add_cg2), (of_rat_qfinal, of_rat_add2)]);
    // w_rat_eq : Equiv s2 of_rat_qfinal

    // le (ofRat q_final) zero, via `Rat.ble`'s own computation.
    let rzero_val = crate::rat_prelude::ops::rzero(d, rat);
    let true_c = d.bool_true();
    let ble_val = d.const_app(rat.ble, &[q_final, rzero_val]);
    let _ = ble_val; // documents the fact being decided
    let refl_true = d.bool_refl(true_c);
    let rat_le = d.lemma(rat.le_of_ble_eq_true, &[q_final, rzero_val, refl_true]);
    let creal_le = d.lemma(p.of_rat_le, &[q_final, rzero_val, rat_le]);
    // creal_le : le (ofRat q_final) (ofRat rzero_val), rzero_val defeq zero_c

    let w_eq_symm = esymm(d, p, s2, of_rat_qfinal, w_rat_eq); // Equiv of_rat_qfinal s2
    let refl_zero = erefl(d, p, zero_c);
    let final_le = d.lemma(
        p.le_congr,
        &[
            of_rat_qfinal,
            s2,
            zero_c,
            zero_c,
            w_eq_symm,
            refl_zero,
            creal_le,
        ],
    );
    // final_le : le s2 zero_c, s2 defeq `sumRange t_lam 3`

    let hconv = d.kernel().const_(p.cos_wide_series_converges, vec![]);
    let hnn = d.kernel().const_(p.cos_wide_tail_nonneg, vec![]);
    let htail = d.kernel().const_(p.cos_wide_tail_antitone, vec![]);
    let cos_fn_wide_c = d.kernel().const_(p.cos_fn_wide, vec![]);
    let g_r = d.apply(cos_fn_wide_c, &[r]);
    let b_term = sum_at(d, p, t_lam, three_nat);

    let upper = d.lemma(
        p.alternating_upper_bound_tail,
        &[a_wide, hnn, htail, g_r, hconv],
    );
    // upper : le g_r b_term

    let value = d.lemma(p.le_trans, &[g_r, b_term, zero_c, upper, final_le]);
    let ty = cle(d, p, g_r, zero_c);
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.cos_wide_nonpositive,
        uparams: vec![],
        ty,
        value,
    })
}
