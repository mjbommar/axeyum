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
use super::trig::{cadd, cle, cmul, cneg, cpow, czero, double_neg, echain, erefl, esymm, one_c};
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
