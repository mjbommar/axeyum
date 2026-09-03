//! **Bishop completeness of `CReal`** (ADR-0512 phase R8): every regular
//! sequence of reals has a limit, constructed rather than merely asserted.
//!
//! ## The two obligations
//!
//! Given `X : Nat → CReal` satisfying [`CReal.RegularSeq`](super::CompletenessNames::regular_seq),
//! Bishop's limit is the **diagonal** `limitSeq X n := seq (X (2n+1)) (2n+1)`
//! ([`CReal.limitSeq`](super::CompletenessNames::limit_seq)) — the shift `2n+1`
//! matches [`CReal.add`](super::CRealPrelude::add)'s own, and for the same
//! reason: it is the sampling rate at which
//! [`Rat.natDivSucc_halve`](crate::RatPrelude::nat_div_succ_halve) turns two
//! half-size errors into one full-size one. Two things then need proving:
//!
//! 1. the diagonal is itself `Regular`, so `CReal.mk` accepts it
//!    ([`CReal.limitSeq_regular`](super::CompletenessNames::limit_seq_regular)),
//!    packaged as [`CReal.limit`](super::CompletenessNames::limit);
//! 2. `X n` converges to it, at a rate this module can actually prove
//!    ([`CReal.limit_dist`](super::CompletenessNames::limit_dist)).
//!
//! ## Why `RegularSeq` is stated at the diagonal, not at an arbitrary index
//!
//! The textbook condition compares `X m` and `X n` as reals via an arbitrary
//! shared representative index — `CReal.le`/`CReal.add`-shaped, the way
//! [`CReal.le`](super::CRealPrelude::le) itself is stated. Unfolding that
//! **at all** first has to cross `CReal.add`'s own index shift, on top of
//! whichever shift the caller chose — the same complication
//! `density.rs`'s module doc measures and avoids for a different pair of
//! operations ("routes the difference through `CReal.add`... That shift buys
//! nothing here"). [`CReal.RegularSeq`](super::CompletenessNames::regular_seq)
//! instead compares the sample **each real already offers at its own
//! index** — `seq (X m) m` — which is exactly the quantity
//! [`super::density::declare_rat_approx_upper`] already proves is within
//! `1/(m+1)` of the real `X m` itself, so bounding it is equivalent up to a
//! constant factor to bounding `X m` and `X n` as reals, and it costs no
//! `CReal.add` anywhere in this module.
//!
//! ## Both proofs are index-shift arithmetic, not Archimedean closing
//!
//! `Equiv.trans`/`le_trans` need an arbitrary third index and
//! [`Rat.le_of_le_add_natDivSucc`](crate::RatPrelude::le_of_le_add_nat_div_succ)
//! because their two hypotheses are stated at indices unrelated to the goal's
//! own. Here every comparison the hypotheses supply is already at a *fixed*
//! index tied to the goal (`shift m`/`shift n` for regularity, `n`/`shift k`
//! for convergence), so both proofs close with [`super::weaken`] against a
//! plain rational inequality — no third index, no Archimedean lemma.

#![allow(
    clippy::doc_markdown,
    clippy::many_single_char_names,
    clippy::similar_names,
    clippy::too_many_arguments
)]

use super::{
    CRealPrelude, DERIVED_HEIGHT, creal_ty, div_succ, halves, modulus, sample, shift, weaken,
    within,
};
use crate::Kernel;
use crate::KernelError;
use crate::env::{Declaration, ReducibilityHint};
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::name::NameId;
use crate::nat_prelude::NatOps;
use crate::rat_prelude::group::rsub;
use crate::rat_prelude::ops::{radd, rat_eq_rewrite, rat_ty, rchain, rcongr, rle, rsymm, rzero};

/// Admit `CReal.RegularSeq`, `CReal.limitSeq`, `CReal.limitSeq_regular`,
/// `CReal.limit` and `CReal.limit_dist`.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` from a `Theorem` here means
/// the kernel **refused** a proof, not that a script gave up.
pub(super) fn declare_completeness(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    declare_regular_seq(d, p)?;
    declare_limit_seq(d, p)?;
    declare_limit_seq_regular(d, p)?;
    declare_limit(d, p)?;
    declare_limit_dist(d, p)
}

/// `Nat → CReal`.
fn seq_of_creal_ty(d: &mut IntDev<'_>, p: CRealPrelude) -> ExprId {
    let nat = d.nat_ty();
    let carrier = creal_ty(d, p);
    d.arrow(nat, carrier)
}

/// `Rat.le (Rat.natDivSucc 1 (shift m)) (Rat.natDivSucc 1 m)` —
/// `1/(2m+2) ≤ 1/(m+1)`, the one inequality both obligations widen through.
///
/// Built exactly as [`super::shifted_bound_le`]'s own first step: pad the
/// left side with a nonnegative zero, fuse it into a doubled fraction, then
/// read the doubled fraction back at the un-shifted denominator via
/// `Rat.natDivSucc_halve`.
///
/// `pub(super)`, not private: [`super::convergence`]'s algebra-of-limits
/// theorems need exactly this inequality to bridge a single real's own sample
/// at `n` against its sample at `shift n` — the blocker the previous slice
/// reported in that module's header. `completeness` and `convergence` are
/// *siblings*, both children of `creal`, so `pub(super)` here (visible in
/// `creal` and all of `creal`'s descendants) is the narrowest modifier that
/// reaches across, and it is reused rather than re-derived.
pub(super) fn half_shift_le(d: &mut IntDev<'_>, p: CRealPrelude, m: ExprId) -> ExprId {
    let rat = p.rat;
    let sm = shift(d, m);
    let one_sm = div_succ(d, p, 1, sm);
    let one_m = div_succ(d, p, 1, m);
    let one_nat = d.num(1);
    let zero = rzero(d, rat);

    let refl = d.lemma(rat.le_refl, &[one_sm]);
    let nonneg = d.lemma(rat.zero_le_nat_div_succ, &[one_nat, sm]);
    let step = d.lemma(
        rat.add_le_add,
        &[one_sm, one_sm, zero, one_sm, refl, nonneg],
    );
    let padded = radd(d, one_sm, zero);
    let summed = radd(d, one_sm, one_sm);
    let trim = d.lemma(rat.add_zero, &[one_sm]);
    let step2 = rat_eq_rewrite(d, padded, one_sm, trim, step, &|d, t| {
        rle(d, rat, t, summed)
    });

    let two_sm = div_succ(d, p, 2, sm);
    let fuse = d.lemma(rat.nat_div_succ_add, &[one_nat, one_nat, sm]);
    let step3 = rat_eq_rewrite(d, summed, two_sm, fuse, step2, &|d, t| {
        rle(d, rat, one_sm, t)
    });

    let halve = d.lemma(rat.nat_div_succ_halve, &[m]);
    rat_eq_rewrite(d, two_sm, one_m, halve, step3, &|d, t| {
        rle(d, rat, one_sm, t)
    })
}

/// `Rat.le (modulus (shift m) (shift n)) (modulus m n)` — the two halves of
/// [`half_shift_le`] combined additively.
///
/// ADR-1592 retirement: was one direct `d.lemma(rat.add_le_add, &[a, b, c,
/// e, hm, hn])` citation; now routed through `linarith::generic::prove_s`
/// over `AlgS.Rat.orderedRingS` (`super::linarith_bridge::rat_add_le_add`)
/// — the SAME fact, the SAME type, reached generically.
fn moduli_shift_le(d: &mut IntDev<'_>, p: CRealPrelude, m: ExprId, n: ExprId) -> ExprId {
    let sm = shift(d, m);
    let sn = shift(d, n);
    let a = div_succ(d, p, 1, sm);
    let b = div_succ(d, p, 1, m);
    let c = div_succ(d, p, 1, sn);
    let e = div_succ(d, p, 1, n);
    let hm = half_shift_le(d, p, m);
    let hn = half_shift_le(d, p, n);
    super::linarith_bridge::rat_add_le_add(d, p, a, b, c, e, hm, hn)
}

/// `Eq Rat ((1/(k+1)+1/(n+1)) + (1/(n+1)+1/(k'+1))) (2/(k+1)+2/(n+1))`, given
/// `k' := shift k` is read as `1/(k+1)` **before** this call (i.e. the caller
/// already widened `1/(shift k + 1)` up to `1/(k+1)`) — this is the pure
/// rearrangement `(a+b)+(b+a) = 2a+2b`.
///
/// Returns `(target, proof)` with `proof : Eq Rat start target`, `start :=
/// (a+b)+(b+a)`.
fn regroup_and_double(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    k: ExprId,
    n: ExprId,
) -> (ExprId, ExprId) {
    let rat = p.rat;
    let one_nat = d.num(1);
    let a = div_succ(d, p, 1, k);
    let b = div_succ(d, p, 1, n);
    let two_a = div_succ(d, p, 2, k);
    let two_b = div_succ(d, p, 2, n);

    let l = radd(d, a, b);
    let r = radd(d, b, a);
    let start = radd(d, l, r);

    // (a+b)+r = a+(b+r)
    let assoc1 = d.lemma(rat.add_assoc, &[a, b, r]);
    let br = radd(d, b, r);
    let mid1 = radd(d, a, br);

    // b+(b+a) = (b+b)+a
    let bb = radd(d, b, b);
    let bb_plus_a = radd(d, bb, a);
    let assoc_b = d.lemma(rat.add_assoc, &[b, b, a]);
    let flip_b = rsymm(d, bb_plus_a, br, assoc_b);
    let step2 = rcongr(d, br, bb_plus_a, flip_b, &|d, t| radd(d, a, t));
    let mid2 = radd(d, a, bb_plus_a);

    // (b+b) = 2/(n+1)
    let fuse_b = d.lemma(rat.nat_div_succ_add, &[one_nat, one_nat, n]);
    let inner_cong = rcongr(d, bb, two_b, fuse_b, &|d, t| radd(d, t, a));
    let two_b_plus_a = radd(d, two_b, a);
    let step3 = rcongr(d, bb_plus_a, two_b_plus_a, inner_cong, &|d, t| {
        radd(d, a, t)
    });
    let mid3 = radd(d, a, two_b_plus_a);

    // 2/(n+1) + a = a + 2/(n+1)
    let comm4 = d.lemma(rat.add_comm, &[two_b, a]);
    let a_plus_two_b = radd(d, a, two_b);
    let step4 = rcongr(d, two_b_plus_a, a_plus_two_b, comm4, &|d, t| radd(d, a, t));
    let mid4 = radd(d, a, a_plus_two_b);

    // a+(a+2/(n+1)) = (a+a)+2/(n+1)
    let aa = radd(d, a, a);
    let aa_plus_two_b = radd(d, aa, two_b);
    let assoc_a = d.lemma(rat.add_assoc, &[a, a, two_b]);
    let step5 = rsymm(d, aa_plus_two_b, mid4, assoc_a);
    let mid5 = aa_plus_two_b;

    // (a+a) = 2/(k+1)
    let fuse_a = d.lemma(rat.nat_div_succ_add, &[one_nat, one_nat, k]);
    let step6 = rcongr(d, aa, two_a, fuse_a, &|d, t| radd(d, t, two_b));
    let target = radd(d, two_a, two_b);

    let (_, proof) = rchain(
        d,
        start,
        &[
            (mid1, assoc1),
            (mid2, step2),
            (mid3, step3),
            (mid4, step4),
            (mid5, step5),
            (target, step6),
        ],
    );
    (target, proof)
}

/// `Rat.le ((modulus k n) + (modulus n (shift k))) (2/(k+1) + 2/(n+1))` — the
/// bound [`declare_limit_dist`] widens through.
fn convergence_bound_le(d: &mut IntDev<'_>, p: CRealPrelude, k: ExprId, n: ExprId) -> ExprId {
    let rat = p.rat;
    let sk = shift(d, k);
    let one_k = div_succ(d, p, 1, k);
    let one_n = div_succ(d, p, 1, n);
    let one_sk = div_succ(d, p, 1, sk);

    let b1 = modulus(d, p, k, n);
    let b2 = modulus(d, p, n, sk);

    let hk = half_shift_le(d, p, k);
    let refl_n = d.lemma(rat.le_refl, &[one_n]);
    let step_inner = d.lemma(rat.add_le_add, &[one_n, one_n, one_sk, one_k, refl_n, hk]);

    let refl_b1 = d.lemma(rat.le_refl, &[b1]);
    let one_n_plus_one_k = radd(d, one_n, one_k);
    let step_outer = d.lemma(
        rat.add_le_add,
        &[b1, b1, b2, one_n_plus_one_k, refl_b1, step_inner],
    );

    let (target, eq_regroup) = regroup_and_double(d, p, k, n);
    let start = radd(d, b1, one_n_plus_one_k);
    let b12 = radd(d, b1, b2);
    rat_eq_rewrite(d, start, target, eq_regroup, step_outer, &|d, t| {
        rle(d, rat, b12, t)
    })
}

/// `CReal.RegularSeq X := ∀ m n, Within (seq (X m) m − seq (X n) n) (modulus m n)`.
fn declare_regular_seq(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let rat = p.rat;
    let nat = d.nat_ty();
    let prop = d.kernel().sort_zero();
    let seq_ty = seq_of_creal_ty(d, p);

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let xm = d.apply(x, &[m]);
    let xn = d.apply(x, &[n]);
    let left = sample(d, p, xm, m);
    let right = sample(d, p, xn, n);
    let difference = rsub(d, rat, left, right);
    let bound = modulus(d, p, m, n);
    let claim = within(d, p, difference, bound);

    let body = {
        let over_n = d.pi_fv(n_fv, nat, claim);
        d.pi_fv(m_fv, nat, over_n)
    };
    let value = d.lam_fv(x_fv, seq_ty, body);
    let ty = d.arrow(seq_ty, prop);
    d.kernel().add_declaration(Declaration::Definition {
        name: p.completeness.regular_seq,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(DERIVED_HEIGHT + 30),
    })
}

/// `CReal.limitSeq X n := seq (X (shift n)) (shift n)`.
fn declare_limit_seq(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let rat_carrier = rat_ty(d);
    let seq_ty = seq_of_creal_ty(d, p);

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let sn = shift(d, n);
    let xsn = d.apply(x, &[sn]);
    let value_body = sample(d, p, xsn, sn);

    let value = {
        let inner = d.lam_fv(n_fv, nat, value_body);
        d.lam_fv(x_fv, seq_ty, inner)
    };
    let ty = {
        let over_n = d.arrow(nat, rat_carrier);
        d.arrow(seq_ty, over_n)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.completeness.limit_seq,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(DERIVED_HEIGHT + 31),
    })
}

/// `CReal.limitSeq_regular : ∀ X, RegularSeq X → Regular (limitSeq X)`.
fn declare_limit_seq_regular(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let seq_ty = seq_of_creal_ty(d, p);

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let h_ty = d.const_app(p.completeness.regular_seq, &[x]);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let sm = shift(d, m);
    let sn = shift(d, n);
    let inst = d.apply(h, &[sm, sn]);

    let xsm = d.apply(x, &[sm]);
    let xsn = d.apply(x, &[sn]);
    let left = sample(d, p, xsm, sm);
    let right = sample(d, p, xsn, sn);
    let difference = rsub(d, p.rat, left, right);
    let bound_sm_sn = modulus(d, p, sm, sn);
    let bound_m_n = modulus(d, p, m, n);
    let order = moduli_shift_le(d, p, m, n);
    let widened = weaken(d, p, difference, bound_sm_sn, bound_m_n, inst, order);

    let value = {
        let over_n = d.lam_fv(n_fv, nat, widened);
        let over_m = d.lam_fv(m_fv, nat, over_n);
        let with_h = d.lam_fv(h_fv, h_ty, over_m);
        d.lam_fv(x_fv, seq_ty, with_h)
    };
    let ty = {
        let limit_seq_x = d.const_app(p.completeness.limit_seq, &[x]);
        let regular_claim = d.const_app(p.regular_pred, &[limit_seq_x]);
        let after_h = d.arrow(h_ty, regular_claim);
        d.pi_fv(x_fv, seq_ty, after_h)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.completeness.limit_seq_regular,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CReal.limit X h := CReal.mk (limitSeq X) (limitSeq_regular X h)`.
fn declare_limit(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let seq_ty = seq_of_creal_ty(d, p);
    let result = creal_ty(d, p);

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let h_ty = d.const_app(p.completeness.regular_seq, &[x]);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let limit_seq_x = d.const_app(p.completeness.limit_seq, &[x]);
    let regularity_proof = d.lemma(p.completeness.limit_seq_regular, &[x, h]);
    let constructor = d.kernel().const_(p.mk, vec![]);
    let body = d.apply(constructor, &[limit_seq_x, regularity_proof]);

    let value = {
        let with_h = d.lam_fv(h_fv, h_ty, body);
        d.lam_fv(x_fv, seq_ty, with_h)
    };
    let ty = {
        let after_h = d.arrow(h_ty, result);
        d.pi_fv(x_fv, seq_ty, after_h)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.completeness.limit,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(DERIVED_HEIGHT + 32),
    })
}

/// `CReal.limit_dist : ∀ X (h : RegularSeq X) n k, Within (seq (X n) k − seq
/// (limit X h) k) (2/(k+1) + 2/(n+1))`.
fn declare_limit_dist(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let rat = p.rat;
    let nat = d.nat_ty();
    let seq_ty = seq_of_creal_ty(d, p);

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let h_ty = d.const_app(p.completeness.regular_seq, &[x]);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);

    let xn = d.apply(x, &[n]);
    let sk = shift(d, k);
    let xsk = d.apply(x, &[sk]);

    let seq_xn_k = sample(d, p, xn, k);
    let seq_xn_n = sample(d, p, xn, n);
    let seq_xsk_sk = sample(d, p, xsk, sk);

    let u1 = rsub(d, rat, seq_xn_k, seq_xn_n);
    let b1 = modulus(d, p, k, n);
    let w1 = d.lemma(p.regular, &[xn, k, n]);

    let u2 = rsub(d, rat, seq_xn_n, seq_xsk_sk);
    let b2 = modulus(d, p, n, sk);
    let w2 = d.apply(h, &[n, sk]);

    let (l1, r1) = halves(d, p, u1, b1, w1);
    let (l2, r2) = halves(d, p, u2, b2, w2);
    let combined = d.lemma(rat.bounds_add, &[u1, b1, u2, b2, l1, r1, l2, r2]);

    let target_diff = rsub(d, rat, seq_xn_k, seq_xsk_sk);
    let quantity_eq = d.lemma(rat.sub_add_sub, &[seq_xn_k, seq_xn_n, seq_xsk_sk]);
    let u12 = radd(d, u1, u2);
    let b12 = radd(d, b1, b2);
    let at_quantity = rat_eq_rewrite(d, u12, target_diff, quantity_eq, combined, &|d, t| {
        within(d, p, t, b12)
    });

    let order = convergence_bound_le(d, p, k, n);
    let two_k = div_succ(d, p, 2, k);
    let two_n = div_succ(d, p, 2, n);
    let target_bound = radd(d, two_k, two_n);
    let result = weaken(d, p, target_diff, b12, target_bound, at_quantity, order);

    let value = {
        let over_k = d.lam_fv(k_fv, nat, result);
        let over_n = d.lam_fv(n_fv, nat, over_k);
        let with_h = d.lam_fv(h_fv, h_ty, over_n);
        d.lam_fv(x_fv, seq_ty, with_h)
    };
    let ty = {
        let limit_x_h = d.const_app(p.completeness.limit, &[x, h]);
        let seq_limit_k = sample(d, p, limit_x_h, k);
        let diff_ty = rsub(d, rat, seq_xn_k, seq_limit_k);
        let two_k_ty = div_succ(d, p, 2, k);
        let two_n_ty = div_succ(d, p, 2, n);
        let bound_ty = radd(d, two_k_ty, two_n_ty);
        let claim = within(d, p, diff_ty, bound_ty);
        let over_k = d.pi_fv(k_fv, nat, claim);
        let over_n = d.pi_fv(n_fv, nat, over_k);
        let after_h = d.pi_fv(h_fv, h_ty, over_n);
        d.pi_fv(x_fv, seq_ty, after_h)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.completeness.limit_dist,
        uparams: vec![],
        ty,
        value,
    })
}

/// The kernel names `creal/completeness.rs` declares.
///
/// One of ADR-1512's per-module registries behind the [`CRealPrelude`]
/// facade: the field, its documentation and its interning all live
/// beside the `declare_*` that uses them, so a declaration added here
/// does not touch `creal.rs` at all.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CompletenessNames {
    /// `CReal.RegularSeq : (Nat → CReal) → Prop` —
    /// `RegularSeq X := ∀ m n, Within (seq (X m) m − seq (X n) n) (1/(m+1)+1/(n+1))`.
    ///
    /// **The canonical-sample formulation, not the arbitrary-index one.** The
    /// textbook statement compares `X m` and `X n` as reals at an arbitrary
    /// shared representative index (`CReal.le`/`CReal.add`-shaped, the way
    /// [`super::CRealPrelude::le`] itself is stated), which routes every consumer through
    /// `CReal.add`'s index shift before it can be unfolded at all. This
    /// definition instead compares the sample **each real already offers at
    /// its own index** — `seq (X m) m`, exactly the quantity
    /// [`super::CRealPrelude::rat_approx_upper`]/[`super::CRealPrelude::rat_approx_lower`] already prove is
    /// within `1/(m+1)` of the real `X m` — so it is equivalent up to a
    /// constant factor to the textbook condition, never mentions `CReal.add`,
    /// and is what [`super::CompletenessNames::limit`] below is built from directly.
    pub regular_seq: NameId,
    /// `CReal.limitSeq : (Nat → CReal) → Nat → Rat` —
    /// `limitSeq X n := seq (X (2n+1)) (2n+1)`.
    ///
    /// The **diagonal**, sampled at Bishop's shift `2n+1` rather than at `n`
    /// itself: [`super::CompletenessNames::limit_seq_regular`]'s estimate needs the two halves of
    /// each pairwise bound to fuse via
    /// [`Rat.natDivSucc_halve`](crate::RatPrelude::nat_div_succ_halve) into
    /// exactly `1/(n+1)`, which only happens at this shift — sampling at `n`
    /// leaves a bound twice the size [`super::CRealPrelude::regular_pred`] asks for, with no
    /// rearrangement able to close the gap.
    pub limit_seq: NameId,
    /// `CReal.limitSeq_regular : ∀ X, RegularSeq X → Regular (limitSeq X)`.
    ///
    /// **Obligation 1: the diagonal is a `CReal` at all.** The proof needs no
    /// arbitrary third index and no Archimedean closing step — unlike
    /// `Equiv.trans`/`le_trans` — because [`super::CompletenessNames::regular_seq`]'s hypothesis
    /// is already stated at the two *fixed* diagonal indices `shift m` and
    /// `shift n`; from there it is one instantiation of `RegularSeq` plus
    /// `weaken` against the rational fact `modulus (shift m) (shift n) ≤
    /// modulus m n`.
    pub limit_seq_regular: NameId,
    /// `CReal.limit : (X : Nat → CReal) → RegularSeq X → CReal := fun X h =>
    /// CReal.mk (limitSeq X) (limitSeq_regular X h)`.
    ///
    /// **Bishop completeness, the construction half.** Every `RegularSeq`
    /// sequence of reals has a limit, produced rather than merely asserted to
    /// exist.
    pub limit: NameId,
    /// `CReal.limit_dist : ∀ X (h : RegularSeq X) n k, Within (seq (X n) k −
    /// seq (limit X h) k) (2/(k+1) + 2/(n+1))`.
    ///
    /// **Bishop completeness, the convergence half**, at the rate `X`'s own
    /// regularity carries (`O(1/n)`, uniformly in the sampling index `k`) —
    /// not merely `∀ n, Equiv (X n) (limit ...)`, which is false in general
    /// (a converging sequence is generally not equal to its limit at any
    /// finite `n`). The estimate chains `X n`'s own regularity between `(k,
    /// n)` with one [`super::CompletenessNames::regular_seq`] instance at `(n, shift k)`, folds
    /// the two `seq (X n) n` occurrences via `Rat.sub_add_sub`, and widens
    /// `1/(shift k + 1)` up to `1/(k+1)` — no arbitrary third index or
    /// Archimedean lemma needed, for the same reason as
    /// [`super::CompletenessNames::limit_seq_regular`].
    pub limit_dist: NameId,
}

impl CompletenessNames {
    /// Interns this module's names under the `CReal` root.
    ///
    /// Split out of `creal.rs`'s `intern_names` by ADR-1512: the kernel
    /// spelling of each name sits in the file that declares it.
    pub(super) fn intern(kernel: &mut Kernel, creal: NameId) -> Self {
        Self {
            regular_seq: kernel.name_str(creal, "RegularSeq"),
            limit_seq: kernel.name_str(creal, "limitSeq"),
            limit_seq_regular: kernel.name_str(creal, "limitSeq_regular"),
            limit: kernel.name_str(creal, "limit"),
            limit_dist: kernel.name_str(creal, "limit_dist"),
        }
    }
}
