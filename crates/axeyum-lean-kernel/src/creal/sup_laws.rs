//! The characterization laws for [`CReal.supOn`](super::CRealPrelude::sup_on):
//! the laws that turn a value with a convergence law into a *supremum*.
//!
//! `creal/supremum.rs` lands `CReal.supOn` and
//! `CReal.supSeq_converges_supOn`, and its own closing section says exactly
//! what that does NOT give:
//!
//! > `supOn` is a VALUE with a `Converges` law, and that is all. It is not yet
//! > characterized as a supremum.
//!
//! This file closes that gap. Two laws, and the asymmetry between them is the
//! whole mathematical content:
//!
//! 1. **`CReal.supOn_approx_lub`** — the APPROXIMATE least-upper-bound law:
//!    for every accuracy index `e` there is a point `x ∈ [a, b]` with
//!    `supOn F a b hab u ≤ F x + 1/(e+1)`. It must stay approximate.
//!    [`CRealPrelude::evt_attained_max_decides_sign`](super::CRealPrelude::evt_attained_max_decides_sign)
//!    (`creal/extreme_value.rs`) proves that an ATTAINING maximiser — the
//!    exact form, `∃ x, F x = supOn` — would decide the sign of an arbitrary
//!    real. That is EVT's row 2, a genuine impossibility result rather than an
//!    unfinished proof, and this statement is its constructive substitute.
//! 2. **`CReal.supOn_ub`** — the upper-bound law, `∀ x ∈ [a, b],
//!    F x ≤ supOn F a b hab u`. See the handoff section at the end of this
//!    documentation for its status.
//!
//! ## The value/argmax distinction is preserved
//!
//! Nothing here produces an argmax, and nothing here may. `supOn_approx_lub`
//! exhibits a point at which `F` comes WITHIN `1/(e+1)` of the supremum; the
//! point it exhibits is a MESH POINT of the level the schedule already picked,
//! and it moves as `e` moves. There is no limit of those points in this
//! development and there cannot be one — extracting it is exactly what
//! `evt_attained_max_decides_sign` refutes. See `creal/supremum.rs`'s own
//! value/argmax section before adding anything to this file.
//!
//! ## Why the least-upper-bound half is the CHEAP half, which is not obvious
//!
//! The natural expectation is that "supOn bounds F above" is easy and
//! "F approaches supOn" is hard, because the second sounds like attainment.
//! It is the other way round, and the reason is worth recording because it
//! decided this lane's order of work:
//!
//! - The approximate LUB law needs a point at which the FINITE mesh maximum is
//!   nearly attained. A finite max over `n+1` samples is nearly attained at one
//!   of them, and "nearly" is exactly what makes it constructive: deciding
//!   WHICH sample attains it would need a decidable comparison of reals, but
//!   deciding which one attains it *to within `eps`* needs only
//!   [`CRealPrelude::lt_cotrans`](super::CRealPrelude::lt_cotrans). That is
//!   [`declare_max_range_attained_approx_thm`], an induction over the fold's
//!   own bound. **No mesh geometry enters at all** — the mesh points arrive
//!   pre-packaged in `[a, b]` from
//!   [`CRealPrelude::riemann_sample_in_bounds`](super::CRealPrelude::riemann_sample_in_bounds).
//! - The upper-bound law needs the opposite: an ARBITRARY `x ∈ [a, b]` placed
//!   within one cell of SOME mesh point, so that uniform continuity can carry
//!   `F x` to a sampled value. `x` is not a mesh point and no computed index
//!   locates it, so that is a genuine cell-location argument (`lt_cotrans`
//!   again, but over the interval rather than over the fold), plus the
//!   modulus/`mesh_le_of_ge` step, plus a limit passage. Strictly more work.
//!
//! ## The one non-obvious step in the assembly
//!
//! `converges_upper_bound` needs `∀ n, le (supSeq F a b u n) bnd` — a bound at
//! EVERY index, not just at the one index whose mesh supplied the witness
//! point. [`declare_sup_seq_le_shift_thm`] supplies it: every term of the sup
//! sequence, coarser or finer, is within `1/2^k` of the term at `k`, by
//! `Nat.le_total` over the two already-proved halves
//! ([`CRealPrelude::sup_seq_mono`](super::CRealPrelude::sup_seq_mono) below
//! `k`, [`CRealPrelude::sup_seq_le_add`](super::CRealPrelude::sup_seq_le_add)
//! above it). Without it the argument would have to re-run the Cauchy estimate
//! by hand at the chosen index.
//!
//! The accuracy bookkeeping is then one halving. The witness is taken at
//! `e2 := 2·e + 1`, so the fold's own slack is `1/(2e+2)`; the sequence shift
//! at the same index is `1/(2^e2)`, weakened to `1/(2e+2)` through
//! [`CRealPrelude::le_mesh_level_count`](super::CRealPrelude::le_mesh_level_count)
//! and `Rat.natDivSucc_antitone`; and the two halves fuse to `1/(e+1)` by
//! `Rat.natDivSucc_add` followed by `Rat.natDivSucc_halve`, whose index shape
//! `succ (2·m)` is why `e2` is built that way and not as `succ (add e e)`.

#![allow(clippy::doc_markdown, clippy::too_many_arguments)]

use super::ring_helpers::right_distrib;
use super::{CRealPrelude, and_intro, cadd, cle, creal_ty, embed};
use crate::KernelError;
use crate::env::Declaration;
use crate::expr::ExprId;
use crate::int_prelude::ops::{IntDev, exists_elim};
use crate::nat_prelude::NatOps;
use crate::rat_prelude::ops::{nat_rewrite_prop, radd, rat_eq_rewrite, rtrans, rzero};

/// `CReal.mul x y`.
fn cmul(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId, y: ExprId) -> ExprId {
    d.const_app(p.mul, &[x, y])
}

/// `CReal.neg x`.
fn cneg(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId) -> ExprId {
    d.const_app(p.neg, &[x])
}

/// `CReal.Equiv x y`.
fn cequiv(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId, y: ExprId) -> ExprId {
    d.const_app(p.equiv, &[x, y])
}

/// `(b + (neg a)) · (1/(m+1))` — the mesh width `Δ`, re-derived here rather
/// than imported from `creal/supremum.rs`'s private copy, per this
/// development's convention (that copy is itself a re-derivation of
/// `integral.rs`'s `delta_of`).
fn mesh_delta(d: &mut IntDev<'_>, p: CRealPrelude, a: ExprId, b: ExprId, m: ExprId) -> ExprId {
    let na = cneg(d, p, a);
    let width = cadd(d, p, b, na);
    let one_nat = d.num(1);
    let frac = d.const_app(p.rat.nat_div_succ, &[one_nat, m]);
    let frac_real = embed(d, p, frac);
    cmul(d, p, width, frac_real)
}

/// `add a (mul (ofNat i) delta)` — the `i`-th left sample point `a + i·Δ`.
fn mesh_sample_point(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    a: ExprId,
    delta: ExprId,
    i: ExprId,
) -> ExprId {
    let oi = d.const_app(p.of_nat, &[i]);
    let shift = cmul(d, p, oi, delta);
    cadd(d, p, a, shift)
}

/// `CReal.ofRat (Rat.natDivSucc 1 e)` — the accuracy `1/(e+1)` as a real.
fn unit_frac_real(d: &mut IntDev<'_>, p: CRealPrelude, e: ExprId) -> (ExprId, ExprId) {
    let one_nat = d.num(1);
    let frac = d.const_app(p.rat.nat_div_succ, &[one_nat, e]);
    let real = embed(d, p, frac);
    (frac, real)
}

// ---------------------------------------------------------------------------
// `CReal.maxRange_attained_approx`
// ---------------------------------------------------------------------------

/// `CReal.maxRange_attained_approx : ∀ (f : Nat → CReal) (n e : Nat),
/// ∃ i, Nat.le i n ∧ le (maxRange f n) (add (f i) (ofRat (Rat.natDivSucc 1 e)))`
/// — **a finite maximum is APPROXIMATELY attained at one of its samples.**
///
/// The exact form (`∃ i ≤ n, maxRange f n = f i`) is not available and must
/// not be attempted: choosing which sample attains the maximum decides
/// `le x y ∨ le y x` for arbitrary reals. The `1/(e+1)` slack is precisely
/// what buys the decision back, through
/// [`CRealPrelude::lt_cotrans`](super::CRealPrelude::lt_cotrans) — for any
/// `eps > 0` and any pair `u`, `v`, either `v < u` or `u < v + eps`, and both
/// branches close.
///
/// Induction on the fold's own bound `n`, with `e` (and hence `eps`) held
/// FIXED outside the motive. Fixing it is what keeps the proof short: the
/// obvious design quantifies `e` inside the motive and applies the inductive
/// hypothesis at a halved accuracy, because the slack looks like it must
/// accumulate over the `n` steps. It does not. At each step the cotransitive
/// split either keeps the inductive hypothesis's own witness UNCHANGED (the
/// new sample loses, so the old estimate is reused verbatim) or discards it
/// entirely for the new index (the new sample wins, and the estimate is
/// `le_of_lt` on the split's own gap). Neither branch adds an epsilon to the
/// other's, so one fixed `eps` carries the whole induction.
///
/// - `n = 0`: `maxRange f 0` is definitionally `f 0`, so the witness is `0`
///   and the estimate is [`CRealPrelude::le_add_of_nonneg`](super::CRealPrelude::le_add_of_nonneg).
/// - `n = j+1`: `maxRange f (succ j)` is definitionally
///   `max (maxRange f j) (f (succ j))`, so
///   [`CRealPrelude::max_le`](super::CRealPrelude::max_le) reduces the goal to
///   two `le`s against one right-hand side, and the split decides which of the
///   two witnesses that right-hand side is built from.
fn declare_max_range_attained_approx_thm(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = creal_ty(d, p);
    let fn_ty = d.arrow(nat, carrier);
    let nat_p = p.rat.int.nat;
    let logic = p.rat.int.logic;
    let one_level = d.level_one();

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let e_fv = d.fresh_fvar();
    let e = d.kernel().fvar(e_fv);

    let (frac, eps) = unit_frac_real(d, p, e);
    let one_nat = d.num(1);
    let frac_nonneg = d.lemma(p.rat.zero_le_nat_div_succ, &[one_nat, e]);
    // `lt zero eps`: `PosBound eps e` is `le eps eps`, so reflexivity is the
    // whole witness. This is the only place strict positivity is needed, and
    // it is what `lt_cotrans` consumes.
    let eps_pos = {
        let refl = d.lemma(p.le_refl, &[eps]);
        d.lemma(p.pos_of_pos_bound, &[eps, e, refl])
    };

    // `fun i => And (Nat.le i k) (le (maxRange f k) (add (f i) eps))`.
    let pred = |d: &mut IntDev<'_>, k: ExprId| -> ExprId {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let bound = d.le(i, k);
        let fi = d.apply(f, &[i]);
        let padded = cadd(d, p, fi, eps);
        let mrk = d.const_app(p.max_range, &[f, k]);
        let est = cle(d, p, mrk, padded);
        let body = d.and(bound, est);
        d.lam_fv(i_fv, nat, body)
    };
    let motive = |d: &mut IntDev<'_>, k: ExprId| -> ExprId {
        let pr = pred(d, k);
        let ex = d.kernel().const_(logic.exists_, vec![one_level]);
        d.apply(ex, &[nat, pr])
    };
    let intro = |d: &mut IntDev<'_>, k: ExprId, witness: ExprId, proof: ExprId| -> ExprId {
        let pr = pred(d, k);
        let ctor = d.kernel().const_(logic.exists_intro, vec![one_level]);
        d.apply(ctor, &[nat, pr, witness, proof])
    };

    let base = |d: &mut IntDev<'_>| -> ExprId {
        let zero_n = d.zero();
        let f0 = d.apply(f, &[zero_n]);
        let bound_ty = d.le(zero_n, zero_n);
        let hb = d.lemma(nat_p.le_refl, &[zero_n]);
        let mr0 = d.const_app(p.max_range, &[f, zero_n]);
        let padded = cadd(d, p, f0, eps);
        let est_ty = cle(d, p, mr0, padded);
        // `le (f 0) (add (f 0) eps)`; `maxRange f 0` reduces to `f 0`.
        let est = d.lemma(p.le_add_of_nonneg, &[f0, frac, frac_nonneg]);
        let whole = and_intro(d, p, bound_ty, est_ty, hb, est);
        intro(d, zero_n, zero_n, whole)
    };

    let step = |d: &mut IntDev<'_>, j: ExprId, ih: ExprId| -> ExprId {
        let sj = d.succ(j);
        let mrj = d.const_app(p.max_range, &[f, j]);
        let fsj = d.apply(f, &[sj]);
        let target = motive(d, sj);
        let pr_j = pred(d, j);

        // `lt (f (succ j)) (add (f (succ j)) eps)`, the cotransitive gap.
        let head_lt = {
            let zero_c = d.kernel().const_(p.zero, vec![]);
            let refl = d.lemma(p.le_refl, &[fsj]);
            let raw = d.lemma(
                p.add_lt_add_of_le_of_lt,
                &[fsj, fsj, zero_c, eps, refl, eps_pos],
            );
            let padded_zero = cadd(d, p, fsj, zero_c);
            let padded_eps = cadd(d, p, fsj, eps);
            let trim = d.lemma(p.add_zero, &[fsj]);
            let refl_rhs = d.lemma(p.equiv_refl, &[padded_eps]);
            d.lemma(
                p.lt_congr,
                &[
                    padded_zero,
                    fsj,
                    padded_eps,
                    padded_eps,
                    trim,
                    refl_rhs,
                    raw,
                ],
            )
        };
        let head_padded = cadd(d, p, fsj, eps);
        let head_le = d.lemma(p.le_of_lt, &[fsj, head_padded, head_lt]);

        let minor = {
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let hp_fv = d.fresh_fvar();
            let hp = d.kernel().fvar(hp_fv);
            let bound_ty = d.le(i, j);
            let fi = d.apply(f, &[i]);
            let padded_i = cadd(d, p, fi, eps);
            let est_ty = cle(d, p, mrj, padded_i);
            let hp_ty = d.and(bound_ty, est_ty);
            let hb = d.and_left(bound_ty, est_ty, hp);
            let hle = d.and_right(bound_ty, est_ty, hp);

            // `Or (lt (f (succ j)) (maxRange f j)) (lt (maxRange f j) (f (succ j) + eps))`.
            let split = d.lemma(p.lt_cotrans, &[fsj, head_padded, head_lt, mrj]);
            let left_ty = d.const_app(p.lt, &[fsj, mrj]);
            let right_ty = d.const_app(p.lt, &[mrj, head_padded]);

            let left_branch = {
                let h_fv = d.fresh_fvar();
                let h = d.kernel().fvar(h_fv);
                // The old witness survives: `f (succ j) < maxRange f j ≤ f i + eps`.
                let hsj_le = d.lemma(p.le_of_lt, &[fsj, mrj, h]);
                let head = d.lemma(p.le_trans, &[fsj, mrj, padded_i, hsj_le, hle]);
                let combined = d.lemma(p.max_le, &[mrj, fsj, padded_i, hle, head]);
                let le_succ_j = d.lemma(nat_p.le_succ, &[j]);
                let bound_succ = d.lemma(nat_p.le_trans, &[i, j, sj, hb, le_succ_j]);
                let bound_succ_ty = d.le(i, sj);
                let mrsj = d.const_app(p.max_range, &[f, sj]);
                let est_succ_ty = cle(d, p, mrsj, padded_i);
                let whole = and_intro(d, p, bound_succ_ty, est_succ_ty, bound_succ, combined);
                let witnessed = intro(d, sj, i, whole);
                d.lam_fv(h_fv, left_ty, witnessed)
            };
            let right_branch = {
                let h_fv = d.fresh_fvar();
                let h = d.kernel().fvar(h_fv);
                // The new sample wins: `maxRange f j < f (succ j) + eps`.
                let hmr_le = d.lemma(p.le_of_lt, &[mrj, head_padded, h]);
                let combined = d.lemma(p.max_le, &[mrj, fsj, head_padded, hmr_le, head_le]);
                let bound_succ = d.lemma(nat_p.le_refl, &[sj]);
                let bound_succ_ty = d.le(sj, sj);
                let mrsj = d.const_app(p.max_range, &[f, sj]);
                let est_succ_ty = cle(d, p, mrsj, head_padded);
                let whole = and_intro(d, p, bound_succ_ty, est_succ_ty, bound_succ, combined);
                let witnessed = intro(d, sj, sj, whole);
                d.lam_fv(h_fv, right_ty, witnessed)
            };

            let body = d.lemma(
                logic.or_elim,
                &[left_ty, right_ty, target, split, left_branch, right_branch],
            );
            let inner = d.lam_fv(hp_fv, hp_ty, body);
            d.lam_fv(i_fv, nat, inner)
        };
        exists_elim(d, pr_j, target, ih, minor)
    };

    let proof = d.induct(&motive, &base, &step, n);
    let concl = motive(d, n);

    let ty = {
        let out = d.pi_fv(e_fv, nat, concl);
        let out = d.pi_fv(n_fv, nat, out);
        d.pi_fv(f_fv, fn_ty, out)
    };
    let value = {
        let out = d.lam_fv(e_fv, nat, proof);
        let out = d.lam_fv(n_fv, nat, out);
        d.lam_fv(f_fv, fn_ty, out)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.max_range_attained_approx,
        uparams: vec![],
        ty,
        value,
    })
}

// ---------------------------------------------------------------------------
// `CReal.supSeq_le_shift`
// ---------------------------------------------------------------------------

/// `CReal.supSeq_le_shift : ∀ F a b u, le a b → ∀ k n,
/// le (supSeq F a b u n) (add (supSeq F a b u k) (ofRat (Rat.natDivSucc 1
/// (meshLevelCount k))))` — EVERY term of the sup sequence is within `1/2^k`
/// of the `k`-th term, in whichever direction.
///
/// [`CRealPrelude::sup_seq_le_add`](super::CRealPrelude::sup_seq_le_add)
/// already says this for `n ≥ k`. The point of this lemma is the other side,
/// which is free: for `n ≤ k` the sequence is MONOTONE
/// ([`CRealPrelude::sup_seq_mono`](super::CRealPrelude::sup_seq_mono) —
/// refining a mesh only adds sample points), so `supSeq n ≤ supSeq k` outright
/// and the `1/2^k` is spent on nothing. `Nat.le_total` joins the two.
///
/// Why it is needed at all: `converges_upper_bound` asks for a bound at EVERY
/// index, and the approximate-LUB assembly has one only at the index whose
/// mesh supplied the witness point.
fn declare_sup_seq_le_shift_thm(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = creal_ty(d, p);
    let func_ty = d.arrow(carrier, carrier);
    let nat_p = p.rat.int.nat;
    let logic = p.rat.int.logic;

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let u_fv = d.fresh_fvar();
    let u = d.kernel().fvar(u_fv);
    let u_ty = d.const_app(p.uniformly_continuous_on, &[f, a, b]);
    let hab_fv = d.fresh_fvar();
    let hab = d.kernel().fvar(hab_fv);
    let hab_ty = cle(d, p, a, b);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let mlc_k = d.const_app(p.mesh_level_count, &[k]);
    let (geom, geom_real) = unit_frac_real(d, p, mlc_k);
    let seq_k = d.const_app(p.sup_seq, &[f, a, b, u, k]);
    let seq_n = d.const_app(p.sup_seq, &[f, a, b, u, n]);
    let rhs = cadd(d, p, seq_k, geom_real);
    let concl = cle(d, p, seq_n, rhs);

    let le_kn_ty = d.le(k, n);
    let le_nk_ty = d.le(n, k);
    let split = d.lemma(nat_p.le_total, &[k, n]);

    let minor_kn = {
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let body = d.lemma(p.sup_seq_le_add, &[f, a, b, u, hab, k, n, h]);
        d.lam_fv(h_fv, le_kn_ty, body)
    };
    let minor_nk = {
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let mono = d.lemma(p.sup_seq_mono, &[f, a, b, u, hab, n, k, h]);
        let one_nat = d.num(1);
        let nonneg = d.lemma(p.rat.zero_le_nat_div_succ, &[one_nat, mlc_k]);
        let grow = d.lemma(p.le_add_of_nonneg, &[seq_k, geom, nonneg]);
        let body = d.lemma(p.le_trans, &[seq_n, seq_k, rhs, mono, grow]);
        d.lam_fv(h_fv, le_nk_ty, body)
    };
    let proof = d.lemma(
        logic.or_elim,
        &[le_kn_ty, le_nk_ty, concl, split, minor_kn, minor_nk],
    );

    let ty = {
        let out = d.pi_fv(n_fv, nat, concl);
        let out = d.pi_fv(k_fv, nat, out);
        let out = d.arrow(hab_ty, out);
        let out = d.pi_fv(u_fv, u_ty, out);
        let out = d.pi_fv(b_fv, carrier, out);
        let out = d.pi_fv(a_fv, carrier, out);
        d.pi_fv(f_fv, func_ty, out)
    };
    let value = {
        let out = d.lam_fv(n_fv, nat, proof);
        let out = d.lam_fv(k_fv, nat, out);
        let out = d.lam_fv(hab_fv, hab_ty, out);
        let out = d.lam_fv(u_fv, u_ty, out);
        let out = d.lam_fv(b_fv, carrier, out);
        let out = d.lam_fv(a_fv, carrier, out);
        d.lam_fv(f_fv, func_ty, out)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.sup_seq_le_shift,
        uparams: vec![],
        ty,
        value,
    })
}

// ---------------------------------------------------------------------------
// `CReal.supOn_approx_lub`
// ---------------------------------------------------------------------------

/// `CReal.supOn_approx_lub : ∀ F a b (hab : le a b) (u : UniformlyContinuousOn
/// F a b) (e : Nat), ∃ x, le a x ∧ (le x b ∧ le (supOn F a b hab u)
/// (add (F x) (ofRat (Rat.natDivSucc 1 e))))` — **the constructive
/// least-upper-bound law.**
///
/// `supOn` is approached by values of `F` on `[a, b]`, to any requested
/// accuracy, at a point exhibited by the proof. It is NOT attained, and the
/// exact form is refuted, not merely unproved — see this module's own header
/// and [`CRealPrelude::evt_attained_max_decides_sign`](super::CRealPrelude::evt_attained_max_decides_sign).
///
/// The assembly, at `e2 := 2·e + 1` (the halving index
/// `Rat.natDivSucc_halve`'s own shape asks for):
///
/// 1. [`CRealPrelude::max_range_attained_approx`](super::CRealPrelude::max_range_attained_approx)
///    at the level-`supLevel F a b u e2` mesh sampler gives an index `i` with
///    `supSeq F a b u e2 ≤ F(a + i·Δ) + 1/(2e+2)`. The equality between
///    `maxRange sampler (meshLevelCount level)` and `supSeq F a b u e2` is
///    definitional — `supSeq`, `meshMax` and the sampler are the same three
///    unfoldings the sup construction already runs on, so nothing is rebuilt
///    here and no `Definition` with a large embedded proof is touched.
/// 2. [`CRealPrelude::riemann_sample_in_bounds`](super::CRealPrelude::riemann_sample_in_bounds)
///    places that sample point in `[a, b]`. This is the whole reason the LUB
///    half needs no cell-location argument: the witness is a mesh point by
///    construction, so its membership is already proved.
/// 3. [`CRealPrelude::sup_seq_le_shift`](super::CRealPrelude::sup_seq_le_shift)
///    turns the estimate at the single index `e2` into one at EVERY index,
///    which is what `converges_upper_bound` consumes.
/// 4. [`CRealPrelude::converges_upper_bound`](super::CRealPrelude::converges_upper_bound)
///    against
///    [`CRealPrelude::sup_seq_converges_sup_on`](super::CRealPrelude::sup_seq_converges_sup_on)
///    passes to the limit.
///
/// The two `1/(2e+2)` summands — the fold's slack and the sequence shift —
/// fuse to `1/(e+1)` by `Rat.natDivSucc_add` then `Rat.natDivSucc_halve`. The
/// sequence shift arrives as `1/2^e2` and is weakened to `1/(2e+2)` through
/// [`CRealPrelude::le_mesh_level_count`](super::CRealPrelude::le_mesh_level_count)
/// and `Rat.natDivSucc_antitone` — the same geometric-to-harmonic step
/// `supSeq_abs_diff_le` runs, for the same reason.
fn declare_sup_on_approx_lub_thm(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = creal_ty(d, p);
    let func_ty = d.arrow(carrier, carrier);
    let nat_p = p.rat.int.nat;
    let rat = p.rat;
    let logic = p.rat.int.logic;
    let one_level = d.level_one();

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let hab_fv = d.fresh_fvar();
    let hab = d.kernel().fvar(hab_fv);
    let hab_ty = cle(d, p, a, b);
    let u_fv = d.fresh_fvar();
    let u = d.kernel().fvar(u_fv);
    let u_ty = d.const_app(p.uniformly_continuous_on, &[f, a, b]);
    let e_fv = d.fresh_fvar();
    let e = d.kernel().fvar(e_fv);

    // `e2 := succ (2 · e)`, exactly `Rat.natDivSucc_halve`'s index shape.
    let e2 = {
        let two_nat = d.num(2);
        let doubled = NatOps::mul(d, two_nat, e);
        d.succ(doubled)
    };
    let (eps_rat, eps_real) = unit_frac_real(d, p, e);
    let (half_rat, half_real) = unit_frac_real(d, p, e2);

    // The level-`e2` mesh: its level, its count, its width, its sampler.
    let level = d.const_app(p.sup_level, &[f, a, b, u, e2]);
    let count = d.const_app(p.mesh_level_count, &[level]);
    let delta = mesh_delta(d, p, a, b, count);
    let sampler = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let sp = mesh_sample_point(d, p, a, delta, i);
        let fx = d.apply(f, &[sp]);
        d.lam_fv(i_fv, nat, fx)
    };
    let seq_e2 = d.const_app(p.sup_seq, &[f, a, b, u, e2]);
    let target_real = d.const_app(p.sup_on, &[f, a, b, hab, u]);

    // `fun x => And (le a x) (And (le x b) (le supOn (add (F x) eps)))`.
    let goal_pred = {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let lo = cle(d, p, a, x);
        let hi = cle(d, p, x, b);
        let fx = d.apply(f, &[x]);
        let padded = cadd(d, p, fx, eps_real);
        let est = cle(d, p, target_real, padded);
        let tail = d.and(hi, est);
        let body = d.and(lo, tail);
        d.lam_fv(x_fv, carrier, body)
    };
    let goal = {
        let ex = d.kernel().const_(logic.exists_, vec![one_level]);
        d.apply(ex, &[carrier, goal_pred])
    };

    // The sup sequence as the eta-expanded lambda `supSeq_converges_supOn`
    // itself names, so `converges_upper_bound`'s `f` argument is the SAME
    // `ExprId` and the `Converges` hypothesis matches without unfolding.
    let seq_lambda = {
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let body = d.const_app(p.sup_seq, &[f, a, b, u, m]);
        d.lam_fv(m_fv, nat, body)
    };
    let conv = d.lemma(p.sup_seq_converges_sup_on, &[f, a, b, hab, u]);

    // `1/2^e2 ≤ 1/(2e+2)` — the geometric-to-harmonic weakening.
    let mlc_e2 = d.const_app(p.mesh_level_count, &[e2]);
    let (geom_rat, geom_real) = unit_frac_real(d, p, mlc_e2);
    let geom_le_half = {
        let hk = d.lemma(p.le_mesh_level_count, &[e2]);
        d.lemma(rat.nat_div_succ_antitone, &[e2, mlc_e2, hk])
    };

    // `1/(2e+2) + 1/(2e+2) = 1/(e+1)`, as a `Rat` equation.
    //
    // `nat_div_succ_add` lands on `natDivSucc (Nat.add 1 1) e2` and
    // `nat_div_succ_halve` starts from `natDivSucc 2 e2`; the two agree by
    // `Nat.add`'s own reduction (the numerals here are unary and both
    // arguments are literals, so this is one `whnf` step, not the superlinear
    // path CLAUDE.md warns about for large formed magnitudes).
    let half_plus_half_eq_eps = {
        let one_nat = d.num(1);
        let two_nat = d.num(2);
        let fuse = d.lemma(rat.nat_div_succ_add, &[one_nat, one_nat, e2]);
        let halve = d.lemma(rat.nat_div_succ_halve, &[e]);
        let two_over = d.const_app(rat.nat_div_succ, &[two_nat, e2]);
        let sum = radd(d, half_rat, half_rat);
        rtrans(d, sum, two_over, eps_rat, fuse, halve)
    };

    let minor = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let hp_fv = d.fresh_fvar();
        let hp = d.kernel().fvar(hp_fv);
        let bound_ty = d.le(i, count);
        let point = mesh_sample_point(d, p, a, delta, i);
        let f_point = d.apply(f, &[point]);
        let padded_half = cadd(d, p, f_point, half_real);
        let mr = d.const_app(p.max_range, &[sampler, count]);
        let est_ty = cle(d, p, mr, padded_half);
        let hp_ty = d.and(bound_ty, est_ty);
        let hb = d.and_left(bound_ty, est_ty, hp);
        let hest = d.and_right(bound_ty, est_ty, hp);

        // The witness lies in `[a, b]`.
        let hlt = d.lemma(nat_p.lt_succ_of_le, &[i, count, hb]);
        let rng = d.const_app(p.riemann_sample_in_bounds, &[a, b, count, i, hab, hlt]);
        let lo_ty = cle(d, p, a, point);
        let hi_ty = cle(d, p, point, b);
        let hlo = d.const_app(logic.and_left, &[lo_ty, hi_ty, rng]);
        let hhi = d.const_app(logic.and_right, &[lo_ty, hi_ty, rng]);

        let padded_eps = cadd(d, p, f_point, eps_real);

        // `∀ m, le (supSeq m) (add (F point) eps)`.
        let forall_bound = {
            let m_fv = d.fresh_fvar();
            let m = d.kernel().fvar(m_fv);
            let seq_m = d.const_app(p.sup_seq, &[f, a, b, u, m]);
            let shift = d.lemma(p.sup_seq_le_shift, &[f, a, b, u, hab, e2, m]);
            let shifted = cadd(d, p, seq_e2, geom_real);

            // Weaken the shift `1/2^e2` to `1/(2e+2)`.
            let lift = d.lemma(p.of_rat_le, &[geom_rat, half_rat, geom_le_half]);
            let refl_seq = d.lemma(p.le_refl, &[seq_e2]);
            let widen = d.lemma(
                p.add_le_add,
                &[seq_e2, seq_e2, geom_real, half_real, refl_seq, lift],
            );
            let shifted_half = cadd(d, p, seq_e2, half_real);
            let step1 = d.lemma(p.le_trans, &[seq_m, shifted, shifted_half, shift, widen]);

            // `supSeq e2 ≤ F point + 1/(2e+2)`, so the whole is
            // `(F point + 1/(2e+2)) + 1/(2e+2)`.
            let refl_half = d.lemma(p.le_refl, &[half_real]);
            let grow = d.lemma(
                p.add_le_add,
                &[seq_e2, padded_half, half_real, half_real, hest, refl_half],
            );
            let doubled = cadd(d, p, padded_half, half_real);
            let step2 = d.lemma(p.le_trans, &[seq_m, shifted_half, doubled, step1, grow]);

            // `(F point + h) + h ≈ F point + (h + h) ≈ F point + eps`.
            let assoc = d.lemma(p.add_assoc, &[f_point, half_real, half_real]);
            let inner_sum = cadd(d, p, half_real, half_real);
            let sum_rat = radd(d, half_rat, half_rat);
            let sum_embed = d.lemma(p.of_rat_add, &[half_rat, half_rat]);
            let sum_real = embed(d, p, sum_rat);
            let rewrite_sum = {
                let start = d.lemma(p.equiv_refl, &[sum_real]);
                rat_eq_rewrite(
                    d,
                    sum_rat,
                    eps_rat,
                    half_plus_half_eq_eps,
                    start,
                    &|d, t| {
                        let emb = embed(d, p, t);
                        cequiv(d, p, sum_real, emb)
                    },
                )
            };
            let inner_to_eps = d.lemma(
                p.equiv_trans,
                &[inner_sum, sum_real, eps_real, sum_embed, rewrite_sum],
            );
            let refl_point = d.lemma(p.equiv_refl, &[f_point]);
            let tail = d.lemma(
                p.add_congr,
                &[
                    f_point,
                    f_point,
                    inner_sum,
                    eps_real,
                    refl_point,
                    inner_to_eps,
                ],
            );
            let regrouped = cadd(d, p, f_point, inner_sum);
            let whole_eq = d.lemma(
                p.equiv_trans,
                &[doubled, regrouped, padded_eps, assoc, tail],
            );
            let refl_seq_m = d.lemma(p.equiv_refl, &[seq_m]);
            let body = d.lemma(
                p.le_congr,
                &[
                    seq_m, seq_m, doubled, padded_eps, refl_seq_m, whole_eq, step2,
                ],
            );
            d.lam_fv(m_fv, nat, body)
        };

        let limit = d.lemma(
            p.converges_upper_bound,
            &[seq_lambda, target_real, padded_eps, forall_bound, conv],
        );

        let est_final_ty = cle(d, p, target_real, padded_eps);
        let tail_ty = d.and(hi_ty, est_final_ty);
        let tail = and_intro(d, p, hi_ty, est_final_ty, hhi, limit);
        let whole = and_intro(d, p, lo_ty, tail_ty, hlo, tail);
        let ctor = d.kernel().const_(logic.exists_intro, vec![one_level]);
        let witnessed = d.apply(ctor, &[carrier, goal_pred, point, whole]);
        let inner = d.lam_fv(hp_fv, hp_ty, witnessed);
        d.lam_fv(i_fv, nat, inner)
    };

    let attained = d.lemma(p.max_range_attained_approx, &[sampler, count, e2]);
    let attained_pred = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let bound = d.le(i, count);
        let si = d.apply(sampler, &[i]);
        let padded = cadd(d, p, si, half_real);
        let mr = d.const_app(p.max_range, &[sampler, count]);
        let est = cle(d, p, mr, padded);
        let body = d.and(bound, est);
        d.lam_fv(i_fv, nat, body)
    };
    let proof = exists_elim(d, attained_pred, goal, attained, minor);

    let ty = {
        let out = d.pi_fv(e_fv, nat, goal);
        let out = d.pi_fv(u_fv, u_ty, out);
        let out = d.pi_fv(hab_fv, hab_ty, out);
        let out = d.pi_fv(b_fv, carrier, out);
        let out = d.pi_fv(a_fv, carrier, out);
        d.pi_fv(f_fv, func_ty, out)
    };
    let value = {
        let out = d.lam_fv(e_fv, nat, proof);
        let out = d.lam_fv(u_fv, u_ty, out);
        let out = d.lam_fv(hab_fv, hab_ty, out);
        let out = d.lam_fv(b_fv, carrier, out);
        let out = d.lam_fv(a_fv, carrier, out);
        d.lam_fv(f_fv, func_ty, out)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.sup_on_approx_lub,
        uparams: vec![],
        ty,
        value,
    })
}

/// Land `CReal.maxRange_attained_approx`.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
pub(super) fn declare_max_range_attained_approx(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    declare_max_range_attained_approx_thm(d, p)
}

/// Land `CReal.supSeq_le_shift`.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
pub(super) fn declare_sup_seq_le_shift(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    declare_sup_seq_le_shift_thm(d, p)
}

/// Land `CReal.supOn_approx_lub`.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
pub(super) fn declare_sup_on_approx_lub(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    declare_sup_on_approx_lub_thm(d, p)
}

// ---------------------------------------------------------------------------
// `CReal.supSeq_le_supOn` and `CReal.supOn_ub_at_supSeq_point`
// ---------------------------------------------------------------------------

/// `CReal.supSeq_le_supOn : ∀ F a b (hab : le a b) u k,
/// le (supSeq F a b u k) (supOn F a b hab u)` — every mesh maximum is below
/// the supremum, EXACTLY, with no epsilon.
///
/// This is the upper-bound law's first half, and it is free. The sup sequence
/// is monotone
/// ([`CRealPrelude::sup_seq_mono`](super::CRealPrelude::sup_seq_mono)) and
/// converges to `supOn`, so its `k`-th term bounds the limit below — but
/// `converges_lower_bound` wants the bound at literally EVERY index including
/// those below `k`, where it is false.
/// [`CRealPrelude::converges_lower_bound_shift`](super::CRealPrelude::converges_lower_bound_shift)
/// is exactly the eventual form that exists for this situation: at shift
/// `s := k` the hypothesis is `∀ n, supSeq k ≤ supSeq (n + k)`, which is
/// monotonicity and nothing else.
///
/// `Nat.le_add_right` states `Le n (add n k)` — the operands the other way
/// round from what the shift needs — so one `Nat.add_comm` rewrite stands
/// between them. That is the only non-mechanical step.
fn declare_sup_seq_le_sup_on_thm(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = creal_ty(d, p);
    let func_ty = d.arrow(carrier, carrier);
    let nat_p = p.rat.int.nat;

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let hab_fv = d.fresh_fvar();
    let hab = d.kernel().fvar(hab_fv);
    let hab_ty = cle(d, p, a, b);
    let u_fv = d.fresh_fvar();
    let u = d.kernel().fvar(u_fv);
    let u_ty = d.const_app(p.uniformly_continuous_on, &[f, a, b]);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);

    let seq_k = d.const_app(p.sup_seq, &[f, a, b, u, k]);
    let target_real = d.const_app(p.sup_on, &[f, a, b, hab, u]);
    let seq_lambda = {
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let body = d.const_app(p.sup_seq, &[f, a, b, u, m]);
        d.lam_fv(m_fv, nat, body)
    };
    let conv = d.lemma(p.sup_seq_converges_sup_on, &[f, a, b, hab, u]);

    let forall_bound = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        // `Nat.le k (Nat.add n k)`, from `le_add_right k n : Le k (add k n)`
        // rewritten along `Nat.add_comm k n`.
        let shifted = NatOps::add(d, k, n);
        let flipped = NatOps::add(d, n, k);
        let raw = d.lemma(nat_p.le_add_right, &[k, n]);
        let comm = d.lemma(nat_p.add_comm, &[k, n]);
        let hle = nat_rewrite_prop(d, shifted, flipped, comm, raw, &|d, t| d.le(k, t));
        let body = d.lemma(p.sup_seq_mono, &[f, a, b, u, hab, k, flipped, hle]);
        d.lam_fv(n_fv, nat, body)
    };
    let proof = d.lemma(
        p.converges_lower_bound_shift,
        &[k, seq_k, seq_lambda, target_real, forall_bound, conv],
    );
    let concl = cle(d, p, seq_k, target_real);

    let ty = {
        let out = d.pi_fv(k_fv, nat, concl);
        let out = d.pi_fv(u_fv, u_ty, out);
        let out = d.pi_fv(hab_fv, hab_ty, out);
        let out = d.pi_fv(b_fv, carrier, out);
        let out = d.pi_fv(a_fv, carrier, out);
        d.pi_fv(f_fv, func_ty, out)
    };
    let value = {
        let out = d.lam_fv(k_fv, nat, proof);
        let out = d.lam_fv(u_fv, u_ty, out);
        let out = d.lam_fv(hab_fv, hab_ty, out);
        let out = d.lam_fv(b_fv, carrier, out);
        let out = d.lam_fv(a_fv, carrier, out);
        d.lam_fv(f_fv, func_ty, out)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.sup_seq_le_sup_on,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CReal.supOn_ub_at_supSeq_point : ∀ F a b (hab : le a b) u k i,
/// Nat.le i (meshLevelCount (supLevel F a b u k)) →
/// le (F (meshSamplePoint a (meshDelta a b (meshLevelCount (supLevel F a b u
/// k))) i)) (supOn F a b hab u)` — **the upper-bound law at every point the
/// construction samples.**
///
/// [`CRealPrelude::max_range_ub`](super::CRealPrelude::max_range_ub) says the
/// fold dominates each of its samples, and `maxRange sampler count` IS
/// `supSeq F a b u k` definitionally (through `supSeq` and `meshMax`, both
/// small `Definition`s with no embedded proof term); then
/// [`declare_sup_seq_le_sup_on_thm`]. Two steps.
///
/// **This is deliberately NOT stated at an arbitrary mesh level `j`**, and the
/// restriction is real rather than laziness. `supSeq` samples only the levels
/// `supLevel F a b u k`, and nothing here proves that schedule is cofinal in
/// the levels: `supLevel` is `Nat.size (bound (b−a)) + trueExpOfModulus m k`,
/// and `trueExpOfModulus` accumulates `expOfModulus`, which is `0` whenever
/// the modulus is. A modulus that is eventually `0` — legitimate for a
/// locally constant `F` — leaves the schedule bounded. So
/// `meshMax F a b j ≤ supOn` at an arbitrary `j` needs a cofinality argument
/// this file does not have, and asserting it would be the stronger claim
/// rather than the honest one.
///
/// It pairs exactly with
/// [`CRealPrelude::sup_on_approx_lub`](super::CRealPrelude::sup_on_approx_lub),
/// whose witness is a point of precisely this family: together they say
/// `supOn` is the supremum of `F` over the sampled set. Extending the upper
/// bound to an ARBITRARY `x ∈ [a, b]` is the remaining step — see this
/// module's header for why that one needs cell location.
fn declare_sup_on_ub_at_sup_seq_point_thm(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = creal_ty(d, p);
    let func_ty = d.arrow(carrier, carrier);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let hab_fv = d.fresh_fvar();
    let hab = d.kernel().fvar(hab_fv);
    let hab_ty = cle(d, p, a, b);
    let u_fv = d.fresh_fvar();
    let u = d.kernel().fvar(u_fv);
    let u_ty = d.const_app(p.uniformly_continuous_on, &[f, a, b]);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);

    let level = d.const_app(p.sup_level, &[f, a, b, u, k]);
    let count = d.const_app(p.mesh_level_count, &[level]);
    let delta = mesh_delta(d, p, a, b, count);
    let sampler = {
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let sp = mesh_sample_point(d, p, a, delta, j);
        let fx = d.apply(f, &[sp]);
        d.lam_fv(j_fv, nat, fx)
    };
    let point = mesh_sample_point(d, p, a, delta, i);
    let f_point = d.apply(f, &[point]);
    let seq_k = d.const_app(p.sup_seq, &[f, a, b, u, k]);
    let target_real = d.const_app(p.sup_on, &[f, a, b, hab, u]);

    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);
    let h_ty = d.le(i, count);

    let ub = d.lemma(p.max_range_ub, &[sampler, count, i, h]);
    let top = d.lemma(p.sup_seq_le_sup_on, &[f, a, b, hab, u, k]);
    let body = d.lemma(p.le_trans, &[f_point, seq_k, target_real, ub, top]);
    let concl = cle(d, p, f_point, target_real);

    let ty = {
        let out = d.arrow(h_ty, concl);
        let out = d.pi_fv(i_fv, nat, out);
        let out = d.pi_fv(k_fv, nat, out);
        let out = d.pi_fv(u_fv, u_ty, out);
        let out = d.pi_fv(hab_fv, hab_ty, out);
        let out = d.pi_fv(b_fv, carrier, out);
        let out = d.pi_fv(a_fv, carrier, out);
        d.pi_fv(f_fv, func_ty, out)
    };
    let value = {
        let out = d.lam_fv(h_fv, h_ty, body);
        let out = d.lam_fv(i_fv, nat, out);
        let out = d.lam_fv(k_fv, nat, out);
        let out = d.lam_fv(u_fv, u_ty, out);
        let out = d.lam_fv(hab_fv, hab_ty, out);
        let out = d.lam_fv(b_fv, carrier, out);
        let out = d.lam_fv(a_fv, carrier, out);
        d.lam_fv(f_fv, func_ty, out)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.sup_on_ub_at_sup_seq_point,
        uparams: vec![],
        ty,
        value,
    })
}

/// Land `CReal.supSeq_le_supOn` and `CReal.supOn_ub_at_supSeq_point`.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
pub(super) fn declare_sup_on_ub_at_sup_seq_point(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    declare_sup_seq_le_sup_on_thm(d, p)?;
    declare_sup_on_ub_at_sup_seq_point_thm(d, p)
}

// ---------------------------------------------------------------------------
// `CReal.stepFamily_locate` -- cell location, stated over the ORDER alone
// ---------------------------------------------------------------------------

/// `le x (add x w)` from `le zero w` -- re-derived from
/// `creal/supremum.rs`'s private `shift_le_of_nonneg_local`, per this
/// development's convention. (`CReal.le_add_of_nonneg` is the same fact but
/// takes its shift as a `Rat`; here the shift is a `CReal` parameter.)
fn shift_le_of_nonneg(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    x: ExprId,
    w: ExprId,
    hw: ExprId,
) -> ExprId {
    let zero_c = d.kernel().const_(p.zero, vec![]);
    let refl_x = d.lemma(p.le_refl, &[x]);
    let grown = d.lemma(p.add_le_add, &[x, x, zero_c, w, refl_x, hw]);
    let padded = cadd(d, p, x, zero_c);
    let target = cadd(d, p, x, w);
    let trim = d.lemma(p.add_zero, &[x]);
    let refl_target = d.lemma(p.equiv_refl, &[target]);
    d.lemma(
        p.le_congr,
        &[padded, x, target, target, trim, refl_target, grown],
    )
}

/// `lt x (add x eps)` from `lt zero eps`.
fn lt_add_pos(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    x: ExprId,
    eps: ExprId,
    eps_pos: ExprId,
) -> ExprId {
    let zero_c = d.kernel().const_(p.zero, vec![]);
    let refl = d.lemma(p.le_refl, &[x]);
    let raw = d.lemma(
        p.add_lt_add_of_le_of_lt,
        &[x, x, zero_c, eps, refl, eps_pos],
    );
    let padded_zero = cadd(d, p, x, zero_c);
    let padded_eps = cadd(d, p, x, eps);
    let trim = d.lemma(p.add_zero, &[x]);
    let refl_rhs = d.lemma(p.equiv_refl, &[padded_eps]);
    d.lemma(
        p.lt_congr,
        &[padded_zero, x, padded_eps, padded_eps, trim, refl_rhs, raw],
    )
}

/// `CReal.stepFamily_locate : forall (P : Nat -> CReal) (w eps : CReal),
/// le zero w -> lt zero eps -> (forall i, le (P (Nat.succ i)) (add (P i) w)) ->
/// forall (n : Nat) (t : CReal), le (P Nat.zero) t ->
/// le t (add (add (P n) w) eps) ->
/// exists i, Nat.le i n /\ (le (P i) (add t eps) /\ le t (add (add (P i) w) eps))`
/// -- **cell location: a real lying under a finite increasing family is
/// located, to within one step plus `eps`, at one member of it.**
///
/// This is the piece the upper-bound law needs and the approximate
/// least-upper-bound law does not (see this module's header). An arbitrary
/// `x` in `[a, b]` is not a mesh point and no computed index finds it:
/// locating it EXACTLY would decide `le x y` or `le y x` for arbitrary reals.
/// Locating it to within `eps` is constructive, by
/// [`CRealPrelude::lt_cotrans`](super::CRealPrelude::lt_cotrans), and `eps` is
/// then absorbed by uniform continuity at the caller.
///
/// **Stated over the ORDER alone, deliberately.** Nothing here mentions
/// `meshDelta`, `meshSamplePoint`, `CReal.mul` or `CReal.ofNat` -- the family
/// `P` is an arbitrary `Nat -> CReal` whose consecutive gaps are bounded by
/// `w`. The mesh-specific version is an instantiation (`P i :=
/// meshSamplePoint a delta i`, `w := delta`) whose only content is the three
/// interface identities `P 0 ~ a`, `P (i+1) ~ P i + delta` and
/// `P N + delta ~ b`. A first draft that carried the mesh through the
/// induction had to re-prove `ofNat (succ i) * delta ~ ofNat i * delta +
/// delta` inside every branch; this version has no ring algebra in it at all,
/// which is most of why it was cheap.
///
/// The induction is on the family's own bound, with `t` quantified INSIDE the
/// motive so that the inductive hypothesis is available at the SHIFTED upper
/// bound the cotransitive split produces:
///
/// - `n = 0`: the witness is `0` and the second conjunct IS the hypothesis.
/// - `n = j+1`: split on `P (j+1) < t` versus `t < P (j+1) + eps`
///   ([`lt_add_pos`] supplies the strict gap). The FIRST branch takes the
///   witness `j+1` and, again, the second conjunct is the hypothesis
///   unchanged. The SECOND branch feeds the inductive hypothesis, and this is
///   the only step that uses `hstep`: `t <= P (j+1) + eps <= (P j + w) + eps`
///   is exactly the shape the motive asks for at `j`.
///
/// Note which index each branch tests. Splitting at `P j` instead of at
/// `P (j+1)` -- the first thing to try -- makes the winning branch's own bound
/// come out at `2w` rather than `w`, because the hypothesis is stated one step
/// above the index being tested. The split has to be at the TOP of the range
/// under consideration, not at the point the inductive hypothesis will be
/// applied to.
fn declare_step_family_locate_thm(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = creal_ty(d, p);
    let fam_ty = d.arrow(nat, carrier);
    let nat_p = p.rat.int.nat;
    let logic = p.rat.int.logic;
    let one_level = d.level_one();
    let zero_c = d.kernel().const_(p.zero, vec![]);

    let pp_fv = d.fresh_fvar();
    let pp = d.kernel().fvar(pp_fv);
    let w_fv = d.fresh_fvar();
    let w = d.kernel().fvar(w_fv);
    let eps_fv = d.fresh_fvar();
    let eps = d.kernel().fvar(eps_fv);
    let hw_fv = d.fresh_fvar();
    let hw_ty = cle(d, p, zero_c, w);
    let hpos_fv = d.fresh_fvar();
    let hpos = d.kernel().fvar(hpos_fv);
    let hpos_ty = d.const_app(p.lt, &[zero_c, eps]);

    // `forall i, le (P (succ i)) (add (P i) w)`.
    let hstep_ty = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let si = d.succ(i);
        let psi = d.apply(pp, &[si]);
        let pi = d.apply(pp, &[i]);
        let shifted = cadd(d, p, pi, w);
        let body = cle(d, p, psi, shifted);
        d.pi_fv(i_fv, nat, body)
    };
    let hstep_fv = d.fresh_fvar();
    let hstep = d.kernel().fvar(hstep_fv);

    let eps_nonneg = d.lemma(p.le_of_lt, &[zero_c, eps, hpos]);

    // `fun i => And (Nat.le i n) (And (le (P i) (t + eps)) (le t ((P i + w) + eps)))`.
    let goal_pred = |d: &mut IntDev<'_>, n: ExprId, t: ExprId| -> ExprId {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let pi = d.apply(pp, &[i]);
        let bound = d.le(i, n);
        let t_eps = cadd(d, p, t, eps);
        let lower = cle(d, p, pi, t_eps);
        let pi_w = cadd(d, p, pi, w);
        let pi_w_eps = cadd(d, p, pi_w, eps);
        let upper = cle(d, p, t, pi_w_eps);
        let inner = d.and(lower, upper);
        let body = d.and(bound, inner);
        d.lam_fv(i_fv, nat, body)
    };
    let goal_at = |d: &mut IntDev<'_>, n: ExprId, t: ExprId| -> ExprId {
        let pr = goal_pred(d, n, t);
        let ex = d.kernel().const_(logic.exists_, vec![one_level]);
        d.apply(ex, &[nat, pr])
    };
    let intro_at =
        |d: &mut IntDev<'_>, n: ExprId, t: ExprId, witness: ExprId, proof: ExprId| -> ExprId {
            let pr = goal_pred(d, n, t);
            let ctor = d.kernel().const_(logic.exists_intro, vec![one_level]);
            d.apply(ctor, &[nat, pr, witness, proof])
        };

    // `forall t, le (P 0) t -> le t ((P n + w) + eps) -> exists i, ...`.
    let motive = |d: &mut IntDev<'_>, n: ExprId| -> ExprId {
        let t_fv = d.fresh_fvar();
        let t = d.kernel().fvar(t_fv);
        let zero_n = d.zero();
        let p0 = d.apply(pp, &[zero_n]);
        let h0_ty = cle(d, p, p0, t);
        let pn = d.apply(pp, &[n]);
        let pn_w = cadd(d, p, pn, w);
        let pn_w_eps = cadd(d, p, pn_w, eps);
        let hn_ty = cle(d, p, t, pn_w_eps);
        let ex = goal_at(d, n, t);
        let inner = d.arrow(hn_ty, ex);
        let inner = d.arrow(h0_ty, inner);
        d.pi_fv(t_fv, carrier, inner)
    };

    let base = |d: &mut IntDev<'_>| -> ExprId {
        let t_fv = d.fresh_fvar();
        let t = d.kernel().fvar(t_fv);
        let zero_n = d.zero();
        let p0 = d.apply(pp, &[zero_n]);
        let h0_fv = d.fresh_fvar();
        let h0 = d.kernel().fvar(h0_fv);
        let h0_ty = cle(d, p, p0, t);
        let hn_fv = d.fresh_fvar();
        let hn = d.kernel().fvar(hn_fv);
        let p0_w = cadd(d, p, p0, w);
        let p0_w_eps = cadd(d, p, p0_w, eps);
        let hn_ty = cle(d, p, t, p0_w_eps);

        let bound_ty = d.le(zero_n, zero_n);
        let hb = d.lemma(nat_p.le_refl, &[zero_n]);
        let t_eps = cadd(d, p, t, eps);
        let grow = shift_le_of_nonneg(d, p, t, eps, eps_nonneg);
        let lower = d.lemma(p.le_trans, &[p0, t, t_eps, h0, grow]);
        let lower_ty = cle(d, p, p0, t_eps);
        let inner = and_intro(d, p, lower_ty, hn_ty, lower, hn);
        let inner_ty = d.and(lower_ty, hn_ty);
        let whole = and_intro(d, p, bound_ty, inner_ty, hb, inner);
        let witnessed = intro_at(d, zero_n, t, zero_n, whole);
        let with_hn = d.lam_fv(hn_fv, hn_ty, witnessed);
        let with_h0 = d.lam_fv(h0_fv, h0_ty, with_hn);
        d.lam_fv(t_fv, carrier, with_h0)
    };

    let step = |d: &mut IntDev<'_>, j: ExprId, ih: ExprId| -> ExprId {
        let sj = d.succ(j);
        let t_fv = d.fresh_fvar();
        let t = d.kernel().fvar(t_fv);
        let zero_n = d.zero();
        let p0 = d.apply(pp, &[zero_n]);
        let h0_fv = d.fresh_fvar();
        let h0 = d.kernel().fvar(h0_fv);
        let h0_ty = cle(d, p, p0, t);
        let hn_fv = d.fresh_fvar();
        let hn = d.kernel().fvar(hn_fv);
        let psj = d.apply(pp, &[sj]);
        let psj_w = cadd(d, p, psj, w);
        let psj_w_eps = cadd(d, p, psj_w, eps);
        let hn_ty = cle(d, p, t, psj_w_eps);

        let target = goal_at(d, sj, t);
        let hlt = lt_add_pos(d, p, psj, eps, hpos);
        let psj_eps = cadd(d, p, psj, eps);
        let split = d.lemma(p.lt_cotrans, &[psj, psj_eps, hlt, t]);
        let left_ty = d.const_app(p.lt, &[psj, t]);
        let right_ty = d.const_app(p.lt, &[t, psj_eps]);

        // `P (succ j) < t`: the top of the range wins, witness `succ j`, and
        // the second conjunct is `hn` unchanged.
        let left_branch = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let bound_ty = d.le(sj, sj);
            let hb = d.lemma(nat_p.le_refl, &[sj]);
            let hle = d.lemma(p.le_of_lt, &[psj, t, h]);
            let t_eps = cadd(d, p, t, eps);
            let grow = shift_le_of_nonneg(d, p, t, eps, eps_nonneg);
            let lower = d.lemma(p.le_trans, &[psj, t, t_eps, hle, grow]);
            let lower_ty = cle(d, p, psj, t_eps);
            let inner = and_intro(d, p, lower_ty, hn_ty, lower, hn);
            let inner_ty = d.and(lower_ty, hn_ty);
            let whole = and_intro(d, p, bound_ty, inner_ty, hb, inner);
            let witnessed = intro_at(d, sj, t, sj, whole);
            d.lam_fv(h_fv, left_ty, witnessed)
        };

        // `t < P (succ j) + eps`: step down. `hstep` is used HERE and nowhere
        // else -- `t <= P (succ j) + eps <= (P j + w) + eps` is exactly the
        // motive's hypothesis at `j`.
        let right_branch = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let hle = d.lemma(p.le_of_lt, &[t, psj_eps, h]);
            let pj = d.apply(pp, &[j]);
            let pj_w = cadd(d, p, pj, w);
            let pj_w_eps = cadd(d, p, pj_w, eps);
            let hs = d.apply(hstep, &[j]);
            let refl_eps = d.lemma(p.le_refl, &[eps]);
            let widen = d.lemma(p.add_le_add, &[psj, pj_w, eps, eps, hs, refl_eps]);
            let hyp = d.lemma(p.le_trans, &[t, psj_eps, pj_w_eps, hle, widen]);
            let ih_res = d.apply(ih, &[t, h0, hyp]);
            let pred_j = goal_pred(d, j, t);

            let minor = {
                let i_fv = d.fresh_fvar();
                let i = d.kernel().fvar(i_fv);
                let hp_fv = d.fresh_fvar();
                let hp = d.kernel().fvar(hp_fv);
                let pi = d.apply(pp, &[i]);
                let bound_j_ty = d.le(i, j);
                let t_eps = cadd(d, p, t, eps);
                let lower_ty = cle(d, p, pi, t_eps);
                let pi_w = cadd(d, p, pi, w);
                let pi_w_eps = cadd(d, p, pi_w, eps);
                let upper_ty = cle(d, p, t, pi_w_eps);
                let inner_ty = d.and(lower_ty, upper_ty);
                let hp_ty = d.and(bound_j_ty, inner_ty);
                let hb = d.and_left(bound_j_ty, inner_ty, hp);
                let rest = d.and_right(bound_j_ty, inner_ty, hp);
                let le_succ_j = d.lemma(nat_p.le_succ, &[j]);
                let bound_sj = d.lemma(nat_p.le_trans, &[i, j, sj, hb, le_succ_j]);
                let bound_sj_ty = d.le(i, sj);
                let whole = and_intro(d, p, bound_sj_ty, inner_ty, bound_sj, rest);
                let witnessed = intro_at(d, sj, t, i, whole);
                let inner = d.lam_fv(hp_fv, hp_ty, witnessed);
                d.lam_fv(i_fv, nat, inner)
            };
            let elim = exists_elim(d, pred_j, target, ih_res, minor);
            d.lam_fv(h_fv, right_ty, elim)
        };

        let body = d.lemma(
            logic.or_elim,
            &[left_ty, right_ty, target, split, left_branch, right_branch],
        );
        let with_hn = d.lam_fv(hn_fv, hn_ty, body);
        let with_h0 = d.lam_fv(h0_fv, h0_ty, with_hn);
        d.lam_fv(t_fv, carrier, with_h0)
    };

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let proof = d.induct(&motive, &base, &step, n);
    let concl = motive(d, n);

    let ty = {
        let out = d.pi_fv(n_fv, nat, concl);
        let out = d.pi_fv(hstep_fv, hstep_ty, out);
        let out = d.arrow(hpos_ty, out);
        let out = d.arrow(hw_ty, out);
        let out = d.pi_fv(eps_fv, carrier, out);
        let out = d.pi_fv(w_fv, carrier, out);
        d.pi_fv(pp_fv, fam_ty, out)
    };
    let value = {
        let out = d.lam_fv(n_fv, nat, proof);
        let out = d.lam_fv(hstep_fv, hstep_ty, out);
        let out = d.lam_fv(hpos_fv, hpos_ty, out);
        let out = d.lam_fv(hw_fv, hw_ty, out);
        let out = d.lam_fv(eps_fv, carrier, out);
        let out = d.lam_fv(w_fv, carrier, out);
        d.lam_fv(pp_fv, fam_ty, out)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.step_family_locate,
        uparams: vec![],
        ty,
        value,
    })
}

/// Land `CReal.stepFamily_locate` alone (a one-declaration `BuildStep`).
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
pub(super) fn declare_step_family_locate(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    declare_step_family_locate_thm(d, p)
}

// ---------------------------------------------------------------------------
// `CReal.meshMax_le_supOn_add` and `CReal.supOn_ub_at_fine_mesh_point`
// ---------------------------------------------------------------------------

/// `CReal.meshMax_le_supOn_add : forall F a b (hab : le a b) u k dd,
/// le (meshMax F a b (Nat.add (supLevel F a b u k) dd))
///    (add (supOn F a b hab u) (ofRat (Rat.natDivSucc 1 (meshLevelCount k))))`
/// -- **`supOn` dominates the mesh maximum at EVERY level above the schedule,
/// to within `1/2^k`.**
///
/// This is the way around the cofinality gap that
/// [`declare_sup_on_ub_at_sup_seq_point_thm`] documents. `supSeq` samples only
/// the levels `supLevel F a b u k`, and nothing proves that schedule is
/// cofinal, so `meshMax F a b j <= supOn` at an arbitrary `j` is not
/// available. But an arbitrary level ABOVE one scheduled level is, because
/// [`CRealPrelude::mesh_max_le_add_of_modulus`](super::CRealPrelude::mesh_max_le_add_of_modulus)
/// is depth-uniform: it takes the refinement depth `dd` as a free argument and
/// spends one epsilon however deep the refinement goes.
///
/// The `hsize` obligation is discharged exactly as
/// `supremum.rs`'s `declare_sup_seq_le_add_thm` discharges its own, and by the
/// same three-line route: `expOfModulus_le_trueExpOfModulus` under
/// `Nat.add_le_add_left`, with the width summand carried through untouched.
/// That is what `supLevel`'s additive shape buys, and it is why the request
/// index here must be `meshLevelCount k` and not `k` -- `expOfModulus m k` is
/// literally `Nat.size (m (meshLevelCount k))`, so the two sides match by
/// delta with nothing recomputed.
///
/// Then one [`declare_sup_seq_le_sup_on_thm`] under `add_le_add`.
fn declare_mesh_max_le_sup_on_add_thm(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = creal_ty(d, p);
    let func_ty = d.arrow(carrier, carrier);
    let nat_p = p.rat.int.nat;

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let hab_fv = d.fresh_fvar();
    let hab = d.kernel().fvar(hab_fv);
    let hab_ty = cle(d, p, a, b);
    let u_fv = d.fresh_fvar();
    let u = d.kernel().fvar(u_fv);
    let u_ty = d.const_app(p.uniformly_continuous_on, &[f, a, b]);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let dd_fv = d.fresh_fvar();
    let dd = d.kernel().fvar(dd_fv);

    // `size c + expOfModulus m k <= size c + trueExpOfModulus m k`, whose
    // right-hand side IS `supLevel F a b u k` by delta.
    let modulus = d.const_app(p.uc_modulus, &[f, a, b, u]);
    let na = cneg(d, p, a);
    let width = cadd(d, p, b, na);
    let c = d.const_app(p.bound, &[width]);
    let size_c = d.const_app(nat_p.size, &[c]);
    let exp_k = d.const_app(p.exp_of_modulus, &[modulus, k]);
    let te_k = d.const_app(p.true_exp_of_modulus, &[modulus, k]);
    let exp_le = d.lemma(p.exp_of_modulus_le_true_exp_of_modulus, &[modulus, k]);
    let hsize = d.lemma(nat_p.add_le_add_left, &[size_c, exp_k, te_k, exp_le]);

    let mlc_k = d.const_app(p.mesh_level_count, &[k]);
    let (_eps_rat, eps) = unit_frac_real(d, p, mlc_k);
    let level = d.const_app(p.sup_level, &[f, a, b, u, k]);
    let deep = NatOps::add(d, level, dd);

    let step = d.lemma(
        p.mesh_max_le_add_of_modulus,
        &[f, a, b, u, mlc_k, level, dd, hab, hsize],
    );

    let seq_k = d.const_app(p.sup_seq, &[f, a, b, u, k]);
    let target_real = d.const_app(p.sup_on, &[f, a, b, hab, u]);
    let top = d.lemma(p.sup_seq_le_sup_on, &[f, a, b, hab, u, k]);
    let refl_eps = d.lemma(p.le_refl, &[eps]);
    let widen = d.lemma(p.add_le_add, &[seq_k, target_real, eps, eps, top, refl_eps]);

    let lhs = d.const_app(p.mesh_max, &[f, a, b, deep]);
    let mid = cadd(d, p, seq_k, eps);
    let rhs = cadd(d, p, target_real, eps);
    let body = d.lemma(p.le_trans, &[lhs, mid, rhs, step, widen]);
    let concl = cle(d, p, lhs, rhs);

    let ty = {
        let out = d.pi_fv(dd_fv, nat, concl);
        let out = d.pi_fv(k_fv, nat, out);
        let out = d.pi_fv(u_fv, u_ty, out);
        let out = d.pi_fv(hab_fv, hab_ty, out);
        let out = d.pi_fv(b_fv, carrier, out);
        let out = d.pi_fv(a_fv, carrier, out);
        d.pi_fv(f_fv, func_ty, out)
    };
    let value = {
        let out = d.lam_fv(dd_fv, nat, body);
        let out = d.lam_fv(k_fv, nat, out);
        let out = d.lam_fv(u_fv, u_ty, out);
        let out = d.lam_fv(hab_fv, hab_ty, out);
        let out = d.lam_fv(b_fv, carrier, out);
        let out = d.lam_fv(a_fv, carrier, out);
        d.lam_fv(f_fv, func_ty, out)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.mesh_max_le_sup_on_add,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CReal.supOn_ub_at_fine_mesh_point : forall F a b (hab : le a b) u k dd i,
/// Nat.le i (meshLevelCount (Nat.add (supLevel F a b u k) dd)) ->
/// le (F (meshSamplePoint a (meshDelta a b (meshLevelCount (Nat.add (supLevel
/// F a b u k) dd))) i)) (add (supOn F a b hab u) (ofRat (Rat.natDivSucc 1
/// (meshLevelCount k))))` -- **the upper-bound law on a family of points that
/// can be made as fine as wanted, at an epsilon chosen independently.**
///
/// [`CRealPrelude::max_range_ub`](super::CRealPrelude::max_range_ub) then
/// [`declare_mesh_max_le_sup_on_add_thm`]. Strictly stronger than
/// [`declare_sup_on_ub_at_sup_seq_point_thm`], which is the `dd = 0` case with
/// the epsilon dropped: here the refinement depth `dd` is free, so the sampled
/// points are not confined to the schedule's own levels, while `k` still
/// controls the error independently of `dd`.
///
/// The remaining gap to the unrestricted law `forall x in [a, b], F x <= supOn`
/// is exactly the arbitrary point: see this module's header, and
/// [`declare_step_family_locate_thm`], which is the tool for it.
fn declare_sup_on_ub_at_fine_mesh_point_thm(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = creal_ty(d, p);
    let func_ty = d.arrow(carrier, carrier);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let hab_fv = d.fresh_fvar();
    let hab = d.kernel().fvar(hab_fv);
    let hab_ty = cle(d, p, a, b);
    let u_fv = d.fresh_fvar();
    let u = d.kernel().fvar(u_fv);
    let u_ty = d.const_app(p.uniformly_continuous_on, &[f, a, b]);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let dd_fv = d.fresh_fvar();
    let dd = d.kernel().fvar(dd_fv);
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);

    let level = d.const_app(p.sup_level, &[f, a, b, u, k]);
    let deep = NatOps::add(d, level, dd);
    let count = d.const_app(p.mesh_level_count, &[deep]);
    let delta = mesh_delta(d, p, a, b, count);
    let sampler = {
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let sp = mesh_sample_point(d, p, a, delta, j);
        let fx = d.apply(f, &[sp]);
        d.lam_fv(j_fv, nat, fx)
    };
    let point = mesh_sample_point(d, p, a, delta, i);
    let f_point = d.apply(f, &[point]);

    let mlc_k = d.const_app(p.mesh_level_count, &[k]);
    let (_eps_rat, eps) = unit_frac_real(d, p, mlc_k);
    let mesh_deep = d.const_app(p.mesh_max, &[f, a, b, deep]);
    let target_real = d.const_app(p.sup_on, &[f, a, b, hab, u]);
    let rhs = cadd(d, p, target_real, eps);

    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);
    let h_ty = d.le(i, count);

    let ub = d.lemma(p.max_range_ub, &[sampler, count, i, h]);
    let dom = d.lemma(p.mesh_max_le_sup_on_add, &[f, a, b, hab, u, k, dd]);
    let body = d.lemma(p.le_trans, &[f_point, mesh_deep, rhs, ub, dom]);
    let concl = cle(d, p, f_point, rhs);

    let ty = {
        let out = d.arrow(h_ty, concl);
        let out = d.pi_fv(i_fv, nat, out);
        let out = d.pi_fv(dd_fv, nat, out);
        let out = d.pi_fv(k_fv, nat, out);
        let out = d.pi_fv(u_fv, u_ty, out);
        let out = d.pi_fv(hab_fv, hab_ty, out);
        let out = d.pi_fv(b_fv, carrier, out);
        let out = d.pi_fv(a_fv, carrier, out);
        d.pi_fv(f_fv, func_ty, out)
    };
    let value = {
        let out = d.lam_fv(h_fv, h_ty, body);
        let out = d.lam_fv(i_fv, nat, out);
        let out = d.lam_fv(dd_fv, nat, out);
        let out = d.lam_fv(k_fv, nat, out);
        let out = d.lam_fv(u_fv, u_ty, out);
        let out = d.lam_fv(hab_fv, hab_ty, out);
        let out = d.lam_fv(b_fv, carrier, out);
        let out = d.lam_fv(a_fv, carrier, out);
        d.lam_fv(f_fv, func_ty, out)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.sup_on_ub_at_fine_mesh_point,
        uparams: vec![],
        ty,
        value,
    })
}

/// Land `CReal.meshMax_le_supOn_add` and `CReal.supOn_ub_at_fine_mesh_point`.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
pub(super) fn declare_sup_on_ub_at_fine_mesh_point(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    declare_mesh_max_le_sup_on_add_thm(d, p)?;
    declare_sup_on_ub_at_fine_mesh_point_thm(d, p)
}
// ---------------------------------------------------------------------------
// `CReal.supOn_ub` -- the upper-bound law at an ARBITRARY point of `[a, b]`
// ---------------------------------------------------------------------------

/// `Equiv y x` from `h : Equiv x y`.
fn esymm(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId, y: ExprId, h: ExprId) -> ExprId {
    d.lemma(p.equiv_symm, &[x, y, h])
}

/// Fold a list of `(next, Equiv current next)` steps into one `Equiv start
/// last`. Duplicated from `creal/monotone.rs`'s `pub(super) echain`, per this
/// development's re-derive-rather-than-widen convention.
fn echain(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    start: ExprId,
    steps: &[(ExprId, ExprId)],
) -> ExprId {
    let mut current = start;
    let mut proof = d.lemma(p.equiv_refl, &[start]);
    for &(next, step) in steps {
        proof = d.lemma(p.equiv_trans, &[start, current, next, proof, step]);
        current = next;
    }
    proof
}

/// `Equiv (add a (add b (neg a))) b` -- `a + (b - a) ~ b`. Duplicated from
/// `creal/monotone.rs`'s and `creal/integral.rs`'s private `add_sub_cancel`.
fn add_sub_cancel(d: &mut IntDev<'_>, p: CRealPrelude, a: ExprId, b: ExprId) -> ExprId {
    let na = cneg(d, p, a);
    let width = cadd(d, p, b, na);
    let start = cadd(d, p, a, width);

    let nab = cadd(d, p, na, b);
    let s1 = cadd(d, p, a, nab);
    let h1 = {
        let comm = d.lemma(p.add_comm, &[b, na]);
        let refl_a = d.lemma(p.equiv_refl, &[a]);
        d.lemma(p.add_congr, &[a, a, width, nab, refl_a, comm])
    };

    let ana = cadd(d, p, a, na);
    let s2 = cadd(d, p, ana, b);
    let h2 = {
        let assoc = d.lemma(p.add_assoc, &[a, na, b]);
        esymm(d, p, s2, s1, assoc)
    };

    let zero_c = d.kernel().const_(p.zero, vec![]);
    let s3 = cadd(d, p, zero_c, b);
    let h3 = {
        let hn = d.lemma(p.add_neg, &[a]);
        let refl_b = d.lemma(p.equiv_refl, &[b]);
        d.lemma(p.add_congr, &[ana, zero_c, b, b, hn, refl_b])
    };

    let s4 = cadd(d, p, b, zero_c);
    let h4 = d.lemma(p.add_comm, &[zero_c, b]);
    let h5 = d.lemma(p.add_zero, &[b]);

    echain(
        d,
        p,
        start,
        &[(s1, h1), (s2, h2), (s3, h3), (s4, h4), (b, h5)],
    )
}

/// `Equiv (ofNat Nat.zero) zero` -- duplicated from `creal/monotone.rs`'s
/// private `of_nat_zero_equiv_local`.
fn of_nat_zero_equiv(d: &mut IntDev<'_>, p: CRealPrelude) -> ExprId {
    let rat = p.rat;
    let zero_nat = d.num(0);
    let unit = d.const_app(rat.nat_div_succ, &[zero_nat, zero_nat]);
    let zero_rat = rzero(d, rat);
    let unit_eq_zero = d.lemma(rat.self_normalize, &[zero_rat]);
    let unit_embed = embed(d, p, unit);
    let refl_start = d.lemma(p.equiv_refl, &[unit_embed]);
    rat_eq_rewrite(d, unit, zero_rat, unit_eq_zero, refl_start, &|d, t| {
        let embedded = embed(d, p, t);
        cequiv(d, p, unit_embed, embedded)
    })
}

/// `Equiv (ofNat (Nat.succ Nat.zero)) one` -- duplicated from
/// `creal/supremum.rs`'s private `of_nat_one_equiv`.
fn of_nat_one_equiv(d: &mut IntDev<'_>, p: CRealPrelude) -> ExprId {
    let rat = p.rat;
    let one_nat = d.num(1);
    let zero_nat = d.num(0);
    let unit = d.const_app(rat.nat_div_succ, &[one_nat, zero_nat]);
    let one_rat = d.kernel().const_(rat.one, vec![]);
    let unit_eq_one = d.lemma(p.rat_unit_eq_one, &[]);
    let unit_embed = embed(d, p, unit);
    let refl_start = d.lemma(p.equiv_refl, &[unit_embed]);
    rat_eq_rewrite(d, unit, one_rat, unit_eq_one, refl_start, &|d, t| {
        let embedded = embed(d, p, t);
        cequiv(d, p, unit_embed, embedded)
    })
}

/// `Equiv (ofNat (Nat.succ m)) (add (ofNat m) one)` -- duplicated from
/// `creal/supremum.rs`'s private `of_nat_succ_equiv`.
///
/// `m` is the numerator on the LEFT in every `natDivSucc`/`Nat.add` pair built
/// here: `Nat.add m 1` iota-reduces (`Nat.add` recurses on its SECOND
/// argument) and `Nat.add 1 m` does not, for a symbolic `m`.
fn of_nat_succ_equiv(d: &mut IntDev<'_>, p: CRealPrelude, m: ExprId) -> ExprId {
    let rat = p.rat;
    let one_nat = d.num(1);
    let zero_nat = d.num(0);
    let one_c = d.kernel().const_(p.one, vec![]);

    let m_rat = d.const_app(rat.nat_div_succ, &[m, zero_nat]);
    let one_ratdiv = d.const_app(rat.nat_div_succ, &[one_nat, zero_nat]);
    let sum_rat = radd(d, m_rat, one_ratdiv);
    let succ_m = d.succ(m);
    let succ_rat = d.const_app(rat.nat_div_succ, &[succ_m, zero_nat]);
    let add_eq = d.lemma(rat.nat_div_succ_add, &[m, one_nat, zero_nat]);

    let of_nat_m = d.const_app(p.of_nat, &[m]);
    let of_nat_1 = d.const_app(p.of_nat, &[one_nat]);
    let of_nat_succ_m = d.const_app(p.of_nat, &[succ_m]);
    let add_of_nat_m_1 = cadd(d, p, of_nat_m, of_nat_1);

    let add_step = d.lemma(p.of_rat_add, &[m_rat, one_ratdiv]);
    let rewritten = rat_eq_rewrite(d, sum_rat, succ_rat, add_eq, add_step, &|d, t| {
        let embedded = embed(d, p, t);
        cequiv(d, p, add_of_nat_m_1, embedded)
    });
    let flipped = esymm(d, p, add_of_nat_m_1, of_nat_succ_m, rewritten);

    let one_eq = of_nat_one_equiv(d, p);
    let refl_m = d.lemma(p.equiv_refl, &[of_nat_m]);
    let congr_step = d.lemma(
        p.add_congr,
        &[of_nat_m, of_nat_m, of_nat_1, one_c, refl_m, one_eq],
    );
    let add_of_nat_m_one = cadd(d, p, of_nat_m, one_c);
    d.lemma(
        p.equiv_trans,
        &[
            of_nat_succ_m,
            add_of_nat_m_1,
            add_of_nat_m_one,
            flipped,
            congr_step,
        ],
    )
}

/// `Equiv (mul one x) x` -- `mul_comm` then `mul_one`. There is no
/// `CReal.one_mul`.
fn one_mul_equiv(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId) -> ExprId {
    let one_c = d.kernel().const_(p.one, vec![]);
    let lhs = cmul(d, p, one_c, x);
    let swapped = cmul(d, p, x, one_c);
    let comm = d.lemma(p.mul_comm, &[one_c, x]);
    let trim = d.lemma(p.mul_one, &[x]);
    d.lemma(p.equiv_trans, &[lhs, swapped, x, comm, trim])
}

/// `Equiv (meshSamplePoint a delta (Nat.succ n)) (add (meshSamplePoint a delta
/// n) delta)` -- the mesh advances by exactly one width per index step.
/// Duplicated from `creal/supremum.rs`'s private `sample_succ_equiv`.
fn sample_succ_equiv(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    a: ExprId,
    delta: ExprId,
    n: ExprId,
) -> ExprId {
    let one_c = d.kernel().const_(p.one, vec![]);
    let of_nat_n = d.const_app(p.of_nat, &[n]);
    let sn = d.succ(n);
    let of_nat_sn = d.const_app(p.of_nat, &[sn]);
    let sum_on = cadd(d, p, of_nat_n, one_c);

    let s1 = of_nat_succ_equiv(d, p, n);
    let refl_delta = d.lemma(p.equiv_refl, &[delta]);
    let lhs_mul = cmul(d, p, of_nat_sn, delta);
    let mid_mul = cmul(d, p, sum_on, delta);
    let m1 = d.lemma(
        p.mul_congr,
        &[of_nat_sn, sum_on, delta, delta, s1, refl_delta],
    );

    let m2 = right_distrib(d, p, of_nat_n, one_c, delta);
    let on_delta = cmul(d, p, of_nat_n, delta);
    let one_delta = cmul(d, p, one_c, delta);
    let split = cadd(d, p, on_delta, one_delta);

    let m3 = one_mul_equiv(d, p, delta);
    let refl_on_delta = d.lemma(p.equiv_refl, &[on_delta]);
    let m4 = d.lemma(
        p.add_congr,
        &[on_delta, on_delta, one_delta, delta, refl_on_delta, m3],
    );
    let trimmed = cadd(d, p, on_delta, delta);

    let chain1 = d.lemma(p.equiv_trans, &[lhs_mul, mid_mul, split, m1, m2]);
    let chain2 = d.lemma(p.equiv_trans, &[lhs_mul, split, trimmed, chain1, m4]);

    let refl_a = d.lemma(p.equiv_refl, &[a]);
    let lifted = d.lemma(p.add_congr, &[a, a, lhs_mul, trimmed, refl_a, chain2]);
    let sp_succ = cadd(d, p, a, lhs_mul);
    let nested = cadd(d, p, a, trimmed);

    let assoc = d.lemma(p.add_assoc, &[a, on_delta, delta]);
    let sp_n = cadd(d, p, a, on_delta);
    let flat = cadd(d, p, sp_n, delta);
    let assoc_symm = esymm(d, p, flat, nested, assoc);

    d.lemma(p.equiv_trans, &[sp_succ, nested, flat, lifted, assoc_symm])
}

/// `Equiv (meshSamplePoint a delta Nat.zero) a` -- the FIRST interface
/// identity `CReal.stepFamily_locate`'s mesh instantiation needs (`P 0 ~ a`).
/// `ofNat 0 ~ 0`, `0 * delta ~ 0` (through `mul_comm`, since there is no
/// `CReal.zero_mul`), then `add_zero`.
fn sample_zero_equiv(d: &mut IntDev<'_>, p: CRealPrelude, a: ExprId, delta: ExprId) -> ExprId {
    let zero_nat = d.num(0);
    let zero_c = d.kernel().const_(p.zero, vec![]);
    let of_nat_0 = d.const_app(p.of_nat, &[zero_nat]);
    let term = cmul(d, p, of_nat_0, delta);
    let zero_delta = cmul(d, p, zero_c, delta);
    let delta_zero = cmul(d, p, delta, zero_c);

    let zero_eq = of_nat_zero_equiv(d, p);
    let refl_delta = d.lemma(p.equiv_refl, &[delta]);
    let t1 = d.lemma(
        p.mul_congr,
        &[of_nat_0, zero_c, delta, delta, zero_eq, refl_delta],
    );
    let t2 = d.lemma(p.mul_comm, &[zero_c, delta]);
    let t3 = d.lemma(p.mul_zero, &[delta]);
    let term_zero = echain(
        d,
        p,
        term,
        &[(zero_delta, t1), (delta_zero, t2), (zero_c, t3)],
    );

    let refl_a = d.lemma(p.equiv_refl, &[a]);
    let lifted = d.lemma(p.add_congr, &[a, a, term, zero_c, refl_a, term_zero]);
    let start = cadd(d, p, a, term);
    let padded = cadd(d, p, a, zero_c);
    let trim = d.lemma(p.add_zero, &[a]);
    echain(d, p, start, &[(padded, lifted), (a, trim)])
}

/// `Equiv (add (meshSamplePoint a (meshDelta a b m) m) (meshDelta a b m)) b`
/// -- the THIRD interface identity (`P N + delta ~ b`): walking `m` mesh steps
/// from `a` and taking one more lands exactly on `b`.
///
/// [`sample_succ_equiv`] read backwards turns `P m + delta` into `P (succ m)`,
/// [`CRealPrelude::mesh_count_width`] collapses `(m+1) * delta` to the width
/// `b + (neg a)`, and [`add_sub_cancel`] folds `a + (b - a)` to `b`. The
/// composition itself is new: `creal/monotone.rs`'s
/// `subdivisionPoint_in_bounds` runs the same three steps but lands a `le`
/// rather than an `Equiv`, so nothing existing could be reused directly.
fn mesh_endpoint_equiv(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    a: ExprId,
    b: ExprId,
    m: ExprId,
) -> ExprId {
    let delta = mesh_delta(d, p, a, b, m);
    let point = mesh_sample_point(d, p, a, delta, m);
    let start = cadd(d, p, point, delta);

    let sm = d.succ(m);
    let next = mesh_sample_point(d, p, a, delta, sm);
    let step = sample_succ_equiv(d, p, a, delta, m);
    let s1 = esymm(d, p, next, start, step);

    let na = cneg(d, p, a);
    let width = cadd(d, p, b, na);
    let of_nat_sm = d.const_app(p.of_nat, &[sm]);
    let scaled = cmul(d, p, of_nat_sm, delta);
    let mw = d.lemma(p.mesh_count_width, &[width, m]);
    let refl_a = d.lemma(p.equiv_refl, &[a]);
    let s2 = d.lemma(p.add_congr, &[a, a, scaled, width, refl_a, mw]);
    let a_width = cadd(d, p, a, width);

    let s3 = add_sub_cancel(d, p, a, b);

    echain(d, p, start, &[(next, s1), (a_width, s2), (b, s3)])
}

/// `le zero (meshDelta a b m)`, given `hab : le a b` -- duplicated from
/// `creal/supremum.rs`'s private `mesh_delta_nonneg`.
fn mesh_delta_nonneg(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    a: ExprId,
    b: ExprId,
    m: ExprId,
    hab: ExprId,
) -> ExprId {
    let na = cneg(d, p, a);
    let width = cadd(d, p, b, na);
    let one_nat = d.num(1);
    let frac = d.const_app(p.rat.nat_div_succ, &[one_nat, m]);
    let frac_real = embed(d, p, frac);
    let zero_c = d.kernel().const_(p.zero, vec![]);

    let refl_na = d.lemma(p.le_refl, &[na]);
    let a_na = cadd(d, p, a, na);
    let shifted = d.lemma(p.add_le_add, &[a, b, na, na, hab, refl_na]);
    let hn = d.lemma(p.add_neg, &[a]);
    let refl_width = d.lemma(p.equiv_refl, &[width]);
    let width_nonneg = d.lemma(
        p.le_congr,
        &[a_na, zero_c, width, width, hn, refl_width, shifted],
    );

    let rzero_v = rzero(d, p.rat);
    let rle_v = d.lemma(p.rat.zero_le_nat_div_succ, &[one_nat, m]);
    let frac_nonneg = d.lemma(p.of_rat_le, &[rzero_v, frac, rle_v]);

    d.lemma(p.mul_nonneg, &[width, frac_real, width_nonneg, frac_nonneg])
}

/// `Eq Nat (Nat.mul 2 m) (Nat.add m m)` -- duplicated from
/// `creal/supremum.rs`'s private `nat_two_mul_eq_add`. `Nat.mul` recurses on
/// its SECOND argument, so `mul 2 m` does not iota-reduce for symbolic `m` and
/// this has to go through `Nat.succ_mul` plus `Nat.one_mul`.
fn nat_two_mul_eq_add(d: &mut IntDev<'_>, p: CRealPrelude, m: ExprId) -> ExprId {
    let nat_p = p.rat.int.nat;
    let one_v = d.num(1);
    let sm = d.lemma(nat_p.succ_mul, &[one_v, m]);
    let one_mul_m = d.lemma(nat_p.one_mul, &[m]);
    let one_m = NatOps::mul(d, one_v, m);
    let cong_add = NatOps::congr(d, one_m, m, one_mul_m, &|d, t| NatOps::add(d, t, m));
    let add_one_m_m = NatOps::add(d, one_m, m);
    let m_m = NatOps::add(d, m, m);
    let two_v = d.num(2);
    let two_m = NatOps::mul(d, two_v, m);
    NatOps::trans(d, two_m, add_one_m_m, m_m, sm, cong_add)
}

/// `Nat.le n (Nat.add k n)` -- duplicated from `creal/integral.rs`'s private
/// `nat_le_add_left`. The prelude has `le_add_right` (`Le n (add n k)`) and no
/// `le_add_left`, so this is that lemma transported across `Nat.add_comm`.
fn nat_le_add_left(d: &mut IntDev<'_>, p: CRealPrelude, k: ExprId, n: ExprId) -> ExprId {
    let nat_p = p.rat.int.nat;
    let h = d.lemma(nat_p.le_add_right, &[n, k]);
    let comm = d.lemma(nat_p.add_comm, &[n, k]);
    let n_plus_k = NatOps::add(d, n, k);
    let k_plus_n = NatOps::add(d, k, n);
    nat_rewrite_prop(d, n_plus_k, k_plus_n, comm, h, &|d, x| d.le(n, x))
}

/// `Nat.le n (Nat.succ (Nat.mul 2 n))` -- the doubling index
/// `Rat.natDivSucc_halve` demands is above `n` itself, so
/// `Rat.natDivSucc_antitone` applies to it.
fn nat_le_succ_two_mul(d: &mut IntDev<'_>, p: CRealPrelude, n: ExprId) -> ExprId {
    let nat_p = p.rat.int.nat;
    let two_v = d.num(2);
    let two_n = NatOps::mul(d, two_v, n);
    let n_n = NatOps::add(d, n, n);
    let two_eq = nat_two_mul_eq_add(d, p, n);
    let back = NatOps::symm(d, two_n, n_n, two_eq);
    let base = d.lemma(nat_p.le_add_right, &[n, n]);
    let lifted = nat_rewrite_prop(d, n_n, two_n, back, base, &|d, x| d.le(n, x));
    d.lemma(nat_p.le_succ_of_le, &[n, two_n, lifted])
}

/// `CReal.supOn_ub : forall F a b (hab : le a b) (u : UniformlyContinuousOn F
/// a b) (x : CReal), le a x -> le x b -> le (F x) (supOn F a b hab u)` --
/// **the upper-bound law at an ARBITRARY point, which is what makes `supOn` a
/// supremum rather than a limit of mesh maxima.**
///
/// With [`declare_sup_on_approx_lub_thm`] this is the pair that characterizes
/// `supOn`: it dominates every value of `F` on `[a, b]`, and it is approached
/// by them to any requested accuracy. Neither says a maximiser exists, and
/// [`CRealPrelude::evt_attained_max_decides_sign`] says none can be
/// constructed.
///
/// # The four steps, and where the margin comes from
///
/// `supLevel`'s own schedule has ZERO margin -- it is exactly fine enough for
/// the modulus at the corresponding accuracy, which is why
/// [`declare_sup_on_ub_at_sup_seq_point_thm`] is stated only at scheduled
/// levels. An off-mesh point needs strictly more, because `stepFamily_locate`
/// returns `|x - P i| <= delta + eps` where the schedule alone would pay for
/// `delta` and nothing else. The margin is bought in TWO independent places,
/// and neither is a scheduled level:
///
/// 1. **The level.** `j := supLevel F a b u kk + (Nat.size c + Nat.size
///    outer2)` -- an arbitrary level ABOVE a scheduled one, which
///    [`declare_mesh_max_le_sup_on_add_thm`] makes usable for one epsilon
///    because `mesh_max_le_add_of_modulus` is depth-uniform. The added summand
///    is chosen to be exactly
///    [`CRealPrelude::mesh_level_count_ge_of_size`]'s own threshold, so
///    `hsize` is `Nat.le dd (Nat.add level dd)` and needs no `Nat.le_dest`
///    (ADR-0710 predicted an `Exists` here; making `dd` concrete removes it).
/// 2. **The accuracy the mesh is asked for.** `outer2 := Nat.succ (2 *
///    outer)`, one HALVING finer than the modulus itself demands, so
///    `mesh_le_of_ge` reports `delta <= 1/(2*outer + 2)` and the locate
///    epsilon can be the same `1/(2*outer + 2)`. The two halves fuse to the
///    `1/(outer + 1)` `uc_spec` consumes, by `Rat.natDivSucc_add` then
///    `Rat.natDivSucc_halve`. Without this the sum `delta + eps` would exceed
///    the modulus budget and no amount of extra LEVEL would fix it.
///
/// The same halving trick runs a second time at the outer accuracy: `kk :=
/// Nat.succ (2 * e)` splits the final `1/(e+1)` between the uniform-continuity
/// transfer and the mesh-maximum gap.
///
/// # The three interface identities
///
/// [`CRealPrelude::step_family_locate`] is stated over the ORDER alone, so
/// instantiating it at the mesh costs exactly the three identities its own
/// documentation names: [`sample_zero_equiv`] (`P 0 ~ a`),
/// [`sample_succ_equiv`] (`P (i+1) ~ P i + delta`) and
/// [`mesh_endpoint_equiv`] (`P N + delta ~ b`). No ring algebra enters the
/// located index itself.
fn declare_sup_on_ub_thm(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = creal_ty(d, p);
    let func_ty = d.arrow(carrier, carrier);
    let nat_p = p.rat.int.nat;
    let rat = p.rat;
    let logic = p.rat.int.logic;

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let hab_fv = d.fresh_fvar();
    let hab = d.kernel().fvar(hab_fv);
    let hab_ty = cle(d, p, a, b);
    let u_fv = d.fresh_fvar();
    let u = d.kernel().fvar(u_fv);
    let u_ty = d.const_app(p.uniformly_continuous_on, &[f, a, b]);
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let hax_fv = d.fresh_fvar();
    let hax = d.kernel().fvar(hax_fv);
    let hax_ty = cle(d, p, a, x);
    let hxb_fv = d.fresh_fvar();
    let hxb = d.kernel().fvar(hxb_fv);
    let hxb_ty = cle(d, p, x, b);

    let zero_c = d.kernel().const_(p.zero, vec![]);
    let one_nat = d.num(1);
    let two_nat = d.num(2);
    let target_real = d.const_app(p.sup_on, &[f, a, b, hab, u]);
    let fx = d.apply(f, &[x]);

    // The rate-`1` accuracy family: `forall e, F x <= supOn + 1/(e+1)`.
    let rate = {
        let e_fv = d.fresh_fvar();
        let e = d.kernel().fvar(e_fv);

        // `kk := succ (2 * e)`, exactly `Rat.natDivSucc_halve`'s index shape:
        // the outer budget `1/(e+1)` splits into two halves of `1/(2e+2)`, one
        // for the uniform-continuity transfer and one for the mesh gap.
        let doubled_e = NatOps::mul(d, two_nat, e);
        let kk = d.succ(doubled_e);
        let (eps_rat, eps_real) = unit_frac_real(d, p, e);
        let (half_rat, half_real) = unit_frac_real(d, p, kk);

        // `outer` is the accuracy the witness itself demands at index `kk`;
        // `outer2 := succ (2 * outer)` is one halving finer, so that the mesh
        // width AND the locate epsilon can each be `1/(outer2 + 1)` and still
        // fuse to the `1/(outer + 1)` `uc_spec` consumes.
        let outer = d.const_app(p.uc_modulus, &[f, a, b, u, kk]);
        let doubled_outer = NatOps::mul(d, two_nat, outer);
        let outer2 = d.succ(doubled_outer);
        let (q_rat, q_real) = unit_frac_real(d, p, outer);
        let (w_rat, w_real) = unit_frac_real(d, p, outer2);

        // The level: a scheduled one plus exactly
        // `mesh_level_count_ge_of_size`'s own threshold, so both consumers are
        // satisfied by one choice.
        let na = cneg(d, p, a);
        let width = cadd(d, p, b, na);
        let c = d.const_app(p.bound, &[width]);
        let size_c = d.const_app(nat_p.size, &[c]);
        let size_outer2 = d.const_app(nat_p.size, &[outer2]);
        let dd = NatOps::add(d, size_c, size_outer2);
        let level = d.const_app(p.sup_level, &[f, a, b, u, kk]);
        let j = NatOps::add(d, level, dd);
        let mm = d.const_app(p.mesh_level_count, &[j]);
        let delta = mesh_delta(d, p, a, b, mm);

        // Step 1 -- `delta <= 1/(outer2 + 1)`.
        let hsize = nat_le_add_left(d, p, level, dd);
        let threshold_ok = d.lemma(p.mesh_level_count_ge_of_size, &[c, outer2, j, hsize]);
        let delta_le_w = d.lemma(p.mesh_le_of_ge, &[a, b, outer2, mm, hab, threshold_ok]);

        // `1/(outer2+1) + 1/(outer2+1) = 1/(outer+1)`, as a `Rat` equation.
        let w_plus_w_eq_q = {
            let fuse = d.lemma(rat.nat_div_succ_add, &[one_nat, one_nat, outer2]);
            let halve = d.lemma(rat.nat_div_succ_halve, &[outer]);
            let two_over = d.const_app(rat.nat_div_succ, &[two_nat, outer2]);
            let sum = radd(d, w_rat, w_rat);
            rtrans(d, sum, two_over, q_rat, fuse, halve)
        };
        // `1/(kk+1) + 1/(kk+1) = 1/(e+1)`.
        let half_plus_half_eq_eps = {
            let fuse = d.lemma(rat.nat_div_succ_add, &[one_nat, one_nat, kk]);
            let halve = d.lemma(rat.nat_div_succ_halve, &[e]);
            let two_over = d.const_app(rat.nat_div_succ, &[two_nat, kk]);
            let sum = radd(d, half_rat, half_rat);
            rtrans(d, sum, two_over, eps_rat, fuse, halve)
        };

        let goal = {
            let padded = cadd(d, p, target_real, eps_real);
            cle(d, p, fx, padded)
        };

        // Step 2 -- locate `x` in the mesh, over the ORDER alone.
        let fam = {
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let sp = mesh_sample_point(d, p, a, delta, i);
            d.lam_fv(i_fv, nat, sp)
        };
        let hw = mesh_delta_nonneg(d, p, a, b, mm, hab);
        let hpos = {
            let h11 = d.lemma(nat_p.le_refl_thm, &[one_nat]);
            let rpos = d.lemma(rat.nat_div_succ_pos, &[one_nat, outer2, h11]);
            d.lemma(p.of_rat_pos, &[w_rat, rpos])
        };
        let w_nonneg = d.lemma(p.le_of_lt, &[zero_c, w_real, hpos]);

        let hstep = {
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let si = d.succ(i);
            let psi = mesh_sample_point(d, p, a, delta, si);
            let pi = mesh_sample_point(d, p, a, delta, i);
            let shifted = cadd(d, p, pi, delta);
            let eq = sample_succ_equiv(d, p, a, delta, i);
            let back = esymm(d, p, psi, shifted, eq);
            let refl_shifted = d.lemma(p.equiv_refl, &[shifted]);
            let le_shifted = d.lemma(p.le_refl, &[shifted]);
            let body = d.lemma(
                p.le_congr,
                &[shifted, psi, shifted, shifted, back, refl_shifted, le_shifted],
            );
            d.lam_fv(i_fv, nat, body)
        };

        let p_zero = {
            let zero_nat = d.zero();
            mesh_sample_point(d, p, a, delta, zero_nat)
        };
        let h0 = {
            let eq = sample_zero_equiv(d, p, a, delta);
            let back = esymm(d, p, p_zero, a, eq);
            let refl_x_eq = d.lemma(p.equiv_refl, &[x]);
            d.lemma(p.le_congr, &[a, p_zero, x, x, back, refl_x_eq, hax])
        };

        let p_mm = mesh_sample_point(d, p, a, delta, mm);
        let p_mm_delta = cadd(d, p, p_mm, delta);
        let hn = {
            let endpoint = mesh_endpoint_equiv(d, p, a, b, mm);
            let back = esymm(d, p, p_mm_delta, b, endpoint);
            let refl_x_eq = d.lemma(p.equiv_refl, &[x]);
            let landed = d.lemma(p.le_congr, &[x, x, b, p_mm_delta, refl_x_eq, back, hxb]);
            let grown = shift_le_of_nonneg(d, p, p_mm_delta, w_real, w_nonneg);
            let padded = cadd(d, p, p_mm_delta, w_real);
            d.lemma(p.le_trans, &[x, p_mm_delta, padded, landed, grown])
        };

        let locate = d.lemma(
            p.step_family_locate,
            &[fam, delta, w_real, hw, hpos, hstep, mm, x, h0, hn],
        );

        let locate_pred = {
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let bound = d.le(i, mm);
            let point = mesh_sample_point(d, p, a, delta, i);
            let x_eps = cadd(d, p, x, w_real);
            let lower = cle(d, p, point, x_eps);
            let stepped = cadd(d, p, point, delta);
            let padded = cadd(d, p, stepped, w_real);
            let upper = cle(d, p, x, padded);
            let inner = d.and(lower, upper);
            let body = d.and(bound, inner);
            d.lam_fv(i_fv, nat, body)
        };

        let minor = {
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let hp_fv = d.fresh_fvar();
            let hp = d.kernel().fvar(hp_fv);

            let point = mesh_sample_point(d, p, a, delta, i);
            let bound_ty = d.le(i, mm);
            let x_eps = cadd(d, p, x, w_real);
            let lower_ty = cle(d, p, point, x_eps);
            let stepped = cadd(d, p, point, delta);
            let padded = cadd(d, p, stepped, w_real);
            let upper_ty = cle(d, p, x, padded);
            let inner_ty = d.and(lower_ty, upper_ty);
            let hp_ty = d.and(bound_ty, inner_ty);

            let hi = d.and_left(bound_ty, inner_ty, hp);
            let hinner = d.and_right(bound_ty, inner_ty, hp);
            let hlo = d.and_left(lower_ty, upper_ty, hinner);
            let hhi = d.and_right(lower_ty, upper_ty, hinner);

            // Step 3 -- `|x - P i| <= 1/(outer + 1)`, the modulus budget, with
            // the locate epsilon absorbed by the extra halving.
            let refl_point = d.lemma(p.le_refl, &[point]);
            let refl_w = d.lemma(p.le_refl, &[w_real]);
            let inner_widen = d.lemma(
                p.add_le_add,
                &[point, point, delta, w_real, refl_point, delta_le_w],
            );
            let point_w = cadd(d, p, point, w_real);
            let outer_widen = d.lemma(
                p.add_le_add,
                &[stepped, point_w, w_real, w_real, inner_widen, refl_w],
            );
            let point_w_w = cadd(d, p, point_w, w_real);
            let chained = d.lemma(p.le_trans, &[x, padded, point_w_w, hhi, outer_widen]);

            // `(P i + w) + w ~ P i + (w + w) ~ P i + 1/(outer+1)`.
            let assoc = d.lemma(p.add_assoc, &[point, w_real, w_real]);
            let ww = cadd(d, p, w_real, w_real);
            let point_ww = cadd(d, p, point, ww);
            let sum_rat = radd(d, w_rat, w_rat);
            let sum_real = embed(d, p, sum_rat);
            let sum_embed = d.lemma(p.of_rat_add, &[w_rat, w_rat]);
            let rewrite_sum = {
                let start = d.lemma(p.equiv_refl, &[sum_real]);
                rat_eq_rewrite(d, sum_rat, q_rat, w_plus_w_eq_q, start, &|d, t| {
                    let emb = embed(d, p, t);
                    cequiv(d, p, sum_real, emb)
                })
            };
            let ww_to_q = d.lemma(p.equiv_trans, &[ww, sum_real, q_real, sum_embed, rewrite_sum]);
            let refl_point_eq = d.lemma(p.equiv_refl, &[point]);
            let tail = d.lemma(
                p.add_congr,
                &[point, point, ww, q_real, refl_point_eq, ww_to_q],
            );
            let point_q = cadd(d, p, point, q_real);
            let whole_eq = d.lemma(
                p.equiv_trans,
                &[point_w_w, point_ww, point_q, assoc, tail],
            );
            let refl_x_eq = d.lemma(p.equiv_refl, &[x]);
            let up = d.lemma(
                p.le_congr,
                &[x, x, point_w_w, point_q, refl_x_eq, whole_eq, chained],
            );

            // The other side: `P i <= x + w <= x + 1/(outer+1)`.
            let houter_le = nat_le_succ_two_mul(d, p, outer);
            let w_le_q = d.lemma(rat.nat_div_succ_antitone, &[outer, outer2, houter_le]);
            let lift = d.lemma(p.of_rat_le, &[w_rat, q_rat, w_le_q]);
            let refl_x_le = d.lemma(p.le_refl, &[x]);
            let widen = d.lemma(
                p.add_le_add,
                &[x, x, w_real, q_real, refl_x_le, lift],
            );
            let x_q = cadd(d, p, x, q_real);
            let down = d.lemma(p.le_trans, &[point, x_eps, x_q, hlo, widen]);

            let closeness = d.lemma(p.abs_le_of_two_sided, &[x, point, q_rat, up, down]);

            // Step 4 -- `uc_spec`, then the fine-mesh upper bound.
            let hlt = d.lemma(nat_p.lt_succ_of_le, &[i, mm, hi]);
            let rng = d.const_app(p.riemann_sample_in_bounds, &[a, b, mm, i, hab, hlt]);
            let plo_ty = cle(d, p, a, point);
            let phi_ty = cle(d, p, point, b);
            let hplo = d.const_app(logic.and_left, &[plo_ty, phi_ty, rng]);
            let hphi = d.const_app(logic.and_right, &[plo_ty, phi_ty, rng]);

            let spec = d.const_app(
                p.uc_spec,
                &[f, a, b, u, kk, x, point, hax, hxb, hplo, hphi, closeness],
            );
            let f_point = d.apply(f, &[point]);
            let transfer = d.lemma(p.le_add_of_abs_sub_le, &[fx, f_point, half_rat, spec]);
            let f_point_half = cadd(d, p, f_point, half_real);

            // `F (P i) <= supOn + 1/2^kk <= supOn + 1/(kk+1)`.
            let fine = d.lemma(
                p.sup_on_ub_at_fine_mesh_point,
                &[f, a, b, hab, u, kk, dd, i, hi],
            );
            let mlc_kk = d.const_app(p.mesh_level_count, &[kk]);
            let (geom_rat, geom_real) = unit_frac_real(d, p, mlc_kk);
            let geom_le_half = {
                let hk = d.lemma(p.le_mesh_level_count, &[kk]);
                d.lemma(rat.nat_div_succ_antitone, &[kk, mlc_kk, hk])
            };
            let geom_lift = d.lemma(p.of_rat_le, &[geom_rat, half_rat, geom_le_half]);
            let refl_target = d.lemma(p.le_refl, &[target_real]);
            let geom_widen = d.lemma(
                p.add_le_add,
                &[
                    target_real,
                    target_real,
                    geom_real,
                    half_real,
                    refl_target,
                    geom_lift,
                ],
            );
            let target_geom = cadd(d, p, target_real, geom_real);
            let target_half = cadd(d, p, target_real, half_real);
            let fine_half = d.lemma(
                p.le_trans,
                &[f_point, target_geom, target_half, fine, geom_widen],
            );

            // `F x <= F (P i) + 1/(kk+1) <= (supOn + 1/(kk+1)) + 1/(kk+1)`.
            let refl_half = d.lemma(p.le_refl, &[half_real]);
            let grow = d.lemma(
                p.add_le_add,
                &[f_point, target_half, half_real, half_real, fine_half, refl_half],
            );
            let doubled = cadd(d, p, target_half, half_real);
            let stacked = d.lemma(
                p.le_trans,
                &[fx, f_point_half, doubled, transfer, grow],
            );

            // `(supOn + h) + h ~ supOn + (h + h) ~ supOn + 1/(e+1)`.
            let assoc2 = d.lemma(p.add_assoc, &[target_real, half_real, half_real]);
            let hh = cadd(d, p, half_real, half_real);
            let target_hh = cadd(d, p, target_real, hh);
            let sum2_rat = radd(d, half_rat, half_rat);
            let sum2_real = embed(d, p, sum2_rat);
            let sum2_embed = d.lemma(p.of_rat_add, &[half_rat, half_rat]);
            let rewrite_sum2 = {
                let start = d.lemma(p.equiv_refl, &[sum2_real]);
                rat_eq_rewrite(d, sum2_rat, eps_rat, half_plus_half_eq_eps, start, &|d, t| {
                    let emb = embed(d, p, t);
                    cequiv(d, p, sum2_real, emb)
                })
            };
            let hh_to_eps = d.lemma(
                p.equiv_trans,
                &[hh, sum2_real, eps_real, sum2_embed, rewrite_sum2],
            );
            let refl_target_eq = d.lemma(p.equiv_refl, &[target_real]);
            let tail2 = d.lemma(
                p.add_congr,
                &[target_real, target_real, hh, eps_real, refl_target_eq, hh_to_eps],
            );
            let target_eps = cadd(d, p, target_real, eps_real);
            let whole_eq2 = d.lemma(
                p.equiv_trans,
                &[doubled, target_hh, target_eps, assoc2, tail2],
            );
            let refl_fx = d.lemma(p.equiv_refl, &[fx]);
            let body = d.lemma(
                p.le_congr,
                &[fx, fx, doubled, target_eps, refl_fx, whole_eq2, stacked],
            );

            let inner = d.lam_fv(hp_fv, hp_ty, body);
            d.lam_fv(i_fv, nat, inner)
        };

        let per_e = exists_elim(d, locate_pred, goal, locate, minor);
        d.lam_fv(e_fv, nat, per_e)
    };

    let body = d.lemma(p.le_of_forall_le_add_rate, &[one_nat, fx, target_real, rate]);
    let concl = cle(d, p, fx, target_real);

    let ty = {
        let out = d.arrow(hxb_ty, concl);
        let out = d.arrow(hax_ty, out);
        let out = d.pi_fv(x_fv, carrier, out);
        let out = d.pi_fv(u_fv, u_ty, out);
        let out = d.pi_fv(hab_fv, hab_ty, out);
        let out = d.pi_fv(b_fv, carrier, out);
        let out = d.pi_fv(a_fv, carrier, out);
        d.pi_fv(f_fv, func_ty, out)
    };
    let value = {
        let out = d.lam_fv(hxb_fv, hxb_ty, body);
        let out = d.lam_fv(hax_fv, hax_ty, out);
        let out = d.lam_fv(x_fv, carrier, out);
        let out = d.lam_fv(u_fv, u_ty, out);
        let out = d.lam_fv(hab_fv, hab_ty, out);
        let out = d.lam_fv(b_fv, carrier, out);
        let out = d.lam_fv(a_fv, carrier, out);
        d.lam_fv(f_fv, func_ty, out)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.sup_on_ub,
        uparams: vec![],
        ty,
        value,
    })
}

/// Land `CReal.supOn_ub`.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
pub(super) fn declare_sup_on_ub(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    declare_sup_on_ub_thm(d, p)
}


#[cfg(test)]
mod sup_laws_tests {
    use super::*;
    use crate::Declaration;

    /// **Mandatory concrete instantiation, two positives and two negative
    /// controls**, on the two declarations of this file that can be
    /// instantiated cheaply.
    ///
    /// `CReal.supOn_approx_lub` and the three theorems around it are
    /// deliberately NOT instantiated concretely here, and that is a
    /// considered choice rather than an omission: every one of them mentions
    /// `CReal.supOn`, whose `Definition` embeds a `regular_of_scaled_cauchy`
    /// construction, so instantiating it at concrete arguments is exactly the
    /// shape `CLAUDE.md` records as pathological (a control that runs for
    /// minutes and gigabytes is worse than no control). What covers them
    /// instead is `creal_tests::every_creal_declaration_is_checked_and_axiom_free`,
    /// which reads the ENVIRONMENT rather than a list and asserts every
    /// declaration this file adds is a `Theorem` with an empty axiom
    /// footprint, plus `creal_prelude_builds`, which is what actually runs
    /// the kernel over the proof terms.
    ///
    /// The two checked here need none of that machinery:
    ///
    /// 1. `stepFamily_locate` at the constant family `P i := 0`, `w := 0`,
    ///    `eps := 1`, `n := 0`, `t := 1`. The control transposes the first
    ///    conjunct's `le` — ONE swap, not two large terms — giving
    ///    `1 + 1 <= 0`, which is false.
    /// 2. `maxRange_attained_approx` at `f i := 0`, `n := 0`, `e := 0` (so
    ///    the slack is `natDivSucc 1 0`, i.e. `1`). The control transposes the
    ///    estimate, giving `0 + 1 <= 0`.
    ///
    /// Both controls are checked in the two directions this repository's
    /// guidance demands: not vacuous (the mutated predicate is asserted not
    /// `def_eq` to the real one) and not inverted (the mutated statement is
    /// genuinely false at the chosen instance, as the comments record).
    #[test]
    fn sup_laws_concrete_and_negative_controls() {
        crate::on_a_deep_stack(sup_laws_concrete_and_negative_controls_body);
    }

    fn sup_laws_concrete_and_negative_controls_body() {
        let mut kernel = crate::Kernel::new();
        let p = crate::build_creal_prelude(&mut kernel).expect("CReal prelude must build");
        let mut d = IntDev::new(&mut kernel, p.rat.int);
        let anon = d.kernel().anon();
        let nat = d.nat_ty();
        let one_level = d.level_one();
        let logic = p.rat.int.logic;

        let zero_c = d.kernel().const_(p.zero, vec![]);
        let one_c = d.kernel().const_(p.one, vec![]);
        let zero_n = d.zero();

        // The constant family `fun _ : Nat => 0`, shared by both cases.
        let fam = {
            let i_fv = d.fresh_fvar();
            d.lam_fv(i_fv, nat, zero_c)
        };

        // --- 1. stepFamily_locate ------------------------------------------
        //
        // `0 <= 0` and `0 < 1` are the two order hypotheses, both closed
        // terms; the step hypothesis is `0 <= 0 + 0`.
        let hw = d.lemma(p.le_refl, &[zero_c]);
        let hpos = d.lemma(p.zero_lt_one, &[]);

        let sum00 = cadd(&mut d, p, zero_c, zero_c);
        let trim0 = d.lemma(p.add_zero, &[zero_c]);
        let hstep = {
            let i_fv = d.fresh_fvar();
            let back = d.lemma(p.equiv_symm, &[sum00, zero_c, trim0]);
            let refl_z = d.lemma(p.equiv_refl, &[zero_c]);
            let le_z = d.lemma(p.le_refl, &[zero_c]);
            let body = d.lemma(
                p.le_congr,
                &[zero_c, zero_c, zero_c, sum00, refl_z, back, le_z],
            );
            d.lam_fv(i_fv, nat, body)
        };

        // `le (P 0) t`, i.e. `0 <= 1`.
        let h0 = d.lemma(p.le_of_lt, &[zero_c, one_c, hpos]);

        // `le t ((P 0 + w) + eps)`, i.e. `1 <= (0 + 0) + 1`, by rewriting the
        // right-hand side down to `1`.
        let sum001 = cadd(&mut d, p, sum00, one_c);
        let zero_plus_one = cadd(&mut d, p, zero_c, one_c);
        let one_plus_zero = cadd(&mut d, p, one_c, zero_c);
        let hn = {
            let refl_one = d.lemma(p.equiv_refl, &[one_c]);
            let collapse_left =
                d.lemma(p.add_congr, &[sum00, zero_c, one_c, one_c, trim0, refl_one]);
            let comm = d.lemma(p.add_comm, &[zero_c, one_c]);
            let trim1 = d.lemma(p.add_zero, &[one_c]);
            let step2 = d.lemma(
                p.equiv_trans,
                &[zero_plus_one, one_plus_zero, one_c, comm, trim1],
            );
            let whole = d.lemma(
                p.equiv_trans,
                &[sum001, zero_plus_one, one_c, collapse_left, step2],
            );
            let back = d.lemma(p.equiv_symm, &[sum001, one_c, whole]);
            let refl_one2 = d.lemma(p.equiv_refl, &[one_c]);
            let le_one = d.lemma(p.le_refl, &[one_c]);
            d.lemma(
                p.le_congr,
                &[one_c, one_c, one_c, sum001, refl_one2, back, le_one],
            )
        };

        let locate = d.lemma(
            p.step_family_locate,
            &[fam, zero_c, one_c, hw, hpos, hstep, zero_n, one_c, h0, hn],
        );

        // `fun i => Nat.le i 0 /\ (0 <= 1 + 1 /\ 1 <= (0 + 0) + 1)`, and the
        // control with the FIRST conjunct's `le` transposed.
        let locate_pred = |d: &mut IntDev<'_>, flip: bool| -> ExprId {
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let bound = d.le(i, zero_n);
            let t_eps = cadd(d, p, one_c, one_c);
            let lower = if flip {
                cle(d, p, t_eps, zero_c)
            } else {
                cle(d, p, zero_c, t_eps)
            };
            let upper = cle(d, p, one_c, sum001);
            let inner = d.and(lower, upper);
            let body = d.and(bound, inner);
            d.lam_fv(i_fv, nat, body)
        };
        let pred_ok = locate_pred(&mut d, false);
        let pred_bad = locate_pred(&mut d, true);
        assert!(
            !d.kernel().def_eq(pred_ok, pred_bad),
            "negative control must not be vacuous: transposing `0 <= 1 + 1` \
             must change the predicate"
        );

        let exists_const = d.kernel().const_(logic.exists_, vec![one_level]);
        let ty_ok = d.apply(exists_const, &[nat, pred_ok]);
        let name_ok = d.kernel().name_str(anon, "__stepFamilyLocateOk");
        let res_ok = d.kernel().add_declaration(Declaration::Theorem {
            name: name_ok,
            uparams: vec![],
            ty: ty_ok,
            value: locate,
        });
        assert!(
            res_ok.is_ok(),
            "stepFamily_locate at the constant family P i := 0, w := 0, \
             eps := 1, n := 0, t := 1 must locate t: {:?}",
            res_ok.err()
        );

        let ty_bad = d.apply(exists_const, &[nat, pred_bad]);
        let name_bad = d.kernel().name_str(anon, "__stepFamilyLocateBad");
        let res_bad = d.kernel().add_declaration(Declaration::Theorem {
            name: name_bad,
            uparams: vec![],
            ty: ty_bad,
            value: locate,
        });
        assert!(
            res_bad.is_err(),
            "negative control must be REJECTED: the same proof term cannot \
             prove the transposed first conjunct `1 + 1 <= 0`"
        );

        // --- 2. maxRange_attained_approx -----------------------------------
        //
        // At `e := 0` the slack is `natDivSucc 1 0`, which is `1`, so the
        // estimate reads `maxRange f 0 <= f i + 1`, i.e. `0 <= 0 + 1`.
        let attained = d.lemma(p.max_range_attained_approx, &[fam, zero_n, zero_n]);
        let one_nat = d.num(1);
        let slack_rat = d.const_app(p.rat.nat_div_succ, &[one_nat, zero_n]);
        let slack = embed(&mut d, p, slack_rat);

        let attained_pred = |d: &mut IntDev<'_>, flip: bool| -> ExprId {
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let bound = d.le(i, zero_n);
            let padded = cadd(d, p, zero_c, slack);
            let mr = d.const_app(p.max_range, &[fam, zero_n]);
            let est = if flip {
                cle(d, p, padded, mr)
            } else {
                cle(d, p, mr, padded)
            };
            let body = d.and(bound, est);
            d.lam_fv(i_fv, nat, body)
        };
        let apred_ok = attained_pred(&mut d, false);
        let apred_bad = attained_pred(&mut d, true);
        assert!(
            !d.kernel().def_eq(apred_ok, apred_bad),
            "negative control must not be vacuous: transposing the estimate \
             must change the predicate"
        );

        let aty_ok = d.apply(exists_const, &[nat, apred_ok]);
        let aname_ok = d.kernel().name_str(anon, "__maxRangeAttainedOk");
        let ares_ok = d.kernel().add_declaration(Declaration::Theorem {
            name: aname_ok,
            uparams: vec![],
            ty: aty_ok,
            value: attained,
        });
        assert!(
            ares_ok.is_ok(),
            "maxRange_attained_approx at f i := 0, n := 0, e := 0 must give \
             `maxRange f 0 <= f 0 + 1`: {:?}",
            ares_ok.err()
        );

        let aty_bad = d.apply(exists_const, &[nat, apred_bad]);
        let aname_bad = d.kernel().name_str(anon, "__maxRangeAttainedBad");
        let ares_bad = d.kernel().add_declaration(Declaration::Theorem {
            name: aname_bad,
            uparams: vec![],
            ty: aty_bad,
            value: attained,
        });
        assert!(
            ares_bad.is_err(),
            "negative control must be REJECTED: the same proof term cannot \
             prove the transposed estimate `0 + 1 <= maxRange f 0`, i.e. \
             `1 <= 0`"
        );
    }
}
