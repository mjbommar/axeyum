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

use super::{CRealPrelude, and_intro, cadd, cle, creal_ty, embed};
use crate::KernelError;
use crate::env::Declaration;
use crate::expr::ExprId;
use crate::int_prelude::ops::{IntDev, exists_elim};
use crate::nat_prelude::NatOps;
use crate::rat_prelude::ops::{radd, rat_eq_rewrite, rtrans};

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
                &[padded_zero, fsj, padded_eps, padded_eps, trim, refl_rhs, raw],
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
                    f_point, f_point, inner_sum, eps_real, refl_point, inner_to_eps,
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
                &[seq_m, seq_m, doubled, padded_eps, refl_seq_m, whole_eq, step2],
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
