//! **`CReal.riemannSum`** — the first integral in this kernel: a finite
//! left-endpoint Riemann sum over `[a, b]` with `Nat.succ m` equal
//! subintervals, built directly on [`super::series`]'s `CReal.sumRange`.
//!
//! ## Why this is a plain `Definition`, not a carrier like `HasDerivativeOn`
//!
//! `derivative.rs`'s `HasDerivativeOn` needs a `Type`-valued carrier because
//! its modulus is genuinely *chosen* data attached to an otherwise-`Prop`
//! obligation (see that file's own module documentation). A Riemann sum has
//! no such data to carry: for a fixed `f`, `a`, `b` and subinterval count, the
//! sum is one fully-determined `CReal`, computed the same way `CReal.sumRange`
//! itself is — so it is a `Definition` built directly out of `add`, `neg`,
//! `mul`, `ofRat`, `ofNat` and `sumRange`, with no `Prop` anywhere in sight.
//!
//! ## The subinterval count, and why division needed no positivity witness
//!
//! `Δ = (b − a)/n` needs `n ≠ 0`. `CReal.inv` ([`super::inverse`]) exists but
//! takes a `PosBound` witness as an explicit argument — exactly the
//! "positivity witness makes the definition awkward" trap the task briefing
//! warned about, and it *would* be awkward here: threading a proof of
//! `0 < ofNat n` through a **finite**, totally ordinary definition just to
//! divide by a natural number is the wrong tool.
//!
//! It is also unnecessary. `n` is a `Nat`, not a `CReal`, so `1/n` is a
//! **rational** number regardless of `a`/`b`, and `Rat.natDivSucc 1 j := 1/(j+1)`
//! ([`archimedean.rs`](super::archimedean)) is already total in `j`. Taking the
//! subinterval count as `Nat.succ m` — i.e. parametrising `riemannSum` by `m`
//! and reading `n := m + 1` — makes `n ≠ 0` true *by construction* rather than
//! a side condition, and `Δ := (b − a) · ofRat (Rat.natDivSucc 1 m)` is then
//! an ordinary total product, no `CReal.inv`, no `PosBound`, no case split.
//! This is the same trick [`derivative.rs`](super::derivative)'s
//! `hasDerivative_smul` already uses for a *different* division (`|c| ≤ k+1`
//! read as `natDivSucc (Nat.succ k) 0`).
//!
//! ## The sample point: LEFT endpoint
//!
//! `riemannSum f a b m` samples `f` at `a + i·Δ` for `i = 0, …, m` — the
//! **left** endpoint of each subinterval. Left was chosen over the midpoint
//! for exactly the reason the briefing flagged as the trade-off: midpoint
//! gives tighter error bounds for a later convergence proof, but it needs an
//! extra `Δ/2` term in the sample-point arithmetic for no benefit to *this*
//! slice (no error bound is proved here at all — only linearity,
//! monotonicity and the exact constant-function computation). Left endpoint
//! is `a + i·Δ` with no further arithmetic, and it is what makes the mandatory
//! computation test (`riemannSum (fun _ => one) zero one 0`, single
//! subinterval, sample point `zero`) land on the obvious index-`0` case.
//!
//! ## What is proved here
//!
//! - **`riemannSum`** itself.
//! - **`riemannSum_add`**: `riemannSum (f+g) ~ riemannSum f + riemannSum g`,
//!   via [`super::series::CRealPrelude::sum_range_congr`] against
//!   [`right_distrib`] (distributing `Δ` into each term) then
//!   [`super::series::CRealPrelude::sum_range_add`].
//! - **`mul_riemannSum`**: `riemannSum (c·f) ~ c · riemannSum f`, via the same
//!   `sum_range_congr` shape against `mul_assoc` (re-associating `(c·f(x))·Δ`
//!   to `c·(f(x)·Δ)`) then
//!   [`super::series::CRealPrelude::mul_sum_range`].
//! - **`riemannSum_le`**: monotonicity, `le a b → (∀ z, le (f z) (g z)) →
//!   le (riemannSum f a b m) (riemannSum g a b m)`. The hypothesis is
//!   **global** (`∀ z`, not restricted to `[a, b]`). `le a b` is still
//!   genuinely used: it is exactly what makes `Δ ≥ 0`, which
//!   [`CRealPrelude::mul_le_mul_of_nonneg_left`] needs to multiply the
//!   pointwise hypothesis through by `Δ` without reversing it.
//! - **`ofNat_le`**: `Nat.le i j → CReal.le (ofNat i) (ofNat j)` — `CReal.ofNat`
//!   is monotone, via `Nat.le_dest` plus
//!   `RatPrelude::nat_div_succ_le_add_left` lifted across
//!   [`CRealPrelude::of_rat_le`]. Independently reusable; nothing else in the
//!   prelude had it.
//! - **`riemannSum_sample_in_bounds`**: `le a b → i < succ m → a ≤ a + i·Δ ≤
//!   b` — every LEFT-endpoint sample point lies in `[a, b]`. The piece
//!   `riemannSum_le`'s own doc used to flag as missing: nonneg-ness of the
//!   lower half ([`shift_le_of_nonneg`], generalizing
//!   [`CRealPrelude::le_add_of_nonneg`] off the rational embedding) and
//!   `ofNat_le` composed with `mul_le_mul_of_nonneg_left` plus the exact
//!   identity `n·Δ ~ (b−a)` ([`mesh_times_count_eq_width`], reusing
//!   [`mesh_inverse_identity`]) for the upper half.
//! - **`riemannSum_le_on`**: `riemannSum_le` with the pointwise hypothesis
//!   RESTRICTED to `[a, b]` (`∀ z, le a z → le z b → le (f z) (g z)`), via
//!   `riemannSum_sample_in_bounds`. `riemannSum_le` itself is **unchanged** —
//!   both theorems exist, stated exactly as their own doc comments say.
//!
//! - **`riemannSum_const`**: `riemannSum (fun _ => c) a b m ~ c · (b − a)`,
//!   exactly, for every `m` — the theorem that says the definition is right
//!   (a constant function's integral is base times height, with no error
//!   term, whatever the subinterval count). Two independent pieces:
//!
//!   1. [`riemann_sum_const_core`]: `sumRange (fun _ => w) (succ m) ~ mul
//!      (ofNat (succ m)) w`, a plain sum-of-a-constant induction on `m`. The
//!      base case needs `ofNat 1 ~ one` ([`of_nat_one_equiv_local`]); the
//!      step needs `ofNat (succ k) ~ add (ofNat k) one`
//!      ([`of_nat_succ_equiv_local`]) plus [`right_distrib`]. Both `of_nat_*`
//!      helpers are local restatements of `derivative.rs`'s private
//!      `of_nat_one_equiv`/`of_nat_succ_equiv` (that file is out of scope for
//!      this slice, so this module cannot call them, only rebuild the same
//!      two short proofs).
//!   2. [`mesh_inverse_identity`]: `mul (ofNat (Nat.succ m)) (embed
//!      (Rat.natDivSucc 1 m)) ~ one` — exactly the `(m+1)/(m+1) = 1` identity
//!      `RatPrelude::inv_nat_div_succ`'s own proof derives in passing
//!      (chaining `nat_div_succ_mul`, `nat_div_succ_scale` and the
//!      already-proved `CReal.ratUnitEqOne` in place of a fresh
//!      `self_normalize` call — see
//!      `rat_prelude/field.rs::declare_inv_nat_div_succ` and
//!      [`nat_div_succ_inverse_pair_eq_one`]), lifted from `Rat` to `CReal`
//!      by `CReal.ofRat_mul`.
//!
//!   [`declare_riemann_sum_const`] combines the two: the summand
//!   `f(a+i·Δ)·Δ` is `c·Δ` regardless of `i` since `f` is constant (an
//!   ordinary beta reduction the kernel's defeq check performs on its own,
//!   so [`riemann_sum_const_core`] is stated and used directly against
//!   `w := mul c delta` with no bridging lemma needed), piece 1 collapses the
//!   sum to `mul (ofNat n) (mul c delta)`, and an eight-step
//!   associativity/commutativity rewrite (using `mul_assoc`/`mul_comm`/
//!   `mul_congr`) exposes `mul (ofNat n) frac_real` next to the width so
//!   piece 2 cancels it, leaving `mul c width` via `mul_one`.
//!
//! **Not attempted**: additivity over an interval split (`riemannSum f a c`
//! vs. `riemannSum f a b` plus `riemannSum f b c`), which is false for a
//! FIXED subinterval count unless the two partitions happen to line up — see
//! `declare_integral`'s caller for that check.

use super::ring_helpers::right_distrib;
use super::{
    CRealPrelude, DERIVED_HEIGHT, and_intro, cadd, creal_ty, div_succ, embed, equiv, halves,
    sample, within,
};
use crate::KernelError;
use crate::env::{Declaration, ReducibilityHint};
use crate::expr::ExprId;
use crate::int_prelude::ops::{IntDev, exists_elim};
use crate::nat_prelude::NatOps;
use crate::rat_prelude::ops::{
    nat_eq_to_rat, nat_rewrite_prop, normalize, one_le_succ, radd, rat_eq_rewrite, rat_ty, rchain,
    req, rle, rmul, rneg, rone, rtrans, rzero,
};

/// Delta height for `CReal.riemannSum`: above `CReal.sumRange`
/// (`DERIVED_HEIGHT + 41`) and `CReal.ofNat` (`DERIVED_HEIGHT + 14`), the two
/// definitions it is built from.
const RIEMANN_HEIGHT: u16 = DERIVED_HEIGHT + 45;

/// Admit `CReal.riemannSum`, `CReal.riemannSum_add`, `CReal.mul_riemannSum`
/// and `CReal.riemannSum_le`. See the module documentation for what is and
/// is not covered.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` from a `Theorem` here means
/// the kernel **refused** a proof, not that a script gave up.
pub(super) fn declare_integral(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    declare_of_nat_le(d, p)?;
    declare_riemann_sum(d, p)?;
    declare_riemann_sum_add(d, p)?;
    declare_mul_riemann_sum(d, p)?;
    declare_riemann_sum_le(d, p)?;
    declare_riemann_sample_in_bounds(d, p)?;
    declare_riemann_sum_le_on(d, p)?;
    declare_riemann_sum_const(d, p)?;
    declare_mesh_le_of_ge(d, p)
}

// --- shared term builders ----------------------------------------------------

/// `CReal -> CReal`.
fn fn_ty(d: &mut IntDev<'_>, p: CRealPrelude) -> ExprId {
    let carrier = creal_ty(d, p);
    d.arrow(carrier, carrier)
}

fn cneg(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId) -> ExprId {
    d.const_app(p.neg, &[x])
}

fn cmul(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId, y: ExprId) -> ExprId {
    d.const_app(p.mul, &[x, y])
}

fn cle(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId, y: ExprId) -> ExprId {
    d.const_app(p.le, &[x, y])
}

fn czero(d: &mut IntDev<'_>, p: CRealPrelude) -> ExprId {
    d.kernel().const_(p.zero, vec![])
}

/// `add b (neg a)` — the interval width `b − a`.
fn width_of(d: &mut IntDev<'_>, p: CRealPrelude, a: ExprId, b: ExprId) -> ExprId {
    let na = cneg(d, p, a);
    cadd(d, p, b, na)
}

/// `mul (add b (neg a)) (ofRat (Rat.natDivSucc 1 m))` — the mesh
/// `Δ = (b − a)/(m + 1)`. Total in `m`: see the module documentation for why
/// no `CReal.inv`/`PosBound` is needed.
fn delta_of(d: &mut IntDev<'_>, p: CRealPrelude, a: ExprId, b: ExprId, m: ExprId) -> ExprId {
    let width = width_of(d, p, a, b);
    let one_nat = d.num(1);
    let frac = d.const_app(p.rat.nat_div_succ, &[one_nat, m]);
    let frac_real = embed(d, p, frac);
    cmul(d, p, width, frac_real)
}

/// `add a (mul (ofNat i) delta)` — the `i`-th LEFT sample point `a + i·Δ`.
fn sample_point(
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

/// `fun i => mul (f (sample_point a delta i)) delta` — the `i`-th Riemann
/// term, `f(a + i·Δ)·Δ`. Built as its own helper (rather than inlined at
/// each call site) so every occurrence — inside `riemannSum`'s own
/// definition and inside every theorem about it — is the *same* term,
/// minimizing what the kernel's defeq check has to bridge.
fn summand_fn(d: &mut IntDev<'_>, p: CRealPrelude, f: ExprId, a: ExprId, delta: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let sp = sample_point(d, p, a, delta, i);
    let fx = d.apply(f, &[sp]);
    let term = cmul(d, p, fx, delta);
    d.lam_fv(i_fv, nat, term)
}

/// `CReal.riemannSum f a b m`.
fn rsum(d: &mut IntDev<'_>, p: CRealPrelude, f: ExprId, a: ExprId, b: ExprId, m: ExprId) -> ExprId {
    d.const_app(p.riemann_sum, &[f, a, b, m])
}

// --- `CReal.ofNat_le` -----------------------------------------------------

/// `CReal.ofNat_le : ∀ i j : Nat, Nat.le i j → CReal.le (ofNat i) (ofNat j)`
/// — `CReal.ofNat` is monotone.
///
/// `CReal.ofNat n := CReal.ofRat (Rat.natDivSucc n 0)` ([`super::archimedean`]),
/// so this is [`RatPrelude::nat_div_succ_le_add_left`]
/// (`∀ a e j, Rat.le (natDivSucc a j) (natDivSucc (a+e) j)` — monotone in the
/// numerator, stated additively so no `Nat`-subtraction ever appears) lifted
/// across [`CRealPrelude::of_rat_le`], then transported from the existential
/// witness `Nat.le_dest` supplies (`i + k = j`) up to the actual bound `j`.
///
/// The same idiom as `series.rs`'s `sumRange_tail_within_le`: `Nat.le_dest i j
/// hij : Exists (fun k => Eq Nat (add i k) j)`; applying
/// `nat_div_succ_le_add_left` at `(i, k, 0)` gives exactly this theorem's
/// conclusion *shape*, but indexed at `add i k` rather than `j`, and one
/// `Nat`-equality transport ([`nat_rewrite_prop`]) carries it over.
fn declare_of_nat_le(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let nat_add = d.prelude().add;
    let nat_le_dest = d.prelude().le_dest;

    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let j_fv = d.fresh_fvar();
    let j = d.kernel().fvar(j_fv);

    let hle_ty = d.le(i, j);
    let hle_fv = d.fresh_fvar();
    let hle = d.kernel().fvar(hle_fv);

    let of_nat_i = d.const_app(p.of_nat, &[i]);
    // target_at(x) := CReal.le (ofNat i) (ofNat x) -- this theorem's
    // conclusion at x := j, and `nat_div_succ_le_add_left`'s shape at
    // x := add i k.
    let target_at = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let of_nat_x = d.const_app(p.of_nat, &[x]);
        cle(d, p, of_nat_i, of_nat_x)
    };
    let target = target_at(d, j);

    // pred := λ k, Eq Nat (add i k) j.
    let pred = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let sum = d.const_app(nat_add, &[i, k]);
        let body = d.eq(sum, j);
        d.lam_fv(k_fv, nat, body)
    };

    let represented = d.const_app(nat_le_dest, &[i, j, hle]);

    let minor = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let i_plus_k = d.const_app(nat_add, &[i, k]);
        let e_ty = d.eq(i_plus_k, j);
        let e_fv = d.fresh_fvar();
        let e = d.kernel().fvar(e_fv);

        // body_at_ik : CReal.le (embed (natDivSucc i 0)) (embed (natDivSucc
        // (add i k) 0)) -- defeq target_at(add i k), since `ofNat n` unfolds
        // to `embed (natDivSucc n 0)`.
        let zero_nat = d.num(0);
        let rat_i = d.const_app(p.rat.nat_div_succ, &[i, zero_nat]);
        let rat_ik = d.const_app(p.rat.nat_div_succ, &[i_plus_k, zero_nat]);
        let rat_le = d.lemma(p.rat.nat_div_succ_le_add_left, &[i, k, zero_nat]);
        let body_at_ik = d.lemma(p.of_rat_le, &[rat_i, rat_ik, rat_le]);

        let rewritten = nat_rewrite_prop(d, i_plus_k, j, e, body_at_ik, &target_at);
        let with_e = d.lam_fv(e_fv, e_ty, rewritten);
        d.lam_fv(k_fv, nat, with_e)
    };

    let proof_body = exists_elim(d, pred, target, represented, minor);

    let ty = {
        let after_hle = d.arrow(hle_ty, target);
        let over_j = d.pi_fv(j_fv, nat, after_hle);
        d.pi_fv(i_fv, nat, over_j)
    };
    let value = {
        let with_hle = d.lam_fv(hle_fv, hle_ty, proof_body);
        let over_j = d.lam_fv(j_fv, nat, with_hle);
        d.lam_fv(i_fv, nat, over_j)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.of_nat_le,
        uparams: vec![],
        ty,
        value,
    })
}

// --- the declarations ---------------------------------------------------------

/// `CReal.riemannSum (f : CReal -> CReal) (a b : CReal) (m : Nat) : CReal :=
///   CReal.sumRange (fun i => mul (f (add a (mul (ofNat i) delta))) delta)
///     (Nat.succ m)`, where `delta = mul (add b (neg a)) (ofRat (natDivSucc 1 m))`.
fn declare_riemann_sum(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let f_ty = fn_ty(d, p);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);

    let delta = delta_of(d, p, a, b, m);
    let n = d.succ(m);
    let summand = summand_fn(d, p, f, a, delta);
    let body = d.const_app(p.sum_range, &[summand, n]);

    let value = {
        let with_m = d.lam_fv(m_fv, nat, body);
        let with_b = d.lam_fv(b_fv, carrier, with_m);
        let with_a = d.lam_fv(a_fv, carrier, with_b);
        d.lam_fv(f_fv, f_ty, with_a)
    };
    let ty = {
        let over_m = d.arrow(nat, carrier);
        let over_b = d.arrow(carrier, over_m);
        let over_a = d.arrow(carrier, over_b);
        d.arrow(f_ty, over_a)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.riemann_sum,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(RIEMANN_HEIGHT),
    })
}

/// `CReal.riemannSum_add : ∀ f g a b m,
/// Equiv (riemannSum (fun r => add (f r) (g r)) a b m)
///       (add (riemannSum f a b m) (riemannSum g a b m))`.
///
/// Route: `sum_range_congr` against [`right_distrib`] turns the combined
/// summand `(f(x)+g(x))·Δ` into `f(x)·Δ + g(x)·Δ` pointwise, then
/// `sum_range_add` splits the sum.
fn declare_riemann_sum_add(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let f_ty = fn_ty(d, p);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);

    let combined = {
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);
        let fr = d.apply(f, &[r]);
        let gr = d.apply(g, &[r]);
        let body = cadd(d, p, fr, gr);
        d.lam_fv(r_fv, carrier, body)
    };

    let delta = delta_of(d, p, a, b, m);
    let n = d.succ(m);

    let f_summand_combined = summand_fn(d, p, combined, a, delta);
    let f_summand_plain = summand_fn(d, p, f, a, delta);
    let g_summand_plain = summand_fn(d, p, g, a, delta);

    // f_summand_split i := add (mul (f si) delta) (mul (g si) delta).
    let f_summand_split = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let sp = sample_point(d, p, a, delta, i);
        let fx = d.apply(f, &[sp]);
        let gx = d.apply(g, &[sp]);
        let ft = cmul(d, p, fx, delta);
        let gt = cmul(d, p, gx, delta);
        let body = cadd(d, p, ft, gt);
        d.lam_fv(i_fv, nat, body)
    };

    // h1 : Equiv (sumRange f_summand_combined n) (sumRange f_summand_split n).
    let h1 = {
        let pointwise = {
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let sp = sample_point(d, p, a, delta, i);
            let fx = d.apply(f, &[sp]);
            let gx = d.apply(g, &[sp]);
            let step = right_distrib(d, p, fx, gx, delta);
            d.lam_fv(i_fv, nat, step)
        };
        d.lemma(
            p.sum_range_congr,
            &[f_summand_combined, f_summand_split, n, pointwise],
        )
    };

    // h2 : Equiv (sumRange f_summand_split n)
    //            (add (sumRange f_summand_plain n) (sumRange g_summand_plain n)).
    let h2 = d.lemma(p.sum_range_add, &[f_summand_plain, g_summand_plain, n]);

    let lhs = d.const_app(p.sum_range, &[f_summand_combined, n]);
    let mid = d.const_app(p.sum_range, &[f_summand_split, n]);
    let rhs = {
        let sf = d.const_app(p.sum_range, &[f_summand_plain, n]);
        let sg = d.const_app(p.sum_range, &[g_summand_plain, n]);
        cadd(d, p, sf, sg)
    };

    let proof = d.lemma(p.equiv_trans, &[lhs, mid, rhs, h1, h2]);

    let ty = {
        let lhs_rs = rsum(d, p, combined, a, b, m);
        let rf = rsum(d, p, f, a, b, m);
        let rg = rsum(d, p, g, a, b, m);
        let rhs_rs = cadd(d, p, rf, rg);
        equiv(d, p, lhs_rs, rhs_rs)
    };

    let ty_full = {
        let over_m = d.pi_fv(m_fv, nat, ty);
        let over_b = d.pi_fv(b_fv, carrier, over_m);
        let over_a = d.pi_fv(a_fv, carrier, over_b);
        let over_g = d.pi_fv(g_fv, f_ty, over_a);
        d.pi_fv(f_fv, f_ty, over_g)
    };
    let value_full = {
        let over_m = d.lam_fv(m_fv, nat, proof);
        let over_b = d.lam_fv(b_fv, carrier, over_m);
        let over_a = d.lam_fv(a_fv, carrier, over_b);
        let over_g = d.lam_fv(g_fv, f_ty, over_a);
        d.lam_fv(f_fv, f_ty, over_g)
    };

    d.kernel().add_declaration(Declaration::Theorem {
        name: p.riemann_sum_add,
        uparams: vec![],
        ty: ty_full,
        value: value_full,
    })
}

/// `CReal.mul_riemannSum : ∀ c f a b m,
/// Equiv (riemannSum (fun r => mul c (f r)) a b m) (mul c (riemannSum f a b m))`.
///
/// Route: `sum_range_congr` against `mul_assoc` re-associates `(c·f(x))·Δ` to
/// `c·(f(x)·Δ)` pointwise, then `mul_sum_range` pulls `c` out of the sum.
fn declare_mul_riemann_sum(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let f_ty = fn_ty(d, p);

    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);

    let combined = {
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);
        let fr = d.apply(f, &[r]);
        let body = cmul(d, p, c, fr);
        d.lam_fv(r_fv, carrier, body)
    };

    let delta = delta_of(d, p, a, b, m);
    let n = d.succ(m);

    let f_summand_combined = summand_fn(d, p, combined, a, delta);
    let f_summand_plain = summand_fn(d, p, f, a, delta);

    // w_summand i := mul c (f_summand_plain i) = mul c (mul (f si) delta).
    let w_summand = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let sp = sample_point(d, p, a, delta, i);
        let fx = d.apply(f, &[sp]);
        let inner = cmul(d, p, fx, delta);
        let body = cmul(d, p, c, inner);
        d.lam_fv(i_fv, nat, body)
    };

    // h1 : Equiv (sumRange f_summand_combined n) (sumRange w_summand n),
    // pointwise via mul_assoc: (c*fx)*delta ~ c*(fx*delta).
    let h1 = {
        let pointwise = {
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let sp = sample_point(d, p, a, delta, i);
            let fx = d.apply(f, &[sp]);
            let step = d.lemma(p.mul_assoc, &[c, fx, delta]);
            d.lam_fv(i_fv, nat, step)
        };
        d.lemma(
            p.sum_range_congr,
            &[f_summand_combined, w_summand, n, pointwise],
        )
    };

    // h_ms : Equiv (mul c (sumRange f_summand_plain n)) (sumRange w_summand n).
    let h_ms = d.lemma(p.mul_sum_range, &[c, f_summand_plain, n]);

    let sum_plain = d.const_app(p.sum_range, &[f_summand_plain, n]);
    let mul_c_sum = cmul(d, p, c, sum_plain);
    let sum_w = d.const_app(p.sum_range, &[w_summand, n]);

    // h2 : Equiv (sumRange w_summand n) (mul c (sumRange f_summand_plain n)).
    let h2 = d.lemma(p.equiv_symm, &[mul_c_sum, sum_w, h_ms]);

    let lhs = d.const_app(p.sum_range, &[f_summand_combined, n]);
    let proof = d.lemma(p.equiv_trans, &[lhs, sum_w, mul_c_sum, h1, h2]);

    let ty = {
        let lhs_rs = rsum(d, p, combined, a, b, m);
        let rf = rsum(d, p, f, a, b, m);
        let rhs_rs = cmul(d, p, c, rf);
        equiv(d, p, lhs_rs, rhs_rs)
    };

    let ty_full = {
        let over_m = d.pi_fv(m_fv, nat, ty);
        let over_b = d.pi_fv(b_fv, carrier, over_m);
        let over_a = d.pi_fv(a_fv, carrier, over_b);
        let over_f = d.pi_fv(f_fv, f_ty, over_a);
        d.pi_fv(c_fv, carrier, over_f)
    };
    let value_full = {
        let over_m = d.lam_fv(m_fv, nat, proof);
        let over_b = d.lam_fv(b_fv, carrier, over_m);
        let over_a = d.lam_fv(a_fv, carrier, over_b);
        let over_f = d.lam_fv(f_fv, f_ty, over_a);
        d.lam_fv(c_fv, carrier, over_f)
    };

    d.kernel().add_declaration(Declaration::Theorem {
        name: p.mul_riemann_sum,
        uparams: vec![],
        ty: ty_full,
        value: value_full,
    })
}

/// `delta := mul (width_of a b) (embed (natDivSucc 1 m))` together with a
/// proof `le zero delta`, given `hab : le a b`. Shared by
/// [`declare_riemann_sum_le`] and [`declare_riemann_sample_in_bounds`]: `le a
/// b` is what makes the width `b − a` nonneg (via `add_le_add` shifted by
/// `neg a`), and the mesh factor `1/(m+1)` is unconditionally nonneg, so
/// `mul_nonneg` closes it.
fn delta_nonneg_of(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    a: ExprId,
    b: ExprId,
    m: ExprId,
    hab: ExprId,
) -> (ExprId, ExprId) {
    let width = width_of(d, p, a, b);
    let one_nat = d.num(1);
    let frac = d.const_app(p.rat.nat_div_succ, &[one_nat, m]);
    let frac_real = embed(d, p, frac);
    let delta = cmul(d, p, width, frac_real);
    let zero_c = czero(d, p);

    // width_nonneg : le zero (add b (neg a)), from `le a b`.
    let width_nonneg = {
        let na = cneg(d, p, a);
        let refl_na = d.lemma(p.le_refl, &[na]);
        let a_na = cadd(d, p, a, na);
        let b_na = cadd(d, p, b, na);
        let shifted = d.lemma(p.add_le_add, &[a, b, na, na, hab, refl_na]);
        // shifted : le (add a (neg a)) (add b (neg a))
        let hn = d.lemma(p.add_neg, &[a]); // Equiv (add a (neg a)) zero
        let refl_bna = d.lemma(p.equiv_refl, &[b_na]);
        d.lemma(
            p.le_congr,
            &[a_na, zero_c, b_na, b_na, hn, refl_bna, shifted],
        )
    };

    // frac_nonneg : le zero (ofRat (natDivSucc 1 m)).
    let frac_nonneg = {
        let rzero = d.kernel().const_(p.rat.zero, vec![]);
        let rle = d.lemma(p.rat.zero_le_nat_div_succ, &[one_nat, m]);
        d.lemma(p.of_rat_le, &[rzero, frac, rle])
    };

    // delta_nonneg : le zero delta.
    let delta_nonneg = d.lemma(p.mul_nonneg, &[width, frac_real, width_nonneg, frac_nonneg]);
    (delta, delta_nonneg)
}

/// `CReal.riemannSum_le : ∀ f g a b m, le a b → (∀ z, le (f z) (g z)) →
/// le (riemannSum f a b m) (riemannSum g a b m)`.
///
/// `le a b` is what makes `Δ ≥ 0` (via `mul_nonneg` on the width `b − a` and
/// the always-nonnegative rational mesh factor), which
/// `mul_le_mul_of_nonneg_left` needs to multiply the pointwise hypothesis
/// through by `Δ` without reversing it. See the module documentation for why
/// the pointwise hypothesis is global rather than restricted to `[a, b]`.
fn declare_riemann_sum_le(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let f_ty = fn_ty(d, p);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);

    let hab_ty = cle(d, p, a, b);
    let hab_fv = d.fresh_fvar();
    let hab = d.kernel().fvar(hab_fv);

    let hfg_ty = {
        let z_fv = d.fresh_fvar();
        let z = d.kernel().fvar(z_fv);
        let fz = d.apply(f, &[z]);
        let gz = d.apply(g, &[z]);
        let body = cle(d, p, fz, gz);
        d.pi_fv(z_fv, carrier, body)
    };
    let hfg_fv = d.fresh_fvar();
    let hfg = d.kernel().fvar(hfg_fv);

    let (delta, delta_nonneg) = delta_nonneg_of(d, p, a, b, m, hab);
    let n = d.succ(m);

    let f_summand = summand_fn(d, p, f, a, delta);
    let g_summand = summand_fn(d, p, g, a, delta);

    let bounded_pointwise = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let sp = sample_point(d, p, a, delta, i);
        let fz = d.apply(f, &[sp]);
        let gz = d.apply(g, &[sp]);
        let h_fg = d.apply(hfg, &[sp]); // le (f sp) (g sp)

        let step = d.lemma(
            p.mul_le_mul_of_nonneg_left,
            &[delta, fz, gz, delta_nonneg, h_fg],
        );
        // step : le (mul delta fz) (mul delta gz)
        let comm_f = d.lemma(p.mul_comm, &[delta, fz]); // Equiv (mul delta fz) (mul fz delta)
        let comm_g = d.lemma(p.mul_comm, &[delta, gz]);
        let df = cmul(d, p, delta, fz);
        let dg = cmul(d, p, delta, gz);
        let fd = cmul(d, p, fz, delta);
        let gd = cmul(d, p, gz, delta);
        let transported = d.lemma(p.le_congr, &[df, fd, dg, gd, comm_f, comm_g, step]);
        // transported : le (mul fz delta) (mul gz delta) = le (f_summand i) (g_summand i)

        let lt_hyp_ty = d.lt(i, n);
        let lt_fv = d.fresh_fvar();
        let with_lt = d.lam_fv(lt_fv, lt_hyp_ty, transported);
        d.lam_fv(i_fv, nat, with_lt)
    };

    let result = d.lemma(
        p.sum_range_le,
        &[f_summand, g_summand, n, bounded_pointwise],
    );

    let ty = {
        let lhs_rs = rsum(d, p, f, a, b, m);
        let rhs_rs = rsum(d, p, g, a, b, m);
        cle(d, p, lhs_rs, rhs_rs)
    };
    let ty_inner = {
        let after_hfg = d.arrow(hfg_ty, ty);
        d.arrow(hab_ty, after_hfg)
    };
    let ty_full = {
        let over_m = d.pi_fv(m_fv, nat, ty_inner);
        let over_b = d.pi_fv(b_fv, carrier, over_m);
        let over_a = d.pi_fv(a_fv, carrier, over_b);
        let over_g = d.pi_fv(g_fv, f_ty, over_a);
        d.pi_fv(f_fv, f_ty, over_g)
    };
    let value_inner = {
        let with_hfg = d.lam_fv(hfg_fv, hfg_ty, result);
        d.lam_fv(hab_fv, hab_ty, with_hfg)
    };
    let value_full = {
        let over_m = d.lam_fv(m_fv, nat, value_inner);
        let over_b = d.lam_fv(b_fv, carrier, over_m);
        let over_a = d.lam_fv(a_fv, carrier, over_b);
        let over_g = d.lam_fv(g_fv, f_ty, over_a);
        d.lam_fv(f_fv, f_ty, over_g)
    };

    d.kernel().add_declaration(Declaration::Theorem {
        name: p.riemann_sum_le,
        uparams: vec![],
        ty: ty_full,
        value: value_full,
    })
}

// --- sample points lie in `[a, b]` ------------------------------------------

/// `CReal.le zero (CReal.ofNat n)` — `CReal.ofNat` is nonneg. Directly from
/// `Rat.zero_le_natDivSucc` lifted across [`CRealPrelude::of_rat_le`] — the
/// same route [`delta_nonneg_of`]'s `frac_nonneg` uses for the mesh factor.
fn zero_le_of_nat(d: &mut IntDev<'_>, p: CRealPrelude, n: ExprId) -> ExprId {
    let zero_nat = d.num(0);
    let rat_n = d.const_app(p.rat.nat_div_succ, &[n, zero_nat]);
    let rzero = d.kernel().const_(p.rat.zero, vec![]);
    let rle = d.lemma(p.rat.zero_le_nat_div_succ, &[n, zero_nat]);
    d.lemma(p.of_rat_le, &[rzero, rat_n, rle])
    // : CReal.le (embed rzero) (embed rat_n) -- defeq CReal.le zero (ofNat n)
}

/// `CReal.le x (add x w)`, given `hw : CReal.le zero w` — for a general
/// nonneg ADDEND `w : CReal`. No public `CReal` prelude lemma gives this: only
/// [`CRealPrelude::le_add_of_nonneg`] does, and only for `w := embed q` at a
/// nonneg RATIONAL `q`. Built directly from `add_le_add`/`add_zero`/`le_congr`
/// — the same three steps `le_add_of_nonneg`'s own proof runs, generalized off
/// the rational embedding.
fn shift_le_of_nonneg(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    x: ExprId,
    w: ExprId,
    hw: ExprId,
) -> ExprId {
    let zero_c = czero(d, p);
    let refl_x = d.lemma(p.le_refl, &[x]);
    let grown = d.lemma(p.add_le_add, &[x, x, zero_c, w, refl_x, hw]);
    // grown : le (add x zero) (add x w)
    let padded = cadd(d, p, x, zero_c);
    let target = cadd(d, p, x, w);
    let trim = d.lemma(p.add_zero, &[x]); // Equiv (add x zero) x
    let refl_target = d.lemma(p.equiv_refl, &[target]);
    d.lemma(
        p.le_congr,
        &[padded, x, target, target, trim, refl_target, grown],
    )
    // : le x (add x w)
}

/// `Equiv (add a (add b (neg a))) b` — `a + (b − a) ~ b`, the ring identity
/// [`add_sub_cancel`]'s callers need to fold `a + width` back down to `b`.
fn add_sub_cancel(d: &mut IntDev<'_>, p: CRealPrelude, a: ExprId, b: ExprId) -> ExprId {
    let na = cneg(d, p, a);
    let width = cadd(d, p, b, na); // b + (-a)
    let start = cadd(d, p, a, width); // a + (b + (-a))

    let nab = cadd(d, p, na, b); // (-a) + b
    let s1 = cadd(d, p, a, nab); // a + ((-a) + b)
    let h1 = {
        let comm = d.lemma(p.add_comm, &[b, na]); // Equiv width nab
        let refl_a = d.lemma(p.equiv_refl, &[a]);
        d.lemma(p.add_congr, &[a, a, width, nab, refl_a, comm])
        // : Equiv start s1
    };

    let ana = cadd(d, p, a, na); // a + (-a)
    let s2 = cadd(d, p, ana, b); // (a + (-a)) + b
    let h2 = {
        let assoc = d.lemma(p.add_assoc, &[a, na, b]);
        // assoc : Equiv (add (add a na) b) (add a (add na b)) = Equiv s2 s1
        d.lemma(p.equiv_symm, &[s2, s1, assoc]) // : Equiv s1 s2
    };

    let zero_c = czero(d, p);
    let s3 = cadd(d, p, zero_c, b); // zero + b
    let h3 = {
        let hn = d.lemma(p.add_neg, &[a]); // Equiv ana zero
        let refl_b = d.lemma(p.equiv_refl, &[b]);
        d.lemma(p.add_congr, &[ana, zero_c, b, b, hn, refl_b])
        // : Equiv s2 s3
    };

    let s4 = cadd(d, p, b, zero_c); // b + zero
    let h4 = d.lemma(p.add_comm, &[zero_c, b]); // Equiv s3 s4

    let h5 = d.lemma(p.add_zero, &[b]); // Equiv s4 b

    echain(
        d,
        p,
        start,
        &[(s1, h1), (s2, h2), (s3, h3), (s4, h4), (b, h5)],
    )
}

/// `Equiv (add x (neg (add x (neg y)))) y` — `x − (x − y) ~ y`, the mirror
/// cancellation [`declare_two_sided_of_abs_sub_le`]'s second (`neg_le_abs`)
/// branch needs. Derived from [`add_sub_cancel`]`(y, x) : Equiv (add y diff)
/// x` (`diff := add x (neg y)`) by adding `neg diff` to BOTH sides of that
/// equation and simplifying the left with `add_assoc`/`add_neg`/`add_zero` —
/// `diff` itself is never unfolded, so this needs no `neg`-distributes-over-
/// `add` law.
fn diff_cancel_left(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId, y: ExprId) -> ExprId {
    let ny = cneg(d, p, y);
    let diff = cadd(d, p, x, ny); // x + (-y)
    let ndiff = cneg(d, p, diff);

    let cancel_yx = add_sub_cancel(d, p, y, x); // Equiv (add y diff) x
    let y_diff = cadd(d, p, y, diff);
    let start = cadd(d, p, y_diff, ndiff); // (y + diff) + (-diff)
    let target = cadd(d, p, x, ndiff); // x + (-diff)

    let h1 = {
        // Equiv start target, by congr-ing `cancel_yx` into the left slot.
        let refl_ndiff = d.lemma(p.equiv_refl, &[ndiff]);
        d.lemma(
            p.add_congr,
            &[y_diff, x, ndiff, ndiff, cancel_yx, refl_ndiff],
        )
    };

    let diff_ndiff = cadd(d, p, diff, ndiff); // diff + (-diff)
    let s1 = cadd(d, p, y, diff_ndiff); // y + (diff + (-diff))
    let h_assoc = d.lemma(p.add_assoc, &[y, diff, ndiff]); // Equiv start s1

    let zero_c = czero(d, p);
    let s2 = cadd(d, p, y, zero_c); // y + zero
    let h_s1_s2 = {
        let hn = d.lemma(p.add_neg, &[diff]); // Equiv (add diff ndiff) zero
        let refl_y = d.lemma(p.equiv_refl, &[y]);
        d.lemma(p.add_congr, &[y, y, diff_ndiff, zero_c, refl_y, hn])
    };

    let h_s2_y = d.lemma(p.add_zero, &[y]); // Equiv s2 y

    let start_eq_y = echain(d, p, start, &[(s1, h_assoc), (s2, h_s1_s2), (y, h_s2_y)]);
    // start_eq_y : Equiv start y

    let symm_h1 = d.lemma(p.equiv_symm, &[start, target, h1]); // Equiv target start

    echain(d, p, target, &[(start, symm_h1), (y, start_eq_y)])
    // : Equiv target y
}

/// `Equiv (mul (ofNat (Nat.succ m)) (mul width frac)) width`, where `frac :=
/// embed (Rat.natDivSucc 1 m)` — `n · Δ ~ (b − a)` when `Δ := width · frac`,
/// exactly (no error term), for every `m`. The width-only case of
/// [`riemann_sum_const_rearrange`]'s own algebra (that one additionally
/// carries a constant factor `c`), reusing [`mesh_inverse_identity`].
fn mesh_times_count_eq_width(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    width: ExprId,
    frac: ExprId,
    m: ExprId,
) -> ExprId {
    let on = {
        let successor = d.succ(m);
        d.const_app(p.of_nat, &[successor])
    };
    let delta = cmul(d, p, width, frac);
    let a_start = cmul(d, p, on, delta); // mul on (mul width frac)

    let on_width = cmul(d, p, on, width);
    let width_on = cmul(d, p, width, on);
    let on_frac = cmul(d, p, on, frac);

    // b1 := mul (mul on width) frac
    let b1 = cmul(d, p, on_width, frac);
    let h1 = {
        let assoc = d.lemma(p.mul_assoc, &[on, width, frac]); // Equiv b1 a_start
        d.lemma(p.equiv_symm, &[b1, a_start, assoc]) // Equiv a_start b1
    };

    // b2 := mul (mul width on) frac
    let b2 = cmul(d, p, width_on, frac);
    let h2 = {
        let comm = d.lemma(p.mul_comm, &[on, width]); // Equiv on_width width_on
        let refl_frac = d.lemma(p.equiv_refl, &[frac]);
        d.lemma(
            p.mul_congr,
            &[on_width, width_on, frac, frac, comm, refl_frac],
        )
        // Equiv b1 b2
    };

    // b3 := mul width (mul on frac)
    let b3 = cmul(d, p, width, on_frac);
    // assoc(width,on,frac) : Equiv (mul (mul width on) frac) (mul width (mul on frac)) = Equiv b2 b3
    let h3 = d.lemma(p.mul_assoc, &[width, on, frac]);

    // b4 := mul width one
    let one_c = d.kernel().const_(p.one, vec![]);
    let b4 = cmul(d, p, width, one_c);
    let h4 = {
        let cancel = mesh_inverse_identity(d, p, m); // Equiv on_frac one_c
        let refl_width = d.lemma(p.equiv_refl, &[width]);
        d.lemma(
            p.mul_congr,
            &[width, width, on_frac, one_c, refl_width, cancel],
        )
        // Equiv b3 b4
    };

    let h5 = d.lemma(p.mul_one, &[width]); // Equiv (mul width one) width = Equiv b4 width

    echain(
        d,
        p,
        a_start,
        &[(b1, h1), (b2, h2), (b3, h3), (b4, h4), (width, h5)],
    )
}

/// `Nat.le i n`, from `hlt : Nat.lt i n` (defeq `Nat.le (succ i) n`) — via
/// `Nat.le_succ i : Nat.le i (succ i)` and `Nat.le_trans`.
fn nat_le_of_lt(d: &mut IntDev<'_>, i: ExprId, n: ExprId, hlt: ExprId) -> ExprId {
    let np = d.prelude();
    let succ_i = d.succ(i);
    let step = d.const_app(np.le_succ, &[i]); // Nat.le i (succ i)
    d.const_app(np.le_trans, &[i, succ_i, n, step, hlt])
}

/// `CReal.riemannSum_sample_in_bounds : ∀ a b m i, le a b → Nat.lt i (Nat.succ
/// m) → And (le a (add a (mul (ofNat i) delta))) (le (add a (mul (ofNat i)
/// delta)) b)`, where `delta := (b − a) · ofRat (Rat.natDivSucc 1 m)` exactly
/// as in `riemannSum` itself — every LEFT-endpoint sample point of a Riemann
/// sum over `[a, b]` lies in `[a, b]`.
///
/// Lower half: `0 ≤ ofNat i` ([`zero_le_of_nat`]) times `0 ≤ Δ`
/// ([`delta_nonneg_of`]) gives `0 ≤ ofNat i · Δ` (`mul_nonneg`), and
/// [`shift_le_of_nonneg`] turns that into `a ≤ a + ofNat i · Δ`.
///
/// Upper half: `i < succ m` gives `i ≤ succ m` ([`nat_le_of_lt`]), so `ofNat i
/// ≤ ofNat (succ m)` ([`CRealPrelude::of_nat_le`]); multiplying through by the
/// nonneg `Δ` (`mul_le_mul_of_nonneg_left`, commuted to put `Δ` on the right
/// the same way `riemannSum_le`'s own pointwise step does) gives `ofNat i · Δ
/// ≤ ofNat (succ m) · Δ`, and `ofNat (succ m) · Δ ~ b − a` exactly
/// ([`mesh_times_count_eq_width`]), so `ofNat i · Δ ≤ b − a`; adding `a` to
/// both sides and folding `a + (b − a) ~ b` ([`add_sub_cancel`]) gives `a +
/// ofNat i · Δ ≤ b`.
fn declare_riemann_sample_in_bounds(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);

    let hab_ty = cle(d, p, a, b);
    let hab_fv = d.fresh_fvar();
    let hab = d.kernel().fvar(hab_fv);

    let n = d.succ(m);
    let hlt_ty = d.lt(i, n);
    let hlt_fv = d.fresh_fvar();
    let hlt = d.kernel().fvar(hlt_fv);

    let (delta, delta_nonneg) = delta_nonneg_of(d, p, a, b, m, hab);
    let sp = sample_point(d, p, a, delta, i);
    let of_nat_i = d.const_app(p.of_nat, &[i]);
    let term = cmul(d, p, of_nat_i, delta); // mul (ofNat i) delta, defeq (sp - a)'s summand

    // lower : le a sp.
    let lower = {
        let i_nonneg = zero_le_of_nat(d, p, i);
        let term_nonneg = d.lemma(p.mul_nonneg, &[of_nat_i, delta, i_nonneg, delta_nonneg]);
        shift_le_of_nonneg(d, p, a, term, term_nonneg)
    };

    // upper : le sp b.
    let upper = {
        let hle_i_n = nat_le_of_lt(d, i, n, hlt);
        let of_nat_ile = d.lemma(p.of_nat_le, &[i, n, hle_i_n]); // le (ofNat i) (ofNat n)
        let of_nat_n = d.const_app(p.of_nat, &[n]);

        let step = d.lemma(
            p.mul_le_mul_of_nonneg_left,
            &[delta, of_nat_i, of_nat_n, delta_nonneg, of_nat_ile],
        );
        // step : le (mul delta (ofNat i)) (mul delta (ofNat n))
        let comm_i = d.lemma(p.mul_comm, &[delta, of_nat_i]);
        let comm_n = d.lemma(p.mul_comm, &[delta, of_nat_n]);
        let di = cmul(d, p, delta, of_nat_i);
        let dn = cmul(d, p, delta, of_nat_n);
        let nd = cmul(d, p, of_nat_n, delta);
        let commuted = d.lemma(p.le_congr, &[di, term, dn, nd, comm_i, comm_n, step]);
        // commuted : le (mul (ofNat i) delta) (mul (ofNat n) delta) = le term nd

        let width = width_of(d, p, a, b);
        let one_nat = d.num(1);
        let frac = d.const_app(p.rat.nat_div_succ, &[one_nat, m]);
        let frac_real = embed(d, p, frac);
        let n_delta_eq_width = mesh_times_count_eq_width(d, p, width, frac_real, m);
        // n_delta_eq_width : Equiv (mul (ofNat n) delta) width -- nd, syntactically

        let refl_term = d.lemma(p.equiv_refl, &[term]);
        let term_le_width = d.lemma(
            p.le_congr,
            &[term, term, nd, width, refl_term, n_delta_eq_width, commuted],
        );
        // term_le_width : le term width

        let refl_a = d.lemma(p.le_refl, &[a]);
        let shifted = d.lemma(p.add_le_add, &[a, a, term, width, refl_a, term_le_width]);
        // shifted : le (add a term) (add a width) = le sp (add a width)

        let cancel = add_sub_cancel(d, p, a, b); // Equiv (add a width) b
        let a_width = cadd(d, p, a, width);
        let refl_sp = d.lemma(p.equiv_refl, &[sp]);
        d.lemma(p.le_congr, &[sp, sp, a_width, b, refl_sp, cancel, shifted])
        // : le sp b
    };

    let a_le_sp = cle(d, p, a, sp);
    let sp_le_b = cle(d, p, sp, b);
    let and_ty = d.const_app(p.rat.int.logic.and, &[a_le_sp, sp_le_b]);
    let proof_body = and_intro(d, p, a_le_sp, sp_le_b, lower, upper);

    let ty = {
        let after_hlt = d.arrow(hlt_ty, and_ty);
        let after_hab = d.arrow(hab_ty, after_hlt);
        let over_i = d.pi_fv(i_fv, nat, after_hab);
        let over_m = d.pi_fv(m_fv, nat, over_i);
        let over_b = d.pi_fv(b_fv, carrier, over_m);
        d.pi_fv(a_fv, carrier, over_b)
    };
    let value = {
        let with_hlt = d.lam_fv(hlt_fv, hlt_ty, proof_body);
        let with_hab = d.lam_fv(hab_fv, hab_ty, with_hlt);
        let over_i = d.lam_fv(i_fv, nat, with_hab);
        let over_m = d.lam_fv(m_fv, nat, over_i);
        let over_b = d.lam_fv(b_fv, carrier, over_m);
        d.lam_fv(a_fv, carrier, over_b)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.riemann_sample_in_bounds,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CReal.riemannSum_le_on : ∀ f g a b m, le a b → (∀ z, le a z → le z b → le
/// (f z) (g z)) → le (riemannSum f a b m) (riemannSum g a b m)` —
/// [`declare_riemann_sum_le`]'s pointwise hypothesis RESTRICTED to `[a, b]`.
/// **`riemannSum_le` itself is unchanged** — both theorems exist, stated
/// exactly as their own doc comments say, per the module documentation.
///
/// Identical scaffolding to `declare_riemann_sum_le`; the only change is
/// inside `bounded_pointwise`: the `i < n` witness the original already
/// threads through for `sum_range_le`'s own signature (there, discarded) is
/// used here to invoke [`declare_riemann_sample_in_bounds`]'s theorem at
/// `(a, b, m, i, hab, hlt)`, and `And.left`/`And.right` split its conclusion
/// into the two bounds `hfg` now needs.
fn declare_riemann_sum_le_on(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let f_ty = fn_ty(d, p);
    let logic = p.rat.int.logic;

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);

    let hab_ty = cle(d, p, a, b);
    let hab_fv = d.fresh_fvar();
    let hab = d.kernel().fvar(hab_fv);

    // hfg_ty := ∀ z, le a z → le z b → le (f z) (g z) -- RESTRICTED to [a, b],
    // unlike `declare_riemann_sum_le`'s global `∀ z, le (f z) (g z)`.
    let hfg_ty = {
        let z_fv = d.fresh_fvar();
        let z = d.kernel().fvar(z_fv);
        let fz = d.apply(f, &[z]);
        let gz = d.apply(g, &[z]);
        let conclusion = cle(d, p, fz, gz);
        let z_le_b = cle(d, p, z, b);
        let after_upper = d.arrow(z_le_b, conclusion);
        let a_le_z = cle(d, p, a, z);
        let after_lower = d.arrow(a_le_z, after_upper);
        d.pi_fv(z_fv, carrier, after_lower)
    };
    let hfg_fv = d.fresh_fvar();
    let hfg = d.kernel().fvar(hfg_fv);

    let (delta, delta_nonneg) = delta_nonneg_of(d, p, a, b, m, hab);
    let n = d.succ(m);

    let f_summand = summand_fn(d, p, f, a, delta);
    let g_summand = summand_fn(d, p, g, a, delta);

    let bounded_pointwise = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let sp = sample_point(d, p, a, delta, i);
        let fz = d.apply(f, &[sp]);
        let gz = d.apply(g, &[sp]);

        let lt_hyp_ty = d.lt(i, n);
        let lt_fv = d.fresh_fvar();
        let lt = d.kernel().fvar(lt_fv);

        // and_bounds : And (le a sp) (le sp b), from
        // `riemannSum_sample_in_bounds a b m i hab lt`.
        let and_bounds = d.const_app(p.riemann_sample_in_bounds, &[a, b, m, i, hab, lt]);
        let a_le_sp = cle(d, p, a, sp);
        let sp_le_b = cle(d, p, sp, b);
        let lower = d.const_app(logic.and_left, &[a_le_sp, sp_le_b, and_bounds]);
        let upper = d.const_app(logic.and_right, &[a_le_sp, sp_le_b, and_bounds]);
        let h_fg = d.apply(hfg, &[sp, lower, upper]); // le (f sp) (g sp)

        let step = d.lemma(
            p.mul_le_mul_of_nonneg_left,
            &[delta, fz, gz, delta_nonneg, h_fg],
        );
        // step : le (mul delta fz) (mul delta gz)
        let comm_f = d.lemma(p.mul_comm, &[delta, fz]); // Equiv (mul delta fz) (mul fz delta)
        let comm_g = d.lemma(p.mul_comm, &[delta, gz]);
        let df = cmul(d, p, delta, fz);
        let dg = cmul(d, p, delta, gz);
        let fd = cmul(d, p, fz, delta);
        let gd = cmul(d, p, gz, delta);
        let transported = d.lemma(p.le_congr, &[df, fd, dg, gd, comm_f, comm_g, step]);
        // transported : le (mul fz delta) (mul gz delta) = le (f_summand i) (g_summand i)

        let with_lt = d.lam_fv(lt_fv, lt_hyp_ty, transported);
        d.lam_fv(i_fv, nat, with_lt)
    };

    let result = d.lemma(
        p.sum_range_le,
        &[f_summand, g_summand, n, bounded_pointwise],
    );

    let ty = {
        let lhs_rs = rsum(d, p, f, a, b, m);
        let rhs_rs = rsum(d, p, g, a, b, m);
        cle(d, p, lhs_rs, rhs_rs)
    };
    let ty_inner = {
        let after_hfg = d.arrow(hfg_ty, ty);
        d.arrow(hab_ty, after_hfg)
    };
    let ty_full = {
        let over_m = d.pi_fv(m_fv, nat, ty_inner);
        let over_b = d.pi_fv(b_fv, carrier, over_m);
        let over_a = d.pi_fv(a_fv, carrier, over_b);
        let over_g = d.pi_fv(g_fv, f_ty, over_a);
        d.pi_fv(f_fv, f_ty, over_g)
    };
    let value_inner = {
        let with_hfg = d.lam_fv(hfg_fv, hfg_ty, result);
        d.lam_fv(hab_fv, hab_ty, with_hfg)
    };
    let value_full = {
        let over_m = d.lam_fv(m_fv, nat, value_inner);
        let over_b = d.lam_fv(b_fv, carrier, over_m);
        let over_a = d.lam_fv(a_fv, carrier, over_b);
        let over_g = d.lam_fv(g_fv, f_ty, over_a);
        d.lam_fv(f_fv, f_ty, over_g)
    };

    d.kernel().add_declaration(Declaration::Theorem {
        name: p.riemann_sum_le_on,
        uparams: vec![],
        ty: ty_full,
        value: value_full,
    })
}

// --- `riemannSum_const` --------------------------------------------------

/// `Equiv (ofNat (Nat.succ Nat.zero)) one` — `CReal.ofNat 1 ~ CReal.one`.
///
/// A local restatement of `derivative.rs`'s private `of_nat_one_equiv`
/// (that file is out of scope for this slice, so it cannot be called from
/// here): `ofNat 1 := ofRat (Rat.natDivSucc 1 0)` unfolds one delta step,
/// `one := ofRat Rat.one` unfolds one delta step the same way, and what
/// bridges them is `Eq Rat (Rat.natDivSucc 1 0) Rat.one`
/// ([`CRealPrelude::rat_unit_eq_one`]), lifted across `ofRat` by
/// [`rat_eq_rewrite`].
fn of_nat_one_equiv_local(d: &mut IntDev<'_>, p: CRealPrelude) -> ExprId {
    let rat = p.rat;
    let one_nat = d.num(1);
    let zero_nat = d.num(0);
    let unit = d.const_app(rat.nat_div_succ, &[one_nat, zero_nat]);
    let one_rat = rone(d, rat);
    let unit_eq_one = d.lemma(p.rat_unit_eq_one, &[]); // Eq Rat unit one_rat
    let unit_embed = embed(d, p, unit); // defeq (ofNat 1)
    let refl_start = d.lemma(p.equiv_refl, &[unit_embed]);
    rat_eq_rewrite(d, unit, one_rat, unit_eq_one, refl_start, &|d, t| {
        let embedded = embed(d, p, t);
        equiv(d, p, unit_embed, embedded)
    })
    // : Equiv unit_embed (ofRat one_rat) -- defeq Equiv (ofNat 1) one.
}

/// `Equiv (ofNat (Nat.succ m)) (add (ofNat m) one)` — the successor law
/// `CReal.ofNat` carries no equation for.
///
/// A local restatement of `derivative.rs`'s private `of_nat_succ_equiv`,
/// for the same out-of-scope-file reason as [`of_nat_one_equiv_local`]:
/// built from [`RatPrelude::nat_div_succ_add`] (`natDivSucc m 0 +
/// natDivSucc 1 0 = natDivSucc (Nat.add m 1) 0`, with `Nat.add m 1` defeq
/// `Nat.succ m`) plus [`CRealPrelude::of_rat_add`] to lift the rational sum
/// across `ofRat`, then [`of_nat_one_equiv_local`] to fold the second
/// summand from `ofNat 1` down to `one`.
fn of_nat_succ_equiv_local(d: &mut IntDev<'_>, p: CRealPrelude, m: ExprId) -> ExprId {
    let rat = p.rat;
    let one_nat = d.num(1);
    let zero_nat = d.num(0);
    let one_c = d.kernel().const_(p.one, vec![]);

    let m_rat = d.const_app(rat.nat_div_succ, &[m, zero_nat]);
    let one_ratdiv = d.const_app(rat.nat_div_succ, &[one_nat, zero_nat]);
    let sum_rat = radd(d, m_rat, one_ratdiv);
    let succ_m = d.succ(m);
    let succ_rat = d.const_app(rat.nat_div_succ, &[succ_m, zero_nat]);
    // Eq Rat sum_rat (natDivSucc (Nat.add m 1) 0), the RHS defeq succ_rat.
    let add_eq = d.lemma(rat.nat_div_succ_add, &[m, one_nat, zero_nat]);

    let of_nat_m = d.const_app(p.of_nat, &[m]);
    let of_nat_1 = d.const_app(p.of_nat, &[one_nat]);
    let of_nat_succ_m = d.const_app(p.of_nat, &[succ_m]);
    let add_of_nat_m_1 = cadd(d, p, of_nat_m, of_nat_1);

    // Equiv (add of_nat_m of_nat_1) (ofRat sum_rat)
    let add_step = d.lemma(p.of_rat_add, &[m_rat, one_ratdiv]);
    // Equiv (add of_nat_m of_nat_1) (ofRat succ_rat) -- defeq (ofNat (succ m))
    let rewritten = rat_eq_rewrite(d, sum_rat, succ_rat, add_eq, add_step, &|d, t| {
        let embedded = embed(d, p, t);
        equiv(d, p, add_of_nat_m_1, embedded)
    });
    // Equiv (ofNat (succ m)) (add of_nat_m of_nat_1)
    let flipped = d.lemma(p.equiv_symm, &[add_of_nat_m_1, of_nat_succ_m, rewritten]);

    // Equiv (add of_nat_m of_nat_1) (add of_nat_m one)
    let one_eq = of_nat_one_equiv_local(d, p);
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
    // : Equiv (ofNat (succ m)) (add (ofNat m) one)
}

/// `Eq Rat (Rat.mul (Rat.natDivSucc (Nat.succ m) 0) (Rat.natDivSucc 1 m))
/// Rat.one` — `(m+1)/1 · 1/(m+1) = 1`.
///
/// The same rational identity `rat_prelude/field.rs::declare_inv_nat_div_succ`
/// derives in passing as its own `cancel` step (`w·c = 1`, with `w :=
/// (m+1)/1` and `c := 1/(m+1)`): `nat_div_succ_mul` fuses the product into a
/// single `natDivSucc`, `Nat.mul_one` collapses its numerator, then
/// `nat_div_succ_scale` at index `0` (composed with `Nat.zero_add`) reads
/// the result as `1/1`, and [`CRealPrelude::rat_unit_eq_one`] closes `1/1 =
/// Rat.one` — reusing that already-proved fact in place of a fresh
/// `self_normalize` call. `field.rs`'s own proof continues past this point
/// to compute `(1/(m+1))⁻¹`; this stops at the product identity, which is
/// all `mesh_inverse_identity` below needs.
fn nat_div_succ_inverse_pair_eq_one(d: &mut IntDev<'_>, p: CRealPrelude, m: ExprId) -> ExprId {
    let rat = p.rat;
    let nat = rat.int.nat;
    let one_nat = d.num(1);
    let zero_nat = d.num(0);
    let successor = d.succ(m);
    let modulus = d.const_app(rat.nat_div_succ, &[one_nat, m]);
    let whole = d.const_app(rat.nat_div_succ, &[successor, zero_nat]);
    let one_val = rone(d, rat);

    let product = rmul(d, whole, modulus);
    let fused = {
        let scaled = NatOps::mul(d, successor, one_nat);
        d.const_app(rat.nat_div_succ, &[scaled, m])
    };
    let fuse = d.lemma(rat.nat_div_succ_mul, &[successor, one_nat, m]);
    let collapsed = d.const_app(rat.nat_div_succ, &[successor, m]);
    let collapse = {
        let scaled = NatOps::mul(d, successor, one_nat);
        let identity = d.lemma(nat.mul_one, &[successor]);
        nat_eq_to_rat(d, scaled, successor, identity, &|d, t| {
            d.const_app(rat.nat_div_succ, &[t, m])
        })
    };
    let unit = d.const_app(rat.nat_div_succ, &[one_nat, zero_nat]);
    let scale = {
        let deep = NatOps::mul(d, successor, zero_nat);
        let index = NatOps::add(d, deep, m);
        let law = d.lemma(rat.nat_div_succ_scale, &[m, zero_nat]);
        let flatten = d.lemma(nat.zero_add, &[m]);
        nat_rewrite_prop(d, index, m, flatten, law, &|d, t| {
            let left = d.const_app(rat.nat_div_succ, &[successor, t]);
            req(d, left, unit)
        })
    };
    let unit_is_one = d.lemma(p.rat_unit_eq_one, &[]);
    let (_, cancel) = rchain(
        d,
        product,
        &[
            (fused, fuse),
            (collapsed, collapse),
            (unit, scale),
            (one_val, unit_is_one),
        ],
    );
    cancel
    // : Eq Rat (rmul whole modulus) one_val
}

/// `Equiv (mul (ofNat (Nat.succ m)) (ofRat (Rat.natDivSucc 1 m))) one` —
/// the mesh count exactly cancels the mesh fraction, for every `m`.
///
/// `ofNat (succ m)` and `ofRat (natDivSucc 1 m)` are each one delta step
/// from an `embed` of the corresponding `Rat.natDivSucc`; `CReal.ofRat_mul`
/// lifts [`nat_div_succ_inverse_pair_eq_one`]'s product identity across
/// that embedding, landing on `embed Rat.one`, itself one delta step from
/// `CReal.one`.
fn mesh_inverse_identity(d: &mut IntDev<'_>, p: CRealPrelude, m: ExprId) -> ExprId {
    let rat = p.rat;
    let one_nat = d.num(1);
    let zero_nat = d.num(0);
    let successor = d.succ(m);
    let modulus = d.const_app(rat.nat_div_succ, &[one_nat, m]);
    let whole = d.const_app(rat.nat_div_succ, &[successor, zero_nat]);

    let embed_whole = embed(d, p, whole); // defeq (ofNat (succ m))
    let embed_modulus = embed(d, p, modulus); // defeq (ofRat (natDivSucc 1 m))
    let product_real = cmul(d, p, embed_whole, embed_modulus);

    let rat_eq = nat_div_succ_inverse_pair_eq_one(d, p, m); // Eq Rat (rmul whole modulus) one_rat
    let of_rat_mul_step = d.lemma(p.of_rat_mul, &[whole, modulus]);
    // : Equiv product_real (embed (rmul whole modulus))

    let product_rat = rmul(d, whole, modulus);
    let one_rat = rone(d, rat);
    rat_eq_rewrite(d, product_rat, one_rat, rat_eq, of_rat_mul_step, &|d, t| {
        let embedded = embed(d, p, t);
        equiv(d, p, product_real, embedded)
    })
    // : Equiv product_real (embed one_rat) -- defeq Equiv product_real one.
}

/// `Equiv (sumRange (fun _ => w) (Nat.succ m)) (mul (ofNat (Nat.succ m)) w)`
/// — `succ m` copies of a constant `w` sum to `(succ m)·w`. Induction on
/// `m`, `w` fixed.
///
/// The base case (`m = 0`) needs `ofNat 1 ~ one`
/// ([`of_nat_one_equiv_local`]); the step needs `ofNat (succ k) ~ add
/// (ofNat k) one` ([`of_nat_succ_equiv_local`]) plus [`right_distrib`] to
/// expand `(ofNat k + one)·w`. Both hold for every `m`/`k` directly (no
/// induction of their own), so inducting on `m` here — rather than on the
/// subinterval COUNT `n` from `Nat.zero` — never needs an `ofNat 0` fact at
/// all, which `CReal.ofNat` (defined via `Rat.natDivSucc _ 0`, not
/// `Nat.rec`) does not give for free.
fn riemann_sum_const_core(d: &mut IntDev<'_>, p: CRealPrelude, w: ExprId, m: ExprId) -> ExprId {
    let const_fn = |d: &mut IntDev<'_>| -> ExprId {
        let i_fv = d.fresh_fvar();
        let nat = d.nat_ty();
        d.lam_fv(i_fv, nat, w)
    };

    let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let f = const_fn(d);
        let sx = d.succ(x);
        let lhs = d.const_app(p.sum_range, &[f, sx]);
        let ox = d.const_app(p.of_nat, &[sx]);
        let rhs = cmul(d, p, ox, w);
        equiv(d, p, lhs, rhs)
    };

    d.induct(
        &motive,
        &|d| {
            // Goal (defeq unfolded): Equiv (add zero w) (mul (ofNat 1) w).
            let zero_c = czero(d, p);
            let one_c = d.kernel().const_(p.one, vec![]);
            let one_nat = d.num(1);
            let of_nat_1 = d.const_app(p.of_nat, &[one_nat]);

            let start = cadd(d, p, zero_c, w);
            let m1w = cmul(d, p, one_c, w);
            let target_mw = cmul(d, p, of_nat_1, w);

            // add zero w ~ w
            let step1 = {
                let comm = d.lemma(p.add_comm, &[zero_c, w]); // add zero w ~ add w zero
                let wz = cadd(d, p, w, zero_c);
                let vanish = d.lemma(p.add_zero, &[w]); // add w zero ~ w
                d.lemma(p.equiv_trans, &[start, wz, w, comm, vanish])
            };
            // w ~ mul one w
            let step2 = {
                let mw1 = cmul(d, p, w, one_c);
                let mul_one_w = d.lemma(p.mul_one, &[w]); // mul w one ~ w
                let back = d.lemma(p.equiv_symm, &[mw1, w, mul_one_w]); // w ~ mul w one
                let comm = d.lemma(p.mul_comm, &[w, one_c]); // mul w one ~ mul one w
                d.lemma(p.equiv_trans, &[w, mw1, m1w, back, comm])
            };
            // mul one w ~ mul (ofNat 1) w
            let step3 = {
                let one_eq = of_nat_one_equiv_local(d, p); // Equiv (ofNat 1) one
                let back = d.lemma(p.equiv_symm, &[of_nat_1, one_c, one_eq]); // one ~ ofNat 1
                let refl_w = d.lemma(p.equiv_refl, &[w]);
                d.lemma(p.mul_congr, &[one_c, of_nat_1, w, w, back, refl_w])
            };
            let s01 = d.lemma(p.equiv_trans, &[start, w, m1w, step1, step2]);
            d.lemma(p.equiv_trans, &[start, m1w, target_mw, s01, step3])
        },
        &|d, j, ih| {
            // ih : Equiv (sumRange f (succ j)) (mul (ofNat (succ j)) w)
            // Goal (defeq unfolded): Equiv (add (sumRange f (succ j)) w)
            //   (mul (ofNat (succ (succ j))) w)
            let f = const_fn(d);
            let sj = d.succ(j);
            let prior = d.const_app(p.sum_range, &[f, sj]);
            let start = cadd(d, p, prior, w);

            let of_nat_sj = d.const_app(p.of_nat, &[sj]);
            let ih_target = cmul(d, p, of_nat_sj, w);

            // start ~ add ih_target w
            let step_ih = {
                let refl_w = d.lemma(p.equiv_refl, &[w]);
                d.lemma(p.add_congr, &[prior, ih_target, w, w, ih, refl_w])
            };
            let after_ih = cadd(d, p, ih_target, w);

            let ssj = d.succ(sj);
            let of_nat_ssj = d.const_app(p.of_nat, &[ssj]);
            let final_target = cmul(d, p, of_nat_ssj, w);

            let one_c = d.kernel().const_(p.one, vec![]);
            let succ_eq = of_nat_succ_equiv_local(d, p, sj); // Equiv (ofNat (succ sj)) (add (ofNat sj) one)
            let sum_of_nat = cadd(d, p, of_nat_sj, one_c);
            let expanded = cmul(d, p, sum_of_nat, w);

            // final_target ~ expanded
            let h_a = {
                let refl_w = d.lemma(p.equiv_refl, &[w]);
                d.lemma(
                    p.mul_congr,
                    &[of_nat_ssj, sum_of_nat, w, w, succ_eq, refl_w],
                )
            };
            // expanded ~ add ih_target (mul one w)
            let h_b = right_distrib(d, p, of_nat_sj, one_c, w);
            let one_w = cmul(d, p, one_c, w);
            let distributed = cadd(d, p, ih_target, one_w);
            // distributed ~ after_ih
            let h_c = {
                let refl_left = d.lemma(p.equiv_refl, &[ih_target]);
                let one_mul_w = {
                    // Equiv (mul one w) w
                    let mw1 = cmul(d, p, w, one_c);
                    let mul_one_w = d.lemma(p.mul_one, &[w]);
                    let comm = d.lemma(p.mul_comm, &[one_c, w]); // mul one w ~ mul w one
                    d.lemma(p.equiv_trans, &[one_w, mw1, w, comm, mul_one_w])
                };
                d.lemma(
                    p.add_congr,
                    &[ih_target, ih_target, one_w, w, refl_left, one_mul_w],
                )
            };

            let rev = {
                let s1 = d.lemma(
                    p.equiv_trans,
                    &[final_target, expanded, distributed, h_a, h_b],
                );
                d.lemma(
                    p.equiv_trans,
                    &[final_target, distributed, after_ih, s1, h_c],
                )
            };
            let rev_flipped = d.lemma(p.equiv_symm, &[final_target, after_ih, rev]);
            d.lemma(
                p.equiv_trans,
                &[start, after_ih, final_target, step_ih, rev_flipped],
            )
        },
        m,
    )
}

/// `Equiv (mul (ofNat (Nat.succ m)) w) (mul c width)` where `w := mul c
/// delta` and `delta := mul width frac` — the algebraic rearrangement that
/// closes [`declare_riemann_sum_const`] once [`riemann_sum_const_core`] has
/// collapsed the sum. An eight-step associativity/commutativity chain
/// exposes `mul (ofNat (succ m)) frac` next to `width`, cancels it via
/// [`mesh_inverse_identity`], then folds the trailing `mul _ one` via
/// `mul_one`.
#[allow(clippy::too_many_arguments)]
fn riemann_sum_const_rearrange(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    c: ExprId,
    width: ExprId,
    frac: ExprId,
    m: ExprId,
) -> ExprId {
    let on = {
        let successor = d.succ(m);
        d.const_app(p.of_nat, &[successor]) // ofNat (succ m)
    };
    let one_c = d.kernel().const_(p.one, vec![]);

    let delta = cmul(d, p, width, frac);
    let w = cmul(d, p, c, delta);
    let a_start = cmul(d, p, on, w); // mul (ofNat n) (mul c (mul width frac))

    let on_c = cmul(d, p, on, c);
    let c_on = cmul(d, p, c, on);
    let on_width = cmul(d, p, on, width);
    let width_on = cmul(d, p, width, on);
    let on_frac = cmul(d, p, on, frac);
    let on_delta = cmul(d, p, on, delta);
    let width_on_frac = cmul(d, p, width_on, frac);
    let width_one = cmul(d, p, width, one_c);
    let width_on_frac_paren = cmul(d, p, width, on_frac);

    // b1 := mul (mul on c) delta
    let b1 = cmul(d, p, on_c, delta);
    // h1 : a_start ~ b1
    let h1 = {
        let assoc = d.lemma(p.mul_assoc, &[on, c, delta]); // Equiv b1 a_start
        d.lemma(p.equiv_symm, &[b1, a_start, assoc])
    };

    // b2 := mul (mul c on) delta
    let b2 = cmul(d, p, c_on, delta);
    // h2 : b1 ~ b2
    let h2 = {
        let comm = d.lemma(p.mul_comm, &[on, c]); // Equiv on_c c_on
        let refl_delta = d.lemma(p.equiv_refl, &[delta]);
        d.lemma(p.mul_congr, &[on_c, c_on, delta, delta, comm, refl_delta])
    };

    // b3 := mul c (mul on delta)
    let b3 = cmul(d, p, c, on_delta);
    // h3 : b2 ~ b3
    let h3 = d.lemma(p.mul_assoc, &[c, on, delta]);

    // b4 := mul c (mul (mul on width) frac)
    let on_width_frac = cmul(d, p, on_width, frac);
    let b4 = cmul(d, p, c, on_width_frac);
    // h4 : b3 ~ b4
    let h4 = {
        let assoc = d.lemma(p.mul_assoc, &[on, width, frac]); // Equiv on_width_frac on_delta
        let inner = d.lemma(p.equiv_symm, &[on_width_frac, on_delta, assoc]);
        let refl_c = d.lemma(p.equiv_refl, &[c]);
        d.lemma(p.mul_congr, &[c, c, on_delta, on_width_frac, refl_c, inner])
    };

    // b5 := mul c (mul (mul width on) frac)
    let b5 = cmul(d, p, c, width_on_frac);
    // h5 : b4 ~ b5
    let h5 = {
        let comm = d.lemma(p.mul_comm, &[on, width]); // Equiv on_width width_on
        let refl_frac = d.lemma(p.equiv_refl, &[frac]);
        let inner = d.lemma(
            p.mul_congr,
            &[on_width, width_on, frac, frac, comm, refl_frac],
        );
        let refl_c = d.lemma(p.equiv_refl, &[c]);
        d.lemma(
            p.mul_congr,
            &[c, c, on_width_frac, width_on_frac, refl_c, inner],
        )
    };

    // b6 := mul c (mul width (mul on frac))
    let b6 = cmul(d, p, c, width_on_frac_paren);
    // h6 : b5 ~ b6
    let h6 = {
        let assoc = d.lemma(p.mul_assoc, &[width, on, frac]); // Equiv width_on_frac width_on_frac_paren
        let refl_c = d.lemma(p.equiv_refl, &[c]);
        d.lemma(
            p.mul_congr,
            &[c, c, width_on_frac, width_on_frac_paren, refl_c, assoc],
        )
    };

    // b7 := mul c (mul width one)
    let b7 = cmul(d, p, c, width_one);
    // h7 : b6 ~ b7
    let h7 = {
        let cancel = mesh_inverse_identity(d, p, m); // Equiv on_frac one_c
        let refl_width = d.lemma(p.equiv_refl, &[width]);
        let inner = d.lemma(
            p.mul_congr,
            &[width, width, on_frac, one_c, refl_width, cancel],
        );
        let refl_c = d.lemma(p.equiv_refl, &[c]);
        d.lemma(
            p.mul_congr,
            &[c, c, width_on_frac_paren, width_one, refl_c, inner],
        )
    };

    // b8 := mul c width
    let b8 = cmul(d, p, c, width);
    // h8 : b7 ~ b8
    let h8 = {
        let mul_one_w = d.lemma(p.mul_one, &[width]); // Equiv width_one width
        let refl_c = d.lemma(p.equiv_refl, &[c]);
        d.lemma(p.mul_congr, &[c, c, width_one, width, refl_c, mul_one_w])
    };

    echain(
        d,
        p,
        a_start,
        &[
            (b1, h1),
            (b2, h2),
            (b3, h3),
            (b4, h4),
            (b5, h5),
            (b6, h6),
            (b7, h7),
            (b8, h8),
        ],
    )
}

/// Chain `Equiv start …` through `(next, step)` pairs — a private restatement
/// of `ring_helpers.rs`'s `echain`, `pub(super)` there and unreachable from
/// this out-of-scope-for-this-slice file for the same reason as
/// [`of_nat_one_equiv_local`].
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

/// `CReal.riemannSum_const : ∀ c a b m,
/// Equiv (riemannSum (fun _ => c) a b m) (mul c (add b (neg a)))` — a
/// constant function's Riemann sum is exactly base times height, for every
/// subinterval count `m`. See the module documentation for the two-piece
/// route.
fn declare_riemann_sum_const(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();

    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);

    let f_const = {
        let r_fv = d.fresh_fvar();
        d.lam_fv(r_fv, carrier, c)
    };

    let width = width_of(d, p, a, b);
    let frac = {
        let one_nat = d.num(1);
        let rat_frac = d.const_app(p.rat.nat_div_succ, &[one_nat, m]);
        embed(d, p, rat_frac)
    };
    let delta = cmul(d, p, width, frac); // defeq delta_of(a, b, m)
    let w = cmul(d, p, c, delta);

    // step1 : Equiv (riemannSum f_const a b m) (mul (ofNat (succ m)) w)
    let step1 = riemann_sum_const_core(d, p, w, m);

    // step2 : Equiv (mul (ofNat (succ m)) w) (mul c width)
    let step2 = riemann_sum_const_rearrange(d, p, c, width, frac, m);

    let successor = d.succ(m);
    let of_nat_n = d.const_app(p.of_nat, &[successor]);
    let a_mid = cmul(d, p, of_nat_n, w);
    let lhs = rsum(d, p, f_const, a, b, m);
    let rhs = cmul(d, p, c, width);

    let proof = d.lemma(p.equiv_trans, &[lhs, a_mid, rhs, step1, step2]);

    let ty = equiv(d, p, lhs, rhs);
    let ty_full = {
        let over_m = d.pi_fv(m_fv, nat, ty);
        let over_b = d.pi_fv(b_fv, carrier, over_m);
        let over_a = d.pi_fv(a_fv, carrier, over_b);
        d.pi_fv(c_fv, carrier, over_a)
    };
    let value_full = {
        let over_m = d.lam_fv(m_fv, nat, proof);
        let over_b = d.lam_fv(b_fv, carrier, over_m);
        let over_a = d.lam_fv(a_fv, carrier, over_b);
        d.lam_fv(c_fv, carrier, over_a)
    };

    d.kernel().add_declaration(Declaration::Theorem {
        name: p.riemann_sum_const,
        uparams: vec![],
        ty: ty_full,
        value: value_full,
    })
}

// --- `CReal.sumRange_double` -- toward `riemannSum_cauchy` -----------------
//
// The refinement estimate `riemannSum_cauchy` needs (see this module's own
// top-level documentation for the paper estimate) compares `riemannSum f a b
// m` at two DIFFERENT subdivision counts. The standard route is a common
// refinement of both partitions; for the special case of doubling the count
// (`m` pieces vs. `2m` pieces, each of the coarse pieces split into two equal
// fine pieces), the needed bookkeeping reduces to a single fact about
// `CReal.sumRange` that mentions no Riemann sum at all: summing `2k` terms of
// an arbitrary `g : Nat -> CReal` and grouping them two at a time gives the
// same total as summing the `k` pairwise sums. That fact is
// [`declare_sum_range_double`], proved directly by induction on `k` (no
// hypothesis on `g` needed — this is pure regrouping, not an estimate), and
// it is landed here as a standalone, reusable building block ahead of the
// error-bound machinery `riemannSum_cauchy` itself still needs (bounding each
// pair's contribution against the coarse term via
// `CReal.UniformlyContinuousOn.spec`, at a subdivision count large enough for
// the outer accuracy via the same magnitude/`e_acc` scaling
// `monotone_of_nonneg_deriv` uses, then folding the resulting sum-of-bounds
// via `CReal.sumRange_le` + `CReal.sumRange_const` + `CReal.mesh_count_width`
// into a single real inequality, and finally converting that real inequality
// into the `CReal.Within`-shaped bound `CReal.Cauchy` demands at `riemannSum`'s
// own canonical sample indices — none of which is attempted here).

/// `fun i => add (g (Nat.mul 2 i)) (g (Nat.succ (Nat.mul 2 i)))` — the
/// `i`-th block of two consecutive `g`-terms, `g(2i) + g(2i+1)`.
/// `fun k => f (Nat.add m k)` — `f` shifted by `m`. Reproduced verbatim from
/// `series.rs::shifted_fn` / `geometric.rs::shifted_fn` (both private to
/// their own modules), matching `CReal.sumRange_split`'s own instantiated
/// conclusion shape exactly so this file's block sums are structurally
/// (not merely propositionally) the same closures `sum_range_split`
/// produces.
fn reblock_shifted_fn(d: &mut IntDev<'_>, m: ExprId, f: ExprId) -> ExprId {
    let nat_add = d.prelude().add;
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let mk = d.const_app(nat_add, &[m, k]);
    let body = d.apply(f, &[mk]);
    let nat = d.nat_ty();
    d.lam_fv(k_fv, nat, body)
}
/// `fun i => sumRange (fun j => g (Nat.add (Nat.mul bs i) j)) bs` — the
/// `i`-th block of `bs` consecutive `g`-terms, starting at `bs * i`. `bs` is
/// always the FIRST argument of `Nat.mul` here, matching the shape
/// `Nat.mul`'s own iota-reduction forces at the induction step below (never
/// `Nat.mul i bs`, which is only propositionally, not definitionally, the
/// same term).
fn reblock_block(d: &mut IntDev<'_>, p: CRealPrelude, g: ExprId, bs: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let offset = NatOps::mul(d, bs, i);
    let shifted = reblock_shifted_fn(d, offset, g);
    let body = d.const_app(p.sum_range, &[shifted, bs]);
    d.lam_fv(i_fv, nat, body)
}
/// The proof term for `CReal.sumRange_reblock` at a fixed block size `bs`,
/// by induction on the block count `k`. See this section's own module
/// documentation for the derivation.
fn sum_range_reblock_proof(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    g: ExprId,
    bs: ExprId,
    k: ExprId,
) -> ExprId {
    let block = reblock_block(d, p, g, bs);

    let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let total = NatOps::mul(d, bs, x);
        let lhs = d.const_app(p.sum_range, &[g, total]);
        let rhs = d.const_app(p.sum_range, &[block, x]);
        equiv(d, p, lhs, rhs)
    };

    d.induct(
        &motive,
        &|d| {
            // motive(zero): `Nat.mul bs Nat.zero ≡ Nat.zero`, so both sides
            // reduce (defeq) to `CReal.zero`.
            let zero_c = czero(d, p);
            d.lemma(p.equiv_refl, &[zero_c])
        },
        &|d, j, ih| {
            // ih : Equiv (sumRange g (mul bs j)) (sumRange block j)
            let bs_j = NatOps::mul(d, bs, j);
            let succ_j = d.succ(j);

            let sum_g_bsj = d.const_app(p.sum_range, &[g, bs_j]);
            let sum_block_j = d.const_app(p.sum_range, &[block, j]);
            let block_j = d.apply(block, &[j]);

            // split_step : Equiv (sumRange g (add bs_j bs))
            //                    (add sum_g_bsj (sumRange (shifted bs_j g) bs))
            // -- the second summand is defeq `block_j` (`reblock_block`'s own
            // definition at `i := j`, same `bs_j` offset, same block size
            // `bs`) by one beta step, no new lemma needed.
            let split_step = d.lemma(p.sum_range_split, &[g, bs_j, bs]);

            // h1 : Equiv (add sum_g_bsj block_j) (add sum_block_j block_j)
            let refl_block_j = d.lemma(p.equiv_refl, &[block_j]);
            let h1 = d.lemma(
                p.add_congr,
                &[sum_g_bsj, sum_block_j, block_j, block_j, ih, refl_block_j],
            );

            // Goal (defeq unfolded, `succ_j`): `Equiv (sumRange g (mul bs
            // succ_j)) (sumRange block succ_j)` -- `mul bs succ_j` is defeq
            // `add bs_j bs` (`Nat.mul`'s iota step), and `sumRange block
            // succ_j` is defeq `add sum_block_j block_j` (`sumRange`'s own
            // iota step), so `equiv_trans(split_step, h1)` closes it exactly.
            let lhs_goal = {
                let total_succ = NatOps::mul(d, bs, succ_j);
                d.const_app(p.sum_range, &[g, total_succ])
            };
            let mid = cadd(d, p, sum_g_bsj, block_j);
            let rhs_goal = d.const_app(p.sum_range, &[block, succ_j]);

            d.lemma(p.equiv_trans, &[lhs_goal, mid, rhs_goal, split_step, h1])
        },
        k,
    )
}
/// `CReal.sumRange_reblock : ∀ (g : Nat → CReal) (n k : Nat), Equiv (sumRange
/// g (Nat.mul (Nat.succ n) k)) (sumRange (fun i => sumRange (fun j => g
/// (Nat.add (Nat.mul (Nat.succ n) i) j)) (Nat.succ n)) k)` — regrouping
/// `k · (n+1)` consecutive terms of an arbitrary `g` into `k` consecutive
/// blocks of `n+1`, exactly (no error term), for an arbitrary block size
/// `n+1` (never zero). Generalizes `CReal.sumRange_double` (block size fixed
/// at the literal `2`) from a private, not-yet-merged worktree branch; see
/// this section's own module documentation for the derivation and precisely
/// what remains toward `riemannSum_cauchy`.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` from a `Theorem` here means
/// the kernel **refused** a proof, not that a script gave up.
pub(super) fn declare_sum_range_reblock(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = creal_ty(d, p);
    let fn_ty = d.arrow(nat, carrier);

    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);

    let bs = d.succ(n);
    let proof = sum_range_reblock_proof(d, p, g, bs, k);

    let ty = {
        let total = NatOps::mul(d, bs, k);
        let lhs = d.const_app(p.sum_range, &[g, total]);
        let block = reblock_block(d, p, g, bs);
        let rhs = d.const_app(p.sum_range, &[block, k]);
        equiv(d, p, lhs, rhs)
    };
    let ty_full = {
        let over_k = d.pi_fv(k_fv, nat, ty);
        let over_n = d.pi_fv(n_fv, nat, over_k);
        d.pi_fv(g_fv, fn_ty, over_n)
    };
    let value_full = {
        let over_k = d.lam_fv(k_fv, nat, proof);
        let over_n = d.lam_fv(n_fv, nat, over_k);
        d.lam_fv(g_fv, fn_ty, over_n)
    };

    d.kernel().add_declaration(Declaration::Theorem {
        name: p.sum_range_reblock,
        uparams: vec![],
        ty: ty_full,
        value: value_full,
    })
}
/// From `Rat.le (Rat.sub u v) w` and `Rat.le (Rat.sub (Rat.neg u) v) w`,
/// derive `CReal.Within u (Rat.add v w)`. Reproduced verbatim from
/// `series.rs::within_of_tail_le` / `geometric.rs::within_of_tail_le` (both
/// private to their own modules) — the RAT-LEVEL half of the bridge, already
/// fully general over any `u, v, w`.
fn within_of_sub_le(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    u: ExprId,
    v: ExprId,
    w: ExprId,
    h1: ExprId,
    h2: ExprId,
) -> ExprId {
    let rat = p.rat;
    let vw = radd(d, v, w);

    let upper = d.lemma(rat.le_of_sub_le, &[u, v, w, h1]);

    let neg_u = rneg(d, u);
    let lower_neg = d.lemma(rat.le_of_sub_le, &[neg_u, v, w, h2]);

    let neg_vw = rneg(d, vw);
    let neg_neg_u = rneg(d, neg_u);
    let flipped = d.lemma(rat.neg_le_neg, &[neg_u, vw, lower_neg]);

    let nn = d.lemma(rat.neg_neg, &[u]);
    let lower = rat_eq_rewrite(d, neg_neg_u, u, nn, flipped, &|d, t| rle(d, rat, neg_vw, t));

    let lower_ty = rle(d, rat, neg_vw, u);
    let upper_ty = rle(d, rat, u, vw);
    and_intro(d, p, lower_ty, upper_ty, lower, upper)
}
/// `CReal.within_of_two_sided_le : ∀ t y : CReal, le t y → le (neg t) y →
/// ∀ i : Nat, Within (seq t i) (add (seq y i) (natDivSucc 2 i))`. See this
/// section's own module documentation for the derivation, and for whether
/// `geometric.rs::geom_tail_within` could be re-derived from this (it could,
/// without editing that file).
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` from a `Theorem` here means
/// the kernel **refused** a proof, not that a script gave up.
pub(super) fn declare_within_of_two_sided_le(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();

    let t_fv = d.fresh_fvar();
    let t = d.kernel().fvar(t_fv);
    let y_fv = d.fresh_fvar();
    let y = d.kernel().fvar(y_fv);

    let neg_t = cneg(d, p, t);
    let hyp1 = cle(d, p, t, y);
    let hyp2 = cle(d, p, neg_t, y);

    let h1_fv = d.fresh_fvar();
    let h1 = d.kernel().fvar(h1_fv);
    let h2_fv = d.fresh_fvar();
    let h2 = d.kernel().fvar(h2_fv);

    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);

    // `CReal.le` is a `Definition` (`le x y := ∀ n, seq x n − seq y n ≤
    // 2/(n+1)`), so `.apply(_, &[i])` unfolds it directly to the per-index
    // `Rat.le` fact -- the same idiom `geom_tail_within`'s own proof uses,
    // just at an arbitrary `i` rather than the tail's own canonical index.
    let h1_at_i = d.apply(h1, &[i]);
    let h2_at_i = d.apply(h2, &[i]);

    let u = sample(d, p, t, i);
    let v = sample(d, p, y, i);
    let w = div_succ(d, p, 2, i);

    let value_body = within_of_sub_le(d, p, u, v, w, h1_at_i, h2_at_i);

    let ty = {
        let vw = radd(d, v, w);
        let claim = within(d, p, u, vw);
        let inner = d.pi_fv(i_fv, nat, claim);
        // `h1_fv`/`h2_fv` escape into `inner` through `v`/`w` (via `y`/`i`),
        // and `t_fv`/`y_fv` escape through `hyp1`/`hyp2` -- all genuinely
        // dependent Pis (`pi_fv`), never `d.arrow`, the same trap
        // `geom_tail_within`'s own `ty` names.
        let with_h2 = d.pi_fv(h2_fv, hyp2, inner);
        let with_h1 = d.pi_fv(h1_fv, hyp1, with_h2);
        let with_y = d.pi_fv(y_fv, carrier, with_h1);
        d.pi_fv(t_fv, carrier, with_y)
    };
    let value = {
        let inner = d.lam_fv(i_fv, nat, value_body);
        let with_h2 = d.lam_fv(h2_fv, hyp2, inner);
        let with_h1 = d.lam_fv(h1_fv, hyp1, with_h2);
        let with_y = d.lam_fv(y_fv, carrier, with_h1);
        d.lam_fv(t_fv, carrier, with_y)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.within_of_two_sided_le,
        uparams: vec![],
        ty,
        value,
    })
}

// --- roadmap step 2: an abs-bound splits into a one-sided bound -----------

/// `CReal.le_add_of_abs_sub_le : ∀ x y : CReal, ∀ q : Rat, le (abs (add x
/// (neg y))) (ofRat q) → le x (add y (ofRat q))` — roadmap step 2 toward
/// `riemannSum_cauchy`: `close_within`'s own `abs`-bound shape (exactly what
/// `UniformlyContinuousOn.spec`'s conclusion and [`declare_fine_sample_close`]
/// produce) unfolds all the way down to the CReal-level one-sided form
/// `sumRange_le`'s pointwise hypothesis needs, rather than stopping at the
/// difference-only `le (add x (neg y)) (ofRat q)`.
///
/// Route: `le_abs_self` gives `d ≤ |d|` at `d := x + (-y)`; `le_trans`
/// against the hypothesis collapses that to `d ≤ q`; `add_le_add` adds `y`
/// on the left of both sides to get `y + d ≤ y + q`; and `add_sub_cancel`
/// (this file's own ring identity, `y + (x + (-y)) ~ x`) folds the left side
/// down to exactly `x` via `le_congr`.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` from a `Theorem` here means
/// the kernel **refused** a proof, not that a script gave up.
pub(super) fn declare_le_add_of_abs_sub_le(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let rat_carrier = rat_ty(d);

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let y_fv = d.fresh_fvar();
    let y = d.kernel().fvar(y_fv);
    let q_fv = d.fresh_fvar();
    let q = d.kernel().fvar(q_fv);

    let ny = cneg(d, p, y);
    let diff = cadd(d, p, x, ny); // x + (-y)
    let abs_diff = d.const_app(p.abs, &[diff]);
    let q_embed = embed(d, p, q);
    let hyp_ty = cle(d, p, abs_diff, q_embed);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    // self_le : le diff abs_diff.
    let self_le = d.lemma(p.le_abs_self, &[diff]);
    // d_le_q : le diff q_embed.
    let d_le_q = d.lemma(p.le_trans, &[diff, abs_diff, q_embed, self_le, h]);

    // grown : le (add y diff) (add y q_embed).
    let refl_y = d.lemma(p.le_refl, &[y]);
    let grown = d.lemma(p.add_le_add, &[y, y, diff, q_embed, refl_y, d_le_q]);

    // cancel : Equiv (add y diff) x -- exactly `add_sub_cancel(y, x)`'s own
    // conclusion, since `diff` IS `add x (neg y)`.
    let cancel = add_sub_cancel(d, p, y, x);

    let y_diff = cadd(d, p, y, diff);
    let yq = cadd(d, p, y, q_embed);
    let refl_yq = d.lemma(p.equiv_refl, &[yq]);
    let conclusion_proof = d.lemma(p.le_congr, &[y_diff, x, yq, yq, cancel, refl_yq, grown]);
    // conclusion_proof : le x yq.

    let ty = {
        let conclusion = cle(d, p, x, yq);
        let after_h = d.arrow(hyp_ty, conclusion);
        let over_q = d.pi_fv(q_fv, rat_carrier, after_h);
        let over_y = d.pi_fv(y_fv, carrier, over_q);
        d.pi_fv(x_fv, carrier, over_y)
    };
    let value = {
        let with_h = d.lam_fv(h_fv, hyp_ty, conclusion_proof);
        let over_q = d.lam_fv(q_fv, rat_carrier, with_h);
        let over_y = d.lam_fv(y_fv, carrier, over_q);
        d.lam_fv(x_fv, carrier, over_y)
    };

    d.kernel().add_declaration(Declaration::Theorem {
        name: p.le_add_of_abs_sub_le,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CReal.two_sided_of_abs_sub_le : ∀ x y : CReal, ∀ q : Rat, le (abs (add x
/// (neg y))) (ofRat q) → And (le x (add y (ofRat q))) (le y (add x (ofRat
/// q)))` — the full abs-splitting lemma the per-block Riemann sum fold's TWO
/// applications of `sumRange_le` (upper and lower) both need from a single
/// `close_within` fact, rather than calling [`declare_le_add_of_abs_sub_le`]
/// twice at swapped arguments (which would need the DIFFERENT hypothesis
/// `le (abs (add y (neg x))) (ofRat q)`, not what a `close_within x y q`
/// fact actually gives).
///
/// The first conjunct reuses [`CRealPrelude::le_add_of_abs_sub_le`] verbatim.
/// The second mirrors its route with `neg_le_abs` in place of `le_abs_self`
/// (`le (neg diff) (abs diff)` rather than `le diff (abs diff)`) and
/// [`diff_cancel_left`] in place of [`add_sub_cancel`] for the
/// add-rearrangement step.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` from a `Theorem` here means
/// the kernel **refused** a proof, not that a script gave up.
pub(super) fn declare_two_sided_of_abs_sub_le(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let rat_carrier = rat_ty(d);
    let logic = p.rat.int.logic;

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let y_fv = d.fresh_fvar();
    let y = d.kernel().fvar(y_fv);
    let q_fv = d.fresh_fvar();
    let q = d.kernel().fvar(q_fv);

    let ny = cneg(d, p, y);
    let diff = cadd(d, p, x, ny); // x + (-y)
    let ndiff = cneg(d, p, diff);
    let abs_diff = d.const_app(p.abs, &[diff]);
    let q_embed = embed(d, p, q);
    let hyp_ty = cle(d, p, abs_diff, q_embed);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let yq = cadd(d, p, y, q_embed);
    let xq = cadd(d, p, x, q_embed);

    // left : le x yq, by the already-declared theorem.
    let left = d.lemma(p.le_add_of_abs_sub_le, &[x, y, q, h]);

    // right : le y xq, the mirror via neg_le_abs.
    let right = {
        let neg_self_le = d.lemma(p.neg_le_abs, &[diff]); // le ndiff abs_diff
        let negd_le_q = d.lemma(p.le_trans, &[ndiff, abs_diff, q_embed, neg_self_le, h]);
        // negd_le_q : le ndiff q_embed

        let refl_x = d.lemma(p.le_refl, &[x]);
        let grown = d.lemma(p.add_le_add, &[x, x, ndiff, q_embed, refl_x, negd_le_q]);
        // grown : le (add x ndiff) xq

        let cancel = diff_cancel_left(d, p, x, y); // Equiv (add x ndiff) y
        let refl_xq = d.lemma(p.equiv_refl, &[xq]);
        let x_ndiff = cadd(d, p, x, ndiff);
        d.lemma(p.le_congr, &[x_ndiff, y, xq, xq, cancel, refl_xq, grown])
        // : le y xq
    };

    let left_ty = cle(d, p, x, yq);
    let right_ty = cle(d, p, y, xq);
    let conclusion_proof = and_intro(d, p, left_ty, right_ty, left, right);

    let ty = {
        let and_ty = d.const_app(logic.and, &[left_ty, right_ty]);
        let after_h = d.arrow(hyp_ty, and_ty);
        let over_q = d.pi_fv(q_fv, rat_carrier, after_h);
        let over_y = d.pi_fv(y_fv, carrier, over_q);
        d.pi_fv(x_fv, carrier, over_y)
    };
    let value = {
        let with_h = d.lam_fv(h_fv, hyp_ty, conclusion_proof);
        let over_q = d.lam_fv(q_fv, rat_carrier, with_h);
        let over_y = d.lam_fv(y_fv, carrier, over_q);
        d.lam_fv(x_fv, carrier, over_y)
    };

    d.kernel().add_declaration(Declaration::Theorem {
        name: p.two_sided_of_abs_sub_le,
        uparams: vec![],
        ty,
        value,
    })
}

// --- roadmap step 3: the per-block fold ------------------------------------

/// `le (mul x z) (mul y z)` from `le zero z` and `le x y` — the missing
/// "multiply by a nonneg constant on the RIGHT" direction;
/// `mul_le_mul_of_nonneg_left` only has the constant on the left, and
/// [`summand_fn`]'s own convention (`f(x)·Δ`, value first) needs the
/// constant on the right. Built from `mul_comm` plus
/// `mul_le_mul_of_nonneg_left`, the same reuse shape [`right_distrib`] uses
/// for `left_distrib`.
fn mul_le_mul_of_nonneg_right(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    x: ExprId,
    y: ExprId,
    z: ExprId,
    hz_nonneg: ExprId,
    hxy: ExprId,
) -> ExprId {
    let zx = cmul(d, p, z, x);
    let zy = cmul(d, p, z, y);
    let grown = d.lemma(p.mul_le_mul_of_nonneg_left, &[z, x, y, hz_nonneg, hxy]);
    // grown : le zx zy
    let xz = cmul(d, p, x, z);
    let yz = cmul(d, p, y, z);
    let c1 = d.lemma(p.mul_comm, &[z, x]); // Equiv zx xz
    let c2 = d.lemma(p.mul_comm, &[z, y]); // Equiv zy yz
    d.lemma(p.le_congr, &[zx, xz, zy, yz, c1, c2, grown])
    // : le xz yz
}

/// `fun _ : Nat => v` — a constant function of a `Nat` index. Reproduced
/// verbatim from `monotone.rs`'s private `const_fn` (that file is out of
/// scope for edits in this slice).
fn const_nat_fn(d: &mut IntDev<'_>, v: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let fv = d.fresh_fvar();
    d.lam_fv(fv, nat, v)
}

/// `Equiv (mul (ofNat (Nat.succ n)) (mul w delta_fine)) (mul w delta_m)`,
/// `delta_fine := mul delta_m (embed (Rat.natDivSucc 1 n))` — folding
/// `(succ n)` copies of a per-fine-piece constant `w·Δ_fine` back down to
/// `w·Δ_m` exactly, for every `w`. The same four-step
/// `mul_assoc`/`mul_comm`/`mul_assoc`/`mesh_count_width` shape
/// `monotone.rs`'s own Archimedean closing step uses (that file is out of
/// scope for edits, so this reproduces the shape rather than calling it),
/// generalized from a bound-specific `w` to an arbitrary one so
/// [`declare_fine_block_sum_close`] can call it twice — once at `w := F
/// base_i`, once at `w := embed (natDivSucc 1 e)` — instead of duplicating
/// the chain.
fn fold_block_term(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    w: ExprId,
    delta_m: ExprId,
    n: ExprId,
) -> ExprId {
    let one_nat = d.num(1);
    let frac_n_rat = d.const_app(p.rat.nat_div_succ, &[one_nat, n]);
    let frac_n = embed(d, p, frac_n_rat);
    let delta_fine = cmul(d, p, delta_m, frac_n);
    let sn = d.succ(n);
    // `sn_real` -- the CReal cast `ofNat (Nat.succ n)`; `sn` itself is a
    // `Nat` and every `mul` below needs its CReal embedding, exactly what
    // `mesh_count_width`'s own `ofNat (Nat.succ m)` is.
    let sn_real = d.const_app(p.of_nat, &[sn]);

    let w_delta_fine = cmul(d, p, w, delta_fine);
    let start = cmul(d, p, sn_real, w_delta_fine); // sn_real * (w * delta_fine)

    let sn_w = cmul(d, p, sn_real, w);
    let s1 = cmul(d, p, sn_w, delta_fine); // (sn_real * w) * delta_fine
    let h1 = {
        let assoc = d.lemma(p.mul_assoc, &[sn_real, w, delta_fine]); // Equiv s1 start
        d.lemma(p.equiv_symm, &[s1, start, assoc])
    };
    // h1 : Equiv start s1

    let w_sn = cmul(d, p, w, sn_real);
    let s2 = cmul(d, p, w_sn, delta_fine); // (w * sn_real) * delta_fine
    let h2 = {
        let comm = d.lemma(p.mul_comm, &[sn_real, w]); // Equiv sn_w w_sn
        let refl_df = d.lemma(p.equiv_refl, &[delta_fine]);
        d.lemma(
            p.mul_congr,
            &[sn_w, w_sn, delta_fine, delta_fine, comm, refl_df],
        )
    };
    // h2 : Equiv s1 s2

    let sn_delta_fine = cmul(d, p, sn_real, delta_fine);
    let s3 = cmul(d, p, w, sn_delta_fine); // w * (sn_real * delta_fine)
    let h3 = d.lemma(p.mul_assoc, &[w, sn_real, delta_fine]); // Equiv s2 s3

    // mesh : Equiv sn_delta_fine delta_m -- `mesh_count_width` at
    // `width := delta_m`, since `delta_fine` IS `mul delta_m frac_n`.
    let mesh = d.lemma(p.mesh_count_width, &[delta_m, n]);
    let target = cmul(d, p, w, delta_m); // w * delta_m
    let h4 = {
        let refl_w = d.lemma(p.equiv_refl, &[w]);
        d.lemma(p.mul_congr, &[w, w, sn_delta_fine, delta_m, refl_w, mesh])
    };
    // h4 : Equiv s3 target

    echain(d, p, start, &[(s1, h1), (s2, h2), (s3, h3), (target, h4)])
    // : Equiv start target
}

/// `CReal.fineBlockSum_close : ∀ F a b e m n i, le a b → UniformlyContinuousOn
/// F a b → Nat.le i m → Nat.le deep m → And (le blockSum (add coarseTerm
/// epsTerm)) (le coarseTerm (add blockSum epsTerm))`, `deep` the same
/// Archimedean threshold [`declare_fine_sample_close`] uses, and (with
/// `delta_m := mul (width_of a b) (embed (natDivSucc 1 m))`, `base_i :=
/// sample_point a delta_m i`, `delta_fine := mul delta_m (embed (natDivSucc
/// 1 n))`):
///
/// - `blockSum := sumRange (summand_fn F base_i delta_fine) (Nat.succ n)` —
///   the fine Riemann sub-sum over coarse block `i`'s own `Nat.succ n` fine
///   pieces (`summand_fn F base_i delta_fine j = mul (F (sample_point base_i
///   delta_fine j)) delta_fine`, and `sample_point base_i delta_fine j` IS
///   `declare_fine_sample_close`'s own `fine_j`).
/// - `coarseTerm := mul (F base_i) delta_m` — the single term `riemannSum`
///   itself would use at coarse index `i`.
/// - `epsTerm := mul (embed (Rat.natDivSucc 1 e)) delta_m` — the roadmap's
///   own `Δ_m · natDivSucc(1, e)`, commuted.
///
/// Roadmap step 3: bound each coarse block's fine sub-sum between `C(i) ±
/// Δ_m · natDivSucc(1, e)`, the per-block piece `riemannSum_cauchy`'s outer
/// fold (step 4) sums over all `Nat.succ m` blocks.
///
/// Route: per fine index `j < Nat.succ n`, [`declare_fine_sample_close`]
/// gives `close_within (F fine_j) (F base_i) (natDivSucc 1 e)`, and
/// [`declare_two_sided_of_abs_sub_le`] splits it into `le (F fine_j) (add
/// (F base_i) eps)` and `le (F base_i) (add (F fine_j) eps)`. Two
/// applications of `sumRange_le` (upper and lower) lift these, via
/// [`mul_le_mul_of_nonneg_right`] against `delta_fine` and `right_distrib`,
/// to `blockSum` against constant/near-constant sums; `sumRange_const` (and,
/// on the lower side, `sumRange_add`) collapse those, and [`fold_block_term`]
/// (applied twice — once at `w := F base_i`, once at `w := embed
/// (natDivSucc 1 e)`) folds the leftover `(succ n) · delta_fine` factor back
/// down to `delta_m`.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` from a `Theorem` here means
/// the kernel **refused** a proof, not that a script gave up.
pub(super) fn declare_fine_block_sum_close(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let f_ty = fn_ty(d, p);
    let logic = p.rat.int.logic;

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let e_fv = d.fresh_fvar();
    let e = d.kernel().fvar(e_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);

    let hab_ty = cle(d, p, a, b);
    let hab_fv = d.fresh_fvar();
    let hab = d.kernel().fvar(hab_fv);

    let u_ty = d.const_app(p.uniformly_continuous_on, &[f, a, b]);
    let u_fv = d.fresh_fvar();
    let u = d.kernel().fvar(u_fv);

    let hi_ty = d.le(i, m);
    let hi_fv = d.fresh_fvar();
    let hi = d.kernel().fvar(hi_fv);

    // deep, EXACTLY as `declare_fine_sample_close` computes it (same
    // Archimedean threshold `mesh_le_of_ge`/`fineSample_close` both use).
    let modulus_fn = d.const_app(p.uc_modulus, &[f, a, b, u]);
    let outer = d.apply(modulus_fn, &[e]);
    let width = width_of(d, p, a, b);
    let (c, magnitude, _width_le_mag) = direct_bound_le(d, p, width);
    let me = NatOps::mul(d, magnitude, outer);
    let deep = NatOps::add(d, me, c);
    let hge_ty = d.le(deep, m);
    let hge_fv = d.fresh_fvar();
    let hge = d.kernel().fvar(hge_fv);

    let (delta_m, delta_m_nonneg) = delta_nonneg_of(d, p, a, b, m, hab);
    let base_i = sample_point(d, p, a, delta_m, i);
    let fbase = d.apply(f, &[base_i]);

    let one_nat = d.num(1);
    let frac_n_rat = d.const_app(p.rat.nat_div_succ, &[one_nat, n]);
    let frac_n = embed(d, p, frac_n_rat);
    let delta_fine = cmul(d, p, delta_m, frac_n);
    let delta_fine_nonneg = {
        let fnn = frac_nonneg(d, p, n);
        d.lemma(p.mul_nonneg, &[delta_m, frac_n, delta_m_nonneg, fnn])
    };

    let eps_rat = d.const_app(p.rat.nat_div_succ, &[one_nat, e]);
    let eps_embed = embed(d, p, eps_rat);

    let sn = d.succ(n);
    // `sn_real` -- the CReal cast `ofNat (Nat.succ n)`, needed everywhere a
    // count of `Nat.succ n` fine pieces gets multiplied against a `CReal`
    // (see `fold_block_term`'s own note: `sn` itself is a `Nat`).
    let sn_real = d.const_app(p.of_nat, &[sn]);

    // block_summand j = mul (F (sample_point base_i delta_fine j)) delta_fine
    // -- `summand_fn`'s own convention, and `sample_point base_i delta_fine
    // j` IS `declare_fine_sample_close`'s own `fine_j`.
    let block_summand = summand_fn(d, p, f, base_i, delta_fine);
    let block_sum = d.const_app(p.sum_range, &[block_summand, sn]);

    let coarse_term = cmul(d, p, fbase, delta_m);
    let eps_term = cmul(d, p, eps_embed, delta_m);

    // --- upper : le block_sum (add coarse_term eps_term) -------------------
    let upper = {
        let w_upper = cadd(d, p, fbase, eps_embed);
        let per_term = cmul(d, p, w_upper, delta_fine);
        let const_upper_fn = const_nat_fn(d, per_term);

        let pointwise = {
            let j_fv = d.fresh_fvar();
            let j = d.kernel().fvar(j_fv);
            let hj_ty = d.lt(j, sn);
            let hj_fv = d.fresh_fvar();
            let hj = d.kernel().fvar(hj_fv);

            let hclose = d.const_app(
                p.fine_sample_close,
                &[f, a, b, e, m, n, i, j, hab, u, hi, hj, hge],
            );
            let fine_j = sample_point(d, p, base_i, delta_fine, j);
            let ffine = d.apply(f, &[fine_j]);
            let split = d.const_app(p.two_sided_of_abs_sub_le, &[ffine, fbase, eps_rat, hclose]);
            let fbase_eps = cadd(d, p, fbase, eps_embed);
            let ffine_eps = cadd(d, p, ffine, eps_embed);
            let upper_ty = cle(d, p, ffine, fbase_eps);
            let lower_ty = cle(d, p, fbase, ffine_eps);
            let upper_j = d.const_app(logic.and_left, &[upper_ty, lower_ty, split]);
            // upper_j : le ffine (add fbase eps_embed)

            let grown = mul_le_mul_of_nonneg_right(
                d,
                p,
                ffine,
                w_upper,
                delta_fine,
                delta_fine_nonneg,
                upper_j,
            );
            // grown : le (mul ffine delta_fine) (mul w_upper delta_fine)
            //       = le (block_summand j) per_term

            let applied = d.apply(block_summand, &[j]);
            let refl_applied = d.lemma(p.equiv_refl, &[applied]);
            let ffine_delta = cmul(d, p, ffine, delta_fine);
            let refl_target = d.lemma(p.equiv_refl, &[per_term]);
            let matched = d.lemma(
                p.le_congr,
                &[
                    ffine_delta,
                    applied,
                    per_term,
                    per_term,
                    refl_applied,
                    refl_target,
                    grown,
                ],
            );
            let inner = d.lam_fv(hj_fv, hj_ty, matched);
            d.lam_fv(j_fv, nat, inner)
        };

        let step_upper = d.lemma(
            p.sum_range_le,
            &[block_summand, const_upper_fn, sn, pointwise],
        );
        // step_upper : le block_sum (sumRange const_upper_fn sn)

        let sum_upper_const = d.lemma(p.sum_range_const, &[per_term, n]);
        // sum_upper_const : Equiv (sumRange const_upper_fn sn) (mul sn per_term)

        let sum_upper = d.const_app(p.sum_range, &[const_upper_fn, sn]);
        let sn_per_term = cmul(d, p, sn_real, per_term);
        let refl_block_sum = d.lemma(p.equiv_refl, &[block_sum]);
        let step1 = d.lemma(
            p.le_congr,
            &[
                block_sum,
                block_sum,
                sum_upper,
                sn_per_term,
                refl_block_sum,
                sum_upper_const,
                step_upper,
            ],
        );
        // step1 : le block_sum sn_per_term

        let fold = fold_block_term(d, p, w_upper, delta_m, n);
        // fold : Equiv sn_per_term (mul w_upper delta_m)

        let w_upper_delta_m = cmul(d, p, w_upper, delta_m);
        let step2 = d.lemma(
            p.le_congr,
            &[
                block_sum,
                block_sum,
                sn_per_term,
                w_upper_delta_m,
                refl_block_sum,
                fold,
                step1,
            ],
        );
        // step2 : le block_sum w_upper_delta_m

        let dist = right_distrib(d, p, fbase, eps_embed, delta_m);
        // dist : Equiv w_upper_delta_m (add coarse_term eps_term)
        let target = cadd(d, p, coarse_term, eps_term);
        d.lemma(
            p.le_congr,
            &[
                block_sum,
                block_sum,
                w_upper_delta_m,
                target,
                refl_block_sum,
                dist,
                step2,
            ],
        )
        // : le block_sum target
    };

    // --- lower : le coarse_term (add block_sum eps_term) -------------------
    let lower = {
        let fbase_delta_fine = cmul(d, p, fbase, delta_fine);
        let const_fbase_fn = const_nat_fn(d, fbase_delta_fine);

        let eps_delta_fine = cmul(d, p, eps_embed, delta_fine);
        let const_eps_fn = const_nat_fn(d, eps_delta_fine);

        let rhs_fn = {
            let j_fv = d.fresh_fvar();
            let j = d.kernel().fvar(j_fv);
            let fj = d.apply(block_summand, &[j]);
            let gj = d.apply(const_eps_fn, &[j]);
            let body = cadd(d, p, fj, gj);
            d.lam_fv(j_fv, nat, body)
        };

        let pointwise = {
            let j_fv = d.fresh_fvar();
            let j = d.kernel().fvar(j_fv);
            let hj_ty = d.lt(j, sn);
            let hj_fv = d.fresh_fvar();
            let hj = d.kernel().fvar(hj_fv);

            let hclose = d.const_app(
                p.fine_sample_close,
                &[f, a, b, e, m, n, i, j, hab, u, hi, hj, hge],
            );
            let fine_j = sample_point(d, p, base_i, delta_fine, j);
            let ffine = d.apply(f, &[fine_j]);
            let split = d.const_app(p.two_sided_of_abs_sub_le, &[ffine, fbase, eps_rat, hclose]);
            let fbase_eps = cadd(d, p, fbase, eps_embed);
            let ffine_eps = cadd(d, p, ffine, eps_embed);
            let upper_ty = cle(d, p, ffine, fbase_eps);
            let lower_ty = cle(d, p, fbase, ffine_eps);
            let lower_j = d.const_app(logic.and_right, &[upper_ty, lower_ty, split]);
            // lower_j : le fbase (add ffine eps_embed)

            let w_lower = cadd(d, p, ffine, eps_embed);
            let grown = mul_le_mul_of_nonneg_right(
                d,
                p,
                fbase,
                w_lower,
                delta_fine,
                delta_fine_nonneg,
                lower_j,
            );
            // grown : le fbase_delta_fine (mul w_lower delta_fine)

            let dist = right_distrib(d, p, ffine, eps_embed, delta_fine);
            // dist : Equiv (mul w_lower delta_fine) (add (mul ffine delta_fine)
            //   (mul eps_embed delta_fine)) = Equiv (...) (rhs_fn j)
            let refl_lhs = d.lemma(p.equiv_refl, &[fbase_delta_fine]);
            let w_lower_delta_fine = cmul(d, p, w_lower, delta_fine);
            let rhs_at_j = d.apply(rhs_fn, &[j]);
            let matched = d.lemma(
                p.le_congr,
                &[
                    fbase_delta_fine,
                    fbase_delta_fine,
                    w_lower_delta_fine,
                    rhs_at_j,
                    refl_lhs,
                    dist,
                    grown,
                ],
            );
            let inner = d.lam_fv(hj_fv, hj_ty, matched);
            d.lam_fv(j_fv, nat, inner)
        };

        let step_lower = d.lemma(p.sum_range_le, &[const_fbase_fn, rhs_fn, sn, pointwise]);
        // step_lower : le (sumRange const_fbase_fn sn) (sumRange rhs_fn sn)

        // LHS: sumRange const_fbase_fn sn ~ mul sn fbase_delta_fine ~ coarse_term.
        let lhs_const = d.lemma(p.sum_range_const, &[fbase_delta_fine, n]);
        let sn_fbase_delta_fine = cmul(d, p, sn_real, fbase_delta_fine);
        let lhs_fold = fold_block_term(d, p, fbase, delta_m, n);
        let sum_fbase = d.const_app(p.sum_range, &[const_fbase_fn, sn]);
        let lhs_chain = echain(
            d,
            p,
            sum_fbase,
            &[(sn_fbase_delta_fine, lhs_const), (coarse_term, lhs_fold)],
        );
        // lhs_chain : Equiv sum_fbase coarse_term

        // RHS: sumRange rhs_fn sn ~ add block_sum (sumRange const_eps_fn sn)
        //   ~ add block_sum eps_term.
        let sum_add = d.lemma(p.sum_range_add, &[block_summand, const_eps_fn, sn]);
        // sum_add : Equiv (sumRange rhs_fn sn) (add block_sum (sumRange
        //   const_eps_fn sn))  -- since `rhs_fn` IS `fun j => add
        //   (block_summand j) (const_eps_fn j)`.
        let sum_eps = d.const_app(p.sum_range, &[const_eps_fn, sn]);
        let add_block_sum_eps = cadd(d, p, block_sum, sum_eps);

        let eps_const = d.lemma(p.sum_range_const, &[eps_delta_fine, n]);
        let sn_eps_delta_fine = cmul(d, p, sn_real, eps_delta_fine);
        let eps_fold = fold_block_term(d, p, eps_embed, delta_m, n);
        let eps_chain = echain(
            d,
            p,
            sum_eps,
            &[(sn_eps_delta_fine, eps_const), (eps_term, eps_fold)],
        );
        // eps_chain : Equiv sum_eps eps_term

        let refl_block_sum = d.lemma(p.equiv_refl, &[block_sum]);
        let target = cadd(d, p, block_sum, eps_term);
        let sum_rhs_fn = d.const_app(p.sum_range, &[rhs_fn, sn]);
        let rhs_chain = {
            let step = d.lemma(
                p.add_congr,
                &[
                    block_sum,
                    block_sum,
                    sum_eps,
                    eps_term,
                    refl_block_sum,
                    eps_chain,
                ],
            );
            // step : Equiv add_block_sum_eps target
            echain(
                d,
                p,
                sum_rhs_fn,
                &[(add_block_sum_eps, sum_add), (target, step)],
            )
        };
        // rhs_chain : Equiv (sumRange rhs_fn sn) target

        d.lemma(
            p.le_congr,
            &[
                sum_fbase,
                coarse_term,
                sum_rhs_fn,
                target,
                lhs_chain,
                rhs_chain,
                step_lower,
            ],
        )
        // : le coarse_term target
    };

    let coarse_plus_eps = cadd(d, p, coarse_term, eps_term);
    let block_sum_plus_eps = cadd(d, p, block_sum, eps_term);
    let upper_ty = cle(d, p, block_sum, coarse_plus_eps);
    let lower_ty = cle(d, p, coarse_term, block_sum_plus_eps);
    let conclusion_proof = and_intro(d, p, upper_ty, lower_ty, upper, lower);

    let ty = {
        let and_ty = d.const_app(logic.and, &[upper_ty, lower_ty]);
        let after_hge = d.arrow(hge_ty, and_ty);
        let after_hi = d.arrow(hi_ty, after_hge);
        let after_u = d.pi_fv(u_fv, u_ty, after_hi);
        let after_hab = d.arrow(hab_ty, after_u);
        let over_i = d.pi_fv(i_fv, nat, after_hab);
        let over_n = d.pi_fv(n_fv, nat, over_i);
        let over_m = d.pi_fv(m_fv, nat, over_n);
        let over_e = d.pi_fv(e_fv, nat, over_m);
        let over_b = d.pi_fv(b_fv, carrier, over_e);
        let over_a = d.pi_fv(a_fv, carrier, over_b);
        d.pi_fv(f_fv, f_ty, over_a)
    };
    let value = {
        let with_hge = d.lam_fv(hge_fv, hge_ty, conclusion_proof);
        let with_hi = d.lam_fv(hi_fv, hi_ty, with_hge);
        let with_u = d.lam_fv(u_fv, u_ty, with_hi);
        let with_hab = d.lam_fv(hab_fv, hab_ty, with_u);
        let over_i = d.lam_fv(i_fv, nat, with_hab);
        let over_n = d.lam_fv(n_fv, nat, over_i);
        let over_m = d.lam_fv(m_fv, nat, over_n);
        let over_e = d.lam_fv(e_fv, nat, over_m);
        let over_b = d.lam_fv(b_fv, carrier, over_e);
        let over_a = d.lam_fv(a_fv, carrier, over_b);
        d.lam_fv(f_fv, f_ty, over_a)
    };

    d.kernel().add_declaration(Declaration::Theorem {
        name: p.fine_block_sum_close,
        uparams: vec![],
        ty,
        value,
    })
}

fn double_block(d: &mut IntDev<'_>, p: CRealPrelude, g: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let two = d.num(2);
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let two_i = NatOps::mul(d, two, i);
    let g0 = d.apply(g, &[two_i]);
    let s2i = d.succ(two_i);
    let g1 = d.apply(g, &[s2i]);
    let body = cadd(d, p, g0, g1);
    d.lam_fv(i_fv, nat, body)
}

/// `Equiv (sumRange g (Nat.mul 2 k)) (sumRange (double_block g) k)` — the
/// proof term, by induction on `k`.
///
/// `Nat.mul`/`Nat.add` are both `define_binary`, recursing on their SECOND
/// argument, and the literal `2` (`d.num(2)`) is a genuine `succ (succ
/// zero)` term (`NatOps::num`'s own definition, not an opaque numeral), so
/// `Nat.mul 2 (Nat.succ j)` reduces by pure defeq (delta+iota, no lemma) to
/// `Nat.succ (Nat.succ (Nat.mul 2 j))` — unfold `mul` once on `succ j`
/// (`define_binary`'s step equation) to `Nat.add (Nat.mul 2 j) 2`, then
/// unfold `add` twice on the literal `2`'s own two `succ`s. `sumRange`'s own
/// recursion then unfolds `sumRange g (succ (succ (mul 2 j)))` twice against
/// that same shape, so the only PROOF content needed is one `add_congr`
/// (lifting the induction hypothesis one `add` level in) and one
/// `add_assoc` (re-bracketing the trailing pair together) — no rewriting of
/// the `Nat` indices themselves.
fn sum_range_double_proof(d: &mut IntDev<'_>, p: CRealPrelude, g: ExprId, k: ExprId) -> ExprId {
    let grouped = double_block(d, p, g);
    let two = d.num(2);

    let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let two_x = NatOps::mul(d, two, x);
        let lhs = d.const_app(p.sum_range, &[g, two_x]);
        let rhs = d.const_app(p.sum_range, &[grouped, x]);
        equiv(d, p, lhs, rhs)
    };

    d.induct(
        &motive,
        &|d| {
            // motive(zero): both sides reduce (defeq) to `CReal.zero`.
            let zero_c = czero(d, p);
            d.lemma(p.equiv_refl, &[zero_c])
        },
        &|d, j, ih| {
            // ih : Equiv (sumRange g (mul 2 j)) (sumRange grouped j)
            // Goal (defeq unfolded): Equiv
            //   (add (add (sumRange g (mul 2 j)) (g (mul 2 j))) (g (succ (mul 2 j))))
            //   (add (sumRange grouped j) (add (g (mul 2 j)) (g (succ (mul 2 j)))))
            let two_j = NatOps::mul(d, two, j);
            let gj = d.apply(g, &[two_j]);
            let s2j = d.succ(two_j);
            let gj1 = d.apply(g, &[s2j]);

            let sum_g_2j = d.const_app(p.sum_range, &[g, two_j]);
            let sum_grouped_j = d.const_app(p.sum_range, &[grouped, j]);

            // h1 : Equiv (add sum_g_2j gj) (add sum_grouped_j gj)
            let refl_gj = d.lemma(p.equiv_refl, &[gj]);
            let h1 = d.lemma(p.add_congr, &[sum_g_2j, sum_grouped_j, gj, gj, ih, refl_gj]);

            // h2 : Equiv (add (add sum_g_2j gj) gj1) (add (add sum_grouped_j gj) gj1)
            let lhs1 = cadd(d, p, sum_g_2j, gj);
            let rhs1 = cadd(d, p, sum_grouped_j, gj);
            let refl_gj1 = d.lemma(p.equiv_refl, &[gj1]);
            let h2 = d.lemma(p.add_congr, &[lhs1, rhs1, gj1, gj1, h1, refl_gj1]);

            // h3 : Equiv (add (add sum_grouped_j gj) gj1) (add sum_grouped_j (add gj gj1))
            let h3 = d.lemma(p.add_assoc, &[sum_grouped_j, gj, gj1]);

            let start = cadd(d, p, lhs1, gj1);
            let lhs2 = cadd(d, p, rhs1, gj1);
            let rhs2 = {
                let inner = cadd(d, p, gj, gj1);
                cadd(d, p, sum_grouped_j, inner)
            };
            d.lemma(p.equiv_trans, &[start, lhs2, rhs2, h2, h3])
        },
        k,
    )
}

/// `CReal.sumRange_double : ∀ g k, Equiv (sumRange g (Nat.mul 2 k))
/// (sumRange (fun i => add (g (Nat.mul 2 i)) (g (Nat.succ (Nat.mul 2 i))))
/// k)`. See this section's own module documentation for what this is for
/// and precisely what is not yet built on top of it.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` from a `Theorem` here means
/// the kernel **refused** a proof, not that a script gave up.
pub(super) fn declare_sum_range_double(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = creal_ty(d, p);
    let fn_ty = d.arrow(nat, carrier);

    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);

    let proof = sum_range_double_proof(d, p, g, k);

    let ty = {
        let two = d.num(2);
        let two_k = NatOps::mul(d, two, k);
        let lhs = d.const_app(p.sum_range, &[g, two_k]);
        let grouped = double_block(d, p, g);
        let rhs = d.const_app(p.sum_range, &[grouped, k]);
        equiv(d, p, lhs, rhs)
    };
    let ty_full = {
        let over_k = d.pi_fv(k_fv, nat, ty);
        d.pi_fv(g_fv, fn_ty, over_k)
    };
    let value_full = {
        let over_k = d.lam_fv(k_fv, nat, proof);
        d.lam_fv(g_fv, fn_ty, over_k)
    };

    d.kernel().add_declaration(Declaration::Theorem {
        name: p.sum_range_double,
        uparams: vec![],
        ty: ty_full,
        value: value_full,
    })
}

// --- `CReal.ofNat_add` / `CReal.ofNat_mul` -- toward `riemannSum_cauchy` ---
//
// `CReal.sumRange_reblock`'s conclusion indexes the fine sum at the RAW
// global index `(succ n)*i + j`; comparing a coarse `riemannSum` block's
// single term against that block's `succ n` fine terms needs the LOCAL
// sample-point arithmetic `a + i*delta_m + j*delta_fine` instead (`delta_fine
// := delta_m * natDivSucc 1 n`, chosen so `(succ n)*delta_fine ~ delta_m` is
// exactly `CReal.mesh_count_width` at `(delta_m, n)` -- no new identity
// needed there). Bridging the two needs `CReal.ofNat` to commute with
// `Nat.add`/`Nat.mul`, which no existing lemma states. Both are direct, with
// no induction on either argument: `CReal.ofNat n := CReal.ofRat
// (Rat.natDivSucc n 0)`, so lifting `Rat.natDivSucc`'s own homomorphism facts
// at denominator index `0` (`RatPrelude::nat_div_succ_add`/`nat_div_succ_mul`,
// the latter already general in its SECOND denominator index, so `0` is just
// one instance) across `CReal.ofRat` via `CReal.ofRat_add`/`CReal.ofRat_mul`
// closes each in one step -- the same one-step-lift idiom
// [`nat_div_succ_inverse_pair_eq_one`] already uses `nat_div_succ_mul` for,
// above.

/// `CReal.ofNat_add : ∀ a b : Nat, Equiv (ofNat (Nat.add a b)) (add (ofNat a)
/// (ofNat b))`. See this section's own module documentation.
fn declare_of_nat_add(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let rat = p.rat;

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);

    let zero_nat = d.num(0);
    let rat_a = d.const_app(rat.nat_div_succ, &[a, zero_nat]);
    let rat_b = d.const_app(rat.nat_div_succ, &[b, zero_nat]);
    let of_nat_a = embed(d, p, rat_a); // defeq (ofNat a)
    let of_nat_b = embed(d, p, rat_b); // defeq (ofNat b)
    let sum_real = cadd(d, p, of_nat_a, of_nat_b);
    // The nicer, `CReal.ofNat`-headed form of `sum_real`, defeq to it (one
    // delta step each side), used only for the OUTWARD-facing `ty`/`value` so
    // the declared statement and its rendered type read `ofNat a`/`ofNat b`
    // rather than the unfolded `ofRat (natDivSucc a 0)` the internal rewrite
    // chain below works with.
    let of_nat_a_nice = d.const_app(p.of_nat, &[a]);
    let of_nat_b_nice = d.const_app(p.of_nat, &[b]);
    let sum_real_nice = cadd(d, p, of_nat_a_nice, of_nat_b_nice);

    // step1 : Equiv sum_real (ofRat (Rat.add rat_a rat_b))
    let step1 = d.lemma(p.of_rat_add, &[rat_a, rat_b]);

    let sum_rat = radd(d, rat_a, rat_b);
    let nat_sum = NatOps::add(d, a, b);
    let rat_target = d.const_app(rat.nat_div_succ, &[nat_sum, zero_nat]);
    // add_eq : Eq Rat sum_rat rat_target
    let add_eq = d.lemma(rat.nat_div_succ_add, &[a, b, zero_nat]);

    let rewritten = rat_eq_rewrite(d, sum_rat, rat_target, add_eq, step1, &|d, t| {
        let embedded = embed(d, p, t);
        equiv(d, p, sum_real, embedded)
    });
    // rewritten : Equiv sum_real (embed rat_target) -- defeq
    // Equiv sum_real_nice (ofNat nat_sum), since `sum_real ~defeq~ sum_real_nice`
    // and `embed rat_target ~defeq~ ofNat nat_sum`.
    let of_nat_sum = d.const_app(p.of_nat, &[nat_sum]);
    let flipped = d.lemma(p.equiv_symm, &[sum_real_nice, of_nat_sum, rewritten]);
    // flipped : Equiv of_nat_sum sum_real_nice

    let ty = {
        let concl = equiv(d, p, of_nat_sum, sum_real_nice);
        let over_b = d.pi_fv(b_fv, nat, concl);
        d.pi_fv(a_fv, nat, over_b)
    };
    let value = {
        let over_b = d.lam_fv(b_fv, nat, flipped);
        d.lam_fv(a_fv, nat, over_b)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.of_nat_add,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CReal.ofNat_mul : ∀ a b : Nat, Equiv (ofNat (Nat.mul a b)) (mul (ofNat a)
/// (ofNat b))`. See this section's own module documentation.
fn declare_of_nat_mul(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let rat = p.rat;

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);

    let zero_nat = d.num(0);
    let rat_a = d.const_app(rat.nat_div_succ, &[a, zero_nat]);
    let rat_b = d.const_app(rat.nat_div_succ, &[b, zero_nat]);
    let of_nat_a = embed(d, p, rat_a);
    let of_nat_b = embed(d, p, rat_b);
    let prod_real = cmul(d, p, of_nat_a, of_nat_b);
    // The nicer, `CReal.ofNat`-headed form, defeq to `prod_real` -- see
    // `declare_of_nat_add`'s identical comment above.
    let of_nat_a_nice = d.const_app(p.of_nat, &[a]);
    let of_nat_b_nice = d.const_app(p.of_nat, &[b]);
    let prod_real_nice = cmul(d, p, of_nat_a_nice, of_nat_b_nice);

    // step1 : Equiv prod_real (ofRat (Rat.mul rat_a rat_b))
    let step1 = d.lemma(p.of_rat_mul, &[rat_a, rat_b]);

    let prod_rat = rmul(d, rat_a, rat_b);
    let nat_prod = NatOps::mul(d, a, b);
    let rat_target = d.const_app(rat.nat_div_succ, &[nat_prod, zero_nat]);
    // mul_eq : Eq Rat prod_rat rat_target
    let mul_eq = d.lemma(rat.nat_div_succ_mul, &[a, b, zero_nat]);

    let rewritten = rat_eq_rewrite(d, prod_rat, rat_target, mul_eq, step1, &|d, t| {
        let embedded = embed(d, p, t);
        equiv(d, p, prod_real, embedded)
    });
    let of_nat_prod = d.const_app(p.of_nat, &[nat_prod]);
    let flipped = d.lemma(p.equiv_symm, &[prod_real_nice, of_nat_prod, rewritten]);

    let ty = {
        let concl = equiv(d, p, of_nat_prod, prod_real_nice);
        let over_b = d.pi_fv(b_fv, nat, concl);
        d.pi_fv(a_fv, nat, over_b)
    };
    let value = {
        let over_b = d.lam_fv(b_fv, nat, flipped);
        d.lam_fv(a_fv, nat, over_b)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.of_nat_mul,
        uparams: vec![],
        ty,
        value,
    })
}

/// Admit `CReal.ofNat_add` and `CReal.ofNat_mul`. See this section's own
/// module documentation for what they bridge toward `riemannSum_cauchy`.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` from a `Theorem` here means
/// the kernel **refused** a proof, not that a script gave up.
pub(super) fn declare_of_nat_hom(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    declare_of_nat_add(d, p)?;
    declare_of_nat_mul(d, p)
}

// --- the succ-shape bridge -- toward `riemannSum_cauchy`'s common refinement
//
// The refinement estimate `riemannSum_cauchy` needs bounds each fine sample
// point against its enclosing coarse sample via
// `CReal.UniformlyContinuousOn.spec`, and the domain-membership hypotheses
// that call needs (`a≤x, x≤b, a≤y, y≤b`) come from `riemannSum_sample_in_bounds`
// / `subdivisionPoint_in_bounds` -- both stated for a partition of a
// `Nat.succ`-shaped count (`Nat.lt i (Nat.succ m)` / `Nat.le i (Nat.succ m)`).
// The fine partition (each of the coarse partition's `Nat.succ n` pieces
// split into `Nat.succ m` further pieces) has total count `(Nat.succ
// n)·(Nat.succ m)`, which every fine index genuinely satisfies but not
// SYNTACTICALLY as `Nat.succ` of anything -- so calling either theorem there
// needs a bridge exhibiting the count in `Nat.succ _` shape.
//
// The needed identity is `(succ n)·(succ m) = succ (n·m + n + m)`,
// `m_prime := n·m + n + m`. [`succ_mul_succ`] below returns it in COMPUTED
// form (`m_prime : Nat` plus a proof), not as an `∃ m', succ m' = …`: both
// `riemannSum_sample_in_bounds` and `subdivisionPoint_in_bounds` take the
// subdivision count as a plain `Nat` DATA argument, used to build the CReal
// sample-point term itself (a `Type`-valued position), and `Exists.rec`
// eliminates only into `Prop` -- an existential witness could not be
// substituted there at all, only used inside an already-Prop-valued goal.
// This is exactly the trap this session's own briefing warned about: "a
// theorem admitted with a type nothing can use."

/// `(Nat.succ n) · (Nat.succ m) = Nat.succ ((n·m + n) + m)` — the succ-shape
/// bridge above, as a private proof-term builder (not a public
/// `CRealPrelude` declaration: this is pure `Nat` arithmetic, out of this
/// file's natural home, but per this session's scope constraints it is
/// landed here rather than in the shared `nat_prelude` — relocate on
/// request).
///
/// Proof: `Nat.succ_mul n (Nat.succ m) : Eq Nat (mul (succ n) (succ m)) (add
/// (mul n (succ m)) (succ m))`. `Nat.mul`/`Nat.add` both recurse on their
/// RIGHT argument (`Nat.mul_succ`/`Nat.add_succ` are `refl`, not induction),
/// so with `sm := succ m` already `succ`-shaped, `mul n sm` unfolds by pure
/// defeq to `add (mul n m) n`, and then `add (add (mul n m) n) sm` unfolds
/// by pure defeq to `succ (add (add (mul n m) n) m)` — i.e. `succ m_prime`.
/// So `Nat.succ_mul`'s own proof term, with NO further rewrite or congruence
/// step, already has the stronger stated type up to the kernel's conversion
/// check; this returns that proof term unchanged.
///
/// Returns `(m_prime, proof)`, `proof : Eq Nat (mul (succ n) (succ m)) (succ
/// m_prime)`, `m_prime := add (add (mul n m) n) m`.
fn succ_mul_succ(d: &mut IntDev<'_>, n: ExprId, m: ExprId) -> (ExprId, ExprId) {
    let np = d.prelude();
    let sm = d.succ(m);
    let nm = NatOps::mul(d, n, m);
    let nm_n = d.const_app(np.add, &[nm, n]);
    let m_prime = d.const_app(np.add, &[nm_n, m]);
    let proof = d.lemma(np.succ_mul, &[n, sm]);
    (m_prime, proof)
}

/// `CReal.meshReciprocalMul : ∀ n m : Nat,
/// Eq Rat (Rat.mul (Rat.natDivSucc 1 n) (Rat.natDivSucc 1 m))
///        (Rat.natDivSucc 1 (Nat.add (Nat.add (Nat.mul n m) n) m))` —
/// refining a partition of `succ m` coarse pieces into `succ n` further
/// pieces each gives a fine mesh factor `1/(n+1) · 1/(m+1)` EXACTLY equal
/// (not merely close) to the single-partition factor `1/(m_prime+1)`,
/// `m_prime := ((n·m)+n)+m` — [`succ_mul_succ`]'s own witness, chosen
/// exactly so `Nat.succ m_prime` is definitionally `(Nat.succ n)·(Nat.succ
/// m)`. The reciprocal-mesh multiplicativity `riemannSum_cauchy`'s common
/// refinement needs, toward reconciling `sumRange_reblock`'s RAW global fine
/// index against `riemannSum`'s own per-block sample-point arithmetic (see
/// this module's own documentation).
///
/// Route: `Rat.natDivSucc k j := normalize (ofNat k) (succ j) _`
/// definitionally, so `Rat.mul (natDivSucc 1 n) (natDivSucc 1 m)` unfolds to
/// `normalize (ofNat 1) (succ n) _ · normalize (ofNat 1) (succ m) _`, and
/// [`RatPrelude::normalize_mul_normalize`] gives this equal to `normalize
/// (Int.mul (ofNat 1) (ofNat 1)) (Nat.mul (succ n) (succ m)) _`.
///
/// **`Nat.mul (succ n) (succ m)` does NOT ι-reduce to `succ m_prime` on its
/// own, and a first version of this declaration assumed it did.** `Nat.mul`
/// recurses on its RIGHT argument, so `mul (succ n) (succ m)` unfolds (right
/// argument `succ m` is succ-shaped) to `add (mul (succ n) m) (succ n)` —
/// STUCK at `mul (succ n) m`, a mul with `succ n` (not `n`) on the left,
/// which cannot reduce further since ITS right argument `m` is symbolic.
/// `Nat.succ_mul`, which [`succ_mul_succ`] actually calls, avoids this by
/// peeling the `succ` off the LEFT via an explicit induction-proved theorem
/// FIRST (`mul (succ n) sm = add (mul n sm) sm`, `sm := succ m`), and only
/// the resulting `add (mul n sm) sm` — with `n` (not `succ n`) inside the
/// inner `mul` — unfolds the rest of the way to `succ m_prime` by pure
/// defeq. So `Nat.mul (succ n) (succ m)` and `succ m_prime` are
/// PROPOSITIONALLY equal (via [`succ_mul_succ`]'s own witness, valid at
/// that stronger type for the same reason its own smoke tests confirm) but
/// NOT definitionally equal, and the two must be bridged by an explicit
/// rewrite: `Int.mul (ofNat 1) (ofNat 1)` ι-reduces to `ofNat 1` on its own
/// (both factors are the CONCRETE literal `1`, so `Nat.mul 1 1` fully
/// computes with no symbolic subterm — this half needs no bridge), lifted
/// to `Eq Int` via [`IntDev::nat_eq_to_int`] multiplying through by
/// `ofNat 1`, and [`RatPrelude::normalize_congr`] (cross-multiplication
/// based, so it needs no defeq between the two denominators at all) closes
/// the gap between `normalize (Int.mul (ofNat 1) (ofNat 1)) (Nat.mul (succ
/// n) (succ m)) _` and the declared `natDivSucc 1 m_prime`.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` from a `Theorem` here means
/// the kernel **refused** a proof, not that a script gave up.
pub(super) fn declare_mesh_reciprocal_mul(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);

    let one_nat = d.num(1);
    let n1 = d.of_nat(one_nat);
    let sn = d.succ(n);
    let sm = d.succ(m);
    let h1 = one_le_succ(d, n);
    let h2 = one_le_succ(d, m);

    let proof = d.lemma(p.rat.normalize_mul_normalize, &[n1, sn, h1, n1, sm, h2]);
    // proof : Eq Rat (natDivSucc 1 n * natDivSucc 1 m)
    //                (normalize (Int.mul n1 n1) (Nat.mul sn sm) pos1)

    let (m_prime, succ_proof) = succ_mul_succ(d, n, m);
    let sm_prime = d.succ(m_prime);

    // `mul_sn_sm` MUST be built the same way `normalize_mul_normalize`'s own
    // conclusion computes its denominator (`NatOps::mul(e1, e2)`), so it is
    // syntactically the SAME term `proof`'s actual type already mentions,
    // not merely an equal one.
    let mul_sn_sm = NatOps::mul(d, sn, sm);

    // `succ_proof`'s ACTUAL type is `Eq Nat (mul sn sm) (add (add (mul n m)
    // n) m)`; its RHS reduces by pure defeq to `Nat.succ m_prime` (`Nat.add`
    // unfolding once on its own succ-shaped right argument) -- see
    // `succ_mul_succ`'s doc and this declaration's own doc for why the LHS
    // needs no reduction at all (same literal term). So `succ_proof` is
    // directly usable at the stronger type `Eq Nat mul_sn_sm sm_prime`.
    let nat_bridge = succ_proof;

    // step : Eq Int (n1 * ofNat mul_sn_sm) (n1 * ofNat sm_prime), lifting
    // `nat_bridge` to `Int` by multiplying both sides by `n1`.
    let step = d.nat_eq_to_int(mul_sn_sm, sm_prime, nat_bridge, &|d, t| {
        let ot = d.of_nat(t);
        d.imul(n1, ot)
    });
    let of_mul_sn_sm = d.of_nat(mul_sn_sm);
    let of_sm_prime = d.of_nat(sm_prime);
    let lhs_int = d.imul(n1, of_mul_sn_sm);
    let rhs_int = d.imul(n1, of_sm_prime);
    // cross_eq : Eq Int (n1 * ofNat sm_prime) (n1 * ofNat mul_sn_sm) --
    // `normalize_congr`'s own cross-multiplication shape at
    // (n1' := Int.mul n1 n1, d1' := mul_sn_sm, n2' := n1, d2' := sm_prime),
    // since `Int.mul n1 n1` is DEFEQ `n1` (both factors the concrete literal
    // `ofNat 1`, so `Nat.mul 1 1` fully computes -- unlike `Nat.mul sn sm`,
    // symbolic in `n, m`).
    let cross_eq = d.isymm(lhs_int, rhs_int, step);

    let pos1 = d.lemma(p.rat.int.nat.one_le_mul, &[sn, sm, h1, h2]);
    let pos2 = one_le_succ(d, m_prime);
    let n1_n1 = d.imul(n1, n1);

    let bridge = d.lemma(
        p.rat.normalize_congr,
        &[n1_n1, mul_sn_sm, pos1, n1, sm_prime, pos2, cross_eq],
    );
    // bridge : Eq Rat (normalize n1_n1 mul_sn_sm pos1) (normalize n1 sm_prime pos2)

    let dn = d.const_app(p.rat.nat_div_succ, &[one_nat, n]);
    let dm = d.const_app(p.rat.nat_div_succ, &[one_nat, m]);
    let lhs_nice = rmul(d, dn, dm);
    let mid = normalize(d, n1_n1, mul_sn_sm, pos1);
    let rhs_nice = d.const_app(p.rat.nat_div_succ, &[one_nat, m_prime]);

    let full_proof = rtrans(d, lhs_nice, mid, rhs_nice, proof, bridge);
    let stmt = req(d, lhs_nice, rhs_nice);

    let ty = {
        let over_m = d.pi_fv(m_fv, nat, stmt);
        d.pi_fv(n_fv, nat, over_m)
    };
    let value = {
        let over_m = d.lam_fv(m_fv, nat, full_proof);
        d.lam_fv(n_fv, nat, over_m)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.mesh_reciprocal_mul,
        uparams: vec![],
        ty,
        value,
    })
}

// --- roadmap step 1: bridging the global fine index to the local block
// sample point ---------------------------------------------------------
//
// `CReal.sumRange_reblock` sums an arbitrary `g` at the RAW global index
// `(succ n)*i + j`; `CReal.fineBlockSum_close` (roadmap step 3) folds a sum
// over the LOCAL fine index `j`, sampled off the coarse block's own point
// `base_i`. Gluing the two needs `F` applied to two sample points that are
// only `Equiv`, not syntactically equal (this file's own module
// documentation flags exactly this gap). This section proves that bridge as
// an UNCONDITIONAL identity -- no bound on `i`/`j` needed at all, unlike
// every other roadmap step, which all need `i ≤ m`/`j < Nat.succ n` to place
// a sample point in `[a, b]`: the two points denote the same real number
// regardless of which fine sub-index or which coarse block, purely from
// `ofNat_add`/`ofNat_mul` distributing the index arithmetic and
// `mesh_count_width` cancelling the `Nat.succ n` factor `meshReciprocalMul`
// introduces.

/// `Equiv delta_m_prime delta_fine`. `delta_m_prime := mul width (embed
/// (Rat.natDivSucc 1 m_prime))` is the mesh at the REFINED count `Nat.succ
/// m_prime`; `delta_fine := mul (mul width (embed (Rat.natDivSucc 1 m)))
/// (embed (Rat.natDivSucc 1 n))` is the coarse mesh `width *
/// natDivSucc(1,m)` split into `Nat.succ n` further pieces -- the EXACT (not
/// merely close) mesh identity `CReal.meshReciprocalMul`
/// gives at the rational level, lifted to `CReal` by `CReal.ofRat_mul` and
/// reassociated to `delta_fine`'s own bracketing. `m_prime` is not
/// constrained here to equal `((n·m)+n)+m` syntactically -- the caller
/// supplies whatever `m_prime` [`succ_mul_succ`] returned, matching
/// `CReal.meshReciprocalMul`'s own conclusion at that same witness.
///
/// Route: `Rat.mul_comm` turns `meshReciprocalMul`'s own `natDivSucc 1 n *
/// natDivSucc 1 m` into the order `delta_fine`'s bracketing needs
/// (`natDivSucc 1 m * natDivSucc 1 n`) via one `Eq Rat` transitivity step;
/// `rat_eq_rewrite` then rewrites a `CReal.Equiv` built from
/// `CReal.ofRat_mul` (turning `embed (mul frac_m frac_n)` into `mul (embed
/// frac_m) (embed frac_n)`) and `mul_assoc` (re-bracketing `width *
/// (frac_m * frac_n)` to `(width * frac_m) * frac_n`, i.e. `delta_m *
/// frac_n`) along that identity.
fn mesh_reblock_delta_eq(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    width: ExprId,
    n: ExprId,
    m: ExprId,
    m_prime: ExprId,
) -> (ExprId, ExprId, ExprId) {
    let one_nat = d.num(1);
    let frac_m = d.const_app(p.rat.nat_div_succ, &[one_nat, m]);
    let frac_n = d.const_app(p.rat.nat_div_succ, &[one_nat, n]);
    let frac_m_prime = d.const_app(p.rat.nat_div_succ, &[one_nat, m_prime]);
    let embed_frac_m = embed(d, p, frac_m);
    let embed_frac_n = embed(d, p, frac_n);
    let delta_m = cmul(d, p, width, embed_frac_m);
    let delta_fine = cmul(d, p, delta_m, embed_frac_n);
    let embed_frac_m_prime = embed(d, p, frac_m_prime);
    let delta_m_prime = cmul(d, p, width, embed_frac_m_prime);

    // h_comm : Eq Rat (mul frac_m frac_n) (mul frac_n frac_m)
    let h_comm = d.lemma(p.rat.mul_comm, &[frac_m, frac_n]);
    // h_recip : Eq Rat (mul frac_n frac_m) frac_m_prime
    let h_recip = d.lemma(p.mesh_reciprocal_mul, &[n, m]);
    let mul_fm_fn = rmul(d, frac_m, frac_n);
    let mul_fn_fm = rmul(d, frac_n, frac_m);
    // h_recip_prime : Eq Rat (mul frac_m frac_n) frac_m_prime
    let h_recip_prime = rtrans(d, mul_fm_fn, mul_fn_fm, frac_m_prime, h_comm, h_recip);

    // pre : Equiv (mul width (embed (mul frac_m frac_n))) delta_fine
    let pre = {
        let embed_prod = embed(d, p, mul_fm_fn);
        let mid_inner = cmul(d, p, embed_frac_m, embed_frac_n);
        // of_rat_mul_step : Equiv mid_inner embed_prod
        let of_rat_mul_step = d.lemma(p.of_rat_mul, &[frac_m, frac_n]);
        // step1 : Equiv embed_prod mid_inner
        let step1 = d.lemma(p.equiv_symm, &[mid_inner, embed_prod, of_rat_mul_step]);
        let refl_width = d.lemma(p.equiv_refl, &[width]);
        let mid = cmul(d, p, width, mid_inner);
        let lhs = cmul(d, p, width, embed_prod);
        // h_a : Equiv lhs mid
        let h_a = d.lemma(
            p.mul_congr,
            &[width, width, embed_prod, mid_inner, refl_width, step1],
        );
        // assoc : Equiv delta_fine mid
        let assoc = d.lemma(p.mul_assoc, &[width, embed_frac_m, embed_frac_n]);
        // h_b : Equiv mid delta_fine
        let h_b = d.lemma(p.equiv_symm, &[delta_fine, mid, assoc]);
        echain(d, p, lhs, &[(mid, h_a), (delta_fine, h_b)])
    };

    let motive = |d: &mut IntDev<'_>, t: ExprId| -> ExprId {
        let embedded = embed(d, p, t);
        let lhs = cmul(d, p, width, embedded);
        equiv(d, p, lhs, delta_fine)
    };
    // proof : Equiv delta_m_prime delta_fine
    let proof = rat_eq_rewrite(d, mul_fm_fn, frac_m_prime, h_recip_prime, pre, &motive);
    (delta_m_prime, delta_fine, proof)
}

/// `(lhs, rhs, proof)` for `CReal.samplePoint_reblock` at `a, b, n, m, i, j`
/// -- see [`declare_sample_point_reblock`]'s own doc comment for the full
/// statement. Built entirely from EXPLICIT congruence/associativity/
/// commutativity steps (never relying on the two sides merely being
/// defeq-shaped alike): every reassociation the derivation needs
/// (`mul_assoc`/`mul_comm` moving the `Nat.succ n` factor across, `add_assoc`
/// re-bracketing the two summands) is its own named lemma application, so
/// this builds identically whether `a, b, n, m, i, j` are free variables (as
/// [`declare_sample_point_reblock`] itself uses) or ground literals (as the
/// concrete instantiation test below uses) -- the exact distinction the
/// session's own caution about symbolic-vs-concrete defects warns is not
/// automatic.
fn sample_point_reblock_proof(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    a: ExprId,
    b: ExprId,
    n: ExprId,
    m: ExprId,
    i: ExprId,
    j: ExprId,
) -> (ExprId, ExprId, ExprId) {
    let width = width_of(d, p, a, b);
    let (m_prime, _succ_proof) = succ_mul_succ(d, n, m);
    let (delta_m_prime, delta_fine, delta_eq) = mesh_reblock_delta_eq(d, p, width, n, m, m_prime);
    let delta_m = delta_of(d, p, a, b, m);
    let base_i = sample_point(d, p, a, delta_m, i);

    let sn = d.succ(n);
    let sn_i = NatOps::mul(d, sn, i);
    let global_idx = NatOps::add(d, sn_i, j);

    let of_nat_sn = d.const_app(p.of_nat, &[sn]);
    let of_nat_i = d.const_app(p.of_nat, &[i]);
    let of_nat_j = d.const_app(p.of_nat, &[j]);
    let of_nat_sn_i = d.const_app(p.of_nat, &[sn_i]);
    let of_nat_global = d.const_app(p.of_nat, &[global_idx]);

    let lhs = sample_point(d, p, a, delta_m_prime, global_idx);
    let rhs = sample_point(d, p, base_i, delta_fine, j);

    let mul_sn_i_term = cmul(d, p, of_nat_sn, of_nat_i);
    let ofnat_split = cadd(d, p, mul_sn_i_term, of_nat_j);
    let term_i_part = cmul(d, p, mul_sn_i_term, delta_m_prime);
    let term_j_part = cmul(d, p, of_nat_j, delta_m_prime);
    let sum_parts = cadd(d, p, term_i_part, term_j_part);
    let mul_i_dm = cmul(d, p, of_nat_i, delta_m);
    let mul_j_fine = cmul(d, p, of_nat_j, delta_fine);
    let target_sum = cadd(d, p, mul_i_dm, mul_j_fine);
    let mul_global_dmp = cmul(d, p, of_nat_global, delta_m_prime);
    let mul_split_dmp = cmul(d, p, ofnat_split, delta_m_prime);
    let a_mul_split_dmp = cadd(d, p, a, mul_split_dmp);
    let a_sum_parts = cadd(d, p, a, sum_parts);
    let a_target_sum = cadd(d, p, a, target_sum);

    // Step A : Equiv of_nat_global ofnat_split -- `ofNat_add`/`ofNat_mul`
    // splitting the global index into its block/offset shape.
    let h_ofnat_global = {
        let mid = cadd(d, p, of_nat_sn_i, of_nat_j);
        let step1 = d.lemma(p.of_nat_add, &[sn_i, j]);
        let step2 = d.lemma(p.of_nat_mul, &[sn, i]);
        let refl_j = d.lemma(p.equiv_refl, &[of_nat_j]);
        let h_add = d.lemma(
            p.add_congr,
            &[
                of_nat_sn_i,
                mul_sn_i_term,
                of_nat_j,
                of_nat_j,
                step2,
                refl_j,
            ],
        );
        echain(d, p, of_nat_global, &[(mid, step1), (ofnat_split, h_add)])
    };

    // Step B : Equiv lhs a_mul_split_dmp.
    let lhs_step1 = {
        let refl_dmp = d.lemma(p.equiv_refl, &[delta_m_prime]);
        let h_mul = d.lemma(
            p.mul_congr,
            &[
                of_nat_global,
                ofnat_split,
                delta_m_prime,
                delta_m_prime,
                h_ofnat_global,
                refl_dmp,
            ],
        );
        let refl_a = d.lemma(p.equiv_refl, &[a]);
        d.lemma(
            p.add_congr,
            &[a, a, mul_global_dmp, mul_split_dmp, refl_a, h_mul],
        )
    };

    // Step C : Equiv a_mul_split_dmp a_sum_parts, via `right_distrib`.
    let lhs_step2 = {
        let dist = right_distrib(d, p, mul_sn_i_term, of_nat_j, delta_m_prime);
        let refl_a = d.lemma(p.equiv_refl, &[a]);
        d.lemma(p.add_congr, &[a, a, mul_split_dmp, sum_parts, refl_a, dist])
    };

    // Step D1 : Equiv term_j_part mul_j_fine, via the mesh identity.
    let h_j = {
        let refl_j = d.lemma(p.equiv_refl, &[of_nat_j]);
        d.lemma(
            p.mul_congr,
            &[
                of_nat_j,
                of_nat_j,
                delta_m_prime,
                delta_fine,
                refl_j,
                delta_eq,
            ],
        )
    };

    // Step D2 : Equiv term_i_part mul_i_dm, via `mul_comm`/`mul_assoc`
    // moving the `Nat.succ n` factor across to meet `mesh_count_width`.
    let h_i = {
        let comm_si = d.lemma(p.mul_comm, &[of_nat_sn, of_nat_i]);
        let mul_i_sn = cmul(d, p, of_nat_i, of_nat_sn);
        let refl_dmp = d.lemma(p.equiv_refl, &[delta_m_prime]);
        let step_a = d.lemma(
            p.mul_congr,
            &[
                mul_sn_i_term,
                mul_i_sn,
                delta_m_prime,
                delta_m_prime,
                comm_si,
                refl_dmp,
            ],
        );
        let mul_i_sn_dmp = cmul(d, p, mul_i_sn, delta_m_prime);

        let step_b = d.lemma(p.mul_assoc, &[of_nat_i, of_nat_sn, delta_m_prime]);
        let inner_sn_dmp = cmul(d, p, of_nat_sn, delta_m_prime);
        let target_b = cmul(d, p, of_nat_i, inner_sn_dmp);

        let refl_sn = d.lemma(p.equiv_refl, &[of_nat_sn]);
        let step_c = d.lemma(
            p.mul_congr,
            &[
                of_nat_sn,
                of_nat_sn,
                delta_m_prime,
                delta_fine,
                refl_sn,
                delta_eq,
            ],
        );
        let inner_sn_fine = cmul(d, p, of_nat_sn, delta_fine);
        let refl_i = d.lemma(p.equiv_refl, &[of_nat_i]);
        let step_c_lift = d.lemma(
            p.mul_congr,
            &[
                of_nat_i,
                of_nat_i,
                inner_sn_dmp,
                inner_sn_fine,
                refl_i,
                step_c,
            ],
        );
        let target_c = cmul(d, p, of_nat_i, inner_sn_fine);

        // mesh : Equiv inner_sn_fine delta_m -- `mesh_count_width(delta_m, n)`,
        // since `inner_sn_fine` is EXACTLY `mul (ofNat (succ n)) (mul delta_m
        // (embed (natDivSucc 1 n)))` up to argument order.
        let mesh = d.lemma(p.mesh_count_width, &[delta_m, n]);
        let step_d = d.lemma(
            p.mul_congr,
            &[of_nat_i, of_nat_i, inner_sn_fine, delta_m, refl_i, mesh],
        );

        echain(
            d,
            p,
            term_i_part,
            &[
                (mul_i_sn_dmp, step_a),
                (target_b, step_b),
                (target_c, step_c_lift),
                (mul_i_dm, step_d),
            ],
        )
    };

    // Step E : Equiv sum_parts target_sum.
    let h_split = d.lemma(
        p.add_congr,
        &[term_i_part, mul_i_dm, term_j_part, mul_j_fine, h_i, h_j],
    );

    // Step F : Equiv a_sum_parts a_target_sum.
    let lhs_step3 = {
        let refl_a = d.lemma(p.equiv_refl, &[a]);
        d.lemma(p.add_congr, &[a, a, sum_parts, target_sum, refl_a, h_split])
    };

    // Step G : Equiv a_target_sum rhs, via `add_assoc(a, mul_i_dm,
    // mul_j_fine)` -- `base_i` is EXACTLY `add a mul_i_dm`, so `add base_i
    // mul_j_fine` is EXACTLY `rhs`, with no further rewrite needed.
    let g_step = {
        let assoc = d.lemma(p.add_assoc, &[a, mul_i_dm, mul_j_fine]);
        d.lemma(p.equiv_symm, &[rhs, a_target_sum, assoc])
    };

    let proof = echain(
        d,
        p,
        lhs,
        &[
            (a_mul_split_dmp, lhs_step1),
            (a_sum_parts, lhs_step2),
            (a_target_sum, lhs_step3),
            (rhs, g_step),
        ],
    );

    (lhs, rhs, proof)
}

/// `CReal.samplePoint_reblock : ∀ a b : CReal, ∀ n m i j : Nat, Equiv
/// (sample_point a delta_m_prime globalIdx) (sample_point base_i delta_fine
/// j)`, `delta_m_prime := mul (add b (neg a)) (embed (Rat.natDivSucc 1
/// m_prime))`, `m_prime := ((n·m)+n)+m` ([`succ_mul_succ`]'s own witness,
/// `Nat.succ m_prime` definitionally `(Nat.succ n)·(Nat.succ m)`),
/// `globalIdx := Nat.add (Nat.mul (Nat.succ n) i) j` (EXACTLY
/// `CReal.sumRange_reblock`'s own global fine index at block size `Nat.succ
/// n`, block index `i`), `base_i := sample_point a delta_m i`, `delta_m :=
/// mul (add b (neg a)) (embed (Rat.natDivSucc 1 m))`, `delta_fine := mul
/// delta_m (embed (Rat.natDivSucc 1 n))` (EXACTLY `CReal.fineSample_close`'s
/// own `fine_j`'s mesh at that same block).
///
/// This is roadmap step 1 toward `riemannSum_cauchy`'s common refinement:
/// `sumRange_reblock`'s conclusion applies an arbitrary `g` to the RAW
/// global index, while `fineBlockSum_close`'s own per-block sum applies `F`
/// at the LOCAL `base_i`/fine-offset arithmetic -- gluing the two needs
/// knowing these two sample points are the SAME real number. An
/// UNCONDITIONAL identity: no bound on `i`/`j` is needed at all, unlike
/// every other roadmap step (all of which place a sample point in `[a, b]`
/// and so need `i ≤ m`/`j < Nat.succ n`).
///
/// Route: [`mesh_reblock_delta_eq`] gives the exact mesh identity `delta_m_prime
/// ~ delta_fine` from `CReal.meshReciprocalMul`; `CReal.ofNat_add`/`ofNat_mul`
/// split `globalIdx` into `(Nat.succ n)*i + j`'s `CReal` shape;
/// `right_distrib` distributes the resulting sum times `delta_m_prime`;
/// `mul_comm`/`mul_assoc` move the `Nat.succ n` factor next to `delta_fine`
/// so `CReal.mesh_count_width` cancels it down to `delta_m`; `add_assoc`
/// closes the gap between the two additive re-groupings. See this file's own
/// module documentation and this section's header comment.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` from a `Theorem` here means
/// the kernel **refused** a proof, not that a script gave up.
pub(super) fn declare_sample_point_reblock(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let j_fv = d.fresh_fvar();
    let j = d.kernel().fvar(j_fv);

    let (lhs, rhs, proof) = sample_point_reblock_proof(d, p, a, b, n, m, i, j);
    let concl = equiv(d, p, lhs, rhs);

    let ty = {
        let over_j = d.pi_fv(j_fv, nat, concl);
        let over_i = d.pi_fv(i_fv, nat, over_j);
        let over_m = d.pi_fv(m_fv, nat, over_i);
        let over_n = d.pi_fv(n_fv, nat, over_m);
        let over_b = d.pi_fv(b_fv, carrier, over_n);
        d.pi_fv(a_fv, carrier, over_b)
    };
    let value = {
        let with_j = d.lam_fv(j_fv, nat, proof);
        let with_i = d.lam_fv(i_fv, nat, with_j);
        let with_m = d.lam_fv(m_fv, nat, with_i);
        let with_n = d.lam_fv(n_fv, nat, with_m);
        let with_b = d.lam_fv(b_fv, carrier, with_n);
        d.lam_fv(a_fv, carrier, with_b)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.sample_point_reblock,
        uparams: vec![],
        ty,
        value,
    })
}

#[cfg(test)]
mod sample_point_reblock_tests {
    use super::*;
    use crate::Declaration;
    use crate::rat_prelude::ops::{req, rrefl};

    /// **Mandatory concrete instantiation** (see the task briefing this
    /// module was built against, and its own caution that a symbolic build
    /// is necessary but a concrete one can still hide a transposed/sign
    /// defect a purely symbolic derivation would not): `n = 1, m = 2, i = 1,
    /// j = 1` (`n != m`, so a swapped `n`/`m` is visible), on `a = ofNat 1,
    /// b = ofNat 4` (`width = 3`, so a swapped `a`/`b` or a dropped `width`
    /// factor is visible too, unlike `width = 1`).
    ///
    /// By hand: `m_prime = n*m+n+m = 2+1+2 = 5`, `delta_m_prime =
    /// 3 * 1/6 = 1/2`, `globalIdx = (succ 1)*1+1 = 3`, LHS `= 1 + 3*(1/2) =
    /// 5/2`. `delta_m = 3 * 1/3 = 1`, `base_i = 1 + 1*1 = 2`, `delta_fine =
    /// 1 * 1/2 = 1/2`, RHS `= 2 + 1*(1/2) = 5/2`. Both `5/2`.
    ///
    /// Checked the same way `riemann_sum_of_the_constant_one_on_0_1_computes_to_one`
    /// (`creal_tests.rs`) checks `CReal.riemannSum`: `CReal.seq` of each side
    /// at a fixed index, `Eq Rat` closed by `Eq.refl` -- pure computation, no
    /// lemma, so a wrong index/mesh construction would leave the two sides
    /// stuck at DIFFERENT rationals and `add_declaration` would return `Err`.
    #[test]
    fn sample_point_reblock_computes_to_five_halves_at_concrete_args() {
        let mut kernel = crate::Kernel::new();
        let p = crate::build_creal_prelude(&mut kernel).expect("CReal prelude must build");
        let mut d = IntDev::new(&mut kernel, p.rat.int);

        let one_lit = d.num(1);
        let four_lit = d.num(4);
        let a = d.const_app(p.of_nat, &[one_lit]);
        let b = d.const_app(p.of_nat, &[four_lit]);
        let n = d.num(1);
        let m = d.num(2);
        let i = d.num(1);
        let j = d.num(1);

        let (lhs, rhs, _proof) = sample_point_reblock_proof(&mut d, p, a, b, n, m, i, j);

        let index = d.num(2);
        let lhs_seq = d.const_app(p.seq, &[lhs, index]);
        let rhs_seq = d.const_app(p.seq, &[rhs, index]);
        let stmt = req(&mut d, lhs_seq, rhs_seq);
        let proof = rrefl(&mut d, lhs_seq);

        let anon = d.kernel().anon();
        let name = d
            .kernel()
            .name_str(anon, "__sample_point_reblock_computes_to_five_halves");
        d.kernel()
            .add_declaration(Declaration::Theorem {
                name,
                uparams: vec![],
                ty: stmt,
                value: proof,
            })
            .unwrap_or_else(|error| {
                panic!(
                    "sample_point_reblock's two sides did NOT compute to the \
                     same rational at n=1, m=2, i=1, j=1 (expected 5/2 both \
                     sides): {error:?}"
                )
            });
    }

    /// The general (symbolic `a, b, n, m, i, j`) proof, wrapped in its own
    /// anonymous theorem -- the same idiom `succ_shape_bridge_tests` above
    /// uses, and independent evidence beyond `creal_prelude_builds`'s own
    /// whole-prelude build that `sample_point_reblock_proof` produces a
    /// well-typed proof term at genuinely free variables, not just at the
    /// ground literals the test above uses.
    #[test]
    fn sample_point_reblock_type_checks_symbolically() {
        let mut kernel = crate::Kernel::new();
        let p = crate::build_creal_prelude(&mut kernel).expect("CReal prelude must build");
        let mut d = IntDev::new(&mut kernel, p.rat.int);
        let carrier = creal_ty(&mut d, p);
        let nat = d.nat_ty();

        let a_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let b_fv = d.fresh_fvar();
        let b = d.kernel().fvar(b_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);

        let (lhs, rhs, proof) = sample_point_reblock_proof(&mut d, p, a, b, n, m, i, j);
        let concl = equiv(&mut d, p, lhs, rhs);

        let ty = {
            let over_j = d.pi_fv(j_fv, nat, concl);
            let over_i = d.pi_fv(i_fv, nat, over_j);
            let over_m = d.pi_fv(m_fv, nat, over_i);
            let over_n = d.pi_fv(n_fv, nat, over_m);
            let over_b = d.pi_fv(b_fv, carrier, over_n);
            d.pi_fv(a_fv, carrier, over_b)
        };
        let value = {
            let with_j = d.lam_fv(j_fv, nat, proof);
            let with_i = d.lam_fv(i_fv, nat, with_j);
            let with_m = d.lam_fv(m_fv, nat, with_i);
            let with_n = d.lam_fv(n_fv, nat, with_m);
            let with_b = d.lam_fv(b_fv, carrier, with_n);
            d.lam_fv(a_fv, carrier, with_b)
        };

        let anon = d.kernel().anon();
        let name = d
            .kernel()
            .name_str(anon, "__sample_point_reblock_symbolic_smoke");
        let result = d.kernel().add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty,
            value,
        });
        assert!(
            result.is_ok(),
            "sample_point_reblock_proof must type-check at free variables: {:?}",
            result.err()
        );
    }
}

/// From `h1 : Equiv (add u v) zero` and `h2 : Equiv (add u w) zero`, derive
/// `Equiv v w` — additive inverses (of the SAME `u`) are unique up to
/// `Equiv`. Built from `add_assoc`/`add_comm`/`add_zero`/`add_congr` alone
/// (the standard group-theory cancellation argument), reused by
/// [`declare_equiv_abs_diff_le`] to identify `neg (add x (neg y))` with
/// `add y (neg x)` without a separate `neg` distributes-over-`add` law.
fn cancel_unique(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    u: ExprId,
    v: ExprId,
    w: ExprId,
    h1: ExprId,
    h2: ExprId,
) -> ExprId {
    let zero_c = czero(d, p);
    let uw = cadd(d, p, u, w);

    // step1 : Equiv v (add v zero).
    let vz = cadd(d, p, v, zero_c);
    let step1 = {
        let trim = d.lemma(p.add_zero, &[v]); // Equiv vz v
        d.lemma(p.equiv_symm, &[vz, v, trim])
    };

    // step2 : Equiv (add v zero) (add v uw), via `symm h2 : Equiv zero uw`.
    let v_uw = cadd(d, p, v, uw);
    let step2 = {
        let refl_v = d.lemma(p.equiv_refl, &[v]);
        let flip = d.lemma(p.equiv_symm, &[uw, zero_c, h2]); // Equiv zero uw
        d.lemma(p.add_congr, &[v, v, zero_c, uw, refl_v, flip])
    };

    // step3 : Equiv (add v uw) (add (add v u) w).
    let vu = cadd(d, p, v, u);
    let vu_w = cadd(d, p, vu, w);
    let step3 = {
        let assoc = d.lemma(p.add_assoc, &[v, u, w]); // Equiv vu_w v_uw
        d.lemma(p.equiv_symm, &[vu_w, v_uw, assoc])
    };

    // step4 : Equiv (add (add v u) w) (add (add u v) w).
    let uv = cadd(d, p, u, v);
    let uv_w = cadd(d, p, uv, w);
    let step4 = {
        let comm = d.lemma(p.add_comm, &[v, u]); // Equiv vu uv
        let refl_w = d.lemma(p.equiv_refl, &[w]);
        d.lemma(p.add_congr, &[vu, uv, w, w, comm, refl_w])
    };

    // step5 : Equiv (add (add u v) w) (add zero w), via h1.
    let zero_w = cadd(d, p, zero_c, w);
    let step5 = {
        let refl_w = d.lemma(p.equiv_refl, &[w]);
        d.lemma(p.add_congr, &[uv, zero_c, w, w, h1, refl_w])
    };

    // step6 : Equiv (add zero w) (add w zero).
    let w_zero = cadd(d, p, w, zero_c);
    let step6 = d.lemma(p.add_comm, &[zero_c, w]);

    // step7 : Equiv (add w zero) w.
    let step7 = d.lemma(p.add_zero, &[w]);

    echain(
        d,
        p,
        v,
        &[
            (vz, step1),
            (v_uw, step2),
            (vu_w, step3),
            (uv_w, step4),
            (zero_w, step5),
            (w_zero, step6),
            (w, step7),
        ],
    )
}

/// `CReal.equivAbsDiffLe : ∀ x y : CReal, Equiv x y → ∀ e : Nat,
/// le (abs (add x (neg y))) (embed (Rat.natDivSucc 1 e))` — two REAL-EQUAL
/// numbers are within ANY chosen rational bound of each other. The general
/// fact `riemannSum_cauchy`'s common refinement needs to promote "the global
/// fine sample point IS the local block sample point" (an EXACT `Equiv`,
/// from pure sample-point arithmetic) into the EXPLICIT, computable distance
/// bound `UniformlyContinuousOn.spec` demands as a hypothesis — no
/// Archimedean threshold on `e` at all, since `Equiv` already gives
/// arbitrary precision for free.
///
/// Route: `le_of_equiv` (both directions, the second via `equiv_symm`) gives
/// `le x y` and `le y x`; each widens (via `add_le_add`/`add_neg`/`le_congr`,
/// the same shape [`width_nonneg_of`] uses) to `le (add x (neg y)) zero` and
/// `le (add y (neg x)) zero`; `frac_nonneg` and `le_trans` push both up to
/// the target bound `embed (natDivSucc 1 e)`. [`cancel_unique`] identifies
/// `neg (add x (neg y))` with `add y (neg x)` (both are additive inverses of
/// `add x (neg y)`, so this needs no `neg`-distributes-over-`add` law), and
/// `le_congr` transports the second bound across that identity; `abs_le`
/// closes both into one.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` from a `Theorem` here means
/// the kernel **refused** a proof, not that a script gave up.
pub(super) fn declare_equiv_abs_diff_le(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let y_fv = d.fresh_fvar();
    let y = d.kernel().fvar(y_fv);

    let hxy_ty = equiv(d, p, x, y);
    let hxy_fv = d.fresh_fvar();
    let hxy = d.kernel().fvar(hxy_fv);

    let e_fv = d.fresh_fvar();
    let e = d.kernel().fvar(e_fv);

    let diff = {
        let ny = cneg(d, p, y);
        cadd(d, p, x, ny)
    };
    let flipped = {
        let nx = cneg(d, p, x);
        cadd(d, p, y, nx)
    };
    let neg_diff = cneg(d, p, diff);
    let zero_c = czero(d, p);

    // d1 : le diff zero.
    let d1 = {
        let ny = cneg(d, p, y);
        let hxy_le = d.lemma(p.le_of_equiv, &[x, y, hxy]);
        let refl_ny = d.lemma(p.le_refl, &[ny]);
        let y_ny = cadd(d, p, y, ny);
        let shifted = d.lemma(p.add_le_add, &[x, y, ny, ny, hxy_le, refl_ny]);
        // shifted : le diff y_ny
        let hn = d.lemma(p.add_neg, &[y]); // Equiv y_ny zero
        let refl_diff = d.lemma(p.equiv_refl, &[diff]);
        d.lemma(
            p.le_congr,
            &[diff, diff, y_ny, zero_c, refl_diff, hn, shifted],
        )
    };

    // d2 : le flipped zero.
    let d2 = {
        let hyx = d.lemma(p.equiv_symm, &[x, y, hxy]);
        let hyx_le = d.lemma(p.le_of_equiv, &[y, x, hyx]);
        let nx = cneg(d, p, x);
        let refl_nx = d.lemma(p.le_refl, &[nx]);
        let x_nx = cadd(d, p, x, nx);
        let shifted = d.lemma(p.add_le_add, &[y, x, nx, nx, hyx_le, refl_nx]);
        // shifted : le flipped x_nx
        let hn = d.lemma(p.add_neg, &[x]); // Equiv x_nx zero
        let refl_flipped = d.lemma(p.equiv_refl, &[flipped]);
        d.lemma(
            p.le_congr,
            &[flipped, flipped, x_nx, zero_c, refl_flipped, hn, shifted],
        )
    };

    let embed_q = {
        let one_nat = d.num(1);
        let q = d.const_app(p.rat.nat_div_succ, &[one_nat, e]);
        embed(d, p, q)
    };
    let q_nonneg = frac_nonneg(d, p, e);

    let upper = d.lemma(p.le_trans, &[diff, zero_c, embed_q, d1, q_nonneg]);
    let lower_flipped = d.lemma(p.le_trans, &[flipped, zero_c, embed_q, d2, q_nonneg]);

    // neg_diff_eq : Equiv flipped neg_diff, both are additive inverses of
    // `diff` (`h_sum_zero : Equiv (add diff flipped) zero` below, and
    // `add_neg(diff) : Equiv (add diff neg_diff) zero`).
    let h_sum_zero = {
        let ny = cneg(d, p, y);
        let nx = cneg(d, p, x);
        let start = cadd(d, p, diff, flipped); // (x + (-y)) + (y + (-x))

        // s1 := add x (add (neg y) flipped).
        let inner0 = cadd(d, p, ny, flipped);
        let s1 = cadd(d, p, x, inner0);
        let h1 = d.lemma(p.add_assoc, &[x, ny, flipped]); // Equiv start s1 (direct)

        // inner chain: (neg y) + flipped ~ ((neg y)+y) + (neg x) ~ zero + (neg x) ~ neg x.
        let ny_y = cadd(d, p, ny, y);
        let inner1 = cadd(d, p, ny_y, nx);
        let h_inner_assoc = {
            // add_assoc(neg y, y, neg x) : Equiv inner1 inner0
            let assoc = d.lemma(p.add_assoc, &[ny, y, nx]);
            d.lemma(p.equiv_symm, &[inner1, inner0, assoc])
        };
        // h_inner_assoc : Equiv inner0 inner1

        let ny_y_zero = {
            let comm = d.lemma(p.add_comm, &[ny, y]); // Equiv ny_y (add y ny)
            let y_ny = cadd(d, p, y, ny);
            let hn = d.lemma(p.add_neg, &[y]); // Equiv y_ny zero
            d.lemma(p.equiv_trans, &[ny_y, y_ny, zero_c, comm, hn])
        };
        // ny_y_zero : Equiv ny_y zero

        let zero_nx = cadd(d, p, zero_c, nx);
        let h_inner2 = {
            let refl_nx = d.lemma(p.equiv_refl, &[nx]);
            d.lemma(p.add_congr, &[ny_y, zero_c, nx, nx, ny_y_zero, refl_nx])
        };
        // h_inner2 : Equiv inner1 zero_nx

        let h_inner3 = {
            let comm = d.lemma(p.add_comm, &[zero_c, nx]); // Equiv zero_nx (add nx zero)
            let nx_zero = cadd(d, p, nx, zero_c);
            let trim = d.lemma(p.add_zero, &[nx]); // Equiv nx_zero nx
            d.lemma(p.equiv_trans, &[zero_nx, nx_zero, nx, comm, trim])
        };
        // h_inner3 : Equiv zero_nx nx

        let inner_eq = echain(
            d,
            p,
            inner0,
            &[(inner1, h_inner_assoc), (zero_nx, h_inner2), (nx, h_inner3)],
        );
        // inner_eq : Equiv inner0 nx

        let h6 = {
            let refl_x = d.lemma(p.equiv_refl, &[x]);
            d.lemma(p.add_congr, &[x, x, inner0, nx, refl_x, inner_eq])
        };
        // h6 : Equiv s1 (add x nx)

        let x_nx = cadd(d, p, x, nx);
        let h7 = d.lemma(p.add_neg, &[x]); // Equiv x_nx zero

        echain(d, p, start, &[(s1, h1), (x_nx, h6), (zero_c, h7)])
    };
    let h_self_zero = d.lemma(p.add_neg, &[diff]); // Equiv (add diff neg_diff) zero

    let raw = cancel_unique(d, p, diff, flipped, neg_diff, h_sum_zero, h_self_zero);
    // raw : Equiv flipped neg_diff

    let lower = {
        let refl_q = d.lemma(p.equiv_refl, &[embed_q]);
        d.lemma(
            p.le_congr,
            &[
                flipped,
                neg_diff,
                embed_q,
                embed_q,
                raw,
                refl_q,
                lower_flipped,
            ],
        )
    };

    let proof_body = d.lemma(p.abs_le, &[diff, embed_q, upper, lower]);

    let ty = {
        let abs_diff = d.const_app(p.abs, &[diff]);
        let concl = cle(d, p, abs_diff, embed_q);
        let after_e = d.pi_fv(e_fv, nat, concl);
        let after_hxy = d.arrow(hxy_ty, after_e);
        let over_y = d.pi_fv(y_fv, carrier, after_hxy);
        d.pi_fv(x_fv, carrier, over_y)
    };
    let value = {
        let with_e = d.lam_fv(e_fv, nat, proof_body);
        let with_hxy = d.lam_fv(hxy_fv, hxy_ty, with_e);
        let over_y = d.lam_fv(y_fv, carrier, with_hxy);
        d.lam_fv(x_fv, carrier, over_y)
    };

    d.kernel().add_declaration(Declaration::Theorem {
        name: p.equiv_abs_diff_le,
        uparams: vec![],
        ty,
        value,
    })
}

// --- the archimedean rescaling: Δ_m into a UniformlyContinuousOn-shaped bound

/// From `hab : le a b`, derive `le zero (width_of a b)` — `b − a ≥ 0`.
/// Reproduces `monotone.rs`'s private `step_nonneg_of`'s `width_nonneg`
/// fragment (that function bundles it with a `frac_real` factor this call
/// site does not need).
fn width_nonneg_of(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    a: ExprId,
    b: ExprId,
    hab: ExprId,
) -> ExprId {
    let zero_c = czero(d, p);
    let na = cneg(d, p, a);
    let refl_na = d.lemma(p.le_refl, &[na]);
    let a_na = cadd(d, p, a, na);
    let b_na = cadd(d, p, b, na);
    let shifted = d.lemma(p.add_le_add, &[a, b, na, na, hab, refl_na]);
    let hn = d.lemma(p.add_neg, &[a]);
    let refl_bna = d.lemma(p.equiv_refl, &[b_na]);
    d.lemma(
        p.le_congr,
        &[a_na, zero_c, b_na, b_na, hn, refl_bna, shifted],
    )
}

/// `CReal.bound x`, `CReal.bound x + 1`, and a DIRECT proof of `le x (ofNat
/// (bound x + 1))` — reproduces `archimedean.rs`'s private `le_proof` (inside
/// `declare_archimedean_property`), generalized to an arbitrary `x`.
/// `CReal.bound` is a total COMPUTABLE projection (`archimedean.rs`'s own
/// module documentation), so this needs no existential elimination at all:
/// the witness `bound x + 1` is read directly off `x`, unlike
/// `monotone_of_nonneg_deriv`'s Archimedean closing step, which eliminates
/// `p.archimedean`'s `∃ n, …` to obtain its bound.
///
/// Returns `(c, magnitude, proof)` with `magnitude = Nat.succ c`,
/// `c = CReal.bound x`, `proof : CReal.le x (CReal.ofNat magnitude)`.
fn direct_bound_le(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId) -> (ExprId, ExprId, ExprId) {
    let rat = p.rat;
    let nat = d.nat_ty();

    let c = d.const_app(p.bound, &[x]);
    let magnitude = d.succ(c);
    let zero_nat = d.num(0);
    let target = d.const_app(rat.nat_div_succ, &[magnitude, zero_nat]);

    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let point = sample(d, p, x, k);
    let bw = d.lemma(p.bound_within, &[x, k]);
    let (_, upper) = halves(d, p, point, target, bw);

    let two_nat = d.num(2);
    let bound2 = d.const_app(rat.nat_div_succ, &[two_nat, k]);
    let nonneg2 = d.lemma(rat.zero_le_nat_div_succ, &[two_nat, k]);

    let zero = rzero(d, rat);
    let target_refl = d.lemma(rat.le_refl, &[target]);
    let widened = d.lemma(
        rat.add_le_add,
        &[target, target, zero, bound2, target_refl, nonneg2],
    );
    let padded_target = radd(d, target, zero);
    let sum = radd(d, target, bound2);
    let trim = d.lemma(rat.add_zero, &[target]);
    let target_le_sum = rat_eq_rewrite(d, padded_target, target, trim, widened, &|d, t| {
        rle(d, rat, t, sum)
    });

    let chained = d.lemma(rat.le_trans, &[point, target, sum, upper, target_le_sum]);
    let at_index = d.lemma(rat.sub_le_of_le, &[point, target, bound2, chained]);
    let proof_body = d.lam_fv(k_fv, nat, at_index);
    (c, magnitude, proof_body)
}

/// `Equiv (mul (ofNat magnitude) (ofRat (natDivSucc 1 deep))) (ofRat
/// (natDivSucc 1 outer))`, given `magnitude = Nat.succ c` and `deep =
/// magnitude*outer + c` (a SYNTACTIC requirement: `Rat.natDivSucc_scale` is
/// applied at `(c, outer)` and its conclusion must match `deep` on the
/// nose). Duplicated verbatim from `monotone.rs`'s private
/// `magnitude_times_frac_eq_outer` (that file is out of scope for this
/// slice).
fn magnitude_times_frac_eq_outer(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    c: ExprId,
    magnitude: ExprId,
    outer: ExprId,
    deep: ExprId,
) -> ExprId {
    let rat = p.rat;
    let nat = rat.int.nat;
    let one_nat = d.num(1);
    let zero_nat = d.num(0);

    let mag_rat = d.const_app(rat.nat_div_succ, &[magnitude, zero_nat]);
    let frac_rat = d.const_app(rat.nat_div_succ, &[one_nat, deep]);
    let mag_real = embed(d, p, mag_rat);
    let frac_real = embed(d, p, frac_rat);
    let product_real = cmul(d, p, mag_real, frac_real);

    let product_rat = rmul(d, mag_rat, frac_rat);
    let fused = {
        let scaled = NatOps::mul(d, magnitude, one_nat);
        d.const_app(rat.nat_div_succ, &[scaled, deep])
    };
    let fuse = d.lemma(rat.nat_div_succ_mul, &[magnitude, one_nat, deep]);
    let collapsed = d.const_app(rat.nat_div_succ, &[magnitude, deep]);
    let collapse = {
        let scaled = NatOps::mul(d, magnitude, one_nat);
        let identity = d.lemma(nat.mul_one, &[magnitude]);
        nat_eq_to_rat(d, scaled, magnitude, identity, &|d, t| {
            d.const_app(rat.nat_div_succ, &[t, deep])
        })
    };
    let outer_rat = d.const_app(rat.nat_div_succ, &[one_nat, outer]);
    let scale = d.lemma(rat.nat_div_succ_scale, &[c, outer]);
    // scale : Eq Rat (natDivSucc magnitude deep) (natDivSucc 1 outer),
    // PROVIDED `deep` is exactly `mul(magnitude, outer) + c`.

    let (_, chain) = rchain(
        d,
        product_rat,
        &[(fused, fuse), (collapsed, collapse), (outer_rat, scale)],
    );

    let of_rat_mul_step = d.lemma(p.of_rat_mul, &[mag_rat, frac_rat]);
    rat_eq_rewrite(
        d,
        product_rat,
        outer_rat,
        chain,
        of_rat_mul_step,
        &|d, t| {
            let embedded = embed(d, p, t);
            equiv(d, p, product_real, embedded)
        },
    )
}

/// `le (mul diff (ofRat (natDivSucc 1 deep))) (ofRat (natDivSucc 1 outer))`,
/// given `diff_le_mag : le diff (ofNat magnitude)`, `magnitude = Nat.succ
/// c`, `deep = magnitude*outer + c`. Duplicated verbatim from `monotone.rs`'s
/// private `step_le_outer_bound` (that file is out of scope for this
/// slice) — the numeric heart of the Archimedean scaling this file's
/// `mesh_le_of_ge` needs.
#[allow(clippy::too_many_arguments)]
fn step_le_outer_bound(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    diff: ExprId,
    diff_le_mag: ExprId,
    c: ExprId,
    magnitude: ExprId,
    outer: ExprId,
    deep: ExprId,
) -> ExprId {
    let one_nat = d.num(1);
    let frac_deep_rat = div_succ(d, p, 1, deep);
    let frac_deep = embed(d, p, frac_deep_rat);
    let frac_nonneg = {
        let rzero_expr = d.kernel().const_(p.rat.zero, vec![]);
        let rle_p = d.lemma(p.rat.zero_le_nat_div_succ, &[one_nat, deep]);
        d.lemma(p.of_rat_le, &[rzero_expr, frac_deep_rat, rle_p])
    };

    let step = cmul(d, p, diff, frac_deep);
    let diff_frac = cmul(d, p, frac_deep, diff);
    let comm1 = d.lemma(p.mul_comm, &[diff, frac_deep]);

    let om = d.const_app(p.of_nat, &[magnitude]);
    let mag_frac = cmul(d, p, frac_deep, om);
    let scaled = d.lemma(
        p.mul_le_mul_of_nonneg_left,
        &[frac_deep, diff, om, frac_nonneg, diff_le_mag],
    );

    let refl_mag_frac = d.lemma(p.equiv_refl, &[mag_frac]);
    let comm1_symm = d.lemma(p.equiv_symm, &[step, diff_frac, comm1]);
    let step_le_mag_frac = d.lemma(
        p.le_congr,
        &[
            diff_frac,
            step,
            mag_frac,
            mag_frac,
            comm1_symm,
            refl_mag_frac,
            scaled,
        ],
    );

    let frac_mag = cmul(d, p, om, frac_deep);
    let comm2 = d.lemma(p.mul_comm, &[frac_deep, om]);
    let collapse = magnitude_times_frac_eq_outer(d, p, c, magnitude, outer, deep);
    let out_bound_rat = div_succ(d, p, 1, outer);
    let out_bound = embed(d, p, out_bound_rat);
    let mag_frac_eq_out = d.lemma(
        p.equiv_trans,
        &[mag_frac, frac_mag, out_bound, comm2, collapse],
    );

    let refl_step = d.lemma(p.equiv_refl, &[step]);
    d.lemma(
        p.le_congr,
        &[
            step,
            step,
            mag_frac,
            out_bound,
            refl_step,
            mag_frac_eq_out,
            step_le_mag_frac,
        ],
    )
}

/// `CReal.mesh_le_of_ge : ∀ a b outer m, le a b → Nat.le ((Nat.succ (bound
/// (add b (neg a))))*outer + bound (add b (neg a))) m → le (mul (add b (neg
/// a)) (ofRat (natDivSucc 1 m))) (ofRat (natDivSucc 1 outer))` — the
/// ARCHIMEDEAN RESCALING `UniformlyContinuousOn.spec` needs: turning the
/// mesh width `Δ_m := (b−a)·natDivSucc(1,m)` into a bound of the exact
/// rational shape `natDivSucc 1 outer` that spec expects, for EVERY block
/// count `m` at or past a computed threshold.
///
/// The threshold and the estimate reuse the SAME construction
/// `monotone.rs`'s `HasDerivativeOn`-based Archimedean closing step uses
/// ([`step_le_outer_bound`]/[`magnitude_times_frac_eq_outer`], duplicated
/// here since that file is out of scope for this slice) — but where that
/// proof is free to pick its OWN subdivision count, this one is handed an
/// arbitrary `m` already at least as large as the threshold (`riemannSum`'s
/// block count is fixed by its caller, not chosen here), so an extra
/// `Rat.natDivSucc_antitone` step widens the exact-threshold bound across
/// the gap. No existential elimination anywhere: [`direct_bound_le`] reads
/// the Archimedean witness directly off `CReal.bound`.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` from a `Theorem` here means
/// the kernel **refused** a proof, not that a script gave up.
fn declare_mesh_le_of_ge(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let outer_fv = d.fresh_fvar();
    let outer = d.kernel().fvar(outer_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);

    let hab_ty = cle(d, p, a, b);
    let hab_fv = d.fresh_fvar();
    let hab = d.kernel().fvar(hab_fv);

    let width = width_of(d, p, a, b);
    let (c, magnitude, width_le_mag) = direct_bound_le(d, p, width);
    let me = NatOps::mul(d, magnitude, outer);
    let deep = NatOps::add(d, me, c);

    let hge_ty = d.le(deep, m);
    let hge_fv = d.fresh_fvar();
    let hge = d.kernel().fvar(hge_fv);

    let width_nonneg = width_nonneg_of(d, p, a, b, hab);
    let bound_at_deep = step_le_outer_bound(d, p, width, width_le_mag, c, magnitude, outer, deep);

    let one_nat = d.num(1);
    let frac_m_rat = d.const_app(p.rat.nat_div_succ, &[one_nat, m]);
    let frac_deep_rat = d.const_app(p.rat.nat_div_succ, &[one_nat, deep]);
    let out_bound_rat = d.const_app(p.rat.nat_div_succ, &[one_nat, outer]);

    let antitone = d.lemma(p.rat.nat_div_succ_antitone, &[deep, m, hge]);
    let frac_le_real = d.lemma(p.of_rat_le, &[frac_m_rat, frac_deep_rat, antitone]);

    let frac_m_real = embed(d, p, frac_m_rat);
    let frac_deep_real = embed(d, p, frac_deep_rat);
    let out_bound = embed(d, p, out_bound_rat);

    let scaled = d.lemma(
        p.mul_le_mul_of_nonneg_left,
        &[
            width,
            frac_m_real,
            frac_deep_real,
            width_nonneg,
            frac_le_real,
        ],
    );

    let step_m = cmul(d, p, width, frac_m_real);
    let step_deep = cmul(d, p, width, frac_deep_real);
    let final_le = d.lemma(
        p.le_trans,
        &[step_m, step_deep, out_bound, scaled, bound_at_deep],
    );

    let concl = cle(d, p, step_m, out_bound);
    let ty = {
        let after_hge = d.arrow(hge_ty, concl);
        let after_hab = d.arrow(hab_ty, after_hge);
        let over_m = d.pi_fv(m_fv, nat, after_hab);
        let over_outer = d.pi_fv(outer_fv, nat, over_m);
        let over_b = d.pi_fv(b_fv, carrier, over_outer);
        d.pi_fv(a_fv, carrier, over_b)
    };
    let value = {
        let with_hge = d.lam_fv(hge_fv, hge_ty, final_le);
        let with_hab = d.lam_fv(hab_fv, hab_ty, with_hge);
        let over_m = d.lam_fv(m_fv, nat, with_hab);
        let over_outer = d.lam_fv(outer_fv, nat, over_m);
        let over_b = d.lam_fv(b_fv, carrier, over_outer);
        d.lam_fv(a_fv, carrier, over_b)
    };

    d.kernel().add_declaration(Declaration::Theorem {
        name: p.mesh_le_of_ge,
        uparams: vec![],
        ty,
        value,
    })
}

// --- the per-term fine-vs-coarse sample bound -- toward `riemannSum_cauchy`'s
// common refinement (roadmap step 1)
//
// Comparing one coarse block's single term against its `succ n` fine
// sub-terms needs every fine sample point in that block to lie within
// `delta_outer` (the COARSE mesh) of the block's own coarse sample point,
// regardless of which fine index `j < succ n` or which coarse block it is —
// this section's own module documentation numbers this "step 1" and flags it
// as a success on its own. `delta_outer` here instantiates to `riemannSum`'s
// own `Δ_m` (this file's `delta_of`) at the call site that uses this; kept
// abstract here since nothing below reads `a`/`b`, only `delta_outer`'s own
// nonnegativity.

/// `Equiv (add (add x w) (neg x)) w` — `(x + w) − x ~ w`. The mirror of
/// [`add_sub_cancel`] (`a + (b − a) ~ b`): here the FIRST operand of the
/// addition is the one subtracted back off, rather than the second.
fn cancel_add_neg_right(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId, w: ExprId) -> ExprId {
    let nx = cneg(d, p, x);
    let xw = cadd(d, p, x, w); // x + w
    let start = cadd(d, p, xw, nx); // (x + w) + (-x)

    let wx = cadd(d, p, w, x); // w + x
    let s1 = cadd(d, p, wx, nx); // (w + x) + (-x)
    let h1 = {
        let comm = d.lemma(p.add_comm, &[x, w]); // Equiv xw wx
        let refl_nx = d.lemma(p.equiv_refl, &[nx]);
        d.lemma(p.add_congr, &[xw, wx, nx, nx, comm, refl_nx])
        // : Equiv start s1
    };

    let xnx = cadd(d, p, x, nx); // x + (-x)
    let s2 = cadd(d, p, w, xnx); // w + (x + (-x))
    let h2 = d.lemma(p.add_assoc, &[w, x, nx]); // Equiv s1 s2

    let zero_c = czero(d, p);
    let s3 = cadd(d, p, w, zero_c); // w + zero
    let h3 = {
        let hn = d.lemma(p.add_neg, &[x]); // Equiv xnx zero_c
        let refl_w = d.lemma(p.equiv_refl, &[w]);
        d.lemma(p.add_congr, &[w, w, xnx, zero_c, refl_w, hn])
        // : Equiv s2 s3
    };

    let h4 = d.lemma(p.add_zero, &[w]); // Equiv s3 w

    echain(d, p, start, &[(s1, h1), (s2, h2), (s3, h3), (w, h4)])
}

/// From `v_nonneg : le zero v` and `bound_nonneg : le zero bound`, `le (neg
/// v) bound`. Reproduced verbatim from `derivative.rs`'s private
/// `neg_le_of_nonneg` (that file is out of scope for this slice).
fn neg_le_of_nonneg(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    v: ExprId,
    bound: ExprId,
    v_nonneg: ExprId,
    bound_nonneg: ExprId,
) -> ExprId {
    let zero_c = czero(d, p);
    let neg_v = cneg(d, p, v);
    let neg_zero = cneg(d, p, zero_c);

    let step = d.lemma(p.neg_le_neg, &[zero_c, v, v_nonneg]);
    // step : le neg_v neg_zero
    let nz_eq = {
        // `Equiv (neg zero) zero`, reproduced verbatim from several modules'
        // private `neg_zero_equiv` (e.g. `derivative.rs`) since this file
        // cannot call any of them.
        let nz = cneg(d, p, zero_c);
        let padded = cadd(d, p, nz, zero_c);
        let flipped = cadd(d, p, zero_c, nz);
        let ha = d.lemma(p.add_zero, &[nz]); // padded ~ nz
        let step1 = d.lemma(p.equiv_symm, &[padded, nz, ha]); // nz ~ padded
        let hb = d.lemma(p.add_comm, &[nz, zero_c]); // padded ~ flipped
        let hc = d.lemma(p.add_neg, &[zero_c]); // flipped ~ zero_c
        echain(d, p, nz, &[(padded, step1), (flipped, hb), (zero_c, hc)])
    };
    let refl_negv = d.lemma(p.equiv_refl, &[neg_v]);
    let le_negv_zero = d.lemma(
        p.le_congr,
        &[neg_v, neg_v, neg_zero, zero_c, refl_negv, nz_eq, step],
    );
    // le_negv_zero : le neg_v zero_c

    d.lemma(
        p.le_trans,
        &[neg_v, zero_c, bound, le_negv_zero, bound_nonneg],
    )
}

/// `le zero (embed (natDivSucc 1 denom))` — the mesh fraction `1/(denom+1)`
/// is always nonneg. The same route [`delta_nonneg_of`]'s own `frac_nonneg`
/// uses, factored out so [`sample_offset_bound`] can call it at the FINE
/// denominator `n` independently of that function's coarse `m`.
fn frac_nonneg(d: &mut IntDev<'_>, p: CRealPrelude, denom: ExprId) -> ExprId {
    let one_nat = d.num(1);
    let frac = d.const_app(p.rat.nat_div_succ, &[one_nat, denom]);
    let rzero_expr = rzero(d, p.rat);
    let rle_p = d.lemma(p.rat.zero_le_nat_div_succ, &[one_nat, denom]);
    d.lemma(p.of_rat_le, &[rzero_expr, frac, rle_p])
}

/// `(term, term_nonneg, term_le_delta)`, `term := mul (ofNat j) delta_fine`,
/// `delta_fine := mul delta (embed (Rat.natDivSucc 1 n))`, `term_nonneg :
/// le zero term`, `term_le_delta : le term delta` — the pure NUMERIC core
/// [`sample_offset_bound`]'s own proof needs (there, to close an `abs_le`)
/// and the fine-sample placement lemma [`declare_fine_sample_in_bounds`]
/// needs directly (there, to place the fine sample point between `base` and
/// `base + delta` via [`shift_le_of_nonneg`]/`add_le_add`). Factored out so
/// both share exactly this proof term rather than two independently-typed
/// copies of it.
fn fine_term_and_bounds(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    delta: ExprId,
    n: ExprId,
    j: ExprId,
    hlt: ExprId,
    delta_nonneg: ExprId,
) -> (ExprId, ExprId, ExprId) {
    let one_nat = d.num(1);
    let frac_n_rat = d.const_app(p.rat.nat_div_succ, &[one_nat, n]);
    let frac_n = embed(d, p, frac_n_rat);
    let delta_fine = cmul(d, p, delta, frac_n); // Δ_fine := delta * natDivSucc 1 n
    let of_nat_j = d.const_app(p.of_nat, &[j]);
    let term = cmul(d, p, of_nat_j, delta_fine); // mul (ofNat j) delta_fine

    let frac_n_nonneg = frac_nonneg(d, p, n);
    let delta_fine_nonneg = d.lemma(p.mul_nonneg, &[delta, frac_n, delta_nonneg, frac_n_nonneg]);

    // term_nonneg : le zero term.
    let term_nonneg = {
        let j_nonneg = zero_le_of_nat(d, p, j);
        d.lemma(
            p.mul_nonneg,
            &[of_nat_j, delta_fine, j_nonneg, delta_fine_nonneg],
        )
    };

    // term_le_delta : le term delta.
    let term_le_delta = {
        let n_succ = d.succ(n);
        let hle_j_n = nat_le_of_lt(d, j, n_succ, hlt); // Nat.le j (succ n)
        let of_nat_n_succ = d.const_app(p.of_nat, &[n_succ]);
        let j_le_n_succ = d.lemma(p.of_nat_le, &[j, n_succ, hle_j_n]); // le (ofNat j) (ofNat (succ n))

        let step = d.lemma(
            p.mul_le_mul_of_nonneg_left,
            &[
                delta_fine,
                of_nat_j,
                of_nat_n_succ,
                delta_fine_nonneg,
                j_le_n_succ,
            ],
        );
        // step : le (mul delta_fine (ofNat j)) (mul delta_fine (ofNat n_succ))
        let comm_j = d.lemma(p.mul_comm, &[delta_fine, of_nat_j]);
        let comm_n = d.lemma(p.mul_comm, &[delta_fine, of_nat_n_succ]);
        let dj = cmul(d, p, delta_fine, of_nat_j);
        let dn = cmul(d, p, delta_fine, of_nat_n_succ);
        let nd = cmul(d, p, of_nat_n_succ, delta_fine);
        let commuted = d.lemma(p.le_congr, &[dj, term, dn, nd, comm_j, comm_n, step]);
        // commuted : le term nd, term = mul (ofNat j) delta_fine

        // n_delta_eq_delta : Equiv (mul (ofNat (succ n)) (mul delta frac_n)) delta
        //                  = Equiv nd delta, since `delta_fine` is exactly
        //   `mul delta frac_n` and `nd` is exactly `mul (ofNat (succ n)) delta_fine`.
        let n_delta_eq_delta = mesh_times_count_eq_width(d, p, delta, frac_n, n);

        let refl_term = d.lemma(p.equiv_refl, &[term]);
        d.lemma(
            p.le_congr,
            &[term, term, nd, delta, refl_term, n_delta_eq_delta, commuted],
        )
        // : le term delta
    };

    (term, term_nonneg, term_le_delta)
}

/// `CReal.le (CReal.abs (CReal.add (CReal.add base (CReal.mul (CReal.ofNat
/// j) (CReal.mul delta (CReal.ofRat (Rat.natDivSucc 1 n))))) (CReal.neg
/// base))) delta` — roadmap step 1: every fine sample point `base +
/// j·Δ_fine` (`Δ_fine := delta · natDivSucc 1 n`, `j < succ n`) lies within
/// `delta` of the block's own coarse sample point `base`, for an arbitrary
/// nonneg `delta` — independent of which coarse block `base` names.
///
/// Route: [`cancel_add_neg_right`] collapses the difference to the pure
/// offset term `mul (ofNat j) Δ_fine`; that term is nonneg (`ofNat j` and
/// `Δ_fine` both nonneg, `mul_nonneg`) and bounded above by `delta` exactly
/// via `j ≤ succ n` ([`nat_le_of_lt`] on the hypothesis `hlt`), `ofNat_le`,
/// `mul_le_mul_of_nonneg_left` and the exact identity `(succ n)·Δ_fine ~
/// delta` ([`mesh_times_count_eq_width`] at `(delta, frac_n, n)` — the same
/// helper [`declare_riemann_sample_in_bounds`]'s `upper` branch already
/// uses, here reused at the FINE denominator rather than the coarse one);
/// [`neg_le_of_nonneg`] gives the other `abs_le` branch directly from that
/// same nonnegativity, with no separate lower-bound argument needed.
fn sample_offset_bound(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    base: ExprId,
    delta: ExprId,
    n: ExprId,
    j: ExprId,
    hlt: ExprId,
    delta_nonneg: ExprId,
) -> ExprId {
    let (term, term_nonneg, term_le_delta) =
        fine_term_and_bounds(d, p, delta, n, j, hlt, delta_nonneg);

    let x_j = cadd(d, p, base, term); // base + term -- the fine sample point
    let diff = {
        let nb = cneg(d, p, base);
        cadd(d, p, x_j, nb) // (base + term) + (-base)
    };
    let diff_eq = cancel_add_neg_right(d, p, base, term); // Equiv diff term

    let neg_term_le_delta = neg_le_of_nonneg(d, p, term, delta, term_nonneg, delta_nonneg);
    let abs_term_le_delta = d.lemma(p.abs_le, &[term, delta, term_le_delta, neg_term_le_delta]);

    let abs_diff = d.const_app(p.abs, &[diff]);
    let abs_term = d.const_app(p.abs, &[term]);
    let abs_diff_term = d.lemma(p.abs_congr, &[diff, term, diff_eq]); // Equiv abs_diff abs_term
    let abs_term_diff = d.lemma(p.equiv_symm, &[abs_diff, abs_term, abs_diff_term]);
    let refl_delta = d.lemma(p.equiv_refl, &[delta]);
    d.lemma(
        p.le_congr,
        &[
            abs_term,
            abs_diff,
            delta,
            delta,
            abs_term_diff,
            refl_delta,
            abs_term_le_delta,
        ],
    )
    // : le abs_diff delta
}

/// `Equiv (sample_point x0 step (Nat.succ i)) (add (sample_point x0 step i)
/// step)` — the coarse/fine successor step `x_{i+1} ~ x_i + step`, in
/// ADDITIVE form. A restatement of `monotone.rs`'s private
/// `consecutive_diff_eq_step` (which proves the DIFFERENCE form `x_{i+1} −
/// x_i ~ step`, built for a different call site) built directly to the
/// additive shape [`declare_fine_sample_in_bounds`] needs: duplicated rather
/// than imported, since that file is out of scope for edits in this slice
/// and `consecutive_diff_eq_step` is private there.
///
/// Route: `ofNat (succ i) ~ ofNat i + one` ([`of_nat_succ_equiv_local`]),
/// `mul_congr` to lift that into `(ofNat (succ i))·step ~ (ofNat i +
/// one)·step`, [`right_distrib`] to expand the right side to `(ofNat
/// i)·step + one·step`, `mul_one`/`mul_comm` to fold `one·step ~ step`, then
/// `add_congr` with `x0` and `add_assoc` to re-bracket `x0 + ((ofNat
/// i)·step + step)` as `(x0 + (ofNat i)·step) + step`.
fn sample_point_succ_step(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    x0: ExprId,
    step: ExprId,
    i: ExprId,
) -> ExprId {
    let of_nat_i = d.const_app(p.of_nat, &[i]);
    let u = cmul(d, p, of_nat_i, step);
    let x_i = cadd(d, p, x0, u); // sample_point x0 step i

    let si = d.succ(i);
    let of_nat_si = d.const_app(p.of_nat, &[si]);
    let v = cmul(d, p, of_nat_si, step); // ofNat(succ i) * step
    let x_si = cadd(d, p, x0, v); // sample_point x0 step (succ i)

    // v_eq_u_plus_step : Equiv v (add u step).
    let v_eq_u_plus_step = {
        let one_c = d.kernel().const_(p.one, vec![]);
        let succ_eq = of_nat_succ_equiv_local(d, p, i); // Equiv of_nat_si (add of_nat_i one_c)
        let sum_of_nat = cadd(d, p, of_nat_i, one_c);
        let expanded = cmul(d, p, sum_of_nat, step);
        let h_a = {
            let refl_step = d.lemma(p.equiv_refl, &[step]);
            d.lemma(
                p.mul_congr,
                &[of_nat_si, sum_of_nat, step, step, succ_eq, refl_step],
            )
        };
        let h_b = right_distrib(d, p, of_nat_i, one_c, step);
        let one_step = cmul(d, p, one_c, step);
        let distributed = cadd(d, p, u, one_step);
        let h_c = {
            let refl_u = d.lemma(p.equiv_refl, &[u]);
            let one_mul_step = {
                let step_one = cmul(d, p, step, one_c);
                let mul_one_step = d.lemma(p.mul_one, &[step]);
                let comm = d.lemma(p.mul_comm, &[one_c, step]);
                d.lemma(
                    p.equiv_trans,
                    &[one_step, step_one, step, comm, mul_one_step],
                )
            };
            d.lemma(p.add_congr, &[u, u, one_step, step, refl_u, one_mul_step])
        };
        let u_plus_step = cadd(d, p, u, step);
        let s1 = d.lemma(p.equiv_trans, &[v, expanded, distributed, h_a, h_b]);
        d.lemma(p.equiv_trans, &[v, distributed, u_plus_step, s1, h_c])
    };

    // x_si = x0 + v ~ x0 + (u + step) ~ (x0 + u) + step = x_i + step.
    let u_plus_step = cadd(d, p, u, step);
    let x0_u_step = cadd(d, p, x0, u_plus_step);
    let h_v = {
        let refl_x0 = d.lemma(p.equiv_refl, &[x0]);
        d.lemma(
            p.add_congr,
            &[x0, x0, v, u_plus_step, refl_x0, v_eq_u_plus_step],
        )
    };
    let x_i_step = cadd(d, p, x_i, step);
    let h_assoc = {
        // add_assoc(x0, u, step) : Equiv (add (add x0 u) step) (add x0 (add u step))
        //                        = Equiv x_i_step x0_u_step
        let assoc = d.lemma(p.add_assoc, &[x0, u, step]);
        d.lemma(p.equiv_symm, &[x_i_step, x0_u_step, assoc])
    };
    d.lemma(p.equiv_trans, &[x_si, x0_u_step, x_i_step, h_v, h_assoc])
    // : Equiv x_si x_i_step
}

/// `CReal.fineSample_in_bounds : ∀ a b m n i j, le a b → Nat.le i m →
/// Nat.lt j (Nat.succ n) → And (le a x) (le x b)`, `x := add (sample_point a
/// delta_m i) (mul (ofNat j) delta_fine)`, `delta_m := mul (add b (neg a))
/// (embed (Rat.natDivSucc 1 m))`, `delta_fine := mul delta_m (embed
/// (Rat.natDivSucc 1 n))` — the fine-sample placement lemma
/// `riemannSum_cauchy`'s per-block fold needs: every FINE sample point `x`
/// inside COARSE block `i` (`i ≤ m`) lies in `[a, b]`, for every fine
/// sub-index `j < Nat.succ n`. See the module documentation's "the succ-shape
/// bridge" section header and [`CRealPrelude::fine_sample_in_bounds`]'s own
/// doc comment for why this is the one-index-shift generalization
/// `riemannSum_sample_in_bounds`/`subdivisionPoint_in_bounds` do not cover.
///
/// Route: two calls to `subdivisionPoint_in_bounds`, at coarse indices `i`
/// (giving `a ≤ base`, `base := sample_point a delta_m i`) and `Nat.succ i`
/// (giving `base' ≤ b`, `base' := sample_point a delta_m (Nat.succ i)`),
/// bracketing the block `[base, base + delta_m]` via
/// [`sample_point_succ_step`] (`base' ~ base + delta_m`). `i ≤ m` weakens to
/// both `i ≤ succ m` (`Nat.le_trans` against `Nat.le_succ`, the exact idiom
/// [`nat_le_of_lt`] already uses) and `succ i ≤ succ m` (`Nat.succ_le_succ`
/// directly) — the two hypotheses `subdivisionPoint_in_bounds` needs at
/// those two indices. [`fine_term_and_bounds`] gives the fine term's own
/// `0 ≤ term` (lower: [`shift_le_of_nonneg`] places `x` past `base`) and
/// `term ≤ delta_m` (upper: `add_le_add` places `x` before `base'`, then
/// `le_congr` rewrites `base'` down to `base + delta_m`); `le_trans` on each
/// side closes `a ≤ x` and `x ≤ b`.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` from a `Theorem` here means
/// the kernel **refused** a proof, not that a script gave up.
pub(super) fn declare_fine_sample_in_bounds(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let logic = p.rat.int.logic;

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let j_fv = d.fresh_fvar();
    let j = d.kernel().fvar(j_fv);

    let hab_ty = cle(d, p, a, b);
    let hab_fv = d.fresh_fvar();
    let hab = d.kernel().fvar(hab_fv);

    let hi_ty = d.le(i, m); // Nat.le i m
    let hi_fv = d.fresh_fvar();
    let hi = d.kernel().fvar(hi_fv);

    let sn = d.succ(n);
    let hj_ty = d.lt(j, sn); // Nat.lt j (Nat.succ n)
    let hj_fv = d.fresh_fvar();
    let hj = d.kernel().fvar(hj_fv);

    let (delta_m, delta_m_nonneg) = delta_nonneg_of(d, p, a, b, m, hab);
    let base = sample_point(d, p, a, delta_m, i);
    let (term, term_nonneg, term_le_delta_m) =
        fine_term_and_bounds(d, p, delta_m, n, j, hj, delta_m_nonneg);
    let x = cadd(d, p, base, term); // the fine sample point

    let np = d.prelude();
    let succ_m = d.succ(m);

    // lower : le a x.
    let a_le_x = {
        // hle_i_succm : Nat.le i (Nat.succ m), from `i ≤ m` and `m ≤ succ m`.
        let hle_i_succm = {
            let le_succ_m = d.const_app(np.le_succ, &[m]);
            d.const_app(np.le_trans, &[i, m, succ_m, hi, le_succ_m])
        };
        let and_base = d.const_app(
            p.subdivision_point_in_bounds,
            &[a, b, m, i, hab, hle_i_succm],
        );
        let a_le_base_ty = cle(d, p, a, base);
        let base_le_b_ty = cle(d, p, base, b);
        let a_le_base = d.const_app(logic.and_left, &[a_le_base_ty, base_le_b_ty, and_base]);

        let base_le_x = shift_le_of_nonneg(d, p, base, term, term_nonneg);
        d.lemma(p.le_trans, &[a, base, x, a_le_base, base_le_x])
    };

    // upper : le x b.
    let x_le_b = {
        let succ_i = d.succ(i);
        // hle_si_succm : Nat.le (Nat.succ i) (Nat.succ m), from `i ≤ m`.
        let hle_si_succm = d.const_app(np.succ_le_succ, &[i, m, hi]);
        let and_base_succ = d.const_app(
            p.subdivision_point_in_bounds,
            &[a, b, m, succ_i, hab, hle_si_succm],
        );
        let base_succ = sample_point(d, p, a, delta_m, succ_i);
        let a_le_base_succ_ty = cle(d, p, a, base_succ);
        let base_succ_le_b_ty = cle(d, p, base_succ, b);
        let base_succ_le_b = d.const_app(
            logic.and_right,
            &[a_le_base_succ_ty, base_succ_le_b_ty, and_base_succ],
        );

        // base_succ ~ add base delta_m.
        let succ_step_eq = sample_point_succ_step(d, p, a, delta_m, i);
        let base_plus_delta = cadd(d, p, base, delta_m);
        let refl_b = d.lemma(p.equiv_refl, &[b]);
        let base_plus_delta_le_b = d.lemma(
            p.le_congr,
            &[
                base_succ,
                base_plus_delta,
                b,
                b,
                succ_step_eq,
                refl_b,
                base_succ_le_b,
            ],
        );

        // x = add base term ≤ add base delta_m, from term ≤ delta_m.
        let refl_base = d.lemma(p.le_refl, &[base]);
        let x_le_base_plus_delta = d.lemma(
            p.add_le_add,
            &[base, base, term, delta_m, refl_base, term_le_delta_m],
        );
        d.lemma(
            p.le_trans,
            &[
                x,
                base_plus_delta,
                b,
                x_le_base_plus_delta,
                base_plus_delta_le_b,
            ],
        )
    };

    let a_le_x_ty = cle(d, p, a, x);
    let x_le_b_ty = cle(d, p, x, b);
    let and_ty = d.const_app(logic.and, &[a_le_x_ty, x_le_b_ty]);
    let proof_body = and_intro(d, p, a_le_x_ty, x_le_b_ty, a_le_x, x_le_b);

    let ty = {
        let after_hj = d.arrow(hj_ty, and_ty);
        let after_hi = d.arrow(hi_ty, after_hj);
        let after_hab = d.arrow(hab_ty, after_hi);
        let over_j = d.pi_fv(j_fv, nat, after_hab);
        let over_i = d.pi_fv(i_fv, nat, over_j);
        let over_n = d.pi_fv(n_fv, nat, over_i);
        let over_m = d.pi_fv(m_fv, nat, over_n);
        let over_b = d.pi_fv(b_fv, carrier, over_m);
        d.pi_fv(a_fv, carrier, over_b)
    };
    let value = {
        let with_hj = d.lam_fv(hj_fv, hj_ty, proof_body);
        let with_hi = d.lam_fv(hi_fv, hi_ty, with_hj);
        let with_hab = d.lam_fv(hab_fv, hab_ty, with_hi);
        let over_j = d.lam_fv(j_fv, nat, with_hab);
        let over_i = d.lam_fv(i_fv, nat, over_j);
        let over_n = d.lam_fv(n_fv, nat, over_i);
        let over_m = d.lam_fv(m_fv, nat, over_n);
        let over_b = d.lam_fv(b_fv, carrier, over_m);
        d.lam_fv(a_fv, carrier, over_b)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.fine_sample_in_bounds,
        uparams: vec![],
        ty,
        value,
    })
}

// --- roadmap step 2: the per-block bound, via `UniformlyContinuousOn.spec` -

/// `CReal.close (x y : CReal) (q : Rat) : Prop := le (abs (add x (neg y)))
/// (ofRat q)` — `|x − y| ≤ q`, real-valued and index-free in `x, y`.
/// Reproduced from `uniform_continuity.rs`'s private `close_within` (that
/// file is out of scope for edits in this slice): the exact shape
/// `UniformlyContinuousOn.spec`'s hypothesis and conclusion both take.
fn close_within(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId, y: ExprId, q: ExprId) -> ExprId {
    let ny = cneg(d, p, y);
    let diff = cadd(d, p, x, ny);
    let magnitude = d.const_app(p.abs, &[diff]);
    let target = embed(d, p, q);
    cle(d, p, magnitude, target)
}

/// `CReal.fineSample_close : ∀ F a b e m n i j, le a b →
/// UniformlyContinuousOn F a b → Nat.le i m → Nat.lt j (Nat.succ n) →
/// Nat.le deep m → close_within (F fine_j) (F base_i) (Rat.natDivSucc 1 e)`,
/// `deep := (Nat.succ (bound (add b (neg a))))·(modulus F a b u e) + bound
/// (add b (neg a))`, `base_i := sample_point a delta_m i`, `fine_j := add
/// base_i (mul (ofNat j) (mul delta_m (embed (natDivSucc 1 n))))`, `delta_m
/// := mul (add b (neg a)) (embed (natDivSucc 1 m))` — roadmap step 2, and
/// this module's own documentation's success condition on its own: EVERY
/// fine sample point inside coarse block `i` is within `1/(e+1)` of that
/// block's own coarse value `F(base_i)`, once the coarse block count `m` is
/// Archimedean-large enough relative to the modulus of uniform continuity
/// at target precision `e`.
///
/// Route: [`sample_offset_bound`] bounds the fine sample's OFFSET from
/// `base_i` by `delta_m` exactly; [`declare_mesh_le_of_ge`]'s own theorem
/// (at `outer := modulus F a b u e`) rescales `delta_m` down to `natDivSucc
/// 1 outer` PROVIDED `m` clears the Archimedean threshold `deep`;
/// `le_trans` chains the two into exactly `UniformlyContinuousOn.spec`'s
/// own hypothesis shape at `n := e`. The two domain-membership pairs `spec`
/// needs come from [`declare_fine_sample_in_bounds`] (the fine point) and
/// [`declare_riemann_sample_in_bounds`] (the coarse point, its `Nat.lt i
/// (Nat.succ m)` hypothesis obtained from this theorem's own `Nat.le i m`
/// via `Nat.lt_succ_of_le`).
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` from a `Theorem` here means
/// the kernel **refused** a proof, not that a script gave up.
pub(super) fn declare_fine_sample_close(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let f_ty = fn_ty(d, p);
    let logic = p.rat.int.logic;

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let e_fv = d.fresh_fvar();
    let e = d.kernel().fvar(e_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let j_fv = d.fresh_fvar();
    let j = d.kernel().fvar(j_fv);

    let hab_ty = cle(d, p, a, b);
    let hab_fv = d.fresh_fvar();
    let hab = d.kernel().fvar(hab_fv);

    let u_ty = d.const_app(p.uniformly_continuous_on, &[f, a, b]);
    let u_fv = d.fresh_fvar();
    let u = d.kernel().fvar(u_fv);

    let hi_ty = d.le(i, m);
    let hi_fv = d.fresh_fvar();
    let hi = d.kernel().fvar(hi_fv);

    let sn = d.succ(n);
    let hj_ty = d.lt(j, sn);
    let hj_fv = d.fresh_fvar();
    let hj = d.kernel().fvar(hj_fv);

    // outer := UniformlyContinuousOn.modulus F a b u e.
    let modulus_fn = d.const_app(p.uc_modulus, &[f, a, b, u]);
    let outer = d.apply(modulus_fn, &[e]);

    // deep, the same Archimedean threshold `mesh_le_of_ge` computes
    // internally at this `outer`.
    let width = width_of(d, p, a, b);
    let (c, magnitude, _width_le_mag) = direct_bound_le(d, p, width);
    let me = NatOps::mul(d, magnitude, outer);
    let deep = NatOps::add(d, me, c);
    let hge_ty = d.le(deep, m);
    let hge_fv = d.fresh_fvar();
    let hge = d.kernel().fvar(hge_fv);

    let (delta_m, delta_m_nonneg) = delta_nonneg_of(d, p, a, b, m, hab);
    let base_i = sample_point(d, p, a, delta_m, i);
    let (term, _term_nonneg, _term_le_delta_m) =
        fine_term_and_bounds(d, p, delta_m, n, j, hj, delta_m_nonneg);
    let fine_j = cadd(d, p, base_i, term);

    // hax, hxb : le a fine_j, le fine_j b.
    let (hax, hxb) = {
        let and_fine = d.const_app(p.fine_sample_in_bounds, &[a, b, m, n, i, j, hab, hi, hj]);
        let hax_ty = cle(d, p, a, fine_j);
        let hxb_ty = cle(d, p, fine_j, b);
        let hax = d.const_app(logic.and_left, &[hax_ty, hxb_ty, and_fine]);
        let hxb = d.const_app(logic.and_right, &[hax_ty, hxb_ty, and_fine]);
        (hax, hxb)
    };

    // hay, hyb : le a base_i, le base_i b.
    let (hay, hyb) = {
        let np = d.prelude();
        let hi_lt = d.const_app(np.lt_succ_of_le, &[i, m, hi]); // Nat.lt i (Nat.succ m)
        let and_coarse = d.const_app(p.riemann_sample_in_bounds, &[a, b, m, i, hab, hi_lt]);
        let hay_ty = cle(d, p, a, base_i);
        let hyb_ty = cle(d, p, base_i, b);
        let hay = d.const_app(logic.and_left, &[hay_ty, hyb_ty, and_coarse]);
        let hyb = d.const_app(logic.and_right, &[hay_ty, hyb_ty, and_coarse]);
        (hay, hyb)
    };

    // hclose : close_within fine_j base_i (natDivSucc 1 outer).
    let hclose = {
        let offset_bound = sample_offset_bound(d, p, base_i, delta_m, n, j, hj, delta_m_nonneg);
        // offset_bound : le (abs (add fine_j (neg base_i))) delta_m
        let mesh_bound = d.const_app(p.mesh_le_of_ge, &[a, b, outer, m, hab, hge]);
        // mesh_bound : le delta_m (embed (natDivSucc 1 outer))
        let one_nat = d.num(1);
        let out_rat = d.const_app(p.rat.nat_div_succ, &[one_nat, outer]);
        let out_bound = embed(d, p, out_rat);
        let ny = cneg(d, p, base_i);
        let diff = cadd(d, p, fine_j, ny);
        let abs_diff = d.const_app(p.abs, &[diff]);
        d.lemma(
            p.le_trans,
            &[abs_diff, delta_m, out_bound, offset_bound, mesh_bound],
        )
    };

    let conclusion = {
        let fx = d.apply(f, &[fine_j]);
        let fy = d.apply(f, &[base_i]);
        let one_nat = d.num(1);
        let out_rat = d.const_app(p.rat.nat_div_succ, &[one_nat, e]);
        close_within(d, p, fx, fy, out_rat)
    };

    let proof_body = d.const_app(
        p.uc_spec,
        &[f, a, b, u, e, fine_j, base_i, hax, hxb, hay, hyb, hclose],
    );

    let ty = {
        let after_hge = d.arrow(hge_ty, conclusion);
        let after_hj = d.arrow(hj_ty, after_hge);
        let after_hi = d.arrow(hi_ty, after_hj);
        // `u` (dependent, not `arrow`): `after_hi` mentions the fvar `u`
        // through `hge_ty`'s own `deep`/`outer := modulus F a b u e`.
        let after_u = d.pi_fv(u_fv, u_ty, after_hi);
        let after_hab = d.arrow(hab_ty, after_u);
        let over_j = d.pi_fv(j_fv, nat, after_hab);
        let over_i = d.pi_fv(i_fv, nat, over_j);
        let over_n = d.pi_fv(n_fv, nat, over_i);
        let over_m = d.pi_fv(m_fv, nat, over_n);
        let over_e = d.pi_fv(e_fv, nat, over_m);
        let over_b = d.pi_fv(b_fv, carrier, over_e);
        let over_a = d.pi_fv(a_fv, carrier, over_b);
        d.pi_fv(f_fv, f_ty, over_a)
    };
    let value = {
        let with_hge = d.lam_fv(hge_fv, hge_ty, proof_body);
        let with_hj = d.lam_fv(hj_fv, hj_ty, with_hge);
        let with_hi = d.lam_fv(hi_fv, hi_ty, with_hj);
        let with_u = d.lam_fv(u_fv, u_ty, with_hi);
        let with_hab = d.lam_fv(hab_fv, hab_ty, with_u);
        let over_j = d.lam_fv(j_fv, nat, with_hab);
        let over_i = d.lam_fv(i_fv, nat, over_j);
        let over_n = d.lam_fv(n_fv, nat, over_i);
        let over_m = d.lam_fv(m_fv, nat, over_n);
        let over_e = d.lam_fv(e_fv, nat, over_m);
        let over_b = d.lam_fv(b_fv, carrier, over_e);
        let over_a = d.lam_fv(a_fv, carrier, over_b);
        d.lam_fv(f_fv, f_ty, over_a)
    };

    d.kernel().add_declaration(Declaration::Theorem {
        name: p.fine_sample_close,
        uparams: vec![],
        ty,
        value,
    })
}

#[cfg(test)]
mod succ_shape_bridge_tests {
    use super::*;
    use crate::Declaration;

    /// Wraps [`succ_mul_succ`] at symbolic `n, m` in a throwaway anonymous
    /// theorem and lets the kernel accept or reject it — building the Rust
    /// closures is not evidence the *term* is well-typed, only
    /// `Kernel::add_declaration`'s trusted checker is (the same idiom as
    /// `sqrt.rs`'s `bridging_smoke_tests`).
    #[test]
    fn succ_mul_succ_type_checks_symbolically() {
        let mut kernel = crate::Kernel::new();
        let p = crate::build_creal_prelude(&mut kernel).expect("CReal prelude must build");
        let mut d = IntDev::new(&mut kernel, p.rat.int);
        let nat = d.nat_ty();

        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);

        let (m_prime, proof) = succ_mul_succ(&mut d, n, m);

        let sn = d.succ(n);
        let sm = d.succ(m);
        let lhs = NatOps::mul(&mut d, sn, sm);
        let succ_m_prime = d.succ(m_prime);
        let claim = d.eq(lhs, succ_m_prime);

        let value = {
            let with_m = d.lam_fv(m_fv, nat, proof);
            d.lam_fv(n_fv, nat, with_m)
        };
        let ty = {
            let over_m = d.pi_fv(m_fv, nat, claim);
            d.pi_fv(n_fv, nat, over_m)
        };

        let anon = d.kernel().anon();
        let name = d.kernel().name_str(anon, "succShapeBridgeSmoke");
        let result = d.kernel().add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty,
            value,
        });
        assert!(
            result.is_ok(),
            "succ_mul_succ must type-check: {:?}",
            result.err()
        );
    }

    /// The mandatory concrete instantiation `n = 2, m = 3` (`n != m`, per the
    /// task's own caution that a transposed-argument defect is invisible at
    /// `n = m`): `3 * 4 = 12 = succ 11`, `m_prime = 6 + 2 + 3 = 11`. Checked
    /// by `Eq.refl` against the literals `11`/`12` — the kernel's own
    /// reduction, not a comment, is what "reduces" means here.
    #[test]
    fn succ_mul_succ_reduces_at_two_three() {
        let mut kernel = crate::Kernel::new();
        let p = crate::build_creal_prelude(&mut kernel).expect("CReal prelude must build");
        let mut d = IntDev::new(&mut kernel, p.rat.int);

        let n = d.num(2);
        let m = d.num(3);
        let (m_prime, _proof) = succ_mul_succ(&mut d, n, m);

        // m_prime must independently equal the literal 11 (n*m+n+m = 6+2+3).
        let eleven = d.num(11);
        let m_prime_eq_eleven = d.eq(m_prime, eleven);
        let m_prime_refl = d.refl(eleven);

        let twelve = d.num(12);
        let succ_m_prime = d.succ(m_prime);
        let succ_m_prime_eq_twelve = d.eq(succ_m_prime, twelve);
        let succ_m_prime_refl = d.refl(twelve);

        let anon = d.kernel().anon();
        let name1 = d
            .kernel()
            .name_str(anon, "succShapeBridgeSmokeMPrimeEleven");
        let r1 = d.kernel().add_declaration(Declaration::Theorem {
            name: name1,
            uparams: vec![],
            ty: m_prime_eq_eleven,
            value: m_prime_refl,
        });
        assert!(r1.is_ok(), "m_prime must reduce to 11: {:?}", r1.err());

        let name2 = d
            .kernel()
            .name_str(anon, "succShapeBridgeSmokeSuccMPrimeTwelve");
        let r2 = d.kernel().add_declaration(Declaration::Theorem {
            name: name2,
            uparams: vec![],
            ty: succ_m_prime_eq_twelve,
            value: succ_m_prime_refl,
        });
        assert!(r2.is_ok(), "succ m_prime must reduce to 12: {:?}", r2.err());
    }
}

#[cfg(test)]
mod sample_offset_bound_tests {
    use super::*;
    use crate::Declaration;

    /// Wraps [`sample_offset_bound`] (roadmap step 1's per-term fine-vs-coarse
    /// bound, toward `riemannSum_cauchy`) in a throwaway anonymous theorem,
    /// symbolically in `base, delta, n, j`, and lets the kernel accept or
    /// reject it -- the same idiom as `succ_shape_bridge_tests` above.
    #[test]
    fn sample_offset_bound_type_checks_symbolically() {
        let mut kernel = crate::Kernel::new();
        let p = crate::build_creal_prelude(&mut kernel).expect("CReal prelude must build");
        let mut d = IntDev::new(&mut kernel, p.rat.int);
        let carrier = creal_ty(&mut d, p);
        let nat = d.nat_ty();

        let base_fv = d.fresh_fvar();
        let base = d.kernel().fvar(base_fv);
        let delta_fv = d.fresh_fvar();
        let delta = d.kernel().fvar(delta_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);

        let n_succ = d.succ(n);
        let hlt_ty = d.lt(j, n_succ);
        let hlt_fv = d.fresh_fvar();
        let hlt = d.kernel().fvar(hlt_fv);

        let zero_c = czero(&mut d, p);
        let delta_nonneg_ty = cle(&mut d, p, zero_c, delta);
        let delta_nonneg_fv = d.fresh_fvar();
        let delta_nonneg = d.kernel().fvar(delta_nonneg_fv);

        let proof_body = sample_offset_bound(&mut d, p, base, delta, n, j, hlt, delta_nonneg);

        // Reconstruct the same conclusion type independently -- `le (abs
        // diff) delta`, `diff := (base + mul (ofNat j) (mul delta (embed
        // (natDivSucc 1 n)))) + (neg base)`.
        let one_nat = d.num(1);
        let frac_n_rat = d.const_app(p.rat.nat_div_succ, &[one_nat, n]);
        let frac_n = embed(&mut d, p, frac_n_rat);
        let delta_fine = cmul(&mut d, p, delta, frac_n);
        let of_nat_j = d.const_app(p.of_nat, &[j]);
        let term = cmul(&mut d, p, of_nat_j, delta_fine);
        let x_j = cadd(&mut d, p, base, term);
        let nb = cneg(&mut d, p, base);
        let diff = cadd(&mut d, p, x_j, nb);
        let abs_diff = d.const_app(p.abs, &[diff]);
        let concl = cle(&mut d, p, abs_diff, delta);

        let ty = {
            let after_nonneg = d.arrow(delta_nonneg_ty, concl);
            let after_hlt = d.arrow(hlt_ty, after_nonneg);
            let over_j = d.pi_fv(j_fv, nat, after_hlt);
            let over_n = d.pi_fv(n_fv, nat, over_j);
            let over_delta = d.pi_fv(delta_fv, carrier, over_n);
            d.pi_fv(base_fv, carrier, over_delta)
        };
        let value = {
            let with_nonneg = d.lam_fv(delta_nonneg_fv, delta_nonneg_ty, proof_body);
            let with_hlt = d.lam_fv(hlt_fv, hlt_ty, with_nonneg);
            let over_j = d.lam_fv(j_fv, nat, with_hlt);
            let over_n = d.lam_fv(n_fv, nat, over_j);
            let over_delta = d.lam_fv(delta_fv, carrier, over_n);
            d.lam_fv(base_fv, carrier, over_delta)
        };

        let anon = d.kernel().anon();
        let name = d.kernel().name_str(anon, "sampleOffsetBoundSmoke");
        let result = d.kernel().add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty,
            value,
        });
        assert!(
            result.is_ok(),
            "sample_offset_bound must type-check: {:?}",
            result.err()
        );
    }
}

#[cfg(test)]
mod le_add_of_abs_sub_le_tests {
    use super::*;
    use crate::Declaration;

    /// The mandatory concrete instantiation: `x := ofNat 3`, `y := ofNat 2`,
    /// `q := Rat.natDivSucc 1 0` (`= 1`) — the TIGHT boundary case `3 ≤ 2 +
    /// 1`, chosen (per this slice's own caution about argument-order
    /// defects) so that swapping `x`/`y`, or adding `q` on the wrong side,
    /// produces a DIFFERENT concrete conclusion type than the one this test
    /// reconstructs independently -- the kernel's own type-checker is what
    /// catches the mismatch, not a comment.
    ///
    /// `h` (the hypothesis `le (abs (add x (neg y))) (ofRat q)`) is left an
    /// assumed free variable rather than proved from scratch — proving it
    /// numerically would need `ofNat` subtraction reduction, `abs` of a
    /// literal, and a `Rat` literal identity, none of which this slice's
    /// declaration itself needs. What this test checks is exactly what the
    /// declaration's own TYPE promises: applying it at concrete literals
    /// yields a term whose type is the expected concrete conclusion.
    #[test]
    fn le_add_of_abs_sub_le_applies_at_three_two_and_one() {
        let mut kernel = crate::Kernel::new();
        let p = crate::build_creal_prelude(&mut kernel).expect("CReal prelude must build");
        let mut d = IntDev::new(&mut kernel, p.rat.int);

        let three = d.num(3);
        let two = d.num(2);
        let x = d.const_app(p.of_nat, &[three]);
        let y = d.const_app(p.of_nat, &[two]);

        let one_nat = d.num(1);
        let zero_nat = d.num(0);
        let q = d.const_app(p.rat.nat_div_succ, &[one_nat, zero_nat]); // 1/(0+1) = 1

        let ny = cneg(&mut d, p, y);
        let diff = cadd(&mut d, p, x, ny);
        let abs_diff = d.const_app(p.abs, &[diff]);
        let q_embed = embed(&mut d, p, q);
        let hyp_ty = cle(&mut d, p, abs_diff, q_embed);

        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);

        let applied = d.const_app(p.le_add_of_abs_sub_le, &[x, y, q, h]);

        // Independently reconstruct the expected conclusion: le x (add y
        // q_embed), i.e. `3 ≤ 2 + 1`.
        let yq = cadd(&mut d, p, y, q_embed);
        let expected = cle(&mut d, p, x, yq);

        let ty = d.arrow(hyp_ty, expected);
        let value = d.lam_fv(h_fv, hyp_ty, applied);

        let anon = d.kernel().anon();
        let name = d.kernel().name_str(anon, "leAddOfAbsSubLeThreeTwoOneSmoke");
        let result = d.kernel().add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty,
            value,
        });
        assert!(
            result.is_ok(),
            "le_add_of_abs_sub_le must apply at (3, 2, 1) with the expected \
             conclusion type: {:?}",
            result.err()
        );
    }
}

#[cfg(test)]
mod two_sided_of_abs_sub_le_tests {
    use super::*;
    use crate::Declaration;

    /// The mandatory concrete instantiation, same triple as
    /// `le_add_of_abs_sub_le_applies_at_three_two_and_one`: `x := 3`,
    /// `y := 2`, `q := 1`, expecting `And (le 3 (2+1)) (le 2 (3+1))` --
    /// both conjuncts tight (`3 ≤ 3`, and `2 ≤ 4` slack), independently
    /// reconstructed so a swapped conjunct, or a conclusion built from the
    /// wrong endpoint, fails to match.
    #[test]
    fn two_sided_of_abs_sub_le_applies_at_three_two_and_one() {
        let mut kernel = crate::Kernel::new();
        let p = crate::build_creal_prelude(&mut kernel).expect("CReal prelude must build");
        let mut d = IntDev::new(&mut kernel, p.rat.int);
        let logic = p.rat.int.logic;

        let three = d.num(3);
        let two = d.num(2);
        let x = d.const_app(p.of_nat, &[three]);
        let y = d.const_app(p.of_nat, &[two]);

        let one_nat = d.num(1);
        let zero_nat = d.num(0);
        let q = d.const_app(p.rat.nat_div_succ, &[one_nat, zero_nat]); // 1/(0+1) = 1

        let ny = cneg(&mut d, p, y);
        let diff = cadd(&mut d, p, x, ny);
        let abs_diff = d.const_app(p.abs, &[diff]);
        let q_embed = embed(&mut d, p, q);
        let hyp_ty = cle(&mut d, p, abs_diff, q_embed);

        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);

        let applied = d.const_app(p.two_sided_of_abs_sub_le, &[x, y, q, h]);

        // Independently reconstruct: And (le x (add y q_embed)) (le y (add x
        // q_embed)), i.e. `And (3 ≤ 2 + 1) (2 ≤ 3 + 1)`.
        let yq = cadd(&mut d, p, y, q_embed);
        let xq = cadd(&mut d, p, x, q_embed);
        let left_ty = cle(&mut d, p, x, yq);
        let right_ty = cle(&mut d, p, y, xq);
        let expected = d.const_app(logic.and, &[left_ty, right_ty]);

        let ty = d.arrow(hyp_ty, expected);
        let value = d.lam_fv(h_fv, hyp_ty, applied);

        let anon = d.kernel().anon();
        let name = d
            .kernel()
            .name_str(anon, "twoSidedOfAbsSubLeThreeTwoOneSmoke");
        let result = d.kernel().add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty,
            value,
        });
        assert!(
            result.is_ok(),
            "two_sided_of_abs_sub_le must apply at (3, 2, 1) with the \
             expected conclusion type: {:?}",
            result.err()
        );
    }
}

#[cfg(test)]
mod fine_block_sum_close_tests {
    use super::*;
    use crate::Declaration;

    /// The mandatory concrete instantiation: `F := fun x => x` (so
    /// `u := CReal.uniformly_continuous_id a b` is a REAL witness, not a
    /// placeholder), `a := 0`, `b := 1`, `e := 0`, `m := 2`, `n := 1`,
    /// `i := 1` -- `m != n` and `i != 0`, per this slice's own caution that a
    /// transposed-argument defect is invisible at equal/zero indices.
    /// `hab`/`hi`/`hge` are left assumed (proving them numerically needs
    /// `bound`/`Nat.le` computation this declaration's own TYPE does not
    /// need), so what this test checks is exactly the declaration's own
    /// promise: applying it at these literals yields a term whose type is
    /// the expected concrete `And` conclusion, independently reconstructed
    /// from the same `delta_nonneg_of`/`sample_point`/`summand_fn` building
    /// blocks the real declaration uses.
    #[test]
    fn fine_block_sum_close_applies_at_concrete_literals() {
        let mut kernel = crate::Kernel::new();
        let p = crate::build_creal_prelude(&mut kernel).expect("CReal prelude must build");
        let mut d = IntDev::new(&mut kernel, p.rat.int);

        let carrier = creal_ty(&mut d, p);
        let identity_body = {
            let x_fv = d.fresh_fvar();
            let x = d.kernel().fvar(x_fv);
            d.lam_fv(x_fv, carrier, x)
        };

        let zero_nat = d.num(0);
        let one_nat_lit = d.num(1);
        let a = d.const_app(p.of_nat, &[zero_nat]);
        let b = d.const_app(p.of_nat, &[one_nat_lit]);
        let e = d.num(0);
        let m = d.num(2);
        let n = d.num(1);
        let i = d.num(1);

        let u = d.const_app(p.uniformly_continuous_id, &[a, b]);

        let hab_ty = cle(&mut d, p, a, b);
        let hab_fv = d.fresh_fvar();
        let hab = d.kernel().fvar(hab_fv);

        let hi_ty = d.le(i, m);
        let hi_fv = d.fresh_fvar();
        let hi = d.kernel().fvar(hi_fv);

        // deep, the same way the real declaration computes it, at F :=
        // identity (so `modulus_fn` reduces to `fun n => n`, though this
        // test does not need that reduction to build the HYPOTHESIS type).
        let modulus_fn = d.const_app(p.uc_modulus, &[identity_body, a, b, u]);
        let outer = d.apply(modulus_fn, &[e]);
        let width = width_of(&mut d, p, a, b);
        let (c, magnitude, _width_le_mag) = direct_bound_le(&mut d, p, width);
        let me = NatOps::mul(&mut d, magnitude, outer);
        let deep = NatOps::add(&mut d, me, c);
        let hge_ty = d.le(deep, m);
        let hge_fv = d.fresh_fvar();
        let hge = d.kernel().fvar(hge_fv);

        let applied = d.const_app(
            p.fine_block_sum_close,
            &[identity_body, a, b, e, m, n, i, hab, u, hi, hge],
        );

        // Independently reconstruct the expected conclusion, using the same
        // building blocks `declare_fine_block_sum_close` itself uses.
        let (delta_m, _delta_m_nonneg) = delta_nonneg_of(&mut d, p, a, b, m, hab);
        let base_i = sample_point(&mut d, p, a, delta_m, i);
        let fbase = d.apply(identity_body, &[base_i]);
        let one_nat = d.num(1);
        let frac_n_rat = d.const_app(p.rat.nat_div_succ, &[one_nat, n]);
        let frac_n = embed(&mut d, p, frac_n_rat);
        let delta_fine = cmul(&mut d, p, delta_m, frac_n);
        let eps_rat = d.const_app(p.rat.nat_div_succ, &[one_nat, e]);
        let eps_embed = embed(&mut d, p, eps_rat);
        let sn = d.succ(n);

        let block_summand = summand_fn(&mut d, p, identity_body, base_i, delta_fine);
        let block_sum = d.const_app(p.sum_range, &[block_summand, sn]);
        let coarse_term = cmul(&mut d, p, fbase, delta_m);
        let eps_term = cmul(&mut d, p, eps_embed, delta_m);
        let coarse_plus_eps = cadd(&mut d, p, coarse_term, eps_term);
        let block_sum_plus_eps = cadd(&mut d, p, block_sum, eps_term);
        let upper_ty = cle(&mut d, p, block_sum, coarse_plus_eps);
        let lower_ty = cle(&mut d, p, coarse_term, block_sum_plus_eps);
        let logic = p.rat.int.logic;
        let expected = d.const_app(logic.and, &[upper_ty, lower_ty]);

        let ty = {
            let after_hge = d.arrow(hge_ty, expected);
            let after_hi = d.arrow(hi_ty, after_hge);
            d.arrow(hab_ty, after_hi)
        };
        let value = {
            let with_hge = d.lam_fv(hge_fv, hge_ty, applied);
            let with_hi = d.lam_fv(hi_fv, hi_ty, with_hge);
            d.lam_fv(hab_fv, hab_ty, with_hi)
        };

        let anon = d.kernel().anon();
        let name = d
            .kernel()
            .name_str(anon, "fineBlockSumCloseConcreteLiteralsSmoke");
        let result = d.kernel().add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty,
            value,
        });
        assert!(
            result.is_ok(),
            "fine_block_sum_close must apply at (identity, 0, 1, e=0, m=2, \
             n=1, i=1) with the expected conclusion type: {:?}",
            result.err()
        );
    }
}

#[cfg(test)]
mod mesh_reciprocal_mul_tests {
    use super::*;
    use crate::Declaration;

    /// The mandatory concrete instantiation: `n := 1, m := 2` (`n != m`, per
    /// this slice's own caution about transposed-argument defects). `m_prime
    /// = (n*m)+n+m = 2+1+2 = 5`, and `(succ n)*(succ m) = 2*3 = 6 = succ 5`,
    /// so `natDivSucc 1 5 = 1/6` should equal `natDivSucc 1 1 * natDivSucc 1
    /// 2 = (1/2)*(1/3)`. This test is the load-bearing check on the
    /// declaration's OWN central claim -- that the kernel's conversion
    /// checker actually bridges `Nat.mul (succ n) (succ m)` down to `succ
    /// m_prime` and `Int.mul (ofNat 1) (ofNat 1)` down to `ofNat 1` with no
    /// extra rewrite step -- applied at concrete literals where every
    /// intermediate `Nat`/`Int` computation fully reduces, not merely
    /// symbolically.
    #[test]
    fn mesh_reciprocal_mul_applies_at_one_two_and_reduces_to_five() {
        let mut kernel = crate::Kernel::new();
        let p = crate::build_creal_prelude(&mut kernel).expect("CReal prelude must build");
        let mut d = IntDev::new(&mut kernel, p.rat.int);

        let n = d.num(1);
        let m = d.num(2);
        let applied = d.const_app(p.mesh_reciprocal_mul, &[n, m]);

        // Independently reconstruct the expected conclusion at the literal
        // `m_prime := 5`, NOT by recomputing `((n*m)+n)+m` symbolically --
        // the whole point is to check the declaration's result against a
        // literal the test built independently.
        let one_nat = d.num(1);
        let five = d.num(5);
        let dn = d.const_app(p.rat.nat_div_succ, &[one_nat, n]);
        let dm = d.const_app(p.rat.nat_div_succ, &[one_nat, m]);
        let lhs = rmul(&mut d, dn, dm);
        let rhs = d.const_app(p.rat.nat_div_succ, &[one_nat, five]);
        let expected = req(&mut d, lhs, rhs);

        let anon = d.kernel().anon();
        let name = d
            .kernel()
            .name_str(anon, "meshReciprocalMulOneTwoFiveSmoke");
        let result = d.kernel().add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty: expected,
            value: applied,
        });
        assert!(
            result.is_ok(),
            "mesh_reciprocal_mul at (1, 2) must have type Eq Rat \
             (natDivSucc 1 1 * natDivSucc 1 2) (natDivSucc 1 5): {:?}",
            result.err()
        );
    }
}

#[cfg(test)]
mod equiv_abs_diff_le_tests {
    use super::*;
    use crate::Declaration;

    /// The mandatory concrete instantiation: `x := y := ofNat 3` (so `hxy`
    /// is a REAL proof, `equiv_refl (ofNat 3)`, not an assumed free
    /// variable) and `e := 0`, expecting `le (abs (add x (neg x))) (embed
    /// (natDivSucc 1 0))` -- independently reconstructed so a swapped
    /// argument or a wrong target bound fails to match.
    #[test]
    fn equiv_abs_diff_le_applies_at_equal_literals() {
        let mut kernel = crate::Kernel::new();
        let p = crate::build_creal_prelude(&mut kernel).expect("CReal prelude must build");
        let mut d = IntDev::new(&mut kernel, p.rat.int);

        let three = d.num(3);
        let x = d.const_app(p.of_nat, &[three]);
        let hxy = d.lemma(p.equiv_refl, &[x]);
        let zero_nat = d.num(0);

        let applied = d.const_app(p.equiv_abs_diff_le, &[x, x, hxy, zero_nat]);

        let diff = {
            let nx = cneg(&mut d, p, x);
            cadd(&mut d, p, x, nx)
        };
        let abs_diff = d.const_app(p.abs, &[diff]);
        let one_nat = d.num(1);
        let q = d.const_app(p.rat.nat_div_succ, &[one_nat, zero_nat]);
        let embed_q = embed(&mut d, p, q);
        let expected = cle(&mut d, p, abs_diff, embed_q);

        let anon = d.kernel().anon();
        let name = d
            .kernel()
            .name_str(anon, "equivAbsDiffLeEqualLiteralsSmoke");
        let result = d.kernel().add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty: expected,
            value: applied,
        });
        assert!(
            result.is_ok(),
            "equiv_abs_diff_le at (ofNat 3, ofNat 3, refl, 0) must have the \
             expected conclusion type: {:?}",
            result.err()
        );
    }
}
