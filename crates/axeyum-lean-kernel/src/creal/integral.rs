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
    CRealPrelude, DERIVED_HEIGHT, and_intro, cadd, creal_ty, div_succ, embed, equiv, sample, within,
};
use crate::KernelError;
use crate::env::{Declaration, ReducibilityHint};
use crate::expr::ExprId;
use crate::int_prelude::ops::{IntDev, exists_elim};
use crate::nat_prelude::NatOps;
use crate::rat_prelude::ops::{
    nat_eq_to_rat, nat_rewrite_prop, radd, rat_eq_rewrite, rchain, req, rle, rmul, rneg, rone,
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
    declare_riemann_sum_const(d, p)
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
#[allow(dead_code)] // staged for the per-term UC bound (riemannSum_cauchy), not yet landed
fn succ_mul_succ(d: &mut IntDev<'_>, n: ExprId, m: ExprId) -> (ExprId, ExprId) {
    let np = d.prelude();
    let sm = d.succ(m);
    let nm = NatOps::mul(d, n, m);
    let nm_n = d.const_app(np.add, &[nm, n]);
    let m_prime = d.const_app(np.add, &[nm_n, m]);
    let proof = d.lemma(np.succ_mul, &[n, sm]);
    (m_prime, proof)
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
