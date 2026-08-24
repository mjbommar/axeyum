//! **Bishop's speed-up combinator**: turn a sequence that is regular up to a
//! constant factor into an exactly-regular one.
//!
//! ## The gap this closes
//!
//! `CReal.sqrt`'s missing piece (`sqrt.rs`'s own module docs) is a rational
//! approximant with a *known-shape* error bound: three composed error sources
//! give `|sqrtApprox x m − sqrtApprox x n| ≤ K/(m+1) + K/(n+1)` for some `K >
//! 1`, but [`CReal.Regular`](super::CRealPrelude::regular_pred) demands
//! exactly `1/(m+1) + 1/(n+1)`, with **no slack**. This module builds the
//! general reindexing combinator that closes that gap for *any* sequence of
//! this shape, not just `sqrtApprox`: sample deeper, and the constant factor
//! divides out exactly.
//!
//! ## Why `product.rs`'s machinery does not already do this
//!
//! [`regular_between`](super::product::regular_between) and
//! [`fuse_at`](super::product::fuse_at) compare two samples of the same
//! already-`Regular` `CReal` — `regular_between` literally instantiates
//! `p.regular` (the fact that `CReal.seq x` is regular) at the two indices.
//! A `KRegular f c` hypothesis below is a raw statement about a bare `Nat →
//! Rat` function that is not (yet, and may never be) packaged as a `CReal` at
//! all — there is no `CReal.regular` to instantiate. So `regular_between`'s
//! crude, any-constant estimate is not reachable here; what *is* reachable,
//! and much stronger, is exactness (see below).
//!
//! ## The index, additively, and why the estimate is exact — not merely bounded
//!
//! `CReal.mul`'s own sampling index `(c+1)·n + c` (`product.rs`,
//! [`mul_index`](super::product::mul_index)) is reused verbatim as the
//! speed-up index, and for the same reason it was built additively there:
//! `Rat.natDivSucc_scale : ∀ c m, natDivSucc (c+1) ((c+1)·m + c) = natDivSucc
//! 1 m` reads the deep sample's own modulus contribution back to the target
//! one **by an equality**, not an inequality, and needs no `Nat.sub` to state
//! the index in the first place. So [`declare_regular_of_kregular`] does not
//! need `regular_between`'s weakening step at all: two rewrites along
//! `natDivSucc_scale` turn a `KRegular f c` instance at the two speed-up
//! indices directly into a `Regular (speedup f c)` instance, exactly.
//!
//! ## What this does not do
//!
//! Composing this with `sqrtApprox` — i.e. proving `sqrtApprox` itself is
//! `KRegular` for some concrete `c` — is not attempted here; that is the
//! ~2000-line rational-inequality half `sqrt.rs`'s docs describe. This module
//! is the reusable combinator side of the gap, deliberately generic in `f`
//! and `c`.

use crate::KernelError;
use crate::env::{Declaration, ReducibilityHint};
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::nat_prelude::NatOps;
use crate::rat_prelude::group::rsub;
use crate::rat_prelude::ops::{radd, rat_eq_rewrite, rat_ty};

use super::product::mul_index;
use super::{CRealPrelude, DERIVED_HEIGHT, div_succ, seq_ty, within};

/// `Rat.natDivSucc k j`, with a **symbolic** numerator — a local copy of
/// `product::div_succ_at` (private there): [`super::div_succ`] only takes a
/// literal, and every bound here is scaled by `Nat.succ c`.
fn div_succ_at(d: &mut IntDev<'_>, p: CRealPrelude, k: ExprId, j: ExprId) -> ExprId {
    d.const_app(p.rat.nat_div_succ, &[k, j])
}

/// `CReal.KRegular f c := ∀ m n, Within (f m − f n) (natDivSucc (c+1) m +
/// natDivSucc (c+1) n)` — Bishop regularity with the modulus `(c+1)/(m+1) +
/// (c+1)/(n+1)`, i.e. regular up to the constant factor `c+1`.
///
/// Parametrized by `c` rather than the raw constant `K = c+1` for the same
/// reason [`CReal.mulShift`](super::CRealPrelude::mul_shift)/[`mul_index`]
/// are: it keeps the sampling index `(c+1)·n + c` and its read-back
/// (`Rat.natDivSucc_scale`) addition-only, with **no `Nat.sub`** — a `K : Nat`
/// parameter with `K = 0` would make the modulus `0/(m+1) + 0/(n+1) ≡ 0`, a
/// degenerate (and for most `f`, false) hypothesis; `c := K − 1` would need a
/// subtraction to recover `K`. Fixing `K := c+1` rules the degenerate case out
/// by construction and needs no side condition.
fn declare_kregular(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let rat = p.rat;
    let sequences = seq_ty(d);
    let nat = d.nat_ty();
    let prop = d.kernel().sort_zero();

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let succ_c = d.succ(c);
    let left = d.apply(f, &[m]);
    let right = d.apply(f, &[n]);
    let difference = rsub(d, rat, left, right);
    let bound = {
        let a = div_succ_at(d, p, succ_c, m);
        let b = div_succ_at(d, p, succ_c, n);
        radd(d, a, b)
    };
    let claim = within(d, p, difference, bound);
    let body = {
        let over_n = d.pi_fv(n_fv, nat, claim);
        d.pi_fv(m_fv, nat, over_n)
    };
    let value = {
        let with_c = d.lam_fv(c_fv, nat, body);
        d.lam_fv(f_fv, sequences, with_c)
    };
    let ty = {
        let inner = d.arrow(nat, prop);
        d.arrow(sequences, inner)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.k_regular_pred,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(DERIVED_HEIGHT),
    })
}

/// `CReal.speedup f c n := f ((c+1)·n + c)` — Bishop's speed-up combinator,
/// reusing [`mul_index`] (`CReal.mul`'s own sampling index) verbatim. Additive
/// throughout: **no `Nat.sub`** anywhere in the index.
fn declare_speedup_def(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let sequences = seq_ty(d);
    let nat = d.nat_ty();
    let rat_carrier = rat_ty(d);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let index = mul_index(d, c, n);
    let body = d.apply(f, &[index]);
    let value = {
        let with_n = d.lam_fv(n_fv, nat, body);
        let with_c = d.lam_fv(c_fv, nat, with_n);
        d.lam_fv(f_fv, sequences, with_c)
    };
    let ty = {
        let inner2 = d.arrow(nat, rat_carrier);
        let inner1 = d.arrow(nat, inner2);
        d.arrow(sequences, inner1)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.speedup,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(DERIVED_HEIGHT + 44),
    })
}

/// `CReal.regular_of_kregular : ∀ f c, KRegular f c → Regular (speedup f c)`,
/// **the headline result**.
///
/// Exact, with no slack: at index `n` the speed-up samples `f` at the index
/// `(c+1)·n + c`, and instantiating `KRegular f c` at the two speed-up
/// indices — `(c+1)·m + c` for `m` and `(c+1)·n + c` for `n` — gives a bound
/// of `natDivSucc (c+1)` at each of those two deep indices;
/// `Rat.natDivSucc_scale` reads each straight back to `natDivSucc 1` at
/// `m`/`n` respectively, exactly `Regular`'s own bound. Two rewrites, no
/// weakening step.
fn declare_regular_of_kregular(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let rat = p.rat;
    let sequences = seq_ty(d);
    let nat = d.nat_ty();

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let hyp_ty = d.const_app(p.k_regular_pred, &[f, c]);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let target = d.const_app(p.speedup, &[f, c]);
    let concl_ty = d.const_app(p.regular_pred, &[target]);

    let proof_inner = {
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);

        let im = mul_index(d, c, m);
        let in_ = mul_index(d, c, n);
        let instance = d.apply(h, &[im, in_]);
        // instance : Within (f im - f in_)
        //              (natDivSucc (c+1) im + natDivSucc (c+1) in_)

        let succ_c = d.succ(c);
        let bound_left = div_succ_at(d, p, succ_c, im);
        let bound_right = div_succ_at(d, p, succ_c, in_);
        let target_left = div_succ(d, p, 1, m);
        let target_right = div_succ(d, p, 1, n);

        let fm = d.apply(f, &[im]);
        let fn_ = d.apply(f, &[in_]);
        let diff = rsub(d, rat, fm, fn_);

        let scale_m = d.lemma(rat.nat_div_succ_scale, &[c, m]);
        let scale_n = d.lemma(rat.nat_div_succ_scale, &[c, n]);

        let step1 = rat_eq_rewrite(d, bound_left, target_left, scale_m, instance, &|d, t| {
            let rhs = radd(d, t, bound_right);
            within(d, p, diff, rhs)
        });
        let step2 = rat_eq_rewrite(d, bound_right, target_right, scale_n, step1, &|d, t| {
            let rhs = radd(d, target_left, t);
            within(d, p, diff, rhs)
        });
        // step2 : Within (f im - f in_) (natDivSucc 1 m + natDivSucc 1 n),
        // definitionally `Within (speedup f c m - speedup f c n) (modulus m n)`.

        let with_n = d.lam_fv(n_fv, nat, step2);
        d.lam_fv(m_fv, nat, with_n)
    };

    let value = {
        let with_h = d.lam_fv(h_fv, hyp_ty, proof_inner);
        let with_c = d.lam_fv(c_fv, nat, with_h);
        d.lam_fv(f_fv, sequences, with_c)
    };
    let ty = {
        let inner = d.arrow(hyp_ty, concl_ty);
        let with_c = d.pi_fv(c_fv, nat, inner);
        d.pi_fv(f_fv, sequences, with_c)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.regular_of_kregular,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CReal.speedup_close : ∀ f c, KRegular f c → ∀ n, Within (f n − speedup f
/// c n) (natDivSucc (c+1) n + natDivSucc 1 n)`.
///
/// **A bound, not an equivalence.** It measures how far the original sample
/// `f n` sits from the speed-up's sample at the *same* index `n` — both sides
/// are plain rationals, `speedup f c n` unfolding to `f ((c+1)·n + c)` — via
/// one `KRegular` instance at `(n, (c+1)·n + c)` and one
/// `Rat.natDivSucc_scale` rewrite on its second summand. The bound does shrink
/// in `n` (it is `≤ (c+2)/(n+1)` after `Rat.natDivSucc_add`, not derived here)
/// but is not `Regular`'s exact modulus, and this does **not** by itself give
/// any `CReal.Equiv` between `f` and its speed-up: that needs `f` packaged as
/// a `CReal` in the first place, which a bare `KRegular f c` hypothesis does
/// not supply.
fn declare_speedup_close(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let rat = p.rat;
    let sequences = seq_ty(d);
    let nat = d.nat_ty();

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let hyp_ty = d.const_app(p.k_regular_pred, &[f, c]);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let proof_inner = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);

        let idx = mul_index(d, c, n);
        let instance = d.apply(h, &[n, idx]);
        // instance : Within (f n - f idx)
        //              (natDivSucc (c+1) n + natDivSucc (c+1) idx)

        let succ_c = d.succ(c);
        let bound_left = div_succ_at(d, p, succ_c, n);
        let bound_right = div_succ_at(d, p, succ_c, idx);
        let target_right = div_succ(d, p, 1, n);

        let fn_left = d.apply(f, &[n]);
        let fn_right = d.apply(f, &[idx]);
        let diff = rsub(d, rat, fn_left, fn_right);

        let scale = d.lemma(rat.nat_div_succ_scale, &[c, n]);

        let step = rat_eq_rewrite(d, bound_right, target_right, scale, instance, &|d, t| {
            let rhs = radd(d, bound_left, t);
            within(d, p, diff, rhs)
        });
        // step : Within (f n - f idx) (natDivSucc (c+1) n + natDivSucc 1 n),
        // definitionally `Within (f n - speedup f c n) (...)`.
        d.lam_fv(n_fv, nat, step)
    };

    let value = {
        let with_h = d.lam_fv(h_fv, hyp_ty, proof_inner);
        let with_c = d.lam_fv(c_fv, nat, with_h);
        d.lam_fv(f_fv, sequences, with_c)
    };

    let ty = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let succ_c = d.succ(c);
        let bound_left = div_succ_at(d, p, succ_c, n);
        let target_right = div_succ(d, p, 1, n);
        let bound = radd(d, bound_left, target_right);
        let target = d.const_app(p.speedup, &[f, c]);
        let speedup_n = d.apply(target, &[n]);
        let fn_left = d.apply(f, &[n]);
        let diff = rsub(d, rat, fn_left, speedup_n);
        let claim = within(d, p, diff, bound);
        let over_n = d.pi_fv(n_fv, nat, claim);
        let inner = d.arrow(hyp_ty, over_n);
        let with_c = d.pi_fv(c_fv, nat, inner);
        d.pi_fv(f_fv, sequences, with_c)
    };

    d.kernel().add_declaration(Declaration::Theorem {
        name: p.speedup_close,
        uparams: vec![],
        ty,
        value,
    })
}

/// Admit `CReal.KRegular`, `CReal.speedup`, `CReal.regular_of_kregular`,
/// `CReal.speedup_close`.
///
/// # Errors
///
/// Returns the trusted gate's rejection.
pub(super) fn declare_speedup(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    declare_kregular(d, p)?;
    declare_speedup_def(d, p)?;
    declare_regular_of_kregular(d, p)?;
    declare_speedup_close(d, p)
}
