//! **`CReal.UniformlyContinuousOn`** (ADR-0512, continuing phase R11): a
//! modulus-carrying notion of uniform continuity on an interval, and the
//! bridge from it to the sequential [`CReal.ContinuousAt`](super::CRealPrelude::continuous_at)
//! [`declare_convergence`](super::convergence::declare_convergence) already
//! has.
//!
//! ## Why the modulus is data, not a proof
//!
//! [`CReal.pos_bound_of_lt`](super::CRealPrelude::pos_bound_of_lt)'s own
//! module documentation already states the house rule: `0 < x` and its
//! `Nat`-indexed witness are the *same proposition*, and the witness still
//! cannot be pulled out of the `Exists` and used to build anything in
//! `Type` — which is exactly why [`CReal.inv`](super::CRealPrelude::inv)
//! takes its modulus `k : Nat` as an explicit argument rather than deriving
//! it from a `PosBound` proof. A `Prop`-level `∀ε∃δ` reading of uniform
//! continuity has the identical shape and hits the identical wall: the
//! finite-sweep argument this predicate exists to support needs `δ` as
//! `Nat` *data* (a partition width, a sampling index), and `Exists.rec`'s
//! target must not depend on the witness when the target is a `Type`. So
//! `UniformlyContinuousOn` is declared in `Type`, with `modulus : Nat →
//! Nat` a field exactly the way [`CReal.seq`](super::CRealPrelude::seq) is
//! a field of `CReal` itself — the one-constructor-inductive shape (a
//! `Type`-valued data field plus a dependent `Prop`-valued spec field,
//! large elimination for the first projection) is copied from `CReal`'s
//! own carrier ([`super::declare_carrier`]), not invented fresh.
//!
//! ## Why the spec is real-valued, not the canonical-sample idiom
//!
//! [`CReal.Converges`](super::CRealPrelude::converges) and
//! [`CReal.Cauchy`](super::CRealPrelude::cauchy) both compare *samples at a
//! shared index* — the convention [`convergence`](super::convergence)'s own
//! module documentation explains and prefers. That convention was tried
//! here first and abandoned: it ties "which term" to "which accuracy index"
//! as the same `n`, and every attempt to route a
//! [`CReal.Converges`](super::CRealPrelude::converges) witness (rate `K/(n+1)`,
//! a *fixed* `K`) through a modulus spec of that shape needs the hypothesis
//! and the conclusion read at two *different* indices — `g n`'s own
//! accuracy is intrinsically `O(1/n)` and cannot be improved by sampling
//! elsewhere, so the "same index" convention has no slack to spend. The
//! real-valued form `le (abs (x − y)) (ofRat (1/(modulus n + 1))) → le
//! (abs (F x − F y)) (ofRat (1/(n+1)))` is index-free in `x, y`: `le`'s own
//! definition is already a `∀m, …` statement, so a proof is free to unfold
//! it at whichever sample index it already needs — the unfolding
//! `uniformly_continuous_imp_continuous_at` (the bridge to `ContinuousAt`,
//! not landed here — see below) would need.
//!
//! ## What this slice lands, and what it does not
//!
//! Landed: the predicate, its two projections (large elimination for
//! `modulus`, ordinary elimination for `spec`), two witnesses (`id` and
//! `const`) that show the predicate is not vacuous, and the closure lemma
//! `uniformly_continuous_add` (`F`, `G` uniformly continuous on `[a,b]` ⇒
//! so is `fun r => F r + G r`, combined modulus `mF(2n+1) + mG(2n+1)`,
//! unblocked by `Rat.natDivSucc_antitone` — see that declaration's own doc
//! comment for the full argument). **Not landed: `uniformly_continuous_mul`,
//! a named `BoundedOn` predicate, scalar multiplication `fun r => a * r`,
//! and the theorem tying `UniformlyContinuousOn` back to `ContinuousAt`.**
//! All were attempted or considered; none is force-fit, for concrete,
//! verified reasons recorded here rather than gestured at.
//!
//! **`uniformly_continuous_mul` and `BoundedOn`.** `hasDerivative_mul`
//! (`derivative.rs`) needs both factors' magnitude bounded on `[a,b]`, and
//! that hypothesis is built by a *local* `bounded_on_ty` helper there — an
//! inline `∀z, a≤z→z≤b→|h z|≤(k+1)/(0+1)` Pi type, never promoted to a
//! kernel-level named predicate. A `mul` closure lemma for
//! `UniformlyContinuousOn` needs the SAME two-factor magnitude-bound
//! composition `hasDerivative_mul`'s own proof builds by hand (`rescale_index`
//! / `fold_index0_first` / `fold_index0_second` / `mul_modulus_components` /
//! `fuse_three_equal_bounds`, several hundred lines), because closeness of a
//! product needs `|F(x)G(x) − F(y)G(y)| ≤ |F(x)||G(x)−G(y)| + |G(y)||F(x)−F(y)|`
//! — a genuine product-of-bounds estimate, not a triangle inequality — and
//! that machinery is private to `derivative.rs`, out of this slice's file
//! boundary. Naming `BoundedOn` as a `Definition` (transparent, so it stays
//! defeq to `bounded_on_ty`'s inline shape and a closure theorem about it
//! could still be applied at `derivative.rs`'s existing call sites) is the
//! right design if this is picked back up, but building `bounded_on_mul`
//! itself is a slice on the order of `hasDerivative_mul` itself, not a
//! same-session extension of `uniformly_continuous_add`.
//!
//! **This blocker is not on the induction path to `hasDerivative_pow` at
//! general `n`, and that is worth stating plainly.** `hasDerivative_cube`
//! (`derivative.rs`) already proves `r*(r*r) = id(r)*sq(r)` by applying
//! `hasDerivative_mul` with `F := id`, so its continuity hypothesis is
//! `uniformly_continuous_id` — landed since this file's first slice. An
//! induction `pow (n+1) = id * pow n` keeps `F := id` at *every* step, so
//! it needs `uniformly_continuous_id` again and again, never
//! `uniformly_continuous_mul`. What it DOES need at every step is
//! boundedness of `id`, of `pow(·,n)`, and of `pow(·,n)`'s own derivative on
//! `[a,b]` — i.e. exactly the `BoundedOn`-closure-under-`mul` gap above, not
//! a `UniformlyContinuousOn` one. So the general power rule's real
//! remaining blocker is `bounded_on_mul`, not `uniformly_continuous_mul`.
//!
//! **Scalar multiplication.** The natural route needs `mul a (add x (neg
//! y))` related to `add (mul a x) (neg (mul a y))` — i.e. a `mul`-vs-`neg`
//! commutation (`a·(x−y) = a·x − a·y` in a form usable at the `CReal.le`
//! level). Nothing in [`CRealPrelude`] states this directly; the nearest
//! facts are [`CReal.left_distrib`](super::CRealPrelude::left_distrib)
//! (distributes over `add`, not `neg`) and
//! [`CReal.neg_mul_neg`](super::CRealPrelude::neg_mul_neg) (both factors
//! negated, not one). Deriving `mul a (neg y) ~ neg (mul a y)` from these —
//! e.g. by showing `mul a y` and `mul a (neg y)` are both additive inverses
//! of one another via `left_distrib` + `add_neg` + `mul_zero`, then
//! invoking uniqueness of the additive inverse — is plausible but is
//! *itself* an unwritten lemma, not a two-line consequence of what already
//! exists. Landing scalar multiplication honestly needs that lemma first;
//! forcing the proof through without it is exactly the "grinding on a
//! false shortcut" the previous slice's IVT counterexample was praised for
//! refusing to do.
//!
//! **`uniformly_continuous_imp_continuous_at`.** The obstruction is
//! concrete: closing it needs, for the *fixed* `K` a `Converges` witness
//! supplies and an *arbitrary* `modulus : Nat → Nat` from the hypothesis, a
//! `Nat` `k` (as a function of the outer index `n`) with `K/(n+1) ≤
//! 1/(modulus k + 1)` — a genuine `Nat`-division search (`k` on the order
//! of `n/K`), not a rearrangement. [`Rat.natDivSucc`](crate::RatPrelude::nat_div_succ)
//! being "not antitone in its index" is flagged as a *deliberately
//! avoided* cost in [`convergence`](super::convergence)'s own module
//! documentation (the comment on `Rat.natDivSucc_scale`), and every
//! existing estimate in this file is engineered to need only a *fixed*,
//! closed-form index — which is exactly what defeated the scalar-mult
//! witness above too (its own modulus, `(c+1)·n + c`, is one of those
//! closed forms, and `nat_div_succ_scale` turns it into an *equality* with
//! no search at all; an *arbitrary* modulus has no such form). Closing this
//! needs `Nat.div`/`Nat.mod` machinery (present in `nat_prelude`, e.g.
//! `Nat.div_mod_bounds`) chained through a four-term real-vs-rational
//! telescope relating a `Converges` witness's sample at `n` to the real
//! distance between `g n` and its limit — worked out on paper to the point
//! of confidence it is provable, but not built: it did not fit this slice.

#![allow(
    clippy::doc_markdown,
    clippy::many_single_char_names,
    clippy::similar_names,
    clippy::too_many_arguments,
    clippy::too_many_lines
)]

use super::ring_helpers::add4_comm;
use super::{CRealPrelude, creal_ty};
use crate::BinderInfo;
use crate::KernelError;
use crate::env::{Declaration, ReducibilityHint};
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::nat_prelude::NatOps;
use crate::rat_prelude::ops::{nat_rewrite_prop, radd, rat_eq_rewrite};

/// Admit `CReal.UniformlyContinuousOn` (the carrier and its two
/// projections), two witnesses (`id` and `const`), and the closure lemma
/// `uniformly_continuous_add`. See the module documentation for why scalar
/// multiplication, `uniformly_continuous_mul`, a named `BoundedOn`
/// predicate, and the bridge to `ContinuousAt` are not landed here.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` from a `Theorem` here
/// means the kernel **refused** a proof, not that a script gave up.
pub(super) fn declare_uniform_continuity(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    declare_carrier(d, p)?;
    declare_projections(d, p)?;
    declare_uniformly_continuous_id(d, p)?;
    declare_uniformly_continuous_const(d, p)?;
    declare_uniformly_continuous_add(d, p)
}

// --- shared term builders ----------------------------------------------------

/// `CReal → CReal`.
fn fn_ty(d: &mut IntDev<'_>, p: CRealPrelude) -> ExprId {
    let carrier = creal_ty(d, p);
    d.arrow(carrier, carrier)
}

/// `Nat → Nat`.
fn nat_fn_ty(d: &mut IntDev<'_>) -> ExprId {
    let nat = d.nat_ty();
    d.arrow(nat, nat)
}

/// `Rat.natDivSucc k j`, with a **symbolic** `Nat` numerator `k`.
fn div_succ_at(d: &mut IntDev<'_>, p: CRealPrelude, k: ExprId, j: ExprId) -> ExprId {
    d.const_app(p.rat.nat_div_succ, &[k, j])
}

/// `Rat.natDivSucc k j`, with a literal numerator `k`.
fn div_succ(d: &mut IntDev<'_>, p: CRealPrelude, k: u32, j: ExprId) -> ExprId {
    let numerator = d.num(k);
    div_succ_at(d, p, numerator, j)
}

/// `CReal.UniformlyContinuousOn F a b`.
fn uc_ty(d: &mut IntDev<'_>, p: CRealPrelude, f: ExprId, a: ExprId, b: ExprId) -> ExprId {
    d.const_app(p.uniformly_continuous_on, &[f, a, b])
}

/// `CReal.le (CReal.abs (CReal.add x (CReal.neg y))) (CReal.ofRat q)` —
/// `|x − y| ≤ q`, real-valued and index-free in `x, y`.
fn close_within(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId, y: ExprId, q: ExprId) -> ExprId {
    let ny = d.const_app(p.neg, &[y]);
    let diff = d.const_app(p.add, &[x, ny]);
    let magnitude = d.const_app(p.abs, &[diff]);
    let target = d.const_app(p.of_rat, &[q]);
    d.const_app(p.le, &[magnitude, target])
}

/// `∀ (n : Nat) (x y : CReal), le a x → le x b → le a y → le y b →
///   close_within x y (natDivSucc 1 (modulus n)) →
///   close_within (f x) (f y) (natDivSucc 1 n)`.
fn uc_spec_body(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    f: ExprId,
    a: ExprId,
    b: ExprId,
    modulus: ExprId,
) -> ExprId {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let y_fv = d.fresh_fvar();
    let y = d.kernel().fvar(y_fv);

    let range_ax = d.const_app(p.le, &[a, x]);
    let range_xb = d.const_app(p.le, &[x, b]);
    let range_ay = d.const_app(p.le, &[a, y]);
    let range_yb = d.const_app(p.le, &[y, b]);

    let mod_n = d.apply(modulus, &[n]);
    let in_bound = div_succ(d, p, 1, mod_n);
    let hyp = close_within(d, p, x, y, in_bound);

    let fx = d.apply(f, &[x]);
    let fy = d.apply(f, &[y]);
    let out_bound = div_succ(d, p, 1, n);
    let conclusion = close_within(d, p, fx, fy, out_bound);

    let body = d.arrow(hyp, conclusion);
    let with_yb = d.arrow(range_yb, body);
    let with_ay = d.arrow(range_ay, with_yb);
    let with_xb = d.arrow(range_xb, with_ay);
    let with_ax = d.arrow(range_ax, with_xb);
    let with_y = d.pi_fv(y_fv, carrier, with_ax);
    let with_x = d.pi_fv(x_fv, carrier, with_y);
    d.pi_fv(n_fv, nat, with_x)
}

// --- the carrier --------------------------------------------------------------

/// `CReal.UniformlyContinuousOn (F : CReal → CReal) (a b : CReal) : Type :=
///   mk (modulus : Nat → Nat) (spec : …)`.
///
/// A one-constructor inductive with three leading parameters (`F, a, b`) —
/// genuinely parametric, unlike `CReal` itself — copying `CReal`'s own
/// carrier shape one level up: a `Type`-valued data field and a dependent
/// `Prop`-valued spec field over it. See the module documentation for why
/// the data field is unavoidable.
fn declare_carrier(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let func_ty = fn_ty(d, p);
    let nat_fn = nat_fn_ty(d);
    let one = d.level_one();
    let type0 = d.kernel().sort(one);

    // ty := Π (F : CReal → CReal) (a b : CReal), Type 0.
    let ty = {
        let f_fv = d.fresh_fvar();
        let a_fv = d.fresh_fvar();
        let b_fv = d.fresh_fvar();
        let with_b = d.pi_fv(b_fv, carrier, type0);
        let with_a = d.pi_fv(a_fv, carrier, with_b);
        d.pi_fv(f_fv, func_ty, with_a)
    };

    // mk_ty := Π (F a b) (modulus : Nat → Nat) (spec : uc_spec_body …),
    //   UniformlyContinuousOn F a b.
    let mk_ty = {
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let a_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let b_fv = d.fresh_fvar();
        let b = d.kernel().fvar(b_fv);
        let mod_fv = d.fresh_fvar();
        let modulus = d.kernel().fvar(mod_fv);

        let spec_ty = uc_spec_body(d, p, f, a, b, modulus);
        let result = uc_ty(d, p, f, a, b);

        let with_spec = d.arrow(spec_ty, result);
        let with_mod = d.pi_fv(mod_fv, nat_fn, with_spec);
        let with_b = d.pi_fv(b_fv, carrier, with_mod);
        let with_a = d.pi_fv(a_fv, carrier, with_b);
        d.pi_fv(f_fv, func_ty, with_a)
    };

    d.kernel()
        .add_inductive(p.uniformly_continuous_on, &[], 3, ty, &[(p.uc_mk, mk_ty)])
}

/// The two projections: the modulus (large elimination, into `Type 0`) and
/// its spec (into `Prop`, with the motive at a witness `u` reading `u`'s
/// *own* modulus — mirroring exactly how
/// [`CReal.regular`](super::CRealPrelude::regular) projects `CReal`'s own
/// `Prop` field in [`super::declare_projections`]).
fn declare_projections(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let func_ty = fn_ty(d, p);
    let nat_fn = nat_fn_ty(d);
    let one = d.level_one();
    let zero_level = d.kernel().level_zero();
    let anon = d.anon_name();

    // modulus : ∀ F a b, UniformlyContinuousOn F a b → Nat → Nat
    //   := fun F a b u => UniformlyContinuousOn.rec F a b (fun _ => Nat → Nat)
    //        (fun modulus _ => modulus) u.
    {
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let a_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let b_fv = d.fresh_fvar();
        let b = d.kernel().fvar(b_fv);
        let carrier_uc = uc_ty(d, p, f, a, b);

        let motive = d
            .kernel()
            .lam(anon, carrier_uc, nat_fn, BinderInfo::Default);
        let minor = {
            let mod_fv = d.fresh_fvar();
            let modulus = d.kernel().fvar(mod_fv);
            let spec_ty = uc_spec_body(d, p, f, a, b, modulus);
            let inner = d.kernel().lam(anon, spec_ty, modulus, BinderInfo::Default);
            d.lam_fv(mod_fv, nat_fn, inner)
        };

        let u_fv = d.fresh_fvar();
        let u = d.kernel().fvar(u_fv);
        let rec = d.kernel().const_(p.uc_rec, vec![one]);
        let body = d.apply(rec, &[f, a, b, motive, minor, u]);
        let value = {
            let with_u = d.lam_fv(u_fv, carrier_uc, body);
            let with_b = d.lam_fv(b_fv, carrier, with_u);
            let with_a = d.lam_fv(a_fv, carrier, with_b);
            d.lam_fv(f_fv, func_ty, with_a)
        };
        let ty = {
            let with_u = d.arrow(carrier_uc, nat_fn);
            let with_b = d.pi_fv(b_fv, carrier, with_u);
            let with_a = d.pi_fv(a_fv, carrier, with_b);
            d.pi_fv(f_fv, func_ty, with_a)
        };
        d.kernel().add_declaration(Declaration::Definition {
            name: p.uc_modulus,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(super::DERIVED_HEIGHT + 40),
        })?;
    }

    // spec : ∀ F a b (u : UniformlyContinuousOn F a b),
    //   uc_spec_body F a b (UniformlyContinuousOn.modulus F a b u)
    //   := fun F a b u => UniformlyContinuousOn.rec F a b
    //        (fun w => uc_spec_body F a b (UniformlyContinuousOn.modulus F a b w))
    //        (fun modulus spec => spec) u.
    {
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let a_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let b_fv = d.fresh_fvar();
        let b = d.kernel().fvar(b_fv);
        let carrier_uc = uc_ty(d, p, f, a, b);

        let claim = |d: &mut IntDev<'_>, w: ExprId| {
            let mod_of_w = d.const_app(p.uc_modulus, &[f, a, b, w]);
            uc_spec_body(d, p, f, a, b, mod_of_w)
        };

        let motive = {
            let w_fv = d.fresh_fvar();
            let w = d.kernel().fvar(w_fv);
            let body = claim(d, w);
            d.lam_fv(w_fv, carrier_uc, body)
        };
        let minor = {
            let mod_fv = d.fresh_fvar();
            let modulus = d.kernel().fvar(mod_fv);
            let spec_ty = uc_spec_body(d, p, f, a, b, modulus);
            let spec_fv = d.fresh_fvar();
            let spec_var = d.kernel().fvar(spec_fv);
            let inner = d.lam_fv(spec_fv, spec_ty, spec_var);
            d.lam_fv(mod_fv, nat_fn, inner)
        };

        let u_fv = d.fresh_fvar();
        let u = d.kernel().fvar(u_fv);
        let rec = d.kernel().const_(p.uc_rec, vec![zero_level]);
        let body = d.apply(rec, &[f, a, b, motive, minor, u]);
        let value = {
            let with_u = d.lam_fv(u_fv, carrier_uc, body);
            let with_b = d.lam_fv(b_fv, carrier, with_u);
            let with_a = d.lam_fv(a_fv, carrier, with_b);
            d.lam_fv(f_fv, func_ty, with_a)
        };
        let ty = {
            let inner = claim(d, u);
            let with_u = d.pi_fv(u_fv, carrier_uc, inner);
            let with_b = d.pi_fv(b_fv, carrier, with_u);
            let with_a = d.pi_fv(a_fv, carrier, with_b);
            d.pi_fv(f_fv, func_ty, with_a)
        };
        d.kernel().add_declaration(Declaration::Theorem {
            name: p.uc_spec,
            uparams: vec![],
            ty,
            value,
        })?;
    }
    Ok(())
}

// --- witness: `id` -------------------------------------------------------------

/// `CReal.uniformly_continuous_id : ∀ a b, UniformlyContinuousOn (fun r => r) a b`.
///
/// The cheapest witness: with `F := id`, `close_within (f x) (f y) q` is
/// `close_within x y q` verbatim (up to beta/η), so the hypothesis at
/// `modulus n := n` **is** the conclusion.
fn declare_uniformly_continuous_id(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();

    let identity = {
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);
        d.lam_fv(r_fv, carrier, r)
    };
    let modulus = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        d.lam_fv(n_fv, nat, n)
    };

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);

    let spec = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let y_fv = d.fresh_fvar();
        let y = d.kernel().fvar(y_fv);
        let hax_fv = d.fresh_fvar();
        let hxb_fv = d.fresh_fvar();
        let hay_fv = d.fresh_fvar();
        let hyb_fv = d.fresh_fvar();
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);

        let range_ax = d.const_app(p.le, &[a, x]);
        let range_xb = d.const_app(p.le, &[x, b]);
        let range_ay = d.const_app(p.le, &[a, y]);
        let range_yb = d.const_app(p.le, &[y, b]);
        let mod_n = d.apply(modulus, &[n]);
        let in_bound = div_succ(d, p, 1, mod_n);
        let hyp = close_within(d, p, x, y, in_bound);

        let with_h = d.lam_fv(h_fv, hyp, h);
        let with_hyb = d.lam_fv(hyb_fv, range_yb, with_h);
        let with_hay = d.lam_fv(hay_fv, range_ay, with_hyb);
        let with_hxb = d.lam_fv(hxb_fv, range_xb, with_hay);
        let with_hax = d.lam_fv(hax_fv, range_ax, with_hxb);
        let with_y = d.lam_fv(y_fv, carrier, with_hax);
        let with_x = d.lam_fv(x_fv, carrier, with_y);
        d.lam_fv(n_fv, nat, with_x)
    };

    let mk_applied = d.const_app(p.uc_mk, &[identity, a, b, modulus, spec]);
    let value = {
        let with_b = d.lam_fv(b_fv, carrier, mk_applied);
        d.lam_fv(a_fv, carrier, with_b)
    };
    let ty = {
        let applied = uc_ty(d, p, identity, a, b);
        let with_b = d.pi_fv(b_fv, carrier, applied);
        d.pi_fv(a_fv, carrier, with_b)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.uniformly_continuous_id,
        uparams: vec![],
        ty,
        value,
    })
}

// --- witness: `const` ----------------------------------------------------------

/// `CReal.uniformly_continuous_const : ∀ c a b, UniformlyContinuousOn (fun _ => c) a b`.
///
/// Any modulus works — `fun _ => 0` is used — because `add c (neg c)` is
/// `Equiv`-zero ([`CReal.add_neg`](super::CRealPrelude::add_neg)), so the
/// conclusion holds independently of the hypothesis. The bulk of this proof
/// is the one fact that *isn't* a direct consequence of `add_neg`: `neg
/// zero` itself has to be shown `≤` an arbitrary nonnegative rational bound,
/// via [`CReal.ofRat_neg`](super::CRealPrelude::of_rat_neg) and
/// `Rat.neg_zero`.
fn declare_uniformly_continuous_const(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let rat = p.rat;
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();

    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let const_fn = {
        let ignore_fv = d.fresh_fvar();
        d.lam_fv(ignore_fv, carrier, c)
    };
    let modulus = {
        let ignore_fv = d.fresh_fvar();
        let zero_nat = d.num(0);
        d.lam_fv(ignore_fv, nat, zero_nat)
    };

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);

    // The one-time rational fact: `Equiv (neg zero_r) zero_r`, `zero_r :=
    // ofRat Rat.zero`, via `ofRat_neg` at `Rat.zero` and `Rat.neg_zero`.
    let rzero_expr = crate::rat_prelude::ops::rzero(d, rat);
    let zero_r = d.const_app(p.of_rat, &[rzero_expr]);
    let neg_zero_r = d.const_app(p.neg, &[zero_r]);

    let of_rat_neg_at_zero = d.lemma(p.of_rat_neg, &[rzero_expr]);
    let neg_rzero_expr = crate::rat_prelude::ops::rneg(d, rzero_expr);
    let neg_zero_eq = d.lemma(rat.neg_zero, &[]);
    let neg_zero_equiv_zero = rat_eq_rewrite(
        d,
        neg_rzero_expr,
        rzero_expr,
        neg_zero_eq,
        of_rat_neg_at_zero,
        &|d, t| {
            let ofr_t = d.const_app(p.of_rat, &[t]);
            let negz = d.const_app(p.neg, &[zero_r]);
            super::equiv(d, p, negz, ofr_t)
        },
    );
    // neg_zero_equiv_zero : Equiv (neg zero_r) zero_r.
    let h_negzero_le_zero = d.lemma(p.le_of_equiv, &[neg_zero_r, zero_r, neg_zero_equiv_zero]);

    let spec = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let x_fv = d.fresh_fvar();
        let y_fv = d.fresh_fvar();
        let hax_fv = d.fresh_fvar();
        let hxb_fv = d.fresh_fvar();
        let hay_fv = d.fresh_fvar();
        let hyb_fv = d.fresh_fvar();
        let h_fv = d.fresh_fvar();

        let x_ref = d.kernel().fvar(x_fv);
        let y_ref = d.kernel().fvar(y_fv);
        let range_ax = d.const_app(p.le, &[a, x_ref]);
        let range_xb = d.const_app(p.le, &[x_ref, b]);
        let range_ay = d.const_app(p.le, &[a, y_ref]);
        let range_yb = d.const_app(p.le, &[y_ref, b]);

        let q = div_succ(d, p, 1, n);
        let mod_n = d.apply(modulus, &[n]);
        let in_bound = div_succ(d, p, 1, mod_n);
        let hyp = close_within(d, p, x_ref, y_ref, in_bound);

        let add_c_negc = {
            let nc = d.const_app(p.neg, &[c]);
            d.const_app(p.add, &[c, nc])
        };

        // Rat.le Rat.zero q, and the two `le` facts against `zero_r`.
        let one_nat = d.num(1);
        let rat_nonneg = d.lemma(rat.zero_le_nat_div_succ, &[one_nat, n]);
        let ofr_q = d.const_app(p.of_rat, &[q]);
        let h_zero_le_q = d.lemma(p.of_rat_le, &[rzero_expr, q, rat_nonneg]);
        let h_negzero_le_q = d.lemma(
            p.le_trans,
            &[neg_zero_r, zero_r, ofr_q, h_negzero_le_zero, h_zero_le_q],
        );

        // `Equiv (add c (neg c)) zero_r`, from `add_neg` (relies on `CReal.zero`
        // being *defined* as `ofRat Rat.zero`, hence defeq to `zero_r`).
        let h1 = d.lemma(p.add_neg, &[c]);

        let h_upper = d.lemma(p.le_of_equiv, &[add_c_negc, zero_r, h1]);
        let h4 = d.lemma(
            p.le_trans,
            &[add_c_negc, zero_r, ofr_q, h_upper, h_zero_le_q],
        );

        let neg_add_c_negc = d.const_app(p.neg, &[add_c_negc]);
        let h1_neg = d.lemma(p.neg_congr, &[add_c_negc, zero_r, h1]);
        let h1_neg_symm = d.lemma(p.equiv_symm, &[neg_add_c_negc, neg_zero_r, h1_neg]);
        let refl_q = d.lemma(p.equiv_refl, &[ofr_q]);
        let h6 = d.lemma(
            p.le_congr,
            &[
                neg_zero_r,
                neg_add_c_negc,
                ofr_q,
                ofr_q,
                h1_neg_symm,
                refl_q,
                h_negzero_le_q,
            ],
        );

        let conclusion = d.lemma(p.abs_le, &[add_c_negc, ofr_q, h4, h6]);
        // `conclusion : close_within c c (natDivSucc 1 n)`, unused by the
        // hypothesis: `const`'s spec is constant in `h`.
        let h = d.kernel().fvar(h_fv);
        let _ = h;

        let with_h = d.lam_fv(h_fv, hyp, conclusion);
        let with_hyb = d.lam_fv(hyb_fv, range_yb, with_h);
        let with_hay = d.lam_fv(hay_fv, range_ay, with_hyb);
        let with_hxb = d.lam_fv(hxb_fv, range_xb, with_hay);
        let with_hax = d.lam_fv(hax_fv, range_ax, with_hxb);
        let with_y = d.lam_fv(y_fv, carrier, with_hax);
        let with_x = d.lam_fv(x_fv, carrier, with_y);
        d.lam_fv(n_fv, nat, with_x)
    };

    let mk_applied = d.const_app(p.uc_mk, &[const_fn, a, b, modulus, spec]);
    let value = {
        let with_b = d.lam_fv(b_fv, carrier, mk_applied);
        let with_a = d.lam_fv(a_fv, carrier, with_b);
        d.lam_fv(c_fv, carrier, with_a)
    };
    let ty = {
        let applied = uc_ty(d, p, const_fn, a, b);
        let with_b = d.pi_fv(b_fv, carrier, applied);
        let with_a = d.pi_fv(a_fv, carrier, with_b);
        d.pi_fv(c_fv, carrier, with_a)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.uniformly_continuous_const,
        uparams: vec![],
        ty,
        value,
    })
}

// --- witness: `add` (closure under `+`) -----------------------------------
//
// The combined modulus is `hasDerivative_add`'s own
// (`creal/derivative.rs::declare_has_derivative_add`): `mF(2n+1) +
// mG(2n+1)`, `Nat.add` rather than `Nat.max` (`nat_prelude` has no
// `Nat.max`), unblocked by `Rat.natDivSucc_antitone`
// (`crate::RatPrelude::nat_div_succ_antitone`) with
// `Nat.le_add_right`/`Nat.add_comm` giving both `<=` directions
// (`mF(2n+1) <= mF(2n+1)+mG(2n+1)` directly, `mG(2n+1) <=
// mG(2n+1)+mF(2n+1) = mF(2n+1)+mG(2n+1)` after one commutation). What
// differs from `hasDerivative_add` is the error term itself: there is no
// `F'`/`G'` telescope here, so combining `F`'s and `G`'s own bounds is
// exactly the two-term triangle inequality, `abs_add_le`, built as a THIRD
// local copy below (`ring_helpers.rs`'s own module doc explains why this
// specific fact is deliberately not shared even though `series.rs` and
// `derivative.rs` already carry one copy each: they discharge the same
// statement through different underlying `neg_add`/`neg_add_distrib`
// proofs, and unifying either without the other is picking a route for one
// call site over the other) plus [`add4_comm`], which IS shared via
// `ring_helpers.rs`.

/// `Equiv (neg (add a b)) (add (neg a) (neg b))` — additive inverse
/// distributes over `add`. A third local copy of `series.rs`'s private
/// `neg_add` (see the section doc above for why it is not shared).
fn neg_add(d: &mut IntDev<'_>, p: CRealPrelude, a: ExprId, b: ExprId) -> ExprId {
    let zero_c = d.kernel().const_(p.zero, vec![]);
    let s = d.const_app(p.add, &[a, b]);
    let na = d.const_app(p.neg, &[a]);
    let nb = d.const_app(p.neg, &[b]);
    let t = d.const_app(p.add, &[na, nb]);
    let ns = d.const_app(p.neg, &[s]);

    // f_proof : Equiv (add s t) zero, via add4_comm + the two `add_neg`s.
    let f_proof = {
        let (target1, h4) = add4_comm(d, p, a, b, na, nb);
        let a_na = d.const_app(p.add, &[a, na]);
        let b_nb = d.const_app(p.add, &[b, nb]);
        let add_zz = d.const_app(p.add, &[zero_c, zero_c]);
        let h_a = d.lemma(p.add_neg, &[a]); // a_na ~ zero
        let h_b = d.lemma(p.add_neg, &[b]); // b_nb ~ zero
        let h5 = d.lemma(p.add_congr, &[a_na, zero_c, b_nb, zero_c, h_a, h_b]); // target1 ~ add_zz
        let h6 = d.lemma(p.add_zero, &[zero_c]); // add_zz ~ zero
        let start = d.const_app(p.add, &[s, t]);
        echain(d, p, start, &[(target1, h4), (add_zz, h5), (zero_c, h6)])
    };

    // neg s ~ add(neg s)(zero) ~ add(neg s)(add s t) ~ (add(neg s)s)+t ~ add zero t ~ t
    let step_a_target = d.const_app(p.add, &[ns, zero_c]);
    let step_a = {
        let h = d.lemma(p.add_zero, &[ns]); // step_a_target ~ ns
        d.lemma(p.equiv_symm, &[step_a_target, ns, h]) // ns ~ step_a_target
    };

    let st = d.const_app(p.add, &[s, t]);
    let step_b_target = d.const_app(p.add, &[ns, st]);
    let step_b = {
        let f_symm = d.lemma(p.equiv_symm, &[st, zero_c, f_proof]); // zero ~ add s t
        let refl_ns = d.lemma(p.equiv_refl, &[ns]);
        d.lemma(p.add_congr, &[ns, ns, zero_c, st, refl_ns, f_symm])
        // step_a_target ~ step_b_target
    };

    let ns_s = d.const_app(p.add, &[ns, s]);
    let step_c_target = d.const_app(p.add, &[ns_s, t]);
    let step_c = {
        let assoc = d.lemma(p.add_assoc, &[ns, s, t]); // step_c_target ~ step_b_target
        d.lemma(p.equiv_symm, &[step_c_target, step_b_target, assoc])
        // step_b_target ~ step_c_target
    };

    let step_d_target = d.const_app(p.add, &[zero_c, t]);
    let step_d = {
        let x = {
            let comm = d.lemma(p.add_comm, &[ns, s]); // ns_s ~ add s ns
            let s_ns = d.const_app(p.add, &[s, ns]);
            let negl = d.lemma(p.add_neg, &[s]); // add s ns ~ zero
            d.lemma(p.equiv_trans, &[ns_s, s_ns, zero_c, comm, negl])
        };
        // x : ns_s ~ zero
        let refl_t = d.lemma(p.equiv_refl, &[t]);
        d.lemma(p.add_congr, &[ns_s, zero_c, t, t, x, refl_t])
        // step_c_target ~ step_d_target
    };

    let t_zero = d.const_app(p.add, &[t, zero_c]);
    let step_e = {
        let comm = d.lemma(p.add_comm, &[zero_c, t]); // step_d_target ~ t_zero
        let collapse = d.lemma(p.add_zero, &[t]); // t_zero ~ t
        d.lemma(p.equiv_trans, &[step_d_target, t_zero, t, comm, collapse])
        // step_d_target ~ t
    };

    echain(
        d,
        p,
        ns,
        &[
            (step_a_target, step_a),
            (step_b_target, step_b),
            (step_c_target, step_c),
            (step_d_target, step_d),
            (t, step_e),
        ],
    )
}

/// Chain `Equiv start …` through `(next, step)` pairs. Local restatement of
/// the identical helper private to `series.rs`/`derivative.rs`/
/// `ring_helpers.rs` (`ring_helpers.rs`'s own module doc explains why
/// `cadd`/`cmul`/`echain`-shaped one-liners are deliberately not shared
/// further than they already are).
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

/// `le (abs (add a b)) (add (abs a) (abs b))` — the two-term triangle
/// inequality. A third local copy of `series.rs`'s/`derivative.rs`'s
/// private `abs_add_le` (see the section doc above for why).
fn abs_add_le(d: &mut IntDev<'_>, p: CRealPrelude, a: ExprId, b: ExprId) -> ExprId {
    let s = d.const_app(p.add, &[a, b]);
    let abs_a = d.const_app(p.abs, &[a]);
    let abs_b = d.const_app(p.abs, &[b]);
    let bound = d.const_app(p.add, &[abs_a, abs_b]);

    // premise1 : le (add a b) (add (abs a) (abs b))
    let le_a = d.lemma(p.le_abs_self, &[a]);
    let le_b = d.lemma(p.le_abs_self, &[b]);
    let premise1 = d.lemma(p.add_le_add, &[a, abs_a, b, abs_b, le_a, le_b]);

    // premise2 : le (neg (add a b)) (add (abs a) (abs b))
    let na = d.const_app(p.neg, &[a]);
    let nb = d.const_app(p.neg, &[b]);
    let t = d.const_app(p.add, &[na, nb]);
    let ns = d.const_app(p.neg, &[s]);
    let na_eq = neg_add(d, p, a, b); // ns ~ t
    let step1 = d.lemma(p.le_of_equiv, &[ns, t, na_eq]); // le ns t
    let nle_a = d.lemma(p.neg_le_abs, &[a]); // le na abs_a
    let nle_b = d.lemma(p.neg_le_abs, &[b]); // le nb abs_b
    let step2 = d.lemma(p.add_le_add, &[na, abs_a, nb, abs_b, nle_a, nle_b]); // le t bound
    let premise2 = d.lemma(p.le_trans, &[ns, t, bound, step1, step2]);

    d.lemma(p.abs_le, &[s, bound, premise1, premise2])
}

/// `CReal.uniformly_continuous_add : ∀ F G a b, UniformlyContinuousOn F a b
/// → UniformlyContinuousOn G a b → UniformlyContinuousOn (fun r => add (F
/// r) (G r)) a b`.
///
/// The combined modulus at accuracy `n` is `mF(2n+1) + mG(2n+1)`. `F`'s and
/// `G`'s own specs at `2n+1` each bound their own error by `1/(2n+2)`; the
/// triangle inequality ([`abs_add_le`]) bounds the combined error by their
/// sum; and `Rat.natDivSucc_add` + `Rat.natDivSucc_halve` fuse the two
/// `1/(2n+2)` bounds into the single target `1/(n+1)` — see the section doc
/// above for the full argument.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
fn declare_uniformly_continuous_add(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let func_ty = fn_ty(d, p);
    let nat = d.nat_ty();

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);

    let huc_f_ty = uc_ty(d, p, f, a, b);
    let huc_f_fv = d.fresh_fvar();
    let huc_f = d.kernel().fvar(huc_f_fv);
    let huc_g_ty = uc_ty(d, p, g, a, b);
    let huc_g_fv = d.fresh_fvar();
    let huc_g = d.kernel().fvar(huc_g_fv);

    let sum_fn = {
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);
        let fr = d.apply(f, &[r]);
        let gr = d.apply(g, &[r]);
        let sum = d.const_app(p.add, &[fr, gr]);
        d.lam_fv(r_fv, carrier, sum)
    };

    let mf = d.const_app(p.uc_modulus, &[f, a, b, huc_f]);
    let mg = d.const_app(p.uc_modulus, &[g, a, b, huc_g]);

    // `modulus_add n := mF (2n+1) + mG (2n+1)`.
    let modulus_add = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let two = d.num(2);
        let two_n = d.mul(two, n);
        let e_prime = d.succ(two_n);
        let mf_e = d.apply(mf, &[e_prime]);
        let mg_e = d.apply(mg, &[e_prime]);
        let sum = d.add(mf_e, mg_e);
        d.lam_fv(n_fv, nat, sum)
    };

    let spec = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let y_fv = d.fresh_fvar();
        let y = d.kernel().fvar(y_fv);
        let hax_fv = d.fresh_fvar();
        let hxb_fv = d.fresh_fvar();
        let hay_fv = d.fresh_fvar();
        let hyb_fv = d.fresh_fvar();
        let h_fv = d.fresh_fvar();

        let range_ax = d.const_app(p.le, &[a, x]);
        let range_xb = d.const_app(p.le, &[x, b]);
        let range_ay = d.const_app(p.le, &[a, y]);
        let range_yb = d.const_app(p.le, &[y, b]);
        let hax = d.kernel().fvar(hax_fv);
        let hxb = d.kernel().fvar(hxb_fv);
        let hay = d.kernel().fvar(hay_fv);
        let hyb = d.kernel().fvar(hyb_fv);

        // `e_prime := succ(2*n)` — Bishop's index shift, the accuracy `F`'s
        // and `G`'s own specs are consulted at.
        let two = d.num(2);
        let two_n = d.mul(two, n);
        let e_prime = d.succ(two_n);
        let mf_e = d.apply(mf, &[e_prime]);
        let mg_e = d.apply(mg, &[e_prime]);
        let combined = d.add(mf_e, mg_e);

        let mod_n = d.apply(modulus_add, &[n]);
        let in_bound = div_succ(d, p, 1, mod_n);
        let hyp = close_within(d, p, x, y, in_bound);
        let h = d.kernel().fvar(h_fv);

        // --- read the combined-modulus hypothesis back down to F's and
        // G's own, via `nat_div_succ_antitone` --------------------------
        let mg_plus_mf = d.add(mg_e, mf_e);
        let nat_p = p.rat.int.nat;
        let h_le_f = d.lemma(nat_p.le_add_right, &[mf_e, mg_e]); // Le mf_e combined
        let raw_g = d.lemma(nat_p.le_add_right, &[mg_e, mf_e]); // Le mg_e mg_plus_mf
        let comm_eq = d.lemma(nat_p.add_comm, &[mg_e, mf_e]); // Eq mg_plus_mf combined
        let h_le_g = nat_rewrite_prop(d, mg_plus_mf, combined, comm_eq, raw_g, &|d, t| {
            NatOps::le(d, mg_e, t)
        });

        let r_f = div_succ(d, p, 1, mf_e);
        let r_g = div_succ(d, p, 1, mg_e);
        let r_combined = div_succ(d, p, 1, combined);
        let rat_f = d.lemma(p.rat.nat_div_succ_antitone, &[mf_e, combined, h_le_f]); // Rat.le r_combined r_f
        let rat_g = d.lemma(p.rat.nat_div_succ_antitone, &[mg_e, combined, h_le_g]); // Rat.le r_combined r_g

        let ofr_combined = d.const_app(p.of_rat, &[r_combined]);
        let ofr_f = d.const_app(p.of_rat, &[r_f]);
        let ofr_g = d.const_app(p.of_rat, &[r_g]);
        let creal_f = d.lemma(p.of_rat_le, &[r_combined, r_f, rat_f]); // le ofr_combined ofr_f
        let creal_g = d.lemma(p.of_rat_le, &[r_combined, r_g, rat_g]); // le ofr_combined ofr_g

        let ny = d.const_app(p.neg, &[y]);
        let diff_xy = d.const_app(p.add, &[x, ny]);
        let abs_diff = d.const_app(p.abs, &[diff_xy]);
        let hyp_f = d.lemma(p.le_trans, &[abs_diff, ofr_combined, ofr_f, h, creal_f]);
        let hyp_g = d.lemma(p.le_trans, &[abs_diff, ofr_combined, ofr_g, h, creal_g]);

        // --- F's and G's own errors, at accuracy `e_prime` ---------------
        let fx = d.apply(f, &[x]);
        let fy = d.apply(f, &[y]);
        let gx = d.apply(g, &[x]);
        let gy = d.apply(g, &[y]);

        let spec_f = d.const_app(p.uc_spec, &[f, a, b, huc_f]);
        let spec_g = d.const_app(p.uc_spec, &[g, a, b, huc_g]);
        let close_f = d.apply(spec_f, &[e_prime, x, y, hax, hxb, hay, hyb, hyp_f]);
        let close_g = d.apply(spec_g, &[e_prime, x, y, hax, hxb, hay, hyb, hyp_g]);
        // close_f : close_within (F x) (F y) (natDivSucc 1 e_prime)
        // close_g : close_within (G x) (G y) (natDivSucc 1 e_prime)

        let neg_fy = d.const_app(p.neg, &[fy]);
        let error_f = d.const_app(p.add, &[fx, neg_fy]);
        let neg_gy = d.const_app(p.neg, &[gy]);
        let error_g = d.const_app(p.add, &[gx, neg_gy]);
        let abs_error_f = d.const_app(p.abs, &[error_f]);
        let abs_error_g = d.const_app(p.abs, &[error_g]);

        let r_prime = div_succ(d, p, 1, e_prime);
        let q_prime = d.const_app(p.of_rat, &[r_prime]);
        // close_f/close_g literally ARE `le abs_error_f q_prime` /
        // `le abs_error_g q_prime` (`close_within` unfolds to exactly this).

        // --- combine via the triangle inequality --------------------------
        let (target, add4_proof) = add4_comm(d, p, fx, gx, neg_fy, neg_gy);
        // target = add error_f error_g;
        // add4_proof : Equiv (add(add fx gx)(add neg_fy neg_gy)) target
        let abs_target = d.const_app(p.abs, &[target]);
        let triangle = abs_add_le(d, p, error_f, error_g);
        // triangle : le abs_target (add abs_error_f abs_error_g)
        let sum_bounds = d.lemma(
            p.add_le_add,
            &[abs_error_f, q_prime, abs_error_g, q_prime, close_f, close_g],
        );
        let abs_ef_plus_eg = d.const_app(p.add, &[abs_error_f, abs_error_g]);
        let q_prime_plus_q_prime = d.const_app(p.add, &[q_prime, q_prime]);
        let combined_le = d.lemma(
            p.le_trans,
            &[
                abs_target,
                abs_ef_plus_eg,
                q_prime_plus_q_prime,
                triangle,
                sum_bounds,
            ],
        );
        // combined_le : le abs_target (add q_prime q_prime)

        // --- combined_diff ~ target, lifted through `abs` ------------------
        let fx_gx = d.const_app(p.add, &[fx, gx]);
        let fy_gy = d.const_app(p.add, &[fy, gy]);
        let neg_fy_gy = d.const_app(p.neg, &[fy_gy]);
        let combined_diff = d.const_app(p.add, &[fx_gx, neg_fy_gy]);
        let abs_combined_diff = d.const_app(p.abs, &[combined_diff]);

        let neg_fy_neg_gy = d.const_app(p.add, &[neg_fy, neg_gy]);
        let step1_target = d.const_app(p.add, &[fx_gx, neg_fy_neg_gy]);
        let neg_add_fy_gy = neg_add(d, p, fy, gy); // neg_fy_gy ~ neg_fy_neg_gy
        let refl_fx_gx = d.lemma(p.equiv_refl, &[fx_gx]);
        let step1 = d.lemma(
            p.add_congr,
            &[
                fx_gx,
                fx_gx,
                neg_fy_gy,
                neg_fy_neg_gy,
                refl_fx_gx,
                neg_add_fy_gy,
            ],
        );
        // step1 : combined_diff ~ step1_target

        let chain_ct = echain(
            d,
            p,
            combined_diff,
            &[(step1_target, step1), (target, add4_proof)],
        );
        // chain_ct : combined_diff ~ target
        let chain_tc = d.lemma(p.equiv_symm, &[combined_diff, target, chain_ct]);
        // chain_tc : target ~ combined_diff
        let abs_equiv = d.lemma(p.abs_congr, &[target, combined_diff, chain_tc]);
        // abs_equiv : abs_target ~ abs_combined_diff

        // --- fuse `add q_prime q_prime` down to `ofRat (natDivSucc 1 n)` --
        let one_nat = d.num(1);
        let of_rat_add_proof = d.lemma(p.of_rat_add, &[r_prime, r_prime]);
        // Equiv (add q_prime q_prime) (ofRat (Rat.add r_prime r_prime))
        let eq1 = d.lemma(p.rat.nat_div_succ_add, &[one_nat, one_nat, e_prime]);
        let two_e_prime = div_succ(d, p, 2, e_prime);
        let radd_r_prime_r_prime = radd(d, r_prime, r_prime);
        let step_a = rat_eq_rewrite(
            d,
            radd_r_prime_r_prime,
            two_e_prime,
            eq1,
            of_rat_add_proof,
            &|d, t| {
                let oft = d.const_app(p.of_rat, &[t]);
                d.const_app(p.equiv, &[q_prime_plus_q_prime, oft])
            },
        );
        // Equiv (add q_prime q_prime) (ofRat two_e_prime)
        let eq2 = d.lemma(p.rat.nat_div_succ_halve, &[n]);
        let out_bound_rat = div_succ(d, p, 1, n);
        let fuse_equiv = rat_eq_rewrite(d, two_e_prime, out_bound_rat, eq2, step_a, &|d, t| {
            let oft = d.const_app(p.of_rat, &[t]);
            d.const_app(p.equiv, &[q_prime_plus_q_prime, oft])
        });
        // fuse_equiv : Equiv (add q_prime q_prime) (ofRat out_bound_rat)
        let ofr_out_bound = d.const_app(p.of_rat, &[out_bound_rat]);

        let result = d.lemma(
            p.le_congr,
            &[
                abs_target,
                abs_combined_diff,
                q_prime_plus_q_prime,
                ofr_out_bound,
                abs_equiv,
                fuse_equiv,
                combined_le,
            ],
        );
        // result : close_within (sum_fn x) (sum_fn y) (natDivSucc 1 n)

        let with_h = d.lam_fv(h_fv, hyp, result);
        let with_hyb = d.lam_fv(hyb_fv, range_yb, with_h);
        let with_hay = d.lam_fv(hay_fv, range_ay, with_hyb);
        let with_hxb = d.lam_fv(hxb_fv, range_xb, with_hay);
        let with_hax = d.lam_fv(hax_fv, range_ax, with_hxb);
        let with_y = d.lam_fv(y_fv, carrier, with_hax);
        let with_x = d.lam_fv(x_fv, carrier, with_y);
        d.lam_fv(n_fv, nat, with_x)
    };

    let mk_applied = d.const_app(p.uc_mk, &[sum_fn, a, b, modulus_add, spec]);
    let value = {
        let with_huc_g = d.lam_fv(huc_g_fv, huc_g_ty, mk_applied);
        let with_huc_f = d.lam_fv(huc_f_fv, huc_f_ty, with_huc_g);
        let with_b = d.lam_fv(b_fv, carrier, with_huc_f);
        let with_a = d.lam_fv(a_fv, carrier, with_b);
        let with_g = d.lam_fv(g_fv, func_ty, with_a);
        d.lam_fv(f_fv, func_ty, with_g)
    };
    let ty = {
        let applied = uc_ty(d, p, sum_fn, a, b);
        let with_huc_g = d.arrow(huc_g_ty, applied);
        let with_huc_f = d.arrow(huc_f_ty, with_huc_g);
        let with_b = d.pi_fv(b_fv, carrier, with_huc_f);
        let with_a = d.pi_fv(a_fv, carrier, with_b);
        let with_g = d.pi_fv(g_fv, func_ty, with_a);
        d.pi_fv(f_fv, func_ty, with_g)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.uniformly_continuous_add,
        uparams: vec![],
        ty,
        value,
    })
}
