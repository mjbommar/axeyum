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
use crate::rat_prelude::ops::{nat_eq_to_rat, nat_rewrite_prop, radd, rat_eq_rewrite};

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
    declare_uniformly_continuous_add(d, p)?;
    declare_uniformly_continuous_neg(d, p)?;
    declare_uniformly_continuous_sub(d, p)
}

/// The `BoundedOn`-hypothesis closure lemmas (`mul`, `sq`) and a concrete
/// instantiation, split into a SECOND entry point because they consume
/// `CReal.BoundedOn` and `CReal.abs_mul_le_of_bounds`
/// (`creal/derivative.rs`), which are not declared until
/// `derivative::declare_derivative` runs -- AFTER this module's own
/// [`declare_uniform_continuity`] in `creal.rs`'s build order. That order
/// cannot simply flip: `derivative.rs` itself calls `CReal.uniformly_continuous_id`
/// as a VALUE (three call sites), so it needs THIS module's early half
/// declared first. Wired in `creal.rs` right after
/// `derivative::declare_derivative`, the same split
/// `derivative::declare_has_derivative_pow_two`/`_pow` already use to wait
/// for `power::declare_power`.
///
/// # Errors
///
/// Returns the trusted gate's rejection.
pub(super) fn declare_uniform_continuity_products(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    declare_uniformly_continuous_mul(d, p)?;
    declare_uniformly_continuous_sq(d, p)?;
    declare_bounded_on_id_unit(d, p)?;
    declare_uniformly_continuous_poly_example(d, p)
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

// --- shared term builders, round two (local copies of small pieces from
// `creal/derivative.rs`, which are private to that file -- see the module
// doc's rationale for `echain`/`neg_add`/`abs_add_le`, which these join) ---

fn czero(d: &mut IntDev<'_>, p: CRealPrelude) -> ExprId {
    d.kernel().const_(p.zero, vec![])
}

fn cneg(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId) -> ExprId {
    d.const_app(p.neg, &[x])
}

fn cadd(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId, y: ExprId) -> ExprId {
    d.const_app(p.add, &[x, y])
}

fn cmul(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId, y: ExprId) -> ExprId {
    d.const_app(p.mul, &[x, y])
}

fn cabs(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId) -> ExprId {
    d.const_app(p.abs, &[x])
}

fn erefl(d: &mut IntDev<'_>, p: CRealPrelude, a: ExprId) -> ExprId {
    d.lemma(p.equiv_refl, &[a])
}

/// From `h : Equiv a b`, `Equiv b a`.
fn esymm(d: &mut IntDev<'_>, p: CRealPrelude, a: ExprId, b: ExprId, h: ExprId) -> ExprId {
    d.lemma(p.equiv_symm, &[a, b, h])
}

/// `ofRat (natDivSucc (Nat.succ k) 0)` -- "`k+1`", `CReal.BoundedOn`'s own
/// magnitude bound. Local copy of `creal/derivative.rs::mag_bound` (private
/// there); constructed via the identical sequence of calls
/// (`d.succ`/`d.num`/[`div_succ_at`]/`p.of_rat`) so that, for the SAME `k`
/// expression, it interns to the SAME term `BoundedOn`'s own declaration
/// unfolds to -- which is what lets [`bounded_on_applied`]'s hypotheses be
/// used directly against it below.
fn mag_bound(d: &mut IntDev<'_>, p: CRealPrelude, k: ExprId) -> ExprId {
    let succ_k = d.succ(k);
    let zero_idx = d.num(0);
    let r = div_succ_at(d, p, succ_k, zero_idx);
    d.const_app(p.of_rat, &[r])
}

/// `le zero (mag_bound k)`, via `Rat.zero_le_natDivSucc` lifted by
/// `CReal.ofRat_le` -- `CReal.zero` is defeq to `ofRat Rat.zero` (the same
/// fact [`declare_uniformly_continuous_const`] already relies on).
fn mag_bound_nonneg(d: &mut IntDev<'_>, p: CRealPrelude, k: ExprId) -> ExprId {
    let succ_k = d.succ(k);
    let zero_idx = d.num(0);
    let bound_rat = div_succ_at(d, p, succ_k, zero_idx);
    let rzero_expr = crate::rat_prelude::ops::rzero(d, p.rat);
    let rat_nonneg = d.lemma(p.rat.zero_le_nat_div_succ, &[succ_k, zero_idx]);
    d.lemma(p.of_rat_le, &[rzero_expr, bound_rat, rat_nonneg])
}

/// `CReal.BoundedOn h a b k` applied.
fn bounded_on_applied(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    h: ExprId,
    a: ExprId,
    b: ExprId,
    k: ExprId,
) -> ExprId {
    d.const_app(p.bounded_on, &[h, a, b, k])
}

/// `(k+1)*m + k` -- `Rat.natDivSucc_scale`'s own index shape. Local copy of
/// `creal/derivative.rs::rescale_index` (private there).
fn rescale_index(d: &mut IntDev<'_>, k: ExprId, m: ExprId) -> ExprId {
    let succ_k = d.succ(k);
    let mul_km = d.mul(succ_k, m);
    d.add(mul_km, k)
}

/// From `h_ab_zero : Equiv (add a b) zero`, `Equiv b (neg a)` -- `b` is the
/// unique additive inverse of `a`. Local copy of
/// `creal/derivative.rs::neg_unique` (private there).
fn neg_unique(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    a: ExprId,
    b: ExprId,
    h_ab_zero: ExprId,
) -> ExprId {
    let zero_c = czero(d, p);
    let neg_a = cneg(d, p, a);

    let add_a_nega = cadd(d, p, a, neg_a);
    let add_nega_a = cadd(d, p, neg_a, a);
    let h_add_neg = d.lemma(p.add_neg, &[a]);
    let comm0 = d.lemma(p.add_comm, &[a, neg_a]);
    let symm_h = esymm(d, p, add_a_nega, zero_c, h_add_neg);
    let zero_equiv_nega_a = d.lemma(
        p.equiv_trans,
        &[zero_c, add_a_nega, add_nega_a, symm_h, comm0],
    );

    let add_b_zero = cadd(d, p, b, zero_c);
    let add_zero_b = cadd(d, p, zero_c, b);
    let h_addzero_b = d.lemma(p.add_zero, &[b]);
    let b_equiv_addbzero = esymm(d, p, add_b_zero, b, h_addzero_b);
    let comm_b0 = d.lemma(p.add_comm, &[b, zero_c]);
    let b_equiv_addzerob = d.lemma(
        p.equiv_trans,
        &[b, add_b_zero, add_zero_b, b_equiv_addbzero, comm_b0],
    );

    let addnega_a = cadd(d, p, neg_a, a);
    let addnega_a_plus_b = cadd(d, p, addnega_a, b);
    let refl_b = erefl(d, p, b);
    let subst1 = d.lemma(
        p.add_congr,
        &[zero_c, addnega_a, b, b, zero_equiv_nega_a, refl_b],
    );

    let a_plus_b = cadd(d, p, a, b);
    let nega_plus_aplusb = cadd(d, p, neg_a, a_plus_b);
    let assoc = d.lemma(p.add_assoc, &[neg_a, a, b]);

    let nega_plus_zero = cadd(d, p, neg_a, zero_c);
    let refl_nega = erefl(d, p, neg_a);
    let subst2 = d.lemma(
        p.add_congr,
        &[neg_a, neg_a, a_plus_b, zero_c, refl_nega, h_ab_zero],
    );

    let final_step = d.lemma(p.add_zero, &[neg_a]);

    echain(
        d,
        p,
        b,
        &[
            (add_zero_b, b_equiv_addzerob),
            (addnega_a_plus_b, subst1),
            (nega_plus_aplusb, assoc),
            (nega_plus_zero, subst2),
            (neg_a, final_step),
        ],
    )
}

/// `Equiv (add (neg x) x) zero`.
fn neg_add_self(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId) -> ExprId {
    let zero_c = czero(d, p);
    let nx = cneg(d, p, x);
    let x_nx = cadd(d, p, x, nx);
    let nx_x = cadd(d, p, nx, x);
    let comm = d.lemma(p.add_comm, &[x, nx]);
    let comm_symm = esymm(d, p, x_nx, nx_x, comm);
    let cancel = d.lemma(p.add_neg, &[x]);
    echain(d, p, nx_x, &[(x_nx, comm_symm), (zero_c, cancel)])
}

/// `Equiv (neg (neg x)) x`.
fn double_neg(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId) -> ExprId {
    let nx = cneg(d, p, x);
    let nnx = cneg(d, p, nx);
    let h = neg_add_self(d, p, x);
    let nu = neg_unique(d, p, nx, x, h);
    esymm(d, p, x, nnx, nu)
}

/// `Equiv (mul x (neg y)) (neg (mul x y))`. Local copy of
/// `creal/derivative.rs::mul_neg_equiv` (private there) -- see this file's
/// module documentation, "Scalar multiplication", for why this identity was
/// previously flagged as an unwritten prerequisite.
fn mul_neg_equiv(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId, y: ExprId) -> ExprId {
    let zero_c = czero(d, p);
    let ny = cneg(d, p, y);
    let xy = cmul(d, p, x, y);
    let x_ny = cmul(d, p, x, ny);
    let y_plus_ny = cadd(d, p, y, ny);
    let x_times_sum = cmul(d, p, x, y_plus_ny);

    let h_add_neg_y = d.lemma(p.add_neg, &[y]);
    let refl_x = erefl(d, p, x);
    let h_mulcongr = d.lemma(p.mul_congr, &[x, x, y_plus_ny, zero_c, refl_x, h_add_neg_y]);
    let x_zero = cmul(d, p, x, zero_c);
    let h_mulzero = d.lemma(p.mul_zero, &[x]);
    let sum_equiv_zero = echain(
        d,
        p,
        x_times_sum,
        &[(x_zero, h_mulcongr), (zero_c, h_mulzero)],
    );

    let h_ld = d.lemma(p.left_distrib, &[x, y, ny]);
    let sum_of_products = cadd(d, p, xy, x_ny);
    let symm_ld = esymm(d, p, x_times_sum, sum_of_products, h_ld);
    let h_sum_zero = d.lemma(
        p.equiv_trans,
        &[
            sum_of_products,
            x_times_sum,
            zero_c,
            symm_ld,
            sum_equiv_zero,
        ],
    );

    neg_unique(d, p, xy, x_ny, h_sum_zero)
}

/// From `h : le (abs w) q`, derive `le (abs (neg w)) q`.
fn abs_neg_le(d: &mut IntDev<'_>, p: CRealPrelude, w: ExprId, q: ExprId, h: ExprId) -> ExprId {
    let abs_w = cabs(d, p, w);
    let neg_w = cneg(d, p, w);
    let w_le_absw = d.lemma(p.le_abs_self, &[w]);
    let w_le_q = d.lemma(p.le_trans, &[w, abs_w, q, w_le_absw, h]);
    let negw_le_absw = d.lemma(p.neg_le_abs, &[w]);
    let negw_le_q = d.lemma(p.le_trans, &[neg_w, abs_w, q, negw_le_absw, h]);

    let neg_neg_w = cneg(d, p, neg_w);
    let nn = double_neg(d, p, w); // Equiv neg_neg_w w
    let nn_symm = esymm(d, p, neg_neg_w, w, nn); // Equiv w neg_neg_w
    let refl_q = erefl(d, p, q);
    let nnw_le_q = d.lemma(p.le_congr, &[w, neg_neg_w, q, q, nn_symm, refl_q, w_le_q]);
    // nnw_le_q : le neg_neg_w q

    d.lemma(p.abs_le, &[neg_w, q, negw_le_q, nnw_le_q])
}

/// `Equiv (add (add x (neg z)) (add z w)) (add x w)` -- the four-term
/// telescoping cancellation the product rule's cross terms collapse
/// through, once each is expressed as `(A - P) + (P - B)`.
fn middle_cancel(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId, z: ExprId, w: ExprId) -> ExprId {
    let zero_c = czero(d, p);
    let nz = cneg(d, p, z);
    let x_nz = cadd(d, p, x, nz);
    let z_w = cadd(d, p, z, w);
    let lhs = cadd(d, p, x_nz, z_w);

    let nz_zw = cadd(d, p, nz, z_w);
    let x_plus_nzzw = cadd(d, p, x, nz_zw);
    let assoc1 = d.lemma(p.add_assoc, &[x, nz, z_w]);
    // assoc1 : Equiv lhs x_plus_nzzw

    let nz_z = cadd(d, p, nz, z);
    let z_nz = cadd(d, p, z, nz);
    let comm_nz_z = d.lemma(p.add_comm, &[nz, z]);
    let cancel_z = d.lemma(p.add_neg, &[z]);
    let nzz_zero = echain(d, p, nz_z, &[(z_nz, comm_nz_z), (zero_c, cancel_z)]);
    // nzz_zero : Equiv nz_z zero_c

    let refl_w = erefl(d, p, w);
    let nzzw_zerow = d.lemma(p.add_congr, &[nz_z, zero_c, w, w, nzz_zero, refl_w]);
    // nzzw_zerow : Equiv (add nz_z w) (add zero_c w)
    let nzz_w = cadd(d, p, nz_z, w);
    let zero_w = cadd(d, p, zero_c, w);

    let assoc2 = d.lemma(p.add_assoc, &[nz, z, w]);
    // assoc2 : Equiv nzz_w nz_zw
    let assoc2_symm = esymm(d, p, nzz_w, nz_zw, assoc2);
    // assoc2_symm : Equiv nz_zw nzz_w

    let w_zero = cadd(d, p, w, zero_c);
    let comm_0w = d.lemma(p.add_comm, &[zero_c, w]);
    let zerow_w = d.lemma(p.add_zero, &[w]);
    let zerow_chain = echain(d, p, zero_w, &[(w_zero, comm_0w), (w, zerow_w)]);
    // zerow_chain : Equiv zero_w w

    let nz_zw_to_w = echain(
        d,
        p,
        nz_zw,
        &[(nzz_w, assoc2_symm), (zero_w, nzzw_zerow), (w, zerow_chain)],
    );
    // nz_zw_to_w : Equiv nz_zw w

    let refl_x = erefl(d, p, x);
    let x_plus_result = d.lemma(p.add_congr, &[x, x, nz_zw, w, refl_x, nz_zw_to_w]);
    // x_plus_result : Equiv x_plus_nzzw (add x w)
    let x_w = cadd(d, p, x, w);

    echain(d, p, lhs, &[(x_plus_nzzw, assoc1), (x_w, x_plus_result)])
}

/// `Equiv (add term1 term2) (add (mul fx gx) (neg (mul fy gy)))`, where
/// `term1 := mul fx (add gx (neg gy))` and `term2 := mul gy (add fx (neg
/// fy))` -- `F(x)G(x) - F(y)G(y) = F(x)(G(x)-G(y)) + G(y)(F(x)-F(y))`, the
/// genuine product-of-bounds estimate this file's module documentation
/// flags (as opposed to a triangle inequality). Returns `(term1, term2,
/// target, proof)`.
fn product_diff_identity(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    fx: ExprId,
    fy: ExprId,
    gx: ExprId,
    gy: ExprId,
) -> (ExprId, ExprId, ExprId, ExprId) {
    let neg_gy = cneg(d, p, gy);
    let neg_fy = cneg(d, p, fy);
    let diff_g = cadd(d, p, gx, neg_gy);
    let diff_f = cadd(d, p, fx, neg_fy);
    let term1 = cmul(d, p, fx, diff_g);
    let term2 = cmul(d, p, gy, diff_f);

    let a_val = cmul(d, p, fx, gx); // A
    let p_val = cmul(d, p, fx, gy); // P
    let b_val = cmul(d, p, fy, gy); // B
    let neg_p_val = cneg(d, p, p_val);
    let neg_b_val = cneg(d, p, b_val);

    // term1 ~ add A (neg P)
    let ld1 = d.lemma(p.left_distrib, &[fx, gx, neg_gy]);
    // ld1 : Equiv term1 (add A (mul fx neg_gy))
    let mfx_ngy = cmul(d, p, fx, neg_gy);
    let mne1 = mul_neg_equiv(d, p, fx, gy); // Equiv mfx_ngy neg_p_val
    let refl_a = erefl(d, p, a_val);
    let cong1 = d.lemma(
        p.add_congr,
        &[a_val, a_val, mfx_ngy, neg_p_val, refl_a, mne1],
    );
    // cong1 : Equiv (add A mfx_ngy) (add A neg_p_val)
    let a_plus_mfxngy = cadd(d, p, a_val, mfx_ngy);
    let a_plus_negp = cadd(d, p, a_val, neg_p_val);
    let term1_equiv = echain(d, p, term1, &[(a_plus_mfxngy, ld1), (a_plus_negp, cong1)]);
    // term1_equiv : Equiv term1 a_plus_negp

    // term2 ~ add P (neg B)
    let ld2 = d.lemma(p.left_distrib, &[gy, fx, neg_fy]);
    // ld2 : Equiv term2 (add (mul gy fx) (mul gy neg_fy))
    let mgy_fx = cmul(d, p, gy, fx);
    let mgy_nfy = cmul(d, p, gy, neg_fy);
    let comm_gyfx = d.lemma(p.mul_comm, &[gy, fx]); // Equiv mgy_fx p_val
    let mgy_fy = cmul(d, p, gy, fy);
    let mne2 = mul_neg_equiv(d, p, gy, fy); // Equiv mgy_nfy (neg mgy_fy)
    let comm_gyfy = d.lemma(p.mul_comm, &[gy, fy]); // Equiv mgy_fy b_val
    let neg_mgyfy = cneg(d, p, mgy_fy);
    let neg_comm_gyfy = d.lemma(p.neg_congr, &[mgy_fy, b_val, comm_gyfy]);
    // neg_comm_gyfy : Equiv neg_mgyfy neg_b_val
    let mgy_nfy_to_negb = echain(
        d,
        p,
        mgy_nfy,
        &[(neg_mgyfy, mne2), (neg_b_val, neg_comm_gyfy)],
    );
    // mgy_nfy_to_negb : Equiv mgy_nfy neg_b_val
    let cong2 = d.lemma(
        p.add_congr,
        &[
            mgy_fx,
            p_val,
            mgy_nfy,
            neg_b_val,
            comm_gyfx,
            mgy_nfy_to_negb,
        ],
    );
    // cong2 : Equiv (add mgy_fx mgy_nfy) (add p_val neg_b_val)
    let mgyfx_plus_mgynfy = cadd(d, p, mgy_fx, mgy_nfy);
    let p_plus_negb = cadd(d, p, p_val, neg_b_val);
    let term2_equiv = echain(
        d,
        p,
        term2,
        &[(mgyfx_plus_mgynfy, ld2), (p_plus_negb, cong2)],
    );
    // term2_equiv : Equiv term2 p_plus_negb

    let sum_equiv = d.lemma(
        p.add_congr,
        &[
            term1,
            a_plus_negp,
            term2,
            p_plus_negb,
            term1_equiv,
            term2_equiv,
        ],
    );
    // sum_equiv : Equiv (add term1 term2) (add a_plus_negp p_plus_negb)
    let lhs_telescope = cadd(d, p, a_plus_negp, p_plus_negb);

    let telescope = middle_cancel(d, p, a_val, p_val, neg_b_val);
    // telescope : Equiv lhs_telescope (add a_val neg_b_val)
    let target = cadd(d, p, a_val, neg_b_val);

    let sum_term1_term2 = cadd(d, p, term1, term2);
    let proof = echain(
        d,
        p,
        sum_term1_term2,
        &[(lhs_telescope, sum_equiv), (target, telescope)],
    );

    (term1, term2, target, proof)
}

/// From `e_prime := rescale_index(k, m)`, `Equiv (mul (mag_bound k) (ofRat
/// (natDivSucc 1 e_prime))) (ofRat (natDivSucc 1 m))`. Local copy of
/// `creal/derivative.rs::fold_index0_first` (private there). Returns
/// `(big_expr, small_expr, ofr_out, proof)`.
fn fold_mag_bound_error(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    k: ExprId,
    m: ExprId,
    e_prime: ExprId,
) -> (ExprId, ExprId, ExprId, ExprId) {
    let succ_k = d.succ(k);
    let zero_idx = d.num(0);
    let bound_rat = div_succ_at(d, p, succ_k, zero_idx); // natDivSucc (succ k) 0
    let big_expr = d.const_app(p.of_rat, &[bound_rat]);

    let r_prime = div_succ(d, p, 1, e_prime); // natDivSucc 1 e_prime
    let small_expr = d.const_app(p.of_rat, &[r_prime]);

    let one_nat = d.num(1);
    let mul_succk_1 = d.mul(succ_k, one_nat);
    let succ_k_e_prime = div_succ_at(d, p, succ_k, e_prime);
    let out_bound_rat = div_succ(d, p, 1, m);

    let eq_mul = d.lemma(p.rat.nat_div_succ_mul, &[succ_k, one_nat, e_prime]);
    let mul_one_eq = d.lemma(p.rat.int.nat.mul_one, &[succ_k]);
    let eq_fold = nat_eq_to_rat(d, mul_succk_1, succ_k, mul_one_eq, &|d, x| {
        div_succ_at(d, p, x, e_prime)
    });
    let eq_scale = d.lemma(p.rat.nat_div_succ_scale, &[k, m]);

    let of_rat_mul_proof = d.lemma(p.of_rat_mul, &[bound_rat, r_prime]);
    let mul_bb_ofre = cmul(d, p, big_expr, small_expr);
    let rat_prod = {
        let f_ap = d.int().rat_mul;
        d.const_app(f_ap, &[bound_rat, r_prime])
    };
    let mul_succk1_e_prime = div_succ_at(d, p, mul_succk_1, e_prime);

    let motive = |d: &mut IntDev<'_>, t: ExprId| {
        let oft = d.const_app(p.of_rat, &[t]);
        d.const_app(p.equiv, &[mul_bb_ofre, oft])
    };
    let step_a = rat_eq_rewrite(
        d,
        rat_prod,
        mul_succk1_e_prime,
        eq_mul,
        of_rat_mul_proof,
        &motive,
    );
    let step_b = rat_eq_rewrite(
        d,
        mul_succk1_e_prime,
        succ_k_e_prime,
        eq_fold,
        step_a,
        &motive,
    );
    let step_c = rat_eq_rewrite(d, succ_k_e_prime, out_bound_rat, eq_scale, step_b, &motive);
    let ofr_out = d.const_app(p.of_rat, &[out_bound_rat]);

    (big_expr, small_expr, ofr_out, step_c)
}

// --- witness: `neg` (closure under unary negation) --------------------------

/// `CReal.uniformly_continuous_neg : ∀ F a b, UniformlyContinuousOn F a b ->
/// UniformlyContinuousOn (fun r => neg (F r)) a b`.
///
/// The modulus is UNCHANGED (`mF` itself) -- negating both sides of a
/// closeness bound does not weaken it, and [`abs_neg_le`] carries the bound
/// across `abs (neg _)`.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
fn declare_uniformly_continuous_neg(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let func_ty = fn_ty(d, p);
    let nat = d.nat_ty();

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);

    let huc_ty = uc_ty(d, p, f, a, b);
    let huc_fv = d.fresh_fvar();
    let huc = d.kernel().fvar(huc_fv);

    let neg_fn = {
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);
        let fr = d.apply(f, &[r]);
        let nfr = cneg(d, p, fr);
        d.lam_fv(r_fv, carrier, nfr)
    };

    let mf = d.const_app(p.uc_modulus, &[f, a, b, huc]);

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

        let mf_n = d.apply(mf, &[n]);
        let in_bound = div_succ(d, p, 1, mf_n);
        let hyp = close_within(d, p, x, y, in_bound);
        let h = d.kernel().fvar(h_fv);

        let fx = d.apply(f, &[x]);
        let fy = d.apply(f, &[y]);
        let spec_f = d.const_app(p.uc_spec, &[f, a, b, huc]);
        let close_f = d.apply(spec_f, &[n, x, y, hax, hxb, hay, hyb, h]);

        let neg_fy = cneg(d, p, fy);
        let w = cadd(d, p, fx, neg_fy);
        let out_bound = div_succ(d, p, 1, n);
        let q = d.const_app(p.of_rat, &[out_bound]);
        // close_f : le (abs w) q

        let bound_neg_w = abs_neg_le(d, p, w, q, close_f);
        let neg_w = cneg(d, p, w);
        // bound_neg_w : le (abs neg_w) q

        let neg_fx = cneg(d, p, fx);
        let neg_neg_fy = cneg(d, p, neg_fy);
        let target = cadd(d, p, neg_fx, neg_neg_fy);
        let nadd = neg_add(d, p, fx, neg_fy);
        // nadd : Equiv neg_w target

        let abs_negw = cabs(d, p, neg_w);
        let abs_target = cabs(d, p, target);
        let abs_equiv = d.lemma(p.abs_congr, &[neg_w, target, nadd]);
        let refl_q = erefl(d, p, q);
        let result = d.lemma(
            p.le_congr,
            &[abs_negw, abs_target, q, q, abs_equiv, refl_q, bound_neg_w],
        );
        // result : le abs_target q

        let with_h = d.lam_fv(h_fv, hyp, result);
        let with_hyb = d.lam_fv(hyb_fv, range_yb, with_h);
        let with_hay = d.lam_fv(hay_fv, range_ay, with_hyb);
        let with_hxb = d.lam_fv(hxb_fv, range_xb, with_hay);
        let with_hax = d.lam_fv(hax_fv, range_ax, with_hxb);
        let with_y = d.lam_fv(y_fv, carrier, with_hax);
        let with_x = d.lam_fv(x_fv, carrier, with_y);
        d.lam_fv(n_fv, nat, with_x)
    };

    let mk_applied = d.const_app(p.uc_mk, &[neg_fn, a, b, mf, spec]);
    let value = {
        let with_huc = d.lam_fv(huc_fv, huc_ty, mk_applied);
        let with_b = d.lam_fv(b_fv, carrier, with_huc);
        let with_a = d.lam_fv(a_fv, carrier, with_b);
        d.lam_fv(f_fv, func_ty, with_a)
    };
    let ty = {
        let applied = uc_ty(d, p, neg_fn, a, b);
        let with_huc = d.arrow(huc_ty, applied);
        let with_b = d.pi_fv(b_fv, carrier, with_huc);
        let with_a = d.pi_fv(a_fv, carrier, with_b);
        d.pi_fv(f_fv, func_ty, with_a)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.uniformly_continuous_neg,
        uparams: vec![],
        ty,
        value,
    })
}

// --- witness: `sub` (closure under subtraction) -----------------------------

/// `CReal.uniformly_continuous_sub : ∀ F G a b, UniformlyContinuousOn F a b
/// -> UniformlyContinuousOn G a b -> UniformlyContinuousOn (fun r => add (F
/// r) (neg (G r))) a b` -- pure composition of
/// [`declare_uniformly_continuous_add`] and
/// [`declare_uniformly_continuous_neg`], no new estimate.
///
/// # Errors
///
/// Returns the trusted gate's rejection.
fn declare_uniformly_continuous_sub(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let func_ty = fn_ty(d, p);

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

    let neg_g_fn = {
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);
        let gr = d.apply(g, &[r]);
        let ngr = cneg(d, p, gr);
        d.lam_fv(r_fv, carrier, ngr)
    };

    let huc_neg_g = d.lemma(p.uniformly_continuous_neg, &[g, a, b, huc_g]);
    let body = d.lemma(
        p.uniformly_continuous_add,
        &[f, neg_g_fn, a, b, huc_f, huc_neg_g],
    );

    let sub_fn = {
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);
        let fr = d.apply(f, &[r]);
        let ngr = d.apply(neg_g_fn, &[r]);
        let diff = cadd(d, p, fr, ngr);
        d.lam_fv(r_fv, carrier, diff)
    };

    let value = {
        let with_huc_g = d.lam_fv(huc_g_fv, huc_g_ty, body);
        let with_huc_f = d.lam_fv(huc_f_fv, huc_f_ty, with_huc_g);
        let with_b = d.lam_fv(b_fv, carrier, with_huc_f);
        let with_a = d.lam_fv(a_fv, carrier, with_b);
        let with_g = d.lam_fv(g_fv, func_ty, with_a);
        d.lam_fv(f_fv, func_ty, with_g)
    };
    let ty = {
        let concl = uc_ty(d, p, sub_fn, a, b);
        let with_huc_g = d.arrow(huc_g_ty, concl);
        let with_huc_f = d.arrow(huc_f_ty, with_huc_g);
        let with_b = d.pi_fv(b_fv, carrier, with_huc_f);
        let with_a = d.pi_fv(a_fv, carrier, with_b);
        let with_g = d.pi_fv(g_fv, func_ty, with_a);
        d.pi_fv(f_fv, func_ty, with_g)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.uniformly_continuous_sub,
        uparams: vec![],
        ty,
        value,
    })
}

// --- witness: `mul` (closure under multiplication, `BoundedOn`-gated) ------

/// `CReal.uniformly_continuous_mul : ∀ F G a b, UniformlyContinuousOn F a b
/// -> UniformlyContinuousOn G a b -> ∀ k1 k2, BoundedOn F a b k1 -> BoundedOn
/// G a b k2 -> UniformlyContinuousOn (fun r => mul (F r) (G r)) a b`.
///
/// ## The estimate, worked on paper first
///
/// `F(x)G(x) - F(y)G(y) = F(x)(G(x)-G(y)) + G(y)(F(x)-F(y))`
/// ([`product_diff_identity`]), so with `|F(x)| <= k1+1` and `|G(y)| <= k2+1`
/// ([`BoundedOn`]):
///
/// `|F(x)G(x)-F(y)G(y)| <= (k1+1)|G(x)-G(y)| + (k2+1)|F(x)-F(y)|`
/// ([`abs_mul_le_of_bounds`](super::CRealPrelude::abs_mul_le_of_bounds) at
/// each term, via the two-sided identity's own triangle inequality
/// [`abs_add_le`]).
///
/// Target accuracy `n` needs `1/(n+1)` total, split as two `1/(2n+2)`
/// shares exactly [`declare_uniformly_continuous_add`]'s own two-way split
/// (`m := succ(2n)`). Each share must absorb its OWN magnitude weight:
/// `(k1+1) * X <= 1/(2n+2)` needs `X <= 1/((k1+1)(2n+2))`, gotten from `G`'s
/// own spec at accuracy `e_g := rescale_index(k1, m) = (k1+1)*m + k1`, since
/// `Rat.natDivSucc_scale` reads `(k1+1)/(e_g+1)` back down to `1/(m+1)`
/// exactly ([`fold_mag_bound_error`] -- concretely, with `k1 = 0`, `m = 3`
/// (accuracy `n=1`): `e_g = 1*3+0 = 3`, and `(0+1)/(3+1) = 1/4 = natDivSucc
/// 1 3`, matching `m=3` on the nose). Symmetrically `e_f :=
/// rescale_index(k2, m)` for `F`'s own spec, weighted by `k2` (`G`'s bound,
/// since term two is `G(y)*(F(x)-F(y))`). The combined modulus is
/// `mG(e_g) + mF(e_f)`, weakened down to each factor's own hypothesis by
/// `Nat.le_add_right` + `Rat.natDivSucc_antitone`, the identical recipe
/// [`declare_uniformly_continuous_add`] uses for its own two-source modulus
/// (`Nat.add_comm` handles the second, symmetric, direction).
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
#[allow(clippy::too_many_lines)]
fn declare_uniformly_continuous_mul(
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

    let k1_fv = d.fresh_fvar();
    let k1 = d.kernel().fvar(k1_fv);
    let k2_fv = d.fresh_fvar();
    let k2 = d.kernel().fvar(k2_fv);

    let hbf_ty = bounded_on_applied(d, p, f, a, b, k1);
    let hbf_fv = d.fresh_fvar();
    let hbf = d.kernel().fvar(hbf_fv);
    let hbg_ty = bounded_on_applied(d, p, g, a, b, k2);
    let hbg_fv = d.fresh_fvar();
    let hbg = d.kernel().fvar(hbg_fv);

    let mul_fn = {
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);
        let fr = d.apply(f, &[r]);
        let gr = d.apply(g, &[r]);
        let prod = cmul(d, p, fr, gr);
        d.lam_fv(r_fv, carrier, prod)
    };

    let mf = d.const_app(p.uc_modulus, &[f, a, b, huc_f]);
    let mg = d.const_app(p.uc_modulus, &[g, a, b, huc_g]);

    let m_of = |d: &mut IntDev<'_>, n: ExprId| -> ExprId {
        let two = d.num(2);
        let two_n = d.mul(two, n);
        d.succ(two_n)
    };

    let modulus_mul = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let m = m_of(d, n);
        let e_g = rescale_index(d, k1, m);
        let e_f = rescale_index(d, k2, m);
        let mg_eg = d.apply(mg, &[e_g]);
        let mf_ef = d.apply(mf, &[e_f]);
        let sum = d.add(mg_eg, mf_ef);
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

        let m = m_of(d, n);
        let e_g = rescale_index(d, k1, m);
        let e_f = rescale_index(d, k2, m);
        let mg_eg = d.apply(mg, &[e_g]);
        let mf_ef = d.apply(mf, &[e_f]);
        let combined = d.add(mg_eg, mf_ef);

        let mod_n = d.apply(modulus_mul, &[n]);
        let in_bound = div_succ(d, p, 1, mod_n);
        let hyp = close_within(d, p, x, y, in_bound);
        let h = d.kernel().fvar(h_fv);

        // --- weaken `h` down to G's and F's own hypotheses, the
        // `uniformly_continuous_add` recipe verbatim. -----------------------
        let nat_p = p.rat.int.nat;
        let h_le_g = d.lemma(nat_p.le_add_right, &[mg_eg, mf_ef]); // Le mg_eg combined
        let mf_plus_mg = d.add(mf_ef, mg_eg);
        let raw_f = d.lemma(nat_p.le_add_right, &[mf_ef, mg_eg]); // Le mf_ef mf_plus_mg
        let comm_eq = d.lemma(nat_p.add_comm, &[mf_ef, mg_eg]); // Eq mf_plus_mg combined
        let h_le_f = nat_rewrite_prop(d, mf_plus_mg, combined, comm_eq, raw_f, &|d, t| {
            NatOps::le(d, mf_ef, t)
        });

        let r_g = div_succ(d, p, 1, mg_eg);
        let r_f = div_succ(d, p, 1, mf_ef);
        let r_combined = div_succ(d, p, 1, combined);
        let rat_g = d.lemma(p.rat.nat_div_succ_antitone, &[mg_eg, combined, h_le_g]);
        let rat_f = d.lemma(p.rat.nat_div_succ_antitone, &[mf_ef, combined, h_le_f]);

        let ofr_combined = d.const_app(p.of_rat, &[r_combined]);
        let ofr_g = d.const_app(p.of_rat, &[r_g]);
        let ofr_f = d.const_app(p.of_rat, &[r_f]);
        let creal_g = d.lemma(p.of_rat_le, &[r_combined, r_g, rat_g]);
        let creal_f = d.lemma(p.of_rat_le, &[r_combined, r_f, rat_f]);

        let ny = cneg(d, p, y);
        let diff_xy = cadd(d, p, x, ny);
        let abs_diff = cabs(d, p, diff_xy);
        let hyp_g = d.lemma(p.le_trans, &[abs_diff, ofr_combined, ofr_g, h, creal_g]);
        let hyp_f = d.lemma(p.le_trans, &[abs_diff, ofr_combined, ofr_f, h, creal_f]);
        // hyp_g : close_within x y r_g ; hyp_f : close_within x y r_f

        let fx = d.apply(f, &[x]);
        let fy = d.apply(f, &[y]);
        let gx = d.apply(g, &[x]);
        let gy = d.apply(g, &[y]);

        let spec_g = d.const_app(p.uc_spec, &[g, a, b, huc_g]);
        let spec_f = d.const_app(p.uc_spec, &[f, a, b, huc_f]);
        let close_g = d.apply(spec_g, &[e_g, x, y, hax, hxb, hay, hyb, hyp_g]);
        let close_f = d.apply(spec_f, &[e_f, x, y, hax, hxb, hay, hyb, hyp_f]);
        // close_g : le (abs (add gx (neg gy))) (ofRat (natDivSucc 1 e_g))
        // close_f : le (abs (add fx (neg fy))) (ofRat (natDivSucc 1 e_f))

        let hbf_x = d.apply(hbf, &[x, hax, hxb]); // le (abs fx) (mag_bound k1)
        let hbg_y = d.apply(hbg, &[y, hay, hyb]); // le (abs gy) (mag_bound k2)

        let (term1, term2, target, diff_proof) = product_diff_identity(d, p, fx, fy, gx, gy);
        let abs_term1 = cabs(d, p, term1);
        let abs_term2 = cabs(d, p, term2);

        // --- term1 := mul fx (add gx (neg gy)), bounded by
        // ofRat(natDivSucc 1 m) -------------------------------------------
        let neg_gy = cneg(d, p, gy);
        let diff_g = cadd(d, p, gx, neg_gy);
        let abs_diff_g = cabs(d, p, diff_g);
        let refl_absdiffg = d.lemma(p.le_refl, &[abs_diff_g]);
        let (fold1_big, fold1_small, fold1_out, fold1_proof) =
            fold_mag_bound_error(d, p, k1, m, e_g);
        let term1_abs_le_prod = d.lemma(
            p.abs_mul_le_of_bounds,
            &[fx, diff_g, fold1_big, abs_diff_g, hbf_x, refl_absdiffg],
        );
        // term1_abs_le_prod : le (abs term1) (mul fold1_big abs_diff_g)
        let magk1_nonneg = mag_bound_nonneg(d, p, k1);
        let scaled_g = d.lemma(
            p.mul_le_mul_of_nonneg_left,
            &[fold1_big, abs_diff_g, fold1_small, magk1_nonneg, close_g],
        );
        // scaled_g : le (mul fold1_big abs_diff_g) (mul fold1_big fold1_small)
        let mul_fold1 = cmul(d, p, fold1_big, abs_diff_g);
        let mul_fold1_small = cmul(d, p, fold1_big, fold1_small);
        let term1_le_unfused = d.lemma(
            p.le_trans,
            &[
                abs_term1,
                mul_fold1,
                mul_fold1_small,
                term1_abs_le_prod,
                scaled_g,
            ],
        );
        // term1_le_unfused : le (abs term1) (mul fold1_big fold1_small)
        let refl_absterm1 = erefl(d, p, abs_term1);
        let final1 = d.lemma(
            p.le_congr,
            &[
                abs_term1,
                abs_term1,
                mul_fold1_small,
                fold1_out,
                refl_absterm1,
                fold1_proof,
                term1_le_unfused,
            ],
        );
        // final1 : le (abs term1) fold1_out,  fold1_out = ofRat(natDivSucc 1 m)

        // --- term2 := mul gy (add fx (neg fy)), symmetric ------------------
        let neg_fy = cneg(d, p, fy);
        let diff_f = cadd(d, p, fx, neg_fy);
        let abs_diff_f = cabs(d, p, diff_f);
        let refl_absdifff = d.lemma(p.le_refl, &[abs_diff_f]);
        let (fold2_big, fold2_small, fold2_out, fold2_proof) =
            fold_mag_bound_error(d, p, k2, m, e_f);
        let term2_abs_le_prod = d.lemma(
            p.abs_mul_le_of_bounds,
            &[gy, diff_f, fold2_big, abs_diff_f, hbg_y, refl_absdifff],
        );
        let magk2_nonneg = mag_bound_nonneg(d, p, k2);
        let scaled_f = d.lemma(
            p.mul_le_mul_of_nonneg_left,
            &[fold2_big, abs_diff_f, fold2_small, magk2_nonneg, close_f],
        );
        let mul_fold2 = cmul(d, p, fold2_big, abs_diff_f);
        let mul_fold2_small = cmul(d, p, fold2_big, fold2_small);
        let term2_le_unfused = d.lemma(
            p.le_trans,
            &[
                abs_term2,
                mul_fold2,
                mul_fold2_small,
                term2_abs_le_prod,
                scaled_f,
            ],
        );
        let refl_absterm2 = erefl(d, p, abs_term2);
        let final2 = d.lemma(
            p.le_congr,
            &[
                abs_term2,
                abs_term2,
                mul_fold2_small,
                fold2_out,
                refl_absterm2,
                fold2_proof,
                term2_le_unfused,
            ],
        );
        // final2 : le (abs term2) fold2_out, fold2_out ALSO = ofRat(natDivSucc 1 m)

        // --- triangle inequality + fuse the two `1/(m+1)` shares into
        // `1/(n+1)`, the `uniformly_continuous_add` tail verbatim. ----------
        let sum_bounds = d.lemma(
            p.add_le_add,
            &[abs_term1, fold1_out, abs_term2, fold2_out, final1, final2],
        );
        let triangle = abs_add_le(d, p, term1, term2);
        let sum_term1_term2 = cadd(d, p, term1, term2);
        let abs_sum = cabs(d, p, sum_term1_term2);
        let sum_of_abs = cadd(d, p, abs_term1, abs_term2);
        let fold1_out_plus_fold1_out = cadd(d, p, fold1_out, fold2_out);
        let combined_le = d.lemma(
            p.le_trans,
            &[
                abs_sum,
                sum_of_abs,
                fold1_out_plus_fold1_out,
                triangle,
                sum_bounds,
            ],
        );
        // combined_le : le abs_sum (add fold1_out fold2_out),
        //   fold1_out = fold2_out = ofRat(natDivSucc 1 m)

        let one_nat = d.num(1);
        let r_prime = div_succ(d, p, 1, m); // == the rational inside fold1_out/fold2_out
        let of_rat_add_proof = d.lemma(p.of_rat_add, &[r_prime, r_prime]);
        let eq1 = d.lemma(p.rat.nat_div_succ_add, &[one_nat, one_nat, m]);
        let two_m = div_succ(d, p, 2, m);
        let radd_r_prime_r_prime = radd(d, r_prime, r_prime);
        let step_a = rat_eq_rewrite(
            d,
            radd_r_prime_r_prime,
            two_m,
            eq1,
            of_rat_add_proof,
            &|d, t| {
                let oft = d.const_app(p.of_rat, &[t]);
                d.const_app(p.equiv, &[fold1_out_plus_fold1_out, oft])
            },
        );
        let eq2 = d.lemma(p.rat.nat_div_succ_halve, &[n]);
        let out_bound_rat = div_succ(d, p, 1, n);
        let fuse_equiv = rat_eq_rewrite(d, two_m, out_bound_rat, eq2, step_a, &|d, t| {
            let oft = d.const_app(p.of_rat, &[t]);
            d.const_app(p.equiv, &[fold1_out_plus_fold1_out, oft])
        });
        // fuse_equiv : Equiv fold1_out_plus_fold1_out (ofRat out_bound_rat)
        let ofr_out_bound = d.const_app(p.of_rat, &[out_bound_rat]);

        let refl_abssum = erefl(d, p, abs_sum);
        let fused = d.lemma(
            p.le_congr,
            &[
                abs_sum,
                abs_sum,
                fold1_out_plus_fold1_out,
                ofr_out_bound,
                refl_abssum,
                fuse_equiv,
                combined_le,
            ],
        );
        // fused : le abs_sum ofr_out_bound

        // --- lift through the algebraic identity `sum_term1_term2 ~ target`
        let abs_target = cabs(d, p, target);
        let target_equiv = d.lemma(p.abs_congr, &[sum_term1_term2, target, diff_proof]);
        let refl_ofr_out_bound = erefl(d, p, ofr_out_bound);
        let result = d.lemma(
            p.le_congr,
            &[
                abs_sum,
                abs_target,
                ofr_out_bound,
                ofr_out_bound,
                target_equiv,
                refl_ofr_out_bound,
                fused,
            ],
        );
        // result : le abs_target ofr_out_bound
        //   == close_within (mul_fn x) (mul_fn y) out_bound_rat

        let with_h = d.lam_fv(h_fv, hyp, result);
        let with_hyb = d.lam_fv(hyb_fv, range_yb, with_h);
        let with_hay = d.lam_fv(hay_fv, range_ay, with_hyb);
        let with_hxb = d.lam_fv(hxb_fv, range_xb, with_hay);
        let with_hax = d.lam_fv(hax_fv, range_ax, with_hxb);
        let with_y = d.lam_fv(y_fv, carrier, with_hax);
        let with_x = d.lam_fv(x_fv, carrier, with_y);
        d.lam_fv(n_fv, nat, with_x)
    };

    let mk_applied = d.const_app(p.uc_mk, &[mul_fn, a, b, modulus_mul, spec]);
    let value = {
        let with_hbg = d.lam_fv(hbg_fv, hbg_ty, mk_applied);
        let with_hbf = d.lam_fv(hbf_fv, hbf_ty, with_hbg);
        let with_k2 = d.lam_fv(k2_fv, nat, with_hbf);
        let with_k1 = d.lam_fv(k1_fv, nat, with_k2);
        let with_huc_g = d.lam_fv(huc_g_fv, huc_g_ty, with_k1);
        let with_huc_f = d.lam_fv(huc_f_fv, huc_f_ty, with_huc_g);
        let with_b = d.lam_fv(b_fv, carrier, with_huc_f);
        let with_a = d.lam_fv(a_fv, carrier, with_b);
        let with_g = d.lam_fv(g_fv, func_ty, with_a);
        d.lam_fv(f_fv, func_ty, with_g)
    };
    let ty = {
        let applied = uc_ty(d, p, mul_fn, a, b);
        let with_hbg = d.arrow(hbg_ty, applied);
        let with_hbf = d.arrow(hbf_ty, with_hbg);
        let with_k2 = d.pi_fv(k2_fv, nat, with_hbf);
        let with_k1 = d.pi_fv(k1_fv, nat, with_k2);
        let with_huc_g = d.arrow(huc_g_ty, with_k1);
        let with_huc_f = d.arrow(huc_f_ty, with_huc_g);
        let with_b = d.pi_fv(b_fv, carrier, with_huc_f);
        let with_a = d.pi_fv(a_fv, carrier, with_b);
        let with_g = d.pi_fv(g_fv, func_ty, with_a);
        d.pi_fv(f_fv, func_ty, with_g)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.uniformly_continuous_mul,
        uparams: vec![],
        ty,
        value,
    })
}

// --- corollary: `sq` ---------------------------------------------------------

/// `CReal.uniformly_continuous_sq : ∀ a b k, BoundedOn (fun r => r) a b k ->
/// UniformlyContinuousOn (fun r => mul r r) a b` -- `mul` specialised to `F
/// := G := id`, both bound witnesses the SAME `BoundedOn id a b k`.
///
/// # Errors
///
/// Returns the trusted gate's rejection.
fn declare_uniformly_continuous_sq(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);

    let identity = {
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);
        d.lam_fv(r_fv, carrier, r)
    };

    let huc_id = d.lemma(p.uniformly_continuous_id, &[a, b]);
    let hb_ty = bounded_on_applied(d, p, identity, a, b, k);
    let hb_fv = d.fresh_fvar();
    let hb = d.kernel().fvar(hb_fv);

    let body = d.lemma(
        p.uniformly_continuous_mul,
        &[identity, identity, a, b, huc_id, huc_id, k, k, hb, hb],
    );

    let sq_fn = {
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);
        let ir = d.apply(identity, &[r]);
        let ir2 = d.apply(identity, &[r]);
        let prod = cmul(d, p, ir, ir2);
        d.lam_fv(r_fv, carrier, prod)
    };

    let value = {
        let with_hb = d.lam_fv(hb_fv, hb_ty, body);
        let with_k = d.lam_fv(k_fv, nat, with_hb);
        let with_b = d.lam_fv(b_fv, carrier, with_k);
        d.lam_fv(a_fv, carrier, with_b)
    };
    let ty = {
        let concl = uc_ty(d, p, sq_fn, a, b);
        let with_hb = d.arrow(hb_ty, concl);
        let with_k = d.pi_fv(k_fv, nat, with_hb);
        let with_b = d.pi_fv(b_fv, carrier, with_k);
        d.pi_fv(a_fv, carrier, with_b)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.uniformly_continuous_sq,
        uparams: vec![],
        ty,
        value,
    })
}

// --- concrete instantiation --------------------------------------------------

/// `CReal.bounded_on_id_unit : BoundedOn (fun r => r) zero (mag_bound 0) 0`
/// -- `id` bounded by `1` on `[0, mag_bound 0]`, where `mag_bound 0 = ofRat
/// (natDivSucc 1 0)` IS the kernel's own representation of the real number
/// `1` (chosen, rather than a separate `CReal.one` endpoint, so this proof
/// needs no bridge lemma between the two: `0 <= z <= mag_bound 0` gives `abs
/// z <= mag_bound 0` directly via `abs_le`, since `neg z <= zero <=
/// mag_bound 0`).
///
/// # Errors
///
/// Returns the trusted gate's rejection.
fn declare_bounded_on_id_unit(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let zero_c = czero(d, p);
    let zero_idx = d.num(0);
    let unit = mag_bound(d, p, zero_idx);

    let identity = {
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);
        d.lam_fv(r_fv, carrier, r)
    };

    let z_fv = d.fresh_fvar();
    let z = d.kernel().fvar(z_fv);
    let haz_fv = d.fresh_fvar();
    let haz = d.kernel().fvar(haz_fv);
    let hzb_fv = d.fresh_fvar();
    let hzb = d.kernel().fvar(hzb_fv);

    let range_az = d.const_app(p.le, &[zero_c, z]);
    let range_zb = d.const_app(p.le, &[z, unit]);

    // le (neg z) unit: neg z <= zero (from 0<=z via neg_le_neg + `neg zero ~
    // zero` unfolds by `CReal.zero`'s own defeq to `ofRat Rat.zero`, so
    // `neg zero` and `zero` need `equiv_of_le_le`-free handling) then
    // zero <= unit (mag_bound_nonneg).
    let neg_z = cneg(d, p, z);
    let neg_zero = cneg(d, p, zero_c);
    let negz_le_negzero = d.lemma(p.neg_le_neg, &[zero_c, z, haz]);
    // negz_le_negzero : le (neg z) (neg zero)
    let rzero_expr = crate::rat_prelude::ops::rzero(d, p.rat);
    let ofr_zero = d.const_app(p.of_rat, &[rzero_expr]);
    let of_rat_neg_at_zero = d.lemma(p.of_rat_neg, &[rzero_expr]);
    // of_rat_neg_at_zero : Equiv (neg ofr_zero) (ofRat (Rat.neg rzero_expr))
    let neg_rzero_expr = crate::rat_prelude::ops::rneg(d, rzero_expr);
    let rat_neg_zero_eq = d.lemma(p.rat.neg_zero, &[]);
    // rat_neg_zero_eq : Eq Rat (Rat.neg rzero_expr) rzero_expr
    let neg_zero_equiv_zero = rat_eq_rewrite(
        d,
        neg_rzero_expr,
        rzero_expr,
        rat_neg_zero_eq,
        of_rat_neg_at_zero,
        &|d, t| {
            let oft = d.const_app(p.of_rat, &[t]);
            d.const_app(p.equiv, &[neg_zero, oft])
        },
    );
    // neg_zero_equiv_zero : Equiv neg_zero ofr_zero
    let refl_negz = erefl(d, p, neg_z);
    let negz_le_ofrzero = d.lemma(
        p.le_congr,
        &[
            neg_z,
            neg_z,
            neg_zero,
            ofr_zero,
            refl_negz,
            neg_zero_equiv_zero,
            negz_le_negzero,
        ],
    );
    // negz_le_ofrzero : le neg_z ofr_zero -- and `ofr_zero` is defeq to `zero_c`
    let zero_le_unit = mag_bound_nonneg(d, p, zero_idx);
    let negz_le_unit = d.lemma(
        p.le_trans,
        &[neg_z, ofr_zero, unit, negz_le_ofrzero, zero_le_unit],
    );

    let body = d.lemma(p.abs_le, &[z, unit, hzb, negz_le_unit]);

    let value = {
        let with_hzb = d.lam_fv(hzb_fv, range_zb, body);
        let with_haz = d.lam_fv(haz_fv, range_az, with_hzb);
        d.lam_fv(z_fv, carrier, with_haz)
    };
    let ty = {
        let concl = {
            let iz = d.apply(identity, &[z]);
            let abs_iz = cabs(d, p, iz);
            d.const_app(p.le, &[abs_iz, unit])
        };
        let with_zb = d.arrow(range_zb, concl);
        let with_az = d.arrow(range_az, with_zb);
        d.pi_fv(z_fv, carrier, with_az)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.bounded_on_id_unit,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CReal.uniformly_continuous_poly_example : UniformlyContinuousOn (fun r
/// => add (add (mul r r) r) one) zero (mag_bound 0)` -- the concrete payoff:
/// `x -> x^2 + x + 1` uniformly continuous on `[0,1]` (`mag_bound 0` IS the
/// kernel's own `1`, see [`declare_bounded_on_id_unit`]), assembled from
/// [`declare_uniformly_continuous_sq`], [`declare_uniformly_continuous_id`],
/// [`declare_uniformly_continuous_const`] and
/// [`declare_uniformly_continuous_add`] with EVERY `BoundedOn` hypothesis
/// discharged concretely (both factors of `sq` are `id`, bounded by
/// [`declare_bounded_on_id_unit`]) rather than left universally quantified.
///
/// # Errors
///
/// Returns the trusted gate's rejection.
fn declare_uniformly_continuous_poly_example(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let zero_c = czero(d, p);
    let zero_idx = d.num(0);
    let unit = mag_bound(d, p, zero_idx);
    let one_c = d.kernel().const_(p.one, vec![]);

    let identity = {
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);
        d.lam_fv(r_fv, carrier, r)
    };

    let huc_id = d.lemma(p.uniformly_continuous_id, &[zero_c, unit]);
    let hb_id = d.lemma(p.bounded_on_id_unit, &[]);

    let huc_sq = d.lemma(p.uniformly_continuous_sq, &[zero_c, unit, zero_idx, hb_id]);
    // huc_sq : UniformlyContinuousOn (fun r => mul (id r) (id r)) zero unit

    let sq_fn = {
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);
        let ir = d.apply(identity, &[r]);
        let ir2 = d.apply(identity, &[r]);
        let prod = cmul(d, p, ir, ir2);
        d.lam_fv(r_fv, carrier, prod)
    };

    let huc_sq_plus_id = d.lemma(
        p.uniformly_continuous_add,
        &[sq_fn, identity, zero_c, unit, huc_sq, huc_id],
    );
    // huc_sq_plus_id : UniformlyContinuousOn (fun r => add (sq_fn r) (id r)) zero unit

    let sq_plus_id_fn = {
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);
        let sqr = d.apply(sq_fn, &[r]);
        let ir = d.apply(identity, &[r]);
        let sum = cadd(d, p, sqr, ir);
        d.lam_fv(r_fv, carrier, sum)
    };

    let huc_const_one = d.lemma(p.uniformly_continuous_const, &[one_c, zero_c, unit]);

    let const_one_fn = {
        let r_fv = d.fresh_fvar();
        d.lam_fv(r_fv, carrier, one_c)
    };
    let huc_poly = d.lemma(
        p.uniformly_continuous_add,
        &[
            sq_plus_id_fn,
            const_one_fn,
            zero_c,
            unit,
            huc_sq_plus_id,
            huc_const_one,
        ],
    );
    // huc_poly : UniformlyContinuousOn
    //   (fun r => add (sq_plus_id_fn r) (const_one_fn r)) zero unit

    let poly_fn = {
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);
        let spr = d.apply(sq_plus_id_fn, &[r]);
        let sum = cadd(d, p, spr, one_c);
        d.lam_fv(r_fv, carrier, sum)
    };
    let ty = uc_ty(d, p, poly_fn, zero_c, unit);

    d.kernel().add_declaration(Declaration::Theorem {
        name: p.uniformly_continuous_poly_example,
        uparams: vec![],
        ty,
        value: huc_poly,
    })
}

// --- the running bound over finitely many sample points ---------------------
//
// `CReal.bounded_of_uniformly_continuous` (the boundedness-of-uniformly-
// continuous-functions theorem, not landed here -- see the module
// documentation) needs, at its last step, a SINGLE `Nat` `k` bounding
// `|F(x_i)|` at every one of finitely many sample points `x_0, …, x_N`. Each
// `|F(x_i)|` is bounded by SOME `mag_bound (g i)` (`g` built from
// `CReal.bound`, a total computable projection -- no search), but picking
// the LARGEST of finitely many `Nat`s by comparison is exactly the kind of
// decision `CReal.le` cannot make (`CReal.le` is undecidable; see the module
// documentation's own house rule, echoing `CReal.pos_bound_of_lt`'s). A
// running SUM sidesteps the comparison entirely: a sum of nonnegative reals
// dominates each addend, and nonnegativity of `mag_bound _` is unconditional
// (`mag_bound_nonneg`, below) -- no case split on any two samples' relative
// size is ever needed. This is the finite-sample form of that idea, proved
// once, independent of where the samples come from.

/// `False.rec (fun _ => target) false_proof : target`. Local copy of the
/// identical private helper in `creal/sqrt.rs` (itself a copy of several
/// `nat_prelude` modules' own private `ex_falso`) -- see that copy's own doc
/// comment for the lineage. Reused here rather than threaded across the
/// module boundary, matching this file's existing practice for
/// [`mag_bound`]/[`bounded_on_applied`]/[`rescale_index`] above.
fn ex_falso(d: &mut IntDev<'_>, p: CRealPrelude, target: ExprId, false_proof: ExprId) -> ExprId {
    let anon = d.anon_name();
    let nat_p = p.rat.int.nat;
    let false_ty = d.kernel().const_(nat_p.logic.false_, vec![]);
    let motive = d.kernel().lam(anon, false_ty, target, BinderInfo::Default);
    let level_zero = d.kernel().level_zero();
    let rec = d.kernel().const_(nat_p.logic.false_rec, vec![level_zero]);
    d.apply(rec, &[motive, false_proof])
}

/// `le x (add x w)`, from `hw : le zero w`. Local copy of the identical
/// private helper in `creal/monotone.rs` (`shift_le_of_nonneg`), duplicated
/// for the same file-boundary reason as [`ex_falso`] above.
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
    let padded = cadd(d, p, x, zero_c);
    let target = cadd(d, p, x, w);
    let trim = d.lemma(p.add_zero, &[x]);
    let refl_target = erefl(d, p, target);
    d.lemma(
        p.le_congr,
        &[padded, x, target, target, trim, refl_target, grown],
    )
}

/// `CReal.le CReal.zero (CReal.sumRange f n)`, where `f := fun j => mag_bound
/// (g j)` for the SAME `g` used by [`declare_mag_bound_le_sum_range_of_lt`].
///
/// By induction on `n`: base case `sumRange f 0 ≡ zero` (`Nat.rec`'s own
/// ι-reduction, matching this file's existing convention — see
/// [`declare_mag_bound_le_sum_range_of_lt`]'s own module documentation), so
/// `le_refl zero` closes it directly against the defeq-unfolded goal.
/// Successor case: `sumRange f (Nat.succ m) ≡ add (sumRange f m) (f m)`
/// (again by raw ι-reduction, no named `sumRange_succ` lemma needed); both
/// summands are nonnegative — the accumulated sum by the induction
/// hypothesis, `f m = mag_bound (g m)` by [`mag_bound_nonneg`] — so
/// [`shift_le_of_nonneg`] extends `le zero (sumRange f m)` across the new
/// term and [`CRealPrelude::le_trans`] chains it from `zero`.
///
/// This is the nonnegativity fact `mag_bound_le_sum_range_of_lt`'s own
/// `minor_equal` branch actually needs as its `shift_le_of_nonneg` witness —
/// nonnegativity of the RUNNING SUM `sum_f_m`, not of the single term
/// `mag_gm` being added to it (those are different propositions, and using
/// the latter where the former is required is exactly the `TypeMismatch`
/// this development hit on its first attempt: `shift_le_of_nonneg(d, p, x,
/// w, hw)` needs `hw : le zero w`, and at that call site `x = mag_gm`, `w =
/// sum_f_m`, so `hw` must be nonnegativity of `sum_f_m`).
fn mag_bound_sum_range_nonneg(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    g: ExprId,
    f: ExprId,
    n: ExprId,
) -> ExprId {
    let stmt_at = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let zero_c = czero(d, p);
        let sx = d.const_app(p.sum_range, &[f, x]);
        d.const_app(p.le, &[zero_c, sx])
    };
    d.induct(
        &stmt_at,
        &|d: &mut IntDev<'_>| -> ExprId {
            let zero_c = czero(d, p);
            d.lemma(p.le_refl, &[zero_c])
        },
        &|d: &mut IntDev<'_>, m: ExprId, ih: ExprId| -> ExprId {
            let gm = d.apply(g, &[m]);
            let mag_gm = mag_bound(d, p, gm);
            let sum_f_m = d.const_app(p.sum_range, &[f, m]);
            let nonneg_fm = mag_bound_nonneg(d, p, gm);
            // le sum_f_m (add sum_f_m mag_gm) -- defeq `sumRange f (succ m)`.
            let step = shift_le_of_nonneg(d, p, sum_f_m, mag_gm, nonneg_fm);
            let zero_c = czero(d, p);
            let target = cadd(d, p, sum_f_m, mag_gm);
            d.lemma(p.le_trans, &[zero_c, sum_f_m, target, ih, step])
        },
        n,
    )
}

/// `CReal.mag_bound_le_sum_range_of_lt : ∀ (g : Nat → Nat) (n i : Nat),
/// Nat.lt i n → CReal.le (mag_bound (g i)) (CReal.sumRange (fun j =>
/// mag_bound (g j)) n)`.
///
/// The `CReal`-valued analogue of `Nat.le_sumRange_of_lt`
/// (`nat_prelude/binomial.rs::declare_le_sum_range_of_lt`), whose proof
/// shape this mirrors almost verbatim: induction on `n` with `i`
/// generalized inside the motive, successor case split by
/// `Nat.lt_or_eq_of_le` into a strict branch (extend the outer induction
/// hypothesis past the new boundary term via [`shift_le_of_nonneg`] +
/// `CReal.le_trans`) and an equal branch (rewrite the goal's sample index
/// from `m` to `i` via `Eq Nat i m`, using [`nat_rewrite_prop`] since the
/// rewritten proposition is `Prop`-valued regardless of the `CReal`-typed
/// terms it mentions -- `NatOps::congr`'s own `Eq` is hardcoded to `Nat`
/// and cannot be used to equate two `CReal`s directly).
///
/// The base case (`n = 0`) is vacuous (`Nat.lt i 0` is impossible,
/// `Nat.not_lt_zero`), regardless of what `CReal.sumRange f 0` reduces to.
///
/// Every step relies on `CReal.sumRange f (Nat.succ n) ≡ add (sumRange f n)
/// (f n)` holding by raw `Nat.rec` ι-reduction (`series.rs::sum_range_succ`'s
/// own proof is `Eq.refl` alone, for the same reason) -- the proof below
/// never invokes `sumRange_succ` as a named lemma, exactly as
/// `Nat.le_sumRange_of_lt`'s own proof never invokes `Nat.sumRange_succ`.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` from a `Theorem` here
/// means the kernel **refused** a proof, not that a script gave up.
fn declare_mag_bound_le_sum_range_of_lt(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let nat_p = p.rat.int.nat;
    let g_ty = nat_fn_ty(d);

    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);

    // f := fun j => mag_bound (g j) : Nat -> CReal.
    let f = {
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let gj = d.apply(g, &[j]);
        let mbj = mag_bound(d, p, gj);
        d.lam_fv(j_fv, nat, mbj)
    };

    let stmt_at = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let hyp = d.lt(i, x);
        let gi = d.apply(g, &[i]);
        let mbi = mag_bound(d, p, gi);
        let sx = d.const_app(p.sum_range, &[f, x]);
        let concl = d.const_app(p.le, &[mbi, sx]);
        let body = d.arrow(hyp, concl);
        d.pi_fv(i_fv, nat, body)
    };

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let stmt = stmt_at(d, n);

    let proof = d.induct(
        &stmt_at,
        &|d: &mut IntDev<'_>| -> ExprId {
            let zero_nat = d.num(0);
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let hyp_ty = d.lt(i, zero_nat);
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);

            let not_lt = d.lemma(nat_p.not_lt_zero, &[i]);
            let false_proof = d.apply(not_lt, &[h]);

            let gi = d.apply(g, &[i]);
            let mbi = mag_bound(d, p, gi);
            let sum0 = d.const_app(p.sum_range, &[f, zero_nat]);
            let target = d.const_app(p.le, &[mbi, sum0]);

            let body = ex_falso(d, p, target, false_proof);
            let with_h = d.lam_fv(h_fv, hyp_ty, body);
            d.lam_fv(i_fv, nat, with_h)
        },
        &|d: &mut IntDev<'_>, m: ExprId, ih: ExprId| -> ExprId {
            let sm = d.succ(m);
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let hyp_ty = d.lt(i, sm);
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);

            // Nat.lt i (succ m) is defeq Nat.le (succ i) (succ m); peel to
            // Nat.le i m, then split it.
            let h_le_im = d.lemma(nat_p.le_of_succ_le_succ, &[i, m, h]);
            let split = d.lemma(nat_p.lt_or_eq_of_le, &[i, m, h_le_im]);

            let strict_ty = d.lt(i, m);
            let equal_ty = d.eq(i, m);

            let gm = d.apply(g, &[m]);
            let mag_gm = mag_bound(d, p, gm);
            let sum_f_m = d.const_app(p.sum_range, &[f, m]);
            // add sum_f_m mag_gm -- defeq `sumRange f (succ m)`.
            let lhs2 = cadd(d, p, sum_f_m, mag_gm);

            let gi = d.apply(g, &[i]);
            let mag_gi = mag_bound(d, p, gi);
            let target = d.const_app(p.le, &[mag_gi, lhs2]);

            let minor_strict = {
                let hlt_fv = d.fresh_fvar();
                let hlt = d.kernel().fvar(hlt_fv);
                let ih_i = d.apply(ih, &[i, hlt]); // le mag_gi sum_f_m
                let nonneg_gm = mag_bound_nonneg(d, p, gm);
                let ext = shift_le_of_nonneg(d, p, sum_f_m, mag_gm, nonneg_gm); // le sum_f_m lhs2
                let body = d.lemma(p.le_trans, &[mag_gi, sum_f_m, lhs2, ih_i, ext]);
                d.lam_fv(hlt_fv, strict_ty, body)
            };
            let minor_equal = {
                let heq_fv = d.fresh_fvar();
                let heq = d.kernel().fvar(heq_fv);
                let sym_heq = d.symm(i, m, heq); // Eq Nat m i

                let nonneg_sum_f_m = mag_bound_sum_range_nonneg(d, p, g, f, m);
                // le mag_gm (add mag_gm sum_f_m)
                let h1 = shift_le_of_nonneg(d, p, mag_gm, sum_f_m, nonneg_sum_f_m);
                let lhs1 = cadd(d, p, mag_gm, sum_f_m);
                let hcomm = d.lemma(p.add_comm, &[mag_gm, sum_f_m]); // Equiv lhs1 lhs2
                let refl_magm = erefl(d, p, mag_gm);
                // le mag_gm lhs2
                let h2 = d.lemma(
                    p.le_congr,
                    &[mag_gm, mag_gm, lhs1, lhs2, refl_magm, hcomm, h1],
                );

                let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
                    let gx = d.apply(g, &[x]);
                    let mbx = mag_bound(d, p, gx);
                    d.const_app(p.le, &[mbx, lhs2])
                };
                let body = nat_rewrite_prop(d, m, i, sym_heq, h2, &motive);
                d.lam_fv(heq_fv, equal_ty, body)
            };

            let selected = d.const_app(
                nat_p.logic.or_elim,
                &[
                    strict_ty,
                    equal_ty,
                    target,
                    split,
                    minor_strict,
                    minor_equal,
                ],
            );
            let with_h = d.lam_fv(h_fv, hyp_ty, selected);
            d.lam_fv(i_fv, nat, with_h)
        },
        n,
    );

    let ty = {
        let over_n = d.pi_fv(n_fv, nat, stmt);
        d.pi_fv(g_fv, g_ty, over_n)
    };
    let value = {
        let over_n = d.lam_fv(n_fv, nat, proof);
        d.lam_fv(g_fv, g_ty, over_n)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.mag_bound_le_sum_range_of_lt,
        uparams: vec![],
        ty,
        value,
    })
}

/// Admit `CReal.mag_bound_le_sum_range_of_lt`. A THIRD entry point (after
/// [`declare_uniform_continuity`] and [`declare_uniform_continuity_products`])
/// because it consumes `CReal.sumRange`, which `series::declare_series`
/// declares after both of those -- see `creal.rs`'s own wiring comment at
/// the call site.
///
/// # Errors
///
/// Returns the trusted gate's rejection.
pub(super) fn declare_uniform_continuity_sums(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    declare_mag_bound_le_sum_range_of_lt(d, p)
}
