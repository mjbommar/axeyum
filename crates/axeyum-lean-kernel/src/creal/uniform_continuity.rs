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
//! `modulus`, ordinary elimination for `spec`), and two witnesses (`id`
//! and `const`) that show the predicate is not vacuous. **Not landed:
//! scalar multiplication `fun r => a * r`, and the theorem tying
//! `UniformlyContinuousOn` back to `ContinuousAt`.** Both were attempted;
//! neither is force-fit, for concrete, verified reasons recorded here
//! rather than gestured at.
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

use super::{CRealPrelude, creal_ty};
use crate::BinderInfo;
use crate::KernelError;
use crate::env::{Declaration, ReducibilityHint};
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::nat_prelude::NatOps;
use crate::rat_prelude::ops::rat_eq_rewrite;

/// Admit `CReal.UniformlyContinuousOn` (the carrier and its two
/// projections) and two witnesses: `id` and `const`. See the module
/// documentation for why a third witness (scalar multiplication) and the
/// bridge to `ContinuousAt` are not landed here.
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
    declare_uniformly_continuous_const(d, p)
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
