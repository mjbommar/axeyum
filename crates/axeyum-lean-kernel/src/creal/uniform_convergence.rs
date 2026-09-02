//! **Uniform convergence of a sequence of functions** (Spivak Ch24), and the
//! gateway power series need.
//!
//! ## Why `UniformConvergesOn` is `Type`-valued, not `Exists`-wrapped `Prop`
//!
//! ```text
//! CReal.UniformConvergesOn (F : Nat → CReal → CReal) (G : CReal → CReal)
//!                          (a b : CReal) : Type :=
//!   mk (rate : Nat)
//!      (spec : ∀ (n : Nat) (x : CReal), le a x → le x b →
//!              close_within (F n x) (G x) (Rat.natDivSucc rate n))
//! ```
//!
//! `CReal.Converges`/`CReal.Cauchy`/`CReal.Bounded`
//! ([`super::convergence`]) are all `Prop`-valued, `∃ K, …` — and that is
//! the RIGHT choice there, because every consumer of those predicates proves
//! another `Prop` from them (`Exists.rec` eliminating into `Prop` is always
//! legal, witness and all). `CReal.UniformlyContinuousOn`
//! ([`super::uniform_continuity`]) is `Type`-valued instead, for a reason
//! that file's own module documentation states explicitly: a later
//! construction needs the modulus as `Nat → Nat` **data**, and `Exists.rec`'s
//! motive must not depend on the witness when the target is a `Type` — so an
//! `∃ modulus, …` cannot be eliminated into a NEW `Nat → Nat` term at all.
//!
//! `UniformConvergesOn` hits exactly that second case, not the first. The
//! theorem this file builds toward — the uniform limit of uniformly
//! continuous functions is uniformly continuous — must **construct** a new
//! `UniformlyContinuousOn G a b` value, and that value's own `modulus` field
//! is computed FROM the uniform-convergence rate (`modulus_G(n)` folds in
//! `F`'s rate to choose how deep into the sequence to look before consulting
//! `F`'s own modulus at that index). A `Nat` extracted from a `Prop`-wrapped
//! `∃ rate, …` cannot be used to build that `Nat → Nat` term — the same
//! `Exists.rec`-into-`Type` wall, one constructor over. So `rate` is a
//! genuine data field here too, following `UniformlyContinuousOn`'s own
//! one-constructor-`Type` shape rather than `Converges`'s `Exists`, even
//! though `UniformConvergesOn` is otherwise much closer in spirit to
//! `Converges` (a `Nat`-indexed family approaching a limit, not an
//! epsilon-delta relation between two points).
//!
//! `rate` is a single `Nat`, not a `Nat → Nat` modulus function like
//! `UniformlyContinuousOn`'s: the canonical-sample idiom `Converges`/`Cauchy`
//! use (compare at the function's OWN index `n`, bound by `rate/(n+1)`,
//! never a second accuracy parameter) already gives a rate that shrinks in
//! `n`, so no separate accuracy-to-index modulus is needed — matching
//! `CReal.Converges`'s own idiom for `spec`'s SHAPE while needing
//! `UniformlyContinuousOn`'s idiom for `rate`'s SORT.
//!
//! The domain `a b : CReal` mirrors `UniformlyContinuousOn`'s own compact
//! interval, deliberately: the discriminating case for this chapter (uniform
//! vs. merely pointwise convergence) needs SOME notion of "uniform in x
//! over WHAT" and `[a, b]` is the shape every other continuity-flavoured
//! predicate in this development already carries.
//!
//! ## What this file lands
//!
//! 1. The definition above, with projections `rate`/`spec` (mirroring
//!    `UniformlyContinuousOn.modulus`/`.spec`'s own large-elimination
//!    projections one field simpler).
//! 2. A concrete, non-degenerate instantiation: `F n x := x` converges
//!    uniformly to `id` on any `[a, b]`, at `rate := 1` — a genuine
//!    (if minimal) exercise of the definition, not merely its statement.
//!
//! **Not landed**: the chapter's headline theorem, "the uniform limit of
//! (uniformly) continuous functions is (uniformly) continuous". The module
//! documentation for `order_extra.rs`'s new `CReal.neg_sub_swap`/
//! `CReal.abs_le_of_two_sided` (added FOR this theorem) and the doc comment
//! on [`declare_uniform_converges_on`] below both describe the fully worked
//! out ε/3 route this theorem needs: pick, at target accuracy `n`, a
//! function-index `N` deep enough that `F`'s own uniform-convergence rate
//! contributes at most `1/(3(n+1))` on EACH side (via `Rat.natDivSucc_scale`
//! + `Rat.natDivSucc_le_add_left`, the same pattern
//!   [`super::convergence::converges_comp_eventually`]'s own doc flags as
//!   necessary and which this file's sibling lemmas make available), consult
//!   `F_N`'s own `UniformlyContinuousOn` modulus at that SAME split accuracy
//!   for the middle term, and combine the three `close_within` legs via
//!   `CReal.abs_le_of_two_sided`. Every piece of that route is now in place
//!   (`neg_sub_swap`, `abs_le_of_two_sided`, and this file's own
//!   [`declare_uniform_converges_on`]/projections); what remains is the
//!   Rust-level assembly of roughly a dozen more `le_congr`/`add_le_add`/
//!   `add_assoc` steps mirroring `convergence.rs`'s own `shifted_bound_at`/
//!   `close_within_of_sample_bound` in scale, which a later slice can complete
//!   without re-deriving anything above it.

use crate::KernelError;
use crate::NatOps;
use crate::env::{Declaration, ReducibilityHint};
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::rat_prelude::group::{rsub, rsum, rsum_append, rsum_perm};
use crate::rat_prelude::ops::{
    nat_eq_to_rat, nat_rewrite_prop, radd, rat_eq_rewrite, rchain, rcongr, rle, rneg, rsymm, rzero,
};

use super::convergence::{
    converges_applied, converges_predicate, exists_intro, kregular_of_cauchy_proof,
};
use super::derivative::{
    abs_le_of_equiv, cabs, cadd, cancel_middle, cmul, cneg, czero, echain, erefl, esymm, hd_ty,
    neg_mul_equiv_left, swap_middle_pair,
};
use super::ring_helpers::{add4_comm, right_distrib};
use super::series::within_symm;
use super::{CRealPrelude, creal_ty, div_succ, embed, halves, modulus, sample, within};

// --- shared term builders ----------------------------------------------------

/// `Nat → CReal → CReal`.
fn seq_fn_ty(d: &mut IntDev<'_>, p: CRealPrelude) -> ExprId {
    let nat = d.nat_ty();
    let carrier = creal_ty(d, p);
    let inner = d.arrow(carrier, carrier);
    d.arrow(nat, inner)
}

/// `CReal → CReal`.
fn fn_ty(d: &mut IntDev<'_>, p: CRealPrelude) -> ExprId {
    let carrier = creal_ty(d, p);
    d.arrow(carrier, carrier)
}

/// `Rat.natDivSucc k j`, with a **symbolic** `Nat` numerator `k`. A private
/// copy of `convergence.rs`'s/`uniform_continuity.rs`'s own `div_succ_at`
/// (Rust privacy: each is a sibling module).
fn div_succ_at(d: &mut IntDev<'_>, p: CRealPrelude, k: ExprId, j: ExprId) -> ExprId {
    d.const_app(p.rat.nat_div_succ, &[k, j])
}

/// `CReal.le (CReal.abs (CReal.add x (CReal.neg y))) (CReal.ofRat q)` — a
/// private copy of `convergence.rs`'s/`uniform_continuity.rs`'s own
/// `close_within`.
fn close_within(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId, y: ExprId, q: ExprId) -> ExprId {
    let ny = d.const_app(p.neg, &[y]);
    let diff = d.const_app(p.add, &[x, ny]);
    let magnitude = d.const_app(p.abs, &[diff]);
    let target = d.const_app(p.of_rat, &[q]);
    d.const_app(p.le, &[magnitude, target])
}

/// `CReal.UniformConvergesOn F G a b`.
fn uconv_ty(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    f: ExprId,
    g: ExprId,
    a: ExprId,
    b: ExprId,
) -> ExprId {
    d.const_app(p.uniform_converges_on, &[f, g, a, b])
}

/// `∀ (n : Nat) (x : CReal), le a x → le x b →
///   close_within (F n x) (G x) (natDivSucc rate n)`.
fn uconv_spec_body(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    big_f: ExprId,
    big_g: ExprId,
    a: ExprId,
    b: ExprId,
    rate: ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let carrier = creal_ty(d, p);

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);

    let fnx = d.apply(big_f, &[n, x]);
    let gx = d.apply(big_g, &[x]);
    let bound = div_succ_at(d, p, rate, n);
    let claim = close_within(d, p, fnx, gx, bound);

    let range_ax = d.const_app(p.le, &[a, x]);
    let range_xb = d.const_app(p.le, &[x, b]);
    let with_hxb = d.arrow(range_xb, claim);
    let with_hax = d.arrow(range_ax, with_hxb);
    let with_x = d.pi_fv(x_fv, carrier, with_hax);
    d.pi_fv(n_fv, nat, with_x)
}

// --- the carrier --------------------------------------------------------------

/// `CReal.UniformConvergesOn (F : Nat → CReal → CReal) (G : CReal → CReal)
/// (a b : CReal) : Type := mk (rate : Nat) (spec : …)`.
///
/// A one-constructor inductive with FOUR leading parameters (`F, G, a, b`),
/// copying `CReal.UniformlyContinuousOn`'s own shape one field simpler (a
/// bare `Nat` data field rather than `Nat → Nat`) — see the module
/// documentation for why the data field, and not an `Exists`, is the
/// deliberate choice here.
fn declare_carrier(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let seq_ty = seq_fn_ty(d, p);
    let func_ty = fn_ty(d, p);
    let one = d.level_one();
    let type0 = d.kernel().sort(one);
    let nat = d.nat_ty();

    let ty = {
        let f_fv = d.fresh_fvar();
        let g_fv = d.fresh_fvar();
        let a_fv = d.fresh_fvar();
        let b_fv = d.fresh_fvar();
        let with_b = d.pi_fv(b_fv, carrier, type0);
        let with_a = d.pi_fv(a_fv, carrier, with_b);
        let with_g = d.pi_fv(g_fv, func_ty, with_a);
        d.pi_fv(f_fv, seq_ty, with_g)
    };

    let mk_ty = {
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let g_fv = d.fresh_fvar();
        let g = d.kernel().fvar(g_fv);
        let a_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let b_fv = d.fresh_fvar();
        let b = d.kernel().fvar(b_fv);
        let rate_fv = d.fresh_fvar();
        let rate = d.kernel().fvar(rate_fv);

        let spec_ty = uconv_spec_body(d, p, f, g, a, b, rate);
        let result = uconv_ty(d, p, f, g, a, b);
        let with_spec = d.arrow(spec_ty, result);
        let with_rate = d.pi_fv(rate_fv, nat, with_spec);
        let with_b = d.pi_fv(b_fv, carrier, with_rate);
        let with_a = d.pi_fv(a_fv, carrier, with_b);
        let with_g = d.pi_fv(g_fv, func_ty, with_a);
        d.pi_fv(f_fv, seq_ty, with_g)
    };

    d.kernel()
        .add_inductive(p.uniform_converges_on, &[], 4, ty, &[(p.uconv_mk, mk_ty)])
}

/// The two projections: `rate` (large elimination, into `Nat`, i.e. `Type
/// 0`) and `spec` (into `Prop`, motive at a witness `u` mentioning `u`'s OWN
/// rate) — mirroring exactly how `uniform_continuity.rs`'s
/// `declare_projections` projects `UniformlyContinuousOn.modulus`/`.spec`.
fn declare_projections(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let seq_ty = seq_fn_ty(d, p);
    let func_ty = fn_ty(d, p);
    let nat = d.nat_ty();
    let one = d.level_one();
    let zero_level = d.kernel().level_zero();
    let anon = d.anon_name();

    // rate : ∀ F G a b, UniformConvergesOn F G a b → Nat.
    {
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let g_fv = d.fresh_fvar();
        let g = d.kernel().fvar(g_fv);
        let a_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let b_fv = d.fresh_fvar();
        let b = d.kernel().fvar(b_fv);
        let carrier_uc = uconv_ty(d, p, f, g, a, b);

        let motive = d
            .kernel()
            .lam(anon, carrier_uc, nat, crate::BinderInfo::Default);
        let minor = {
            let rate_fv = d.fresh_fvar();
            let rate = d.kernel().fvar(rate_fv);
            let spec_ty = uconv_spec_body(d, p, f, g, a, b, rate);
            let inner = d
                .kernel()
                .lam(anon, spec_ty, rate, crate::BinderInfo::Default);
            d.lam_fv(rate_fv, nat, inner)
        };
        let u_fv = d.fresh_fvar();
        let u = d.kernel().fvar(u_fv);
        let rec = d.kernel().const_(p.uconv_rec, vec![one]);
        let body = d.apply(rec, &[f, g, a, b, motive, minor, u]);
        let value = {
            let with_u = d.lam_fv(u_fv, carrier_uc, body);
            let with_b = d.lam_fv(b_fv, carrier, with_u);
            let with_a = d.lam_fv(a_fv, carrier, with_b);
            let with_g = d.lam_fv(g_fv, func_ty, with_a);
            d.lam_fv(f_fv, seq_ty, with_g)
        };
        let ty = {
            let with_u = d.arrow(carrier_uc, nat);
            let with_b = d.pi_fv(b_fv, carrier, with_u);
            let with_a = d.pi_fv(a_fv, carrier, with_b);
            let with_g = d.pi_fv(g_fv, func_ty, with_a);
            d.pi_fv(f_fv, seq_ty, with_g)
        };
        d.kernel().add_declaration(Declaration::Definition {
            name: p.uconv_rate,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(super::DERIVED_HEIGHT + 41),
        })?;
    }

    // spec : ∀ F G a b (u : UniformConvergesOn F G a b),
    //   uconv_spec_body F G a b (rate F G a b u).
    {
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let g_fv = d.fresh_fvar();
        let g = d.kernel().fvar(g_fv);
        let a_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let b_fv = d.fresh_fvar();
        let b = d.kernel().fvar(b_fv);
        let carrier_uc = uconv_ty(d, p, f, g, a, b);

        let claim = |d: &mut IntDev<'_>, w: ExprId| {
            let rate_of_w = d.const_app(p.uconv_rate, &[f, g, a, b, w]);
            uconv_spec_body(d, p, f, g, a, b, rate_of_w)
        };

        let motive = {
            let w_fv = d.fresh_fvar();
            let w = d.kernel().fvar(w_fv);
            let body = claim(d, w);
            d.lam_fv(w_fv, carrier_uc, body)
        };
        let minor = {
            let rate_fv = d.fresh_fvar();
            let rate = d.kernel().fvar(rate_fv);
            let spec_ty = uconv_spec_body(d, p, f, g, a, b, rate);
            let spec_fv = d.fresh_fvar();
            let spec_var = d.kernel().fvar(spec_fv);
            let inner = d.lam_fv(spec_fv, spec_ty, spec_var);
            d.lam_fv(rate_fv, nat, inner)
        };
        let u_fv = d.fresh_fvar();
        let u = d.kernel().fvar(u_fv);
        let rec = d.kernel().const_(p.uconv_rec, vec![zero_level]);
        let body = d.apply(rec, &[f, g, a, b, motive, minor, u]);
        let value = {
            let with_u = d.lam_fv(u_fv, carrier_uc, body);
            let with_b = d.lam_fv(b_fv, carrier, with_u);
            let with_a = d.lam_fv(a_fv, carrier, with_b);
            let with_g = d.lam_fv(g_fv, func_ty, with_a);
            d.lam_fv(f_fv, seq_ty, with_g)
        };
        let ty = {
            let inner = claim(d, u);
            let with_u = d.pi_fv(u_fv, carrier_uc, inner);
            let with_b = d.pi_fv(b_fv, carrier, with_u);
            let with_a = d.pi_fv(a_fv, carrier, with_b);
            let with_g = d.pi_fv(g_fv, func_ty, with_a);
            d.pi_fv(f_fv, seq_ty, with_g)
        };
        d.kernel().add_declaration(Declaration::Theorem {
            name: p.uconv_spec,
            uparams: vec![],
            ty,
            value,
        })?;
    }
    Ok(())
}

// --- witness: `id` -------------------------------------------------------------

/// `CReal.uniform_converges_id : ∀ a b, UniformConvergesOn (fun n x => x)
/// (fun x => x) a b`.
///
/// The cheapest witness, and the "F n x := x (constant in n) converges
/// uniformly to id" instance the task brief names: `F n x − G x` is
/// EXACTLY zero for every `n, x` (no index-dependent decay needed), so
/// `rate := 1` (any rate works; `1` is used since `Rat.zero_le_natDivSucc`
/// already gives `0 ≤ natDivSucc 1 n` directly) closes the spec once
/// `abs (add x (neg x))` is shown `Equiv`-zero — via `CReal.add_neg` and the
/// two-step "`abs zero ~ zero`" identity (`neg zero ~ zero` from
/// `add_neg`/`add_comm`/`add_zero`, then `max zero (neg zero) ~ max zero
/// zero ~ zero`).
fn declare_uniform_converges_id(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let rat = p.rat;
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let zero = d.kernel().const_(p.zero, vec![]);

    // neg_zero_equiv : Equiv (neg zero) zero.
    let neg_zero_equiv = {
        let nz = d.const_app(p.neg, &[zero]);
        let zero_nz = d.const_app(p.add, &[zero, nz]);
        let nz_zero = d.const_app(p.add, &[nz, zero]);
        let comm = d.lemma(p.add_comm, &[zero, nz]); // Equiv zero_nz nz_zero
        let az = d.lemma(p.add_zero, &[nz]); // Equiv nz_zero nz
        let step1 = d.lemma(p.equiv_trans, &[zero_nz, nz_zero, nz, comm, az]);
        // step1 : Equiv zero_nz nz
        let step1_symm = d.lemma(p.equiv_symm, &[zero_nz, nz, step1]); // Equiv nz zero_nz
        let step2 = d.lemma(p.add_neg, &[zero]); // Equiv zero_nz zero
        d.lemma(p.equiv_trans, &[nz, zero_nz, zero, step1_symm, step2])
    };

    // abs_zero_equiv : Equiv (abs zero) zero.
    let abs_zero_equiv = {
        let nz = d.const_app(p.neg, &[zero]);
        let abs_zero = d.const_app(p.max, &[zero, nz]);
        let zz = d.const_app(p.max, &[zero, zero]);
        let refl_zero = d.lemma(p.equiv_refl, &[zero]);
        let step1 = d.lemma(
            p.max_congr,
            &[zero, zero, nz, zero, refl_zero, neg_zero_equiv],
        );
        // step1 : Equiv abs_zero zz
        let le1 = d.lemma(p.le_max_left, &[zero, zero]); // le zero zz
        let refl_z = d.lemma(p.le_refl, &[zero]);
        let le2 = d.lemma(p.max_le, &[zero, zero, zero, refl_z, refl_z]); // le zz zero
        let step2 = d.lemma(p.equiv_of_le_le, &[zz, zero, le2, le1]); // Equiv zz zero
        d.lemma(p.equiv_trans, &[abs_zero, zz, zero, step1, step2])
    };

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);

    let identity = {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        d.lam_fv(x_fv, carrier, x)
    };
    let seq_identity = {
        let n_fv = d.fresh_fvar();
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let inner = d.lam_fv(x_fv, carrier, x);
        d.lam_fv(n_fv, nat, inner)
    };

    let one_nat = d.num(1);
    let spec = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let hax_fv = d.fresh_fvar();
        let hxb_fv = d.fresh_fvar();

        let nx = d.const_app(p.neg, &[x]);
        let diff = d.const_app(p.add, &[x, nx]);
        let diff_zero = d.lemma(p.add_neg, &[x]); // Equiv diff zero
        let abs_diff = d.const_app(p.abs, &[diff]);
        let abs_zero = d.const_app(p.abs, &[zero]);
        let diff_abs_congr = d.lemma(p.abs_congr, &[diff, zero, diff_zero]);
        // diff_abs_congr : Equiv abs_diff abs_zero
        let abs_diff_zero = d.lemma(
            p.equiv_trans,
            &[abs_diff, abs_zero, zero, diff_abs_congr, abs_zero_equiv],
        );
        // abs_diff_zero : Equiv abs_diff zero
        let abs_diff_le_zero = d.lemma(p.le_of_equiv, &[abs_diff, zero, abs_diff_zero]);
        // abs_diff_le_zero : le abs_diff zero

        let bound = div_succ_at(d, p, one_nat, n);
        let bound_real = d.const_app(p.of_rat, &[bound]);
        let rat_zero = d.kernel().const_(rat.zero, vec![]);
        let zero_le_bound = d.lemma(rat.zero_le_nat_div_succ, &[one_nat, n]); // Rat.le rat_zero bound
        let zero_real_le_bound_real = d.lemma(p.of_rat_le, &[rat_zero, bound, zero_le_bound]);
        // zero_real_le_bound_real : CReal.le (ofRat rat_zero) bound_real,
        // and `ofRat rat_zero` is defeq to `zero` (CReal.zero's own Definition).
        let body = d.lemma(
            p.le_trans,
            &[
                abs_diff,
                zero,
                bound_real,
                abs_diff_le_zero,
                zero_real_le_bound_real,
            ],
        );

        let with_h = body;
        let range_xb = d.const_app(p.le, &[x, b]);
        let range_ax = d.const_app(p.le, &[a, x]);
        let with_hxb = d.lam_fv(hxb_fv, range_xb, with_h);
        let with_hax = d.lam_fv(hax_fv, range_ax, with_hxb);
        let with_x = d.lam_fv(x_fv, carrier, with_hax);
        d.lam_fv(n_fv, nat, with_x)
    };

    let mk_applied = d.const_app(p.uconv_mk, &[seq_identity, identity, a, b, one_nat, spec]);
    let value = {
        let with_b = d.lam_fv(b_fv, carrier, mk_applied);
        d.lam_fv(a_fv, carrier, with_b)
    };
    let ty = {
        let applied = uconv_ty(d, p, seq_identity, identity, a, b);
        let with_b = d.pi_fv(b_fv, carrier, applied);
        d.pi_fv(a_fv, carrier, with_b)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.uniform_converges_id,
        uparams: vec![],
        ty,
        value,
    })
}

/// `Equiv (neg zero) zero` — shared by [`declare_uniform_converges_id`] and
/// [`declare_uniform_converges_geom_half`].
fn neg_zero_equiv(d: &mut IntDev<'_>, p: CRealPrelude) -> ExprId {
    let zero = d.kernel().const_(p.zero, vec![]);
    let nz = d.const_app(p.neg, &[zero]);
    let zero_nz = d.const_app(p.add, &[zero, nz]);
    let nz_zero = d.const_app(p.add, &[nz, zero]);
    let comm = d.lemma(p.add_comm, &[zero, nz]); // Equiv zero_nz nz_zero
    let az = d.lemma(p.add_zero, &[nz]); // Equiv nz_zero nz
    let step1 = d.lemma(p.equiv_trans, &[zero_nz, nz_zero, nz, comm, az]);
    let step1_symm = d.lemma(p.equiv_symm, &[zero_nz, nz, step1]); // Equiv nz zero_nz
    let step2 = d.lemma(p.add_neg, &[zero]); // Equiv zero_nz zero
    d.lemma(p.equiv_trans, &[nz, zero_nz, zero, step1_symm, step2])
}

/// `CReal.uniform_converges_geom_half : UniformConvergesOn (fun n x => mul x
/// (pow half n)) (fun _ => zero) zero one`.
///
/// The task brief's SECOND concrete instance: `F n x := x · (1/2)^n`
/// converges uniformly to the constant `0` on `[0, 1]`, and — unlike
/// [`declare_uniform_converges_id`] — the two sides are genuinely different
/// values for every `n`. `rate := 1` closes it exactly, with no weakening
/// step: `0 ≤ x ≤ 1` and `0 ≤ (1/2)^n` give `0 ≤ x·(1/2)^n ≤ (1/2)^n`
/// ([`CRealPrelude::mul_nonneg`]/`mul_le_mul_of_nonneg_left` after a
/// `mul_comm`/`mul_one` rearrangement to multiply on the right), so
/// `abs(x·(1/2)^n) ≤ (1/2)^n` (`CReal.abs_le`), and
/// [`CRealPrelude::pow_half_le_nat_div_succ`] bounds `(1/2)^n` by EXACTLY
/// `natDivSucc 1 n` already.
fn declare_uniform_converges_geom_half(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let zero = d.kernel().const_(p.zero, vec![]);
    let one = d.kernel().const_(p.one, vec![]);
    let half = super::exponential::half(d, p);
    let half_rat = super::exponential::half_rat(d, p);
    let one_nat = d.num(1);

    // half_nonneg : le zero half, via `Rat.zero_le_natDivSucc 1 1` and
    // `CReal.ofRat_le` -- the same one-line route `exponential.rs`'s own
    // private `half_nonneg_proof` uses (reproduced, not widened: a lane's
    // own precedent for this exact fact, one line).
    let half_nonneg = {
        let zero_rat = d.kernel().const_(p.rat.zero, vec![]);
        let half_le = d.lemma(p.rat.zero_le_nat_div_succ, &[one_nat, one_nat]);
        d.lemma(p.of_rat_le, &[zero_rat, half_rat, half_le])
    };

    let seq_fn = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let pow_half_n = d.const_app(p.pow, &[half, n]);
        let w = d.const_app(p.mul, &[x, pow_half_n]);
        let inner = d.lam_fv(x_fv, carrier, w);
        d.lam_fv(n_fv, nat, inner)
    };
    let const_zero = {
        let x_fv = d.fresh_fvar();
        d.lam_fv(x_fv, carrier, zero)
    };

    let neg_zero_eq = neg_zero_equiv(d, p);

    let spec = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let hax_fv = d.fresh_fvar();
        let hax = d.kernel().fvar(hax_fv);
        let hxb_fv = d.fresh_fvar();
        let hxb = d.kernel().fvar(hxb_fv);

        let pow_half_n = d.const_app(p.pow, &[half, n]);
        let w = d.const_app(p.mul, &[x, pow_half_n]);
        let pow_nonneg_n = d.lemma(p.pow_nonneg, &[half, half_nonneg, n]);
        // pow_nonneg_n : le zero pow_half_n

        // w_nonneg : le zero w.
        let w_nonneg = d.lemma(p.mul_nonneg, &[x, pow_half_n, hax, pow_nonneg_n]);

        // w_le_pow : le w pow_half_n, via `mul_le_mul_of_nonneg_left` on the
        // LEFT factor `pow_half_n` (nonneg) and `hxb : le x one`, then
        // `mul_comm`/`mul_one` to read the result back at `w`.
        let mul_cx = d.const_app(p.mul, &[pow_half_n, x]);
        let mul_c1 = d.const_app(p.mul, &[pow_half_n, one]);
        let left_bound = d.lemma(
            p.mul_le_mul_of_nonneg_left,
            &[pow_half_n, x, one, pow_nonneg_n, hxb],
        );
        // left_bound : le mul_cx mul_c1
        let comm1 = d.lemma(p.mul_comm, &[x, pow_half_n]); // Equiv w mul_cx
        let comm1_symm = d.lemma(p.equiv_symm, &[w, mul_cx, comm1]); // Equiv mul_cx w
        let refl_mul_c1 = d.lemma(p.equiv_refl, &[mul_c1]);
        let step1 = d.lemma(
            p.le_congr,
            &[
                mul_cx,
                w,
                mul_c1,
                mul_c1,
                comm1_symm,
                refl_mul_c1,
                left_bound,
            ],
        );
        // step1 : le w mul_c1
        let mul_one_eq = d.lemma(p.mul_one, &[pow_half_n]); // Equiv mul_c1 pow_half_n
        let refl_w_v1 = d.lemma(p.equiv_refl, &[w]);
        let w_le_pow = d.lemma(
            p.le_congr,
            &[w, w, mul_c1, pow_half_n, refl_w_v1, mul_one_eq, step1],
        );
        // w_le_pow : le w pow_half_n

        // neg_w_le_pow : le (neg w) pow_half_n, via `0 ≤ w -> neg w ≤ neg
        // zero ~ zero ≤ pow_half_n`.
        let neg_w = d.const_app(p.neg, &[w]);
        let neg_zero = d.const_app(p.neg, &[zero]);
        let neg_w_le_neg_zero = d.lemma(p.neg_le_neg, &[zero, w, w_nonneg]);
        // neg_w_le_neg_zero : le neg_w neg_zero
        let refl_neg_w = d.lemma(p.equiv_refl, &[neg_w]);
        let neg_w_le_zero = d.lemma(
            p.le_congr,
            &[
                neg_w,
                neg_w,
                neg_zero,
                zero,
                refl_neg_w,
                neg_zero_eq,
                neg_w_le_neg_zero,
            ],
        );
        let neg_w_le_pow = d.lemma(
            p.le_trans,
            &[neg_w, zero, pow_half_n, neg_w_le_zero, pow_nonneg_n],
        );

        let abs_w_bound = d.lemma(p.abs_le, &[w, pow_half_n, w_le_pow, neg_w_le_pow]);
        // abs_w_bound : le (abs w) pow_half_n

        let final_n_bound = div_succ_at(d, p, one_nat, n);
        let pow_half_le_nd = d.lemma(p.pow_half_le_nat_div_succ, &[n]);
        // pow_half_le_nd : le pow_half_n (ofRat final_n_bound)
        let final_n_bound_real = d.const_app(p.of_rat, &[final_n_bound]);
        let abs_w = d.const_app(p.abs, &[w]);
        let abs_w_final = d.lemma(
            p.le_trans,
            &[
                abs_w,
                pow_half_n,
                final_n_bound_real,
                abs_w_bound,
                pow_half_le_nd,
            ],
        );
        // abs_w_final : le (abs w) (ofRat final_n_bound)

        // Relate `close_within w zero (natDivSucc 1 n)`, i.e.
        // `le (abs (add w (neg zero))) (ofRat final_n_bound)`, to
        // `abs_w_final` via `add w (neg zero) ~ w`.
        let w_plus_negzero = d.const_app(p.add, &[w, neg_zero]);
        let refl_w_v2 = d.lemma(p.equiv_refl, &[w]);
        let step_a = d.lemma(p.add_congr, &[w, w, neg_zero, zero, refl_w_v2, neg_zero_eq]);
        // step_a : Equiv w_plus_negzero (add w zero)
        let w_plus_zero = d.const_app(p.add, &[w, zero]);
        let step_b = d.lemma(p.add_zero, &[w]); // Equiv w_plus_zero w
        let chain_w = d.lemma(
            p.equiv_trans,
            &[w_plus_negzero, w_plus_zero, w, step_a, step_b],
        );
        // chain_w : Equiv w_plus_negzero w
        let abs_congr_step = d.lemma(p.abs_congr, &[w_plus_negzero, w, chain_w]);
        // abs_congr_step : Equiv (abs w_plus_negzero) (abs w)
        let abs_w_plus_negzero = d.const_app(p.abs, &[w_plus_negzero]);
        let abs_congr_symm = d.lemma(p.equiv_symm, &[abs_w_plus_negzero, abs_w, abs_congr_step]);
        let refl_final_n_bound = d.lemma(p.equiv_refl, &[final_n_bound_real]);
        let final_close = d.lemma(
            p.le_congr,
            &[
                abs_w,
                abs_w_plus_negzero,
                final_n_bound_real,
                final_n_bound_real,
                abs_congr_symm,
                refl_final_n_bound,
                abs_w_final,
            ],
        );
        // final_close : le (abs w_plus_negzero) (ofRat final_n_bound)
        //             = close_within w zero (natDivSucc 1 n)

        let with_h = final_close;
        let range_xb = d.const_app(p.le, &[x, one]);
        let range_ax = d.const_app(p.le, &[zero, x]);
        let with_hxb = d.lam_fv(hxb_fv, range_xb, with_h);
        let with_hax = d.lam_fv(hax_fv, range_ax, with_hxb);
        let with_x = d.lam_fv(x_fv, carrier, with_hax);
        d.lam_fv(n_fv, nat, with_x)
    };

    let mk_applied = d.const_app(p.uconv_mk, &[seq_fn, const_zero, zero, one, one_nat, spec]);
    let ty = uconv_ty(d, p, seq_fn, const_zero, zero, one);
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.uniform_converges_geom_half,
        uparams: vec![],
        ty,
        value: mk_applied,
    })
}

/// Admit `CReal.UniformConvergesOn` (the carrier and its two projections)
/// and `CReal.uniform_converges_id`.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` from a `Theorem` here
/// means the kernel **refused** a proof, not that a script gave up.
pub(super) fn declare_uniform_converges_on(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    declare_carrier(d, p)?;
    declare_projections(d, p)?;
    declare_uniform_converges_id(d, p)
}

/// `CReal.uniform_converges_geom_half` — a SECOND entry point, dispatched
/// after `geometric::declare_geometric` in `creal.rs`'s build order (needs
/// `CReal.pow`/`CReal.pow_nonneg` from `power::declare_power` and
/// `CReal.pow_half_le_nat_div_succ` from `geometric::declare_geometric`,
/// both well after this file's own [`declare_uniform_converges_on`]).
///
/// # Errors
///
/// Returns the trusted gate's rejection.
pub(super) fn declare_uniform_converges_geom(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    declare_uniform_converges_geom_half(d, p)
}

// ============================================================================
// Theorem: the uniform limit of uniformly continuous functions is uniformly
// continuous.
// ============================================================================
//
// `∀ F G a b, UniformConvergesOn F G a b → (∀ n, UniformlyContinuousOn (F n)
// a b) → UniformlyContinuousOn G a b`.
//
// The route (ε/3, done properly rather than diagonally — see this file's
// module documentation for why a diagonal `n := m` choice is UNSOUND here,
// the same obstruction `convergence.rs::converges_comp_eventually`'s own
// module doc names for composing `Converges` through `UniformlyContinuousOn`):
// at target accuracy `n`, pick a SINGLE function-index `N` (independent of
// `x, y` — the whole content of "uniform") deep enough that `F`'s uniform
// rate contributes at most `1/(3(n+1))` on EACH side ([`weaken_rate`]), reuse
// the SAME split accuracy to query `F_N`'s own modulus for the middle term,
// and combine the three `close_within` legs via `chain_triangle_upper` +
// `regroup_and_fuse` + `CReal.abs_le_of_two_sided`
// (`creal/order_extra.rs`, added for exactly this theorem).

/// `CReal.UniformlyContinuousOn F a b` — a private copy (Rust privacy) of
/// `uniform_continuity.rs`'s own `uc_ty`.
fn uc_ty(d: &mut IntDev<'_>, p: CRealPrelude, f: ExprId, a: ExprId, b: ExprId) -> ExprId {
    d.const_app(p.uniformly_continuous_on, &[f, a, b])
}

/// From `k target : Nat`, produce `(big_n, proof)` where `big_n := (k+1) *
/// target + k` and `proof : Rat.le (natDivSucc k big_n) (natDivSucc 1
/// target)`.
///
/// `Rat.natDivSucc_scale` reads the deep index `(k+1)*target+k` back to
/// exactly `1/(target+1)` (an equality, at numerator `k+1`); widening the
/// numerator DOWN from `k+1` to `k` first costs one
/// `Rat.natDivSucc_le_add_left`, whose stated numerator `Nat.add k 1` is
/// bridged to `Nat.succ k` (what `nat_div_succ_scale`'s own construction
/// uses) by a bare `Eq.refl` accepted under defeq — `Nat.add` recurses on
/// its RIGHT argument, so `Nat.add k (Nat.succ Nat.zero)` reduces to
/// `Nat.succ k` regardless of `k`.
fn weaken_rate(d: &mut IntDev<'_>, p: CRealPrelude, k: ExprId, target: ExprId) -> (ExprId, ExprId) {
    let rat = p.rat;
    let one_nat = d.num(1);
    let kp = d.succ(k);
    let product = NatOps::mul(d, kp, target);
    let big_n = NatOps::add(d, product, k);

    let add_k1 = NatOps::add(d, k, one_nat);
    let step_num = d.lemma(rat.nat_div_succ_le_add_left, &[k, one_nat, big_n]);
    // step_num : Rat.le (natDivSucc k big_n) (natDivSucc add_k1 big_n)

    let bridge = NatOps::refl(d, add_k1);
    let base_bound = div_succ_at(d, p, k, big_n);
    let widened = nat_rewrite_prop(d, add_k1, kp, bridge, step_num, &|d, t| {
        let bound = div_succ_at(d, p, t, big_n);
        rle(d, rat, base_bound, bound)
    });
    // widened : Rat.le base_bound (natDivSucc kp big_n)

    let eq1 = d.lemma(rat.nat_div_succ_scale, &[k, target]);
    // eq1 : Eq Rat (natDivSucc kp big_n) (natDivSucc 1 target)
    let deep_bound = div_succ_at(d, p, kp, big_n);
    let final_bound = div_succ_at(d, p, one_nat, target);
    let proof = rat_eq_rewrite(d, deep_bound, final_bound, eq1, widened, &|d, t| {
        rle(d, rat, base_bound, t)
    });
    (big_n, proof)
}

/// From `close_within x y q1` and `Rat.le q1 q2`, derive `close_within x y
/// q2` — a private copy of `convergence.rs`'s own `weaken_close_within`.
fn weaken_close_within(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    x: ExprId,
    y: ExprId,
    q1: ExprId,
    q2: ExprId,
    h_close: ExprId,
    h_rat_le: ExprId,
) -> ExprId {
    let ny = d.const_app(p.neg, &[y]);
    let diff = d.const_app(p.add, &[x, ny]);
    let abs_diff = d.const_app(p.abs, &[diff]);
    let e1 = d.const_app(p.of_rat, &[q1]);
    let e2 = d.const_app(p.of_rat, &[q2]);
    let embed_le = d.lemma(p.of_rat_le, &[q1, q2, h_rat_le]);
    d.lemma(p.le_trans, &[abs_diff, e1, e2, h_close, embed_le])
}

/// From `h1 : le p_term (add m_term q)`, `h2 : le m_term (add n_term q)`,
/// `h3 : le n_term (add t_term q)`, derive
/// `le p_term (add (add (add t_term q) q) q)` — a three-leg triangle where
/// every leg costs the SAME bound `q`, by scaling the later legs' bound up
/// (`add_le_add` with `le_refl q`) to match the accumulated depth before
/// combining with `le_trans`.
fn chain_triangle_upper(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    p_term: ExprId,
    m_term: ExprId,
    n_term: ExprId,
    t_term: ExprId,
    q: ExprId,
    h1: ExprId,
    h2: ExprId,
    h3: ExprId,
) -> ExprId {
    let refl_q = d.lemma(p.le_refl, &[q]);

    let m_q = d.const_app(p.add, &[m_term, q]);
    let n_q = d.const_app(p.add, &[n_term, q]);
    let h2s = d.lemma(p.add_le_add, &[m_term, n_q, q, q, h2, refl_q]);
    // h2s : le m_q (add n_q q)
    let n_qq = d.const_app(p.add, &[n_q, q]);
    let c12 = d.lemma(p.le_trans, &[p_term, m_q, n_qq, h1, h2s]);
    // c12 : le p_term n_qq

    let t_q = d.const_app(p.add, &[t_term, q]);
    let h3s = d.lemma(p.add_le_add, &[n_term, t_q, q, q, h3, refl_q]);
    // h3s : le n_q (add t_q q)
    let t_qq = d.const_app(p.add, &[t_q, q]);
    let h3ss = d.lemma(p.add_le_add, &[n_q, t_qq, q, q, h3s, refl_q]);
    // h3ss : le n_qq (add t_qq q)
    let t_qqq = d.const_app(p.add, &[t_qq, q]);
    d.lemma(p.le_trans, &[p_term, n_qq, t_qqq, c12, h3ss])
    // : le p_term t_qqq   where t_qqq = ((t_term + q) + q) + q
}

/// From `base q : CReal` (`q := ofRat q_rat`), produce `(q3_rat, proof)`
/// where `q3_rat := Rat.add q_rat (Rat.add q_rat q_rat)` and
/// `proof : Equiv (add (add (add base q) q) q) (add base (ofRat q3_rat))`.
fn regroup_and_fuse(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    base: ExprId,
    q: ExprId,
    q_rat: ExprId,
) -> (ExprId, ExprId) {
    let base_q = d.const_app(p.add, &[base, q]);
    let base_q_q = d.const_app(p.add, &[base_q, q]);
    let base_qqq = d.const_app(p.add, &[base_q_q, q]);
    let qq = d.const_app(p.add, &[q, q]);

    let base_q_qq = d.const_app(p.add, &[base_q, qq]);
    let assoc1 = d.lemma(p.add_assoc, &[base_q, q, q]);
    // assoc1 : Equiv base_qqq base_q_qq

    let q_qq = d.const_app(p.add, &[q, qq]);
    let base_plus_qqq_inner = d.const_app(p.add, &[base, q_qq]);
    let assoc2 = d.lemma(p.add_assoc, &[base, q, qq]);
    // assoc2 : Equiv base_q_qq base_plus_qqq_inner

    let chain1 = d.lemma(
        p.equiv_trans,
        &[base_qqq, base_q_qq, base_plus_qqq_inner, assoc1, assoc2],
    );
    // chain1 : Equiv base_qqq base_plus_qqq_inner

    let q2_rat = radd(d, q_rat, q_rat);
    let q2_embed = d.const_app(p.of_rat, &[q2_rat]);
    let fuse_inner = d.lemma(p.of_rat_add, &[q_rat, q_rat]);
    // fuse_inner : Equiv qq q2_embed
    let refl_q = d.lemma(p.equiv_refl, &[q]);
    let q_q2embed = d.const_app(p.add, &[q, q2_embed]);
    let congr_inner = d.lemma(p.add_congr, &[q, q, qq, q2_embed, refl_q, fuse_inner]);
    // congr_inner : Equiv q_qq q_q2embed

    let q3_rat = radd(d, q_rat, q2_rat);
    let q3_embed = d.const_app(p.of_rat, &[q3_rat]);
    let fuse_outer = d.lemma(p.of_rat_add, &[q_rat, q2_rat]);
    // fuse_outer : Equiv q_q2embed q3_embed
    let chain_inner = d.lemma(
        p.equiv_trans,
        &[q_qq, q_q2embed, q3_embed, congr_inner, fuse_outer],
    );
    // chain_inner : Equiv q_qq q3_embed

    let refl_base = d.lemma(p.equiv_refl, &[base]);
    let base_plus_q3embed = d.const_app(p.add, &[base, q3_embed]);
    let congr_outer = d.lemma(
        p.add_congr,
        &[base, base, q_qq, q3_embed, refl_base, chain_inner],
    );
    // congr_outer : Equiv base_plus_qqq_inner base_plus_q3embed

    let chain2 = d.lemma(
        p.equiv_trans,
        &[
            base_qqq,
            base_plus_qqq_inner,
            base_plus_q3embed,
            chain1,
            congr_outer,
        ],
    );
    // chain2 : Equiv base_qqq base_plus_q3embed
    (q3_rat, chain2)
}

/// `CReal.uniform_limit_uniformly_continuous : ∀ F G a b,
/// UniformConvergesOn F G a b → (∀ n, UniformlyContinuousOn (F n) a b) →
/// UniformlyContinuousOn G a b`.
///
/// See the section documentation above for the route.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
fn declare_uniform_limit_uniformly_continuous(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let rat = p.rat;
    let carrier = creal_ty(d, p);
    let seq_ty = seq_fn_ty(d, p);
    let func_ty = fn_ty(d, p);
    let nat = d.nat_ty();
    let one_nat = d.num(1);
    let two_nat = d.num(2);
    let three_nat = d.succ(two_nat);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);

    let hu_ty = uconv_ty(d, p, f, g, a, b);
    let hu_fv = d.fresh_fvar();
    let hu = d.kernel().fvar(hu_fv);

    let hc_ty = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let fn_term = d.apply(f, &[n]);
        let applied = uc_ty(d, p, fn_term, a, b);
        d.pi_fv(n_fv, nat, applied)
    };
    let hc_fv = d.fresh_fvar();
    let hc = d.kernel().fvar(hc_fv);

    let k = d.const_app(p.uconv_rate, &[f, g, a, b, hu]);
    let huspec = d.const_app(p.uconv_spec, &[f, g, a, b, hu]);
    // huspec : ∀ n x, le a x → le x b → close_within (f n x) (g x) (natDivSucc k n)

    // `e3(n) := 4n+3`, `weaken_rate three_nat n`'s OWN index -- reused so the
    // FINAL fusion step (`q3_rat ≤ natDivSucc 1 n`) is exactly
    // `weaken_rate`'s own output, no independent index arithmetic needed.
    let modulus_g = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let (e3, _) = weaken_rate(d, p, three_nat, n);
        let big_n = {
            let kp = d.succ(k);
            let product = NatOps::mul(d, kp, e3);
            NatOps::add(d, product, k)
        };
        let fn_big_n = d.apply(f, &[big_n]);
        let hc_big_n = d.apply(hc, &[big_n]);
        let modulus_big_n = d.const_app(p.uc_modulus, &[fn_big_n, a, b, hc_big_n]);
        let m = d.apply(modulus_big_n, &[e3]);
        d.lam_fv(n_fv, nat, m)
    };

    let spec_g = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let y_fv = d.fresh_fvar();
        let y = d.kernel().fvar(y_fv);
        let hax_fv = d.fresh_fvar();
        let hax = d.kernel().fvar(hax_fv);
        let hxb_fv = d.fresh_fvar();
        let hxb = d.kernel().fvar(hxb_fv);
        let hay_fv = d.fresh_fvar();
        let hay = d.kernel().fvar(hay_fv);
        let hyb_fv = d.fresh_fvar();
        let hyb = d.kernel().fvar(hyb_fv);

        let (e3, final_weaken) = weaken_rate(d, p, three_nat, n);
        // final_weaken : Rat.le (natDivSucc three_nat e3) (natDivSucc 1 n)
        let (big_n, k_weaken) = weaken_rate(d, p, k, e3);
        // k_weaken : Rat.le (natDivSucc k big_n) (natDivSucc 1 e3)

        let fn_big_n = d.apply(f, &[big_n]);
        let hc_big_n = d.apply(hc, &[big_n]);
        let modulus_big_n = d.const_app(p.uc_modulus, &[fn_big_n, a, b, hc_big_n]);
        let mod_at_e3 = d.apply(modulus_big_n, &[e3]);

        let h_bound = div_succ_at(d, p, one_nat, mod_at_e3);
        let h_ty = close_within(d, p, x, y, h_bound);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);

        // mid : close_within (fn_big_n x) (fn_big_n y) (natDivSucc 1 e3)
        let uc_spec_big_n = d.const_app(p.uc_spec, &[fn_big_n, a, b, hc_big_n]);
        let mid = d.apply(uc_spec_big_n, &[e3, x, y, hax, hxb, hay, hyb, h]);

        // t1 : close_within (fn_big_n x) (g x) (natDivSucc k big_n)
        let t1 = d.apply(huspec, &[big_n, x, hax, hxb]);
        // t3 : close_within (fn_big_n y) (g y) (natDivSucc k big_n)
        let t3 = d.apply(huspec, &[big_n, y, hay, hyb]);

        let k_big_n_bound = div_succ_at(d, p, k, big_n);
        let e3_bound = div_succ_at(d, p, one_nat, e3);
        let fn_big_n_x = d.apply(fn_big_n, &[x]);
        let fn_big_n_y = d.apply(fn_big_n, &[y]);
        let gx = d.apply(g, &[x]);
        let gy = d.apply(g, &[y]);

        let t1w = weaken_close_within(d, p, fn_big_n_x, gx, k_big_n_bound, e3_bound, t1, k_weaken);
        let t3w = weaken_close_within(d, p, fn_big_n_y, gy, k_big_n_bound, e3_bound, t3, k_weaken);
        // t1w : close_within (fn_big_n x) (g x) e3_bound
        // t3w : close_within (fn_big_n y) (g y) e3_bound

        let e3_embed = d.const_app(p.of_rat, &[e3_bound]);
        let logic = rat.int.logic;

        let split_two_sided = |d: &mut IntDev<'_>, u: ExprId, v: ExprId, hclose: ExprId| {
            let split = d.const_app(p.two_sided_of_abs_sub_le, &[u, v, e3_bound, hclose]);
            let v_plus = d.const_app(p.add, &[v, e3_embed]);
            let u_plus = d.const_app(p.add, &[u, e3_embed]);
            let upper_ty = d.const_app(p.le, &[u, v_plus]);
            let lower_ty = d.const_app(p.le, &[v, u_plus]);
            let uv = d.const_app(logic.and_left, &[upper_ty, lower_ty, split]);
            let vu = d.const_app(logic.and_right, &[upper_ty, lower_ty, split]);
            (uv, vu)
        };

        // (t1a, t1b) : le fn_big_n_x (gx+e3), le gx (fn_big_n_x+e3)
        let (t1a, t1b) = split_two_sided(d, fn_big_n_x, gx, t1w);
        // (mida, midb) : le fn_big_n_x (fn_big_n_y+e3), le fn_big_n_y (fn_big_n_x+e3)
        let (mida, midb) = split_two_sided(d, fn_big_n_x, fn_big_n_y, mid);
        // (t3a, t3b) : le fn_big_n_y (gy+e3), le gy (fn_big_n_y+e3)
        let (t3a, t3b) = split_two_sided(d, fn_big_n_y, gy, t3w);

        // (A) : le gx (((gy+e3)+e3)+e3)
        let raw_a = chain_triangle_upper(
            d, p, gx, fn_big_n_x, fn_big_n_y, gy, e3_embed, t1b, mida, t3a,
        );
        // (B) : le gy (((gx+e3)+e3)+e3)
        let raw_b = chain_triangle_upper(
            d, p, gy, fn_big_n_y, fn_big_n_x, gx, e3_embed, t3b, midb, t1a,
        );

        let (q3_rat_a, fuse_a) = regroup_and_fuse(d, p, gy, e3_embed, e3_bound);
        let (q3_rat_b, fuse_b) = regroup_and_fuse(d, p, gx, e3_embed, e3_bound);
        // q3_rat_a and q3_rat_b are built identically (same formula, no
        // dependence on `base`), so they are the same term.
        let q3_rat = q3_rat_a;
        let _ = q3_rat_b;

        let refl_gx = d.lemma(p.equiv_refl, &[gx]);
        let raw_a_rhs = {
            let base_q = d.const_app(p.add, &[gy, e3_embed]);
            let base_q_q = d.const_app(p.add, &[base_q, e3_embed]);
            d.const_app(p.add, &[base_q_q, e3_embed])
        };
        let q3_embed = d.const_app(p.of_rat, &[q3_rat]);
        let target_a = d.const_app(p.add, &[gy, q3_embed]);
        let a_final = d.lemma(
            p.le_congr,
            &[gx, gx, raw_a_rhs, target_a, refl_gx, fuse_a, raw_a],
        );
        // a_final : le gx (add gy (ofRat q3_rat))

        let refl_gy = d.lemma(p.equiv_refl, &[gy]);
        let raw_b_rhs = {
            let base_q = d.const_app(p.add, &[gx, e3_embed]);
            let base_q_q = d.const_app(p.add, &[base_q, e3_embed]);
            d.const_app(p.add, &[base_q_q, e3_embed])
        };
        let target_b = d.const_app(p.add, &[gx, q3_embed]);
        let b_final = d.lemma(
            p.le_congr,
            &[gy, gy, raw_b_rhs, target_b, refl_gy, fuse_b, raw_b],
        );
        // b_final : le gy (add gx (ofRat q3_rat))

        let combined = d.lemma(p.abs_le_of_two_sided, &[gx, gy, q3_rat, a_final, b_final]);
        // combined : close_within gx gy q3_rat

        // q3_rat ≤ natDivSucc 1 n, via `final_weaken` and fusing
        // e3_bound+e3_bound+e3_bound into natDivSucc three_nat e3.
        let two_ish = NatOps::add(d, one_nat, one_nat);
        let fuse1 = d.lemma(rat.nat_div_succ_add, &[one_nat, one_nat, e3]);
        // fuse1 : Eq (radd e3_bound e3_bound) (natDivSucc two_ish e3)
        let nd_two_ish = div_succ_at(d, p, two_ish, e3);
        let inner_sum = radd(d, e3_bound, e3_bound);
        let congr_q3 = {
            let f = |d: &mut IntDev<'_>, t: ExprId| radd(d, e3_bound, t);
            crate::rat_prelude::ops::rcongr(d, inner_sum, nd_two_ish, fuse1, &f)
        };
        // congr_q3 : Eq q3_rat (radd e3_bound nd_two_ish)
        let radd_mid = radd(d, e3_bound, nd_two_ish);
        let add_expr = NatOps::add(d, one_nat, two_ish);
        let fuse2 = d.lemma(rat.nat_div_succ_add, &[one_nat, two_ish, e3]);
        // fuse2 : Eq (radd e3_bound nd_two_ish) (natDivSucc add_expr e3)
        let nd_add_expr = div_succ_at(d, p, add_expr, e3);
        let (_, combined_eq) = crate::rat_prelude::ops::rchain(
            d,
            q3_rat,
            &[(radd_mid, congr_q3), (nd_add_expr, fuse2)],
        );
        // combined_eq : Eq q3_rat (natDivSucc add_expr e3)

        let bridge3 = NatOps::refl(d, add_expr);
        let nd_three_e3 = div_succ_at(d, p, three_nat, e3);
        let final_q3_eq =
            nat_rewrite_prop(d, add_expr, three_nat, bridge3, combined_eq, &|d, t| {
                let nd = div_succ_at(d, p, t, e3);
                crate::rat_prelude::ops::req(d, q3_rat, nd)
            });
        // final_q3_eq : Eq q3_rat nd_three_e3

        let final_q3_eq_symm = crate::rat_prelude::ops::rsymm(d, q3_rat, nd_three_e3, final_q3_eq);
        // final_q3_eq_symm : Eq nd_three_e3 q3_rat
        let final_n_bound = div_succ_at(d, p, one_nat, n);
        let q3_le_final = rat_eq_rewrite(
            d,
            nd_three_e3,
            q3_rat,
            final_q3_eq_symm,
            final_weaken,
            &|d, t| rle(d, rat, t, final_n_bound),
        );
        // q3_le_final : Rat.le q3_rat (natDivSucc 1 n)

        let final_close =
            weaken_close_within(d, p, gx, gy, q3_rat, final_n_bound, combined, q3_le_final);
        // final_close : close_within gx gy (natDivSucc 1 n)

        let with_h = d.lam_fv(h_fv, h_ty, final_close);
        let range_yb = d.const_app(p.le, &[y, b]);
        let range_ay = d.const_app(p.le, &[a, y]);
        let range_xb = d.const_app(p.le, &[x, b]);
        let range_ax = d.const_app(p.le, &[a, x]);
        let with_hyb = d.lam_fv(hyb_fv, range_yb, with_h);
        let with_hay = d.lam_fv(hay_fv, range_ay, with_hyb);
        let with_hxb = d.lam_fv(hxb_fv, range_xb, with_hay);
        let with_hax = d.lam_fv(hax_fv, range_ax, with_hxb);
        let with_y = d.lam_fv(y_fv, carrier, with_hax);
        let with_x = d.lam_fv(x_fv, carrier, with_y);
        d.lam_fv(n_fv, nat, with_x)
    };

    let mk_applied = d.const_app(p.uc_mk, &[g, a, b, modulus_g, spec_g]);

    let value = {
        let with_hc = d.lam_fv(hc_fv, hc_ty, mk_applied);
        let with_hu = d.lam_fv(hu_fv, hu_ty, with_hc);
        let with_b = d.lam_fv(b_fv, carrier, with_hu);
        let with_a = d.lam_fv(a_fv, carrier, with_b);
        let with_g = d.lam_fv(g_fv, func_ty, with_a);
        d.lam_fv(f_fv, seq_ty, with_g)
    };
    let ty = {
        let conclusion = uc_ty(d, p, g, a, b);
        let after_hc = d.arrow(hc_ty, conclusion);
        let after_hu = d.arrow(hu_ty, after_hc);
        let with_b = d.pi_fv(b_fv, carrier, after_hu);
        let with_a = d.pi_fv(a_fv, carrier, with_b);
        let with_g = d.pi_fv(g_fv, func_ty, with_a);
        d.pi_fv(f_fv, seq_ty, with_g)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.uniform_limit_uniformly_continuous,
        uparams: vec![],
        ty,
        value,
    })
}

/// Admit `CReal.uniform_limit_uniformly_continuous`, the chapter's headline
/// theorem. A SECOND entry point (Rust privacy aside, this needs
/// `CReal.UniformlyContinuousOn`'s `modulus`/`spec` projections, declared by
/// `uniform_continuity::declare_uniform_continuity`, which runs after this
/// file's own [`declare_uniform_converges_on`] in `creal.rs`'s build order).
///
/// # Errors
///
/// Returns the trusted gate's rejection.
pub(super) fn declare_uniform_convergence_continuity(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    declare_uniform_limit_uniformly_continuous(d, p)
}

// ============================================================================
// Theorem: sums preserve uniform convergence.
// ============================================================================
//
// `∀ F H G K a b, UniformConvergesOn F G a b → UniformConvergesOn H K a b →
// UniformConvergesOn (fun n x => add (F n x) (H n x)) (fun x => add (G x) (K
// x)) a b`.
//
// The rate for the sum is EXACTLY `k1 + k2` (the two component rates added),
// because both `close_within` bounds already share the SAME denominator
// index `n` -- `Rat.natDivSucc_add` fuses `natDivSucc k1 n + natDivSucc k2 n`
// into `natDivSucc (k1+k2) n` with no widening/scaling step at all, unlike
// [`declare_uniform_limit_uniformly_continuous`]'s `weaken_rate`, which is
// needed there only because that theorem compares bounds at TWO DIFFERENT
// indices (the target accuracy `n` and a deeper function-index `N`). The
// route: split each `close_within` hypothesis into its two one-sided `le`
// legs via `CReal.two_sided_of_abs_sub_le`, combine the matching legs with
// `CReal.add_le_add`, rearrange the resulting four-term sum with
// [`add4_comm`] so the two "gap" terms land together, fuse the two
// `ofRat`-embedded gaps into one `ofRat (Rat.add b1 b2)` via
// `CReal.ofRat_add`, rebuild a single `close_within` bound at that fused
// rational via `CReal.abs_le_of_two_sided`, and finally widen that bound (by
// an EXACT `Rat` equality this time, not merely an inequality) to the stated
// `natDivSucc (k1+k2) n` shape via `Rat.natDivSucc_add` and
// [`weaken_close_within`].

/// `CReal.uniform_converges_add : ∀ F H G K a b, UniformConvergesOn F G a b →
/// UniformConvergesOn H K a b → UniformConvergesOn (fun n x => add (F n x) (H
/// n x)) (fun x => add (G x) (K x)) a b`.
///
/// See the section documentation above for the route.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
pub(super) fn declare_uniform_converges_add(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let rat = p.rat;
    let carrier = creal_ty(d, p);
    let seq_ty = seq_fn_ty(d, p);
    let func_ty = fn_ty(d, p);
    let nat = d.nat_ty();
    let logic = rat.int.logic;

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);
    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);

    let hu1_ty = uconv_ty(d, p, f, g, a, b);
    let hu1_fv = d.fresh_fvar();
    let hu1 = d.kernel().fvar(hu1_fv);
    let hu2_ty = uconv_ty(d, p, h, k, a, b);
    let hu2_fv = d.fresh_fvar();
    let hu2 = d.kernel().fvar(hu2_fv);

    // `sum_seq := fun n x => add (F n x) (H n x)`, `sum_fn := fun x => add (G
    // x) (K x)` -- the subject of the conclusion's `UniformConvergesOn`.
    let sum_seq = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let fnx = d.apply(f, &[n, x]);
        let hnx = d.apply(h, &[n, x]);
        let sum = d.const_app(p.add, &[fnx, hnx]);
        let with_x = d.lam_fv(x_fv, carrier, sum);
        d.lam_fv(n_fv, nat, with_x)
    };
    let sum_fn = {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let gx = d.apply(g, &[x]);
        let kx = d.apply(k, &[x]);
        let sum = d.const_app(p.add, &[gx, kx]);
        d.lam_fv(x_fv, carrier, sum)
    };

    let k1 = d.const_app(p.uconv_rate, &[f, g, a, b, hu1]);
    let k2 = d.const_app(p.uconv_rate, &[h, k, a, b, hu2]);
    let rate = NatOps::add(d, k1, k2);

    let huspec1 = d.const_app(p.uconv_spec, &[f, g, a, b, hu1]);
    let huspec2 = d.const_app(p.uconv_spec, &[h, k, a, b, hu2]);

    let spec = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let hax_fv = d.fresh_fvar();
        let hax = d.kernel().fvar(hax_fv);
        let hxb_fv = d.fresh_fvar();
        let hxb = d.kernel().fvar(hxb_fv);

        let fnx = d.apply(f, &[n, x]);
        let hnx = d.apply(h, &[n, x]);
        let gx = d.apply(g, &[x]);
        let kx = d.apply(k, &[x]);
        let sumf = d.const_app(p.add, &[fnx, hnx]);
        let sumg = d.const_app(p.add, &[gx, kx]);

        let b1 = div_succ_at(d, p, k1, n);
        let b2 = div_succ_at(d, p, k2, n);
        let e1 = d.const_app(p.of_rat, &[b1]);
        let e2 = d.const_app(p.of_rat, &[b2]);

        // t1 : close_within fnx gx b1, t2 : close_within hnx kx b2.
        let t1 = d.apply(huspec1, &[n, x, hax, hxb]);
        let t2 = d.apply(huspec2, &[n, x, hax, hxb]);

        // Split each into its two one-sided legs.
        let gx_plus_e1 = d.const_app(p.add, &[gx, e1]);
        let fnx_plus_e1 = d.const_app(p.add, &[fnx, e1]);
        let f1u_ty = d.const_app(p.le, &[fnx, gx_plus_e1]);
        let f1l_ty = d.const_app(p.le, &[gx, fnx_plus_e1]);
        let split1 = d.const_app(p.two_sided_of_abs_sub_le, &[fnx, gx, b1, t1]);
        let f1u = d.const_app(logic.and_left, &[f1u_ty, f1l_ty, split1]);
        let f1l = d.const_app(logic.and_right, &[f1u_ty, f1l_ty, split1]);

        let kx_plus_e2 = d.const_app(p.add, &[kx, e2]);
        let hnx_plus_e2 = d.const_app(p.add, &[hnx, e2]);
        let f2u_ty = d.const_app(p.le, &[hnx, kx_plus_e2]);
        let f2l_ty = d.const_app(p.le, &[kx, hnx_plus_e2]);
        let split2 = d.const_app(p.two_sided_of_abs_sub_le, &[hnx, kx, b2, t2]);
        let f2u = d.const_app(logic.and_left, &[f2u_ty, f2l_ty, split2]);
        let f2l = d.const_app(logic.and_right, &[f2u_ty, f2l_ty, split2]);

        // su : le sumf (add gx_plus_e1 kx_plus_e2)
        let su = d.lemma(p.add_le_add, &[fnx, gx_plus_e1, hnx, kx_plus_e2, f1u, f2u]);
        // sl : le sumg (add fnx_plus_e1 hnx_plus_e2)
        let sl = d.lemma(p.add_le_add, &[gx, fnx_plus_e1, kx, hnx_plus_e2, f1l, f2l]);

        // Rearrange each RHS: (a+e1)+(c+e2) ~ (a+c)+(e1+e2).
        let (target_u, pu) = add4_comm(d, p, gx, e1, kx, e2);
        // target_u = add (add gx kx) (add e1 e2)
        let rhs_u = d.const_app(p.add, &[gx_plus_e1, kx_plus_e2]);
        let refl_sumf = d.lemma(p.equiv_refl, &[sumf]);
        let su2 = d.lemma(
            p.le_congr,
            &[sumf, sumf, rhs_u, target_u, refl_sumf, pu, su],
        );
        // su2 : le sumf target_u

        let (target_l, pl) = add4_comm(d, p, fnx, e1, hnx, e2);
        // target_l = add sumf (add e1 e2)   (add fnx hnx is exactly sumf)
        let rhs_l = d.const_app(p.add, &[fnx_plus_e1, hnx_plus_e2]);
        let refl_sumg = d.lemma(p.equiv_refl, &[sumg]);
        let sl2 = d.lemma(
            p.le_congr,
            &[sumg, sumg, rhs_l, target_l, refl_sumg, pl, sl],
        );
        // sl2 : le sumg target_l

        // Fuse the two `ofRat`-embedded gaps into one.
        let e1e2 = d.const_app(p.add, &[e1, e2]);
        let radd_b1b2 = radd(d, b1, b2);
        let fuse = d.lemma(p.of_rat_add, &[b1, b2]);
        // fuse : Equiv e1e2 (ofRat radd_b1b2)
        let ofrat_radd = d.const_app(p.of_rat, &[radd_b1b2]);

        let sumg_add4 = d.const_app(p.add, &[gx, kx]);
        let final_u_rhs = d.const_app(p.add, &[sumg_add4, ofrat_radd]);
        let congr_u = {
            let refl_sumg4 = d.lemma(p.equiv_refl, &[sumg_add4]);
            d.lemma(
                p.add_congr,
                &[sumg_add4, sumg_add4, e1e2, ofrat_radd, refl_sumg4, fuse],
            )
        };
        // congr_u : Equiv target_u final_u_rhs
        let hxy = d.lemma(
            p.le_congr,
            &[sumf, sumf, target_u, final_u_rhs, refl_sumf, congr_u, su2],
        );
        // hxy : le sumf final_u_rhs

        let final_l_rhs = d.const_app(p.add, &[sumf, ofrat_radd]);
        let congr_l = {
            let refl_sumf2 = d.lemma(p.equiv_refl, &[sumf]);
            d.lemma(
                p.add_congr,
                &[sumf, sumf, e1e2, ofrat_radd, refl_sumf2, fuse],
            )
        };
        // congr_l : Equiv target_l final_l_rhs
        let hyx = d.lemma(
            p.le_congr,
            &[sumg, sumg, target_l, final_l_rhs, refl_sumg, congr_l, sl2],
        );
        // hyx : le sumg final_l_rhs

        let combined = d.lemma(p.abs_le_of_two_sided, &[sumf, sumg, radd_b1b2, hxy, hyx]);
        // combined : close_within sumf sumg radd_b1b2

        // Widen the bound from `radd b1 b2` to `natDivSucc rate n` -- an
        // EXACT equality via `Rat.natDivSucc_add`, not merely an
        // inequality.
        let eq_k = d.lemma(rat.nat_div_succ_add, &[k1, k2, n]);
        // eq_k : Eq Rat radd_b1b2 (natDivSucc rate n)
        let final_bound = div_succ_at(d, p, rate, n);
        let refl_le = d.lemma(rat.le_refl, &[radd_b1b2]);
        let rat_le_final = rat_eq_rewrite(d, radd_b1b2, final_bound, eq_k, refl_le, &|d, t| {
            rle(d, rat, radd_b1b2, t)
        });
        // rat_le_final : Rat.le radd_b1b2 final_bound

        let final_close = weaken_close_within(
            d,
            p,
            sumf,
            sumg,
            radd_b1b2,
            final_bound,
            combined,
            rat_le_final,
        );
        // final_close : close_within sumf sumg final_bound

        let range_xb = d.const_app(p.le, &[x, b]);
        let range_ax = d.const_app(p.le, &[a, x]);
        let with_hxb = d.lam_fv(hxb_fv, range_xb, final_close);
        let with_hax = d.lam_fv(hax_fv, range_ax, with_hxb);
        let with_x = d.lam_fv(x_fv, carrier, with_hax);
        d.lam_fv(n_fv, nat, with_x)
    };

    let mk_applied = d.const_app(p.uconv_mk, &[sum_seq, sum_fn, a, b, rate, spec]);

    let value = {
        let with_hu2 = d.lam_fv(hu2_fv, hu2_ty, mk_applied);
        let with_hu1 = d.lam_fv(hu1_fv, hu1_ty, with_hu2);
        let with_b = d.lam_fv(b_fv, carrier, with_hu1);
        let with_a = d.lam_fv(a_fv, carrier, with_b);
        let with_k = d.lam_fv(k_fv, func_ty, with_a);
        let with_g = d.lam_fv(g_fv, func_ty, with_k);
        let with_h = d.lam_fv(h_fv, seq_ty, with_g);
        d.lam_fv(f_fv, seq_ty, with_h)
    };
    let ty = {
        let conclusion = uconv_ty(d, p, sum_seq, sum_fn, a, b);
        let after_hu2 = d.arrow(hu2_ty, conclusion);
        let after_hu1 = d.arrow(hu1_ty, after_hu2);
        let with_b = d.pi_fv(b_fv, carrier, after_hu1);
        let with_a = d.pi_fv(a_fv, carrier, with_b);
        let with_k = d.pi_fv(k_fv, func_ty, with_a);
        let with_g = d.pi_fv(g_fv, func_ty, with_k);
        let with_h = d.pi_fv(h_fv, seq_ty, with_g);
        d.pi_fv(f_fv, seq_ty, with_h)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.uniform_converges_add,
        uparams: vec![],
        ty,
        value,
    })
}

// ============================================================================
// The `Within -> close_within` bridge, generic in `x` and `y`.
// ============================================================================
//
// `UniformConvergesOn`'s `spec` needs a CReal-level `close_within` bound, but
// `Converges`/`Cauchy`/`regular_of_scaled_cauchy` (`creal/convergence.rs`)
// speak entirely in terms of `Within` -- raw rational samples matched at a
// SHARED index. Nothing exposed from this file's own already-landed theorems
// bridges the two: `converges_of_scaled_cauchy` stays in `Within` throughout
// (see its own doc comment), and `within_of_two_sided_le`
// (`creal/integral.rs`) goes the WRONG direction (a real-valued two-sided
// bound produces a `Within` fact at a chosen index, not the reverse).
//
// `creal/convergence.rs` already has this exact bridge, generic in BOTH `x`
// and `y`, at its own private (unexported) `close_within_of_sample_bound` --
// see that function's doc comment there. It is not `pub(super)`, and making
// it so is an edit to a file this session does not own (another lane's), so
// this section is an INDEPENDENT construction of the same conclusion, not a
// copy: where `close_within_of_sample_bound` reads `CReal.regular` at a
// SHIFTED index and telescopes four terms (`shifted_bound_at`), this route
// goes through `CRealPrelude::sample_upper_bound`/`sample_lower_bound`
// (`creal/uniform_continuity.rs`) directly at `hp`'s OWN index `n` -- no
// shift, no telescope, since those two lemmas already say "a value is within
// `1/(n+1)` of its own `n`-th sample" with no Cauchy hypothesis at all.

/// `Rat.Eq (Rat.add (Rat.sub a b) b) a` — adding back what was subtracted
/// cancels. A private copy of the technique `convergence.rs`'s own
/// (unexported) `add_sub_cancel` uses (Rust privacy: sibling module), in the
/// order [`one_sided_via_samples`] needs it.
fn sub_add_cancel(d: &mut IntDev<'_>, p: CRealPrelude, a: ExprId, b: ExprId) -> ExprId {
    let rat = p.rat;
    let neg_b = rneg(d, b);
    let a_negb = radd(d, a, neg_b);
    let lhs = radd(d, a_negb, b);
    let assoc = d.lemma(rat.add_assoc, &[a, neg_b, b]);
    // assoc : Eq lhs (add a (add neg_b b))
    let negb_b = radd(d, neg_b, b);
    let cancel_inner = d.lemma(rat.neg_add_cancel, &[b]); // Eq negb_b zero
    let zero = rzero(d, rat);
    let cancel = rcongr(d, negb_b, zero, cancel_inner, &|d, t| radd(d, a, t));
    let a_plus_zero = radd(d, a, zero);
    let add_zero_proof = d.lemma(rat.add_zero, &[a]); // Eq a_plus_zero a
    let a_radd_negb_b = radd(d, a, negb_b);
    let (_, proof) = rchain(
        d,
        lhs,
        &[
            (a_radd_negb_b, assoc),
            (a_plus_zero, cancel),
            (a, add_zero_proof),
        ],
    );
    // proof : Eq lhs a, and `lhs` is defeq `Rat.add (Rat.sub a b) b`
    // (`Rat.sub a b := Rat.add a (Rat.neg b)`, the same unfold
    // `Rat.sub_self`'s own proof leans on directly).
    proof
}

/// From `upper_uv : Rat.le (Rat.sub (sample u n) (sample v n)) (natDivSucc k
/// n)`, derive `(bound_rat, proof)` where `bound_rat := Rat.add o (Rat.add
/// bk o)` (`bk := natDivSucc k n`, `o := natDivSucc 1 n`) and `proof :
/// CReal.le u (CReal.add v (CReal.ofRat bound_rat))`.
///
/// The one-sided half of [`close_within_of_within_at`]'s bridge. `u`'s own
/// `1/(n+1)`-slack self-approximation
/// ([`CRealPrelude::sample_upper_bound`]) chains through `upper_uv`
/// (rearranged via `Rat.le_of_sub_le`) into `v`'s OWN sample `av`; then `av`
/// is rewritten as `(av - o) + o` ([`sub_add_cancel`]) so that `v`'s own
/// `1/(n+1)`-slack self-approximation
/// ([`CRealPrelude::sample_lower_bound`], stated in terms of `av - o`)
/// applies directly, via `CReal.ofRat_add`/`CReal.add_le_add`/`CReal.le_congr`
/// to move between the split and fused forms.
fn one_sided_via_samples(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    u: ExprId,
    v: ExprId,
    n: ExprId,
    bk: ExprId,
    o: ExprId,
    upper_uv: ExprId,
) -> (ExprId, ExprId) {
    let rat = p.rat;
    let au = sample(d, p, u, n);
    let av = sample(d, p, v, n);

    // au_le_avbk : Rat.le au (Rat.add av bk).
    let au_le_avbk = d.lemma(rat.le_of_sub_le, &[au, av, bk, upper_uv]);

    // step2 : Rat.le (au+o) ((av+bk)+o).
    let o_refl = d.lemma(rat.le_refl, &[o]);
    let av_bk = radd(d, av, bk);
    let step2 = d.lemma(rat.add_le_add, &[au, av_bk, o, o, au_le_avbk, o_refl]);

    // step3 : Rat.le (au+o) (av+(bk+o)), reassociating the RHS.
    let bk_o = radd(d, bk, o);
    let av_bk_o = radd(d, av, bk_o);
    let assoc1 = d.lemma(rat.add_assoc, &[av, bk, o]);
    let au_o = radd(d, au, o);
    let av_bk_then_o = radd(d, av_bk, o);
    let step3 = rat_eq_rewrite(d, av_bk_then_o, av_bk_o, assoc1, step2, &|d, t| {
        rle(d, rat, au_o, t)
    });

    // bridge_eq : Eq (av+(bk+o)) ((av-o)+(o+(bk+o))), substituting
    // `av = (av-o)+o` (`sub_add_cancel`, symmetrized) then reassociating.
    let av_minus_o = rsub(d, rat, av, o);
    let cancel = sub_add_cancel(d, p, av, o); // Eq (radd av_minus_o o) av
    let restored = radd(d, av_minus_o, o);
    let cancel_symm = rsymm(d, restored, av, cancel); // Eq av restored
    let av_bko_congr = rcongr(d, av, restored, cancel_symm, &|d, t| radd(d, t, bk_o));
    // av_bko_congr : Eq (av+bk_o) (restored+bk_o)
    let o_bk_o = radd(d, o, bk_o);
    let assoc2 = d.lemma(rat.add_assoc, &[av_minus_o, o, bk_o]);
    // assoc2 : Eq (restored+bk_o) ((av-o)+(o+bk_o))
    let target_shape = radd(d, av_minus_o, o_bk_o);
    let restored_bk_o = radd(d, restored, bk_o);
    let (_, bridge_eq) = rchain(
        d,
        av_bk_o,
        &[(restored_bk_o, av_bko_congr), (target_shape, assoc2)],
    );

    // step4 : Rat.le (au+o) ((av-o)+(o+bk_o)).
    let step4 = rat_eq_rewrite(d, av_bk_o, target_shape, bridge_eq, step3, &|d, t| {
        rle(d, rat, au_o, t)
    });

    // chain1 : CReal.le u (ofRat target_shape).
    let hu_upper = d.lemma(p.sample_upper_bound, &[u, n]);
    let mid = embed(d, p, au_o);
    let target1 = embed(d, p, target_shape);
    let ofrat_le_1 = d.lemma(p.of_rat_le, &[au_o, target_shape, step4]);
    let chain1 = d.lemma(p.le_trans, &[u, mid, target1, hu_upper, ofrat_le_1]);

    // chain2 : CReal.le u (add (ofRat av_minus_o) (ofRat o_bk_o)), splitting
    // `target1` via `CReal.ofRat_add`.
    let embed_av_minus_o = embed(d, p, av_minus_o);
    let embed_o_bk_o = embed(d, p, o_bk_o);
    let split = d.const_app(p.add, &[embed_av_minus_o, embed_o_bk_o]);
    let fuse = d.lemma(p.of_rat_add, &[av_minus_o, o_bk_o]);
    // fuse : Equiv split target1
    let fuse_symm = d.lemma(p.equiv_symm, &[split, target1, fuse]);
    let refl_u = d.lemma(p.equiv_refl, &[u]);
    let chain2 = d.lemma(
        p.le_congr,
        &[u, u, target1, split, refl_u, fuse_symm, chain1],
    );

    // step5 : CReal.le split (add v (ofRat o_bk_o)), via `sample_lower_bound`.
    let hv_lower = d.lemma(p.sample_lower_bound, &[v, n]);
    let o_bk_o_refl = d.lemma(p.le_refl, &[embed_o_bk_o]);
    let step5 = d.lemma(
        p.add_le_add,
        &[
            embed_av_minus_o,
            v,
            embed_o_bk_o,
            embed_o_bk_o,
            hv_lower,
            o_bk_o_refl,
        ],
    );

    let final_target = d.const_app(p.add, &[v, embed_o_bk_o]);
    let result = d.lemma(p.le_trans, &[u, split, final_target, chain2, step5]);
    (o_bk_o, result)
}

/// From `hp : Within (Rat.sub (sample x n) (sample y n)) (natDivSucc k n)`,
/// derive `(rate, proof)` where `proof : close_within x y (natDivSucc rate
/// n)` — the `Within -> close_within` bridge, generic in BOTH `x` and `y`
/// (stronger than the task needed: no bespoke construction of either is
/// assumed anywhere above or below).
///
/// `rate := 1+(k+1)`: `hp`'s own `k/(n+1)` slack plus `1/(n+1)` for each of
/// `x`/`y`'s own self-approximation gap ([`one_sided_via_samples`], called
/// once per direction with `(u,v) := (x,y)` and `(u,v) := (y,x)`), fused via
/// two `Rat.natDivSucc_add` applications. See this section's own module
/// documentation for why this is an independent construction of
/// `convergence.rs`'s own (unexported, un-reused) `close_within_of_sample_bound`
/// rather than a copy of it.
pub(super) fn close_within_of_within_at(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    x: ExprId,
    y: ExprId,
    n: ExprId,
    k: ExprId,
    hp: ExprId,
) -> (ExprId, ExprId) {
    let rat = p.rat;
    let ax = sample(d, p, x, n);
    let ay = sample(d, p, y, n);
    let diff = rsub(d, rat, ax, ay);
    let bk = div_succ_at(d, p, k, n);
    let one_nat = d.num(1);
    let o = div_succ_at(d, p, one_nat, n);

    let (hp_lower, hp_upper) = halves(d, p, diff, bk, hp);

    // hp_upper_swapped : Rat.le (sub ay ax) bk, via `bounds_neg` + `neg_sub`.
    let hp_upper_swapped = {
        let neg_bk = rneg(d, bk);
        let neg_diff = rneg(d, diff);
        let bn_left = rle(d, rat, neg_bk, neg_diff);
        let bn_right = rle(d, rat, neg_diff, bk);
        let bn = d.lemma(rat.bounds_neg, &[diff, bk, hp_lower, hp_upper]);
        let raw = d.and_right(bn_left, bn_right, bn);
        let ay_ax = rsub(d, rat, ay, ax);
        let neg_sub_eq = d.lemma(rat.neg_sub, &[ax, ay]); // Eq neg_diff ay_ax
        rat_eq_rewrite(d, neg_diff, ay_ax, neg_sub_eq, raw, &|d, t| {
            rle(d, rat, t, bk)
        })
    };

    let (bound_rat, goal_up) = one_sided_via_samples(d, p, x, y, n, bk, o, hp_upper);
    let (_, goal_down) = one_sided_via_samples(d, p, y, x, n, bk, o, hp_upper_swapped);

    let close = d.lemma(
        p.abs_le_of_two_sided,
        &[x, y, bound_rat, goal_up, goal_down],
    );

    // Fuse `bound_rat = o + (bk + o)` into a single `natDivSucc rate n`.
    let k1 = NatOps::add(d, k, one_nat);
    let eq_a = d.lemma(rat.nat_div_succ_add, &[k, one_nat, n]);
    // eq_a : Eq (radd bk o) (natDivSucc k1 n)
    let bk_o = radd(d, bk, o);
    let k1_nat_div = div_succ_at(d, p, k1, n);
    let inner_congr = rcongr(d, bk_o, k1_nat_div, eq_a, &|d, t| radd(d, o, t));
    // inner_congr : Eq bound_rat (radd o k1_nat_div)
    let rate = NatOps::add(d, one_nat, k1);
    let eq_b = d.lemma(rat.nat_div_succ_add, &[one_nat, k1, n]);
    // eq_b : Eq (radd o k1_nat_div) (natDivSucc rate n)
    let final_bound = div_succ_at(d, p, rate, n);
    let o_k1 = radd(d, o, k1_nat_div);
    let (_, eq_k) = rchain(d, bound_rat, &[(o_k1, inner_congr), (final_bound, eq_b)]);

    let refl_le = d.lemma(rat.le_refl, &[bound_rat]);
    let rat_le_final = rat_eq_rewrite(d, bound_rat, final_bound, eq_k, refl_le, &|d, t| {
        rle(d, rat, bound_rat, t)
    });
    let final_close = weaken_close_within(d, p, x, y, bound_rat, final_bound, close, rat_le_final);
    (rate, final_close)
}

/// Admit `CReal.close_within_of_within`. See
/// [`close_within_of_within_at`]'s own doc comment for the route.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// refused a proof, not that a script gave up.
pub(super) fn declare_close_within_of_within(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let y_fv = d.fresh_fvar();
    let y = d.kernel().fvar(y_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);

    let ax = sample(d, p, x, n);
    let ay = sample(d, p, y, n);
    let diff = rsub(d, p.rat, ax, ay);
    let bk = div_succ_at(d, p, k, n);
    let hyp_ty = within(d, p, diff, bk);
    let hp_fv = d.fresh_fvar();
    let hp = d.kernel().fvar(hp_fv);

    let (rate, proof) = close_within_of_within_at(d, p, x, y, n, k, hp);

    let value = {
        let with_hp = d.lam_fv(hp_fv, hyp_ty, proof);
        let with_k = d.lam_fv(k_fv, nat, with_hp);
        let with_n = d.lam_fv(n_fv, nat, with_k);
        let with_y = d.lam_fv(y_fv, carrier, with_n);
        d.lam_fv(x_fv, carrier, with_y)
    };
    let ty = {
        let final_bound = div_succ_at(d, p, rate, n);
        let concl = close_within(d, p, x, y, final_bound);
        let inner = d.arrow(hyp_ty, concl);
        let with_k = d.pi_fv(k_fv, nat, inner);
        let with_n = d.pi_fv(n_fv, nat, with_k);
        let with_y = d.pi_fv(y_fv, carrier, with_n);
        d.pi_fv(x_fv, carrier, with_y)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.close_within_of_within,
        uparams: vec![],
        ty,
        value,
    })
}

// ============================================================================
// Theorem: the Weierstrass M-test.
// ============================================================================
//
// `CReal.weierstrassMTest : ∀ (f : Nat → CReal → CReal) (mseq : Nat → CReal)
// (a b : CReal), le a b → (∀ j p q, Equiv p q → Equiv (f j p) (f j q)) →
// ∀ k, (∀ j pt, le a pt → le pt b → le (abs (f j pt)) (mseq j)) →
// (∀ pp qq, Within (seq (sumRange mseq pp) pp − seq (sumRange mseq qq) qq)
//   (natDivSucc k pp + natDivSucc k qq)) →
// UniformConvergesOn (fun n pt => sumRange (fun j => f j pt) n)
//                     (fun pt => ⟨the limit built at `clamp a b pt`⟩) a b`.
//
// **The totality obstruction, and how it is resolved.** `UniformConvergesOn`'s
// own `G` field is a raw, TOTAL `CReal → CReal` -- one of `UniformConvergesOn
// F G a b`'s four PARAMETERS, fixed before `rate`/`spec` are built -- but the
// only route this file has to a well-defined limit (`series.rs`'s raw,
// non-existential Cauchy-comparison machinery, `convergence.rs`'s
// `regular_of_scaled_cauchy`/`converges_of_scaled_cauchy`) needs, at each
// point, a POINTWISE DOMINATION PROOF `∀ j, le (abs (f j pt)) (mseq j)`,
// which this theorem's own hypothesis only supplies for `pt` ALREADY KNOWN to
// satisfy `le a pt`/`le pt b`. `CReal.le` is not decidable (this
// development's own standing rule: never branch on it), so there is no way
// to conjure that membership proof for an arbitrary symbolic `pt` -- `G`
// genuinely cannot be built from `pt` directly, and this is exactly the
// obstruction the module documentation of this declaration's own caller was
// written to flag before assembly began.
//
// The fix is the same one `creal.rs`'s own `crossing_close_clamped` names for
// an unrelated theorem: **clamp first, for free.** `pt_clamped := max a (min
// pt b)` is UNCONDITIONALLY in `[a, b]` (`le_max_left` gives the lower bound
// outright; `max_le` + `min_le_right` gives the upper bound from the new
// `le a b` hypothesis alone, no case split, no decidability), so `G := fun pt
// => <limit built from pt_clamped>` is total by construction. The price is a
// SECOND hypothesis this route needs beyond what a first reading of the
// M-test states: `f`'s pointwise congruence (`∀ j p q, Equiv p q → Equiv (f j
// p) (f j q)`). Without it, `f j` is only a function of a REPRESENTATIVE
// (this development's `CReal` is a Bishop SETOID, not a literal quotient --
// ADR-0512 -- so an arbitrary `CReal → CReal` term need not respect `Equiv`
// at all), and nothing relates `f j pt` to `f j pt_clamped` even once `pt ~
// pt_clamped` is shown (`equiv_of_le_le` from `min_le_left`/`le_min`, then
// again from `max_le`/`le_max_right`, chained by `equiv_trans`). This
// congruence hypothesis is not a proof-engineering convenience; it is the
// same assumption -- "`f` is a genuine function of the real number, not of
// its representative" -- that is invisible (automatically true) in a
// classical set-theoretic treatment and must be stated explicitly here.
//
// With both in hand, [`declare_weierstrass_m_test`] builds exactly ONE Cauchy
// structure -- at `pt_clamped`, reusing
// [`CRealPrelude::sum_range_cauchy_dominated_ordered_normalized`] the same
// way `series.rs`'s own (`Prop`-`Exists`-wrapped) `sumRange_cauchy_of_dominated`
// assembles it (`Nat.le_total` case split, [`within_symm`] flip in one
// branch -- an INDEPENDENT construction, not a copy, since here the Cauchy
// witness for `mseq` is already raw rather than needing its own
// `exists_elim`) -- and derives `G pt`'s `CReal.mk` from it via
// [`kregular_of_cauchy_proof`] + `regular_of_kregular` + `speedup`/
// `speedup_close`, mirroring `convergence.rs`'s own `converges_of_scaled_cauchy`
// construction (independent again: that theorem's conclusion is `Prop`-wrapped
// `Converges`, and this file needs the raw per-`n` `Within` fact underneath
// it, generic in `pt`). [`close_within_of_within_at`] turns that fact into
// `close_within (sumRange f_clamped n) (G pt) …`; one `sumRange_congr`/
// `add_congr`/`abs_congr`/`le_congr` chain (using the congruence hypothesis
// and `pt ~ pt_clamped`) transports it to the UNCLAMPED `close_within
// (sumRange f_pt n) (G pt) …` that `spec` actually needs.

/// `λ n, seq (f n) n` -- a private copy of `convergence.rs`'s own
/// (unexported) `diagonal` (Rust privacy: sibling module), needed here to
/// build `G`'s `CReal.mk` directly rather than through
/// `converges_of_scaled_cauchy`'s own `Prop`-wrapped `Converges` conclusion
/// (this file needs the raw per-`n` `Within` fact underneath it, generic in
/// a symbolic point, which an `Exists`-wrapped `Converges` cannot supply
/// into a `Type`-valued construction).
fn diagonal_seq(d: &mut IntDev<'_>, p: CRealPrelude, f: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let fn_term = d.apply(f, &[n]);
    let body = sample(d, p, fn_term, n);
    d.lam_fv(n_fv, nat, body)
}

/// Admit `CReal.weierstrassMTest`. See the section documentation above for
/// the route, the clamping construction that makes `G` total, and why the
/// pointwise-congruence hypothesis is needed.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
#[allow(clippy::too_many_lines)]
pub(super) fn declare_weierstrass_m_test(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let rat = p.rat;
    let nat = d.nat_ty();
    let carrier = creal_ty(d, p);
    let seq_ty = seq_fn_ty(d, p); // Nat -> CReal -> CReal
    let mseq_ty = d.arrow(nat, carrier); // Nat -> CReal

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let mseq_fv = d.fresh_fvar();
    let mseq = d.kernel().fvar(mseq_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);

    let hab_ty = d.const_app(p.le, &[a, b]);
    let hab_fv = d.fresh_fvar();
    let hab = d.kernel().fvar(hab_fv);

    // hcong : ∀ j p q, Equiv p q → Equiv (f j p) (f j q).
    let hcong_ty = {
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let pp_fv = d.fresh_fvar();
        let pp = d.kernel().fvar(pp_fv);
        let qq_fv = d.fresh_fvar();
        let qq = d.kernel().fvar(qq_fv);
        let heq_ty = d.const_app(p.equiv, &[pp, qq]);
        let fjp = d.apply(f, &[j, pp]);
        let fjq = d.apply(f, &[j, qq]);
        let concl = d.const_app(p.equiv, &[fjp, fjq]);
        let inner = d.arrow(heq_ty, concl);
        let with_qq = d.pi_fv(qq_fv, carrier, inner);
        let with_pp = d.pi_fv(pp_fv, carrier, with_qq);
        d.pi_fv(j_fv, nat, with_pp)
    };
    let hcong_fv = d.fresh_fvar();
    let hcong = d.kernel().fvar(hcong_fv);

    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);

    // hdom : ∀ j pt, le a pt → le pt b → le (abs (f j pt)) (mseq j).
    let hdom_ty = {
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let pt_fv = d.fresh_fvar();
        let pt = d.kernel().fvar(pt_fv);
        let fjpt = d.apply(f, &[j, pt]);
        let abs_fjpt = d.const_app(p.abs, &[fjpt]);
        let mj = d.apply(mseq, &[j]);
        let concl = d.const_app(p.le, &[abs_fjpt, mj]);
        let range_ax = d.const_app(p.le, &[a, pt]);
        let range_xb = d.const_app(p.le, &[pt, b]);
        let with_xb = d.arrow(range_xb, concl);
        let with_ax = d.arrow(range_ax, with_xb);
        let with_pt = d.pi_fv(pt_fv, carrier, with_ax);
        d.pi_fv(j_fv, nat, with_pt)
    };
    let hdom_fv = d.fresh_fvar();
    let hdom = d.kernel().fvar(hdom_fv);

    // hcauchy : ∀ pp qq, Within (seq (sumRange mseq pp) pp − seq (sumRange
    // mseq qq) qq) (natDivSucc k pp + natDivSucc k qq) -- the raw,
    // non-existential Cauchy witness for `mseq`'s own partial sums.
    let hcauchy_ty = {
        let pp_fv = d.fresh_fvar();
        let pp = d.kernel().fvar(pp_fv);
        let qq_fv = d.fresh_fvar();
        let qq = d.kernel().fvar(qq_fv);
        let sum_pp = d.const_app(p.sum_range, &[mseq, pp]);
        let sum_qq = d.const_app(p.sum_range, &[mseq, qq]);
        let left = sample(d, p, sum_pp, pp);
        let right = sample(d, p, sum_qq, qq);
        let diff = rsub(d, rat, left, right);
        let bpp = div_succ_at(d, p, k, pp);
        let bqq = div_succ_at(d, p, k, qq);
        let bound = radd(d, bpp, bqq);
        let claim = within(d, p, diff, bound);
        let over_qq = d.pi_fv(qq_fv, nat, claim);
        d.pi_fv(pp_fv, nat, over_qq)
    };
    let hcauchy_fv = d.fresh_fvar();
    let hcauchy = d.kernel().fvar(hcauchy_fv);

    // `F' := fun n pt => sumRange (fun j => f j pt) n` -- the conclusion's
    // own sequence-of-functions.
    let big_f = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let pt_fv = d.fresh_fvar();
        let pt = d.kernel().fvar(pt_fv);
        let f_pt = {
            let j_fv = d.fresh_fvar();
            let j = d.kernel().fvar(j_fv);
            let body = d.apply(f, &[j, pt]);
            d.lam_fv(j_fv, nat, body)
        };
        let body = d.const_app(p.sum_range, &[f_pt, n]);
        let with_pt = d.lam_fv(pt_fv, carrier, body);
        d.lam_fv(n_fv, nat, with_pt)
    };

    // --- one shared point `pt`, used both to build `G` (standalone,
    // total) and, reusing the SAME fvar, to build `spec`'s own binder --
    // see the section documentation for why `G` cannot depend on `hax`/
    // `hxb` and must route through the clamp instead.
    let pt_fv = d.fresh_fvar();
    let pt = d.kernel().fvar(pt_fv);

    let min_pt_b = d.const_app(p.min, &[pt, b]);
    let pt_clamped = d.const_app(p.max, &[a, min_pt_b]);

    let hax_c = d.lemma(p.le_max_left, &[a, min_pt_b]); // le a pt_clamped
    let hxb_c = {
        let min_le_right_pt_b = d.lemma(p.min_le_right, &[pt, b]); // le (min pt b) b
        d.lemma(p.max_le, &[a, min_pt_b, b, hab, min_le_right_pt_b]) // le pt_clamped b
    };

    let f_pt_clamped = {
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let body = d.apply(f, &[j, pt_clamped]);
        d.lam_fv(j_fv, nat, body)
    };
    let hyp1_c = {
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let body = d.apply(hdom, &[j, pt_clamped, hax_c, hxb_c]);
        d.lam_fv(j_fv, nat, body)
    };

    // `k_prime := k + 8`, eight bare `Nat.succ`s -- already fully reduced,
    // matching `series.rs::declare_sum_range_cauchy_of_dominated`'s own
    // choice (see that function's doc comment for why a `succ` tower rather
    // than the source theorem's own nested-`Nat.add` chain).
    let k_prime = {
        let mut kp = k;
        for _ in 0..8 {
            kp = d.succ(kp);
        }
        kp
    };

    // `case_proof : ∀ m n, Within (seq (sumRange f_pt_clamped m) m − seq
    // (sumRange f_pt_clamped n) n) (natDivSucc k_prime m + natDivSucc
    // k_prime n)` -- the `Nat.le_total` case split, verbatim in SHAPE to
    // `series.rs::declare_sum_range_cauchy_of_dominated`'s own `case_proof`,
    // independent in that `hcauchy` here is already raw (no `exists_elim`
    // needed).
    let case_proof = {
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let n2_fv = d.fresh_fvar();
        let n2 = d.kernel().fvar(n2_fv);

        let sum_fc_m = d.const_app(p.sum_range, &[f_pt_clamped, m]);
        let sum_fc_n = d.const_app(p.sum_range, &[f_pt_clamped, n2]);
        let y_m = sample(d, p, sum_fc_m, m);
        let z_n = sample(d, p, sum_fc_n, n2);
        let diff_mn = rsub(d, rat, y_m, z_n);
        let bm = div_succ_at(d, p, k_prime, m);
        let bn = div_succ_at(d, p, k_prime, n2);
        let bound_mn = radd(d, bm, bn);
        let claim_mn = within(d, p, diff_mn, bound_mn);

        let left_ty = d.le(m, n2);
        let right_ty = d.le(n2, m);
        let total_mn = {
            let name = d.prelude().le_total;
            d.const_app(name, &[m, n2])
        };

        let body = d.or_elim(
            left_ty,
            right_ty,
            claim_mn,
            total_mn,
            &|d, hmn| {
                let raw = d.lemma(
                    p.sum_range_cauchy_dominated_ordered_normalized,
                    &[f_pt_clamped, mseq, k, m, n2, hyp1_c, hcauchy, hmn],
                );
                let bound_nm = radd(d, bn, bm);
                let flipped = within_symm(d, p, z_n, y_m, bound_nm, raw);
                let comm_eq = d.lemma(rat.add_comm, &[bn, bm]);
                rat_eq_rewrite(d, bound_nm, bound_mn, comm_eq, flipped, &|d, t| {
                    within(d, p, diff_mn, t)
                })
            },
            &|d, hnm| {
                d.lemma(
                    p.sum_range_cauchy_dominated_ordered_normalized,
                    &[f_pt_clamped, mseq, k, n2, m, hyp1_c, hcauchy, hnm],
                )
            },
        );
        let over_n2 = d.lam_fv(n2_fv, nat, body);
        d.lam_fv(m_fv, nat, over_n2)
    };

    // `G pt := CReal.mk (speedup (diagonal (sumRange f_pt_clamped)) k_prime)
    // (regularity proof)` -- total, since `pt_clamped`/`hax_c`/`hxb_c`/
    // `case_proof` above never touched `hax`/`hxb`.
    let sum_fc_all = d.const_app(p.sum_range, &[f_pt_clamped]);
    let raw_pt = diagonal_seq(d, p, sum_fc_all);
    let kregular_proof_pt = kregular_of_cauchy_proof(d, p, raw_pt, k_prime, case_proof);
    let reg_proof_pt = d.const_app(p.regular_of_kregular, &[raw_pt, k_prime, kregular_proof_pt]);
    let speedup_term_pt = d.const_app(p.speedup, &[raw_pt, k_prime]);
    let g_pt = d.const_app(p.mk, &[speedup_term_pt, reg_proof_pt]);
    let sc_pt = d.const_app(p.speedup_close, &[raw_pt, k_prime, kregular_proof_pt]);
    let succ_k_prime = d.succ(k_prime);
    let one_nat = d.num(1);
    let k2 = NatOps::add(d, succ_k_prime, one_nat);

    let big_g = d.lam_fv(pt_fv, carrier, g_pt);

    // --- `spec`, reusing `pt_fv` so `apply(big_g, [pt])` and this file's
    // own reconstructed `g_pt` coincide exactly, not merely up to defeq.
    let (rate, spec) = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let hax_fv = d.fresh_fvar();
        let hax = d.kernel().fvar(hax_fv);
        let hxb_fv = d.fresh_fvar();
        let hxb = d.kernel().fvar(hxb_fv);

        let sc_pt_n = d.apply(sc_pt, &[n]);
        let bound_left_n = div_succ_at(d, p, succ_k_prime, n);
        let bound_right_n = div_succ_at(d, p, one_nat, n);
        let sc_n_bound = radd(d, bound_left_n, bound_right_n);
        let raw_pt_n = d.apply(raw_pt, &[n]);
        let speedup_n = d.apply(speedup_term_pt, &[n]);
        let diff_n = rsub(d, rat, raw_pt_n, speedup_n);

        let fuse = d.lemma(rat.nat_div_succ_add, &[succ_k_prime, one_nat, n]);
        let target_bound_n = div_succ_at(d, p, k2, n);
        let step_n = rat_eq_rewrite(d, sc_n_bound, target_bound_n, fuse, sc_pt_n, &|d, t| {
            within(d, p, diff_n, t)
        });
        // step_n : Within (raw_pt n − speedup_term_pt n) (natDivSucc k2 n)
        //        = Within (sample (sumRange f_pt_clamped n) n
        //                  − sample g_pt n) (natDivSucc k2 n), by beta/iota.

        let x_term = d.const_app(p.sum_range, &[f_pt_clamped, n]);
        let (rate, proof_clamped) = close_within_of_within_at(d, p, x_term, g_pt, n, k2, step_n);
        // proof_clamped : close_within x_term g_pt (natDivSucc rate n).

        // --- congruence bridge: `pt ~ pt_clamped`, then transport along
        // `hcong`/`sumRange_congr` to the UNCLAMPED sequence.
        let le_refl_pt = d.lemma(p.le_refl, &[pt]);
        let low_min = d.lemma(p.min_le_left, &[pt, b]); // le (min pt b) pt
        let high_min = d.lemma(p.le_min, &[pt, b, pt, le_refl_pt, hxb]); // le pt (min pt b)
        let e1 = d.lemma(p.equiv_of_le_le, &[min_pt_b, pt, low_min, high_min]);
        // e1 : Equiv (min pt b) pt

        let equiv_refl_a = d.lemma(p.equiv_refl, &[a]);
        let max_a_pt = d.const_app(p.max, &[a, pt]);
        let max_cong = d.lemma(p.max_congr, &[a, a, min_pt_b, pt, equiv_refl_a, e1]);
        // max_cong : Equiv pt_clamped max_a_pt

        let low_max = d.lemma(p.max_le, &[a, pt, pt, hax, le_refl_pt]); // le max_a_pt pt
        let high_max = d.lemma(p.le_max_right, &[a, pt]); // le pt max_a_pt
        let e2 = d.lemma(p.equiv_of_le_le, &[max_a_pt, pt, low_max, high_max]);
        // e2 : Equiv max_a_pt pt

        let hclamp_eq = d.lemma(p.equiv_trans, &[pt_clamped, max_a_pt, pt, max_cong, e2]);
        // hclamp_eq : Equiv pt_clamped pt

        let f_pt = {
            let j_fv = d.fresh_fvar();
            let j = d.kernel().fvar(j_fv);
            let body = d.apply(f, &[j, pt]);
            d.lam_fv(j_fv, nat, body)
        };
        let heq_pointwise = {
            let j_fv = d.fresh_fvar();
            let j = d.kernel().fvar(j_fv);
            let body = d.apply(hcong, &[j, pt_clamped, pt, hclamp_eq]);
            d.lam_fv(j_fv, nat, body)
        };
        let heq_sum = d.lemma(p.sum_range_congr, &[f_pt_clamped, f_pt, n, heq_pointwise]);
        // heq_sum : Equiv (sumRange f_pt_clamped n) (sumRange f_pt n)

        let sum_fpt_n = d.const_app(p.sum_range, &[f_pt, n]);
        let neg_g_pt = d.const_app(p.neg, &[g_pt]);
        let refl_neg_g_pt = d.lemma(p.equiv_refl, &[neg_g_pt]);
        let inner_before = d.const_app(p.add, &[x_term, neg_g_pt]);
        let inner_after = d.const_app(p.add, &[sum_fpt_n, neg_g_pt]);
        let add_cong = d.lemma(
            p.add_congr,
            &[
                x_term,
                sum_fpt_n,
                neg_g_pt,
                neg_g_pt,
                heq_sum,
                refl_neg_g_pt,
            ],
        );
        // add_cong : Equiv inner_before inner_after
        let abs_cong = d.lemma(p.abs_congr, &[inner_before, inner_after, add_cong]);
        // abs_cong : Equiv (abs inner_before) (abs inner_after)

        let final_bound = div_succ_at(d, p, rate, n);
        let rhs_embed = embed(d, p, final_bound);
        let refl_rhs = d.lemma(p.equiv_refl, &[rhs_embed]);
        let lhs_before = d.const_app(p.abs, &[inner_before]);
        let lhs_after = d.const_app(p.abs, &[inner_after]);
        let final_proof = d.lemma(
            p.le_congr,
            &[
                lhs_before,
                lhs_after,
                rhs_embed,
                rhs_embed,
                abs_cong,
                refl_rhs,
                proof_clamped,
            ],
        );
        // final_proof : close_within (sumRange f_pt n) g_pt (natDivSucc rate n)
        //             = close_within (F' n pt) (G pt) (natDivSucc rate n).

        let range_ax = d.const_app(p.le, &[a, pt]);
        let range_xb = d.const_app(p.le, &[pt, b]);
        let with_hxb = d.lam_fv(hxb_fv, range_xb, final_proof);
        let with_hax = d.lam_fv(hax_fv, range_ax, with_hxb);
        let with_pt = d.lam_fv(pt_fv, carrier, with_hax);
        let spec = d.lam_fv(n_fv, nat, with_pt);
        (rate, spec)
    };

    let mk_applied = d.const_app(p.uconv_mk, &[big_f, big_g, a, b, rate, spec]);

    let value = {
        let with_hcauchy = d.lam_fv(hcauchy_fv, hcauchy_ty, mk_applied);
        let with_hdom = d.lam_fv(hdom_fv, hdom_ty, with_hcauchy);
        let with_k = d.lam_fv(k_fv, nat, with_hdom);
        let with_hcong = d.lam_fv(hcong_fv, hcong_ty, with_k);
        let with_hab = d.lam_fv(hab_fv, hab_ty, with_hcong);
        let with_b = d.lam_fv(b_fv, carrier, with_hab);
        let with_a = d.lam_fv(a_fv, carrier, with_b);
        let with_mseq = d.lam_fv(mseq_fv, mseq_ty, with_a);
        d.lam_fv(f_fv, seq_ty, with_mseq)
    };
    let ty = {
        // `hab`/`hdom`/`hcauchy` are each genuinely referenced inside
        // `big_g` (via `hax_c`/`hxb_c`/`hyp1_c`/`case_proof`), so
        // `conclusion` mentions all three free variables and each must bind
        // with `pi_fv`, never `d.arrow` -- an `arrow` leaves the occurrence
        // inside `conclusion` unabstracted, `UnboundFVar` at kernel check
        // time. `hcong` is NOT referenced by `conclusion` (only by `spec`,
        // which is not part of the TYPE), so it alone stays `arrow`.
        let conclusion = uconv_ty(d, p, big_f, big_g, a, b);
        let after_hcauchy = d.pi_fv(hcauchy_fv, hcauchy_ty, conclusion);
        let after_hdom = d.pi_fv(hdom_fv, hdom_ty, after_hcauchy);
        let with_k = d.pi_fv(k_fv, nat, after_hdom);
        let after_hcong = d.arrow(hcong_ty, with_k);
        let after_hab = d.pi_fv(hab_fv, hab_ty, after_hcong);
        let with_b = d.pi_fv(b_fv, carrier, after_hab);
        let with_a = d.pi_fv(a_fv, carrier, with_b);
        let with_mseq = d.pi_fv(mseq_fv, mseq_ty, with_a);
        d.pi_fv(f_fv, seq_ty, with_mseq)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.weierstrass_m_test,
        uparams: vec![],
        ty,
        value,
    })
}

// ============================================================================
// Theorem: the Weierstrass M-test specialized to a bounded-coefficient power
// series -- `CReal.powerSeriesUniformConvergesOn`.
// ============================================================================
//
// `∀ c M, (∀ j, le (abs (c j)) M) → ∀ r, le zero r → ∀ k, (∀ pp qq, Within
// (seq (sumRange mseq pp) pp − seq (sumRange mseq qq) qq) (natDivSucc k pp +
// natDivSucc k qq)) → UniformConvergesOn (fun n x => sumRange (fun j =>
// powerSeriesTerm c j x) n) G zero r`, where `mseq j := mul M (pow r j)`.
//
// This is [`declare_weierstrass_m_test`] applied at `f := powerSeriesTerm
// c`, `a := zero`, `b := r`, `hab := hr0` (`le zero r`, reused directly --
// choosing `[0, r]` rather than `[−r, r]` means `hab` costs nothing beyond
// the domination hypothesis's own lower bound, where `[−r, r]` would need a
// separate `le (neg r) r` lemma from `le zero r`), `hcong :=
// CReal.powerSeriesTerm_congr c` and `hdom` built inline from
// `CReal.powerSeriesTerm_abs_le`. The dominating series' own raw Cauchy
// modulus `(k, …)` stays a direct parameter, exactly as
// `CReal.weierstrassMTest` itself takes one: `G` is built FROM `k` inside
// that theorem's own proof (see its module documentation), so a caller
// cannot supply a `Cauchy`-`Prop`-wrapped fact and have this declaration
// eliminate the existential internally -- `Exists.rec`'s target must not
// mention the witness, and here it would (through `G`). A caller obtains
// `(k, …)` from [`RatioTestNames::geom_scaled_cauchy_of_lt`] plus their own
// `Exists`-elimination, same as any other consumer of a `Cauchy` fact.
//
// `r < 1` is deliberately not a hypothesis: nothing in this construction
// needs it directly, and it is implicit in whatever Cauchy witness a caller
// can actually produce for `mseq`.
//
// The `ty` here is read off with [`crate::tc::Kernel::infer`] rather than
// hand-built: `weierstrassMTest`'s own conclusion embeds its limit `G`,
// which is a large expression this declaration has no reason to reconstruct
// by hand a second time (see [`declare_weierstrass_m_test`]'s own `ty`
// construction for how large that reconstruction is when done directly).

/// Admit `CReal.powerSeriesUniformConvergesOn`. See the section
/// documentation above for the route.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
pub(super) fn declare_power_series_uniform_converges(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = creal_ty(d, p);
    let coeff_ty = d.arrow(nat, carrier);
    let zero_c = d.kernel().const_(p.zero, vec![]);

    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);

    // hbound_ty : ∀ j, le (abs (c j)) m.
    let hbound_ty = {
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let cj = d.apply(c, &[j]);
        let abs_cj = d.const_app(p.abs, &[cj]);
        let body = d.const_app(p.le, &[abs_cj, m]);
        d.pi_fv(j_fv, nat, body)
    };
    let hbound_fv = d.fresh_fvar();
    let hbound = d.kernel().fvar(hbound_fv);

    let r_fv = d.fresh_fvar();
    let r = d.kernel().fvar(r_fv);
    let hr0_ty = d.const_app(p.le, &[zero_c, r]);
    let hr0_fv = d.fresh_fvar();
    let hr0 = d.kernel().fvar(hr0_fv);

    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);

    // mseq := λ n, mul m (pow r n) -- the dominating geometric series.
    let mseq = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let pow_r_n = d.const_app(p.pow, &[r, n]);
        let prod = d.const_app(p.mul, &[m, pow_r_n]);
        d.lam_fv(n_fv, nat, prod)
    };

    // hcauchy_ty : ∀ pp qq, Within (seq (sumRange mseq pp) pp − seq
    // (sumRange mseq qq) qq) (natDivSucc k pp + natDivSucc k qq) --
    // verbatim in SHAPE to `declare_weierstrass_m_test`'s own `hcauchy_ty`.
    let hcauchy_ty = {
        let pp_fv = d.fresh_fvar();
        let pp = d.kernel().fvar(pp_fv);
        let qq_fv = d.fresh_fvar();
        let qq = d.kernel().fvar(qq_fv);
        let sum_pp = d.const_app(p.sum_range, &[mseq, pp]);
        let sum_qq = d.const_app(p.sum_range, &[mseq, qq]);
        let left = sample(d, p, sum_pp, pp);
        let right = sample(d, p, sum_qq, qq);
        let diff = rsub(d, p.rat, left, right);
        let bpp = div_succ_at(d, p, k, pp);
        let bqq = div_succ_at(d, p, k, qq);
        let bound = radd(d, bpp, bqq);
        let claim = within(d, p, diff, bound);
        let over_qq = d.pi_fv(qq_fv, nat, claim);
        d.pi_fv(pp_fv, nat, over_qq)
    };
    let hcauchy_fv = d.fresh_fvar();
    let hcauchy = d.kernel().fvar(hcauchy_fv);

    // f := powerSeriesTerm c : Nat -> CReal -> CReal.
    let f = d.const_app(p.power_series_term, &[c]);
    // hcong := powerSeriesTerm_congr c : ∀ j p q, Equiv p q → Equiv (f j p)
    // (f j q).
    let hcong = d.const_app(p.power_series_term_congr, &[c]);
    // hab := hr0 (a := zero, b := r).
    let hab = hr0;

    // hdom : ∀ j pt, le zero pt → le pt r → le (abs (f j pt)) (mseq j).
    let hdom = {
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let pt_fv = d.fresh_fvar();
        let pt = d.kernel().fvar(pt_fv);
        let hax_fv = d.fresh_fvar();
        let hax = d.kernel().fvar(hax_fv);
        let hxb_fv = d.fresh_fvar();
        let hxb = d.kernel().fvar(hxb_fv);
        let inner = d.lemma(
            p.power_series_term_abs_le,
            &[c, m, hbound, pt, r, hax, hxb, j],
        );
        let hxb_ty = d.const_app(p.le, &[pt, r]);
        let hax_ty = d.const_app(p.le, &[zero_c, pt]);
        let with_hxb = d.lam_fv(hxb_fv, hxb_ty, inner);
        let with_hax = d.lam_fv(hax_fv, hax_ty, with_hxb);
        let with_pt = d.lam_fv(pt_fv, carrier, with_hax);
        d.lam_fv(j_fv, nat, with_pt)
    };

    let weierstrass_applied = d.lemma(
        p.weierstrass_m_test,
        &[f, mseq, zero_c, r, hab, hcong, k, hdom, hcauchy],
    );

    let value = {
        let with_hcauchy = d.lam_fv(hcauchy_fv, hcauchy_ty, weierstrass_applied);
        let with_k = d.lam_fv(k_fv, nat, with_hcauchy);
        let with_hr0 = d.lam_fv(hr0_fv, hr0_ty, with_k);
        let with_r = d.lam_fv(r_fv, carrier, with_hr0);
        let with_hbound = d.lam_fv(hbound_fv, hbound_ty, with_r);
        let with_m = d.lam_fv(m_fv, carrier, with_hbound);
        d.lam_fv(c_fv, coeff_ty, with_m)
    };

    let ty = d.kernel().infer(value)?;

    d.kernel().add_declaration(Declaration::Theorem {
        name: p.power_series_uniform_converges,
        uparams: vec![],
        ty,
        value,
    })
}

// =============================================================================
// `CReal.hasDerivative_uniform_limit` — the interchange of limit and derivative
// =============================================================================
//
// Sixteen declarations in this development conclude `HasDerivativeOn`, and
// until this one every one of them was a POINTWISE combinator
// (const/id/sq/neg/add/sub/smul/mul/pow/cube/chain/congr/integral_const): none
// took a limit hypothesis, and `uniform_limit_uniformly_continuous` was the
// only theorem anywhere that transported ANY property through a uniform limit.
//
// ## Why there is no finite-partial-sum shortcut
//
// Writing `Sₙ` for a member of the sequence and `G` for its uniform limit, the
// standard split of the derivative's own error term is
//
//   (G y − G x) − G'(x)(y−x)
//     = [(G y − G x) − (Sₙ y − Sₙ x)]        (A)
//     + [(Sₙ y − Sₙ x) − Sₙ'(x)(y−x)]        (B)
//     + [(Sₙ'(x) − G'(x))·(y−x)]             (C)
//
// (B) is `Sₙ`'s own `HasDerivativeOn.spec` and (C) is uniform convergence of
// the DERIVATIVES. (A) is the whole difficulty: uniform convergence of the
// FUNCTIONS bounds it by a CONSTANT `2δₙ`, while `deriv_spec_body`'s budget is
// `(1/(e+1))·|y − x|` quantified over every `y` within `1/(m e + 1)` of `x`,
// INCLUDING points arbitrarily close to it. No choice of `n` absorbs a constant
// into an `ε·|y − x|` budget, so the interchange is forced by the SHAPE of the
// spec and not by how the limit happens to be taken.
//
// (A) goes through a mean value estimate on the tail instead —
// `derivative.rs`'s `abs_diff_sub_le_of_deriv_bound`, which for every `k` gives
//
//   |(Fₖ y − Fₖ x) − (Sₙ y − Sₙ x)|  ≤  (r'/(k+1) + r'/(n+1))·|y − x|
//
// and `le_of_forall_le_add_small` removes the `k → ∞` slack. The two function
// legs `|G y − Fₖ y|` and `|Fₖ x − G x|` contribute `2r/(k+1)`, absorbed into
// the same rational budget because `|y − x| ≤ 1` (from the spec's own closeness
// hypothesis via `Rat.natDivSucc_le_one`) turns the remaining `r'/(k+1)·|y−x|`
// into `r'/(k+1)`.
//
// ## The accuracy bookkeeping
//
// A three-way split at `1/(3e+3)`, the shape `hasDerivative_mul` already
// performs. `sidx e := 3e+2`, so each leg is bounded by `1/(sidx e + 1)` and
// `Rat.natDivSucc_add` twice plus `Rat.natDivSucc_scale` at `c := 2` fuses the
// three back to `1/(e+1)`. That the scale lemma's own index `(c+1)·m + c` IS
// `3e+2` is why `sidx` is written as [`scaled_index`] at `k := 2` and not as a
// hand-built `Nat`: no separate identity is then needed, only the numerator
// bridge `Nat.add (Nat.add 1 1) 1 ≡ Nat.succ 2`, which is a bare `Eq.refl`
// under defeq (`Nat.add` recurses on its RIGHT argument, so both sides reduce).
//
// The sequence index is `nidx e := scaled_index r' (sidx e)`, which is
// [`weaken_rate`]'s index, so the derivative series' rate at `nidx e` is at most
// `1/(3e+3)` by that function's own proof, reused verbatim. The modulus is then
// simply `Sₙ`'s own modulus at the split accuracy — and because `deriv_spec_body`
// applies the modulus to `e` as a redex, the incoming closeness hypothesis lands
// in `HasDerivativeOn.spec`'s slot with nothing but beta.
//
// Nothing here inspects a sequence element: `Fₙ` and `Fₙ'` are opaque, and every
// fact used about them is one of the two `UniformConvergesOn.spec`s or the
// per-index `HasDerivativeOn`.

/// [`weaken_rate`]'s index alone, without building its proof term:
/// `(k+1)·target + k`. The two must agree, since that proof is applied at the
/// index this returns.
fn scaled_index(d: &mut IntDev<'_>, k: ExprId, target: ExprId) -> ExprId {
    let kp = d.succ(k);
    let product = NatOps::mul(d, kp, target);
    NatOps::add(d, product, k)
}

/// From `h : le (abs (add u (neg v))) (ofRat q)`, derive
/// `le (abs (add v (neg u))) (ofRat q)`.
///
/// Through the two-sided form, which is the only public route:
/// `Equiv (abs (neg x)) (abs x)` is not a declaration in this development, and
/// `CReal.abs` is deliberately one-sided. [`CRealPrelude::two_sided_of_abs_sub_le`]
/// and [`CRealPrelude::abs_le_of_two_sided`] are exact converses, so nothing is
/// lost.
fn abs_sub_flip(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    u: ExprId,
    v: ExprId,
    q: ExprId,
    h: ExprId,
) -> ExprId {
    let cq = embed(d, p, q);
    let v_q = cadd(d, p, v, cq);
    let u_q = cadd(d, p, u, cq);
    let l_ty = d.const_app(p.le, &[u, v_q]);
    let r_ty = d.const_app(p.le, &[v, u_q]);
    let both = d.lemma(p.two_sided_of_abs_sub_le, &[u, v, q, h]);
    let hl = d.and_left(l_ty, r_ty, both);
    let hr = d.and_right(l_ty, r_ty, both);
    d.lemma(p.abs_le_of_two_sided, &[v, u, q, hr, hl])
}

/// `le (mul u c) (mul v c)` from `hc0 : le zero c` and `huv : le u v` —
/// monotonicity of multiplication on the RIGHT, which this development has only
/// on the left ([`CRealPrelude::mul_le_mul_of_nonneg_left`]); two `mul_comm`
/// transports around it.
fn mul_right_mono(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    c: ExprId,
    u: ExprId,
    v: ExprId,
    hc0: ExprId,
    huv: ExprId,
) -> ExprId {
    let cu = cmul(d, p, c, u);
    let cv = cmul(d, p, c, v);
    let uc = cmul(d, p, u, c);
    let vc = cmul(d, p, v, c);
    let step = d.lemma(p.mul_le_mul_of_nonneg_left, &[c, u, v, hc0, huv]);
    let e1 = d.lemma(p.mul_comm, &[c, u]);
    let e2 = d.lemma(p.mul_comm, &[c, v]);
    d.lemma(p.le_congr, &[cu, uc, cv, vc, e1, e2, step])
}

/// `(rational, its embedding, le zero it)` for `natDivSucc k idx` —
/// `derivative.rs`'s own `nonneg_rat_bound` with an arbitrary numerator
/// EXPRESSION rather than a literal `u32`, since every numerator here is a
/// projected `UniformConvergesOn.rate`.
fn nonneg_bound(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    k: ExprId,
    idx: ExprId,
) -> (ExprId, ExprId, ExprId) {
    let q = div_succ_at(d, p, k, idx);
    let cq = embed(d, p, q);
    let rz = rzero(d, p.rat);
    let rat_nonneg = d.lemma(p.rat.zero_le_nat_div_succ, &[k, idx]);
    let proof = d.lemma(p.of_rat_le, &[rz, q, rat_nonneg]);
    (q, cq, proof)
}

/// Admit `CReal.hasDerivative_uniform_limit`. See
/// [`CRealPrelude::has_derivative_uniform_limit`] and the section comment above.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` from the final `Theorem` here
/// means the kernel **refused** the proof, not that a script gave up.
pub(super) fn declare_has_derivative_uniform_limit(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let seqfn = seq_fn_ty(d, p);
    let funct = fn_ty(d, p);
    let nat = d.nat_ty();
    let rat = p.rat;
    let one_nat = d.num(1);
    let two_nat = d.num(2);
    let zero_nat = d.num(0);
    let zero_c = czero(d, p);
    let one_c = d.kernel().const_(p.one, vec![]);

    let fns_fv = d.fresh_fvar();
    let fns = d.kernel().fvar(fns_fv);
    let fnsp_fv = d.fresh_fvar();
    let fnsp = d.kernel().fvar(fnsp_fv);
    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let gp_fv = d.fresh_fvar();
    let gp = d.kernel().fvar(gp_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);

    // hall : ∀ n, HasDerivativeOn (F n) (F' n) a b.
    let hall_ty = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let fn_n = d.apply(fns, &[n]);
        let fnp_n = d.apply(fnsp, &[n]);
        let body = hd_ty(d, p, fn_n, fnp_n, a, b);
        d.pi_fv(n_fv, nat, body)
    };
    let hall_fv = d.fresh_fvar();
    let hall = d.kernel().fvar(hall_fv);

    let hg_ty = uconv_ty(d, p, fns, g, a, b);
    let hg_fv = d.fresh_fvar();
    let hg = d.kernel().fvar(hg_fv);
    let hgp_ty = uconv_ty(d, p, fnsp, gp, a, b);
    let hgp_fv = d.fresh_fvar();
    let hgp = d.kernel().fvar(hgp_fv);

    let rr = d.const_app(p.uconv_rate, &[fns, g, a, b, hg]);
    let rrp = d.const_app(p.uconv_rate, &[fnsp, gp, a, b, hgp]);

    // --- the modulus ---------------------------------------------------------
    let modulus = {
        let e_fv = d.fresh_fvar();
        let e = d.kernel().fvar(e_fv);
        let sidx = scaled_index(d, two_nat, e);
        let nidx = scaled_index(d, rrp, sidx);
        let fn_n = d.apply(fns, &[nidx]);
        let fnp_n = d.apply(fnsp, &[nidx]);
        let hdn = d.apply(hall, &[nidx]);
        let body = d.const_app(p.hd_modulus, &[fn_n, fnp_n, a, b, hdn, sidx]);
        d.lam_fv(e_fv, nat, body)
    };

    // --- the spec's binders --------------------------------------------------
    let e_fv = d.fresh_fvar();
    let e = d.kernel().fvar(e_fv);
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let y_fv = d.fresh_fvar();
    let y = d.kernel().fvar(y_fv);

    let hax_ty = d.const_app(p.le, &[a, x]);
    let hax_fv = d.fresh_fvar();
    let hax = d.kernel().fvar(hax_fv);
    let hxb_ty = d.const_app(p.le, &[x, b]);
    let hxb_fv = d.fresh_fvar();
    let hxb = d.kernel().fvar(hxb_fv);
    let hay_ty = d.const_app(p.le, &[a, y]);
    let hay_fv = d.fresh_fvar();
    let hay = d.kernel().fvar(hay_fv);
    let hyb_ty = d.const_app(p.le, &[y, b]);
    let hyb_fv = d.fresh_fvar();
    let hyb = d.kernel().fvar(hyb_fv);

    let nx = cneg(d, p, x);
    let dy = cadd(d, p, y, nx);
    let w = cabs(d, p, dy);
    let w_nonneg = d.lemma(p.abs_nonneg, &[dy]);
    let refl_w = d.lemma(p.le_refl, &[w]);

    let mod_e = d.apply(modulus, &[e]);
    let close_rat = div_succ_at(d, p, one_nat, mod_e);
    let close_bound = embed(d, p, close_rat);
    let hclose_ty = d.const_app(p.le, &[w, close_bound]);
    let hclose_fv = d.fresh_fvar();
    let hclose = d.kernel().fvar(hclose_fv);

    let sidx = scaled_index(d, two_nat, e);
    let q3 = div_succ_at(d, p, one_nat, sidx);
    let cq3 = embed(d, p, q3);
    let bnd3 = cmul(d, p, cq3, w);
    let nidx = scaled_index(d, rrp, sidx);
    let sfn = d.apply(fns, &[nidx]);
    let sfnp = d.apply(fnsp, &[nidx]);
    let hdn = d.apply(hall, &[nidx]);

    // `|y − x| ≤ 1`, which is what lets leg (A)'s k-dependent slack be paid in
    // a purely rational budget.
    let one_rat = div_succ_at(d, p, one_nat, zero_nat);
    let hw1_rat = d.lemma(rat.nat_div_succ_le_one, &[mod_e]);
    let hw1_emb = d.lemma(p.of_rat_le, &[close_rat, one_rat, hw1_rat]);
    let hw_le_one = d.lemma(p.le_trans, &[w, close_bound, one_c, hclose, hw1_emb]);

    // --- leg (B): the chosen member's own spec -------------------------------
    let leg_b = d.const_app(
        p.hd_spec,
        &[sfn, sfnp, a, b, hdn, sidx, x, y, hax, hxb, hay, hyb, hclose],
    );
    let sfn_y = d.apply(sfn, &[y]);
    let sfn_x = d.apply(sfn, &[x]);
    let n_sfn_x = cneg(d, p, sfn_x);
    let v_gap = cadd(d, p, sfn_y, n_sfn_x);
    let n_v_gap = cneg(d, p, v_gap);
    let sfnp_x = d.apply(sfnp, &[x]);
    let sfnp_dy = cmul(d, p, sfnp_x, dy);
    let n_sfnp_dy = cneg(d, p, sfnp_dy);
    let eb = cadd(d, p, v_gap, n_sfnp_dy);

    // --- leg (C): uniform convergence of the derivatives, at `x` -------------
    let gp_x = d.apply(gp, &[x]);
    let qc = div_succ_at(d, p, rrp, nidx);
    let hc0 = d.const_app(p.uconv_spec, &[fnsp, gp, a, b, hgp, nidx, x, hax, hxb]);
    let (_, hrate) = weaken_rate(d, p, rrp, sidx);
    let hc1 = weaken_close_within(d, p, sfnp_x, gp_x, qc, q3, hc0, hrate);
    let n_gp_x = cneg(d, p, gp_x);
    let cdiff = cadd(d, p, sfnp_x, n_gp_x);
    let leg_c = d.lemma(p.abs_mul_le_of_bounds, &[cdiff, dy, cq3, w, hc1, refl_w]);
    let ec = cmul(d, p, cdiff, dy);

    // `ec ~ S'(x)·(y−x) − G'(x)·(y−x)`, the shape the telescope consumes.
    let gp_dy = cmul(d, p, gp_x, dy);
    let n_gp_dy = cneg(d, p, gp_dy);
    let q_term = cadd(d, p, sfnp_dy, n_gp_dy);
    let ec_step1 = right_distrib(d, p, sfnp_x, n_gp_x, dy);
    let ngp_dy = cmul(d, p, n_gp_x, dy);
    let ec_mid = cadd(d, p, sfnp_dy, ngp_dy);
    let refl_sfnp_dy = erefl(d, p, sfnp_dy);
    let neg_mul = neg_mul_equiv_left(d, p, gp_x, dy);
    let ec_step2 = d.lemma(
        p.add_congr,
        &[sfnp_dy, sfnp_dy, ngp_dy, n_gp_dy, refl_sfnp_dy, neg_mul],
    );
    let ec_eq = echain(d, p, ec, &[(ec_mid, ec_step1), (q_term, ec_step2)]);
    let ec_eq_symm = esymm(d, p, ec, q_term, ec_eq);
    let leg_q = abs_le_of_equiv(d, p, q_term, ec, bnd3, ec_eq_symm, leg_c);

    // --- leg (A): the limit's increment against the chosen member's ----------
    let g_y = d.apply(g, &[y]);
    let g_x = d.apply(g, &[x]);
    let n_g_x = cneg(d, p, g_x);
    let u_gap = cadd(d, p, g_y, n_g_x);
    let ea = cadd(d, p, u_gap, n_v_gap);
    let abs_ea = cabs(d, p, ea);

    let inner = {
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let rr2 = NatOps::add(d, rr, rr);
        let sumr = NatOps::add(d, rr2, rrp);
        let (kidx, hkrate) = weaken_rate(d, p, sumr, j);
        let kfn = d.apply(fns, &[kidx]);
        let kfnp = d.apply(fnsp, &[kidx]);
        let hdk = d.apply(hall, &[kidx]);

        let kfn_y = d.apply(kfn, &[y]);
        let kfn_x = d.apply(kfn, &[x]);
        let n_kfn_x = cneg(d, p, kfn_x);
        let vk_gap = cadd(d, p, kfn_y, n_kfn_x);

        // (1) |U − Vₖ| ≤ 2·(r/(k+1)).
        let (qr, cqr, _) = nonneg_bound(d, p, rr, kidx);
        let hraw_y = d.const_app(p.uconv_spec, &[fns, g, a, b, hg, kidx, y, hay, hyb]);
        let ht1 = abs_sub_flip(d, p, kfn_y, g_y, qr, hraw_y);
        let hraw_x = d.const_app(p.uconv_spec, &[fns, g, a, b, hg, kidx, x, hax, hxb]);
        let n_kfn_y = cneg(d, p, kfn_y);
        let t1 = cadd(d, p, g_y, n_kfn_y);
        let w2 = cadd(d, p, g_x, n_kfn_x);
        let n_w2 = cneg(d, p, w2);
        let kfn_x_gx = cadd(d, p, kfn_x, n_g_x);
        let flip_w2 = d.lemma(p.neg_sub_swap, &[g_x, kfn_x]);
        let hw2n = abs_le_of_equiv(d, p, n_w2, kfn_x_gx, cqr, flip_w2, hraw_x);

        let t1_w2 = cadd(d, p, t1, n_w2);
        let abs_t1 = cabs(d, p, t1);
        let abs_nw2 = cabs(d, p, n_w2);
        let abs_pair = cadd(d, p, abs_t1, abs_nw2);
        let two_qr = cadd(d, p, cqr, cqr);
        let tri1 = d.lemma(p.abs_add_le, &[t1, n_w2]);
        let sum1 = d.lemma(p.add_le_add, &[abs_t1, cqr, abs_nw2, cqr, ht1, hw2n]);
        let abs_t1w2 = cabs(d, p, t1_w2);
        let h1a = d.lemma(p.le_trans, &[abs_t1w2, abs_pair, two_qr, tri1, sum1]);
        let n_vk_gap = cneg(d, p, vk_gap);
        let u_vk = cadd(d, p, u_gap, n_vk_gap);
        let swap1 = swap_middle_pair(d, p, g_y, g_x, kfn_y, kfn_x);
        let h_uvk = abs_le_of_equiv(d, p, u_vk, t1_w2, two_qr, swap1, h1a);

        // (2) |Vₖ − V| ≤ (r'/(k+1) + r'/(n+1))·|y − x| — the tail estimate.
        let (_, cqpk, hqpk0) = nonneg_bound(d, p, rrp, kidx);
        let (qpn, cqpn, hqpn0) = nonneg_bound(d, p, rrp, nidx);
        let mm = cadd(d, p, cqpk, cqpn);
        let zz = cadd(d, p, zero_c, zero_c);
        let sum_nonneg = d.lemma(p.add_le_add, &[zero_c, cqpk, zero_c, cqpn, hqpk0, hqpn0]);
        let refl_mm = erefl(d, p, mm);
        let az = d.lemma(p.add_zero, &[zero_c]);
        let hm0 = d.lemma(p.le_congr, &[zz, zero_c, mm, mm, az, refl_mm, sum_nonneg]);

        let hgap = {
            let z_fv = d.fresh_fvar();
            let z = d.kernel().fvar(z_fv);
            let haz_ty = d.const_app(p.le, &[a, z]);
            let haz_fv = d.fresh_fvar();
            let haz = d.kernel().fvar(haz_fv);
            let hzb_ty = d.const_app(p.le, &[z, b]);
            let hzb_fv = d.fresh_fvar();
            let hzb = d.kernel().fvar(hzb_fv);

            let kfnp_z = d.apply(kfnp, &[z]);
            let sfnp_z = d.apply(sfnp, &[z]);
            let gp_z = d.apply(gp, &[z]);
            let n_gp_z = cneg(d, p, gp_z);
            let n_sfnp_z = cneg(d, p, sfnp_z);
            let left = cadd(d, p, kfnp_z, n_gp_z);
            let right = cadd(d, p, gp_z, n_sfnp_z);
            let whole = cadd(d, p, kfnp_z, n_sfnp_z);

            let hk = d.const_app(p.uconv_spec, &[fnsp, gp, a, b, hgp, kidx, z, haz, hzb]);
            let hnraw = d.const_app(p.uconv_spec, &[fnsp, gp, a, b, hgp, nidx, z, haz, hzb]);
            let hn = abs_sub_flip(d, p, sfnp_z, gp_z, qpn, hnraw);

            let pairsum = cadd(d, p, left, right);
            let abs_left = cabs(d, p, left);
            let abs_right = cabs(d, p, right);
            let abs_pair2 = cadd(d, p, abs_left, abs_right);
            let tri2 = d.lemma(p.abs_add_le, &[left, right]);
            let sum2 = d.lemma(p.add_le_add, &[abs_left, cqpk, abs_right, cqpn, hk, hn]);
            let abs_pairsum = cabs(d, p, pairsum);
            let hz = d.lemma(p.le_trans, &[abs_pairsum, abs_pair2, mm, tri2, sum2]);
            let cm = cancel_middle(d, p, kfnp_z, gp_z, sfnp_z);
            let cm_symm = esymm(d, p, pairsum, whole, cm);
            let body = abs_le_of_equiv(d, p, whole, pairsum, mm, cm_symm, hz);

            let with_hzb = d.lam_fv(hzb_fv, hzb_ty, body);
            let with_haz = d.lam_fv(haz_fv, haz_ty, with_hzb);
            d.lam_fv(z_fv, carrier, with_haz)
        };

        let h_tail = d.const_app(
            p.abs_diff_sub_le_of_deriv_bound,
            &[
                kfn, kfnp, sfn, sfnp, a, b, hdk, hdn, mm, hm0, hgap, x, y, hax, hxb, hay, hyb,
            ],
        );
        let vk_v = cadd(d, p, vk_gap, n_v_gap);
        let mm_w = cmul(d, p, mm, w);

        // (3) assemble EA from the two legs.
        let sum_a = cadd(d, p, u_vk, vk_v);
        let abs_uvk = cabs(d, p, u_vk);
        let abs_vkv = cabs(d, p, vk_v);
        let abs_pair3 = cadd(d, p, abs_uvk, abs_vkv);
        let bnd_a = cadd(d, p, two_qr, mm_w);
        let tri3 = d.lemma(p.abs_add_le, &[u_vk, vk_v]);
        let sum3 = d.lemma(
            p.add_le_add,
            &[abs_uvk, two_qr, abs_vkv, mm_w, h_uvk, h_tail],
        );
        let abs_suma = cabs(d, p, sum_a);
        let ha0 = d.lemma(p.le_trans, &[abs_suma, abs_pair3, bnd_a, tri3, sum3]);
        let cm_a = cancel_middle(d, p, u_gap, vk_gap, v_gap);
        let cm_a_symm = esymm(d, p, sum_a, ea, cm_a);
        let ha1 = abs_le_of_equiv(d, p, ea, sum_a, bnd_a, cm_a_symm, ha0);

        // (4) `2r/(k+1) + (r'/(k+1) + r'/(n+1))·|y−x| ≤ Q₃·|y−x| + 1/(j+1)`.
        let cqpk_w = cmul(d, p, cqpk, w);
        let cqpn_w = cmul(d, p, cqpn, w);
        let split_mw = right_distrib(d, p, cqpk, cqpn, w);
        let sum_mw = cadd(d, p, cqpk_w, cqpn_w);

        let cqpk_one = cmul(d, p, cqpk, one_c);
        let step_k = d.lemma(
            p.mul_le_mul_of_nonneg_left,
            &[cqpk, w, one_c, hqpk0, hw_le_one],
        );
        let mul_one_k = d.lemma(p.mul_one, &[cqpk]);
        let refl_cqpkw = erefl(d, p, cqpk_w);
        let hk_le = d.lemma(
            p.le_congr,
            &[
                cqpk_w, cqpk_w, cqpk_one, cqpk, refl_cqpkw, mul_one_k, step_k,
            ],
        );

        let (_, hrate2) = weaken_rate(d, p, rrp, sidx);
        let hq_le = d.lemma(p.of_rat_le, &[qpn, q3, hrate2]);
        let hn_le = mul_right_mono(d, p, w, cqpn, cq3, w_nonneg, hq_le);

        let sum_target = cadd(d, p, cqpk, bnd3);
        let sum_step = d.lemma(p.add_le_add, &[cqpk_w, cqpk, cqpn_w, bnd3, hk_le, hn_le]);
        let refl_sum_target = erefl(d, p, sum_target);
        let split_symm = esymm(d, p, mm_w, sum_mw, split_mw);
        let hmw = d.lemma(
            p.le_congr,
            &[
                sum_mw,
                mm_w,
                sum_target,
                sum_target,
                split_symm,
                refl_sum_target,
                sum_step,
            ],
        );

        let refl_two_qr = d.lemma(p.le_refl, &[two_qr]);
        let bnd_a2 = cadd(d, p, two_qr, sum_target);
        let ha2_step = d.lemma(
            p.add_le_add,
            &[two_qr, two_qr, mm_w, sum_target, refl_two_qr, hmw],
        );
        let ha2 = d.lemma(p.le_trans, &[abs_ea, bnd_a, bnd_a2, ha1, ha2_step]);

        // Regroup `2r/(k+1) + (Q'ₖ + Q₃·|y−x|)` as `Q₃·|y−x| + (2r/(k+1) + Q'ₖ)`.
        let xy_sum = cadd(d, p, two_qr, cqpk);
        let assoc = d.lemma(p.add_assoc, &[two_qr, cqpk, bnd3]);
        let regroup_l = cadd(d, p, xy_sum, bnd3);
        let assoc_symm = esymm(d, p, regroup_l, bnd_a2, assoc);
        let regroup_r = cadd(d, p, bnd3, xy_sum);
        let comm = d.lemma(p.add_comm, &[xy_sum, bnd3]);
        let regroup = echain(d, p, bnd_a2, &[(regroup_l, assoc_symm), (regroup_r, comm)]);
        let refl_abs_ea = erefl(d, p, abs_ea);
        let ha3 = d.lemma(
            p.le_congr,
            &[abs_ea, abs_ea, bnd_a2, regroup_r, refl_abs_ea, regroup, ha2],
        );

        // `2r/(k+1) + Q'ₖ ~ ofRat ((2r + r')/(k+1)) ≤ ofRat (1/(j+1))`.
        let sum_qr = radd(d, qr, qr);
        let dq2 = div_succ_at(d, p, rr2, kidx);
        let eq_a = d.lemma(rat.nat_div_succ_add, &[rr, rr, kidx]);
        let two_qr_eq0 = d.lemma(p.of_rat_add, &[qr, qr]);
        let two_qr_eq = rat_eq_rewrite(d, sum_qr, dq2, eq_a, two_qr_eq0, &|d, t| {
            let et = embed(d, p, t);
            d.const_app(p.equiv, &[two_qr, et])
        });
        let cdq2 = embed(d, p, dq2);
        let refl_cqpk = erefl(d, p, cqpk);
        let mid_xy = cadd(d, p, cdq2, cqpk);
        let xy_step1 = d.lemma(
            p.add_congr,
            &[two_qr, cdq2, cqpk, cqpk, two_qr_eq, refl_cqpk],
        );
        let qpk_rat = div_succ_at(d, p, rrp, kidx);
        let sum_dq2 = radd(d, dq2, qpk_rat);
        let dsum = div_succ_at(d, p, sumr, kidx);
        let eq_b = d.lemma(rat.nat_div_succ_add, &[rr2, rrp, kidx]);
        let xy_step2a = d.lemma(p.of_rat_add, &[dq2, qpk_rat]);
        let xy_step2 = rat_eq_rewrite(d, sum_dq2, dsum, eq_b, xy_step2a, &|d, t| {
            let et = embed(d, p, t);
            d.const_app(p.equiv, &[mid_xy, et])
        });
        let cdsum = embed(d, p, dsum);
        let xy_eq = echain(d, p, xy_sum, &[(mid_xy, xy_step1), (cdsum, xy_step2)]);
        let xy_le_eq = d.lemma(p.le_of_equiv, &[xy_sum, cdsum, xy_eq]);
        let qj = div_succ_at(d, p, one_nat, j);
        let cqj = embed(d, p, qj);
        let emb_kj = d.lemma(p.of_rat_le, &[dsum, qj, hkrate]);
        let xy_le = d.lemma(p.le_trans, &[xy_sum, cdsum, cqj, xy_le_eq, emb_kj]);

        let refl_bnd3 = d.lemma(p.le_refl, &[bnd3]);
        let target_j = cadd(d, p, bnd3, cqj);
        let final_step = d.lemma(p.add_le_add, &[bnd3, bnd3, xy_sum, cqj, refl_bnd3, xy_le]);
        let body = d.lemma(p.le_trans, &[abs_ea, regroup_r, target_j, ha3, final_step]);
        d.lam_fv(j_fv, nat, body)
    };
    let leg_a = d.lemma(p.le_of_forall_le_add_small, &[abs_ea, bnd3, inner]);

    // --- the three-way telescope --------------------------------------------
    let u_minus_sd = cadd(d, p, u_gap, n_sfnp_dy);
    let s1 = cadd(d, p, ea, eb);
    let abs_eb = cabs(d, p, eb);
    let abs_s1 = cabs(d, p, s1);
    let pair1 = cadd(d, p, abs_ea, abs_eb);
    let two_bnd3 = cadd(d, p, bnd3, bnd3);
    let tri_1 = d.lemma(p.abs_add_le, &[ea, eb]);
    let sum_1 = d.lemma(p.add_le_add, &[abs_ea, bnd3, abs_eb, bnd3, leg_a, leg_b]);
    let hs1 = d.lemma(p.le_trans, &[abs_s1, pair1, two_bnd3, tri_1, sum_1]);
    let cm1 = cancel_middle(d, p, u_gap, v_gap, sfnp_dy);
    let cm1_symm = esymm(d, p, s1, u_minus_sd, cm1);
    let hp = abs_le_of_equiv(d, p, u_minus_sd, s1, two_bnd3, cm1_symm, hs1);

    let s2 = cadd(d, p, u_minus_sd, q_term);
    let abs_p = cabs(d, p, u_minus_sd);
    let abs_q = cabs(d, p, q_term);
    let pair2 = cadd(d, p, abs_p, abs_q);
    let three_bnd3 = cadd(d, p, two_bnd3, bnd3);
    let abs_s2 = cabs(d, p, s2);
    let tri_2 = d.lemma(p.abs_add_le, &[u_minus_sd, q_term]);
    let sum_2 = d.lemma(p.add_le_add, &[abs_p, two_bnd3, abs_q, bnd3, hp, leg_q]);
    let hs2 = d.lemma(p.le_trans, &[abs_s2, pair2, three_bnd3, tri_2, sum_2]);
    let cm2 = cancel_middle(d, p, u_gap, sfnp_dy, gp_dy);
    let err = cadd(d, p, u_gap, n_gp_dy);
    let cm2_symm = esymm(d, p, s2, err, cm2);
    let herr = abs_le_of_equiv(d, p, err, s2, three_bnd3, cm2_symm, hs2);

    // --- fuse three copies of `1/(3e+3)` back to `1/(e+1)` -------------------
    let two_cq3 = cadd(d, p, cq3, cq3);
    let two_cq3_w = cmul(d, p, two_cq3, w);
    let fuse1 = right_distrib(d, p, cq3, cq3, w);
    let fuse1_symm = esymm(d, p, two_cq3_w, two_bnd3, fuse1);
    let refl_bnd3b = erefl(d, p, bnd3);
    let fuse_step1 = d.lemma(
        p.add_congr,
        &[two_bnd3, two_cq3_w, bnd3, bnd3, fuse1_symm, refl_bnd3b],
    );
    let three_cq3 = cadd(d, p, two_cq3, cq3);
    let three_cq3_w = cmul(d, p, three_cq3, w);
    let mid_fuse = cadd(d, p, two_cq3_w, bnd3);
    let fuse2 = right_distrib(d, p, two_cq3, cq3, w);
    let fuse_step2 = esymm(d, p, three_cq3_w, mid_fuse, fuse2);

    let n11 = NatOps::add(d, one_nat, one_nat);
    let d2 = div_succ_at(d, p, n11, sidx);
    let sum_q3a = radd(d, q3, q3);
    let eq_c = d.lemma(rat.nat_div_succ_add, &[one_nat, one_nat, sidx]);
    let two_cq3_eq0 = d.lemma(p.of_rat_add, &[q3, q3]);
    let two_cq3_eq = rat_eq_rewrite(d, sum_q3a, d2, eq_c, two_cq3_eq0, &|d, t| {
        let et = embed(d, p, t);
        d.const_app(p.equiv, &[two_cq3, et])
    });
    let cd2 = embed(d, p, d2);
    let refl_cq3 = erefl(d, p, cq3);
    let mid3 = cadd(d, p, cd2, cq3);
    let three_step1 = d.lemma(p.add_congr, &[two_cq3, cd2, cq3, cq3, two_cq3_eq, refl_cq3]);
    let n111 = NatOps::add(d, n11, one_nat);
    let d3a = div_succ_at(d, p, n111, sidx);
    let sum_d2 = radd(d, d2, q3);
    let eq_d = d.lemma(rat.nat_div_succ_add, &[n11, one_nat, sidx]);
    let three_step2a = d.lemma(p.of_rat_add, &[d2, q3]);
    let three_step2 = rat_eq_rewrite(d, sum_d2, d3a, eq_d, three_step2a, &|d, t| {
        let et = embed(d, p, t);
        d.const_app(p.equiv, &[mid3, et])
    });
    let cd3a = embed(d, p, d3a);
    let three_eq0 = echain(d, p, three_cq3, &[(mid3, three_step1), (cd3a, three_step2)]);

    // `Nat.add (Nat.add 1 1) 1 ≡ Nat.succ 2` — a bare `Eq.refl` under defeq,
    // exactly `weaken_rate`'s own numerator bridge.
    let three_expr = d.succ(two_nat);
    let bridge = NatOps::refl(d, n111);
    let three_eq1 = nat_rewrite_prop(d, n111, three_expr, bridge, three_eq0, &|d, t| {
        let bound = div_succ_at(d, p, t, sidx);
        let et = embed(d, p, bound);
        d.const_app(p.equiv, &[three_cq3, et])
    });
    let d3 = div_succ_at(d, p, three_expr, sidx);
    let q1e = div_succ_at(d, p, one_nat, e);
    let eq_scale = d.lemma(rat.nat_div_succ_scale, &[two_nat, e]);
    let three_eq = rat_eq_rewrite(d, d3, q1e, eq_scale, three_eq1, &|d, t| {
        let et = embed(d, p, t);
        d.const_app(p.equiv, &[three_cq3, et])
    });
    let cq1e = embed(d, p, q1e);
    let refl_w2 = erefl(d, p, w);
    let fuse_step3 = d.lemma(p.mul_congr, &[three_cq3, cq1e, w, w, three_eq, refl_w2]);
    let goal_bound = cmul(d, p, cq1e, w);
    let fuse = echain(
        d,
        p,
        three_bnd3,
        &[
            (mid_fuse, fuse_step1),
            (three_cq3_w, fuse_step2),
            (goal_bound, fuse_step3),
        ],
    );
    let abs_err = cabs(d, p, err);
    let refl_abs_err = erefl(d, p, abs_err);
    let spec_body_proof = d.lemma(
        p.le_congr,
        &[
            abs_err,
            abs_err,
            three_bnd3,
            goal_bound,
            refl_abs_err,
            fuse,
            herr,
        ],
    );

    let spec = {
        let with_hclose = d.lam_fv(hclose_fv, hclose_ty, spec_body_proof);
        let with_hyb = d.lam_fv(hyb_fv, hyb_ty, with_hclose);
        let with_hay = d.lam_fv(hay_fv, hay_ty, with_hyb);
        let with_hxb = d.lam_fv(hxb_fv, hxb_ty, with_hay);
        let with_hax = d.lam_fv(hax_fv, hax_ty, with_hxb);
        let with_y = d.lam_fv(y_fv, carrier, with_hax);
        let with_x = d.lam_fv(x_fv, carrier, with_y);
        d.lam_fv(e_fv, nat, with_x)
    };

    let witness = d.const_app(p.hd_mk, &[g, gp, a, b, modulus, spec]);

    let value = {
        let with_hgp = d.lam_fv(hgp_fv, hgp_ty, witness);
        let with_hg = d.lam_fv(hg_fv, hg_ty, with_hgp);
        let with_hall = d.lam_fv(hall_fv, hall_ty, with_hg);
        let with_b = d.lam_fv(b_fv, carrier, with_hall);
        let with_a = d.lam_fv(a_fv, carrier, with_b);
        let with_gp = d.lam_fv(gp_fv, funct, with_a);
        let with_g = d.lam_fv(g_fv, funct, with_gp);
        let with_fnsp = d.lam_fv(fnsp_fv, seqfn, with_g);
        d.lam_fv(fns_fv, seqfn, with_fnsp)
    };
    let ty = {
        let concl = hd_ty(d, p, g, gp, a, b);
        let after_hgp = d.arrow(hgp_ty, concl);
        let after_hg = d.arrow(hg_ty, after_hgp);
        let after_hall = d.arrow(hall_ty, after_hg);
        let over_b = d.pi_fv(b_fv, carrier, after_hall);
        let over_a = d.pi_fv(a_fv, carrier, over_b);
        let over_gp = d.pi_fv(gp_fv, funct, over_a);
        let over_g = d.pi_fv(g_fv, funct, over_gp);
        let over_fnsp = d.pi_fv(fnsp_fv, seqfn, over_g);
        d.pi_fv(fns_fv, seqfn, over_fnsp)
    };

    d.kernel().add_declaration(Declaration::Theorem {
        name: p.has_derivative_uniform_limit,
        uparams: vec![],
        ty,
        value,
    })
}

// =============================================================================
// `CReal.converges_of_abs_diff_le` -- the REAL-valued convergence criterion,
// bridged down to `CReal.Converges`'s own canonical-sample form.
//
// This is the `Converges` sibling of `creal/ivt.rs`'s
// `CReal.cauchy_of_abs_diff_le`, and it closes the gap
// `docs/plan/status/175-pi-r2b.md` named as the last structural piece under
// pi rung 2: `UniformConvergesOn.spec` (and every `weierstrassMTest`
// consumer) hands back a `close_within`-shaped fact,
// `le (abs (add (f n) (neg L))) (ofRat (natDivSucc K n))`, while
// `CReal.Converges f L` is stated on the RATIONAL representatives,
// `exists K, forall n, Within (seq (f n) n - seq L n) (natDivSucc K n)`.
// Nothing crossed that gap in this direction: `close_within_of_within` and
// `close_within_of_within_indexed` (this file) run the OTHER way, and
// `converges_of_close`/`converges_of_scaled_cauchy`
// (`creal/convergence.rs`) both already start from a `Within`.
//
// **The `CReal.add` index shift is real but it is NOT this bridge's
// obligation to discharge by hand**, which is what an earlier sizing of this
// task (as "a third general bridge, comparable in size to `converges_add`'s
// own construction") over-estimated: `CReal.sharedIndexToCanonical`
// (`creal/integral.rs`) already IS that index-shift regularity bridge,
// stated generically in both reals and in the bound function, and
// `cauchy_of_abs_diff_le` already demonstrated the composition. What is new
// here is only the arithmetic, and at a single shared index it is strictly
// SMALLER than the Cauchy case's:
//
//   1. `le_abs_self`/`neg_le_abs` + `le_trans` split the hypothesis at `n`
//      into the two one-sided reals `within_of_two_sided_le` wants.
//   2. `within_of_two_sided_le` gives `forall i, Within (seq (f n - L) i)
//      (q + 2/(i+1))` at an arbitrary SHARED index, `q := natDivSucc K n`.
//   3. `sharedIndexToCanonical` at `p := q := n` and `j := 3n+2` moves to the
//      canonical index, at the cost of two regularity legs:
//
//          ((1/(n+1) + 1/(sj+1)) + (q + 2/(j+1))) + (1/(sj+1) + 1/(n+1))
//
//      `sj := 2j+1`. `Rat.natDivSucc_halve j` collapses the two `1/(sj+1)`
//      legs to `1/(j+1)`, `Rat.natDivSucc_add` fuses that with the `2/(j+1)`
//      slack to `3/(j+1)`, and `Rat.natDivSucc_scale 2 n` makes `3/(j+1)`
//      EXACTLY `1/(n+1)`.
//   4. What is left is `q + (1/(n+1) + (1/(n+1) + 1/(n+1)))`, three
//      `Rat.natDivSucc_add` fusions to `natDivSucc (K+3) n`.
//
// **The whole six-term bound is an EQUALITY.** Unlike `cauchy_of_abs_diff_le`
// -- whose two canonical indices `m`/`n` differ, so its two numerators have to
// be widened to a shared witness by `Rat.natDivSucc_le_add_left` -- there is
// exactly one index here, so no widening step exists anywhere in this proof.
//
// **There is no low-index obligation.** `Converges` is a uniform-rate
// condition constraining every `n` including `n = 0`, and the shifted-series
// route an earlier slice tried was genuinely blocked there. This route is
// not: every step above is an identity in `n`, so `n = 0` is simply the
// instance where all four denominators are `1` and the bound reads `K + 3`.
// Nothing is chosen "eventually" and nothing is assumed about `n`.
//
// The permutation that groups the six summands is `rsum_perm`, not an inline
// `add_assoc`/`add_comm` chain: it panics on a non-permutation, so a
// mis-derived rearrangement fails with a Rust message naming the two lists
// rather than as an opaque `TypeMismatch` a thousand terms deep.
// =============================================================================

/// `CReal.converges_of_abs_diff_le` -- see
/// [`super::CRealPrelude::converges_of_abs_diff_le`] for the statement and
/// this section's header for the route.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
#[allow(clippy::too_many_lines)]
pub(super) fn declare_converges_of_abs_diff_le(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let seq_ty = d.arrow(nat, carrier);
    let rat = p.rat;

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let l_fv = d.fresh_fvar();
    let l = d.kernel().fvar(l_fv);
    let cap_k_fv = d.fresh_fvar();
    let cap_k = d.kernel().fvar(cap_k_fv);

    // hyp : forall n, le (abs (add (f n) (neg L))) (ofRat (natDivSucc K n)).
    let hyp_ty = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let f_at = d.apply(f, &[n]);
        let q = div_succ_at(d, p, cap_k, n);
        let claim = close_within(d, p, f_at, l, q);
        d.pi_fv(n_fv, nat, claim)
    };
    let hyp_fv = d.fresh_fvar();
    let hyp = d.kernel().fvar(hyp_fv);

    let one_nat = d.num(1);
    let two_nat = d.num(2);
    let three_nat = d.succ(two_nat);
    let k3 = d.add(cap_k, three_nat);

    // --- the body, at a concrete `n` ----------------------------------------
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let fn_n = d.apply(f, &[n]);
    let neg_l = cneg(d, p, l);
    let t = cadd(d, p, fn_n, neg_l);
    let abs_t = cabs(d, p, t);
    let q_atom = div_succ_at(d, p, cap_k, n);
    let y = embed(d, p, q_atom);

    let h_n = d.apply(hyp, &[n]);
    let ht = {
        let self_le = d.lemma(p.le_abs_self, &[t]);
        d.lemma(p.le_trans, &[t, abs_t, y, self_le, h_n])
    };
    let hnt = {
        let neg_t = cneg(d, p, t);
        let neg_le = d.lemma(p.neg_le_abs, &[t]);
        d.lemma(p.le_trans, &[neg_t, abs_t, y, neg_le, h_n])
    };

    // `bound i := seq y i + 2/(i+1)` -- exactly `within_of_two_sided_le`'s own
    // conclusion, so `w` inhabits `forall i, Within (seq t i) (bound i)` with
    // no transport.
    let bound_lam = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let seq_y_i = sample(d, p, y, i);
        let slack = div_succ(d, p, 2, i);
        let body = radd(d, seq_y_i, slack);
        d.lam_fv(i_fv, nat, body)
    };
    let w = d.lemma(p.within_of_two_sided_le, &[t, y, ht, hnt]);

    // `j := 3n+2` -- `Rat.natDivSucc_scale`'s own `(c+1)*n + c` index at
    // `c := 2`, so `3/(j+1)` is EXACTLY `1/(n+1)`.
    let j = {
        let scaled = NatOps::mul(d, three_nat, n);
        d.add(scaled, two_nat)
    };
    let sj = {
        let doubled = NatOps::mul(d, two_nat, j);
        d.succ(doubled)
    };

    let sic = d.lemma(
        p.shared_index_to_canonical,
        &[fn_n, l, bound_lam, w, n, n, j],
    );

    // The bound `sic` carries, with `bound_lam j` beta-reduced and
    // `seq (ofRat q) j` iota-reduced to `q` (both hold definitionally, so
    // `sic` inhabits this type unchanged).
    let a_atom = div_succ(d, p, 1, n);
    let b_atom = div_succ(d, p, 1, sj);
    let d_atom = div_succ(d, p, 2, j);
    let leg1 = modulus(d, p, n, sj);
    let leg3 = modulus(d, p, sj, n);
    let bound_j = radd(d, q_atom, d_atom);
    let leg12 = radd(d, leg1, bound_j);
    let total = radd(d, leg12, leg3);

    // --- the rational identity ----------------------------------------------
    // total = rsum [A, B, Q, D, B, A]
    let flat = [a_atom, b_atom, q_atom, d_atom, b_atom, a_atom];
    let flat_sum = rsum(d, rat, &flat);
    let flatten = {
        let four = rsum(d, rat, &[a_atom, b_atom, q_atom, d_atom]);
        // (A + B) + (Q + D) = rsum [A, B, Q, D]
        let step_inner = rsum_append(d, rat, &[a_atom, b_atom], &[q_atom, d_atom]);
        let step_top = rcongr(d, leg12, four, step_inner, &|d, tm| radd(d, tm, leg3));
        let top_mid = radd(d, four, leg3);
        let step_join = rsum_append(d, rat, &[a_atom, b_atom, q_atom, d_atom], &[b_atom, a_atom]);
        let (_, eq) = rchain(d, total, &[(top_mid, step_top), (flat_sum, step_join)]);
        eq
    };

    // Permute so the three slack atoms sit at the TAIL, where `B + (B + D)`
    // is a genuine subterm of the right-nested sum.
    let sorted = [q_atom, a_atom, a_atom, b_atom, b_atom, d_atom];
    let perm = rsum_perm(d, rat, &flat, &sorted);
    let sorted_sum = rsum(d, rat, &sorted);

    // `B + (B + D) = 1/(n+1)`, exactly.
    let slack_sum = rsum(d, rat, &[b_atom, b_atom, d_atom]);
    let slack_eq = {
        // B + (B + D) = (B + B) + D
        let bb = radd(d, b_atom, b_atom);
        let assoc = d.lemma(rat.add_assoc, &[b_atom, b_atom, d_atom]);
        let left_nested = radd(d, bb, d_atom);
        let step0 = rsymm(d, left_nested, slack_sum, assoc);
        // B + B = natDivSucc 2 sj = natDivSucc 1 j
        let one_one = d.add(one_nat, one_nat);
        let fused_raw = d.const_app(rat.nat_div_succ, &[one_one, sj]);
        let fuse = d.lemma(rat.nat_div_succ_add, &[one_nat, one_nat, sj]);
        let two_sj = d.const_app(rat.nat_div_succ, &[two_nat, sj]);
        let renumber = {
            let refl_two = d.refl(two_nat);
            nat_eq_to_rat(d, one_one, two_nat, refl_two, &|d, x| {
                d.const_app(rat.nat_div_succ, &[x, sj])
            })
        };
        let halve = d.lemma(rat.nat_div_succ_halve, &[j]);
        let one_j = div_succ(d, p, 1, j);
        let (_, bb_eq) = rchain(
            d,
            bb,
            &[(fused_raw, fuse), (two_sj, renumber), (one_j, halve)],
        );
        let step1 = rcongr(d, bb, one_j, bb_eq, &|d, tm| radd(d, tm, d_atom));
        let after_bb = radd(d, one_j, d_atom);
        // 1/(j+1) + 2/(j+1) = natDivSucc 3 j = natDivSucc 1 n
        let one_two = d.add(one_nat, two_nat);
        let fused3_raw = d.const_app(rat.nat_div_succ, &[one_two, j]);
        let fuse3 = d.lemma(rat.nat_div_succ_add, &[one_nat, two_nat, j]);
        let three_j = d.const_app(rat.nat_div_succ, &[three_nat, j]);
        let renumber3 = {
            let refl_three = d.refl(three_nat);
            nat_eq_to_rat(d, one_two, three_nat, refl_three, &|d, x| {
                d.const_app(rat.nat_div_succ, &[x, j])
            })
        };
        let scale = d.lemma(rat.nat_div_succ_scale, &[two_nat, n]);
        let (_, eq) = rchain(
            d,
            slack_sum,
            &[
                (left_nested, step0),
                (after_bb, step1),
                (fused3_raw, fuse3),
                (three_j, renumber3),
                (a_atom, scale),
            ],
        );
        eq
    };
    let collapsed = [q_atom, a_atom, a_atom, a_atom];
    let collapse_step = rcongr(d, slack_sum, a_atom, slack_eq, &|d, tm| {
        let i1 = radd(d, a_atom, tm);
        let i2 = radd(d, a_atom, i1);
        radd(d, q_atom, i2)
    });
    let collapsed_sum = rsum(d, rat, &collapsed);

    // `Q + (A + (A + A)) = natDivSucc (K+3) n`, exactly. No widening.
    let target = div_succ_at(d, p, k3, n);
    let fold_eq = {
        // A + A = natDivSucc 2 n
        let aa = radd(d, a_atom, a_atom);
        let one_one = d.add(one_nat, one_nat);
        let fused_raw = d.const_app(rat.nat_div_succ, &[one_one, n]);
        let fuse = d.lemma(rat.nat_div_succ_add, &[one_nat, one_nat, n]);
        let two_n = d.const_app(rat.nat_div_succ, &[two_nat, n]);
        let renumber = {
            let refl_two = d.refl(two_nat);
            nat_eq_to_rat(d, one_one, two_nat, refl_two, &|d, x| {
                d.const_app(rat.nat_div_succ, &[x, n])
            })
        };
        let (_, aa_eq) = rchain(d, aa, &[(fused_raw, fuse), (two_n, renumber)]);
        let step_a = rcongr(d, aa, two_n, aa_eq, &|d, tm| {
            let inner = radd(d, a_atom, tm);
            radd(d, q_atom, inner)
        });
        let mid1_inner = radd(d, a_atom, two_n);
        let mid1 = radd(d, q_atom, mid1_inner);
        // A + natDivSucc 2 n = natDivSucc 3 n
        let one_two = d.add(one_nat, two_nat);
        let fused3_raw = d.const_app(rat.nat_div_succ, &[one_two, n]);
        let fuse3 = d.lemma(rat.nat_div_succ_add, &[one_nat, two_nat, n]);
        let three_n = d.const_app(rat.nat_div_succ, &[three_nat, n]);
        let renumber3 = {
            let refl_three = d.refl(three_nat);
            nat_eq_to_rat(d, one_two, three_nat, refl_three, &|d, x| {
                d.const_app(rat.nat_div_succ, &[x, n])
            })
        };
        let (_, inner_eq) = rchain(d, mid1_inner, &[(fused3_raw, fuse3), (three_n, renumber3)]);
        let step_b = rcongr(d, mid1_inner, three_n, inner_eq, &|d, tm| {
            radd(d, q_atom, tm)
        });
        let mid2 = radd(d, q_atom, three_n);
        let fuse_k = d.lemma(rat.nat_div_succ_add, &[cap_k, three_nat, n]);
        let (_, eq) = rchain(
            d,
            collapsed_sum,
            &[(mid1, step_a), (mid2, step_b), (target, fuse_k)],
        );
        eq
    };

    let (_, total_eq) = rchain(
        d,
        total,
        &[
            (flat_sum, flatten),
            (sorted_sum, perm),
            (collapsed_sum, collapse_step),
            (target, fold_eq),
        ],
    );
    // total_eq : Eq total (natDivSucc (K+3) n)

    let left_sample = sample(d, p, fn_n, n);
    let right_sample = sample(d, p, l, n);
    let difference = rsub(d, rat, left_sample, right_sample);
    let body = rat_eq_rewrite(d, total, target, total_eq, sic, &|d, tm| {
        within(d, p, difference, tm)
    });

    let per_n = d.lam_fv(n_fv, nat, body);
    let pred = converges_predicate(d, p, f, l);
    let witness = exists_intro(d, p, nat, pred, k3, per_n);

    let value = {
        let over_hyp = d.lam_fv(hyp_fv, hyp_ty, witness);
        let over_k = d.lam_fv(cap_k_fv, nat, over_hyp);
        let over_l = d.lam_fv(l_fv, carrier, over_k);
        d.lam_fv(f_fv, seq_ty, over_l)
    };
    let ty = {
        let concl = converges_applied(d, p, f, l);
        let after_hyp = d.arrow(hyp_ty, concl);
        let over_k = d.pi_fv(cap_k_fv, nat, after_hyp);
        let over_l = d.pi_fv(l_fv, carrier, over_k);
        d.pi_fv(f_fv, seq_ty, over_l)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.converges_of_abs_diff_le,
        uparams: vec![],
        ty,
        value,
    })
}
