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
//! [`super::convergence::converges_comp_eventually`]'s own doc flags as
//! necessary and which this file's sibling lemmas make available), consult
//! `F_N`'s own `UniformlyContinuousOn` modulus at that SAME split accuracy
//! for the middle term, and combine the three `close_within` legs via
//! `CReal.abs_le_of_two_sided`. Every piece of that route is now in place
//! (`neg_sub_swap`, `abs_le_of_two_sided`, and this file's own
//! [`declare_uniform_converges_on`]/projections); what remains is the
//! Rust-level assembly of roughly a dozen more `le_congr`/`add_le_add`/
//! `add_assoc` steps mirroring `convergence.rs`'s own `shifted_bound_at`/
//! `close_within_of_sample_bound` in scale, which a later slice can complete
//! without re-deriving anything above it.

use crate::KernelError;
use crate::NatOps;
use crate::env::{Declaration, ReducibilityHint};
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::rat_prelude::ops::{nat_rewrite_prop, radd, rat_eq_rewrite, rle};

use super::{CRealPrelude, creal_ty};

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
