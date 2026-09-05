//! Tests for `complex/estimates.rs`.
//!
//! Every assertion here is read **out of the kernel** — the environment, the
//! declaration kinds, `Kernel::axiom_footprint`, and above all
//! `Kernel::add_declaration`'s own verdict on a hand-built identity proof —
//! and never out of source text or a doc comment.
//!
//! The pattern each pair below uses is `complex/deriv.rs`'s
//! `in_disc_unfolds_to_the_distance_from_the_centre` /
//! `in_disc_argument_order_is_load_bearing`: a `Definition` is confirmed by
//! admitting `fun h => h` against its claimed unfolding, and the confirmation
//! is only worth anything paired with a NEGATIVE control that the *same*
//! identity proof is REFUSED against a nearby wrong shape. A positive test
//! alone would pass for a definition off by any amount the kernel happens to
//! unfold through.

use super::{ComplexPrelude, build_complex_prelude};
use crate::int_prelude::ops::IntDev;
use crate::nat_prelude::NatOps;
use crate::{Declaration, Kernel, on_a_deep_stack};

/// A built `Complex` kernel, as a clone of one template — `complex_tests`'
/// `built()` verbatim, kept local so this file's tests do not depend on that
/// module's private items.
fn built() -> (Kernel, ComplexPrelude) {
    use std::sync::OnceLock;
    static TEMPLATE: OnceLock<(Kernel, ComplexPrelude)> = OnceLock::new();
    let (kernel, prelude) = TEMPLATE.get_or_init(|| {
        on_a_deep_stack(|| {
            let mut kernel = Kernel::new();
            let prelude = build_complex_prelude(&mut kernel).expect("Complex prelude must build");
            (kernel, prelude)
        })
    });
    (kernel.clone(), *prelude)
}

/// Admit `Eq Nat lhs rhs` by `Eq.refl rhs` and report the kernel's verdict.
///
/// The whole content of every modulus test below: the two sides are equal
/// **definitionally** or they are not, and `Eq.refl` is exactly the proof that
/// asks the kernel that question and nothing else.
fn nat_eq_by_refl(
    kernel: &mut Kernel,
    p: ComplexPrelude,
    label: &str,
    build: &dyn Fn(&mut IntDev<'_>) -> (crate::ExprId, crate::ExprId),
) -> bool {
    let anon = kernel.anon();
    let mut d = IntDev::new(kernel, p.creal.rat.int);
    let (lhs, rhs) = build(&mut d);
    let ty = d.eq(lhs, rhs);
    let value = d.refl(rhs);
    let name = d.kernel().name_str(anon, label);
    d.kernel()
        .add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty,
            value,
        })
        .is_ok()
}

/// `Complex.UniformlyContinuousOn.modulus` really projects the modulus the
/// constructor stored: `uniformlyContinuous_id`'s is the IDENTITY, so at the
/// concrete index `3` it must reduce to `3`.
///
/// This is the evaluation test the new `Definition` owes — the trusted gate
/// type-checks `modulus`, and a projection returning the wrong field (or the
/// wrong constructor argument) has exactly the same type.
#[test]
fn uniformly_continuous_id_modulus_is_the_identity() {
    let (mut kernel, p) = built();
    let admitted = nat_eq_by_refl(
        &mut kernel,
        p,
        "Check.uc_id_modulus_is_identity",
        &|d: &mut IntDev<'_>| {
            let carrier = d.kernel().const_(p.complex, vec![]);
            let c = d.kernel().const_(p.zero, vec![]);
            let r = d.kernel().const_(p.creal.one, vec![]);
            let id_fn = {
                let z_fv = d.fresh_fvar();
                let z = d.kernel().fvar(z_fv);
                d.lam_fv(z_fv, carrier, z)
            };
            let witness = d.const_app(p.estimates.uniformly_continuous_id, &[c, r]);
            let modulus = d.const_app(p.estimates.uc_modulus, &[id_fn, c, r, witness]);
            let three = d.num(3);
            let lhs = d.apply(modulus, &[three]);
            (lhs, three)
        },
    );
    assert!(
        admitted,
        "UniformlyContinuousOn.modulus applied to uniformlyContinuous_id must \
         reduce to the identity function"
    );
}

/// The negative control for
/// [`uniformly_continuous_id_modulus_is_the_identity`]: `uniformlyContinuous_id`'s
/// modulus must NOT reduce to the constant `0`.
///
/// Without this, a `modulus` projection that returned `fun _ => 0` for every
/// witness would still pass the positive test at index `0`, and every witness
/// in this module would still build — nothing else unfolds `modulus` at a
/// literal.
#[test]
fn uniformly_continuous_id_modulus_is_not_constant_zero() {
    let (mut kernel, p) = built();
    let admitted = nat_eq_by_refl(
        &mut kernel,
        p,
        "Check.uc_id_modulus_is_not_zero",
        &|d: &mut IntDev<'_>| {
            let carrier = d.kernel().const_(p.complex, vec![]);
            let c = d.kernel().const_(p.zero, vec![]);
            let r = d.kernel().const_(p.creal.one, vec![]);
            let id_fn = {
                let z_fv = d.fresh_fvar();
                let z = d.kernel().fvar(z_fv);
                d.lam_fv(z_fv, carrier, z)
            };
            let witness = d.const_app(p.estimates.uniformly_continuous_id, &[c, r]);
            let modulus = d.const_app(p.estimates.uc_modulus, &[id_fn, c, r, witness]);
            let three = d.num(3);
            let zero = d.num(0);
            let lhs = d.apply(modulus, &[three]);
            (lhs, zero)
        },
    );
    assert!(
        !admitted,
        "uniformlyContinuous_id's modulus at 3 must NOT be 0 -- if this is \
         admitted the projection is returning a constant, not the stored field"
    );
}

/// `uniformlyContinuous_const`'s stored modulus is the constant `0`, which is
/// the discriminating companion to
/// [`uniformly_continuous_id_modulus_is_the_identity`]: the two witnesses
/// store DIFFERENT moduli, so a projection that ignored the witness could not
/// satisfy both.
#[test]
fn uniformly_continuous_const_modulus_is_zero() {
    let (mut kernel, p) = built();
    let admitted = nat_eq_by_refl(
        &mut kernel,
        p,
        "Check.uc_const_modulus_is_zero",
        &|d: &mut IntDev<'_>| {
            let carrier = d.kernel().const_(p.complex, vec![]);
            let k = d.kernel().const_(p.one, vec![]);
            let c = d.kernel().const_(p.zero, vec![]);
            let r = d.kernel().const_(p.creal.one, vec![]);
            let const_fn = {
                let ignore_fv = d.fresh_fvar();
                d.lam_fv(ignore_fv, carrier, k)
            };
            let witness = d.const_app(p.estimates.uniformly_continuous_const, &[k, c, r]);
            let modulus = d.const_app(p.estimates.uc_modulus, &[const_fn, c, r, witness]);
            let three = d.num(3);
            let zero = d.num(0);
            let lhs = d.apply(modulus, &[three]);
            (lhs, zero)
        },
    );
    assert!(
        admitted,
        "uniformlyContinuous_const's modulus must be the constant 0"
    );
}

/// Admit
/// `∀ F F' c r (hf : HasDerivativeOn F F' c r) (k : Nat)
///    (hb : BoundedOn F' c r k) (n : Nat),
///  Eq Nat (UniformlyContinuousOn.modulus F c r
///            (uniformlyContinuous_of_hasDerivative F F' c r hf k hb) n)
///         (m (rescale_index 0 inner) + rescale_index k inner + 0)`
/// by `Eq.refl`, with `inner := 2n+1` when `halved` and `inner := n`
/// otherwise. Returns the kernel's verdict.
///
/// **Every variable is BOUND.** An earlier draft of this pair left them free,
/// which made `add_declaration` return `UnboundFVar` for both the positive
/// test and its control — so the control "passed" while proving nothing, the
/// vacuous half of the two ways a negative control fails. The positive test
/// failing is what exposed it; had the positive been the vacuous one the pair
/// would have looked green.
fn of_has_derivative_modulus_admitted(
    kernel: &mut Kernel,
    p: ComplexPrelude,
    halved: bool,
) -> bool {
    use crate::creal::derivative::rescale_index;

    let anon = kernel.anon();
    let mut d = IntDev::new(kernel, p.creal.rat.int);
    let carrier = d.kernel().const_(p.complex, vec![]);
    let real = d.kernel().const_(p.creal.creal, vec![]);
    let nat = d.nat_ty();
    let func_ty = d.arrow(carrier, carrier);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let fp_fv = d.fresh_fvar();
    let fp = d.kernel().fvar(fp_fv);
    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let r_fv = d.fresh_fvar();
    let r = d.kernel().fvar(r_fv);

    let hf_ty = d.const_app(p.deriv.has_derivative_on, &[f, fp, c, r]);
    let hf_fv = d.fresh_fvar();
    let hf = d.kernel().fvar(hf_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    // The named `Complex.BoundedOn` rather than its inline shape: the theorem
    // takes the inline one, and the two are definitionally equal, so passing
    // this exercises that defeq as well.
    let hb_ty = d.const_app(p.estimates.bounded_on, &[fp, c, r, k]);
    let hb_fv = d.fresh_fvar();
    let hb = d.kernel().fvar(hb_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let witness = d.const_app(
        p.estimates.uniformly_continuous_of_has_derivative,
        &[f, fp, c, r, hf, k, hb],
    );
    let modulus = d.const_app(p.estimates.uc_modulus, &[f, c, r, witness]);
    let lhs = d.apply(modulus, &[n]);

    let inner = if halved {
        let two = d.num(2);
        let two_n = d.mul(two, n);
        d.succ(two_n)
    } else {
        n
    };
    let zero_nat = d.num(0);
    let e_a = rescale_index(&mut d, zero_nat, inner);
    let e_b = rescale_index(&mut d, k, inner);
    let m = d.const_app(p.deriv.hd_modulus, &[f, fp, c, r, hf]);
    let m_a = d.apply(m, &[e_a]);
    let head = d.add(m_a, e_b);
    let rhs = d.add(head, zero_nat);

    let claim = d.eq(lhs, rhs);
    let body = d.refl(rhs);
    let value = {
        let with_n = d.lam_fv(n_fv, nat, body);
        let with_hb = d.lam_fv(hb_fv, hb_ty, with_n);
        let with_k = d.lam_fv(k_fv, nat, with_hb);
        let with_hf = d.lam_fv(hf_fv, hf_ty, with_k);
        let with_r = d.lam_fv(r_fv, real, with_hf);
        let with_c = d.lam_fv(c_fv, carrier, with_r);
        let with_fp = d.lam_fv(fp_fv, func_ty, with_c);
        d.lam_fv(f_fv, func_ty, with_fp)
    };
    let ty = {
        let with_n = d.pi_fv(n_fv, nat, claim);
        let with_hb = d.pi_fv(hb_fv, hb_ty, with_n);
        let with_k = d.pi_fv(k_fv, nat, with_hb);
        let with_hf = d.pi_fv(hf_fv, hf_ty, with_k);
        let with_r = d.pi_fv(r_fv, real, with_hf);
        let with_c = d.pi_fv(c_fv, carrier, with_r);
        let with_fp = d.pi_fv(fp_fv, func_ty, with_c);
        d.pi_fv(f_fv, func_ty, with_fp)
    };

    let label = if halved {
        "Check.uc_of_hd_modulus_is_halved"
    } else {
        "Check.uc_of_hd_modulus_unhalved"
    };
    let name = d.kernel().name_str(anon, label);
    d.kernel()
        .add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty,
            value,
        })
        .is_ok()
}

/// **The halving is in the modulus, and this reads it out of the kernel.**
///
/// `uniformlyContinuous_of_hasDerivative`'s modulus at accuracy `n` is
/// `m(rescale_index(0, 2n+1)) + rescale_index(k, 2n+1) + 0` — the inner index
/// is `2n+1`, not `n`, because the estimate spends `1/(n+1)` as two equal
/// halves (the module documentation's display). The equation is admitted under
/// binders for `F, F', c, r, hf, k, n`, so it constrains the modulus as a
/// FUNCTION and not at one sampled index.
#[test]
fn uniformly_continuous_of_has_derivative_modulus_is_halved() {
    let (mut kernel, p) = built();
    assert!(
        of_has_derivative_modulus_admitted(&mut kernel, p, true),
        "uniformlyContinuous_of_hasDerivative's modulus must read its two \
         summands at the HALVED index 2n+1"
    );
}

/// The negative control for
/// [`uniformly_continuous_of_has_derivative_modulus_is_halved`]: the same
/// `Eq.refl` proof must be REFUSED against the un-halved modulus, which reads
/// both summands at `n` instead of `2n+1`.
///
/// This is the mutation this file's construction is most exposed to — dropping
/// the halving leaves the two summands each already at the full target
/// `1/(n+1)`, so their sum overshoots by a factor of two. The control is only
/// worth anything because its positive twin is ADMITTED under the same
/// binders: a shared construction error refuses both, which is exactly what
/// happened on this pair's first run.
#[test]
fn uniformly_continuous_of_has_derivative_modulus_without_halving_is_refused() {
    let (mut kernel, p) = built();
    assert!(
        !of_has_derivative_modulus_admitted(&mut kernel, p, false),
        "the UN-halved modulus (inner index n instead of 2n+1) must be REFUSED"
    );
}

/// `Complex.BoundedOn F c r k` unfolds to EXACTLY
/// `∀ z, InDisc c r z → CReal.le (Complex.abs (F z)) (ofRat (natDivSucc (k+1) 0))`,
/// confirmed by admitting `fun h => h` against that inline shape.
///
/// `Complex.bounded_on_unfold` is the same statement as a prelude declaration;
/// this repeats it here so the pair below (positive plus its numerator
/// control) lives in one place.
#[test]
fn bounded_on_unfolds_to_the_disc_wide_magnitude_bound() {
    let (mut kernel, p) = built();
    let admitted = bounded_on_identity_admitted(&mut kernel, p, true);
    assert!(
        admitted,
        "BoundedOn must be definitionally its inline `∀ z, InDisc → |F z| ≤ \
         (k+1)/1` shape"
    );
}

/// The negative control for
/// [`bounded_on_unfolds_to_the_disc_wide_magnitude_bound`]: the SAME identity
/// proof must be REFUSED when the bound's numerator is `k` rather than
/// `Nat.succ k`.
///
/// The two differ by one `Nat.succ`, and the difference is load-bearing: at
/// `k = 0` the wrong shape says `|F z| ≤ 0`, so a bound that ought to be
/// satisfiable by every function on the disc becomes satisfiable only by the
/// zero function. Nothing else in this module unfolds `BoundedOn` at a
/// literal, so without this control the off-by-one would survive.
#[test]
fn bounded_on_numerator_is_the_successor_of_the_index() {
    let (mut kernel, p) = built();
    let admitted = bounded_on_identity_admitted(&mut kernel, p, false);
    assert!(
        !admitted,
        "BoundedOn with numerator `k` instead of `k+1` must be REFUSED"
    );
}

/// Admit `fun (h : Complex.BoundedOn F c r k) => h` against the inline shape,
/// with the bound's numerator either `Nat.succ k` (`succ_numerator`) or the
/// bare `k`. Returns the kernel's verdict.
fn bounded_on_identity_admitted(
    kernel: &mut Kernel,
    p: ComplexPrelude,
    succ_numerator: bool,
) -> bool {
    let anon = kernel.anon();
    let mut d = IntDev::new(kernel, p.creal.rat.int);
    let creal = p.creal;
    let carrier = d.kernel().const_(p.complex, vec![]);
    let real = d.kernel().const_(creal.creal, vec![]);
    let nat = d.nat_ty();
    let func_ty = d.arrow(carrier, carrier);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let r_fv = d.fresh_fvar();
    let r = d.kernel().fvar(r_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);

    let hypothesis = d.const_app(p.estimates.bounded_on, &[f, c, r, k]);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let claim = {
        let z_fv = d.fresh_fvar();
        let z = d.kernel().fvar(z_fv);
        let disc_z = d.const_app(p.deriv.in_disc, &[c, r, z]);
        let fz = d.apply(f, &[z]);
        let abs_fz = d.const_app(p.abs, &[fz]);
        let numerator = if succ_numerator { d.succ(k) } else { k };
        let zero_idx = d.num(0);
        let q = d.const_app(creal.rat.nat_div_succ, &[numerator, zero_idx]);
        let bound = d.const_app(creal.of_rat, &[q]);
        let concl = d.const_app(creal.le, &[abs_fz, bound]);
        let with_disc = d.arrow(disc_z, concl);
        d.pi_fv(z_fv, carrier, with_disc)
    };

    let value = {
        let with_h = d.lam_fv(h_fv, hypothesis, h);
        let with_k = d.lam_fv(k_fv, nat, with_h);
        let with_r = d.lam_fv(r_fv, real, with_k);
        let with_c = d.lam_fv(c_fv, carrier, with_r);
        d.lam_fv(f_fv, func_ty, with_c)
    };
    let ty = {
        let with_h = d.arrow(hypothesis, claim);
        let with_k = d.pi_fv(k_fv, nat, with_h);
        let with_r = d.pi_fv(r_fv, real, with_k);
        let with_c = d.pi_fv(c_fv, carrier, with_r);
        d.pi_fv(f_fv, func_ty, with_c)
    };

    let label = if succ_numerator {
        "Check.bounded_on_unfolds"
    } else {
        "Check.bounded_on_bare_numerator"
    };
    let name = d.kernel().name_str(anon, label);
    d.kernel()
        .add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty,
            value,
        })
        .is_ok()
}

/// `Complex.abs_mul_le_of_bounds`'s conclusion is bounded by the product of
/// the two bounds in THAT ORDER (`B·b`, the first argument's bound first) —
/// checked by instantiating the theorem and admitting its own result type.
///
/// The negative control below swaps the product, which is a different `CReal`
/// term even though the two are `Equiv`.
#[test]
fn abs_mul_le_of_bounds_multiplies_the_bounds_in_argument_order() {
    let (mut kernel, p) = built();
    assert!(
        abs_mul_bound_order_admitted(&mut kernel, p, true),
        "abs_mul_le_of_bounds must conclude `le (abs (mul u v)) (mul B b)`"
    );
}

/// The negative control for
/// [`abs_mul_le_of_bounds_multiplies_the_bounds_in_argument_order`]: the
/// commuted product `b·B` is a DIFFERENT term (`CReal.mul` is not
/// definitionally commutative — `CReal.mul_comm` is a proved `Equiv`, not a
/// reduction), so ascribing the theorem to it must be refused.
#[test]
fn abs_mul_le_of_bounds_bound_order_is_load_bearing() {
    let (mut kernel, p) = built();
    assert!(
        !abs_mul_bound_order_admitted(&mut kernel, p, false),
        "the COMMUTED bound `mul b B` must be REFUSED"
    );
}

/// Instantiate `Complex.abs_mul_le_of_bounds` and ascribe it to
/// `le (abs (mul u v)) (mul B b)` (`in_order`) or to the commuted
/// `mul b B`. Returns the kernel's verdict.
fn abs_mul_bound_order_admitted(kernel: &mut Kernel, p: ComplexPrelude, in_order: bool) -> bool {
    let anon = kernel.anon();
    let mut d = IntDev::new(kernel, p.creal.rat.int);
    let creal = p.creal;
    let carrier = d.kernel().const_(p.complex, vec![]);
    let real = d.kernel().const_(creal.creal, vec![]);

    let u_fv = d.fresh_fvar();
    let u = d.kernel().fvar(u_fv);
    let v_fv = d.fresh_fvar();
    let v = d.kernel().fvar(v_fv);
    let bb_fv = d.fresh_fvar();
    let bb = d.kernel().fvar(bb_fv);
    let sb_fv = d.fresh_fvar();
    let sb = d.kernel().fvar(sb_fv);

    let abs_u = d.const_app(p.abs, &[u]);
    let abs_v = d.const_app(p.abs, &[v]);
    let h1_ty = d.const_app(creal.le, &[abs_u, bb]);
    let h1_fv = d.fresh_fvar();
    let h1 = d.kernel().fvar(h1_fv);
    let h2_ty = d.const_app(creal.le, &[abs_v, sb]);
    let h2_fv = d.fresh_fvar();
    let h2 = d.kernel().fvar(h2_fv);

    let body = d.lemma(p.estimates.abs_mul_le_of_bounds, &[u, v, bb, sb, h1, h2]);
    let prod = d.const_app(p.mul, &[u, v]);
    let abs_prod = d.const_app(p.abs, &[prod]);
    let bound = if in_order {
        d.const_app(creal.mul, &[bb, sb])
    } else {
        d.const_app(creal.mul, &[sb, bb])
    };
    let claim = d.const_app(creal.le, &[abs_prod, bound]);

    let value = {
        let with_h2 = d.lam_fv(h2_fv, h2_ty, body);
        let with_h1 = d.lam_fv(h1_fv, h1_ty, with_h2);
        let with_sb = d.lam_fv(sb_fv, real, with_h1);
        let with_bb = d.lam_fv(bb_fv, real, with_sb);
        let with_v = d.lam_fv(v_fv, carrier, with_bb);
        d.lam_fv(u_fv, carrier, with_v)
    };
    let ty = {
        let with_h2 = d.arrow(h2_ty, claim);
        let with_h1 = d.arrow(h1_ty, with_h2);
        let with_sb = d.pi_fv(sb_fv, real, with_h1);
        let with_bb = d.pi_fv(bb_fv, real, with_sb);
        let with_v = d.pi_fv(v_fv, carrier, with_bb);
        d.pi_fv(u_fv, carrier, with_v)
    };

    let label = if in_order {
        "Check.abs_mul_bounds_in_order"
    } else {
        "Check.abs_mul_bounds_commuted"
    };
    let name = d.kernel().name_str(anon, label);
    d.kernel()
        .add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty,
            value,
        })
        .is_ok()
}
