//! Tests for `complex/uc_closure.rs` and `complex/cauchy_riemann.rs`.
//!
//! Every assertion is read **out of the kernel** — `Kernel::add_declaration`'s
//! own verdict on a hand-built term — and never out of source text or a doc
//! comment. Each positive test is paired with a NEGATIVE control that the
//! *same* proof shape is REFUSED against a nearby wrong one, because a
//! positive test alone passes for any modulus the kernel happens to unfold to.
//!
//! The two properties pinned here are exactly the two mutants ADR-1656
//! records:
//!
//! * the combined modulus really SUMS both sources — dropping either summand
//!   changes the value the projection reduces to, so
//!   [`uniformly_continuous_add_modulus_sums_both_sources`] and its `mul`
//!   twin die on that mutant rather than merely failing to build; and
//! * `Complex.inDisc_of_two_sided`'s two one-sided bounds are NOT
//!   interchangeable, so a sign flip at any call site is refused
//!   ([`in_disc_of_two_sided_bound_order_is_load_bearing`]).

use super::estimates::bounded_on_ty;
use super::{ComplexPrelude, build_complex_prelude};
use crate::int_prelude::ops::IntDev;
use crate::nat_prelude::NatOps;
use crate::{Declaration, ExprId, Kernel, on_a_deep_stack};

/// A built `Complex` kernel, as a clone of one template — `estimates_tests`'
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

/// Offer the kernel a hand-built `(ty, value)` pair and report its verdict.
///
/// The whole content of every test below: the kernel accepts the term or it
/// does not, and nothing else is inspected.
fn admits(
    kernel: &mut Kernel,
    p: ComplexPrelude,
    label: &str,
    build: &dyn Fn(&mut IntDev<'_>) -> (ExprId, ExprId),
) -> bool {
    let anon = kernel.anon();
    let mut d = IntDev::new(kernel, p.creal.rat.int);
    let (ty, value) = build(&mut d);
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

/// `fun z => z`, at the `Complex` carrier.
fn id_fn(d: &mut IntDev<'_>, p: ComplexPrelude) -> ExprId {
    let carrier = d.kernel().const_(p.complex, vec![]);
    let z_fv = d.fresh_fvar();
    let z = d.kernel().fvar(z_fv);
    d.lam_fv(z_fv, carrier, z)
}

/// `fun z => Complex.add (F z) (G z)` for `F = G = fun z => z`, i.e. the
/// subject `uniformlyContinuous_add` is stated about at `id`, `id`.
fn id_plus_id(d: &mut IntDev<'_>, p: ComplexPrelude) -> ExprId {
    let carrier = d.kernel().const_(p.complex, vec![]);
    let z_fv = d.fresh_fvar();
    let z = d.kernel().fvar(z_fv);
    let sum = d.const_app(p.add, &[z, z]);
    d.lam_fv(z_fv, carrier, sum)
}

/// `fun z => Complex.mul (F z) (G z)` for `F = G = fun z => z`.
fn id_times_id(d: &mut IntDev<'_>, p: ComplexPrelude) -> ExprId {
    let carrier = d.kernel().const_(p.complex, vec![]);
    let z_fv = d.fresh_fvar();
    let z = d.kernel().fvar(z_fv);
    let prod = d.const_app(p.mul, &[z, z]);
    d.lam_fv(z_fv, carrier, prod)
}

// ---------------------------------------------------------------------------
// `uniformlyContinuous_add`: the modulus sums BOTH sources
// ---------------------------------------------------------------------------

/// `uniformlyContinuous_add`'s modulus at `F = G = id` is
/// `n ↦ mId(2n+1) + mId(2n+1)`, and `uniformlyContinuous_id`'s modulus is the
/// identity, so at `n = 1` it must reduce to `3 + 3 = 6`.
///
/// This is the observable the "one of the two moduli ignored" mutant destroys:
/// with either summand dropped the same projection reduces to `3`, not `6`.
#[test]
fn uniformly_continuous_add_modulus_sums_both_sources() {
    let (mut kernel, p) = built();
    let admitted = admits(
        &mut kernel,
        p,
        "Check.uc_add_modulus_sums_both",
        &|d: &mut IntDev<'_>| {
            let c = d.kernel().const_(p.zero, vec![]);
            let r = d.kernel().const_(p.creal.one, vec![]);
            let f = id_fn(d, p);
            let subject = id_plus_id(d, p);
            let huc = d.const_app(p.estimates.uniformly_continuous_id, &[c, r]);
            let witness = d.const_app(
                p.uc_closure.uniformly_continuous_add,
                &[f, f, c, r, huc, huc],
            );
            let modulus = d.const_app(p.estimates.uc_modulus, &[subject, c, r, witness]);
            let one = d.num(1);
            let six = d.num(6);
            let lhs = d.apply(modulus, &[one]);
            let ty = d.eq(lhs, six);
            let value = d.refl(six);
            (ty, value)
        },
    );
    assert!(
        admitted,
        "uniformlyContinuous_add's modulus at n = 1 with both sources the \
         identity must reduce to 3 + 3 = 6"
    );
}

/// The negative control for
/// [`uniformly_continuous_add_modulus_sums_both_sources`]: the same modulus
/// must NOT reduce to `3`, the value it would take if either of the two
/// sources were dropped.
///
/// Without this the positive test alone would still pass for a modulus that
/// consulted one factor and doubled it.
#[test]
fn uniformly_continuous_add_modulus_is_not_one_source_alone() {
    let (mut kernel, p) = built();
    let admitted = admits(
        &mut kernel,
        p,
        "Check.uc_add_modulus_not_one_source",
        &|d: &mut IntDev<'_>| {
            let c = d.kernel().const_(p.zero, vec![]);
            let r = d.kernel().const_(p.creal.one, vec![]);
            let f = id_fn(d, p);
            let subject = id_plus_id(d, p);
            let huc = d.const_app(p.estimates.uniformly_continuous_id, &[c, r]);
            let witness = d.const_app(
                p.uc_closure.uniformly_continuous_add,
                &[f, f, c, r, huc, huc],
            );
            let modulus = d.const_app(p.estimates.uc_modulus, &[subject, c, r, witness]);
            let one = d.num(1);
            let three = d.num(3);
            let lhs = d.apply(modulus, &[one]);
            let ty = d.eq(lhs, three);
            let value = d.refl(three);
            (ty, value)
        },
    );
    assert!(
        !admitted,
        "uniformlyContinuous_add's modulus at n = 1 must NOT be 3 -- if this \
         is admitted one of the two sources is being ignored"
    );
}

// ---------------------------------------------------------------------------
// `uniformlyContinuous_mul`: the same, through the rescaled indices
// ---------------------------------------------------------------------------

/// `uniformlyContinuous_mul`'s modulus at `F = G = id` and `k1 = k2 = 0` is
/// `n ↦ mId(rescale(0, 2n+1)) + mId(rescale(0, 2n+1))`, and
/// `rescale_index(0, m) = 1·m + 0 = m`, so at `n = 1` it must reduce to
/// `3 + 3 = 6`.
///
/// The two `BoundedOn` hypotheses are bound rather than supplied: the modulus
/// does not depend on them, and that independence is itself part of what this
/// test confirms.
#[test]
fn uniformly_continuous_mul_modulus_sums_both_sources() {
    let (mut kernel, p) = built();
    let admitted = admits(
        &mut kernel,
        p,
        "Check.uc_mul_modulus_sums_both",
        &|d: &mut IntDev<'_>| {
            let c = d.kernel().const_(p.zero, vec![]);
            let r = d.kernel().const_(p.creal.one, vec![]);
            let f = id_fn(d, p);
            let subject = id_times_id(d, p);
            let huc = d.const_app(p.estimates.uniformly_continuous_id, &[c, r]);
            let zero_nat = d.num(0);
            let hb_ty = bounded_on_ty(d, p, f, c, r, zero_nat);
            let hb_fv = d.fresh_fvar();
            let hb = d.kernel().fvar(hb_fv);
            let witness = d.const_app(
                p.uc_closure.uniformly_continuous_mul,
                &[f, f, c, r, huc, huc, zero_nat, zero_nat, hb, hb],
            );
            let modulus = d.const_app(p.estimates.uc_modulus, &[subject, c, r, witness]);
            let one = d.num(1);
            let six = d.num(6);
            let lhs = d.apply(modulus, &[one]);
            let inner_ty = d.eq(lhs, six);
            let inner_value = d.refl(six);
            let ty = d.pi_fv(hb_fv, hb_ty, inner_ty);
            let value = d.lam_fv(hb_fv, hb_ty, inner_value);
            (ty, value)
        },
    );
    assert!(
        admitted,
        "uniformlyContinuous_mul's modulus at n = 1 with both sources the \
         identity and both magnitude indices 0 must reduce to 3 + 3 = 6"
    );
}

/// The negative control for
/// [`uniformly_continuous_mul_modulus_sums_both_sources`]: the same modulus
/// must NOT reduce to `3`.
#[test]
fn uniformly_continuous_mul_modulus_is_not_one_source_alone() {
    let (mut kernel, p) = built();
    let admitted = admits(
        &mut kernel,
        p,
        "Check.uc_mul_modulus_not_one_source",
        &|d: &mut IntDev<'_>| {
            let c = d.kernel().const_(p.zero, vec![]);
            let r = d.kernel().const_(p.creal.one, vec![]);
            let f = id_fn(d, p);
            let subject = id_times_id(d, p);
            let huc = d.const_app(p.estimates.uniformly_continuous_id, &[c, r]);
            let zero_nat = d.num(0);
            let hb_ty = bounded_on_ty(d, p, f, c, r, zero_nat);
            let hb_fv = d.fresh_fvar();
            let hb = d.kernel().fvar(hb_fv);
            let witness = d.const_app(
                p.uc_closure.uniformly_continuous_mul,
                &[f, f, c, r, huc, huc, zero_nat, zero_nat, hb, hb],
            );
            let modulus = d.const_app(p.estimates.uc_modulus, &[subject, c, r, witness]);
            let one = d.num(1);
            let three = d.num(3);
            let lhs = d.apply(modulus, &[one]);
            let inner_ty = d.eq(lhs, three);
            let inner_value = d.refl(three);
            let ty = d.pi_fv(hb_fv, hb_ty, inner_ty);
            let value = d.lam_fv(hb_fv, hb_ty, inner_value);
            (ty, value)
        },
    );
    assert!(
        !admitted,
        "uniformlyContinuous_mul's modulus at n = 1 must NOT be 3 -- if this \
         is admitted one of the two sources is being ignored"
    );
}

// ---------------------------------------------------------------------------
// `inDisc_of_two_sided`: the two one-sided bounds are not interchangeable
// ---------------------------------------------------------------------------

/// Build `(ty, value)` for `∀ c r u (h1 : le u r) (h2 : le (neg u) r),
/// InDisc c r (add c (ofReal u))`, proved by applying
/// `Complex.inDisc_of_two_sided` to the two hypotheses in the order given by
/// `swapped`.
fn two_sided_application(d: &mut IntDev<'_>, p: ComplexPrelude, swapped: bool) -> (ExprId, ExprId) {
    let creal = p.creal;
    let carrier = d.kernel().const_(p.complex, vec![]);
    let real = d.kernel().const_(creal.creal, vec![]);

    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let r_fv = d.fresh_fvar();
    let r = d.kernel().fvar(r_fv);
    let u_fv = d.fresh_fvar();
    let u = d.kernel().fvar(u_fv);

    let neg_u = d.const_app(creal.neg, &[u]);
    let hi_ty = d.const_app(creal.le, &[u, r]);
    let lo_ty = d.const_app(creal.le, &[neg_u, r]);
    let hi_fv = d.fresh_fvar();
    let hi = d.kernel().fvar(hi_fv);
    let lo_fv = d.fresh_fvar();
    let lo = d.kernel().fvar(lo_fv);

    let args: [ExprId; 5] = if swapped {
        [c, r, u, lo, hi]
    } else {
        [c, r, u, hi, lo]
    };
    let body = d.const_app(p.cauchy_riemann.in_disc_of_two_sided, &args);

    let w = d.const_app(p.of_real, &[u]);
    let point = d.const_app(p.add, &[c, w]);
    let concl = d.const_app(p.deriv.in_disc, &[c, r, point]);

    let value = {
        let with_lo = d.lam_fv(lo_fv, lo_ty, body);
        let with_hi = d.lam_fv(hi_fv, hi_ty, with_lo);
        let with_u = d.lam_fv(u_fv, real, with_hi);
        let with_r = d.lam_fv(r_fv, real, with_u);
        d.lam_fv(c_fv, carrier, with_r)
    };
    let ty = {
        let with_lo = d.arrow(lo_ty, concl);
        let with_hi = d.arrow(hi_ty, with_lo);
        let with_u = d.pi_fv(u_fv, real, with_hi);
        let with_r = d.pi_fv(r_fv, real, with_u);
        d.pi_fv(c_fv, carrier, with_r)
    };
    (ty, value)
}

/// `Complex.inDisc_of_two_sided` takes the UPPER bound `le u r` first and the
/// lower bound `le (neg u) r` second.
#[test]
fn in_disc_of_two_sided_takes_the_upper_bound_first() {
    let (mut kernel, p) = built();
    let admitted = admits(
        &mut kernel,
        p,
        "Check.in_disc_two_sided_order",
        &|d: &mut IntDev<'_>| two_sided_application(d, p, false),
    );
    assert!(
        admitted,
        "inDisc_of_two_sided must accept (le u r, le (neg u) r) in that order"
    );
}

/// The negative control: the SAME application with the two bounds swapped must
/// be REFUSED.
///
/// This is the observable a sign flip destroys. `le u r` and `le (neg u) r`
/// are distinct types for a bound `u`, so a proof that fed the lower bound
/// where the upper is expected — the shape a Cauchy–Riemann sign error takes —
/// cannot type-check, and this test says so rather than leaving it to be
/// noticed downstream.
#[test]
fn in_disc_of_two_sided_bound_order_is_load_bearing() {
    let (mut kernel, p) = built();
    let admitted = admits(
        &mut kernel,
        p,
        "Check.in_disc_two_sided_order_swapped",
        &|d: &mut IntDev<'_>| two_sided_application(d, p, true),
    );
    assert!(
        !admitted,
        "inDisc_of_two_sided with its two one-sided bounds SWAPPED must be \
         refused -- if this is admitted the sign of the offset is not pinned"
    );
}
