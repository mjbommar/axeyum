//! Tests for the ℚ ring producer. Same four batteries as `ring::int::tests`,
//! minus the declared-theorem retirement style (all five ℚ targets are
//! private proof-construction helpers).
//!
//! 1. **Five retirement targets**, all private helpers:
//!    `rat_prelude/matrix.rs::{mul_sub_right_rev, factor_k_out_of_three,
//!    middle_swap, zero_mul}` and `rat_prelude/probability.rs::scale_sq`.
//! 2. **False goals decline `NotAnIdentity`.**
//! 3. **Corrupted claims are rejected by the KERNEL**, procedure's own check
//!    disabled (`prove_eq_unverified`).
//! 4. **The fragment's boundary.** `div` declines `NonRing`; `x*y = y*x` is
//!    an identity (`sort_factors`); `2*t = t+t` still proves even though the
//!    coefficient cap is 1, because `2` spelled `add one one` goes through
//!    the additive route, not a capped coefficient (see module docs — the
//!    `CoefficientTooLarge` decline is unreachable from any goal this
//!    fragment's own numeral recognizer can construct, a defensive check
//!    rather than an exercised one).

#![allow(clippy::many_single_char_names, clippy::similar_names)]

use crate::int_prelude::ops::IntDev;
use crate::rat_prelude::ops::{radd, req, rmul, rneg, rzero};
use crate::ring::Decline;
use crate::ring::rat as ring;
use crate::{NameId, NatOps, RatPrelude, build_rat_prelude, on_a_deep_stack};

struct Env {
    k: crate::Kernel,
    p: RatPrelude,
    root: NameId,
}

impl Env {
    fn new() -> Self {
        let mut k = crate::Kernel::new();
        let p = build_rat_prelude(&mut k).expect("Rat prelude must build");
        let anon = k.anon();
        let root = k.name_str(anon, "ring_rat_test");
        Self { k, p, root }
    }

    fn name(&mut self, s: &str) -> NameId {
        let root = self.root;
        self.k.name_str(root, s)
    }
}

fn retire_fresh(
    label: &str,
    arity: usize,
    build: &dyn Fn(&mut IntDev<'_>, &[crate::ExprId]) -> crate::ExprId,
) {
    let mut env = Env::new();
    let p = env.p;
    let name = env.name(label);
    let mut d = IntDev::new(&mut env.k, p.int);
    ring::theorem(&mut d, &p, name, arity, build).unwrap_or_else(|e| panic!("{label}: {e}"));
    assert!(
        d.kernel().environment().contains(name),
        "{label}: the kernel did not learn the name",
    );
}

// ---------------------------------------------------------------------------
// 1. the five retirement targets
// ---------------------------------------------------------------------------

#[test]
fn target_matrix_mul_sub_right_rev() {
    on_a_deep_stack(|| {
        // `rat_prelude/matrix.rs::mul_sub_right_rev`: `(k*x)-(k*y) = k*(x-y)`.
        retire_fresh("mul_sub_right_rev", 3, &|d, v| {
            let (k, x, y) = (v[0], v[1], v[2]);
            let kx = rmul(d, k, x);
            let ky = rmul(d, k, y);
            let neg_ky = rneg(d, ky);
            let lhs = radd(d, kx, neg_ky);
            let neg_y = rneg(d, y);
            let xy = radd(d, x, neg_y);
            let rhs = rmul(d, k, xy);
            req(d, lhs, rhs)
        });
    });
}

#[test]
fn target_matrix_factor_k_out_of_three() {
    on_a_deep_stack(|| {
        // `rat_prelude/matrix.rs::factor_k_out_of_three`:
        // `(k*x-k*y)+k*z = k*((x-y)+z)`.
        retire_fresh("factor_k_out_of_three", 4, &|d, v| {
            let (k, x, y, z) = (v[0], v[1], v[2], v[3]);
            let kx = rmul(d, k, x);
            let ky = rmul(d, k, y);
            let neg_ky = rneg(d, ky);
            let kx_minus_ky = radd(d, kx, neg_ky);
            let kz = rmul(d, k, z);
            let lhs = radd(d, kx_minus_ky, kz);
            let neg_y = rneg(d, y);
            let xy = radd(d, x, neg_y);
            let xy_z = radd(d, xy, z);
            let rhs = rmul(d, k, xy_z);
            req(d, lhs, rhs)
        });
    });
}

#[test]
fn target_matrix_middle_swap() {
    on_a_deep_stack(|| {
        // `rat_prelude/matrix.rs::middle_swap`: `w*(x*y) = x*(w*y)`.
        retire_fresh("middle_swap", 3, &|d, v| {
            let (w, x, y) = (v[0], v[1], v[2]);
            let xy = rmul(d, x, y);
            let lhs = rmul(d, w, xy);
            let wy = rmul(d, w, y);
            let rhs = rmul(d, x, wy);
            req(d, lhs, rhs)
        });
    });
}

#[test]
fn target_matrix_zero_mul() {
    on_a_deep_stack(|| {
        // `rat_prelude/matrix.rs::zero_mul`: `zero * x = zero`.
        let mut env = Env::new();
        let p = env.p;
        let name = env.name("zero_mul");
        let mut d = IntDev::new(&mut env.k, p.int);
        ring::theorem(&mut d, &p, name, 1, &|d, v| {
            let x = v[0];
            let zero = rzero(d, p);
            let lhs = rmul(d, zero, x);
            req(d, lhs, zero)
        })
        .unwrap_or_else(|e| panic!("zero_mul: {e}"));
        assert!(d.kernel().environment().contains(name));
    });
}

#[test]
fn target_probability_scale_sq() {
    on_a_deep_stack(|| {
        // `rat_prelude/probability.rs::scale_sq`: `(a*w)*(a*w) = (a*a)*(w*w)`.
        retire_fresh("scale_sq", 2, &|d, v| {
            let (a, w) = (v[0], v[1]);
            let aw = rmul(d, a, w);
            let lhs = rmul(d, aw, aw);
            let aa = rmul(d, a, a);
            let ww = rmul(d, w, w);
            let rhs = rmul(d, aa, ww);
            req(d, lhs, rhs)
        });
    });
}

// ---------------------------------------------------------------------------
// 2. false goals decline `NotAnIdentity`
// ---------------------------------------------------------------------------

fn attempt(
    build: &dyn Fn(&mut IntDev<'_>, &[crate::ExprId]) -> crate::ExprId,
) -> Result<crate::ExprId, Decline> {
    let mut env = Env::new();
    let p = env.p;
    let name = env.name("attempt");
    let mut d = IntDev::new(&mut env.k, p.int);
    ring::theorem(&mut d, &p, name, 2, build).map_err(|e| match e {
        ring::RingError::Declined(dec) => dec,
        ring::RingError::Rejected(e) => panic!("kernel rejected a true goal: {e:?}"),
    })
}

#[test]
fn a_wrong_coefficient_declines() {
    on_a_deep_stack(|| {
        let got = attempt(&|d, v| {
            let aa = radd(d, v[0], v[0]);
            req(d, aa, v[0])
        });
        assert_eq!(got, Err(Decline::NotAnIdentity));
    });
}

#[test]
fn a_wrong_variable_declines() {
    on_a_deep_stack(|| {
        let got = attempt(&|d, v| {
            let a_only = radd(d, v[0], v[0]);
            let a_b = radd(d, v[0], v[1]);
            req(d, a_only, a_b)
        });
        assert_eq!(got, Err(Decline::NotAnIdentity));
    });
}

#[test]
fn a_wrong_sign_declines() {
    on_a_deep_stack(|| {
        let got = attempt(&|d, v| {
            let neg_a = rneg(d, v[0]);
            let lhs = radd(d, v[0], neg_a);
            req(d, lhs, v[0])
        });
        assert_eq!(got, Err(Decline::NotAnIdentity));
    });
}

// ---------------------------------------------------------------------------
// 3. corrupted claims are rejected by the KERNEL
// ---------------------------------------------------------------------------

fn kernel_verdict_on(
    build: &dyn Fn(&mut IntDev<'_>, crate::ExprId, crate::ExprId) -> (crate::ExprId, crate::ExprId),
) -> Result<crate::ExprId, String> {
    let mut env = Env::new();
    let p = env.p;
    let mut d = IntDev::new(&mut env.k, p.int);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let (lhs, rhs) = build(&mut d, a, b);

    let term = ring::prove_eq_unverified(&mut d, &p, lhs, rhs)
        .map_err(|dec| format!("the procedure declined instead of emitting: {dec:?}"))?;

    let concl = req(&mut d, lhs, rhs);
    let rat_ty = crate::rat_prelude::ops::rat_ty(&mut d);
    let value = d.lam_fv(b_fv, rat_ty, term);
    let ty = d.pi_fv(b_fv, rat_ty, concl);
    let value = d.lam_fv(a_fv, rat_ty, value);
    let ty = d.pi_fv(a_fv, rat_ty, ty);
    let name = {
        let anon = d.kernel().anon();
        d.kernel().name_str(anon, "corrupted")
    };
    match d.declare_theorem(name, ty, value) {
        Ok(()) => Ok(ty),
        Err(e) => Err(format!("{e:?}")),
    }
}

#[test]
fn the_honest_identity_is_the_positive_control() {
    on_a_deep_stack(|| {
        kernel_verdict_on(&|d, a, b| {
            let ab = radd(d, a, b);
            let ba = radd(d, b, a);
            (ab, ba)
        })
        .expect("a + b = b + a must be admitted");
    });
}

#[test]
fn a_coefficient_off_by_one_is_rejected_by_the_kernel() {
    on_a_deep_stack(|| {
        let verdict = kernel_verdict_on(&|d, a, _b| {
            let aa = radd(d, a, a);
            (aa, a)
        });
        assert!(
            verdict.is_err(),
            "the kernel admitted `a + a = a`, forced past the procedure's own check",
        );
    });
}

#[test]
fn a_swapped_variable_is_rejected_by_the_kernel() {
    on_a_deep_stack(|| {
        let verdict = kernel_verdict_on(&|d, a, b| {
            let a_only = radd(d, a, a);
            let a_b = radd(d, a, b);
            (a_only, a_b)
        });
        assert!(
            verdict.is_err(),
            "the kernel admitted `a + a = a + b`, forced past the procedure's own check",
        );
    });
}

#[test]
fn the_procedures_own_check_also_catches_a_corrupted_claim() {
    on_a_deep_stack(|| {
        let mut env = Env::new();
        let p = env.p;
        let mut d = IntDev::new(&mut env.k, p.int);
        let a_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let aa = radd(&mut d, a, a);
        let got = ring::prove_eq(&mut d, &p, aa, a);
        assert_eq!(got.err(), Some(Decline::NotAnIdentity));
    });
}

// ---------------------------------------------------------------------------
// 4. the fragment's boundary
// ---------------------------------------------------------------------------

#[test]
fn a_goal_containing_div_declines_nonring() {
    on_a_deep_stack(|| {
        let mut env = Env::new();
        let p = env.p;
        let name = env.name("attempt_div");
        let mut d = IntDev::new(&mut env.k, p.int);
        let got = ring::theorem(&mut d, &p, name, 2, &|d, v| {
            let div = d.const_app(p.div, &[v[0], v[1]]);
            req(d, div, v[0])
        })
        .map_err(|e| match e {
            ring::RingError::Declined(dec) => dec,
            ring::RingError::Rejected(e) => panic!("kernel rejected a true goal: {e:?}"),
        });
        assert_eq!(got.err(), Some(Decline::NonRing));
    });
}

#[test]
fn commuting_two_products_is_an_identity() {
    on_a_deep_stack(|| {
        let got = attempt(&|d, v| {
            let xy = rmul(d, v[0], v[1]);
            let yx = rmul(d, v[1], v[0]);
            req(d, xy, yx)
        });
        assert!(got.is_ok(), "x*y = y*x must be proved: {got:?}");
    });
}

#[test]
fn a_wrong_intra_monomial_factor_declines() {
    on_a_deep_stack(|| {
        let got = attempt(&|d, v| {
            let xy = rmul(d, v[0], v[1]);
            let xx = rmul(d, v[0], v[0]);
            req(d, xy, xx)
        });
        assert_eq!(got, Err(Decline::NotAnIdentity));
    });
}

#[test]
fn a_numeral_two_spelled_as_one_plus_one_is_still_proved() {
    on_a_deep_stack(|| {
        // `2*t = t+t` — NOT via a magnitude-2 coefficient (this fragment's
        // `as_numeral` recognizes only `{-1,0,1}`, so a genuine
        // `CoefficientTooLarge` at `scale_item` is unreachable from any goal
        // this producer's own numeral recognizer can ever construct — see
        // the module docs). `2` here is spelled `add one one`, a compound
        // `Rat` term this fragment flattens as an ordinary 2-item additive
        // sum, and `distribute` scales `t` by each `1` separately — so the
        // identity is proved through the SUM route, not a capped coefficient
        // route, and the two-copy result matches `t+t` directly.
        let mut env = Env::new();
        let p = env.p;
        let name = env.name("two_as_sum");
        let mut d = IntDev::new(&mut env.k, p.int);
        let got = ring::theorem(&mut d, &p, name, 1, &|d, v| {
            let t = v[0];
            let one = crate::rat_prelude::ops::rone(d, p);
            let two = radd(d, one, one);
            let lhs = rmul(d, two, t);
            let rhs = radd(d, t, t);
            req(d, lhs, rhs)
        });
        assert!(got.is_ok(), "2*t = t+t must still be proved: {got:?}");
    });
}

// ---------------------------------------------------------------------------
// 5. `cancel_pairs` — the pass added for `crate::geo::qplane` (ADR-1635).
//
// The three tests below are a matched set, and each dies to a different
// change: the first two die if the pass is removed, the third dies if the
// pass is made unsound by cancelling monomials whose factor lists differ.
// ---------------------------------------------------------------------------

/// **The pass is load-bearing.** `x*y + -(y*x) = 0` needs *both*
/// `sort_factors` (to see the two monomials as the same one) and
/// `cancel_pairs` (to annihilate the pair). Without the cancellation pass
/// this declines `NotAnIdentity`, and the whole ℚ coordinate-geometry
/// development rests on exactly this shape.
#[test]
fn opposite_monomials_cancel_to_zero() {
    on_a_deep_stack(|| {
        let mut env = Env::new();
        let p = env.p;
        let name = env.name("opposite_monomials_cancel");
        let mut d = IntDev::new(&mut env.k, p.int);
        let got = ring::theorem(&mut d, &p, name, 2, &|d, v| {
            let (x, y) = (v[0], v[1]);
            let xy = rmul(d, x, y);
            let yx = rmul(d, y, x);
            let neg = rneg(d, yx);
            let lhs = radd(d, xy, neg);
            let z = rzero(d, p);
            req(d, lhs, z)
        });
        assert!(got.is_ok(), "x*y + -(y*x) = 0 must be proved: {got:?}");
    });
}

/// The determinant shape the geometry actually asks for, as a bare four-atom
/// identity: `(q₂ − p₂)·p₁ + (p₁ − q₁)·p₂ + (p₂·q₁ − p₁·q₂) = 0`, which is
/// `Geo.QPlane.joinOnLeft` with the projections spelled out. Three separate
/// cancelling pairs, and the pass must reach the ones that are not first in
/// the sorted list.
#[test]
fn a_two_by_two_determinant_expansion_collapses() {
    on_a_deep_stack(|| {
        let mut env = Env::new();
        let p = env.p;
        let name = env.name("determinant_collapses");
        let mut d = IntDev::new(&mut env.k, p.int);
        let got = ring::theorem(&mut d, &p, name, 4, &|d, v| {
            let (p1, p2, q1, q2) = (v[0], v[1], v[2], v[3]);
            let big_a = {
                let n = rneg(d, p2);
                radd(d, q2, n)
            };
            let big_b = {
                let n = rneg(d, q1);
                radd(d, p1, n)
            };
            let big_c = {
                let m1 = rmul(d, p2, q1);
                let m2 = rmul(d, p1, q2);
                let n = rneg(d, m2);
                radd(d, m1, n)
            };
            let t1 = rmul(d, big_a, p1);
            let t2 = rmul(d, big_b, p2);
            let sum = radd(d, t1, t2);
            let lhs = radd(d, sum, big_c);
            let z = rzero(d, p);
            req(d, lhs, z)
        });
        assert!(got.is_ok(), "the join passes through P: {got:?}");
    });
}

/// **Negative control for the same pass.** `x*y + -(x*x) = 0` is NOT an
/// identity — the two monomials have different factor lists — and must still
/// decline. A `cancel_pairs` that ignored the factor list would "prove" it.
#[test]
fn unequal_monomials_do_not_cancel() {
    on_a_deep_stack(|| {
        let mut env = Env::new();
        let p = env.p;
        let mut d = IntDev::new(&mut env.k, p.int);
        let x_fv = d.fresh_fvar();
        let y_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let y = d.kernel().fvar(y_fv);
        let xy = rmul(&mut d, x, y);
        let xx = rmul(&mut d, x, x);
        let neg = rneg(&mut d, xx);
        let lhs = radd(&mut d, xy, neg);
        let z = rzero(&mut d, p);
        match ring::prove_eq(&mut d, &p, lhs, z) {
            Err(Decline::NotAnIdentity) => {}
            other => panic!("x*y + -(x*x) = 0 must decline NotAnIdentity, got {other:?}"),
        }
    });
}
