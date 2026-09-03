//! Tests for the ℤ ring producer. Same four batteries as `ring::nat::tests`.
//!
//! 1. **Five retirement targets.** One declared theorem (`Int.mul_sub`) and
//!    four private proof-construction helpers (`int_prelude/gcd.rs::factor_out`,
//!    `int_prelude/fibonacci.rs::mul_two_eq_add_self`,
//!    `int_prelude/wilson.rs::diff_of_squares`, and the *duplicated* private
//!    `neg_neg` in both `gcd.rs` and `fibonacci.rs`) — the private ones have
//!    no declared name to compare against, so each test re-derives the exact
//!    statement the hand code proves and requires the kernel to admit it as a
//!    fresh declaration.
//! 2. **False goals decline `NotAnIdentity`.**
//! 3. **Corrupted claims are rejected by the KERNEL**, procedure's own check
//!    disabled (`prove_eq_unverified`).
//! 4. **The fragment's boundary.** `ediv`/`emod` decline `NonRing`; `x*y =
//!    y*x` is an identity (`sort_factors`), with a negative control.

#![allow(clippy::many_single_char_names, clippy::similar_names)]

use crate::int_prelude::ops::IntDev;
use crate::ring::Decline;
use crate::ring::int as ring;
use crate::{ExprId, IntPrelude, Kernel, NameId, NatOps, build_int_prelude, on_a_deep_stack};

struct Env {
    k: Kernel,
    p: IntPrelude,
    root: NameId,
}

impl Env {
    fn new() -> Self {
        let mut k = Kernel::new();
        let p = build_int_prelude(&mut k).expect("Int prelude must build");
        let anon = k.anon();
        let root = k.name_str(anon, "ring_int_test");
        Self { k, p, root }
    }

    fn name(&mut self, s: &str) -> NameId {
        let root = self.root;
        self.k.name_str(root, s)
    }

    fn prelude_type(&self, name: NameId) -> ExprId {
        self.k
            .environment()
            .get(name)
            .expect("the prelude declares this name")
            .ty()
    }
}

/// Declare `label` by the procedure and require its type to be definitionally
/// equal to the prelude's own statement of `mirror`.
fn retire_named(
    label: &str,
    mirror: fn(&IntPrelude) -> NameId,
    arity: usize,
    build: &dyn Fn(&mut IntDev<'_>, &[ExprId]) -> ExprId,
) {
    let mut env = Env::new();
    let p = env.p;
    let expected = env.prelude_type(mirror(&p));
    let name = env.name(label);
    {
        let mut d = IntDev::new(&mut env.k, p);
        ring::theorem(&mut d, &p, name, arity, build).unwrap_or_else(|e| panic!("{label}: {e}"));
    }
    let got = env.prelude_type(name);
    assert!(
        env.k.def_eq(got, expected),
        "{label}: the emitted declaration's type is not the prelude's statement",
    );
}

/// Declare `label` with no prelude name to compare against — the private
/// retirement targets. Requires only that the kernel admits the declaration.
fn retire_fresh(label: &str, arity: usize, build: &dyn Fn(&mut IntDev<'_>, &[ExprId]) -> ExprId) {
    let mut env = Env::new();
    let p = env.p;
    let name = env.name(label);
    let mut d = IntDev::new(&mut env.k, p);
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
fn target_gcd_factor_out() {
    on_a_deep_stack(|| {
        // `int_prelude/gcd.rs::factor_out`: `A*mp + neg(A*mn) = A*(mp + neg mn)`.
        retire_fresh("factor_out", 3, &|d, v| {
            let (a, mp, mn) = (v[0], v[1], v[2]);
            let bp = d.imul(a, mp);
            let q = d.imul(a, mn);
            let neg_q = d.ineg(q);
            let lhs = d.iadd(bp, neg_q);
            let neg_mn = d.ineg(mn);
            let u0 = d.iadd(mp, neg_mn);
            let rhs = d.imul(a, u0);
            d.ieq(lhs, rhs)
        });
    });
}

#[test]
fn target_fibonacci_mul_two_eq_add_self() {
    on_a_deep_stack(|| {
        // `int_prelude/fibonacci.rs::mul_two_eq_add_self`: `2*t = t+t`.
        retire_fresh("mul_two_eq_add_self", 1, &|d, v| {
            let t = v[0];
            let two_nat = d.num(2);
            let two = d.of_nat(two_nat);
            let lhs = d.imul(two, t);
            let rhs = d.iadd(t, t);
            d.ieq(lhs, rhs)
        });
    });
}

#[test]
fn target_wilson_diff_of_squares() {
    on_a_deep_stack(|| {
        // `int_prelude/wilson.rs::diff_of_squares`: `(a-1)*(a+1) = a*a - 1`.
        retire_fresh("diff_of_squares", 1, &|d, v| {
            let a = v[0];
            let one = d.ione();
            let sub_a1 = d.isub(a, one);
            let add_a1 = d.iadd(a, one);
            let lhs = d.imul(sub_a1, add_a1);
            let aa = d.imul(a, a);
            let rhs = d.isub(aa, one);
            d.ieq(lhs, rhs)
        });
    });
}

#[test]
fn target_int_mul_sub() {
    on_a_deep_stack(|| {
        // Declared theorem `Int.mul_sub`, `int_prelude/sub.rs::declare_mul_sub`.
        retire_named("mul_sub", |p| p.mul_sub, 3, &|d, v| {
            let (n, x, y) = (v[0], v[1], v[2]);
            let sub_xy = d.isub(x, y);
            let lhs = d.imul(n, sub_xy);
            let mul_nx = d.imul(n, x);
            let mul_ny = d.imul(n, y);
            let rhs = d.isub(mul_nx, mul_ny);
            d.ieq(lhs, rhs)
        });
    });
}

#[test]
fn target_neg_neg_duplicated_in_gcd_and_fibonacci() {
    on_a_deep_stack(|| {
        // `int_prelude/gcd.rs::neg_neg` and `int_prelude/fibonacci.rs::neg_neg`:
        // two independent private hand-derivations of the same identity
        // `neg (neg x) = x`, exactly the "duplicated helper" shape ring-tactic-1
        // found eight of over ℕ.
        retire_fresh("neg_neg", 1, &|d, v| {
            let x = v[0];
            let neg_x = d.ineg(x);
            let nn = d.ineg(neg_x);
            d.ieq(nn, x)
        });
    });
}

// ---------------------------------------------------------------------------
// 2. false goals decline `NotAnIdentity`
// ---------------------------------------------------------------------------

fn attempt(build: &dyn Fn(&mut IntDev<'_>, &[ExprId]) -> ExprId) -> Result<ExprId, Decline> {
    let mut env = Env::new();
    let p = env.p;
    let name = env.name("attempt");
    let mut d = IntDev::new(&mut env.k, p);
    ring::theorem(&mut d, &p, name, 2, build).map_err(|e| match e {
        ring::RingError::Declined(dec) => dec,
        ring::RingError::Rejected(e) => panic!("kernel rejected a true goal: {e:?}"),
    })
}

#[test]
fn a_wrong_coefficient_declines() {
    on_a_deep_stack(|| {
        let got = attempt(&|d, v| {
            let aa = d.iadd(v[0], v[0]);
            d.ieq(aa, v[0])
        });
        assert_eq!(got, Err(Decline::NotAnIdentity));
    });
}

#[test]
fn a_wrong_constant_declines() {
    on_a_deep_stack(|| {
        let got = attempt(&|d, v| {
            let ab = d.iadd(v[0], v[1]);
            let one = d.ione();
            let ab1 = d.iadd(ab, one);
            d.ieq(ab, ab1)
        });
        assert_eq!(got, Err(Decline::NotAnIdentity));
    });
}

#[test]
fn a_wrong_variable_declines() {
    on_a_deep_stack(|| {
        let got = attempt(&|d, v| {
            let a_only = d.iadd(v[0], v[0]);
            let a_b = d.iadd(v[0], v[1]);
            d.ieq(a_only, a_b)
        });
        assert_eq!(got, Err(Decline::NotAnIdentity));
    });
}

#[test]
fn a_wrong_sign_declines() {
    on_a_deep_stack(|| {
        // `x + (-x) = x`, i.e. `0 = x` -- false for a free variable `x`.
        let got = attempt(&|d, v| {
            let neg_x = d.ineg(v[0]);
            let lhs = d.iadd(v[0], neg_x);
            d.ieq(lhs, v[0])
        });
        assert_eq!(got, Err(Decline::NotAnIdentity));
    });
}

// ---------------------------------------------------------------------------
// 3. corrupted claims are rejected by the KERNEL
// ---------------------------------------------------------------------------

fn kernel_verdict_on(
    build: &dyn Fn(&mut IntDev<'_>, ExprId, ExprId) -> (ExprId, ExprId),
) -> Result<ExprId, String> {
    let mut env = Env::new();
    let p = env.p;
    let mut d = IntDev::new(&mut env.k, p);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let (lhs, rhs) = build(&mut d, a, b);

    let term = ring::prove_eq_unverified(&mut d, &p, lhs, rhs)
        .map_err(|dec| format!("the procedure declined instead of emitting: {dec:?}"))?;

    let concl = d.ieq(lhs, rhs);
    let int_ty = d.int_ty();
    let value = d.lam_fv(b_fv, int_ty, term);
    let ty = d.pi_fv(b_fv, int_ty, concl);
    let value = d.lam_fv(a_fv, int_ty, value);
    let ty = d.pi_fv(a_fv, int_ty, ty);
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
            let ab = d.iadd(a, b);
            let ba = d.iadd(b, a);
            (ab, ba)
        })
        .expect("a + b = b + a must be admitted");
    });
}

#[test]
fn a_coefficient_off_by_one_is_rejected_by_the_kernel() {
    on_a_deep_stack(|| {
        let verdict = kernel_verdict_on(&|d, a, _b| {
            let aa = d.iadd(a, a);
            (aa, a)
        });
        assert!(
            verdict.is_err(),
            "the kernel admitted `a + a = a`, forced past the procedure's own check",
        );
    });
}

#[test]
fn an_extra_constant_is_rejected_by_the_kernel() {
    on_a_deep_stack(|| {
        let verdict = kernel_verdict_on(&|d, a, b| {
            let ab = d.iadd(a, b);
            let one = d.ione();
            let ab1 = d.iadd(ab, one);
            (ab, ab1)
        });
        assert!(
            verdict.is_err(),
            "the kernel admitted `a + b = a + b + 1`, forced past the procedure's own check",
        );
    });
}

#[test]
fn a_swapped_variable_is_rejected_by_the_kernel() {
    on_a_deep_stack(|| {
        let verdict = kernel_verdict_on(&|d, a, b| {
            let a_only = d.iadd(a, a);
            let a_b = d.iadd(a, b);
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
        let mut d = IntDev::new(&mut env.k, p);
        let a_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let aa = d.iadd(a, a);
        let got = ring::prove_eq(&mut d, &p, aa, a);
        assert_eq!(got.err(), Some(Decline::NotAnIdentity));
    });
}

// ---------------------------------------------------------------------------
// 4. the fragment's boundary
// ---------------------------------------------------------------------------

#[test]
fn a_goal_containing_ediv_declines_nonring() {
    on_a_deep_stack(|| {
        let got = attempt(&|d, v| {
            let q = d.iediv(v[0], v[1]);
            d.ieq(q, v[0])
        });
        assert_eq!(got, Err(Decline::NonRing));
    });
}

#[test]
fn a_goal_containing_emod_declines_nonring() {
    on_a_deep_stack(|| {
        let got = attempt(&|d, v| {
            let r = d.iemod(v[0], v[1]);
            d.ieq(r, v[0])
        });
        assert_eq!(got, Err(Decline::NonRing));
    });
}

#[test]
fn commuting_two_products_is_an_identity() {
    on_a_deep_stack(|| {
        let got = attempt(&|d, v| {
            let xy = d.imul(v[0], v[1]);
            let yx = d.imul(v[1], v[0]);
            d.ieq(xy, yx)
        });
        assert!(got.is_ok(), "x*y = y*x must be proved: {got:?}");
    });
}

#[test]
fn a_wrong_intra_monomial_factor_declines() {
    on_a_deep_stack(|| {
        let got = attempt(&|d, v| {
            let xy = d.imul(v[0], v[1]);
            let xx = d.imul(v[0], v[0]);
            d.ieq(xy, xx)
        });
        assert_eq!(got, Err(Decline::NotAnIdentity));
    });
}

#[test]
fn negating_a_compound_sum_distributes() {
    on_a_deep_stack(|| {
        // `neg (a+b) = (neg a) + (neg b)` -- exercises `flatten_neg`'s
        // `neg_add` branch directly (not reachable from any of the five
        // retirement targets).
        let got = attempt(&|d, v| {
            let sum = d.iadd(v[0], v[1]);
            let lhs = d.ineg(sum);
            let neg_a = d.ineg(v[0]);
            let neg_b = d.ineg(v[1]);
            let rhs = d.iadd(neg_a, neg_b);
            d.ieq(lhs, rhs)
        });
        assert!(
            got.is_ok(),
            "neg(a+b) = neg a + neg b must be proved: {got:?}"
        );
    });
}

#[test]
fn cancellation_in_the_middle_of_a_sum() {
    on_a_deep_stack(|| {
        // `w + a + (-a) + z = w + z` -- the cancelling pair sorts to a
        // MIDDLE position (nonempty prefix `[w]`, nonempty tail `[z]`),
        // exercising `cancel_pairs`'s general (k > 0) branch rather than the
        // `diff_of_squares`-shaped `k == 0` one.
        let mut env = Env::new();
        let p = env.p;
        let name = env.name("cancel_middle");
        let mut d = IntDev::new(&mut env.k, p);
        let ty = ring::theorem(&mut d, &p, name, 3, &|d, v| {
            let (w, a, z) = (v[0], v[1], v[2]);
            let neg_a = d.ineg(a);
            let wa = d.iadd(w, a);
            let wa_nega = d.iadd(wa, neg_a);
            let lhs = d.iadd(wa_nega, z);
            let rhs = d.iadd(w, z);
            d.ieq(lhs, rhs)
        })
        .unwrap_or_else(|e| panic!("cancel_middle: {e}"));
        let _ = ty;
    });
}

#[test]
fn a_dangling_negation_does_not_over_cancel() {
    on_a_deep_stack(|| {
        // `a + (-a) + a` is `a`, NOT `0` -- the cancellation pass must stop
        // after removing exactly one adjacent opposite pair, not chase the
        // leftover `a` into cancelling something it never paired with.
        let got = attempt(&|d, v| {
            let neg_a = d.ineg(v[0]);
            let a_nega = d.iadd(v[0], neg_a);
            let lhs = d.iadd(a_nega, v[0]);
            d.ieq(lhs, v[0])
        });
        assert!(got.is_ok(), "a + (-a) + a = a must be proved: {got:?}");
    });
}

#[test]
fn a_negated_atom_times_a_negated_atom_is_positive() {
    on_a_deep_stack(|| {
        // `(neg a) * (neg b) = a*b` -- the `(true, true)` sign case in
        // `apply_mono_signs`, not reachable from any of the five targets.
        let got = attempt(&|d, v| {
            let neg_a = d.ineg(v[0]);
            let neg_b = d.ineg(v[1]);
            let lhs = d.imul(neg_a, neg_b);
            let rhs = d.imul(v[0], v[1]);
            d.ieq(lhs, rhs)
        });
        assert!(got.is_ok(), "(-a)*(-b) = a*b must be proved: {got:?}");
    });
}
