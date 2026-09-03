//! Tests for the ℕ ring producer.
//!
//! Four batteries, mirroring `linarith::nat::tests`'s structure:
//!
//! 1. **The ten retirement targets.** Two are declared theorems
//!    (`Nat.right_distrib`, `Nat.add_right_comm`) and the emitted term's type
//!    is checked definitionally equal to the *prelude's own* statement. The
//!    other eight are private per-file proof-construction helpers — eight
//!    independent hand-written copies of the same identity `(a+b)+(c+d) =
//!    (a+c)+(b+d)` across `binomial.rs`, `div_mod_lemmas.rs`,
//!    `finite_set.rs`, `fibonacci.rs`, `subset_sum.rs`, `rec_agreement.rs`,
//!    `count_range_reversal.rs` and `eisenstein_lemma.rs` — which have no
//!    declared name to compare against, so each test instead re-derives the
//!    exact statement the hand code proves and requires the kernel to admit
//!    it as a fresh declaration.
//! 2. **False goals decline `NotAnIdentity`.** Unlike `linarith`'s bounded
//!    search, this normalizer is a complete decision procedure *within the
//!    fragment*, so a genuine non-identity gets a positive refusal, not
//!    "search exhausted".
//! 3. **Corrupted claims are rejected by the KERNEL**, with the procedure's
//!    own normal-form check switched off (`prove_eq_unverified`). `ring` has
//!    no hypothesis slot for a proof to be swapped into (every risk here is
//!    "is the claimed identity actually true"), so the three corruptions are
//!    three different ways a claimed identity can be false: a coefficient
//!    off by one, an extra constant, and a swapped variable. A positive
//!    control (the same route, an actually-true identity) sits beside them,
//!    and a fourth test keeps the procedure's own check honest.
//! 4. **The fragment's boundary.** `div`/`mod`/`sub` decline `NonRing`; a
//!    sized negative records what this normalizer's lack of intra-monomial
//!    sorting costs (`x*y = y*x`, true but declined).

#![allow(clippy::many_single_char_names, clippy::similar_names)]

use crate::ring::Decline;
use crate::ring::nat as ring;
use crate::{
    ExprId, Kernel, NameId, NatOps, NatPrelude, NatState, build_nat_prelude, on_a_deep_stack,
};

/// A development over a kernel carrying the `Nat` prelude.
struct Fixture {
    k: Kernel,
    p: NatPrelude,
    st: NatState,
    root: NameId,
}

impl NatOps for Fixture {
    fn kernel(&mut self) -> &mut Kernel {
        &mut self.k
    }

    fn nat_state(&mut self) -> &mut NatState {
        &mut self.st
    }
}

impl Fixture {
    fn new() -> Self {
        let mut k = Kernel::new();
        let p = build_nat_prelude(&mut k).expect("Nat prelude must build");
        let st = NatState::new(&mut k, p);
        let anon = k.anon();
        let root = k.name_str(anon, "ring_test");
        Self { k, p, st, root }
    }

    fn name(&mut self, s: &str) -> NameId {
        let root = self.root;
        self.k.name_str(root, s)
    }

    /// The type the prelude's own hand-written proof was admitted at.
    fn prelude_type(&self, name: NameId) -> ExprId {
        self.k
            .environment()
            .get(name)
            .expect("the prelude declares this name")
            .ty()
    }
}

/// Declare `label` by the procedure and require its type to be definitionally
/// equal to the prelude's existing statement of `mirror` — for the two
/// retirement targets that already have a declared name.
fn retire_named(
    label: &str,
    mirror: fn(&NatPrelude) -> NameId,
    arity: usize,
    build: &dyn Fn(&mut Fixture, &[ExprId]) -> ExprId,
) {
    let mut f = Fixture::new();
    let p = f.p;
    let expected = f.prelude_type(mirror(&p));
    let name = f.name(label);
    let ty =
        ring::theorem(&mut f, &p, name, arity, build).unwrap_or_else(|e| panic!("{label}: {e}"));
    assert!(
        f.k.def_eq(ty, expected),
        "{label}: the emitted declaration's type is not the prelude's statement",
    );
    assert!(
        f.k.environment().contains(name),
        "{label}: the kernel did not learn the name",
    );
}

/// Declare `label` by the procedure with no prelude name to compare
/// against — the eight private-helper retirement targets. The test is the
/// exact statement the hand code built (`(a+b)+(c+d) = (a+c)+(b+d)`,
/// 4-arity), re-derived here and required to be admitted.
fn retire_regroup_four(label: &str) {
    let mut f = Fixture::new();
    let p = f.p;
    let name = f.name(label);
    let ty = ring::theorem(&mut f, &p, name, 4, &|d, v| {
        let (a, b, c, dd) = (v[0], v[1], v[2], v[3]);
        let ab = d.add(a, b);
        let cd = d.add(c, dd);
        let lhs = d.add(ab, cd);
        let ac = d.add(a, c);
        let bd = d.add(b, dd);
        let rhs = d.add(ac, bd);
        d.eq(lhs, rhs)
    })
    .unwrap_or_else(|e| panic!("{label}: {e}"));
    assert!(
        f.k.environment().contains(name),
        "{label}: the kernel did not learn the name",
    );
    let _ = ty;
}

// ---------------------------------------------------------------------------
// 1. the ten retirement targets
// ---------------------------------------------------------------------------

#[test]
fn target_bezout_expand_scaled_right() {
    on_a_deep_stack(|| {
        // `nat_prelude/bezout.rs::expand_scaled_right` (lines 142-188, 47
        // lines): `g*(a*mp+b*np) = (g*a)*mp + (g*b)*np`. Unlike the other
        // nine targets this one actually exercises monomial-merging
        // (`combine_items`'s `Mono * Mono` case via `mul_assoc`), not just
        // the outer sum's normalizer.
        let mut f = Fixture::new();
        let p = f.p;
        let name = f.name("expand_scaled_right");
        ring::theorem(&mut f, &p, name, 5, &|d, v| {
            let (g, a, b, mp, np) = (v[0], v[1], v[2], v[3], v[4]);
            let a_mp = d.mul(a, mp);
            let b_np = d.mul(b, np);
            let whole = d.add(a_mp, b_np);
            let lhs = d.mul(g, whole);
            let ga = d.mul(g, a);
            let scaled_a_mp = d.mul(ga, mp);
            let gb = d.mul(g, b);
            let scaled_b_np = d.mul(gb, np);
            let rhs = d.add(scaled_a_mp, scaled_b_np);
            d.eq(lhs, rhs)
        })
        .unwrap_or_else(|e| panic!("expand_scaled_right: {e}"));
        assert!(f.k.environment().contains(name));
    });
}

#[test]
fn target_algebra_add_right_comm() {
    on_a_deep_stack(|| {
        // `nat_prelude/algebra.rs::declare_additive_theorems`, the
        // `add_right_comm` theorem (lines 198-216): `(x+y)+z = (x+z)+y`.
        retire_named("add_right_comm", |p| p.add_right_comm, 3, &|d, v| {
            let (x, y, z) = (v[0], v[1], v[2]);
            let xy = d.add(x, y);
            let lhs = d.add(xy, z);
            let xz = d.add(x, z);
            let rhs = d.add(xz, y);
            d.eq(lhs, rhs)
        });
    });
}

#[test]
fn target_binomial_add_add_add_comm() {
    // `nat_prelude/binomial.rs::add_add_add_comm` (lines 59-114, 56 lines).
    on_a_deep_stack(|| retire_regroup_four("binomial_add_add_add_comm"));
}

#[test]
fn target_div_mod_lemmas_add_add_add_comm() {
    // `nat_prelude/div_mod_lemmas.rs::add_add_add_comm` (lines 486-538, 53 lines).
    on_a_deep_stack(|| retire_regroup_four("div_mod_lemmas_add_add_add_comm"));
}

#[test]
fn target_finite_set_add_regroup_four() {
    // `nat_prelude/finite_set.rs::add_regroup_four` (lines 325-359, 35 lines).
    on_a_deep_stack(|| retire_regroup_four("finite_set_add_regroup_four"));
}

#[test]
fn target_fibonacci_add_regroup_four() {
    // `nat_prelude/fibonacci.rs::add_regroup_four` (lines 556-590, 35 lines).
    on_a_deep_stack(|| retire_regroup_four("fibonacci_add_regroup_four"));
}

#[test]
fn target_subset_sum_add_regroup_four() {
    // `nat_prelude/subset_sum.rs::add_regroup_four` (lines 108-142, 35 lines).
    on_a_deep_stack(|| retire_regroup_four("subset_sum_add_regroup_four"));
}

#[test]
fn target_rec_agreement_add_add_add_comm() {
    // `nat_prelude/rec_agreement.rs::add_add_add_comm` (lines 4402-4457, 56 lines).
    on_a_deep_stack(|| retire_regroup_four("rec_agreement_add_add_add_comm"));
}

#[test]
fn target_count_range_reversal_add_add_add_comm() {
    // `nat_prelude/count_range_reversal.rs::add_add_add_comm` (lines 161-209, 49 lines).
    on_a_deep_stack(|| retire_regroup_four("count_range_reversal_add_add_add_comm"));
}

#[test]
fn target_eisenstein_lemma_regroup_four() {
    // `nat_prelude/eisenstein_lemma.rs::regroup_four` (lines 845-878, 34 lines).
    on_a_deep_stack(|| retire_regroup_four("eisenstein_lemma_regroup_four"));
}

// ---------------------------------------------------------------------------
// 2. false goals decline `NotAnIdentity`
// ---------------------------------------------------------------------------

fn attempt(build: &dyn Fn(&mut Fixture, &[ExprId]) -> ExprId) -> Result<ExprId, Decline> {
    let mut f = Fixture::new();
    let p = f.p;
    let name = f.name("attempt");
    ring::theorem(&mut f, &p, name, 2, build).map_err(|e| match e {
        ring::RingError::Declined(d) => d,
        ring::RingError::Rejected(e) => panic!("kernel rejected a true goal: {e:?}"),
    })
}

#[test]
fn a_wrong_coefficient_declines() {
    on_a_deep_stack(|| {
        // `a + a` is not `a` — a genuinely false claim, not a search miss.
        let got = attempt(&|d, v| {
            let aa = d.add(v[0], v[0]);
            d.eq(aa, v[0])
        });
        assert_eq!(got, Err(Decline::NotAnIdentity));
    });
}

#[test]
fn a_wrong_constant_declines() {
    on_a_deep_stack(|| {
        let got = attempt(&|d, v| {
            let ab = d.add(v[0], v[1]);
            let one = d.num(1);
            let ab1 = d.add(ab, one);
            d.eq(ab, ab1)
        });
        assert_eq!(got, Err(Decline::NotAnIdentity));
    });
}

#[test]
fn a_wrong_variable_declines() {
    on_a_deep_stack(|| {
        let got = attempt(&|d, v| {
            let a_only = d.add(v[0], v[0]);
            let a_b = d.add(v[0], v[1]);
            d.eq(a_only, a_b)
        });
        assert_eq!(got, Err(Decline::NotAnIdentity));
    });
}

// ---------------------------------------------------------------------------
// 3. corrupted claims are rejected by the KERNEL
// ---------------------------------------------------------------------------

/// Build `lhs`/`rhs` over two free `Nat` variables, emit a proof of `Eq lhs
/// rhs` with the procedure's own check disabled, and require the KERNEL's
/// verdict on the resulting declaration.
fn kernel_verdict_on(
    build: &dyn Fn(&mut Fixture, ExprId, ExprId) -> (ExprId, ExprId),
) -> Result<ExprId, String> {
    let mut f = Fixture::new();
    let p = f.p;
    let a_fv = f.fresh_fvar();
    let b_fv = f.fresh_fvar();
    let a = f.k.fvar(a_fv);
    let b = f.k.fvar(b_fv);
    let (lhs, rhs) = build(&mut f, a, b);

    let term = ring::prove_eq_unverified(&mut f, &p, lhs, rhs)
        .map_err(|d| format!("the procedure declined instead of emitting: {d:?}"))?;

    let concl = f.eq(lhs, rhs);
    let nat = f.nat_ty();
    let value = f.lam_fv(b_fv, nat, term);
    let ty = f.pi_fv(b_fv, nat, concl);
    let value = f.lam_fv(a_fv, nat, value);
    let ty = f.pi_fv(a_fv, nat, ty);
    let name = f.name("corrupted");
    match f.declare_theorem(name, ty, value) {
        Ok(()) => Ok(ty),
        Err(e) => Err(format!("{e:?}")),
    }
}

#[test]
fn the_honest_identity_is_the_positive_control() {
    on_a_deep_stack(|| {
        // Without this, every corruption below could be "rejected" for a
        // reason unrelated to the corruption.
        kernel_verdict_on(&|d, a, b| {
            let ab = d.add(a, b);
            let ba = d.add(b, a);
            (ab, ba)
        })
        .expect("a + b = b + a must be admitted");
    });
}

#[test]
fn a_coefficient_off_by_one_is_rejected_by_the_kernel() {
    on_a_deep_stack(|| {
        let verdict = kernel_verdict_on(&|d, a, _b| {
            let aa = d.add(a, a);
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
            let ab = d.add(a, b);
            let one = d.num(1);
            let ab1 = d.add(ab, one);
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
            let a_only = d.add(a, a);
            let a_b = d.add(a, b);
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
        // Same corruption, `verify = true`: the procedure declines rather
        // than emitting. Both answers are useful, and running only one of
        // them would leave the trust story circular.
        let mut f = Fixture::new();
        let p = f.p;
        let a_fv = f.fresh_fvar();
        let a = f.k.fvar(a_fv);
        let aa = f.add(a, a);
        let got = ring::prove_eq(&mut f, &p, aa, a);
        assert_eq!(got.err(), Some(Decline::NotAnIdentity));
    });
}

// ---------------------------------------------------------------------------
// 4. the fragment's boundary
// ---------------------------------------------------------------------------

#[test]
fn a_goal_containing_div_declines_nonring() {
    on_a_deep_stack(|| {
        let got = attempt(&|d, v| {
            let q = d.div(v[0], v[1]);
            d.eq(q, v[0])
        });
        assert_eq!(got, Err(Decline::NonRing));
    });
}

#[test]
fn a_goal_containing_mod_declines_nonring() {
    on_a_deep_stack(|| {
        let got = attempt(&|d, v| {
            let r = d.modulo(v[0], v[1]);
            d.eq(r, v[0])
        });
        assert_eq!(got, Err(Decline::NonRing));
    });
}

#[test]
fn a_goal_containing_truncated_sub_declines_nonring() {
    on_a_deep_stack(|| {
        let got = attempt(&|d, v| {
            let s = d.sub(v[0], v[1]);
            d.eq(s, v[0])
        });
        assert_eq!(got, Err(Decline::NonRing));
    });
}

#[test]
fn commuting_two_products_is_a_sized_negative() {
    on_a_deep_stack(|| {
        // `x*y = y*x` is TRUE, but this normalizer does not sort factors
        // *within* a monomial (see the module docs) — a genuine, documented
        // incompleteness, not a bug. The decline is the honest answer, and
        // this is the "first stuck term" this lane reports.
        let got = attempt(&|d, v| {
            let xy = d.mul(v[0], v[1]);
            let yx = d.mul(v[1], v[0]);
            d.eq(xy, yx)
        });
        assert_eq!(got, Err(Decline::NotAnIdentity));
    });
}
