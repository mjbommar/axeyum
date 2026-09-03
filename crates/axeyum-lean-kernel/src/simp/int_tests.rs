//! Tests for the ℤ `simp` producer.
//!
//! Four batteries, mirroring `simp::nat::tests`'s structure:
//!
//! 1. **Three retirement targets** — fewer than ℕ's ten, and precisely why is
//!    part of the finding: `IntPrelude` has no `zero_add`/`zero_mul`, so a
//!    goal needing the reversed argument order must route through
//!    `add_comm`/`mul_comm` as an extra rule, and (per the module docs) that
//!    is only SAFE when the goal's post-annihilation fixed point has no
//!    `add`/`mul` structure left for comm to keep re-swapping. A wide search
//!    of `int_prelude` for hypothesis-free, induction-free rewrite chains
//!    found exactly three call sites with that shape (`add_left_neg`,
//!    `zero_mul_eq_zero`, `zero_add`); several more plausible-looking
//!    candidates (`neg_mul`, `neg_mul_neg`) were tried and DECLINED
//!    `BudgetExceeded` when actually run, because their fixed point still
//!    contains a bare commuting pair — see `a_neg_mul_shaped_goal_is_not_a_
//!    safe_retirement_target` below, which pins that finding as a test
//!    rather than leaving it as a claim in a doc comment.
//! 2. **Goals needing a lemma outside the default set decline
//!    `NoProgress`.**
//! 3. **Corrupted claims are rejected by the KERNEL**, own-check disabled.
//! 4. **A looping rule set declines `BudgetExceeded`, not a hang** — over ℤ
//!    this is reachable even WITH the default set present, since neither
//!    `add`'s nor `mul`'s defaults fire on two bare symbolic atoms.

#![allow(clippy::many_single_char_names, clippy::similar_names)]

use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::simp::Decline;
use crate::simp::int::{self as simp, Rule};
use crate::{IntPrelude, Kernel, NameId, NatOps, build_int_prelude, on_a_deep_stack};

/// A kernel carrying the integer prelude, plus a name root of this suite's own.
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
        let root = k.name_str(anon, "simp_int_test");
        Self { k, p, root }
    }

    fn name(&mut self, s: &str) -> NameId {
        let root = self.root;
        self.k.name_str(root, s)
    }
}

/// Declare `label` under `rules_of(&p)` (built from THIS test's own `Env`,
/// never a throwaway probe kernel — `NameId`s are per-kernel, so a rule set
/// built against a different kernel's `IntPrelude` would silently cite the
/// wrong names), and require the kernel to admit it AND `Kernel::infer` to
/// independently accept the emitted proof at the declared type — the same
/// double-check `simp::nat::tests::retire` uses.
fn retire(
    label: &str,
    rules_of: &dyn Fn(&IntPrelude) -> Vec<Rule>,
    arity: usize,
    build: &dyn Fn(&mut IntDev<'_>, &[ExprId]) -> (ExprId, ExprId),
) {
    let mut env = Env::new();
    let p = env.p;
    let rules = rules_of(&p);
    let name = env.name(label);
    {
        let mut d = IntDev::new(&mut env.k, p);
        simp::theorem(&mut d, &rules, name, arity, build)
            .unwrap_or_else(|e| panic!("{label}: {e}"));
    }
    assert!(
        env.k.environment().contains(name),
        "{label}: the kernel did not learn the name",
    );
    let ty = env.k.environment().get(name).expect("declared").ty();
    let value = env
        .k
        .environment()
        .get(name)
        .expect("declared")
        .value()
        .expect("a theorem carries a value");
    let inferred = env
        .k
        .infer(value)
        .unwrap_or_else(|e| panic!("{label}: Kernel::infer rejected the emitted proof: {e:?}"));
    assert!(
        env.k.def_eq(inferred, ty),
        "{label}: Kernel::infer's type is not the declared statement",
    );
}

// ---------------------------------------------------------------------------
// 1. three retirement targets
// ---------------------------------------------------------------------------

#[test]
fn target_add_basics_declare_add_left_neg() {
    // `int_prelude/add_basics.rs::declare_add_left_neg` (lines 26-43, 18
    // lines): `Eq (add (neg a) a) zero`, via `add_comm` (extra, ordered
    // after the defaults) then `add_neg` (default).
    on_a_deep_stack(|| {
        retire(
            "add_left_neg",
            &|p| simp::with_extra(&simp::default_rules(p), &[simp::rule_add_comm(p)]),
            1,
            &|d, v| {
                let a = v[0];
                let neg_a = d.ineg(a);
                let lhs = d.iadd(neg_a, a);
                let zero = d.izero();
                (lhs, zero)
            },
        );
    });
}

#[test]
fn target_sign_product_zero_mul_eq_zero() {
    // `int_prelude/sign_product.rs::zero_mul_eq_zero` (lines 78-89, 12
    // lines): `Eq (mul zero x) zero`, via `mul_comm` (extra) then
    // `mul_zero` (default). There is no `zero_mul` law in `IntPrelude`.
    on_a_deep_stack(|| {
        retire(
            "zero_mul_eq_zero",
            &|p| simp::with_extra(&simp::default_rules(p), &[simp::rule_mul_comm(p)]),
            1,
            &|d, v| {
                let x = v[0];
                let zero = d.izero();
                let lhs = d.imul(zero, x);
                (lhs, zero)
            },
        );
    });
}

#[test]
fn target_fibonacci_zero_add() {
    // `int_prelude/fibonacci.rs::zero_add` (lines 1213-1222, 10 lines): `Eq
    // (add zero x) x`, via `add_comm` (extra) then `add_zero` (default).
    // There is no `zero_add` law in `IntPrelude` either.
    on_a_deep_stack(|| {
        retire(
            "zero_add",
            &|p| simp::with_extra(&simp::default_rules(p), &[simp::rule_add_comm(p)]),
            1,
            &|d, v| {
                let x = v[0];
                let zero = d.izero();
                let lhs = d.iadd(zero, x);
                (lhs, x)
            },
        );
    });
}

/// Pins the finding the module docs make in prose: `neg_mul`-shaped goals
/// (`Eq (mul (neg a) b) (neg (mul a b))`) are NOT reachable under this
/// engine even though they look similar to the three targets above, because
/// their fixed point still contains a bare commuting `mul` pair.
#[test]
fn a_neg_mul_shaped_goal_is_not_a_safe_retirement_target() {
    on_a_deep_stack(|| {
        let mut env = Env::new();
        let p = env.p;
        let defaults = simp::default_rules(&p);
        let extra = [simp::rule_mul_comm(&p)];
        let rules = simp::with_extra(&defaults, &extra);
        let mut d = IntDev::new(&mut env.k, p);
        let a_fv = d.fresh_fvar();
        let b_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let b = d.kernel().fvar(b_fv);
        let neg_a = d.ineg(a);
        let lhs = d.imul(neg_a, b);
        let ab = d.imul(a, b);
        let rhs = d.ineg(ab);
        let got = simp::prove_eq(&mut d, &rules, lhs, rhs);
        assert_eq!(got, Err(Decline::BudgetExceeded));
    });
}

// ---------------------------------------------------------------------------
// 2. goals needing a lemma outside the default set decline `NoProgress`
// ---------------------------------------------------------------------------

#[test]
fn a_goal_needing_add_comm_declines_no_progress() {
    on_a_deep_stack(|| {
        let mut env = Env::new();
        let p = env.p;
        let rules = simp::default_rules(&p);
        let mut d = IntDev::new(&mut env.k, p);
        let a_fv = d.fresh_fvar();
        let b_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let b = d.kernel().fvar(b_fv);
        let lhs = d.iadd(a, b);
        let rhs = d.iadd(b, a);
        let got = simp::prove_eq(&mut d, &rules, lhs, rhs);
        assert_eq!(got, Err(Decline::NoProgress));
    });
}

#[test]
fn a_goal_needing_mul_comm_declines_no_progress() {
    on_a_deep_stack(|| {
        let mut env = Env::new();
        let p = env.p;
        let rules = simp::default_rules(&p);
        let mut d = IntDev::new(&mut env.k, p);
        let a_fv = d.fresh_fvar();
        let b_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let b = d.kernel().fvar(b_fv);
        let lhs = d.imul(a, b);
        let rhs = d.imul(b, a);
        let got = simp::prove_eq(&mut d, &rules, lhs, rhs);
        assert_eq!(got, Err(Decline::NoProgress));
    });
}

// ---------------------------------------------------------------------------
// 3. corrupted claims are rejected by the KERNEL
// ---------------------------------------------------------------------------

fn kernel_verdict_on(
    build: &dyn Fn(&mut IntDev<'_>, ExprId, ExprId) -> (ExprId, ExprId),
) -> Result<NameId, String> {
    let mut env = Env::new();
    let p = env.p;
    let rules = simp::default_rules(&p);
    let name = env.name("corrupted");
    let mut d = IntDev::new(&mut env.k, p);
    let a_fv = d.fresh_fvar();
    let b_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b = d.kernel().fvar(b_fv);
    let (lhs, rhs) = build(&mut d, a, b);

    let term = simp::prove_eq_unverified(&mut d, &rules, lhs, rhs)
        .map_err(|e| format!("the procedure declined instead of emitting: {e:?}"))?;

    let int_ty = d.int_ty();
    let concl = d.ieq(lhs, rhs);
    let value = d.lam_fv(b_fv, int_ty, term);
    let ty = d.pi_fv(b_fv, int_ty, concl);
    let value = d.lam_fv(a_fv, int_ty, value);
    let ty = d.pi_fv(a_fv, int_ty, ty);
    match d
        .kernel()
        .add_declaration(crate::env::Declaration::Theorem {
            name,
            uparams: vec![],
            ty,
            value,
        }) {
        Ok(()) => Ok(name),
        Err(e) => Err(format!("{e:?}")),
    }
}

#[test]
fn the_honest_identity_is_the_positive_control() {
    on_a_deep_stack(|| {
        kernel_verdict_on(&|d, a, _b| {
            let z = d.izero();
            let lhs = d.iadd(a, z);
            (lhs, a)
        })
        .expect("a + 0 = a must be admitted");
    });
}

#[test]
fn an_unrelated_right_hand_side_is_rejected_by_the_kernel() {
    on_a_deep_stack(|| {
        // `a + 0 = b`: the LHS rewrites to `a` (1 step, `add_zero`); `b` is
        // an unrelated free variable (0 steps).
        let verdict = kernel_verdict_on(&|d, a, b| {
            let z = d.izero();
            let lhs = d.iadd(a, z);
            (lhs, b)
        });
        assert!(
            verdict.is_err(),
            "the kernel admitted `a + 0 = b`, forced past the procedure's own check",
        );
    });
}

#[test]
fn an_extra_operand_is_rejected_by_the_kernel() {
    on_a_deep_stack(|| {
        // `a + 0 = a * 1 + 1`-shaped: LHS rewrites to `a` (1 step); RHS
        // (`add (mul a one) one`) matches no default at its root.
        let verdict = kernel_verdict_on(&|d, a, _b| {
            let z = d.izero();
            let lhs = d.iadd(a, z);
            let one = d.ione();
            let a_one = d.imul(a, one);
            let rhs = d.iadd(a_one, one);
            (lhs, rhs)
        });
        assert!(
            verdict.is_err(),
            "the kernel admitted a corrupted claim, forced past the procedure's own check",
        );
    });
}

#[test]
fn a_swapped_variable_is_rejected_by_the_kernel() {
    on_a_deep_stack(|| {
        // `a + 0 = b + 0`: BOTH sides rewrite (`add_zero`, one step each),
        // to `a` and `b` respectively -- two DIFFERENT free variables.
        let verdict = kernel_verdict_on(&|d, a, b| {
            let z = d.izero();
            let lhs = d.iadd(a, z);
            let rhs = d.iadd(b, z);
            (lhs, rhs)
        });
        assert!(
            verdict.is_err(),
            "the kernel admitted `a + 0 = b + 0`, forced past the procedure's own check",
        );
    });
}

#[test]
fn the_procedures_own_check_also_catches_a_corrupted_claim() {
    on_a_deep_stack(|| {
        let mut env = Env::new();
        let p = env.p;
        let rules = simp::default_rules(&p);
        let mut d = IntDev::new(&mut env.k, p);
        let a_fv = d.fresh_fvar();
        let b_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let b = d.kernel().fvar(b_fv);
        let z = d.izero();
        let lhs = d.iadd(a, z);
        let rhs = d.iadd(b, z);
        let got = simp::prove_eq(&mut d, &rules, lhs, rhs);
        assert_eq!(got.err(), Some(Decline::SidesDiffer));
    });
}

// ---------------------------------------------------------------------------
// 4. a looping rule set declines `BudgetExceeded`, not a hang
// ---------------------------------------------------------------------------

#[test]
fn add_comm_extra_on_a_bare_symbolic_pair_declines_budget_exceeded() {
    on_a_deep_stack(|| {
        // `a + b = b + a` is TRUE, but with two bare symbolic atoms neither
        // `add`'s nor `mul`'s defaults ever fire, so `add_comm` (the extra)
        // is the ONLY applicable rule at every step and oscillates forever.
        let mut env = Env::new();
        let p = env.p;
        let defaults = simp::default_rules(&p);
        let extra = [simp::rule_add_comm(&p)];
        let rules = simp::with_extra(&defaults, &extra);
        let mut d = IntDev::new(&mut env.k, p);
        let a_fv = d.fresh_fvar();
        let b_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let b = d.kernel().fvar(b_fv);
        let lhs = d.iadd(a, b);
        let rhs = d.iadd(b, a);
        let got = simp::prove_eq(&mut d, &rules, lhs, rhs);
        assert_eq!(got, Err(Decline::BudgetExceeded));
    });
}
