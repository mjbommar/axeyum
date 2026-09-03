//! Tests for the ℕ `simp` producer.
//!
//! Four batteries, mirroring `ring::nat::tests`'s structure (see its module
//! docs):
//!
//! 1. **The ten retirement targets** — private per-file proof-construction
//!    helpers with no declared name to compare against, so each test
//!    re-derives the exact statement the hand code proves and requires the
//!    kernel to admit it as a fresh declaration. Two of the ten shapes
//!    (`one_add_eq_succ`, `two_mul_eq_add`) are each proved by TWO
//!    independent call sites — a duplicated-helper finding in the style of
//!    ADR-1580's `add_add_add_comm` family.
//! 2. **Goals needing a lemma outside the default set decline
//!    `NoProgress`** — a commutativity/associativity law is never in the
//!    default set (see the crate-root module docs on why it cannot
//!    terminate here), so a goal that genuinely needs one gets a plain "did
//!    not move" refusal on both sides.
//! 3. **Corrupted claims are rejected by the KERNEL**, with the procedure's
//!    own "did both sides converge to the same term" check switched off
//!    (`prove_eq_unverified`).
//! 4. **A looping rule set declines `BudgetExceeded`, not a hang.**

#![allow(clippy::many_single_char_names, clippy::similar_names)]

use crate::simp::Decline;
use crate::simp::nat::{self as simp, Rule};
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
        let root = k.name_str(anon, "simp_test");
        Self { k, p, st, root }
    }

    fn name(&mut self, s: &str) -> NameId {
        let root = self.root;
        self.k.name_str(root, s)
    }
}

/// Declare `label` by the procedure, under the default ℕ rule set, with no
/// prelude name to compare against; requires the kernel to admit it.
fn retire(label: &str, arity: usize, build: &dyn Fn(&mut Fixture, &[ExprId]) -> ExprId) {
    let mut f = Fixture::new();
    let p = f.p;
    let rules: Vec<Rule<Fixture>> = simp::default_rules(&p);
    let name = f.name(label);
    let ty = simp::theorem(&mut f, &p, &rules, name, arity, build)
        .unwrap_or_else(|e| panic!("{label}: {e}"));
    assert!(
        f.k.environment().contains(name),
        "{label}: the kernel did not learn the name",
    );
    // The emitted declaration must also be independently accepted by
    // `Kernel::infer` at its own stated type -- not merely "add_declaration
    // returned Ok", the same double-check `ring`/`linarith` use.
    let value =
        f.k.environment()
            .get(name)
            .expect("declared")
            .value()
            .expect("a theorem carries a value");
    let inferred =
        f.k.infer(value)
            .unwrap_or_else(|e| panic!("{label}: Kernel::infer rejected the emitted proof: {e:?}"));
    assert!(
        f.k.def_eq(inferred, ty),
        "{label}: Kernel::infer's type is not the declared statement",
    );
}

// ---------------------------------------------------------------------------
// 1. the ten retirement targets
// ---------------------------------------------------------------------------

#[test]
fn target_count_range_reversal_one_add_eq_succ() {
    // `nat_prelude/count_range_reversal.rs::one_add_eq_succ` (lines
    // 197-209, 13 lines): `Eq (add one n) (succ n)`, via `succ_add` +
    // `zero_add`.
    on_a_deep_stack(|| {
        retire("count_range_reversal_one_add_eq_succ", 1, &|d, v| {
            let n = v[0];
            let one = d.num(1);
            let lhs = d.add(one, n);
            let rhs = d.succ(n);
            d.eq(lhs, rhs)
        });
    });
}

#[test]
fn target_totient_lemmas_one_add_eq_succ() {
    // `nat_prelude/totient_lemmas.rs::one_add_eq_succ` (lines 1148-1163, 16
    // lines): a BYTE-IDENTICAL duplicate of the target above, at a second
    // call site -- an ADR-1580-style duplicated-helper finding.
    on_a_deep_stack(|| {
        retire("totient_lemmas_one_add_eq_succ", 1, &|d, v| {
            let n = v[0];
            let one = d.num(1);
            let lhs = d.add(one, n);
            let rhs = d.succ(n);
            d.eq(lhs, rhs)
        });
    });
}

#[test]
fn target_powsq_add_one_eq_succ() {
    // `nat_prelude/powsq.rs::add_one_eq_succ` (lines 93-108, 16 lines): `Eq
    // (add x one) (succ x)`, via `add_succ` + `add_zero` -- the mirror
    // direction of the `one_add_eq_succ` family (variable on the LEFT of
    // `add` here, not the right).
    on_a_deep_stack(|| {
        retire("powsq_add_one_eq_succ", 1, &|d, v| {
            let x = v[0];
            let one = d.num(1);
            let lhs = d.add(x, one);
            let rhs = d.succ(x);
            d.eq(lhs, rhs)
        });
    });
}

#[test]
fn target_gauss_lemma_two_mul_eq_add() {
    // `nat_prelude/gauss_lemma.rs::two_mul_eq_add` (lines 1329-1344, 16
    // lines): `Eq (mul 2 m) (add m m)`, via `succ_mul` + `one_mul`.
    on_a_deep_stack(|| {
        retire("gauss_lemma_two_mul_eq_add", 1, &|d, v| {
            let m = v[0];
            let two = d.num(2);
            let lhs = d.mul(two, m);
            let rhs = d.add(m, m);
            d.eq(lhs, rhs)
        });
    });
}

#[test]
fn target_parity_mul_two_eq_add_self() {
    // `nat_prelude/parity.rs::mul_two_eq_add_self` (lines 533-549, 17
    // lines): a second, independent hand-written copy of the SAME identity
    // as the target above, at a second call site.
    on_a_deep_stack(|| {
        retire("parity_mul_two_eq_add_self", 1, &|d, v| {
            let k = v[0];
            let two = d.num(2);
            let lhs = d.mul(two, k);
            let rhs = d.add(k, k);
            d.eq(lhs, rhs)
        });
    });
}

#[test]
fn target_bit_order_double_eq() {
    // `nat_prelude/bit_order.rs::double_eq` (lines 25-31, 7 lines): `Eq
    // (add (add zero x) x) (add x x)`, via `zero_add` alone.
    on_a_deep_stack(|| {
        retire("bit_order_double_eq", 1, &|d, v| {
            let x = v[0];
            let zero = d.zero();
            let add_zero_x = d.add(zero, x);
            let lhs = d.add(add_zero_x, x);
            let rhs = d.add(x, x);
            d.eq(lhs, rhs)
        });
    });
}

#[test]
fn target_catalan_two_succ_eq() {
    // `nat_prelude/catalan.rs::two_succ_eq` (lines 129-138, 10 lines): `Eq
    // (add (succ np) np) (succ (add np np))`, via `succ_add` alone.
    on_a_deep_stack(|| {
        retire("catalan_two_succ_eq", 1, &|d, v| {
            let np = v[0];
            let snp = d.succ(np);
            let lhs = d.add(snp, np);
            let a2 = d.add(np, np);
            let rhs = d.succ(a2);
            d.eq(lhs, rhs)
        });
    });
}

#[test]
fn target_bezout_prove_bezout_zero_equation() {
    // `nat_prelude/bezout.rs::prove_bezout_zero_equation` (lines 365-383,
    // 19 lines): `Eq ((n + 0*0) + n*0) (0*0 + n*1)`, both sides reducing to
    // `n` -- the deepest of the ten, exercising nested descent (the
    // rewrite site is inside TWO layers of `add`) on both sides.
    on_a_deep_stack(|| {
        retire("bezout_prove_bezout_zero_equation", 1, &|d, v| {
            let n = v[0];
            let zero = d.zero();
            let one = d.num(1);
            let zero_zero = d.mul(zero, zero);
            let n_zero = d.mul(n, zero);
            let first = d.add(n, zero_zero);
            let lhs = d.add(first, n_zero);
            let n_one = d.mul(n, one);
            let rhs = d.add(zero_zero, n_one);
            d.eq(lhs, rhs)
        });
    });
}

#[test]
fn target_add_factorial_lt_two_add_eq_succ_succ() {
    // `nat_prelude/add_factorial_lt.rs::two_add_eq_succ_succ` (lines
    // 121-148, 28 lines): `Eq (add 2 x) (succ (succ x))`, via `succ_add`
    // twice and `zero_add` once -- the deepest SUCC nesting among the ten.
    on_a_deep_stack(|| {
        retire("add_factorial_lt_two_add_eq_succ_succ", 1, &|d, v| {
            let x = v[0];
            let two = d.num(2);
            let lhs = d.add(two, x);
            let sx = d.succ(x);
            let rhs = d.succ(sx);
            d.eq(lhs, rhs)
        });
    });
}

#[test]
fn target_euler_distrib_one_plus() {
    // `nat_prelude/euler.rs::distrib_one_plus` (lines 91-104, 14 lines):
    // `Eq (mul (add one k) x) (add x (mul k x))`, via `right_distrib` (a
    // caller-supplied EXTRA rule, not in the default set -- see
    // `simp::nat::rule_right_distrib`'s docs) + `one_mul`.
    on_a_deep_stack(|| {
        let mut f = Fixture::new();
        let p = f.p;
        let defaults: Vec<Rule<Fixture>> = simp::default_rules(&p);
        let extra = [simp::rule_right_distrib::<Fixture>(&p)];
        let rules = simp::with_extra(&defaults, &extra);
        let name = f.name("euler_distrib_one_plus");
        simp::theorem(&mut f, &p, &rules, name, 2, &|d, v| {
            let (k, x) = (v[0], v[1]);
            let one = d.num(1);
            let one_plus_k = d.add(one, k);
            let lhs = d.mul(one_plus_k, x);
            let kx = d.mul(k, x);
            let rhs = d.add(x, kx);
            d.eq(lhs, rhs)
        })
        .unwrap_or_else(|e| panic!("euler_distrib_one_plus: {e}"));
        assert!(f.k.environment().contains(name));
    });
}

// ---------------------------------------------------------------------------
// 2. goals needing a lemma outside the default set decline `NoProgress`
// ---------------------------------------------------------------------------

fn attempt(build: &dyn Fn(&mut Fixture, &[ExprId]) -> ExprId) -> Result<ExprId, Decline> {
    let mut f = Fixture::new();
    let p = f.p;
    let rules: Vec<Rule<Fixture>> = simp::default_rules(&p);
    let name = f.name("attempt");
    simp::theorem(&mut f, &p, &rules, name, 2, build).map_err(|e| match e {
        simp::SimpError::Declined(d) => d,
        simp::SimpError::Rejected(e) => panic!("kernel rejected a true goal: {e:?}"),
    })
}

#[test]
fn a_goal_needing_add_comm_declines_no_progress() {
    on_a_deep_stack(|| {
        // `x + y = y + x` is TRUE, but the default set has no commutativity
        // law (see the crate-root module docs on why one can never be a
        // default), and neither `x` nor `y` is a literal `zero`/`succ`, so
        // no default rule matches anywhere in either side.
        let got = attempt(&|d, v| {
            let xy = d.add(v[0], v[1]);
            let yx = d.add(v[1], v[0]);
            d.eq(xy, yx)
        });
        assert_eq!(got, Err(Decline::NoProgress));
    });
}

#[test]
fn a_goal_needing_mul_comm_declines_no_progress() {
    on_a_deep_stack(|| {
        let got = attempt(&|d, v| {
            let xy = d.mul(v[0], v[1]);
            let yx = d.mul(v[1], v[0]);
            d.eq(xy, yx)
        });
        assert_eq!(got, Err(Decline::NoProgress));
    });
}

#[test]
fn a_goal_needing_add_assoc_declines_no_progress() {
    on_a_deep_stack(|| {
        let got = attempt(&|d, v| {
            let (x, y) = (v[0], v[1]);
            let z = x; // reuse a bound var as the third atom; still symbolic
            let xy = d.add(x, y);
            let lhs = d.add(xy, z);
            let yz = d.add(y, z);
            let rhs = d.add(x, yz);
            d.eq(lhs, rhs)
        });
        assert_eq!(got, Err(Decline::NoProgress));
    });
}

// ---------------------------------------------------------------------------
// 3. corrupted claims are rejected by the KERNEL
// ---------------------------------------------------------------------------

/// Build `lhs`/`rhs` over two free `Nat` variables, emit a proof of `Eq lhs
/// rhs` with the procedure's own convergence check disabled, and require
/// the KERNEL's verdict on the resulting declaration.
fn kernel_verdict_on(
    build: &dyn Fn(&mut Fixture, ExprId, ExprId) -> (ExprId, ExprId),
) -> Result<ExprId, String> {
    let mut f = Fixture::new();
    let p = f.p;
    let rules: Vec<Rule<Fixture>> = simp::default_rules(&p);
    let a_fv = f.fresh_fvar();
    let b_fv = f.fresh_fvar();
    let a = f.k.fvar(a_fv);
    let b = f.k.fvar(b_fv);
    let (lhs, rhs) = build(&mut f, a, b);

    let term = simp::prove_eq_unverified(&mut f, &rules, lhs, rhs)
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
        kernel_verdict_on(&|d, a, _b| {
            let zero = d.zero();
            let lhs = d.add(zero, a);
            (lhs, a)
        })
        .expect("0 + a = a must be admitted");
    });
}

#[test]
fn an_unrelated_right_hand_side_is_rejected_by_the_kernel() {
    on_a_deep_stack(|| {
        // `0 + a = b`: the LHS rewrites (1 step, `zero_add`) to `a`; `b` is
        // an unrelated free variable the procedure never touches (0 steps).
        // A genuinely false claim for `a != b`.
        let verdict = kernel_verdict_on(&|d, a, b| {
            let zero = d.zero();
            let lhs = d.add(zero, a);
            (lhs, b)
        });
        assert!(
            verdict.is_err(),
            "the kernel admitted `0 + a = b`, forced past the procedure's own check",
        );
    });
}

#[test]
fn an_extra_operand_is_rejected_by_the_kernel() {
    on_a_deep_stack(|| {
        // `0 + a = a + 1`: the LHS rewrites to `a`; the RHS (`add a one`)
        // matches no default rule (its second operand is `one`, not a
        // literal `zero`) and stays fixed. `a != a + 1` generically.
        let verdict = kernel_verdict_on(&|d, a, _b| {
            let zero = d.zero();
            let lhs = d.add(zero, a);
            let one = d.num(1);
            let rhs = d.add(a, one);
            (lhs, rhs)
        });
        assert!(
            verdict.is_err(),
            "the kernel admitted `0 + a = a + 1`, forced past the procedure's own check",
        );
    });
}

#[test]
fn a_swapped_variable_is_rejected_by_the_kernel() {
    on_a_deep_stack(|| {
        // `0 + a = 0 + b`: BOTH sides rewrite (`zero_add`, one step each),
        // to `a` and `b` respectively -- two DIFFERENT free variables.
        let verdict = kernel_verdict_on(&|d, a, b| {
            let zero = d.zero();
            let lhs = d.add(zero, a);
            let rhs = d.add(zero, b);
            (lhs, rhs)
        });
        assert!(
            verdict.is_err(),
            "the kernel admitted `0 + a = 0 + b`, forced past the procedure's own check",
        );
    });
}

#[test]
fn the_procedures_own_check_also_catches_a_corrupted_claim() {
    on_a_deep_stack(|| {
        // Same corruption as the swapped-variable case, `verify = true`:
        // the procedure declines rather than emitting. Both answers are
        // useful, and running only one of them would leave the trust story
        // circular.
        let mut f = Fixture::new();
        let p = f.p;
        let rules: Vec<Rule<Fixture>> = simp::default_rules(&p);
        let a_fv = f.fresh_fvar();
        let b_fv = f.fresh_fvar();
        let a = f.k.fvar(a_fv);
        let b = f.k.fvar(b_fv);
        let zero = f.zero();
        let lhs = f.add(zero, a);
        let rhs = f.add(zero, b);
        let got = simp::prove_eq(&mut f, &rules, lhs, rhs);
        assert_eq!(got.err(), Some(Decline::SidesDiffer));
    });
}

// ---------------------------------------------------------------------------
// 4. a looping rule set declines `BudgetExceeded`, not a hang
// ---------------------------------------------------------------------------

fn r_add_comm<D: NatOps>(d: &mut D, a: &[ExprId]) -> (ExprId, ExprId) {
    (d.add(a[0], a[1]), d.add(a[1], a[0]))
}

#[test]
fn add_comm_alone_declines_budget_exceeded_not_a_hang() {
    on_a_deep_stack(|| {
        // `add_comm`'s LHS pattern `add a b` matches ANY `add` application,
        // including its own output, so a rule set containing it alone never
        // reaches a fixed point -- see the crate-root module docs. The goal
        // itself (`x + y = y + x`) is TRUE; what is under test is that the
        // procedure declines within budget rather than looping.
        let mut f = Fixture::new();
        let p = f.p;
        let rules: Vec<Rule<Fixture>> = vec![Rule {
            name: p.add_comm,
            arity: 2,
            orientation: crate::simp::Orientation::Forward,
            build: r_add_comm,
        }];
        let x_fv = f.fresh_fvar();
        let y_fv = f.fresh_fvar();
        let x = f.k.fvar(x_fv);
        let y = f.k.fvar(y_fv);
        let lhs = f.add(x, y);
        let rhs = f.add(y, x);
        let got = simp::prove_eq(&mut f, &rules, lhs, rhs);
        assert_eq!(got, Err(Decline::BudgetExceeded));
    });
}
