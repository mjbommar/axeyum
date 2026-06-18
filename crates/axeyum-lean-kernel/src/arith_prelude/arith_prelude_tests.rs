//! Proof-term tests for the arithmetic prelude (ADR-0036, the LRA / Farkas
//! reconstruction foundation).
//!
//! These tests are the real deliverable: they **build proof terms** over the
//! axiomatized linear ordered field and `infer`-check them. A test passes only
//! if the trusted type-checker genuinely accepts the proof — exactly what
//! `la_generic` (Farkas) reconstruction will do. Covered: `lt_irrefl` applied,
//! `lt_trans`, `add_le_add`, and a **baby-Farkas refutation** deriving `False`
//! from `le a zero` and `le one a`. We also assert every axiom admits and the
//! environment has the expected declarations, plus a determinism check.
#![allow(clippy::similar_names, clippy::many_single_char_names)]

use crate::env::Declaration;
use crate::{ArithPrelude, BinderInfo, Kernel, build_arith_prelude};

/// A fixture: a kernel with the arithmetic prelude plus an abstract point
/// `a : R` and hypotheses are added per-test.
struct Fixture {
    k: Kernel,
    p: ArithPrelude,
    a: crate::NameId,
}

fn fixture() -> Fixture {
    let mut k = Kernel::new();
    let p = build_arith_prelude(&mut k);
    let anon = k.anon();
    // a : R.
    let a = k.name_str(anon, "a");
    let r_ty = k.const_(p.r, vec![]);
    k.add_declaration(Declaration::Axiom {
        name: a,
        uparams: vec![],
        ty: r_ty,
    })
    .unwrap();
    Fixture { k, p, a }
}

impl Fixture {
    fn a_const(&mut self) -> crate::ExprId {
        self.k.const_(self.a, vec![])
    }
    /// `le x y` as a Prop term.
    fn le(&mut self, x: crate::ExprId, y: crate::ExprId) -> crate::ExprId {
        let lec = self.k.const_(self.p.le, vec![]);
        let e = self.k.app(lec, x);
        self.k.app(e, y)
    }
    /// `lt x y` as a Prop term.
    fn lt(&mut self, x: crate::ExprId, y: crate::ExprId) -> crate::ExprId {
        let ltc = self.k.const_(self.p.lt, vec![]);
        let e = self.k.app(ltc, x);
        self.k.app(e, y)
    }
    fn zero(&mut self) -> crate::ExprId {
        self.k.const_(self.p.zero, vec![])
    }
    fn one(&mut self) -> crate::ExprId {
        self.k.const_(self.p.one, vec![])
    }
    fn false_(&mut self) -> crate::ExprId {
        self.k.const_(self.p.logic.false_, vec![])
    }
    /// Declare a hypothesis axiom `name : ty` and return its const term.
    fn hyp(&mut self, name: &str, ty: crate::ExprId) -> (crate::NameId, crate::ExprId) {
        let anon = self.k.anon();
        let nm = self.k.name_str(anon, name);
        self.k
            .add_declaration(Declaration::Axiom {
                name: nm,
                uparams: vec![],
                ty,
            })
            .unwrap();
        let c = self.k.const_(nm, vec![]);
        (nm, c)
    }
}

/// The prelude admits: every axiom type-checked through the trusted gate and is
/// present in the environment. A green build of `build_arith_prelude` already
/// *is* the well-formedness proof; this asserts the environment shape.
#[test]
fn arith_prelude_admits_all_declarations() {
    let mut k = Kernel::new();
    let p = build_arith_prelude(&mut k);

    for name in [
        p.r,
        p.add,
        p.mul,
        p.neg,
        p.zero,
        p.one,
        p.le,
        p.lt,
        p.le_refl,
        p.le_trans,
        p.lt_irrefl,
        p.lt_trans,
        p.lt_of_lt_of_le,
        p.lt_of_le_of_lt,
        p.le_of_lt,
        p.add_le_add,
        p.add_comm,
        p.add_assoc,
        p.add_zero,
        p.add_neg,
        p.mul_le_mul_of_nonneg_left,
        p.zero_lt_one,
    ] {
        assert!(
            k.environment().contains(name),
            "arith prelude should declare {}",
            k.display_name(name)
        );
        // Every declaration is an Axiom (the carrier/ops/relations/axioms).
        assert!(
            matches!(
                k.environment().get(name).unwrap(),
                Declaration::Axiom { .. }
            ),
            "{} should be an Axiom",
            k.display_name(name)
        );
    }
    // The logical prelude is embedded and present.
    assert!(k.environment().contains(p.logic.false_));
    assert!(k.environment().contains(p.logic.not));
}

/// Every axiom's *type* itself infers to a `Sort` — i.e. the whole axiom set is
/// well-formed (the trusted admission gate already enforced this, but we
/// re-check the types infer with no error).
#[test]
fn every_axiom_type_infers_to_a_sort() {
    use crate::expr::ExprNode;
    let mut k = Kernel::new();
    let p = build_arith_prelude(&mut k);
    for name in [
        p.le_refl,
        p.le_trans,
        p.lt_irrefl,
        p.lt_trans,
        p.lt_of_lt_of_le,
        p.lt_of_le_of_lt,
        p.le_of_lt,
        p.add_le_add,
        p.add_comm,
        p.add_assoc,
        p.add_zero,
        p.add_neg,
        p.mul_le_mul_of_nonneg_left,
        p.zero_lt_one,
    ] {
        let ty = k.environment().get(name).unwrap().ty();
        let inferred = k.infer(ty).unwrap();
        assert!(
            matches!(k.expr_node(inferred), ExprNode::Sort(_)),
            "axiom {} type should infer to a Sort",
            k.display_name(name)
        );
    }
}

/// **`lt_irrefl` applied**: `fun (h : lt a a) => lt_irrefl a h : False`, so the
/// closed term `fun (h : lt a a) => lt_irrefl a h` infers `lt a a → False`
/// (i.e. `Not (lt a a)` unfolded). The kernel checks the whole term.
#[test]
fn lt_irrefl_applied_checks() {
    let mut f = fixture();
    let anon = f.k.anon();
    let a = f.a_const();
    let lt_aa = f.lt(a, a);

    // proof := fun (h : lt a a) => lt_irrefl a h.
    let irrefl = f.k.const_(f.p.lt_irrefl, vec![]);
    let a2 = f.a_const();
    let proof = {
        let e = f.k.app(irrefl, a2); // lt_irrefl a : Not (lt a a)
        let h = f.k.bvar(0);
        let body = f.k.app(e, h); // (Not (lt a a)) applied to (h : lt a a) ⇒ False
        f.k.lam(anon, lt_aa, body, BinderInfo::Default)
    };
    let inferred = f.k.infer(proof).unwrap();
    // Expected: lt a a → False.
    let a3 = f.a_const();
    let lt_aa2 = f.lt(a3, a3);
    let false_ = f.false_();
    let expected = f.k.pi(anon, lt_aa2, false_, BinderInfo::Default);
    assert!(
        f.k.def_eq(inferred, expected),
        "lt_irrefl applied : lt a a → False"
    );
}

/// **transitivity**: from `h1 : lt a b`, `h2 : lt b c`,
/// `lt_trans a b c h1 h2 : lt a c` checks. We use `a`, plus abstract `b`, `c`.
#[test]
fn lt_trans_checks() {
    let mut f = fixture();
    let anon = f.k.anon();
    // b, c : R.
    let r_ty = f.k.const_(f.p.r, vec![]);
    let b = f.k.name_str(anon, "b");
    f.k.add_declaration(Declaration::Axiom {
        name: b,
        uparams: vec![],
        ty: r_ty,
    })
    .unwrap();
    let c = f.k.name_str(anon, "c");
    f.k.add_declaration(Declaration::Axiom {
        name: c,
        uparams: vec![],
        ty: r_ty,
    })
    .unwrap();

    let a = f.a_const();
    let b_c = f.k.const_(b, vec![]);
    let c_c = f.k.const_(c, vec![]);
    let lt_ab = f.lt(a, b_c);
    let lt_bc = f.lt(b_c, c_c);
    let (_, h1) = f.hyp("h1", lt_ab);
    let (_, h2) = f.hyp("h2", lt_bc);

    // lt_trans a b c h1 h2.
    let a2 = f.a_const();
    let proof = {
        let tr = f.k.const_(f.p.lt_trans, vec![]);
        let e = f.k.app(tr, a2);
        let e = f.k.app(e, b_c);
        let e = f.k.app(e, c_c);
        let e = f.k.app(e, h1);
        f.k.app(e, h2)
    };
    let inferred = f.k.infer(proof).unwrap();
    let a3 = f.a_const();
    let expected = f.lt(a3, c_c);
    assert!(f.k.def_eq(inferred, expected), "lt_trans : lt a c");
}

/// **additive monotonicity**: with abstract points and `h1 : le a b`,
/// `h2 : le c d`, `add_le_add a b c d h1 h2 : le (add a c) (add b d)` checks.
#[test]
fn add_le_add_checks() {
    let mut f = fixture();
    let anon = f.k.anon();
    let r_ty = f.k.const_(f.p.r, vec![]);
    let mk = |f: &mut Fixture, s: &str| {
        let nm = f.k.name_str(anon, s);
        f.k.add_declaration(Declaration::Axiom {
            name: nm,
            uparams: vec![],
            ty: r_ty,
        })
        .unwrap();
        f.k.const_(nm, vec![])
    };
    let a = f.a_const();
    let b = mk(&mut f, "b2");
    let c = mk(&mut f, "c2");
    let d = mk(&mut f, "d2");

    let le_ab = f.le(a, b);
    let le_cd = f.le(c, d);
    let (_, h1) = f.hyp("h1", le_ab);
    let (_, h2) = f.hyp("h2", le_cd);

    // add_le_add a b c d h1 h2.
    let a2 = f.a_const();
    let proof = {
        let ax = f.k.const_(f.p.add_le_add, vec![]);
        let e = f.k.app(ax, a2);
        let e = f.k.app(e, b);
        let e = f.k.app(e, c);
        let e = f.k.app(e, d);
        let e = f.k.app(e, h1);
        f.k.app(e, h2)
    };
    let inferred = f.k.infer(proof).unwrap();
    // Expected: le (add a c) (add b d).
    let a3 = f.a_const();
    let add = |f: &mut Fixture, x: crate::ExprId, y: crate::ExprId| {
        let addc = f.k.const_(f.p.add, vec![]);
        let e = f.k.app(addc, x);
        f.k.app(e, y)
    };
    let add_ac = add(&mut f, a3, c);
    let add_bd = add(&mut f, b, d);
    let expected = f.le(add_ac, add_bd);
    assert!(
        f.k.def_eq(inferred, expected),
        "add_le_add : le (add a c) (add b d)"
    );
}

/// **Baby-Farkas refutation**: from `h1 : le a zero` and `h2 : le one a`,
/// derive `False`. The chain is:
///   `le_trans one a zero h2 h1 : le one zero`, then
///   `lt_of_le_of_lt one zero one (above) zero_lt_one : lt one one`, then
///   `lt_irrefl one : Not (lt one one)` (i.e. `lt one one → False`), applied to
///   the previous step to yield `False`.
/// The kernel checks the whole closed term, and we confirm it infers `False`.
#[test]
fn baby_farkas_refutation_checks() {
    let mut f = fixture();
    let a = f.a_const();
    let zero = f.zero();
    let one = f.one();

    // Hypotheses: h1 : le a zero, h2 : le one a.
    let le_a0 = f.le(a, zero);
    let le_1a = {
        let one2 = f.one();
        let a2 = f.a_const();
        f.le(one2, a2)
    };
    let (_, h1) = f.hyp("h1", le_a0);
    let (_, h2) = f.hyp("h2", le_1a);

    // step1 := le_trans one a zero h2 h1 : le one zero.
    let a2 = f.a_const();
    let step1 = {
        let tr = f.k.const_(f.p.le_trans, vec![]);
        let e = f.k.app(tr, one);
        let e = f.k.app(e, a2);
        let e = f.k.app(e, zero);
        let e = f.k.app(e, h2);
        f.k.app(e, h1)
    };
    // step2 := lt_of_le_of_lt one zero one step1 zero_lt_one : lt one one.
    let one2 = f.one();
    let zero2 = f.zero();
    let one3 = f.one();
    let step2 = {
        let ax = f.k.const_(f.p.lt_of_le_of_lt, vec![]);
        let e = f.k.app(ax, one2);
        let e = f.k.app(e, zero2);
        let e = f.k.app(e, one3);
        let e = f.k.app(e, step1);
        let zlo = f.k.const_(f.p.zero_lt_one, vec![]);
        f.k.app(e, zlo)
    };
    // refute := lt_irrefl one step2 : False.
    let one4 = f.one();
    let proof = {
        let irrefl = f.k.const_(f.p.lt_irrefl, vec![]);
        let e = f.k.app(irrefl, one4); // Not (lt one one)
        f.k.app(e, step2) // applied to (lt one one) ⇒ False
    };
    let inferred = f.k.infer(proof).unwrap();
    let false_ = f.false_();
    assert!(
        f.k.def_eq(inferred, false_),
        "baby-Farkas refutation : False"
    );
}

/// Determinism: building the prelude twice yields identical `ArithPrelude`
/// (same dense ids), since interning is insertion-ordered.
#[test]
fn build_is_deterministic() {
    let mut k1 = Kernel::new();
    let p1 = build_arith_prelude(&mut k1);
    let mut k2 = Kernel::new();
    let p2 = build_arith_prelude(&mut k2);
    assert_eq!(p1, p2, "ArithPrelude ids are deterministic");
}
