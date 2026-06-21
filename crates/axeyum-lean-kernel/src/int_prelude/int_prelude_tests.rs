//! Proof-term tests for the integer prelude (ADR-0042, the integer-arithmetic /
//! Diophantine reconstruction foundation).
//!
//! These tests build proof terms over the axiomatized discretely-ordered
//! commutative ring and `infer`-check them. A test passes only if the trusted
//! type-checker genuinely accepts the proof. The headline test exercises the
//! integer-specific **discreteness** axiom: given `0 < x` and `x < 1`,
//! `no_int_between x (And.intro _ _ h0 h1) : False`. We also assert every axiom
//! admits, every axiom type infers to a `Sort`, and the build is deterministic.
#![allow(clippy::similar_names, clippy::many_single_char_names)]

use crate::env::Declaration;
use crate::{IntPrelude, Kernel, build_int_prelude};

/// A fixture: a kernel with the integer prelude plus an abstract point `x : Z`;
/// hypotheses are added per-test.
struct Fixture {
    k: Kernel,
    p: IntPrelude,
    x: crate::NameId,
}

fn fixture() -> Fixture {
    let mut k = Kernel::new();
    let p = build_int_prelude(&mut k);
    let anon = k.anon();
    // x : Z.
    let x = k.name_str(anon, "x");
    let z_ty = k.const_(p.z, vec![]);
    k.add_declaration(Declaration::Axiom {
        name: x,
        uparams: vec![],
        ty: z_ty,
    })
    .unwrap();
    Fixture { k, p, x }
}

impl Fixture {
    fn x_const(&mut self) -> crate::ExprId {
        self.k.const_(self.x, vec![])
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
    /// `And p q` as a Prop term (two explicit Prop arguments).
    fn and(&mut self, p: crate::ExprId, q: crate::ExprId) -> crate::ExprId {
        let andc = self.k.const_(self.p.logic.and, vec![]);
        let e = self.k.app(andc, p);
        self.k.app(e, q)
    }
    /// `Not r` as a Prop term.
    fn not(&mut self, r: crate::ExprId) -> crate::ExprId {
        let notc = self.k.const_(self.p.logic.not, vec![]);
        self.k.app(notc, r)
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
/// present in the environment as an `Axiom`. A green build of `build_int_prelude`
/// already *is* the well-formedness proof; this asserts the environment shape.
#[test]
fn int_prelude_admits_all_declarations() {
    let mut k = Kernel::new();
    let p = build_int_prelude(&mut k);

    for name in [
        p.z,
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
        p.add_lt_add_of_le_of_lt,
        p.mul_le_mul_of_nonneg_left,
        p.zero_lt_one,
        p.mul_comm,
        p.mul_assoc,
        p.mul_one,
        p.mul_zero,
        p.left_distrib,
        p.mul_nonneg,
        p.no_int_between,
        p.le_total,
        p.lt_of_le_of_ne,
    ] {
        assert!(
            k.environment().contains(name),
            "int prelude should declare {}",
            k.display_name(name)
        );
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
    assert!(k.environment().contains(p.logic.and));
    assert!(k.environment().contains(p.logic.and_intro));
}

/// Every axiom's *type* itself infers to a `Sort` — i.e. the whole axiom set is
/// well-formed (the trusted admission gate already enforced this, but we
/// re-check the types infer with no error).
#[test]
fn every_axiom_type_infers_to_a_sort() {
    use crate::expr::ExprNode;
    let mut k = Kernel::new();
    let p = build_int_prelude(&mut k);
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
        p.add_lt_add_of_le_of_lt,
        p.mul_le_mul_of_nonneg_left,
        p.zero_lt_one,
        p.mul_comm,
        p.mul_assoc,
        p.mul_one,
        p.mul_zero,
        p.left_distrib,
        p.mul_nonneg,
        p.no_int_between,
        p.le_total,
        p.lt_of_le_of_ne,
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

/// **`no_int_between` applied**: `no_int_between x : Not (And (lt zero x)
/// (lt x one))`. We build a fresh `x : Z` const, apply `no_int_between` to it,
/// `infer`, and `def_eq`-check the inferred type against the expected
/// `Not (And (lt zero x) (lt x one))`. (Mirrors `arith_prelude`'s
/// `lt_irrefl_applied_checks`.)
#[test]
fn no_int_between_applied_checks() {
    let mut f = fixture();
    let x = f.x_const();

    // proof := no_int_between x.
    let nib = f.k.const_(f.p.no_int_between, vec![]);
    let proof = f.k.app(nib, x);
    let inferred = f.k.infer(proof).unwrap();

    // Expected: Not (And (lt zero x) (lt x one)).
    let zero = f.zero();
    let x2 = f.x_const();
    let lt_0x = f.lt(zero, x2);
    let x3 = f.x_const();
    let one = f.one();
    let lt_x1 = f.lt(x3, one);
    let conj = f.and(lt_0x, lt_x1);
    let expected = f.not(conj);
    assert!(
        f.k.def_eq(inferred, expected),
        "no_int_between x : Not (And (lt zero x) (lt x one))"
    );
}

/// **discreteness refutation** — the integer-specific content: given
/// `h0 : lt zero x` and `h1 : lt x one`, the term
/// `no_int_between x (And.intro (lt zero x) (lt x one) h0 h1)` infers to `False`.
/// The conjunction is built with the logic prelude's `And.intro`, which takes the
/// two Prop arguments explicitly (`And.intro P Q hp hq : And P Q`), and
/// `no_int_between x : Not (And …)` unfolds to `And … → False`, so the whole term
/// is `False`.
#[test]
fn discreteness_refutes_zero_lt_x_lt_one() {
    let mut f = fixture();

    // Hypotheses h0 : lt zero x, h1 : lt x one.
    let zero = f.zero();
    let x = f.x_const();
    let lt_0x = f.lt(zero, x);
    let x2 = f.x_const();
    let one = f.one();
    let lt_x1 = f.lt(x2, one);
    let (_, h0) = f.hyp("h0", lt_0x);
    let (_, h1) = f.hyp("h1", lt_x1);

    // and_proof := And.intro (lt zero x) (lt x one) h0 h1 : And (lt zero x)(lt x one).
    let zero2 = f.zero();
    let x3 = f.x_const();
    let p_prop = f.lt(zero2, x3); // lt zero x
    let x4 = f.x_const();
    let one2 = f.one();
    let q_prop = f.lt(x4, one2); // lt x one
    let and_proof = {
        let intro = f.k.const_(f.p.logic.and_intro, vec![]);
        let e = f.k.app(intro, p_prop);
        let e = f.k.app(e, q_prop);
        let e = f.k.app(e, h0);
        f.k.app(e, h1)
    };

    // proof := no_int_between x and_proof : False.
    let x5 = f.x_const();
    let proof = {
        let nib = f.k.const_(f.p.no_int_between, vec![]);
        let e = f.k.app(nib, x5); // no_int_between x : Not (And …)
        f.k.app(e, and_proof) // applied to (And …) ⇒ False
    };
    let inferred = f.k.infer(proof).unwrap();
    let false_ = f.false_();
    assert!(
        f.k.def_eq(inferred, false_),
        "no_int_between x (And.intro … h0 h1) : False"
    );
}

/// Determinism: building the prelude twice yields identical `IntPrelude` (same
/// dense ids), since interning is insertion-ordered.
#[test]
fn build_is_deterministic() {
    let mut k1 = Kernel::new();
    let p1 = build_int_prelude(&mut k1);
    let mut k2 = Kernel::new();
    let p2 = build_int_prelude(&mut k2);
    assert_eq!(p1, p2, "IntPrelude ids are deterministic");
}
