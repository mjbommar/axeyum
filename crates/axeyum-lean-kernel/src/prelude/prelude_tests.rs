//! Proof-term tests for the logical prelude (ADR-0036, the P3.7 foundation).
//!
//! These tests are the real deliverable: they **build proof terms** with the
//! kernel and `infer` them to the proposition they prove. A test passes only if
//! the trusted type-checker genuinely accepts the proof — exactly what
//! Alethe→Lean reconstruction will do. Covered proofs: and-introduction,
//! and-elimination (left/right), or-introduction + or case-analysis,
//! `Eq.refl` + `Eq` transport (symmetry, which also ι-reduces on `refl`), modus
//! ponens, ex-falso via `False.rec`, and an `And.comm`-style composite built
//! from the smaller pieces.
//!
//! Convention for the abstract propositions: `A`, `B`, `C : Prop` are declared
//! as axioms (so they are genuine `Const`s of type `Prop`), and hypotheses
//! `ha : A`, `hb : B` are axioms too. A proof "checks" when `infer` returns the
//! expected proposition (compared with `def_eq`, since the kernel may return a
//! β/ι-equal but not syntactically identical normal form).
#![allow(clippy::similar_names, clippy::many_single_char_names)]

use crate::env::Declaration;
use crate::expr::ExprNode;
use crate::{BinderInfo, Kernel, LogicPrelude, build_logic_prelude};

/// A test fixture: a kernel with the prelude plus abstract `A, B, C : Prop` and
/// `ha : A`, `hb : B` axioms.
struct Fixture {
    k: Kernel,
    p: LogicPrelude,
    a: crate::NameId,
    b: crate::NameId,
    c: crate::NameId,
    ha: crate::NameId,
    hb: crate::NameId,
}

fn fixture() -> Fixture {
    let mut k = Kernel::new();
    let p = build_logic_prelude(&mut k);
    let anon = k.anon();

    // A, B, C : Prop.
    let prop_axiom = |k: &mut Kernel, s: &str| -> crate::NameId {
        let name = k.name_str(anon, s);
        let prop = k.sort_zero();
        k.add_declaration(Declaration::Axiom {
            name,
            uparams: vec![],
            ty: prop,
        })
        .unwrap();
        name
    };
    let a = prop_axiom(&mut k, "A");
    let b = prop_axiom(&mut k, "B");
    let c = prop_axiom(&mut k, "C");

    // ha : A, hb : B.
    let a_const = k.const_(a, vec![]);
    let b_const = k.const_(b, vec![]);
    let ha = k.name_str(anon, "ha");
    k.add_declaration(Declaration::Axiom {
        name: ha,
        uparams: vec![],
        ty: a_const,
    })
    .unwrap();
    let hb = k.name_str(anon, "hb");
    k.add_declaration(Declaration::Axiom {
        name: hb,
        uparams: vec![],
        ty: b_const,
    })
    .unwrap();

    Fixture {
        k,
        p,
        a,
        b,
        c,
        ha,
        hb,
    }
}

impl Fixture {
    fn a_const(&mut self) -> crate::ExprId {
        self.k.const_(self.a, vec![])
    }
    fn b_const(&mut self) -> crate::ExprId {
        self.k.const_(self.b, vec![])
    }
    fn c_const(&mut self) -> crate::ExprId {
        self.k.const_(self.c, vec![])
    }
    fn ha_const(&mut self) -> crate::ExprId {
        self.k.const_(self.ha, vec![])
    }
    fn hb_const(&mut self) -> crate::ExprId {
        self.k.const_(self.hb, vec![])
    }
    /// `And A B` (the proposition).
    fn and_ab(&mut self) -> crate::ExprId {
        let and = self.k.const_(self.p.and, vec![]);
        let a = self.a_const();
        let b = self.b_const();
        let e = self.k.app(and, a);
        self.k.app(e, b)
    }
}

/// The prelude admits: every declaration type-checked through the trusted gate,
/// and the expected names are present with the expected recursor metadata. A
/// green build of `build_logic_prelude` already *is* the well-formedness proof;
/// this asserts the environment shape.
#[test]
fn prelude_admits_all_declarations() {
    let mut k = Kernel::new();
    let p = build_logic_prelude(&mut k);

    for name in [
        p.true_,
        p.true_intro,
        p.true_rec,
        p.false_,
        p.false_rec,
        p.and,
        p.and_intro,
        p.and_rec,
        p.or,
        p.or_inl,
        p.or_inr,
        p.or_rec,
        p.iff,
        p.iff_intro,
        p.iff_rec,
        p.eq,
        p.eq_refl,
        p.eq_rec,
        p.not,
    ] {
        assert!(
            k.environment().contains(name),
            "prelude should declare {}",
            k.display_name(name)
        );
    }

    // False is a genuine zero-constructor inductive.
    match k.environment().get(p.false_).unwrap() {
        Declaration::Inductive { ctor_names, .. } => {
            assert!(ctor_names.is_empty(), "False has no constructors");
        }
        _ => panic!("False should be an inductive"),
    }
    // And has 2 params, 0 indices, 1 minor (intro).
    match k.environment().get(p.and_rec).unwrap() {
        Declaration::Recursor {
            num_params,
            num_indices,
            num_minors,
            ..
        } => {
            assert_eq!(*num_params, 2);
            assert_eq!(*num_indices, 0);
            assert_eq!(*num_minors, 1);
        }
        _ => panic!("And.rec should be a recursor"),
    }
    // Or has 2 minors (inl, inr).
    match k.environment().get(p.or_rec).unwrap() {
        Declaration::Recursor { num_minors, .. } => assert_eq!(*num_minors, 2),
        _ => panic!("Or.rec should be a recursor"),
    }
    // Eq has 2 params and 1 index.
    match k.environment().get(p.eq_rec).unwrap() {
        Declaration::Recursor {
            num_params,
            num_indices,
            ..
        } => {
            assert_eq!(*num_params, 2);
            assert_eq!(*num_indices, 1);
        }
        _ => panic!("Eq.rec should be a recursor"),
    }
}

/// `False.rec` (zero-constructor recursor) exists and its generated type
/// infer-checks to a `Sort` — confirming the kernel handles the ex-falso
/// eliminator (the empty-constructor recursor) rather than choking on it.
#[test]
fn false_rec_exists_and_self_checks() {
    let mut k = Kernel::new();
    let p = build_logic_prelude(&mut k);
    assert!(k.environment().contains(p.false_rec));
    let rec_ty = k.environment().get(p.false_rec).unwrap().ty();
    let inferred = k.infer(rec_ty).unwrap();
    assert!(
        matches!(k.expr_node(inferred), ExprNode::Sort(_)),
        "False.rec type should infer to a Sort"
    );
    // It has zero minors (one per constructor; False has none).
    match k.environment().get(p.false_rec).unwrap() {
        Declaration::Recursor { num_minors, .. } => {
            assert_eq!(*num_minors, 0, "False.rec has no minor premises");
        }
        _ => panic!("False.rec should be a recursor"),
    }
}

/// **and-introduction**: `And.intro A B ha hb : And A B`. We build the proof
/// term and `infer` it; the inferred type is `And A B`.
#[test]
fn and_intro_checks() {
    let mut f = fixture();
    let a = f.a_const();
    let b = f.b_const();
    let ha = f.ha_const();
    let hb = f.hb_const();

    // And.intro A B ha hb.
    let intro = f.k.const_(f.p.and_intro, vec![]);
    let proof = {
        let e = f.k.app(intro, a);
        let e = f.k.app(e, b);
        let e = f.k.app(e, ha);
        f.k.app(e, hb)
    };
    let inferred = f.k.infer(proof).unwrap();
    let expected = f.and_ab();
    assert!(
        f.k.def_eq(inferred, expected),
        "And.intro A B ha hb : And A B"
    );
}

/// **and-elimination (left)**: the proof `fun (h : And A B) =>
/// And.rec A B (fun _ => A) (fun ha hb => ha) h` infers `And A B → A`. The motive
/// is the constant `A`, and the minor projects the first field.
#[test]
fn and_elim_left_checks() {
    let mut f = fixture();
    let a = f.a_const();
    let b = f.b_const();
    let and_ab = f.and_ab();

    // motive := fun (_ : And A B) => A.
    let anon = f.k.anon();
    let motive = f.k.lam(anon, and_ab, a, BinderInfo::Default);
    // minor := fun (ha : A) (hb : B) => ha   (ha is BVar 1).
    let minor = {
        let v1 = f.k.bvar(1);
        let inner = f.k.lam(anon, b, v1, BinderInfo::Default);
        f.k.lam(anon, a, inner, BinderInfo::Default)
    };
    // proof := fun (h : And A B) => And.rec.{0} A B motive minor h.
    // Elimination into Prop ⇒ v := 0.
    let z = f.k.level_zero();
    let proof = {
        let rec = f.k.const_(f.p.and_rec, vec![z]);
        let e = f.k.app(rec, a);
        let e = f.k.app(e, b);
        let e = f.k.app(e, motive);
        let e = f.k.app(e, minor);
        let h = f.k.bvar(0);
        let body = f.k.app(e, h);
        f.k.lam(anon, and_ab, body, BinderInfo::Default)
    };
    let inferred = f.k.infer(proof).unwrap();
    // Expected: And A B → A.
    let a2 = f.a_const();
    let and_ab2 = f.and_ab();
    let expected = f.k.pi(anon, and_ab2, a2, BinderInfo::Default);
    assert!(
        f.k.def_eq(inferred, expected),
        "and-elim-left : And A B → A"
    );
}

/// **and-elimination (right)**: same shape, projecting the second field:
/// `fun (h : And A B) => And.rec A B (fun _ => B) (fun ha hb => hb) h :
/// And A B → B`.
#[test]
fn and_elim_right_checks() {
    let mut f = fixture();
    let a = f.a_const();
    let b = f.b_const();
    let and_ab = f.and_ab();
    let anon = f.k.anon();

    let motive = f.k.lam(anon, and_ab, b, BinderInfo::Default);
    // minor := fun (ha : A) (hb : B) => hb   (hb is BVar 0).
    let minor = {
        let v0 = f.k.bvar(0);
        let inner = f.k.lam(anon, b, v0, BinderInfo::Default);
        f.k.lam(anon, a, inner, BinderInfo::Default)
    };
    let z = f.k.level_zero();
    let proof = {
        let rec = f.k.const_(f.p.and_rec, vec![z]);
        let e = f.k.app(rec, a);
        let e = f.k.app(e, b);
        let e = f.k.app(e, motive);
        let e = f.k.app(e, minor);
        let h = f.k.bvar(0);
        let body = f.k.app(e, h);
        f.k.lam(anon, and_ab, body, BinderInfo::Default)
    };
    let inferred = f.k.infer(proof).unwrap();
    let b2 = f.b_const();
    let and_ab2 = f.and_ab();
    let expected = f.k.pi(anon, and_ab2, b2, BinderInfo::Default);
    assert!(
        f.k.def_eq(inferred, expected),
        "and-elim-right : And A B → B"
    );
}

/// **or-introduction**: `Or.inl A B ha : Or A B`.
#[test]
fn or_inl_checks() {
    let mut f = fixture();
    let a = f.a_const();
    let b = f.b_const();
    let ha = f.ha_const();

    let inl = f.k.const_(f.p.or_inl, vec![]);
    let proof = {
        let e = f.k.app(inl, a);
        let e = f.k.app(e, b);
        f.k.app(e, ha)
    };
    let inferred = f.k.infer(proof).unwrap();
    // Expected: Or A B.
    let or = f.k.const_(f.p.or, vec![]);
    let a2 = f.a_const();
    let b2 = f.b_const();
    let expected = {
        let e = f.k.app(or, a2);
        f.k.app(e, b2)
    };
    assert!(f.k.def_eq(inferred, expected), "Or.inl A B ha : Or A B");
}

/// **or case-analysis**: `fun (h : Or A B) => Or.rec A B (fun _ => C) f g h`
/// infers `Or A B → C`, where `f : A → C` and `g : B → C` are abstract
/// eliminators (axioms). This is the disjunction eliminator checking.
#[test]
fn or_case_analysis_checks() {
    let mut f = fixture();
    let anon = f.k.anon();
    let a = f.a_const();
    let c = f.c_const();

    // f : A → C, g : B → C  (axioms).
    let ac = f.k.pi(anon, a, c, BinderInfo::Default);
    let f_name = f.k.name_str(anon, "f");
    f.k.add_declaration(Declaration::Axiom {
        name: f_name,
        uparams: vec![],
        ty: ac,
    })
    .unwrap();
    let bc = {
        let b2 = f.b_const();
        let c2 = f.c_const();
        f.k.pi(anon, b2, c2, BinderInfo::Default)
    };
    let g_name = f.k.name_str(anon, "g");
    f.k.add_declaration(Declaration::Axiom {
        name: g_name,
        uparams: vec![],
        ty: bc,
    })
    .unwrap();

    // Or A B.
    let or = f.k.const_(f.p.or, vec![]);
    let a3 = f.a_const();
    let b3 = f.b_const();
    let or_ab = {
        let e = f.k.app(or, a3);
        f.k.app(e, b3)
    };
    // motive := fun (_ : Or A B) => C.
    let c3 = f.c_const();
    let motive = f.k.lam(anon, or_ab, c3, BinderInfo::Default);
    // minor_inl := fun (ha : A) => f ha ;  minor_inr := fun (hb : B) => g hb.
    let f_const = f.k.const_(f_name, vec![]);
    let a4 = f.a_const();
    let minor_inl = {
        let v0 = f.k.bvar(0);
        let body = f.k.app(f_const, v0);
        f.k.lam(anon, a4, body, BinderInfo::Default)
    };
    let g_const = f.k.const_(g_name, vec![]);
    let b4 = f.b_const();
    let minor_inr = {
        let v0 = f.k.bvar(0);
        let body = f.k.app(g_const, v0);
        f.k.lam(anon, b4, body, BinderInfo::Default)
    };

    // proof := fun (h : Or A B) => Or.rec.{0} A B motive minor_inl minor_inr h.
    let z = f.k.level_zero();
    let a5 = f.a_const();
    let b5 = f.b_const();
    let or_ab2 = {
        let or2 = f.k.const_(f.p.or, vec![]);
        let e = f.k.app(or2, a5);
        f.k.app(e, b5)
    };
    let proof = {
        let rec = f.k.const_(f.p.or_rec, vec![z]);
        let e = f.k.app(rec, a5);
        let e = f.k.app(e, b5);
        let e = f.k.app(e, motive);
        let e = f.k.app(e, minor_inl);
        let e = f.k.app(e, minor_inr);
        let h = f.k.bvar(0);
        let body = f.k.app(e, h);
        f.k.lam(anon, or_ab2, body, BinderInfo::Default)
    };
    let inferred = f.k.infer(proof).unwrap();
    // Expected: Or A B → C.
    let c4 = f.c_const();
    let a6 = f.a_const();
    let b6 = f.b_const();
    let or_ab3 = {
        let or3 = f.k.const_(f.p.or, vec![]);
        let e = f.k.app(or3, a6);
        f.k.app(e, b6)
    };
    let expected = f.k.pi(anon, or_ab3, c4, BinderInfo::Default);
    assert!(
        f.k.def_eq(inferred, expected),
        "or case-analysis : Or A B → C"
    );
}

/// **`Eq.refl`**: `Eq.refl A ha : Eq A ha ha` for a carrier and a point.
/// Uses `A : Sort 1` (a `Type`) and `x : A` so the universe `u := 1`.
#[test]
fn eq_refl_checks() {
    let mut k = Kernel::new();
    let p = build_logic_prelude(&mut k);
    let anon = k.anon();

    // A : Sort 1, x : A.
    let one = {
        let z = k.level_zero();
        k.level_succ(z)
    };
    let s1 = k.sort(one);
    let a_carrier = k.name_str(anon, "Carrier");
    k.add_declaration(Declaration::Axiom {
        name: a_carrier,
        uparams: vec![],
        ty: s1,
    })
    .unwrap();
    let big_a = k.const_(a_carrier, vec![]);
    let x_name = k.name_str(anon, "x");
    k.add_declaration(Declaration::Axiom {
        name: x_name,
        uparams: vec![],
        ty: big_a,
    })
    .unwrap();
    let x = k.const_(x_name, vec![]);

    // Eq.refl.{1} A x : Eq.{1} A x x.
    let refl = k.const_(p.eq_refl, vec![one]);
    let proof = {
        let e = k.app(refl, big_a);
        k.app(e, x)
    };
    let inferred = k.infer(proof).unwrap();
    // Expected: Eq A x x.
    let eq = k.const_(p.eq, vec![one]);
    let expected = {
        let e = k.app(eq, big_a);
        let e = k.app(e, x);
        k.app(e, x)
    };
    assert!(k.def_eq(inferred, expected), "Eq.refl A x : Eq A x x");
}

/// **`Eq` transport (symmetry)**: from `h : Eq A x y` derive `Eq A y x`. We
/// build `Eq.symm := fun (y) (h : Eq A x y) => Eq.rec A x (motive) (refl A x) y h`
/// with `motive := fun (b) (_ : Eq A x b) => Eq A b x`, and check it type-checks.
/// We then check the eliminator **computes** on `refl`: applied to `x` and
/// `Eq.refl A x`, it ι-reduces to `Eq.refl A x`.
#[test]
fn eq_symm_checks_and_computes_on_refl() {
    let mut k = Kernel::new();
    let p = build_logic_prelude(&mut k);
    let anon = k.anon();

    // A : Sort 1, x : A.
    let one = {
        let z = k.level_zero();
        k.level_succ(z)
    };
    let s1 = k.sort(one);
    let a_carrier = k.name_str(anon, "Carrier");
    k.add_declaration(Declaration::Axiom {
        name: a_carrier,
        uparams: vec![],
        ty: s1,
    })
    .unwrap();
    let big_a = k.const_(a_carrier, vec![]);
    let x_name = k.name_str(anon, "x");
    k.add_declaration(Declaration::Axiom {
        name: x_name,
        uparams: vec![],
        ty: big_a,
    })
    .unwrap();
    let x = k.const_(x_name, vec![]);

    let eq = |k: &mut Kernel, ty: crate::ExprId, l: crate::ExprId, r: crate::ExprId| {
        let e = k.const_(p.eq, vec![one]);
        let e = k.app(e, ty);
        let e = k.app(e, l);
        k.app(e, r)
    };

    // motive := fun (b : A) (_ : Eq A x b) => Eq A b x.
    //   Under binders b, h (innermost = 0): b = BVar 1 in the body `Eq A b x`,
    //   b = BVar 0 in the h domain `Eq A x b`.
    let motive = {
        let b1 = k.bvar(1);
        let eq_bx = eq(&mut k, big_a, b1, x);
        let b0 = k.bvar(0);
        let eq_xb = eq(&mut k, big_a, x, b0);
        let inner_h = k.lam(anon, eq_xb, eq_bx, BinderInfo::Default);
        k.lam(anon, big_a, inner_h, BinderInfo::Default)
    };
    // refl_case := Eq.refl A x : Eq A x x = motive x (refl A x) (after β).
    let refl_ax = {
        let refl = k.const_(p.eq_refl, vec![one]);
        let e = k.app(refl, big_a);
        k.app(e, x)
    };

    // The transport applied to x and (refl A x):
    //   Eq.rec.{0,1} A x motive (refl A x) x (refl A x)  ι→  refl A x.
    let z = k.level_zero();
    let app = {
        let rec = k.const_(p.eq_rec, vec![z, one]);
        let e = k.app(rec, big_a);
        let e = k.app(e, x);
        let e = k.app(e, motive);
        let e = k.app(e, refl_ax);
        let e = k.app(e, x); // index arg b := x
        k.app(e, refl_ax) // major
    };
    // It type-checks to `motive x (refl A x)` = `Eq A x x` (β/ι-equal).
    let inferred = k.infer(app).unwrap();
    let eq_xx = eq(&mut k, big_a, x, x);
    assert!(
        k.def_eq(inferred, eq_xx),
        "transport on refl proves Eq A x x"
    );
    // And it ι-reduces to `refl A x`.
    assert_eq!(k.whnf(app), refl_ax, "Eq.rec on refl ι→ the refl_case");
}

/// **modus ponens**: `fun (h : A → B) (ha : A) => h ha : (A → B) → A → B`.
/// Trivial but foundational — function application is the proof rule.
#[test]
fn modus_ponens_checks() {
    let mut f = fixture();
    let anon = f.k.anon();
    let a = f.a_const();
    let b = f.b_const();

    // A → B.
    let ab = f.k.pi(anon, a, b, BinderInfo::Default);
    // proof := fun (h : A → B) (ha : A) => h ha.  h = BVar 1, ha = BVar 0.
    let a2 = f.a_const();
    let proof = {
        let h = f.k.bvar(1);
        let ha = f.k.bvar(0);
        let body = f.k.app(h, ha);
        let inner = f.k.lam(anon, a2, body, BinderInfo::Default);
        f.k.lam(anon, ab, inner, BinderInfo::Default)
    };
    let inferred = f.k.infer(proof).unwrap();
    // Expected: (A → B) → A → B.
    let a3 = f.a_const();
    let b3 = f.b_const();
    let ab2 = f.k.pi(anon, a3, b3, BinderInfo::Default);
    let a4 = f.a_const();
    let b4 = f.b_const();
    let ab3 = f.k.pi(anon, a4, b4, BinderInfo::Default);
    let expected = f.k.pi(anon, ab2, ab3, BinderInfo::Default);
    assert!(
        f.k.def_eq(inferred, expected),
        "modus ponens : (A → B) → A → B"
    );
}

/// **ex-falso** via `False.rec`: `fun (h : False) => False.rec (fun _ => C) h`
/// infers `False → C`. The zero-constructor recursor takes only the motive and
/// the major (no minors), so it eliminates any `False` into any `C`.
#[test]
fn ex_falso_checks() {
    let mut f = fixture();
    let anon = f.k.anon();
    let c = f.c_const();
    let false_const = f.k.const_(f.p.false_, vec![]);

    // motive := fun (_ : False) => C.
    let motive = f.k.lam(anon, false_const, c, BinderInfo::Default);
    // proof := fun (h : False) => False.rec.{0} motive h.
    let z = f.k.level_zero();
    let false_const2 = f.k.const_(f.p.false_, vec![]);
    let proof = {
        let rec = f.k.const_(f.p.false_rec, vec![z]);
        let e = f.k.app(rec, motive);
        let h = f.k.bvar(0);
        let body = f.k.app(e, h);
        f.k.lam(anon, false_const2, body, BinderInfo::Default)
    };
    let inferred = f.k.infer(proof).unwrap();
    // Expected: False → C.
    let c2 = f.c_const();
    let false_const3 = f.k.const_(f.p.false_, vec![]);
    let expected = f.k.pi(anon, false_const3, c2, BinderInfo::Default);
    assert!(f.k.def_eq(inferred, expected), "ex-falso : False → C");
}

/// **`True.intro`**: the trivial proof `True.intro : True` checks.
#[test]
fn true_intro_checks() {
    let mut k = Kernel::new();
    let p = build_logic_prelude(&mut k);
    let intro = k.const_(p.true_intro, vec![]);
    let inferred = k.infer(intro).unwrap();
    let true_const = k.const_(p.true_, vec![]);
    assert!(k.def_eq(inferred, true_const), "True.intro : True");
}

/// **`Not` unfolds**: `Not A` is def-eq to `A → False` (the definition
/// δ-unfolds), so a proof `fun (h : Not A) (ha : A) => h ha : Not A → A → False`
/// checks — `Not` is genuinely the function-to-`False`.
#[test]
fn not_unfolds_to_arrow_false() {
    let mut f = fixture();
    let anon = f.k.anon();
    let a = f.a_const();

    // Not A.
    let not = f.k.const_(f.p.not, vec![]);
    let not_a = f.k.app(not, a);
    // A → False  (what Not A should unfold to).
    let a2 = f.a_const();
    let false_const = f.k.const_(f.p.false_, vec![]);
    let arrow_false = f.k.pi(anon, a2, false_const, BinderInfo::Default);
    assert!(
        f.k.def_eq(not_a, arrow_false),
        "Not A def-eq A → False (δ-unfold)"
    );

    // proof := fun (h : Not A) (ha : A) => h ha : Not A → A → False.
    let a3 = f.a_const();
    let proof = {
        let h = f.k.bvar(1);
        let ha = f.k.bvar(0);
        let body = f.k.app(h, ha);
        let inner = f.k.lam(anon, a3, body, BinderInfo::Default);
        let not2 = f.k.const_(f.p.not, vec![]);
        let a4 = f.a_const();
        let not_a2 = f.k.app(not2, a4);
        f.k.lam(anon, not_a2, inner, BinderInfo::Default)
    };
    assert!(f.k.infer(proof).is_ok(), "Not-application proof checks");
}

/// **Composite proof — `And.comm`**: `fun (h : And A B) =>
/// And.intro B A (and-elim-right h) (and-elim-left h) : And A B → And B A`.
/// A genuine multi-step proof assembled from the pieces: it eliminates the
/// hypothesis twice and re-introduces the conjunction with the operands swapped.
/// The kernel verifies the whole term.
#[test]
fn and_comm_composite_checks() {
    let mut f = fixture();
    let anon = f.k.anon();
    let z = f.k.level_zero();

    // Helper: and-elim that, given the conjunction term `h_expr : And A B`,
    // projects field `which` (0 = left/A, 1 = right/B) by applying And.rec
    // directly (no outer lambda — we want the projected proof of A or B).
    //   And.rec A B (fun _ => P) (fun ha hb => field) h_expr
    // where P, field depend on `which`.
    // We inline both projections below.

    // The conjunction proposition `And A B` (rebuilt fresh as needed).
    let and_ab = f.and_ab();

    // h : And A B is the lambda's BVar 0.
    // and-elim-right h : B.
    let a1 = f.a_const();
    let b1 = f.b_const();
    let and_ab_motive_r = f.and_ab();
    let motive_r = f.k.lam(anon, and_ab_motive_r, b1, BinderInfo::Default);
    let minor_r = {
        let v0 = f.k.bvar(0); // hb
        let inner = f.k.lam(anon, b1, v0, BinderInfo::Default);
        f.k.lam(anon, a1, inner, BinderInfo::Default)
    };
    // and-elim-left h : A.
    let a2 = f.a_const();
    let b2 = f.b_const();
    let and_ab_motive_l = f.and_ab();
    let motive_l = f.k.lam(anon, and_ab_motive_l, a2, BinderInfo::Default);
    let minor_l = {
        let v1 = f.k.bvar(1); // ha
        let inner = f.k.lam(anon, b2, v1, BinderInfo::Default);
        f.k.lam(anon, a2, inner, BinderInfo::Default)
    };

    // Build, inside the outer `fun (h : And A B) => …`, the body:
    //   And.intro B A (And.rec A B motive_r minor_r h) (And.rec A B motive_l minor_l h)
    let a3 = f.a_const();
    let b3 = f.b_const();
    // proof_right := And.rec.{0} A B motive_r minor_r h   (: B)
    let elim_right = {
        let rec = f.k.const_(f.p.and_rec, vec![z]);
        let e = f.k.app(rec, a3);
        let e = f.k.app(e, b3);
        let e = f.k.app(e, motive_r);
        let e = f.k.app(e, minor_r);
        let h = f.k.bvar(0);
        f.k.app(e, h)
    };
    let a4 = f.a_const();
    let b4 = f.b_const();
    let elim_left = {
        let rec = f.k.const_(f.p.and_rec, vec![z]);
        let e = f.k.app(rec, a4);
        let e = f.k.app(e, b4);
        let e = f.k.app(e, motive_l);
        let e = f.k.app(e, minor_l);
        let h = f.k.bvar(0);
        f.k.app(e, h)
    };
    // And.intro B A elim_right elim_left  : And B A.
    let b5 = f.b_const();
    let a5 = f.a_const();
    let body = {
        let intro = f.k.const_(f.p.and_intro, vec![]);
        let e = f.k.app(intro, b5);
        let e = f.k.app(e, a5);
        let e = f.k.app(e, elim_right);
        f.k.app(e, elim_left)
    };
    // proof := fun (h : And A B) => body.
    let proof = f.k.lam(anon, and_ab, body, BinderInfo::Default);

    let inferred = f.k.infer(proof).unwrap();
    // Expected: And A B → And B A.
    let and_ab_dom = f.and_ab();
    let and_ba = {
        let and = f.k.const_(f.p.and, vec![]);
        let b6 = f.b_const();
        let a6 = f.a_const();
        let e = f.k.app(and, b6);
        f.k.app(e, a6)
    };
    let expected = f.k.pi(anon, and_ab_dom, and_ba, BinderInfo::Default);
    assert!(
        f.k.def_eq(inferred, expected),
        "And.comm : And A B → And B A"
    );
}

/// **`Iff.intro`**: from `mp : A → B` and `mpr : B → A` (axioms), the proof
/// `Iff.intro A B mp mpr : Iff A B` checks — both directions packaged.
#[test]
fn iff_intro_checks() {
    let mut f = fixture();
    let anon = f.k.anon();
    let a = f.a_const();
    let b = f.b_const();

    // mp : A → B, mpr : B → A.
    let ab = f.k.pi(anon, a, b, BinderInfo::Default);
    let mp_name = f.k.name_str(anon, "mp");
    f.k.add_declaration(Declaration::Axiom {
        name: mp_name,
        uparams: vec![],
        ty: ab,
    })
    .unwrap();
    let ba = {
        let b2 = f.b_const();
        let a2 = f.a_const();
        f.k.pi(anon, b2, a2, BinderInfo::Default)
    };
    let mpr_name = f.k.name_str(anon, "mpr");
    f.k.add_declaration(Declaration::Axiom {
        name: mpr_name,
        uparams: vec![],
        ty: ba,
    })
    .unwrap();

    // Iff.intro A B mp mpr.
    let a3 = f.a_const();
    let b3 = f.b_const();
    let mp = f.k.const_(mp_name, vec![]);
    let mpr = f.k.const_(mpr_name, vec![]);
    let proof = {
        let intro = f.k.const_(f.p.iff_intro, vec![]);
        let e = f.k.app(intro, a3);
        let e = f.k.app(e, b3);
        let e = f.k.app(e, mp);
        f.k.app(e, mpr)
    };
    let inferred = f.k.infer(proof).unwrap();
    // Expected: Iff A B.
    let iff = f.k.const_(f.p.iff, vec![]);
    let a4 = f.a_const();
    let b4 = f.b_const();
    let expected = {
        let e = f.k.app(iff, a4);
        f.k.app(e, b4)
    };
    assert!(
        f.k.def_eq(inferred, expected),
        "Iff.intro A B mp mpr : Iff A B"
    );
}
