//! Tests for the environment / declaration layer (ADR-0036, slice 3):
//! the trusted `add_declaration` admission gate, universe instantiation,
//! `Const` inference, δ-unfolding in WHNF, and the lazy-delta def_eq step.
//!
//! These build real `Kernel`+`Environment` states and check **known** typing
//! judgments (the polymorphic identity, axioms, definitions, opaque
//! constants), plus the rejection cases the trusted kernel must catch.
//!
//! Single-character mathematical binder names (`u`, `α`, `x`) match the
//! type-theory literature, so the relevant naming lints are relaxed.
#![allow(
    clippy::many_single_char_names,
    clippy::similar_names,
    clippy::doc_markdown
)]

use crate::env::{Declaration, ReducibilityHint};
use crate::expr::ExprNode;
use crate::tc::KernelError;
use crate::{BinderInfo, Kernel, Lit};

/// Build the polymorphic identity declaration
/// `id : Π(α:Sort u), α → α := λ(α:Sort u)(x:α), x`, returning its name and
/// uparam `u`.
fn declare_id(k: &mut Kernel) -> (crate::NameId, crate::NameId) {
    let anon = k.anon();
    let id_name = k.name_str(anon, "id");
    let u_name = k.name_str(anon, "u");
    let u = k.level_param(u_name);
    let sort_u = k.sort(u);

    // type: Π (α : Sort u), Π (_ : #0), #1
    let dom_inner = k.bvar(0); // α as the inner domain
    let body_inner = k.bvar(1); // α (the outer binder) as the codomain
    let pi_inner = k.pi(anon, dom_inner, body_inner, BinderInfo::Default);
    let ty = k.pi(anon, sort_u, pi_inner, BinderInfo::Default);

    // value: λ (α : Sort u), λ (x : #0), #0
    let x_dom = k.bvar(0); // x : α
    let x_body = k.bvar(0); // returns x
    let lam_inner = k.lam(anon, x_dom, x_body, BinderInfo::Default);
    let value = k.lam(anon, sort_u, lam_inner, BinderInfo::Default);

    let decl = Declaration::Definition {
        name: id_name,
        uparams: vec![u_name],
        ty,
        value,
        hint: ReducibilityHint::Regular(1),
    };
    k.add_declaration(decl).expect("id should type-check");
    (id_name, u_name)
}

/// The polymorphic identity admits, and `infer(Const id [v])` yields the
/// `Π`-type with `u := v` instantiated.
#[test]
fn id_admits_and_const_infers_instantiated_type() {
    let mut k = Kernel::new();
    let (id_name, _u) = declare_id(&mut k);
    assert!(k.environment().contains(id_name));

    // infer Const id [1 level]: should be Π (α : Sort 1), α → α.
    let anon = k.anon();
    let z = k.level_zero();
    let one = k.level_succ(z);
    let c = k.const_(id_name, vec![one]);
    let inferred = k.infer(c).unwrap();

    let s1 = k.sort(one);
    let dom_inner = k.bvar(0);
    let body_inner = k.bvar(1);
    let pi_inner = k.pi(anon, dom_inner, body_inner, BinderInfo::Default);
    let expected = k.pi(anon, s1, pi_inner, BinderInfo::Default);
    assert_eq!(inferred, expected);
}

/// `(id (Sort 0) (Sort 0))`-style application type-checks and the head
/// δ-unfolds + β-reduces to the argument.
#[test]
fn id_application_checks_and_reduces() {
    let mut k = Kernel::new();
    let (id_name, _u) = declare_id(&mut k);

    // id at level 1, so the type argument Sort 0 (: Sort 1) fits α : Sort 1.
    let z = k.level_zero();
    let one = k.level_succ(z);
    let s0 = k.sort_zero();
    // id.{1} (Sort 0) : Sort 0 → Sort 0
    let id_c = k.const_(id_name, vec![one]);
    let id_at = k.app(id_c, s0);
    // Apply to an inhabitant of Sort 0: use Sort 0's own... no, need x : Sort 0.
    // Sort 0 : Sort 1, so apply id at level 2 to (Sort 1 : Sort 2)? Keep it
    // simple: check id_at type-checks (Sort 0 → Sort 0) and reduces id_at to
    // the identity lambda on Sort 0.
    let ty = k.infer(id_at).unwrap();
    // ty should be Sort 0 → Sort 0 = Π (_ : Sort 0), Sort 0.
    assert!(matches!(k.expr_node(ty), ExprNode::Pi(..)));

    // Now apply to a concrete inhabitant. Sort 0 : Sort 1, so use id.{2}.
    let two = k.level_succ(one);
    let s1 = k.sort(one);
    let id_c2 = k.const_(id_name, vec![two]);
    let id_at2 = k.app(id_c2, s1); // id.{2} (Sort 1) : Sort 1 → Sort 1
    let full = k.app(id_at2, s0); // (id.{2} (Sort 1)) (Sort 0), Sort 0 : Sort 1
    let full_ty = k.infer(full).unwrap();
    assert_eq!(full_ty, s1); // result type α = Sort 1
    let reduced = k.whnf(full);
    assert_eq!(reduced, s0); // δ + β reduces to the argument
}

/// A mismatched universe-argument count on a `Const` errors.
#[test]
fn const_universe_arity_mismatch() {
    let mut k = Kernel::new();
    let (id_name, _u) = declare_id(&mut k);
    // id expects 1 uparam; give it 0.
    let c0 = k.const_(id_name, vec![]);
    let err = k.infer(c0).unwrap_err();
    assert!(
        matches!(
            err,
            KernelError::UniverseArityMismatch {
                expected: 1,
                got: 0,
                ..
            }
        ),
        "got {err:?}"
    );
    // Give it 2.
    let z = k.level_zero();
    let one = k.level_succ(z);
    let c2 = k.const_(id_name, vec![z, one]);
    let err2 = k.infer(c2).unwrap_err();
    assert!(
        matches!(
            err2,
            KernelError::UniverseArityMismatch {
                expected: 1,
                got: 2,
                ..
            }
        ),
        "got {err2:?}"
    );
}

/// Polymorphic instantiation at two distinct level args yields the two
/// correspondingly-instantiated types.
#[test]
fn polymorphic_instantiation_two_levels() {
    let mut k = Kernel::new();
    let (id_name, _u) = declare_id(&mut k);
    let anon = k.anon();
    let z = k.level_zero();
    let one = k.level_succ(z);
    let two = k.level_succ(one);

    let c1 = k.const_(id_name, vec![one]);
    let t1 = k.infer(c1).unwrap();
    let c2 = k.const_(id_name, vec![two]);
    let t2 = k.infer(c2).unwrap();
    assert_ne!(
        t1, t2,
        "different level args give different instantiated types"
    );

    let s1 = k.sort(one);
    let s2 = k.sort(two);
    // t1 head domain is Sort 1, t2 head domain is Sort 2.
    let dom_inner = k.bvar(0);
    let body_inner = k.bvar(1);
    let pi_inner = k.pi(anon, dom_inner, body_inner, BinderInfo::Default);
    let exp1 = k.pi(anon, s1, pi_inner, BinderInfo::Default);
    let exp2 = k.pi(anon, s2, pi_inner, BinderInfo::Default);
    assert_eq!(t1, exp1);
    assert_eq!(t2, exp2);
}

/// An axiom is admitted; `Const ax []` infers its declared type; and the axiom
/// does NOT δ-unfold in whnf.
#[test]
fn axiom_infers_and_does_not_unfold() {
    let mut k = Kernel::new();
    let anon = k.anon();
    let ax_name = k.name_str(anon, "ax");
    let s0 = k.sort_zero(); // SomeType := Sort 0 (a type)
    let decl = Declaration::Axiom {
        name: ax_name,
        uparams: vec![],
        ty: s0,
    };
    k.add_declaration(decl).expect("axiom should admit");

    let c = k.const_(ax_name, vec![]);
    let ty = k.infer(c).unwrap();
    assert_eq!(ty, s0);
    // The axiom Const is already whnf — it never unfolds.
    let reduced = k.whnf(c);
    assert_eq!(reduced, c);
}

/// A definition δ-unfolds in whnf to its value, and is def_eq to its unfolding.
#[test]
fn definition_unfolds_and_def_eq() {
    let mut k = Kernel::new();
    let anon = k.anon();
    // two : Sort 1 := Sort 0   (a trivial monomorphic def; Sort 0 : Sort 1)
    let two_name = k.name_str(anon, "two");
    let z = k.level_zero();
    let one = k.level_succ(z);
    let s1 = k.sort(one);
    let s0 = k.sort_zero();
    let decl = Declaration::Definition {
        name: two_name,
        uparams: vec![],
        ty: s1,
        value: s0,
        hint: ReducibilityHint::Regular(0),
    };
    k.add_declaration(decl).expect("def should admit");

    let c = k.const_(two_name, vec![]);
    // whnf δ-unfolds the const to its value Sort 0.
    let reduced = k.whnf(c);
    assert_eq!(reduced, s0);
    // def_eq between the const and its unfolding holds.
    assert!(k.def_eq(c, s0));
    assert!(k.def_eq(s0, c));
}

/// Two distinct definitions are def_eq iff their values are def_eq.
#[test]
fn distinct_defs_def_eq_iff_values_eq() {
    let mut k = Kernel::new();
    let anon = k.anon();
    let z = k.level_zero();
    let one = k.level_succ(z);
    let s1 = k.sort(one);
    let s0 = k.sort_zero();

    // a : Sort 1 := Sort 0 ;  b : Sort 1 := Sort 0  (same value)
    let a_name = k.name_str(anon, "a");
    let b_name = k.name_str(anon, "b");
    k.add_declaration(Declaration::Definition {
        name: a_name,
        uparams: vec![],
        ty: s1,
        value: s0,
        hint: ReducibilityHint::Regular(0),
    })
    .unwrap();
    k.add_declaration(Declaration::Definition {
        name: b_name,
        uparams: vec![],
        ty: s1,
        value: s0,
        hint: ReducibilityHint::Regular(0),
    })
    .unwrap();
    let ca = k.const_(a_name, vec![]);
    let cb = k.const_(b_name, vec![]);
    assert!(k.def_eq(ca, cb), "two defs with equal values are def_eq");

    // c : Sort 2 := Sort 1  (different value)
    let two = k.level_succ(one);
    let s2 = k.sort(two);
    let c_name = k.name_str(anon, "c");
    k.add_declaration(Declaration::Definition {
        name: c_name,
        uparams: vec![],
        ty: s2,
        value: s1,
        hint: ReducibilityHint::Regular(0),
    })
    .unwrap();
    let cc = k.const_(c_name, vec![]);
    assert!(
        !k.def_eq(ca, cc),
        "defs with different values are not def_eq"
    );
}

/// The same-const lazy-delta short-circuit: `id.{1}` is def_eq to `id.{1}`
/// (same const, same regular hint), and stays usable through applications.
#[test]
fn same_const_lazy_delta_short_circuit() {
    let mut k = Kernel::new();
    let (id_name, _u) = declare_id(&mut k);
    let z = k.level_zero();
    let one = k.level_succ(z);
    let s0 = k.sort_zero();

    let lhs = k.const_(id_name, vec![one]);
    let lhs = k.app(lhs, s0);
    let rhs = k.const_(id_name, vec![one]);
    let rhs = k.app(rhs, s0);
    assert!(k.def_eq(lhs, rhs));

    // Different universe args on the same const: still def_eq here because both
    // unfold to identity lambdas that are def_eq after β on Sort 0.
    let two = k.level_succ(one);
    let rhs2 = k.const_(id_name, vec![two]);
    let rhs2 = k.app(rhs2, s0);
    assert!(k.def_eq(lhs, rhs2));
}

/// Opaque is admitted (value is checked) but does NOT δ-unfold in def_eq/whnf.
#[test]
fn opaque_admitted_but_not_unfolded() {
    let mut k = Kernel::new();
    let anon = k.anon();
    let z = k.level_zero();
    let one = k.level_succ(z);
    let s1 = k.sort(one);
    let s0 = k.sort_zero();
    let op_name = k.name_str(anon, "op");
    // op : Sort 1 := Sort 0  (value type-checks against Sort 1)
    k.add_declaration(Declaration::Opaque {
        name: op_name,
        uparams: vec![],
        ty: s1,
        value: s0,
    })
    .expect("opaque should admit");

    let c = k.const_(op_name, vec![]);
    // Does NOT unfold in whnf.
    assert_eq!(k.whnf(c), c);
    // Not def_eq to its value (opaque never unfolds).
    assert!(!k.def_eq(c, s0));
    // But trivially def_eq to itself.
    assert!(k.def_eq(c, c));
}

/// add_declaration REJECTS a definition whose value's type ≠ declared type.
#[test]
fn reject_value_type_mismatch() {
    let mut k = Kernel::new();
    let anon = k.anon();
    let z = k.level_zero();
    let one = k.level_succ(z);
    let two = k.level_succ(one);
    let s1 = k.sort(one);
    // bad : Sort 1 := Sort 1   but Sort 1 : Sort 2 ≠ Sort 1.
    let bad_name = k.name_str(anon, "bad");
    let err = k
        .add_declaration(Declaration::Definition {
            name: bad_name,
            uparams: vec![],
            ty: s1,
            value: s1,
            hint: ReducibilityHint::Regular(0),
        })
        .unwrap_err();
    assert!(
        matches!(err, KernelError::DeclarationValueMismatch { .. }),
        "got {err:?}"
    );
    // Rejected: not admitted.
    assert!(!k.environment().contains(bad_name));
    let _ = two;
}

/// add_declaration REJECTS a redeclared name.
#[test]
fn reject_redeclaration() {
    let mut k = Kernel::new();
    let anon = k.anon();
    let s0 = k.sort_zero();
    let n = k.name_str(anon, "dup");
    k.add_declaration(Declaration::Axiom {
        name: n,
        uparams: vec![],
        ty: s0,
    })
    .unwrap();
    let err = k
        .add_declaration(Declaration::Axiom {
            name: n,
            uparams: vec![],
            ty: s0,
        })
        .unwrap_err();
    assert!(
        matches!(err, KernelError::DeclarationExists { .. }),
        "got {err:?}"
    );
    assert_eq!(k.environment().len(), 1);
}

/// add_declaration REJECTS a declaration whose type is not a sort.
#[test]
fn reject_type_not_a_sort() {
    let mut k = Kernel::new();
    let anon = k.anon();
    let s0 = k.sort_zero();
    // A type that is a lambda `λ (x : Sort 0), x : Sort 0 → Sort 0` (a Pi, not
    // a Sort), so it is not a valid declaration type.
    let xb = k.bvar(0);
    let bad_ty = k.lam(anon, s0, xb, BinderInfo::Default);
    let n = k.name_str(anon, "weird");
    let err = k
        .add_declaration(Declaration::Axiom {
            name: n,
            uparams: vec![],
            ty: bad_ty,
        })
        .unwrap_err();
    assert!(
        matches!(err, KernelError::DeclarationTypeNotASort { .. }),
        "got {err:?}"
    );
}

/// A theorem is admitted and its `Const` infers its declared (Prop) type.
#[test]
fn theorem_admits_and_infers() {
    let mut k = Kernel::new();
    let anon = k.anon();
    // First an axiom `P : Prop` (Sort 0 is a type, so P : Sort 0 is fine as a
    // proposition placeholder via an axiom whose type is Sort 0).
    // We declare `triv : Sort 0 := <a proof>`. To have a concrete proof, use
    // `True`-like: declare axiom `p : Sort 0` (a Prop), and `pf : p`.
    let p_name = k.name_str(anon, "p");
    let s0 = k.sort_zero();
    k.add_declaration(Declaration::Axiom {
        name: p_name,
        uparams: vec![],
        ty: s0,
    })
    .unwrap();
    // axiom proof : p
    let proof_name = k.name_str(anon, "proof");
    let p_const = k.const_(p_name, vec![]);
    k.add_declaration(Declaration::Axiom {
        name: proof_name,
        uparams: vec![],
        ty: p_const,
    })
    .unwrap();
    // theorem thm : p := proof
    let thm_name = k.name_str(anon, "thm");
    let proof_const = k.const_(proof_name, vec![]);
    let p_const2 = k.const_(p_name, vec![]);
    k.add_declaration(Declaration::Theorem {
        name: thm_name,
        uparams: vec![],
        ty: p_const2,
        value: proof_const,
    })
    .expect("theorem should admit");

    let thm_c = k.const_(thm_name, vec![]);
    let ty = k.infer(thm_c).unwrap();
    assert_eq!(ty, p_const2);
}

/// Deferred boundary still errors cleanly: a `Lit` term yields UnsupportedLit
/// (no panic).
#[test]
fn deferred_lit_still_errors() {
    let mut k = Kernel::new();
    let n = k.lit(Lit::nat(3_u8));
    let err = k.infer(n).unwrap_err();
    assert!(matches!(err, KernelError::UnsupportedLit), "got {err:?}");
}

/// A declaration whose value references an UNKNOWN const is rejected (the
/// trusted gate surfaces UnknownConst, not a panic).
#[test]
fn reject_value_with_dangling_const() {
    let mut k = Kernel::new();
    let anon = k.anon();
    let s0 = k.sort_zero();
    let missing = k.name_str(anon, "missing");
    let dangling = k.const_(missing, vec![]);
    let n = k.name_str(anon, "uses_missing");
    let err = k
        .add_declaration(Declaration::Definition {
            name: n,
            uparams: vec![],
            ty: s0,
            value: dangling,
            hint: ReducibilityHint::Regular(0),
        })
        .unwrap_err();
    assert!(
        matches!(err, KernelError::UnknownConst { .. }),
        "got {err:?}"
    );
}

/// Determinism: building the same environment twice yields the same inferred
/// type id for a polymorphic const instantiation.
#[test]
fn determinism_env() {
    fn build() -> usize {
        let mut k = Kernel::new();
        let (id_name, _u) = declare_id(&mut k);
        let z = k.level_zero();
        let one = k.level_succ(z);
        let c = k.const_(id_name, vec![one]);
        k.infer(c).unwrap().index()
    }
    assert_eq!(build(), build());
}
