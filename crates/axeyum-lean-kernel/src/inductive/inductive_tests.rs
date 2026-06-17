//! Tests for the inductive layer (ADR-0036, slice 4): the `add_inductive`
//! admission gate, recursor generation (with the self-check that the generated
//! recursor type infers to a `Sort`), and ι-reduction in WHNF — validated
//! against KNOWN recursors and ι-rules (`Bool`, a 3-way enum, a structure with
//! fields), plus the rejections the trusted gate must catch.
#![allow(
    clippy::many_single_char_names,
    clippy::similar_names,
    clippy::doc_markdown
)]

use crate::env::Declaration;
use crate::expr::ExprNode;
use crate::tc::KernelError;
use crate::{BinderInfo, Kernel};

/// Declare an enum-style inductive `name : Sort 1` with the given nullary
/// constructors. Returns `(ind_name, rec_name, ctor_names)`.
fn declare_enum(
    k: &mut Kernel,
    name: &str,
    ctor_strs: &[&str],
) -> (crate::NameId, crate::NameId, Vec<crate::NameId>) {
    let anon = k.anon();
    let ind_name = k.name_str(anon, name);
    // I : Sort 1  (a `Type`).
    let z = k.level_zero();
    let one = k.level_succ(z);
    let ty = k.sort(one);
    let ind_const = k.const_(ind_name, vec![]);

    let ctor_names: Vec<crate::NameId> = ctor_strs.iter().map(|s| k.name_str(anon, *s)).collect();
    let ctors: Vec<(crate::NameId, crate::ExprId)> =
        ctor_names.iter().map(|&cn| (cn, ind_const)).collect();

    k.add_inductive(ind_name, &[], ty, &ctors)
        .expect("enum should admit");
    let rec_name = k.name_str(ind_name, "rec");
    (ind_name, rec_name, ctor_names)
}

/// Bool backbone: `Bool : Sort 1` with `tt, ff`. The recursor admits, its type
/// infers, and `Bool.rec (fun _ => A) a b tt` ι-reduces to `a`, `… ff` to `b`.
#[test]
fn bool_rec_iota_picks_right_minor() {
    let mut k = Kernel::new();
    let (ind_name, rec_name, ctors) = declare_enum(&mut k, "Bool", &["tt", "ff"]);
    let tt = k.const_(ctors[0], vec![]);
    let ff = k.const_(ctors[1], vec![]);

    // The recursor is registered and its type infers to a Sort (self-check
    // duplicated here at the test level).
    assert!(k.environment().contains(rec_name));
    let rec_decl = k.environment().get(rec_name).unwrap().clone();
    let rec_ty = rec_decl.ty();
    let rec_ty_ty = k.infer(rec_ty).unwrap();
    assert!(matches!(k.expr_node(rec_ty_ty), ExprNode::Sort(_)));

    // Recursor uparams: [v] (elim level), since Bool has none.
    let v = match &rec_decl {
        Declaration::Recursor { uparams, .. } => uparams[0],
        _ => panic!("expected recursor"),
    };
    let v_lvl = k.level_param(v);

    // motive := fun (_ : Bool) => A   where A := Sort 0 (an abstract type).
    let s0 = k.sort_zero();
    let anon = k.anon();
    let ind_const = k.const_(ind_name, vec![]);
    let motive = k.lam(anon, ind_const, s0, BinderInfo::Default);

    // a, b : A = Sort 0. Use distinct free variables.
    let a = k.fvar(1);
    let b = k.fvar(2);

    // Bool.rec.{v} motive a b tt   (universe arg = v's own param level is fine
    // for whnf; the const carries one level arg).
    let rec_const = k.const_(rec_name, vec![v_lvl]);
    let app_tt = {
        let e = k.app(rec_const, motive);
        let e = k.app(e, a);
        let e = k.app(e, b);
        k.app(e, tt)
    };
    assert_eq!(k.whnf(app_tt), a, "Bool.rec … tt should ι-reduce to a");

    let rec_const2 = k.const_(rec_name, vec![v_lvl]);
    let app_ff = {
        let e = k.app(rec_const2, motive);
        let e = k.app(e, a);
        let e = k.app(e, b);
        k.app(e, ff)
    };
    assert_eq!(k.whnf(app_ff), b, "Bool.rec … ff should ι-reduce to b");
}

/// A 3-way enum: ι picks the right minor for each of three constructors.
#[test]
fn three_way_enum_iota() {
    let mut k = Kernel::new();
    let (ind_name, rec_name, ctors) = declare_enum(&mut k, "RGB", &["red", "green", "blue"]);

    let rec_decl = k.environment().get(rec_name).unwrap().clone();
    let v = match &rec_decl {
        Declaration::Recursor { uparams, .. } => uparams[0],
        _ => panic!(),
    };
    let v_lvl = k.level_param(v);

    let s0 = k.sort_zero();
    let anon = k.anon();
    let ind_const = k.const_(ind_name, vec![]);
    let motive = k.lam(anon, ind_const, s0, BinderInfo::Default);

    let m0 = k.fvar(10);
    let m1 = k.fvar(11);
    let m2 = k.fvar(12);
    let minors = [m0, m1, m2];

    for (i, &ctor) in ctors.iter().enumerate() {
        let ctor_c = k.const_(ctor, vec![]);
        let rec_const = k.const_(rec_name, vec![v_lvl]);
        let e = k.app(rec_const, motive);
        let e = k.app(e, m0);
        let e = k.app(e, m1);
        let e = k.app(e, m2);
        let e = k.app(e, ctor_c);
        assert_eq!(k.whnf(e), minors[i], "ctor {i} should pick minor {i}");
    }
}

/// A structure with fields: `mk : A → B → P` for abstract `A, B : Sort 0`. The
/// minor premise binds the fields; `P.rec C m (mk x y)` ι-reduces to `m x y`.
#[test]
fn structure_with_fields_iota_passes_fields() {
    let mut k = Kernel::new();
    let anon = k.anon();

    // First declare abstract types A, B : Sort 1 as axioms (so `mk`'s fields
    // A, B type-check as types).
    let z = k.level_zero();
    let one = k.level_succ(z);
    let s1 = k.sort(one);
    let a_name = k.name_str(anon, "A");
    let b_name = k.name_str(anon, "B");
    k.add_declaration(Declaration::Axiom {
        name: a_name,
        uparams: vec![],
        ty: s1,
    })
    .unwrap();
    k.add_declaration(Declaration::Axiom {
        name: b_name,
        uparams: vec![],
        ty: s1,
    })
    .unwrap();
    let a_ty = k.const_(a_name, vec![]);
    let b_ty = k.const_(b_name, vec![]);

    // P : Sort 1 with mk : A → B → P  (a closed Pi telescope; A, B are
    // non-recursive — they don't mention P).
    let p_name = k.name_str(anon, "P");
    let p_const = k.const_(p_name, vec![]);
    let mk_name = k.name_str(anon, "mk");
    // mk type: Π (_ : A) (_ : B), P   — body P is closed (no field reference).
    let mk_ty = {
        let inner = k.pi(anon, b_ty, p_const, BinderInfo::Default);
        k.pi(anon, a_ty, inner, BinderInfo::Default)
    };
    k.add_inductive(p_name, &[], s1, &[(mk_name, mk_ty)])
        .expect("structure should admit");
    let rec_name = k.name_str(p_name, "rec");

    let rec_decl = k.environment().get(rec_name).unwrap().clone();
    // Self-check the generated recursor type.
    let rec_ty = rec_decl.ty();
    let rec_ty_ty = k.infer(rec_ty).unwrap();
    assert!(matches!(k.expr_node(rec_ty_ty), ExprNode::Sort(_)));

    let v = match &rec_decl {
        Declaration::Recursor { uparams, .. } => uparams[0],
        _ => panic!(),
    };
    let v_lvl = k.level_param(v);

    // motive := fun (_ : P) => Sort 0.
    let s0 = k.sort_zero();
    let p_const2 = k.const_(p_name, vec![]);
    let motive = k.lam(anon, p_const2, s0, BinderInfo::Default);

    // m : Π (x : A) (y : B), motive (mk x y). We just need a free var of the
    // right shape for ι; use an fvar `m` and concrete field args x, y.
    let m = k.fvar(20);
    let x = k.fvar(21); // : A
    let y = k.fvar(22); // : B

    // mk x y
    let mk_const = k.const_(mk_name, vec![]);
    let mk_xy = {
        let e = k.app(mk_const, x);
        k.app(e, y)
    };

    // P.rec motive m (mk x y)  ι→  m x y
    let rec_const = k.const_(rec_name, vec![v_lvl]);
    let app = {
        let e = k.app(rec_const, motive);
        let e = k.app(e, m);
        k.app(e, mk_xy)
    };
    let expected = {
        let e = k.app(m, x);
        k.app(e, y)
    };
    assert_eq!(k.whnf(app), expected, "P.rec C m (mk x y) ι→ m x y");
}

/// Reject: a constructor whose result isn't the inductive.
#[test]
fn reject_wrong_result_head() {
    let mut k = Kernel::new();
    let anon = k.anon();
    let z = k.level_zero();
    let one = k.level_succ(z);
    let s1 = k.sort(one);
    let ind_name = k.name_str(anon, "Foo");
    // ctor result is `Sort 0`, not `Foo`.
    let s0 = k.sort_zero();
    let bad_ctor = k.name_str(anon, "bad");
    let err = k
        .add_inductive(ind_name, &[], s1, &[(bad_ctor, s0)])
        .unwrap_err();
    assert!(
        matches!(err, KernelError::ConstructorResultMismatch { .. }),
        "got {err:?}"
    );
    // Nothing admitted (rolled back).
    assert!(!k.environment().contains(ind_name));
    assert!(!k.environment().contains(bad_ctor));
}

/// Reject: a recursive constructor (a field mentions the inductive).
#[test]
fn reject_recursive_constructor() {
    let mut k = Kernel::new();
    let anon = k.anon();
    let z = k.level_zero();
    let one = k.level_succ(z);
    let s1 = k.sort(one);
    let ind_name = k.name_str(anon, "Rec");
    let ind_const = k.const_(ind_name, vec![]);
    // ctor: Π (_ : Rec), Rec   — the field type mentions `Rec` (recursive).
    let cn = k.name_str(anon, "node");
    let cty = k.pi(anon, ind_const, ind_const, BinderInfo::Default);
    let err = k
        .add_inductive(ind_name, &[], s1, &[(cn, cty)])
        .unwrap_err();
    assert!(
        matches!(err, KernelError::RecursiveInductiveNotSupported { .. }),
        "got {err:?}"
    );
    assert!(!k.environment().contains(ind_name));
    assert!(!k.environment().contains(cn));
}

/// Reject: an inductive whose type is not a `Sort` (e.g. a `Pi` ⇒ parametric,
/// deferred).
#[test]
fn reject_type_not_a_sort() {
    let mut k = Kernel::new();
    let anon = k.anon();
    let z = k.level_zero();
    let one = k.level_succ(z);
    let s1 = k.sort(one);
    let s0 = k.sort_zero();
    // ty := Π (_ : Sort 0), Sort 1   (a parametric inductive's type — deferred).
    let bad_ty = k.pi(anon, s0, s1, BinderInfo::Default);
    let ind_name = k.name_str(anon, "Param");
    let err = k.add_inductive(ind_name, &[], bad_ty, &[]).unwrap_err();
    assert!(
        matches!(err, KernelError::InductiveTypeNotASort { .. }),
        "got {err:?}"
    );
    assert!(!k.environment().contains(ind_name));
}

/// Reject: a duplicate inductive name.
#[test]
fn reject_duplicate_name() {
    let mut k = Kernel::new();
    let (ind_name, _rec, _ctors) = declare_enum(&mut k, "Dup", &["x"]);
    // Re-declare `Dup`.
    let z = k.level_zero();
    let one = k.level_succ(z);
    let s1 = k.sort(one);
    let err = k.add_inductive(ind_name, &[], s1, &[]).unwrap_err();
    assert!(
        matches!(err, KernelError::DeclarationExists { .. }),
        "got {err:?}"
    );
}

/// The generated recursor's type type-checks (the soundness self-check, also
/// done internally by `add_inductive`).
#[test]
fn generated_recursor_type_infers() {
    let mut k = Kernel::new();
    let (_ind, rec_name, _ctors) = declare_enum(&mut k, "Two", &["a", "b"]);
    let rec_ty = k.environment().get(rec_name).unwrap().ty();
    let inferred = k.infer(rec_ty).unwrap();
    assert!(matches!(k.expr_node(inferred), ExprNode::Sort(_)));
}

/// `infer(Const(I.rec / c_i / I))` resolves via the registered declarations.
#[test]
fn const_resolution_for_inductive_family() {
    let mut k = Kernel::new();
    let (ind_name, rec_name, ctors) = declare_enum(&mut k, "Col", &["c0"]);

    // infer(Const(Col)) is the inductive's declared type, `Sort 1`.
    let ind_c = k.const_(ind_name, vec![]);
    let ind_ty = k.infer(ind_c).unwrap();
    let z = k.level_zero();
    let one = k.level_succ(z);
    let s1 = k.sort(one);
    assert_eq!(ind_ty, s1);

    // infer(Const(c0)) : Col.
    let c0 = k.const_(ctors[0], vec![]);
    let c0_ty = k.infer(c0).unwrap();
    assert_eq!(c0_ty, ind_c);

    // infer(Const(Col.rec, [v])) succeeds (resolves the recursor type).
    let rec_decl = k.environment().get(rec_name).unwrap().clone();
    let v = match &rec_decl {
        Declaration::Recursor { uparams, .. } => uparams[0],
        _ => panic!(),
    };
    let v_lvl = k.level_param(v);
    let rec_c = k.const_(rec_name, vec![v_lvl]);
    assert!(k.infer(rec_c).is_ok());
}

/// Determinism: building the same inductive twice yields the same recursor type
/// id.
#[test]
fn determinism_inductive() {
    fn build() -> usize {
        let mut k = Kernel::new();
        let (_ind, rec_name, _ctors) = declare_enum(&mut k, "Det", &["p", "q"]);
        k.environment().get(rec_name).unwrap().ty().index()
    }
    assert_eq!(build(), build());
}
