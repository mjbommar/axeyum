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

/// Reject: a **reflexive / higher-order** recursive field — a field whose type
/// is a `Pi` ending in the inductive (`(Nat → I) → I`). Direct recursive fields
/// are now admitted (slice 5), but reflexive ones are still deferred.
#[test]
fn reject_reflexive_recursive_field() {
    let mut k = Kernel::new();
    let anon = k.anon();
    let z = k.level_zero();
    let one = k.level_succ(z);
    let s1 = k.sort(one);
    let ind_name = k.name_str(anon, "Refl");
    let ind_const = k.const_(ind_name, vec![]);
    // ctor: Π (_ : (Refl → Refl)), Refl — the field type is a Pi ending in I.
    let cn = k.name_str(anon, "node");
    let field_ty = k.pi(anon, ind_const, ind_const, BinderInfo::Default);
    let cty = k.pi(anon, field_ty, ind_const, BinderInfo::Default);
    let err = k
        .add_inductive(ind_name, &[], s1, &[(cn, cty)])
        .unwrap_err();
    assert!(
        matches!(err, KernelError::ReflexiveOrNestedNotSupported { .. }),
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

// ---------------------------------------------------------------------------
// Recursive inductives (slice 5): Nat and a binary tree.
// ---------------------------------------------------------------------------

/// Declare `Nat : Sort 1` with `zero : Nat` and `succ : Nat → Nat`. Returns
/// `(nat_name, rec_name, [zero_name, succ_name])`.
fn declare_nat(k: &mut Kernel) -> (crate::NameId, crate::NameId, [crate::NameId; 2]) {
    let anon = k.anon();
    let nat = k.name_str(anon, "Nat");
    let z = k.level_zero();
    let one = k.level_succ(z);
    let s1 = k.sort(one);
    let nat_const = k.const_(nat, vec![]);

    let zero = k.name_str(anon, "zero");
    let succ = k.name_str(anon, "succ");
    // succ : Nat → Nat  (a direct recursive field).
    let succ_ty = k.pi(anon, nat_const, nat_const, BinderInfo::Default);
    k.add_inductive(nat, &[], s1, &[(zero, nat_const), (succ, succ_ty)])
        .expect("Nat should admit");
    let rec_name = k.name_str(nat, "rec");
    (nat, rec_name, [zero, succ])
}

/// Nat admits; its recursor type infer-checks (the self-check — the key signal
/// the IH de Bruijn indices are right); the `succ` minor has the shape
/// `Π (n : Nat) (ih : motive n), motive (succ n)`.
#[test]
fn nat_admits_and_succ_minor_has_ih() {
    let mut k = Kernel::new();
    let (nat, rec_name, [_zero, succ]) = declare_nat(&mut k);

    // The recursor type infer-checks to a Sort (also done internally).
    let rec_decl = k.environment().get(rec_name).unwrap().clone();
    let rec_ty = rec_decl.ty();
    let inferred = k.infer(rec_ty).unwrap();
    assert!(matches!(k.expr_node(inferred), ExprNode::Sort(_)));

    // Inspect the recursor type's telescope: {motive} (m_zero) (m_succ) (major).
    // Walk down two Pis (motive, m_zero) to the m_succ binder, and check the
    // m_succ minor type is `Π (n : Nat) (ih : motive n), motive (succ n)`.
    let motive_pi = rec_ty;
    let ExprNode::Pi(_, _motive_ty, after_motive, _) = k.expr_node(motive_pi).clone() else {
        panic!("rec ty should start with the motive Pi");
    };
    let ExprNode::Pi(_, _m_zero_ty, after_zero, _) = k.expr_node(after_motive).clone() else {
        panic!("expected the zero minor Pi");
    };
    let ExprNode::Pi(_, m_succ_ty, _after_succ, _) = k.expr_node(after_zero).clone() else {
        panic!("expected the succ minor Pi");
    };
    // m_succ_ty = Π (n : Nat), Π (ih : motive n), motive (succ n).
    let ExprNode::Pi(_, n_ty, succ_minor_body, _) = k.expr_node(m_succ_ty).clone() else {
        panic!("succ minor should bind the field n");
    };
    // The field's type is `Nat`.
    let nat_const = k.const_(nat, vec![]);
    assert_eq!(n_ty, nat_const, "succ field n : Nat");
    // Next binder is the IH `ih : motive (BVar 0)` (i.e. `motive n`).
    let ExprNode::Pi(_, ih_ty, motive_result, _) = k.expr_node(succ_minor_body).clone() else {
        panic!("succ minor should bind one induction hypothesis after the field");
    };
    // ih_ty is `motive (BVar 0)` — an application whose argument is the field n.
    let ExprNode::App(_ih_motive, ih_arg) = k.expr_node(ih_ty).clone() else {
        panic!("IH type should be `motive n` (an application)");
    };
    assert!(
        matches!(k.expr_node(ih_arg), ExprNode::BVar(0)),
        "IH argument should be the just-bound field n (BVar 0)"
    );
    // motive_result is `motive (succ (BVar 1))` — succ applied to the field,
    // which is now BVar 1 (one binder, the IH, was crossed).
    let ExprNode::App(_m, succ_app) = k.expr_node(motive_result).clone() else {
        panic!("minor result should be `motive (succ n)`");
    };
    let (head, args) = {
        let mut h = succ_app;
        let mut a = Vec::new();
        while let ExprNode::App(f, x) = k.expr_node(h).clone() {
            a.push(x);
            h = f;
        }
        a.reverse();
        (h, a)
    };
    assert!(
        matches!(k.expr_node(head), ExprNode::Const(n, _) if *n == succ),
        "minor result head should be `succ`"
    );
    assert_eq!(args.len(), 1, "succ applied to one arg");
    assert!(
        matches!(k.expr_node(args[0]), ExprNode::BVar(1)),
        "succ's argument should be the field n (BVar 1, IH crossed)"
    );
}

/// Nat ι backbone: `Nat.rec C z s zero` ι→ `z`, and
/// `Nat.rec C z s (succ k)` ι→ `s k (Nat.rec C z s k)` (the recursive call
/// appears in the reduct).
#[test]
fn nat_rec_iota_backbone() {
    let mut k = Kernel::new();
    let (_nat, rec_name, [zero, succ]) = declare_nat(&mut k);

    let rec_decl = k.environment().get(rec_name).unwrap().clone();
    let v = match &rec_decl {
        Declaration::Recursor { uparams, .. } => uparams[0],
        _ => panic!(),
    };
    let v_lvl = k.level_param(v);

    // Abstract C : Nat → Sort 0, z, s, and an fvar k : Nat.
    let big_c = k.fvar(1);
    let z_min = k.fvar(2);
    let s_min = k.fvar(3);
    let kk = k.fvar(4);

    // Nat.rec C z s zero  ι→  z
    let zero_c = k.const_(zero, vec![]);
    let rec_const = k.const_(rec_name, vec![v_lvl]);
    let app_zero = {
        let e = k.app(rec_const, big_c);
        let e = k.app(e, z_min);
        let e = k.app(e, s_min);
        k.app(e, zero_c)
    };
    assert_eq!(k.whnf(app_zero), z_min, "Nat.rec C z s zero ι→ z");

    // Nat.rec C z s (succ k)  ι→  s k (Nat.rec C z s k)
    let succ_c = k.const_(succ, vec![]);
    let succ_k = k.app(succ_c, kk);
    let rec_const2 = k.const_(rec_name, vec![v_lvl]);
    let app_succ = {
        let e = k.app(rec_const2, big_c);
        let e = k.app(e, z_min);
        let e = k.app(e, s_min);
        k.app(e, succ_k)
    };
    // Expected: s k (Nat.rec C z s k).
    let inner_rec = {
        let rc = k.const_(rec_name, vec![v_lvl]);
        let e = k.app(rc, big_c);
        let e = k.app(e, z_min);
        let e = k.app(e, s_min);
        k.app(e, kk)
    };
    let expected = {
        let e = k.app(s_min, kk);
        k.app(e, inner_rec)
    };
    // One ι step (whnf does not recurse into the spine, so the inner rec is left
    // as a stuck `Nat.rec … k`). Compare structurally.
    let reduced = k.whnf(app_succ);
    assert_eq!(
        reduced, expected,
        "Nat.rec C z s (succ k) ι→ s k (Nat.rec C z s k)"
    );
}

/// End-to-end recursive computation: with `C := fun _ => Nat`,
/// `z := zero`, `s := fun (_ : Nat) (ih : Nat) => succ ih`, the term
/// `Nat.rec C z s (succ (succ zero))` whnf's all the way to `succ (succ zero)`
/// (an identity-by-recursion) — multi-step ι + β actually computes.
#[test]
fn nat_rec_computes_identity() {
    let mut k = Kernel::new();
    let (nat, rec_name, [zero, succ]) = declare_nat(&mut k);
    let anon = k.anon();

    let rec_decl = k.environment().get(rec_name).unwrap().clone();
    let v = match &rec_decl {
        Declaration::Recursor { uparams, .. } => uparams[0],
        _ => panic!(),
    };
    // For a `Sort 1`-valued motive (C : Nat → Sort 1 = Type), elaborate the
    // recursor at v := 1 so `C := fun _ => Nat` is well-typed.
    let lz = k.level_zero();
    let one = k.level_succ(lz);
    let _ = v;
    let v_lvl = one;

    let nat_const = k.const_(nat, vec![]);
    let zero_c = k.const_(zero, vec![]);
    let succ_c = k.const_(succ, vec![]);

    // C := fun (_ : Nat) => Nat.
    let big_c = k.lam(anon, nat_const, nat_const, BinderInfo::Default);
    // z := zero.
    let z_min = zero_c;
    // s := fun (_ : Nat) (ih : Nat) => succ ih   (ih is BVar 0).
    let s_min = {
        let v0 = k.bvar(0);
        let succ_ih = k.app(succ_c, v0);
        let inner = k.lam(anon, nat_const, succ_ih, BinderInfo::Default);
        k.lam(anon, nat_const, inner, BinderInfo::Default)
    };

    // two := succ (succ zero).
    let two = {
        let s1 = k.app(succ_c, zero_c);
        k.app(succ_c, s1)
    };

    // Nat.rec.{1} C z s two.
    let rec_const = k.const_(rec_name, vec![v_lvl]);
    let app = {
        let e = k.app(rec_const, big_c);
        let e = k.app(e, z_min);
        let e = k.app(e, s_min);
        k.app(e, two)
    };
    // whnf only reduces the head; to fully compute we whnf, then whnf the
    // resulting spine arguments. The head reduces to `succ (Nat.rec … (succ
    // zero))`; recurse into the argument to drive the recursion to completion.
    let computed = whnf_deep(&mut k, app);
    assert_eq!(
        computed, two,
        "Nat.rec (id by recursion) on 2 computes to 2"
    );
}

/// Fully normalize `e` by WHNF-ing the head and then recursively each spine
/// argument (a test-only "deep" normalizer for closed first-order terms).
fn whnf_deep(k: &mut Kernel, e: crate::ExprId) -> crate::ExprId {
    let e = k.whnf(e);
    let mut spine = Vec::new();
    let mut h = e;
    while let ExprNode::App(f, a) = k.expr_node(h).clone() {
        spine.push(a);
        h = f;
    }
    spine.reverse();
    let mut out = h;
    for a in spine {
        let a = whnf_deep(k, a);
        out = k.app(out, a);
    }
    out
}

/// A binary-tree-like type with two recursive fields: `leaf : Tree`,
/// `node : Tree → Tree → Tree`. The recursor has **two** IH binders for `node`;
/// ι passes two recursive calls.
#[test]
fn tree_two_recursive_fields() {
    let mut k = Kernel::new();
    let anon = k.anon();
    let z = k.level_zero();
    let one = k.level_succ(z);
    let s1 = k.sort(one);
    let tree = k.name_str(anon, "Tree");
    let tree_const = k.const_(tree, vec![]);
    let leaf = k.name_str(anon, "leaf");
    let node = k.name_str(anon, "node");
    // node : Tree → Tree → Tree.
    let node_ty = {
        let inner = k.pi(anon, tree_const, tree_const, BinderInfo::Default);
        k.pi(anon, tree_const, inner, BinderInfo::Default)
    };
    k.add_inductive(tree, &[], s1, &[(leaf, tree_const), (node, node_ty)])
        .expect("Tree should admit");
    let rec_name = k.name_str(tree, "rec");

    // Self-check.
    let rec_decl = k.environment().get(rec_name).unwrap().clone();
    let rec_ty = rec_decl.ty();
    let rec_ty_ty = k.infer(rec_ty).unwrap();
    assert!(matches!(k.expr_node(rec_ty_ty), ExprNode::Sort(_)));
    let v = match &rec_decl {
        Declaration::Recursor { uparams, .. } => uparams[0],
        _ => panic!(),
    };
    let v_lvl = k.level_param(v);

    // The `node` minor type must bind two fields then two IHs:
    // Π (l : Tree) (r : Tree) (ih_l : motive l) (ih_r : motive r),
    //   motive (node l r). Walk the telescope.
    let ExprNode::Pi(_, _motive, after_motive, _) = k.expr_node(rec_ty).clone() else {
        panic!()
    };
    let ExprNode::Pi(_, _m_leaf, after_leaf, _) = k.expr_node(after_motive).clone() else {
        panic!()
    };
    let ExprNode::Pi(_, m_node, _after_node, _) = k.expr_node(after_leaf).clone() else {
        panic!()
    };
    // Count the leading Pi binders of the node minor and check the last two are
    // the IHs (their types are `motive (BVar _)` applications).
    let mut binders = Vec::new();
    let mut cur = m_node;
    while let ExprNode::Pi(_, dom, body, _) = k.expr_node(cur).clone() {
        binders.push(dom);
        cur = body;
    }
    assert_eq!(binders.len(), 4, "node minor: 2 fields + 2 IHs");
    // The last two binder domains are `motive _` applications (the IHs).
    for d in &binders[2..] {
        assert!(
            matches!(k.expr_node(*d), ExprNode::App(..)),
            "node IH binder should be a `motive _` application"
        );
    }

    // ι: Tree.rec C m_leaf m_node (node leaf leaf)
    //      ι→ m_node leaf leaf (Tree.rec C m_leaf m_node leaf)
    //                          (Tree.rec C m_leaf m_node leaf)
    let big_c = k.fvar(1);
    let m_leaf = k.fvar(2);
    let m_node = k.fvar(3);
    let leaf_c = k.const_(leaf, vec![]);
    let node_c = k.const_(node, vec![]);
    let node_ll = {
        let e = k.app(node_c, leaf_c);
        k.app(e, leaf_c)
    };
    let rec_const = k.const_(rec_name, vec![v_lvl]);
    let app = {
        let e = k.app(rec_const, big_c);
        let e = k.app(e, m_leaf);
        let e = k.app(e, m_node);
        k.app(e, node_ll)
    };
    let inner_rec = {
        let rc = k.const_(rec_name, vec![v_lvl]);
        let e = k.app(rc, big_c);
        let e = k.app(e, m_leaf);
        let e = k.app(e, m_node);
        k.app(e, leaf_c)
    };
    let expected = {
        let e = k.app(m_node, leaf_c);
        let e = k.app(e, leaf_c);
        let e = k.app(e, inner_rec);
        k.app(e, inner_rec)
    };
    assert_eq!(
        k.whnf(app),
        expected,
        "node ι passes the two fields and two recursive calls"
    );
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
