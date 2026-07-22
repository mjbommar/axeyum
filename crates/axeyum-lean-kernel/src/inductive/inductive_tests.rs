//! Tests for the inductive layer (ADR-0036, slice 7): the `add_inductive`
//! admission gate, recursor generation (with the self-check that the generated
//! recursor type infers to a `Sort`), and ι-reduction in WHNF — validated
//! against KNOWN recursors and ι-rules. Covers the slice-4 enums/structures, the
//! slice-5 recursive types (`Nat`, binary trees), the slice-6 **parametric**
//! families (`List`, `Option`, `Prod`, `Sum`), and the slice-7 **indexed**
//! families (`Eq` — the backbone — plus a simple indexed enum), with the
//! dependent-motive `Eq.rec` self-check, its ι-reduction on `refl`, and a
//! transport that computes; recursive-indexed and higher-order recursive
//! families; plus the malformed/non-positive rejections the trusted gate must
//! catch.
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

    k.add_inductive(ind_name, &[], 0, ty, &ctors)
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
    k.add_inductive(p_name, &[], 0, s1, &[(mk_name, mk_ty)])
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
        .add_inductive(ind_name, &[], 0, s1, &[(bad_ctor, s0)])
        .unwrap_err();
    assert!(
        matches!(err, KernelError::ConstructorResultMismatch { .. }),
        "got {err:?}"
    );
    // Nothing admitted (rolled back).
    assert!(!k.environment().contains(ind_name));
    assert!(!k.environment().contains(bad_ctor));
}

/// Reject: a mixed-polarity higher-order field. Its codomain occurrence is
/// positive, but its domain occurrence is negative and wins before the later
/// reflexive-feature decline.
#[test]
fn reject_non_positive_recursive_field() {
    let mut k = Kernel::new();
    let anon = k.anon();
    let z = k.level_zero();
    let one = k.level_succ(z);
    let s1 = k.sort(one);
    let ind_name = k.name_str(anon, "Refl");
    let ind_const = k.const_(ind_name, vec![]);
    // ctor: Π (_ : (Refl → Refl)), Refl — the field type contains I on both
    // sides of the inner Pi.
    let cn = k.name_str(anon, "node");
    let field_ty = k.pi(anon, ind_const, ind_const, BinderInfo::Default);
    let cty = k.pi(anon, field_ty, ind_const, BinderInfo::Default);
    let err = k
        .add_inductive(ind_name, &[], 0, s1, &[(cn, cty)])
        .unwrap_err();
    assert!(
        matches!(
            err,
            KernelError::NonPositiveInductiveOccurrence {
                inductive,
                ctor,
                field_index: 0,
            } if inductive == ind_name && ctor == cn
        ),
        "got {err:?}"
    );
    assert!(!k.environment().contains(ind_name));
    assert!(!k.environment().contains(cn));
}

/// A negative occurrence is classified before constructor type inference and
/// before provisional environment insertion. The dangling codomain would be an
/// `UnknownConst` if the later type checker ran first.
#[test]
fn positivity_preflight_precedes_provisional_insertion_and_type_checking() {
    let mut k = Kernel::new();
    let anon = k.anon();
    let one = {
        let zero = k.level_zero();
        k.level_succ(zero)
    };
    let ty = k.sort(one);
    let ind_name = k.name_str(anon, "Preflight");
    let ind_const = k.const_(ind_name, vec![]);
    let unknown_name = k.name_str(anon, "MissingType");
    let unknown = k.const_(unknown_name, vec![]);
    let ctor = k.name_str(ind_name, "mk");
    let negative = k.pi(anon, ind_const, unknown, BinderInfo::Default);
    let ctor_ty = k.pi(anon, negative, ind_const, BinderInfo::Default);

    let before: Vec<_> = k
        .environment()
        .iter()
        .map(|(&name, declaration)| (name, declaration.clone()))
        .collect();
    let error = k
        .add_inductive(ind_name, &[], 0, ty, &[(ctor, ctor_ty)])
        .unwrap_err();
    assert_eq!(
        error,
        KernelError::NonPositiveInductiveOccurrence {
            inductive: ind_name,
            ctor,
            field_index: 0,
        }
    );
    let after: Vec<_> = k
        .environment()
        .iter()
        .map(|(&name, declaration)| (name, declaration.clone()))
        .collect();
    assert_eq!(after, before);
    assert!(!k.environment().contains(ind_name));
    assert!(!k.environment().contains(ctor));
}

/// A family nested below a foreign type constructor is not a valid raw kernel
/// recursive application. Native nested-inductive lowering remains separate.
#[test]
fn reject_family_nested_under_foreign_head() {
    let mut k = Kernel::new();
    let anon = k.anon();
    let one = {
        let zero = k.level_zero();
        k.level_succ(zero)
    };
    let sort_one = k.sort(one);
    let wrapper = k.name_str(anon, "Wrapper");
    let wrapper_ty = k.pi(anon, sort_one, sort_one, BinderInfo::Default);
    k.add_declaration(Declaration::Axiom {
        name: wrapper,
        uparams: vec![],
        ty: wrapper_ty,
    })
    .expect("Wrapper type former should admit");

    let ind_name = k.name_str(anon, "NestedRaw");
    let ind_const = k.const_(ind_name, vec![]);
    let wrapper_const = k.const_(wrapper, vec![]);
    let nested = k.app(wrapper_const, ind_const);
    let ctor = k.name_str(ind_name, "mk");
    let ctor_ty = k.pi(anon, nested, ind_const, BinderInfo::Default);
    let error = k
        .add_inductive(ind_name, &[], 0, sort_one, &[(ctor, ctor_ty)])
        .unwrap_err();
    assert_eq!(
        error,
        KernelError::InvalidInductiveOccurrence {
            inductive: ind_name,
            ctor,
            field_index: 0,
        }
    );
    assert!(!k.environment().contains(ind_name));
    assert!(!k.environment().contains(ctor));
    assert!(k.environment().contains(wrapper));
}

/// A recursive indexed application may not contain the family being declared
/// inside one of its own index expressions (Lean issue #2125 boundary).
#[test]
fn reject_family_occurrence_inside_recursive_index() {
    let mut k = Kernel::new();
    let anon = k.anon();
    let one = {
        let zero = k.level_zero();
        k.level_succ(zero)
    };
    let sort_one = k.sort(one);
    let ind_name = k.name_str(anon, "SelfIndex");
    let ind_const = k.const_(ind_name, vec![]);
    let ind_ty = k.pi(anon, sort_one, sort_one, BinderInfo::Default);
    let ctor = k.name_str(ind_name, "mk");

    // mk : (A : Type) -> SelfIndex (SelfIndex A) -> SelfIndex A
    let ctor_ty = {
        let a_for_result = k.bvar(1);
        let result = k.app(ind_const, a_for_result);
        let a_for_field = k.bvar(0);
        let inner_index = k.app(ind_const, a_for_field);
        let recursive_field = k.app(ind_const, inner_index);
        let inner = k.pi(anon, recursive_field, result, BinderInfo::Default);
        k.pi(anon, sort_one, inner, BinderInfo::Default)
    };
    let error = k
        .add_inductive(ind_name, &[], 0, ind_ty, &[(ctor, ctor_ty)])
        .unwrap_err();
    assert_eq!(
        error,
        KernelError::InvalidInductiveOccurrence {
            inductive: ind_name,
            ctor,
            field_index: 1,
        }
    );
    assert!(!k.environment().contains(ind_name));
    assert!(!k.environment().contains(ctor));
}

/// Admit: an inductive whose type has a leading `Pi` not declared as a
/// parameter (`num_params = 0`) is now an **indexed** family (slice 7). With 0
/// params, `ty := Π (_ : Sort 0), Sort 1` has one index of type `Sort 0` and an
/// empty constructor list — an indexed, ctor-free type — and admits. (Declaring
/// the binder as a parameter, `num_params = 1`, is the parametric path.)
#[test]
fn indexed_ctorless_inductive_admits() {
    let mut k = Kernel::new();
    let anon = k.anon();
    let z = k.level_zero();
    let one = k.level_succ(z);
    let s1 = k.sort(one);
    let s0 = k.sort_zero();
    // ty := Π (_ : Sort 0), Sort 1   (one index of type Sort 0, no params).
    let ty = k.pi(anon, s0, s1, BinderInfo::Default);
    let ind_name = k.name_str(anon, "Indexed0");
    k.add_inductive(ind_name, &[], 0, ty, &[])
        .expect("indexed ctor-free type should admit");
    assert!(k.environment().contains(ind_name));
    // The recursor records one index.
    let rec_name = k.name_str(ind_name, "rec");
    let rec_decl = k.environment().get(rec_name).unwrap().clone();
    match &rec_decl {
        Declaration::Recursor { num_indices, .. } => assert_eq!(*num_indices, 1),
        _ => panic!("expected recursor"),
    }
    // Its type infer-checks (the self-check).
    let rec_ty = rec_decl.ty();
    let inferred = k.infer(rec_ty).unwrap();
    assert!(matches!(k.expr_node(inferred), ExprNode::Sort(_)));
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
    let err = k.add_inductive(ind_name, &[], 0, s1, &[]).unwrap_err();
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

/// A potentially-Prop family with multiple constructors receives no fresh
/// elimination universe, even when its result level is polymorphic. A successor
/// result level is provably nonzero and therefore retains the fresh universe.
#[test]
fn sort_polymorphic_large_elimination_is_conservative() {
    let mut k = Kernel::new();
    let anon = k.anon();
    let u = k.name_str(anon, "u");
    let u_level = k.level_param(u);
    let poly = k.name_str(anon, "Poly");
    let poly_const = k.const_(poly, vec![u_level]);
    let left = k.name_str(poly, "left");
    let right = k.name_str(poly, "right");
    let poly_sort = k.sort(u_level);
    k.add_inductive(
        poly,
        &[u],
        0,
        poly_sort,
        &[(left, poly_const), (right, poly_const)],
    )
    .expect("sort-polymorphic enum should admit with a restricted recursor");
    let poly_rec = k.name_str(poly, "rec");
    match k.environment().get(poly_rec).expect("Poly.rec") {
        Declaration::Recursor { uparams, .. } => assert_eq!(uparams, &[u]),
        _ => panic!("expected recursor"),
    }

    let data = k.name_str(anon, "AlwaysData");
    let data_const = k.const_(data, vec![u_level]);
    let data_left = k.name_str(data, "left");
    let data_right = k.name_str(data, "right");
    let result_level = k.level_succ(u_level);
    let data_sort = k.sort(result_level);
    k.add_inductive(
        data,
        &[u],
        0,
        data_sort,
        &[(data_left, data_const), (data_right, data_const)],
    )
    .expect("provably non-Prop enum should large-eliminate");
    let data_rec = k.name_str(data, "rec");
    match k.environment().get(data_rec).expect("AlwaysData.rec") {
        Declaration::Recursor { uparams, .. } => {
            assert_eq!(uparams.len(), 2);
            assert_eq!(uparams[1], u);
            assert_ne!(uparams[0], u);
        }
        _ => panic!("expected recursor"),
    }
}

/// Lean's one-constructor rule distinguishes a recoverable data field (the
/// field is itself a result index) from a hidden witness and from a field that
/// merely occurs beneath an index expression.
#[test]
#[allow(clippy::too_many_lines)]
fn prop_single_constructor_requires_exact_result_argument() {
    let mut k = Kernel::new();
    let anon = k.anon();
    let (nat, _nat_rec, _nat_ctors) = declare_nat(&mut k);
    let nat_const = k.const_(nat, vec![]);
    let prop = k.sort_zero();

    // Visible : Nat -> Prop | mk (n : Nat) : Visible n
    let visible = k.name_str(anon, "Visible");
    let visible_const = k.const_(visible, vec![]);
    let visible_ty = k.pi(anon, nat_const, prop, BinderInfo::Default);
    let visible_mk = k.name_str(visible, "mk");
    let visible_mk_ty = {
        let n = k.bvar(0);
        let result = k.app(visible_const, n);
        k.pi(anon, nat_const, result, BinderInfo::Default)
    };
    k.add_inductive(visible, &[], 0, visible_ty, &[(visible_mk, visible_mk_ty)])
        .expect("index-exposed field should admit");
    let visible_rec = k.name_str(visible, "rec");
    match k.environment().get(visible_rec).expect("Visible.rec") {
        Declaration::Recursor { uparams, .. } => assert_eq!(uparams.len(), 1),
        _ => panic!("expected recursor"),
    }

    // Hidden : Prop | mk (n : Nat) : Hidden
    let hidden = k.name_str(anon, "Hidden");
    let hidden_const = k.const_(hidden, vec![]);
    let hidden_mk = k.name_str(hidden, "mk");
    let hidden_mk_ty = k.pi(anon, nat_const, hidden_const, BinderInfo::Default);
    k.add_inductive(hidden, &[], 0, prop, &[(hidden_mk, hidden_mk_ty)])
        .expect("hidden-witness proposition should admit with restricted recursor");
    let hidden_rec = k.name_str(hidden, "rec");
    match k.environment().get(hidden_rec).expect("Hidden.rec") {
        Declaration::Recursor { uparams, .. } => assert!(uparams.is_empty()),
        _ => panic!("expected recursor"),
    }

    // Nested : Nat -> Prop | mk (n : Nat) : Nested (f n). Exact result-argument
    // equality is required: merely appearing below `f` is not recoverability.
    let f_name = k.name_str(anon, "f");
    let f_ty = k.pi(anon, nat_const, nat_const, BinderInfo::Default);
    k.add_declaration(Declaration::Axiom {
        name: f_name,
        uparams: vec![],
        ty: f_ty,
    })
    .unwrap();
    let f = k.const_(f_name, vec![]);
    let nested = k.name_str(anon, "Nested");
    let nested_const = k.const_(nested, vec![]);
    let nested_ty = k.pi(anon, nat_const, prop, BinderInfo::Default);
    let nested_mk = k.name_str(nested, "mk");
    let nested_mk_ty = {
        let n = k.bvar(0);
        let f_n = k.app(f, n);
        let result = k.app(nested_const, f_n);
        k.pi(anon, nat_const, result, BinderInfo::Default)
    };
    k.add_inductive(nested, &[], 0, nested_ty, &[(nested_mk, nested_mk_ty)])
        .expect("nested-index proposition should admit with restricted recursor");
    let nested_rec = k.name_str(nested, "rec");
    match k.environment().get(nested_rec).expect("Nested.rec") {
        Declaration::Recursor { uparams, .. } => assert!(uparams.is_empty()),
        _ => panic!("expected recursor"),
    }
}

/// A sole constructor whose fields are proofs remains a syntactic
/// subsingleton, including the direct-recursive proof-field backbone used by
/// accessibility-style predicates.
#[test]
fn prop_proof_fields_retain_large_elimination() {
    let mut k = Kernel::new();
    let anon = k.anon();
    let prop = k.sort_zero();
    let acc_like = k.name_str(anon, "AccLike");
    let acc_like_const = k.const_(acc_like, vec![]);
    let intro = k.name_str(acc_like, "intro");
    let intro_ty = k.pi(anon, acc_like_const, acc_like_const, BinderInfo::Default);
    k.add_inductive(acc_like, &[], 0, prop, &[(intro, intro_ty)])
        .expect("single-constructor recursive proof should admit");
    let rec = k.name_str(acc_like, "rec");
    match k.environment().get(rec).expect("AccLike.rec") {
        Declaration::Recursor { uparams, .. } => assert_eq!(uparams.len(), 1),
        _ => panic!("expected recursor"),
    }
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
    k.add_inductive(nat, &[], 0, s1, &[(zero, nat_const), (succ, succ_ty)])
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
    k.add_inductive(tree, &[], 0, s1, &[(leaf, tree_const), (node, node_ty)])
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

// ---------------------------------------------------------------------------
// Parametric inductives (slice 6): List, Option, Prod, Sum.
// ---------------------------------------------------------------------------

/// Declare `List.{u} (α : Sort u) : Sort u` with `nil : List α` and
/// `cons : α → List α → List α`. Returns `(list_name, rec_name, u_param,
/// [nil_name, cons_name])`.
fn declare_list(
    k: &mut Kernel,
) -> (
    crate::NameId,
    crate::NameId,
    crate::NameId,
    [crate::NameId; 2],
) {
    let anon = k.anon();
    let u = k.name_str(anon, "u");
    let u_lvl = k.level_param(u);
    let sort_u = k.sort(u_lvl);
    let list = k.name_str(anon, "List");

    // ty := Π (α : Sort u), Sort (u+1). The successor makes this family
    // provably non-Prop for every universe assignment, so its computational
    // recursor may eliminate into an arbitrary Sort.
    let alpha_name = k.name_str(anon, "α");
    let result_level = k.level_succ(u_lvl);
    let result_sort = k.sort(result_level);
    let ty = k.pi(alpha_name, sort_u, result_sort, BinderInfo::Default);

    // List α  (the inductive const applied to the param BVar 0, used in ctor
    // telescope bodies). In the constructor types we build below, `α` is BVar 0
    // at the parameter binder, then shifts under further field binders.
    let list_const = k.const_(list, vec![u_lvl]);

    let nil = k.name_str(anon, "nil");
    let cons = k.name_str(anon, "cons");

    // nil : Π (α : Sort u), List α   — `List α` = `List` applied to BVar 0.
    let nil_ty = {
        let a0 = k.bvar(0);
        let list_a = k.app(list_const, a0);
        k.pi(alpha_name, sort_u, list_a, BinderInfo::Default)
    };

    // cons : Π (α : Sort u) (a : α) (l : List α), List α.
    //   Under binders, de Bruijn indices (innermost = 0):
    //   - param α: BVar 2 at the result, BVar 1 in `l`'s type, BVar 0 in `a`'s type.
    //   Build inside-out: result `List α` with α = BVar 2; then bind `l : List α`
    //   with α = BVar 1; then bind `a : α` with α = BVar 0; then bind param α.
    let cons_ty = {
        let a2 = k.bvar(2);
        let list_a_res = k.app(list_const, a2); // List α (result)
        let a1 = k.bvar(1);
        let list_a_l = k.app(list_const, a1); // l : List α
        let l_name = k.name_str(anon, "l");
        let inner_l = k.pi(l_name, list_a_l, list_a_res, BinderInfo::Default);
        let a0 = k.bvar(0); // a : α
        let a_name = k.name_str(anon, "a");
        let inner_a = k.pi(a_name, a0, inner_l, BinderInfo::Default);
        k.pi(alpha_name, sort_u, inner_a, BinderInfo::Default)
    };

    k.add_inductive(list, &[u], 1, ty, &[(nil, nil_ty), (cons, cons_ty)])
        .expect("List should admit");
    let rec_name = k.name_str(list, "rec");
    (list, rec_name, u, [nil, cons])
}

/// List admits (parametric, num_params = 1); its recursor type infer-checks (the
/// param de Bruijn self-check); and the `cons` minor has the shape
/// `Π (a : α) (l : List α) (ih : motive l), motive (cons α a l)` — the parameter
/// `α` threaded into both the `motive` IH argument and the `cons` application.
#[test]
fn list_admits_and_cons_minor_threads_param() {
    let mut k = Kernel::new();
    let (list, rec_name, _u, [_nil, cons]) = declare_list(&mut k);

    // The recursor type infer-checks to a Sort (also done internally).
    let rec_decl = k.environment().get(rec_name).unwrap().clone();
    let rec_ty = rec_decl.ty();
    let inferred = k.infer(rec_ty).unwrap();
    assert!(matches!(k.expr_node(inferred), ExprNode::Sort(_)));

    // num_params is recorded as 1.
    match &rec_decl {
        Declaration::Recursor { num_params, .. } => assert_eq!(*num_params, 1),
        _ => panic!("expected recursor"),
    }

    // Telescope: Π (α) {motive} (m_nil) (m_cons) (major), motive major.
    // Walk: param α, motive, m_nil, then m_cons.
    let ExprNode::Pi(_, _alpha_ty, after_param, _) = k.expr_node(rec_ty).clone() else {
        panic!("rec ty should start with the param α Pi");
    };
    let ExprNode::Pi(_, _motive_ty, after_motive, _) = k.expr_node(after_param).clone() else {
        panic!("expected the motive Pi");
    };
    let ExprNode::Pi(_, _m_nil_ty, after_nil, _) = k.expr_node(after_motive).clone() else {
        panic!("expected the nil minor Pi");
    };
    let ExprNode::Pi(_, m_cons_ty, _after_cons, _) = k.expr_node(after_nil).clone() else {
        panic!("expected the cons minor Pi");
    };
    // m_cons_ty = Π (a : α) (l : List α) (ih : motive l), motive (cons α a l).
    // Count binders: 2 fields (a, l) + 1 IH = 3 leading Pis, then the body.
    let mut binders = Vec::new();
    let mut cur = m_cons_ty;
    while let ExprNode::Pi(_, dom, body, _) = k.expr_node(cur).clone() {
        binders.push(dom);
        cur = body;
    }
    assert_eq!(binders.len(), 3, "cons minor: 2 fields (a, l) + 1 IH");
    // The third binder (the IH) is a `motive _` application.
    assert!(
        matches!(k.expr_node(binders[2]), ExprNode::App(..)),
        "cons IH binder should be a `motive l` application"
    );
    // The minor result is `motive (cons α a l)` — head `cons`, applied to 3 args
    // (the threaded param α and the two fields a, l).
    let ExprNode::App(_m, cons_app) = k.expr_node(cur).clone() else {
        panic!("cons minor result should be `motive (cons α a l)`");
    };
    let (head, args) = {
        let mut h = cons_app;
        let mut a = Vec::new();
        while let ExprNode::App(f, x) = k.expr_node(h).clone() {
            a.push(x);
            h = f;
        }
        a.reverse();
        (h, a)
    };
    assert!(
        matches!(k.expr_node(head), ExprNode::Const(n, _) if *n == cons),
        "minor result head should be `cons`"
    );
    assert_eq!(args.len(), 3, "cons applied to the param α and two fields");
    let _ = list;
}

/// List ι backbone: `List.rec α C cnil ccons (nil α)` ι→ `cnil`, and
/// `List.rec α C cnil ccons (cons α a l)` ι→
/// `ccons a l (List.rec α C cnil ccons l)` (param α threaded into the recursive
/// call; the inner rec is left stuck by single-step whnf).
#[test]
fn list_rec_iota_backbone() {
    let mut k = Kernel::new();
    let (list, rec_name, u, [nil, cons]) = declare_list(&mut k);
    let u_lvl = k.level_param(u);

    let rec_decl = k.environment().get(rec_name).unwrap().clone();
    let v = match &rec_decl {
        Declaration::Recursor { uparams, .. } => uparams[0],
        _ => panic!(),
    };
    let v_lvl = k.level_param(v);

    // Concrete param α, motive C, minors cnil/ccons, and field fvars a, l.
    let alpha = k.fvar(1);
    let big_c = k.fvar(2);
    let cnil = k.fvar(3);
    let ccons = k.fvar(4);
    let a = k.fvar(5);
    let l = k.fvar(6);
    let _ = list;

    // nil α
    let nil_c = k.const_(nil, vec![u_lvl]);
    let nil_alpha = k.app(nil_c, alpha);

    // List.rec.{v,u} α C cnil ccons (nil α)  ι→  cnil
    let rec_const = k.const_(rec_name, vec![v_lvl, u_lvl]);
    let app_nil = {
        let e = k.app(rec_const, alpha);
        let e = k.app(e, big_c);
        let e = k.app(e, cnil);
        let e = k.app(e, ccons);
        k.app(e, nil_alpha)
    };
    assert_eq!(
        k.whnf(app_nil),
        cnil,
        "List.rec α C cnil ccons (nil α) ι→ cnil"
    );

    // cons α a l
    let cons_c = k.const_(cons, vec![u_lvl]);
    let cons_aal = {
        let e = k.app(cons_c, alpha);
        let e = k.app(e, a);
        k.app(e, l)
    };
    // List.rec α C cnil ccons (cons α a l)
    //   ι→  ccons a l (List.rec α C cnil ccons l)
    let rec_const2 = k.const_(rec_name, vec![v_lvl, u_lvl]);
    let app_cons = {
        let e = k.app(rec_const2, alpha);
        let e = k.app(e, big_c);
        let e = k.app(e, cnil);
        let e = k.app(e, ccons);
        k.app(e, cons_aal)
    };
    let inner_rec = {
        let rc = k.const_(rec_name, vec![v_lvl, u_lvl]);
        let e = k.app(rc, alpha);
        let e = k.app(e, big_c);
        let e = k.app(e, cnil);
        let e = k.app(e, ccons);
        k.app(e, l)
    };
    let expected = {
        let e = k.app(ccons, a);
        let e = k.app(e, l);
        k.app(e, inner_rec)
    };
    assert_eq!(
        k.whnf(app_cons),
        expected,
        "List.rec α C cnil ccons (cons α a l) ι→ ccons a l (List.rec … l)"
    );
}

/// End-to-end parametric computation: with `α := Nat`, `C := fun _ => Nat`,
/// `cnil := zero`, `ccons := fun (_a : Nat) (_l : List Nat) (ih : Nat) => succ ih`,
/// the length-like recursion over `cons Nat a (cons Nat b (nil Nat))` computes to
/// `succ (succ zero)` — multi-step parametric ι + β actually computes.
#[test]
fn list_rec_computes_length() {
    let mut k = Kernel::new();
    let (list, rec_name, u, [nil, cons]) = declare_list(&mut k);
    let u_lvl = k.level_param(u);
    let anon = k.anon();

    // A Nat to recurse into (independent inductive, num_params = 0).
    let (nat, _nat_rec, [zero, succ]) = declare_nat(&mut k);
    let nat_const = k.const_(nat, vec![]);
    let zero_c = k.const_(zero, vec![]);
    let succ_c = k.const_(succ, vec![]);

    // Elaborate List.rec at v := 1 (so C : List Nat → Sort 1 is well-typed) and
    // u := 1 (Nat : Sort 1).
    let lz = k.level_zero();
    let one = k.level_succ(lz);
    let v_lvl = one;
    // α := Nat lives at Sort 1, so instantiate the List family's `u` to 1 too.
    let u_arg = one;
    let _ = u_lvl;

    // C := fun (_ : List Nat) => Nat.   List Nat = List.{1} applied to Nat.
    let list_nat = {
        let list_c = k.const_(list, vec![u_arg]);
        k.app(list_c, nat_const)
    };
    let big_c = k.lam(anon, list_nat, nat_const, BinderInfo::Default);
    // cnil := zero.
    let cnil = zero_c;
    // ccons := fun (_a : Nat) (_l : List Nat) (ih : Nat) => succ ih  (ih = BVar 0).
    let ccons = {
        let v0 = k.bvar(0);
        let succ_ih = k.app(succ_c, v0);
        let inner_ih = k.lam(anon, nat_const, succ_ih, BinderInfo::Default);
        let inner_l = k.lam(anon, list_nat, inner_ih, BinderInfo::Default);
        k.lam(anon, nat_const, inner_l, BinderInfo::Default)
    };

    // The list `cons Nat a (cons Nat b (nil Nat))` with concrete element fvars.
    let a = k.fvar(100);
    let b = k.fvar(101);
    let nil_c = k.const_(nil, vec![u_arg]);
    let cons_c = k.const_(cons, vec![u_arg]);
    let nil_nat = k.app(nil_c, nat_const);
    let cons_b = {
        let e = k.app(cons_c, nat_const);
        let e = k.app(e, b);
        k.app(e, nil_nat)
    };
    let cons_a = {
        let e = k.app(cons_c, nat_const);
        let e = k.app(e, a);
        k.app(e, cons_b)
    };

    // List.rec.{1,1} Nat C cnil ccons (cons Nat a (cons Nat b (nil Nat))).
    let rec_const = k.const_(rec_name, vec![v_lvl, u_arg]);
    let app = {
        let e = k.app(rec_const, nat_const);
        let e = k.app(e, big_c);
        let e = k.app(e, cnil);
        let e = k.app(e, ccons);
        k.app(e, cons_a)
    };
    let computed = whnf_deep(&mut k, app);
    // Expected: succ (succ zero).
    let two = {
        let s1 = k.app(succ_c, zero_c);
        k.app(succ_c, s1)
    };
    assert_eq!(
        computed, two,
        "List length-by-recursion over [a, b] computes to 2"
    );
}

/// `Option.{u} (α : Sort u) : Sort (u+1)` with `none : Option α` and
/// `some : α → Option α` (1 param, non-recursive): admits, recursor self-checks,
/// and ι passes the field through (param threaded).
#[test]
fn option_admits_and_iota() {
    let mut k = Kernel::new();
    let anon = k.anon();
    let u = k.name_str(anon, "u");
    let u_lvl = k.level_param(u);
    let sort_u = k.sort(u_lvl);
    let result_level = k.level_succ(u_lvl);
    let result_sort = k.sort(result_level);
    let opt = k.name_str(anon, "Option");
    let alpha_name = k.name_str(anon, "α");
    let ty = k.pi(alpha_name, sort_u, result_sort, BinderInfo::Default);
    let opt_const = k.const_(opt, vec![u_lvl]);

    let none = k.name_str(anon, "none");
    let some = k.name_str(anon, "some");
    // none : Π (α : Sort u), Option α.
    let none_ty = {
        let a0 = k.bvar(0);
        let opt_a = k.app(opt_const, a0);
        k.pi(alpha_name, sort_u, opt_a, BinderInfo::Default)
    };
    // some : Π (α : Sort u) (a : α), Option α.
    let some_ty = {
        let a1 = k.bvar(1);
        let opt_a = k.app(opt_const, a1); // result, α = BVar 1
        let a0 = k.bvar(0); // a : α
        let a_name = k.name_str(anon, "a");
        let inner = k.pi(a_name, a0, opt_a, BinderInfo::Default);
        k.pi(alpha_name, sort_u, inner, BinderInfo::Default)
    };
    k.add_inductive(opt, &[u], 1, ty, &[(none, none_ty), (some, some_ty)])
        .expect("Option should admit");
    let rec_name = k.name_str(opt, "rec");

    let rec_decl = k.environment().get(rec_name).unwrap().clone();
    let rec_ty = rec_decl.ty();
    let inferred = k.infer(rec_ty).unwrap();
    assert!(matches!(k.expr_node(inferred), ExprNode::Sort(_)));
    let v = match &rec_decl {
        Declaration::Recursor { uparams, .. } => uparams[0],
        _ => panic!(),
    };
    let v_lvl = k.level_param(v);

    // ι: Option.rec α C cnone csome (some α x) ι→ csome x.
    let alpha = k.fvar(1);
    let big_c = k.fvar(2);
    let cnone = k.fvar(3);
    let csome = k.fvar(4);
    let x = k.fvar(5);
    let some_c = k.const_(some, vec![u_lvl]);
    let some_ax = {
        let e = k.app(some_c, alpha);
        k.app(e, x)
    };
    let rec_const = k.const_(rec_name, vec![v_lvl, u_lvl]);
    let app = {
        let e = k.app(rec_const, alpha);
        let e = k.app(e, big_c);
        let e = k.app(e, cnone);
        let e = k.app(e, csome);
        k.app(e, some_ax)
    };
    let expected = k.app(csome, x);
    assert_eq!(k.whnf(app), expected, "Option.rec … (some α x) ι→ csome x");
}

/// `Prod.{u,w} (α : Sort u) (β : Sort w) : Sort (max u w + 1)` with
/// `mk : α → β → Prod α β` (2 params, non-recursive): admits, recursor
/// self-checks, and ι passes both fields (both params threaded into the result).
#[test]
fn prod_two_params_admits_and_iota() {
    let mut k = Kernel::new();
    let anon = k.anon();
    let u = k.name_str(anon, "u");
    let w = k.name_str(anon, "w");
    let u_lvl = k.level_param(u);
    let w_lvl = k.level_param(w);
    let sort_u = k.sort(u_lvl);
    let sort_w = k.sort(w_lvl);
    let max_uw = k.level_max(u_lvl, w_lvl);
    let result_level = k.level_succ(max_uw);
    let sort_result = k.sort(result_level);
    let prod = k.name_str(anon, "Prod");
    let prod_const = k.const_(prod, vec![u_lvl, w_lvl]);

    // The successor keeps the family outside Prop for every assignment.
    // ty := Π (α : Sort u) (β : Sort w), Sort (max u w + 1).
    let alpha_name = k.name_str(anon, "α");
    let beta_name = k.name_str(anon, "β");
    let ty = {
        let inner = k.pi(beta_name, sort_w, sort_result, BinderInfo::Default);
        k.pi(alpha_name, sort_u, inner, BinderInfo::Default)
    };

    // mk : Π (α : Sort u) (β : Sort w) (a : α) (b : β), Prod α β.
    //   At the result, α = BVar 3, β = BVar 2; in `b`'s type β = BVar 1 (no, β is
    //   the inner param); let's compute carefully (innermost binder = 0):
    //   binders outer→inner: α(param), β(param), a(field), b(field).
    //   At result depth (under all 4): α = BVar 3, β = BVar 2.
    //   `b : β`  is under α, β, a  → β = BVar 1.
    //   `a : α`  is under α, β     → α = BVar 1.
    let mk = k.name_str(anon, "mk");
    let mk_ty = {
        let a3 = k.bvar(3);
        let b2 = k.bvar(2);
        let prod_ab = {
            let e = k.app(prod_const, a3);
            k.app(e, b2)
        }; // Prod α β (result)
        let b1 = k.bvar(1); // b : β
        let b_name = k.name_str(anon, "b");
        let inner_b = k.pi(b_name, b1, prod_ab, BinderInfo::Default);
        let a1 = k.bvar(1); // a : α  (under α, β)
        let a_name = k.name_str(anon, "a");
        let inner_a = k.pi(a_name, a1, inner_b, BinderInfo::Default);
        let inner_beta = k.pi(beta_name, sort_w, inner_a, BinderInfo::Default);
        k.pi(alpha_name, sort_u, inner_beta, BinderInfo::Default)
    };

    k.add_inductive(prod, &[u, w], 2, ty, &[(mk, mk_ty)])
        .expect("Prod should admit");
    let rec_name = k.name_str(prod, "rec");

    let rec_decl = k.environment().get(rec_name).unwrap().clone();
    let rec_ty = rec_decl.ty();
    let inferred = k.infer(rec_ty).unwrap();
    assert!(matches!(k.expr_node(inferred), ExprNode::Sort(_)));
    match &rec_decl {
        Declaration::Recursor { num_params, .. } => assert_eq!(*num_params, 2),
        _ => panic!(),
    }
    let v = match &rec_decl {
        Declaration::Recursor { uparams, .. } => uparams[0],
        _ => panic!(),
    };
    let v_lvl = k.level_param(v);

    // ι: Prod.rec α β C cmk (mk α β a b) ι→ cmk a b.
    let alpha = k.fvar(1);
    let beta = k.fvar(2);
    let big_c = k.fvar(3);
    let cmk = k.fvar(4);
    let a = k.fvar(5);
    let b = k.fvar(6);
    let mk_c = k.const_(mk, vec![u_lvl, w_lvl]);
    let mk_abab = {
        let e = k.app(mk_c, alpha);
        let e = k.app(e, beta);
        let e = k.app(e, a);
        k.app(e, b)
    };
    let rec_const = k.const_(rec_name, vec![v_lvl, u_lvl, w_lvl]);
    let app = {
        let e = k.app(rec_const, alpha);
        let e = k.app(e, beta);
        let e = k.app(e, big_c);
        let e = k.app(e, cmk);
        k.app(e, mk_abab)
    };
    let expected = {
        let e = k.app(cmk, a);
        k.app(e, b)
    };
    assert_eq!(
        k.whnf(app),
        expected,
        "Prod.rec α β C cmk (mk α β a b) ι→ cmk a b"
    );
}

/// `Sum.{u,w} (α : Sort u) (β : Sort w) : Sort (max u w + 1)` with
/// `inl : α → Sum α β` and `inr : β → Sum α β` (2 params, multiple ctors): admits,
/// recursor self-checks, and ι picks the right minor (param-threaded).
#[test]
#[allow(clippy::too_many_lines)]
fn sum_two_params_multiple_ctors() {
    let mut k = Kernel::new();
    let anon = k.anon();
    let u = k.name_str(anon, "u");
    let w = k.name_str(anon, "w");
    let u_lvl = k.level_param(u);
    let w_lvl = k.level_param(w);
    let sort_u = k.sort(u_lvl);
    let sort_w = k.sort(w_lvl);
    let max_uw = k.level_max(u_lvl, w_lvl);
    let result_level = k.level_succ(max_uw);
    let sort_result = k.sort(result_level);
    let sum = k.name_str(anon, "Sum");
    let sum_const = k.const_(sum, vec![u_lvl, w_lvl]);

    let alpha_name = k.name_str(anon, "α");
    let beta_name = k.name_str(anon, "β");
    let ty = {
        let inner = k.pi(beta_name, sort_w, sort_result, BinderInfo::Default);
        k.pi(alpha_name, sort_u, inner, BinderInfo::Default)
    };

    // inl : Π (α : Sort u) (β : Sort w) (a : α), Sum α β.
    //   binders: α, β, a; result Sum α β → α = BVar 2, β = BVar 1; `a : α` → α = BVar 1.
    let inl = k.name_str(anon, "inl");
    let inl_ty = {
        let a2 = k.bvar(2);
        let b1 = k.bvar(1);
        let sum_ab = {
            let e = k.app(sum_const, a2);
            k.app(e, b1)
        };
        let a1 = k.bvar(1); // a : α
        let a_name = k.name_str(anon, "a");
        let inner_a = k.pi(a_name, a1, sum_ab, BinderInfo::Default);
        let inner_beta = k.pi(beta_name, sort_w, inner_a, BinderInfo::Default);
        k.pi(alpha_name, sort_u, inner_beta, BinderInfo::Default)
    };
    // inr : Π (α : Sort u) (β : Sort w) (b : β), Sum α β.
    //   `b : β` is under α, β → β = BVar 0.
    let inr = k.name_str(anon, "inr");
    let inr_ty = {
        let a2 = k.bvar(2);
        let b1 = k.bvar(1);
        let sum_ab = {
            let e = k.app(sum_const, a2);
            k.app(e, b1)
        };
        let b0 = k.bvar(0); // b : β
        let b_name = k.name_str(anon, "b");
        let inner_b = k.pi(b_name, b0, sum_ab, BinderInfo::Default);
        let inner_beta = k.pi(beta_name, sort_w, inner_b, BinderInfo::Default);
        k.pi(alpha_name, sort_u, inner_beta, BinderInfo::Default)
    };

    k.add_inductive(sum, &[u, w], 2, ty, &[(inl, inl_ty), (inr, inr_ty)])
        .expect("Sum should admit");
    let rec_name = k.name_str(sum, "rec");

    let rec_decl = k.environment().get(rec_name).unwrap().clone();
    let rec_ty = rec_decl.ty();
    let inferred = k.infer(rec_ty).unwrap();
    assert!(matches!(k.expr_node(inferred), ExprNode::Sort(_)));
    let v = match &rec_decl {
        Declaration::Recursor { uparams, .. } => uparams[0],
        _ => panic!(),
    };
    let v_lvl = k.level_param(v);

    let alpha = k.fvar(1);
    let beta = k.fvar(2);
    let big_c = k.fvar(3);
    let cinl = k.fvar(4);
    let cinr = k.fvar(5);
    let x = k.fvar(6);

    // ι: Sum.rec α β C cinl cinr (inl α β x) ι→ cinl x.
    let inl_c = k.const_(inl, vec![u_lvl, w_lvl]);
    let inl_abx = {
        let e = k.app(inl_c, alpha);
        let e = k.app(e, beta);
        k.app(e, x)
    };
    let rec_const = k.const_(rec_name, vec![v_lvl, u_lvl, w_lvl]);
    let app_inl = {
        let e = k.app(rec_const, alpha);
        let e = k.app(e, beta);
        let e = k.app(e, big_c);
        let e = k.app(e, cinl);
        let e = k.app(e, cinr);
        k.app(e, inl_abx)
    };
    let expected_inl = k.app(cinl, x);
    assert_eq!(
        k.whnf(app_inl),
        expected_inl,
        "Sum.rec … (inl α β x) ι→ cinl x"
    );

    // ι: Sum.rec α β C cinl cinr (inr α β x) ι→ cinr x.
    let inr_c = k.const_(inr, vec![u_lvl, w_lvl]);
    let inr_abx = {
        let e = k.app(inr_c, alpha);
        let e = k.app(e, beta);
        k.app(e, x)
    };
    let rec_const2 = k.const_(rec_name, vec![v_lvl, u_lvl, w_lvl]);
    let app_inr = {
        let e = k.app(rec_const2, alpha);
        let e = k.app(e, beta);
        let e = k.app(e, big_c);
        let e = k.app(e, cinl);
        let e = k.app(e, cinr);
        k.app(e, inr_abx)
    };
    let expected_inr = k.app(cinr, x);
    assert_eq!(
        k.whnf(app_inr),
        expected_inr,
        "Sum.rec … (inr α β x) ι→ cinr x"
    );
}

// ---------------------------------------------------------------------------
// Indexed inductives (slice 7): Eq is the backbone.
// ---------------------------------------------------------------------------

/// Declare `Eq.{u} {α : Sort u} (a : α) : α → Prop` (params: α, a; 1 index of
/// type α) with `refl : Eq α a a`. Returns `(eq_name, rec_name, u, refl_name)`.
fn declare_eq(k: &mut Kernel) -> (crate::NameId, crate::NameId, crate::NameId, crate::NameId) {
    let anon = k.anon();
    let u = k.name_str(anon, "u");
    let u_lvl = k.level_param(u);
    let sort_u = k.sort(u_lvl);
    let eq = k.name_str(anon, "Eq");
    let eq_const = k.const_(eq, vec![u_lvl]);

    // ty := Π (α : Sort u) (a : α) (b : α), Prop.
    //   binders outer→inner: α, a, b. The index `b : α` is under α, a → α = BVar 1.
    //   `a : α` is under α → α = BVar 0.
    let alpha_name = k.name_str(anon, "α");
    let a_name = k.name_str(anon, "a");
    let b_name = k.name_str(anon, "b");
    let prop = k.sort_zero();
    let ty = {
        let a1 = k.bvar(1); // α at the b binder
        let inner_b = k.pi(b_name, a1, prop, BinderInfo::Default);
        let a0 = k.bvar(0); // α at the a binder
        let inner_a = k.pi(a_name, a0, inner_b, BinderInfo::Default);
        k.pi(alpha_name, sort_u, inner_a, BinderInfo::Default)
    };

    // refl : Π (α : Sort u) (a : α), Eq α a a.
    //   result `Eq α a a` under binders α, a → α = BVar 1, a = BVar 0.
    let refl = k.name_str(anon, "refl");
    let refl_ty = {
        let a1 = k.bvar(1); // α
        let a0 = k.bvar(0); // a
        let eq_app = {
            let e = k.app(eq_const, a1);
            let e = k.app(e, a0);
            k.app(e, a0)
        };
        let inner_a = k.pi(a_name, a0, eq_app, BinderInfo::Default);
        k.pi(alpha_name, sort_u, inner_a, BinderInfo::Default)
    };

    k.add_inductive(eq, &[u], 2, ty, &[(refl, refl_ty)])
        .expect("Eq should admit");
    let rec_name = k.name_str(eq, "rec");
    (eq, rec_name, u, refl)
}

/// `Eq` admits (2 params, 1 index, non-recursive); `Eq.rec`'s generated type
/// infer-checks (the dependent-motive self-check) and records `num_indices = 1`.
#[test]
fn eq_admits_and_recursor_self_checks() {
    let mut k = Kernel::new();
    let (_eq, rec_name, _u, _refl) = declare_eq(&mut k);

    let rec_decl = k.environment().get(rec_name).unwrap().clone();
    // The dependent recursor type infer-checks to a Sort (the crux self-check).
    let rec_ty = rec_decl.ty();
    let inferred = k.infer(rec_ty).unwrap();
    assert!(matches!(k.expr_node(inferred), ExprNode::Sort(_)));
    match &rec_decl {
        Declaration::Recursor {
            num_params,
            num_indices,
            num_minors,
            ..
        } => {
            assert_eq!(*num_params, 2, "Eq has 2 params (α, a)");
            assert_eq!(*num_indices, 1, "Eq has 1 index");
            assert_eq!(*num_minors, 1, "Eq has one ctor (refl)");
        }
        _ => panic!("expected recursor"),
    }
}

/// The generated `Eq.rec` type matches the known shape
/// `Π (α) (a) {motive : Π (b:α), Eq a b → Sort v} (refl_case : motive a refl)
///   (b:α) (h : Eq a b), motive b h`. We walk the telescope: 2 params, then the
/// motive, then 1 minor, then 1 index (b), then the major (h). The motive's own
/// type is a `Π (b:α), Eq a b → Sort v`; the minor's result applies the motive
/// to `a` (the ctor's index expr) and `refl α a` — the crux.
#[test]
fn eq_recursor_structure() {
    let mut k = Kernel::new();
    let (eq, rec_name, _u, refl) = declare_eq(&mut k);

    let rec_ty = k.environment().get(rec_name).unwrap().ty();
    // Walk: α, a (params), motive, refl_case (minor), b (index), h (major).
    let ExprNode::Pi(_, _alpha, after_alpha, _) = k.expr_node(rec_ty).clone() else {
        panic!("rec ty should bind param α");
    };
    let ExprNode::Pi(_, _a, after_a, _) = k.expr_node(after_alpha).clone() else {
        panic!("rec ty should bind param a");
    };
    let ExprNode::Pi(_, motive_ty, after_motive, _) = k.expr_node(after_a).clone() else {
        panic!("rec ty should bind the motive");
    };
    // motive_ty = Π (b : α), Π (_ : Eq a b), Sort v — two leading Pis.
    let ExprNode::Pi(_, _b_dom, motive_body, _) = k.expr_node(motive_ty).clone() else {
        panic!("motive type should bind the index b");
    };
    let ExprNode::Pi(_, eq_dom, motive_codom, _) = k.expr_node(motive_body).clone() else {
        panic!("motive type should bind `Eq a b`");
    };
    // The motive's second domain is `Eq a b` (head `Eq`).
    let (eq_head, eq_args) = {
        let mut h = eq_dom;
        let mut a = Vec::new();
        while let ExprNode::App(f, x) = k.expr_node(h).clone() {
            a.push(x);
            h = f;
        }
        a.reverse();
        (h, a)
    };
    assert!(
        matches!(k.expr_node(eq_head), ExprNode::Const(n, _) if *n == eq),
        "motive's second domain head should be `Eq`"
    );
    assert_eq!(eq_args.len(), 3, "Eq applied to α, a, b");
    assert!(
        matches!(k.expr_node(motive_codom), ExprNode::Sort(_)),
        "motive codomain is a Sort"
    );

    // The minor (refl_case) result is `motive a (refl α a)` — head is the motive
    // applied to the ctor's index expr `a` and `refl α a`.
    let ExprNode::Pi(_, refl_case_ty, after_minor, _) = k.expr_node(after_motive).clone() else {
        panic!("rec ty should bind the refl_case minor");
    };
    // refl_case_ty is directly `motive <a> (refl α a)` (refl has no fields/IHs).
    let (minor_head, minor_args) = {
        let mut h = refl_case_ty;
        let mut a = Vec::new();
        while let ExprNode::App(f, x) = k.expr_node(h).clone() {
            a.push(x);
            h = f;
        }
        a.reverse();
        (h, a)
    };
    // Head is the motive (a BVar referencing the motive binder), applied to two
    // args: the index expr and the `refl α a` application.
    assert_eq!(
        minor_args.len(),
        2,
        "minor applies the motive to the ctor index expr and `refl α a`"
    );
    let _ = minor_head;
    // The second minor arg is `refl α a` (head `refl`).
    let (refl_head, refl_args) = {
        let mut h = minor_args[1];
        let mut a = Vec::new();
        while let ExprNode::App(f, x) = k.expr_node(h).clone() {
            a.push(x);
            h = f;
        }
        a.reverse();
        (h, a)
    };
    assert!(
        matches!(k.expr_node(refl_head), ExprNode::Const(n, _) if *n == refl),
        "minor's constructor application head should be `refl`"
    );
    assert_eq!(refl_args.len(), 2, "refl applied to the params α, a");

    // After the minor: the index b (a Pi), then the major h.
    let ExprNode::Pi(_, _b_index, after_index, _) = k.expr_node(after_minor).clone() else {
        panic!("rec ty should bind the index b after the minor");
    };
    let ExprNode::Pi(_, major_ty, _result, _) = k.expr_node(after_index).clone() else {
        panic!("rec ty should bind the major h");
    };
    // The major's type is `Eq α a b` (head `Eq`).
    let (mh, _ma) = k.unfold_apps(major_ty);
    assert!(
        matches!(k.expr_node(mh), ExprNode::Const(n, _) if *n == eq),
        "major type head should be `Eq`"
    );
}

/// `Eq.rec` ι backbone: `Eq.rec α a motive refl_case a (refl α a)` ι→ `refl_case`
/// (the index arg before the major is dropped; the constructor major fires the
/// rule).
#[test]
fn eq_rec_iota_on_refl() {
    let mut k = Kernel::new();
    let (eq, rec_name, u, refl) = declare_eq(&mut k);
    let u_lvl = k.level_param(u);

    let rec_decl = k.environment().get(rec_name).unwrap().clone();
    let v = match &rec_decl {
        Declaration::Recursor { uparams, .. } => uparams[0],
        _ => panic!(),
    };
    let v_lvl = k.level_param(v);
    let _ = eq;

    // Concrete params α, a; motive; refl_case; and the index arg + major.
    let alpha = k.fvar(1);
    let a = k.fvar(2);
    let motive = k.fvar(3);
    let refl_case = k.fvar(4);

    // refl α a (the major; also the index arg `a` before it).
    let refl_c = k.const_(refl, vec![u_lvl]);
    let refl_aa = {
        let e = k.app(refl_c, alpha);
        k.app(e, a)
    };

    // Eq.rec.{v,u} α a motive refl_case a (refl α a)  ι→  refl_case.
    let rec_const = k.const_(rec_name, vec![v_lvl, u_lvl]);
    let app = {
        let e = k.app(rec_const, alpha);
        let e = k.app(e, a);
        let e = k.app(e, motive);
        let e = k.app(e, refl_case);
        let e = k.app(e, a); // the index arg b := a
        k.app(e, refl_aa) // the major
    };
    assert_eq!(
        k.whnf(app),
        refl_case,
        "Eq.rec α a motive refl_case a (refl α a) ι→ refl_case"
    );
}

/// Eq end-to-end: a symmetry-like transport. With the motive
/// `motive := fun (b : α) (_ : Eq α a b) => Eq α b a`, `Eq.rec`'s refl_case has
/// type `motive a (refl α a) = Eq α a a`; supplying `refl α a` for it and
/// applying to `a` and `refl α a` ι-reduces to that refl_case — the transport
/// computes on `refl`.
#[test]
fn eq_rec_transport_computes() {
    let mut k = Kernel::new();
    let anon = k.anon();
    let (eq, rec_name, u, refl) = declare_eq(&mut k);
    let u_lvl = k.level_param(u);

    let rec_decl = k.environment().get(rec_name).unwrap().clone();
    let v = match &rec_decl {
        Declaration::Recursor { uparams, .. } => uparams[0],
        _ => panic!(),
    };
    let v_lvl = k.level_param(v);

    // A concrete carrier A : Sort 1 (axiom) and a, the basepoint.
    let one = {
        let z = k.level_zero();
        k.level_succ(z)
    };
    let s1 = k.sort(one);
    let a_carrier = k.name_str(anon, "A");
    k.add_declaration(Declaration::Axiom {
        name: a_carrier,
        uparams: vec![],
        ty: s1,
    })
    .unwrap();
    let big_a = k.const_(a_carrier, vec![]);
    let a_pt = k.name_str(anon, "apt");
    k.add_declaration(Declaration::Axiom {
        name: a_pt,
        uparams: vec![],
        ty: big_a,
    })
    .unwrap();
    let a = k.const_(a_pt, vec![]);

    // motive := fun (b : A) (_ : Eq A a b) => Eq A b a   (symmetry's target).
    //   Under binders b, h (innermost = 0): b = BVar 1.
    let eq_c = k.const_(eq, vec![u_lvl]);
    let motive = {
        let b1 = k.bvar(1); // b
        // Eq A b a
        let eq_ba = {
            let e = k.app(eq_c, big_a);
            let e = k.app(e, b1);
            k.app(e, a)
        };
        // Eq A a b  (the h domain): b = BVar 0 under the b binder only.
        let b0 = k.bvar(0);
        let eq_ab = {
            let e = k.app(eq_c, big_a);
            let e = k.app(e, a);
            k.app(e, b0)
        };
        let h_name = k.name_str(anon, "h");
        let inner_h = k.lam(h_name, eq_ab, eq_ba, BinderInfo::Default);
        let b_name = k.name_str(anon, "b");
        k.lam(b_name, big_a, inner_h, BinderInfo::Default)
    };

    // refl_case := refl A a  : Eq A a a  (= motive a (refl A a) after β).
    let refl_c = k.const_(refl, vec![u_lvl]);
    let refl_aa = {
        let e = k.app(refl_c, big_a);
        k.app(e, a)
    };

    // Eq.rec.{1,1} A a motive (refl A a) a (refl A a)  ι→  refl A a.
    // Elaborate at v := 1 (motive returns a Sort 0 Prop, so v = 1 suffices for
    // the recursor's elimination level here we just need ι to fire).
    let rec_const = k.const_(rec_name, vec![v_lvl, u_lvl]);
    let app = {
        let e = k.app(rec_const, big_a);
        let e = k.app(e, a);
        let e = k.app(e, motive);
        let e = k.app(e, refl_aa);
        let e = k.app(e, a); // index arg b := a
        k.app(e, refl_aa) // major
    };
    assert_eq!(
        k.whnf(app),
        refl_aa,
        "transport ι-fires on refl and yields the refl_case (refl A a)"
    );
}

/// A direct recursive field on an indexed family receives an IH at the field's
/// own index, and its computation rule recursively evaluates that field.
#[test]
fn recursive_indexed_field_admits_and_computes() {
    let mut k = Kernel::new();
    let anon = k.anon();
    let (nat, _nat_rec, [_zero, succ]) = declare_nat(&mut k);
    let nat_const = k.const_(nat, vec![]);

    let z = k.level_zero();
    let one = k.level_succ(z);
    let s1 = k.sort(one);
    let vname = k.name_str(anon, "V");
    let v_const = k.const_(vname, vec![]);

    // ty := Π (_ : Nat), Sort 1   (0 params, 1 index of type Nat).
    let ty = k.pi(anon, nat_const, s1, BinderInfo::Default);

    // cons : Π (n : Nat) (_ : V n), V (succ n).
    //   binders n, (rec field). result `V (succ n)`: n = BVar 1; field `V n`:
    //   n = BVar 0.
    let cons = k.name_str(anon, "cons");
    let succ_c = k.const_(succ, vec![]);
    let cons_ty = {
        let n1 = k.bvar(1);
        let succ_n = k.app(succ_c, n1);
        let v_succ_n = k.app(v_const, succ_n); // V (succ n)  (result)
        let n0 = k.bvar(0);
        let v_n = k.app(v_const, n0); // V n  (recursive field)
        let inner = k.pi(anon, v_n, v_succ_n, BinderInfo::Default);
        let n_name = k.name_str(anon, "n");
        k.pi(n_name, nat_const, inner, BinderInfo::Default)
    };
    k.add_inductive(vname, &[], 0, ty, &[(cons, cons_ty)])
        .expect("recursive indexed family should admit");
    let rec_name = k.name_str(vname, "rec");
    let rec_decl = k.environment().get(rec_name).unwrap().clone();
    let rec_level = match rec_decl {
        Declaration::Recursor {
            ref uparams,
            num_motives,
            num_minors,
            num_indices,
            ..
        } => {
            assert_eq!((num_motives, num_minors, num_indices), (1, 1, 1));
            k.level_param(uparams[0])
        }
        _ => panic!("V.rec should be a recursor"),
    };

    let motive = k.fvar(100);
    let minor = k.fvar(101);
    let n = k.fvar(102);
    let tail = k.fvar(103);
    let cons_c = k.const_(cons, vec![]);
    let major = {
        let app = k.app(cons_c, n);
        k.app(app, tail)
    };
    let succ_n = k.app(succ_c, n);
    let rec_c = k.const_(rec_name, vec![rec_level]);
    let application = {
        let app = k.app(rec_c, motive);
        let app = k.app(app, minor);
        let app = k.app(app, succ_n);
        k.app(app, major)
    };
    let recursive_call = {
        let rec_c = k.const_(rec_name, vec![rec_level]);
        let app = k.app(rec_c, motive);
        let app = k.app(app, minor);
        let app = k.app(app, n);
        k.app(app, tail)
    };
    let expected = {
        let app = k.app(minor, n);
        let app = k.app(app, tail);
        k.app(app, recursive_call)
    };
    assert_eq!(k.whnf(application), expected);
}

/// A simple **indexed enum** with two constructors landing at different index
/// values: `Parity : Bool → Sort 1` (0 params, 1 index of type Bool) with
/// `even : Parity tt` and `odd : Parity ff`. Admits; the recursor self-checks;
/// ι picks the right minor by the major's index.
#[test]
fn indexed_enum_two_ctors() {
    let mut k = Kernel::new();
    // A Bool to index over.
    let (_bool, _bool_rec, bctors) = declare_enum(&mut k, "Bool2", &["tt", "ff"]);
    let tt = k.const_(bctors[0], vec![]);
    let ff = k.const_(bctors[1], vec![]);
    let bool2 = {
        let anon = k.anon();
        k.name_str(anon, "Bool2")
    };
    let bool2_const = k.const_(bool2, vec![]);

    let anon = k.anon();
    let z = k.level_zero();
    let one = k.level_succ(z);
    let s1 = k.sort(one);
    let parity = k.name_str(anon, "Parity");
    let parity_const = k.const_(parity, vec![]);

    // ty := Π (_ : Bool2), Sort 1   (1 index of type Bool2).
    let ty = k.pi(anon, bool2_const, s1, BinderInfo::Default);

    // even : Parity tt   (index expr tt);  odd : Parity ff   (index expr ff).
    let even = k.name_str(anon, "even");
    let odd = k.name_str(anon, "odd");
    let even_ty = k.app(parity_const, tt);
    let odd_ty = k.app(parity_const, ff);

    k.add_inductive(parity, &[], 0, ty, &[(even, even_ty), (odd, odd_ty)])
        .expect("Parity should admit");
    let rec_name = k.name_str(parity, "rec");

    let rec_decl = k.environment().get(rec_name).unwrap().clone();
    let rec_ty = rec_decl.ty();
    let inferred = k.infer(rec_ty).unwrap();
    assert!(matches!(k.expr_node(inferred), ExprNode::Sort(_)));
    let v = match &rec_decl {
        Declaration::Recursor {
            uparams,
            num_indices,
            ..
        } => {
            assert_eq!(*num_indices, 1);
            uparams[0]
        }
        _ => panic!(),
    };
    let v_lvl = k.level_param(v);

    // ι: Parity.rec motive m_even m_odd tt even ι→ m_even.
    let motive = k.fvar(1);
    let m_even = k.fvar(2);
    let m_odd = k.fvar(3);
    let even_c = k.const_(even, vec![]);
    let odd_c = k.const_(odd, vec![]);

    let rec_const = k.const_(rec_name, vec![v_lvl]);
    let app_even = {
        let e = k.app(rec_const, motive);
        let e = k.app(e, m_even);
        let e = k.app(e, m_odd);
        let e = k.app(e, tt); // index arg
        k.app(e, even_c) // major
    };
    assert_eq!(k.whnf(app_even), m_even, "Parity.rec … tt even ι→ m_even");

    let rec_const2 = k.const_(rec_name, vec![v_lvl]);
    let app_odd = {
        let e = k.app(rec_const2, motive);
        let e = k.app(e, m_even);
        let e = k.app(e, m_odd);
        let e = k.app(e, ff); // index arg
        k.app(e, odd_c) // major
    };
    assert_eq!(k.whnf(app_odd), m_odd, "Parity.rec … ff odd ι→ m_odd");
}

/// Reject: a constructor whose result is the inductive applied to the **wrong**
/// parameter. For `Box.{u} (α : Sort u)` with `mk : Π (α : Sort u) (β : Sort u),
/// Box β` (the result uses the *second* bound `β`, not the parameter `α`), the
/// result is not `Box α` ⇒ `ConstructorResultMismatch` (the wrong-args path).
#[test]
fn reject_ctor_wrong_param() {
    let mut k = Kernel::new();
    let anon = k.anon();
    let u = k.name_str(anon, "u");
    let u_lvl = k.level_param(u);
    let sort_u = k.sort(u_lvl);
    let boxn = k.name_str(anon, "Box");
    let box_const = k.const_(boxn, vec![u_lvl]);
    let alpha_name = k.name_str(anon, "α");
    let ty = k.pi(alpha_name, sort_u, sort_u, BinderInfo::Default);

    // mk : Π (α : Sort u) (β : Sort u), Box β  — result applies Box to BVar 0
    // (β), but the single parameter is α (BVar 1). The check opens ONE param (α)
    // then a field (β : Sort u); the result `Box β` ≠ `Box α`.
    let mk = k.name_str(anon, "mk");
    let beta_name = k.name_str(anon, "β");
    let mk_ty = {
        let b0 = k.bvar(0); // β
        let box_beta = k.app(box_const, b0);
        let inner = k.pi(beta_name, sort_u, box_beta, BinderInfo::Default);
        k.pi(alpha_name, sort_u, inner, BinderInfo::Default)
    };
    let err = k
        .add_inductive(boxn, &[u], 1, ty, &[(mk, mk_ty)])
        .unwrap_err();
    assert!(
        matches!(err, KernelError::ConstructorResultMismatch { .. }),
        "got {err:?}"
    );
    assert!(!k.environment().contains(boxn));
    assert!(!k.environment().contains(mk));
}

/// A higher-order recursive field receives a telescope-shaped IH, and its
/// computation rule supplies a lambda that recursively evaluates every field
/// application.
#[test]
fn parametric_higher_order_field_admits_and_computes() {
    let mut k = Kernel::new();
    let anon = k.anon();
    let u = k.name_str(anon, "u");
    let u_lvl = k.level_param(u);
    let sort_u = k.sort(u_lvl);
    let refl = k.name_str(anon, "PRefl");
    let refl_const = k.const_(refl, vec![u_lvl]);
    let alpha_name = k.name_str(anon, "α");
    let ty = k.pi(alpha_name, sort_u, sort_u, BinderInfo::Default);

    // node : Π (α : Sort u) (f : (α → PRefl α)), PRefl α — the field `f` is a Pi
    // ending in `PRefl α` (reflexive). Build inside-out under binders α, f.
    let node = k.name_str(anon, "node");
    let node_ty = {
        let a1 = k.bvar(1); // α at result
        let refl_a_res = k.app(refl_const, a1);
        // field f : (α → PRefl α). Under the param binder only (before f),
        // α = BVar 0. The arrow's body PRefl α has α = BVar 1 (under the arrow's
        // own binder).
        let a0_dom = k.bvar(0); // α (arrow domain)
        let a1_body = k.bvar(1); // α (arrow body, under arrow binder)
        let refl_a_body = k.app(refl_const, a1_body);
        let f_ty = k.pi(anon, a0_dom, refl_a_body, BinderInfo::Default);
        let f_name = k.name_str(anon, "f");
        let inner = k.pi(f_name, f_ty, refl_a_res, BinderInfo::Default);
        k.pi(alpha_name, sort_u, inner, BinderInfo::Default)
    };
    k.add_inductive(refl, &[u], 1, ty, &[(node, node_ty)])
        .expect("higher-order recursive family should admit");
    let rec_name = k.name_str(refl, "rec");
    let rec_decl = k.environment().get(rec_name).unwrap().clone();
    let family_level = match rec_decl {
        Declaration::Recursor {
            ref uparams,
            num_motives,
            num_minors,
            num_indices,
            ..
        } => {
            assert_eq!((num_motives, num_minors, num_indices), (1, 1, 0));
            assert_eq!(
                uparams.len(),
                1,
                "potentially-Prop family eliminates to Prop"
            );
            k.level_param(uparams[0])
        }
        _ => panic!("PRefl.rec should be a recursor"),
    };

    let alpha = k.fvar(100);
    let motive = k.fvar(101);
    let minor = k.fvar(102);
    let field = k.fvar(103);
    let node_c = k.const_(node, vec![family_level]);
    let major = {
        let app = k.app(node_c, alpha);
        k.app(app, field)
    };
    let rec_c = k.const_(rec_name, vec![family_level]);
    let application = {
        let app = k.app(rec_c, alpha);
        let app = k.app(app, motive);
        let app = k.app(app, minor);
        k.app(app, major)
    };
    let ih = {
        let x = k.bvar(0);
        let field_x = k.app(field, x);
        let rec_c = k.const_(rec_name, vec![family_level]);
        let app = k.app(rec_c, alpha);
        let app = k.app(app, motive);
        let app = k.app(app, minor);
        let body = k.app(app, field_x);
        k.lam(anon, alpha, body, BinderInfo::Default)
    };
    let expected = {
        let app = k.app(minor, field);
        k.app(app, ih)
    };
    assert_eq!(k.whnf(application), expected);
}

/// Determinism for a parametric inductive: building `List` twice yields the same
/// recursor type id.
#[test]
fn determinism_parametric_inductive() {
    fn build() -> usize {
        let mut k = Kernel::new();
        let (_list, rec_name, _u, _ctors) = declare_list(&mut k);
        k.environment().get(rec_name).unwrap().ty().index()
    }
    assert_eq!(build(), build());
}
