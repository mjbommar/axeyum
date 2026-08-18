//! Tests for the free-monoid string prelude: admission through the trusted
//! gates, and the ι-computations the word-clash reconstruction relies on
//! (`head`/`tail` selectors and the `Char` is-tester all kernel-compute on
//! concrete constructors).

use crate::prelude::build_logic_prelude;
use crate::string_prelude::build_string_prelude;
use crate::{BinderInfo, Kernel};

/// A kernel with the logical + string prelude over a `num_chars` alphabet.
fn setup(num_chars: usize) -> (Kernel, crate::StringPrelude) {
    let mut k = Kernel::new();
    let logic = build_logic_prelude(&mut k).expect("logic prelude must build");
    let sp = build_string_prelude(&mut k, logic, num_chars).expect("string prelude must build");
    (k, sp)
}

#[test]
fn prelude_admits_and_registers() {
    let (k, sp) = setup(3);
    // The inductives, constructors, recursors, and append are in the environment.
    for n in [
        sp.char_ind,
        sp.char_rec,
        sp.str_ind,
        sp.str_nil,
        sp.str_cons,
        sp.str_rec,
        sp.append,
    ] {
        assert!(
            k.environment().contains(n),
            "declaration must be registered"
        );
    }
    assert_eq!(sp.char_ctors.len(), 3);
    for &c in &sp.char_ctors {
        assert!(k.environment().contains(c));
    }
}

#[test]
fn empty_alphabet_admits() {
    // A pure equality/disequality reconstruction needs no concrete character.
    let (k, sp) = setup(0);
    assert!(sp.char_ctors.is_empty());
    assert!(k.environment().contains(sp.str_ind));
}

#[test]
fn tail_selector_iota_reduces() {
    let (mut k, sp) = setup(2);
    let c0 = sp.char(&mut k, 0);
    let nil = sp.nil(&mut k);
    let list = sp.cons(&mut k, c0, nil); // cons c0 nil
    let tail = sp.tail_fn(&mut k);
    let applied = k.app(tail, list); // tail (cons c0 nil)
    let nil2 = sp.nil(&mut k);
    assert!(k.def_eq(applied, nil2), "tail (cons c0 nil) ↝ nil");
}

#[test]
fn head_selector_iota_reduces() {
    let (mut k, sp) = setup(2);
    let c1 = sp.char(&mut k, 1);
    let nil = sp.nil(&mut k);
    let list = sp.cons(&mut k, c1, nil);
    let head = sp.head_fn(&mut k);
    let applied = k.app(head, list); // head (cons c1 nil)
    let c1b = sp.char(&mut k, 1);
    assert!(k.def_eq(applied, c1b), "head (cons c1 nil) ↝ c1");
}

#[test]
fn projection_composition_reaches_second_char() {
    // head (tail (cons c0 (cons c1 nil))) ↝ c1.
    let (mut k, sp) = setup(2);
    let c0 = sp.char(&mut k, 0);
    let c1 = sp.char(&mut k, 1);
    let nil = sp.nil(&mut k);
    let inner = sp.cons(&mut k, c1, nil);
    let list = sp.cons(&mut k, c0, inner);
    let tail = sp.tail_fn(&mut k);
    let head = sp.head_fn(&mut k);
    let t = k.app(tail, list);
    let h = k.app(head, t);
    let c1b = sp.char(&mut k, 1);
    assert!(k.def_eq(h, c1b));
}

#[test]
fn is_tester_iota_folds_to_bool() {
    let (mut k, sp) = setup(3);
    let is_c1 = sp.char_is_tester(&mut k, 1);
    let c1 = sp.char(&mut k, 1);
    let applied_true = k.app(is_c1, c1); // is_c1 c1 ↝ true
    let btrue = k.const_(sp.logic.bool_true, vec![]);
    assert!(k.def_eq(applied_true, btrue), "is_c1 c1 ↝ true");

    let is_c1b = sp.char_is_tester(&mut k, 1);
    let c2 = sp.char(&mut k, 2);
    let applied_false = k.app(is_c1b, c2); // is_c1 c2 ↝ false
    let bfalse = k.const_(sp.logic.bool_false, vec![]);
    assert!(k.def_eq(applied_false, bfalse), "is_c1 c2 ↝ false");
}

#[test]
fn append_is_a_checked_definition_not_an_axiom() {
    // `append` used to be the last `Declaration::Axiom` outside the `real`
    // prelude. It is now a `Definition` with a `Str.rec` body, so this test dies
    // the moment anyone re-admits it as an assumption.
    let (k, sp) = setup(1);
    match k.environment().get(sp.append) {
        Some(crate::Declaration::Definition { .. }) => {}
        other => panic!("append must be a checked Definition, got {other:?}"),
    }
}

#[test]
fn string_prelude_trusted_surface_is_empty() {
    // The ratchet behind `string: axiom=0` in `nat_axiom_inventory`. It counts
    // the same three kinds over the same environment (logic + string), so this
    // fails in-tree the moment any assumption is reintroduced — the example is a
    // separate binary and a lane can land a prelude change without running it.
    let (k, _sp) = setup(3);
    let trusted: Vec<String> = k
        .environment()
        .iter()
        .filter_map(|(_, declaration)| match declaration {
            crate::Declaration::Axiom { name, .. }
            | crate::Declaration::Opaque { name, .. }
            | crate::Declaration::Quotient { name, .. } => Some(k.display_name(*name).to_string()),
            _ => None,
        })
        .collect();
    assert!(
        trusted.is_empty(),
        "the string prelude must admit nothing without a checked body; found {trusted:?}"
    );
}

#[test]
fn append_iota_computes_on_concrete_strings() {
    // append [c0,c1] [c1,c0] ↝ [c0,c1,c1,c0] — the whole point of defining it.
    let (mut k, sp) = setup(2);
    let a = str_of(&mut k, &sp, &[0, 1]);
    let b = str_of(&mut k, &sp, &[1, 0]);
    let ap = sp.append_app(&mut k, a, b);
    let want = str_of(&mut k, &sp, &[0, 1, 1, 0]);
    assert!(k.def_eq(ap, want), "append [0,1] [1,0] ↝ [0,1,1,0]");

    // …and it still infers at the declared type.
    let inferred = k.infer(ap).expect("append a b : Str");
    let str_const = sp.str_const(&mut k);
    assert!(k.def_eq(inferred, str_const), "append a b : Str");

    // A wrong answer is still rejected (def_eq is not vacuously true here).
    let wrong = str_of(&mut k, &sp, &[0, 1, 0, 1]);
    assert!(
        !k.def_eq(ap, wrong),
        "append must not equate distinct words"
    );
}

#[test]
fn append_is_stuck_on_an_opaque_argument() {
    // The property the word-clash reconstruction relies on: with an opaque `Str`
    // variable on the left, `append` has no ι-rule to fire, so it behaves exactly
    // like the uninterpreted binary symbol it used to be. Defining it did not
    // make an open term collapse to something.
    let (mut k, sp) = setup(2);
    let v = opaque_str(&mut k, &sp, "v_stuck");
    let b = str_of(&mut k, &sp, &[1]);
    let ap = sp.append_app(&mut k, v, b);
    assert!(!k.def_eq(ap, v), "append v [c1] is not v");
    assert!(!k.def_eq(ap, b), "append v [c1] is not [c1]");
    let inferred = k.infer(ap).expect("append v b : Str");
    let str_const = sp.str_const(&mut k);
    assert!(k.def_eq(inferred, str_const));
}

/// Each proved law, checked by **re-deriving its statement** and demanding the
/// kernel's stored theorem type match — so deleting a law, weakening it, or
/// re-admitting it as an `Axiom` all fail here.
#[test]
fn monoid_laws_are_declared_theorems_with_the_stated_types() {
    let (mut k, sp) = setup(2);
    let str_ty = sp.str_const(&mut k);
    let char_ty = k.const_(sp.char_ind, vec![]);
    let anon = k.anon();

    // nil_append : ∀ (b : Str), Eq Str (append nil b) b
    {
        let b = k.bvar(0);
        let nil = sp.nil(&mut k);
        let lhs = sp.append_app(&mut k, nil, b);
        let body = mk_eq(&mut k, &sp, str_ty, 1, lhs, b);
        let want = k.pi(anon, str_ty, body, BinderInfo::Default);
        assert_theorem_type(&mut k, sp.nil_append, want, "nil_append");
    }

    // cons_append : ∀ (h : Char) (t b : Str),
    //                 Eq Str (append (cons h t) b) (cons h (append t b))
    {
        let h = k.bvar(2);
        let t = k.bvar(1);
        let b = k.bvar(0);
        let consed = sp.cons(&mut k, h, t);
        let lhs = sp.append_app(&mut k, consed, b);
        let tail_append = sp.append_app(&mut k, t, b);
        let rhs = sp.cons(&mut k, h, tail_append);
        let body = mk_eq(&mut k, &sp, str_ty, 1, lhs, rhs);
        let over_b = k.pi(anon, str_ty, body, BinderInfo::Default);
        let over_t = k.pi(anon, str_ty, over_b, BinderInfo::Default);
        let want = k.pi(anon, char_ty, over_t, BinderInfo::Default);
        assert_theorem_type(&mut k, sp.cons_append, want, "cons_append");
    }

    // append_nil : ∀ (a : Str), Eq Str (append a nil) a
    {
        let a = k.bvar(0);
        let nil = sp.nil(&mut k);
        let lhs = sp.append_app(&mut k, a, nil);
        let body = mk_eq(&mut k, &sp, str_ty, 1, lhs, a);
        let want = k.pi(anon, str_ty, body, BinderInfo::Default);
        assert_theorem_type(&mut k, sp.append_nil, want, "append_nil");
    }

    // append_assoc : ∀ (a b c : Str),
    //                  Eq Str (append (append a b) c) (append a (append b c))
    {
        let a = k.bvar(2);
        let b = k.bvar(1);
        let c = k.bvar(0);
        let left = {
            let inner = sp.append_app(&mut k, a, b);
            sp.append_app(&mut k, inner, c)
        };
        let right = {
            let inner = sp.append_app(&mut k, b, c);
            sp.append_app(&mut k, a, inner)
        };
        let body = mk_eq(&mut k, &sp, str_ty, 1, left, right);
        let over_c = k.pi(anon, str_ty, body, BinderInfo::Default);
        let over_b = k.pi(anon, str_ty, over_c, BinderInfo::Default);
        let want = k.pi(anon, str_ty, over_b, BinderInfo::Default);
        assert_theorem_type(&mut k, sp.append_assoc, want, "append_assoc");
    }
}

/// `decl` must be a `Declaration::Theorem` (a checked proof body, not an
/// assumption) whose stored type is definitionally the expected statement.
fn assert_theorem_type(k: &mut Kernel, name: crate::NameId, want: crate::ExprId, label: &str) {
    let got = match k.environment().get(name) {
        Some(crate::Declaration::Theorem { ty, .. }) => *ty,
        other => panic!("{label} must be a checked Theorem, got {other:?}"),
    };
    assert!(
        k.def_eq(got, want),
        "{label} type mismatch:\n  stored : {}\n  wanted : {}",
        k.render_lean(got),
        k.render_lean(want)
    );
}

/// The laws are usable as lemmas: instantiate `append_assoc` at three opaque
/// `Str` variables and let the kernel infer the resulting proposition. This is
/// what a length/cancellation reconstruction would do, and it fails if the
/// theorem is missing or its telescope order changes.
#[test]
fn append_assoc_instantiates_at_opaque_words() {
    let (mut k, sp) = setup(2);
    let x = opaque_str(&mut k, &sp, "w_x");
    let y = opaque_str(&mut k, &sp, "w_y");
    let z = opaque_str(&mut k, &sp, "w_z");
    let lemma = k.const_(sp.append_assoc, vec![]);
    let applied = {
        let e = k.app(lemma, x);
        let e = k.app(e, y);
        k.app(e, z)
    };
    let inferred = k.infer(applied).expect("append_assoc x y z infers");
    let str_ty = sp.str_const(&mut k);
    let want = {
        let left = {
            let inner = sp.append_app(&mut k, x, y);
            sp.append_app(&mut k, inner, z)
        };
        let right = {
            let inner = sp.append_app(&mut k, y, z);
            sp.append_app(&mut k, x, inner)
        };
        mk_eq(&mut k, &sp, str_ty, 1, left, right)
    };
    assert!(
        k.def_eq(inferred, want),
        "append_assoc x y z : (x ++ y) ++ z = x ++ (y ++ z), got {}",
        k.render_lean(inferred)
    );
}

/// `append_nil` is the half that is *not* definitional: on an opaque word the
/// kernel cannot reduce `append v nil` to `v`, so the theorem is doing real
/// work rather than restating `Eq.refl`.
#[test]
fn append_nil_is_not_definitional_on_an_opaque_word() {
    let (mut k, sp) = setup(2);
    let v = opaque_str(&mut k, &sp, "w_v");
    let nil = sp.nil(&mut k);
    let lhs = sp.append_app(&mut k, v, nil);
    assert!(
        !k.def_eq(lhs, v),
        "append v nil is NOT definitionally v — the induction is load-bearing"
    );
    let lemma = k.const_(sp.append_nil, vec![]);
    let applied = k.app(lemma, v);
    let inferred = k.infer(applied).expect("append_nil v infers");
    let str_ty = sp.str_const(&mut k);
    let want = mk_eq(&mut k, &sp, str_ty, 1, lhs, v);
    assert!(k.def_eq(inferred, want), "append_nil v : append v nil = v");
}

/// The load-bearing clash computation, end to end at the prelude level: from
/// `h : Eq Str (cons c0 nil) (cons c1 nil)` (two distinct one-character strings),
/// build a `False` proof that the kernel `infer`s to `False` — via a single
/// `congrArg` of `g = is_c0 ∘ head` and the `Bool.true ≠ Bool.false` discriminator.
#[test]
fn distinct_singletons_refute_to_false() {
    let (mut k, sp) = setup(2);
    let anon = k.anon();
    let str_const = sp.str_const(&mut k);
    let bool_const = k.const_(sp.logic.bool_, vec![]);

    // The two concrete members and the hypothesis h : Eq Str a b.
    let a = {
        let c0 = sp.char(&mut k, 0);
        let nil = sp.nil(&mut k);
        sp.cons(&mut k, c0, nil)
    };
    let b = {
        let c1 = sp.char(&mut k, 1);
        let nil = sp.nil(&mut k);
        sp.cons(&mut k, c1, nil)
    };
    let h_name = {
        let n = k.name_str(anon, "h_clash");
        let one = level(&mut k, 1);
        let eq = k.const_(sp.logic.eq, vec![one]);
        let ty = {
            let e = k.app(eq, str_const);
            let e = k.app(e, a);
            k.app(e, b)
        };
        k.add_declaration(crate::Declaration::Axiom {
            name: n,
            uparams: vec![],
            ty,
        })
        .expect("clash hypothesis admits");
        n
    };
    let h = k.const_(h_name, vec![]);

    // g : Str → Bool := λ s, is_c0 (head s).  g a ↝ true, g b ↝ false.
    let head = sp.head_fn(&mut k);
    let is_c0 = sp.char_is_tester(&mut k, 0);
    let g = {
        let s = k.bvar(0);
        let hs = k.app(head, s);
        let body = k.app(is_c0, hs);
        k.lam(anon, str_const, body, BinderInfo::Default)
    };
    let g_a = k.app(g, a); // ↝ true
    let g_b = k.app(g, b); // ↝ false

    // symm h : Eq Str b a, then congrArg g : Eq Bool (g b) (g a) = Eq Bool lhs true.
    let symm = eq_symm(&mut k, &sp, str_const, 1, a, b, h);
    let congr = congr_arg_str_bool(&mut k, &sp, str_const, bool_const, 1, g, b, a, symm);
    // build_bool_true_ne_false(lhs = g_b, congr : Eq Bool g_b true) → False.
    let false_proof = bool_true_ne_false(&mut k, &sp, bool_const, 1, g_b, congr);
    let _ = g_a;

    let inferred = k.infer(false_proof).expect("False proof infers");
    let false_const = k.const_(sp.logic.false_, vec![]);
    assert!(
        k.def_eq(inferred, false_const),
        "clash refutation infers to False"
    );
}

// ---- minimal Eq/congr/discriminator helpers for the end-to-end test ----------

fn mk_eq(
    k: &mut Kernel,
    sp: &crate::StringPrelude,
    ty: crate::ExprId,
    u: usize,
    x: crate::ExprId,
    y: crate::ExprId,
) -> crate::ExprId {
    let lvl = level(k, u);
    let eq = k.const_(sp.logic.eq, vec![lvl]);
    let e = k.app(eq, ty);
    let e = k.app(e, x);
    k.app(e, y)
}

fn level(k: &mut Kernel, n: usize) -> crate::LevelId {
    let mut l = k.level_zero();
    for _ in 0..n {
        l = k.level_succ(l);
    }
    l
}

fn eq_refl(
    k: &mut Kernel,
    sp: &crate::StringPrelude,
    ty: crate::ExprId,
    u: usize,
    a: crate::ExprId,
) -> crate::ExprId {
    let lvl = level(k, u);
    let refl = k.const_(sp.logic.eq_refl, vec![lvl]);
    let e = k.app(refl, ty);
    k.app(e, a)
}

#[allow(clippy::too_many_arguments)]
fn eq_symm(
    k: &mut Kernel,
    sp: &crate::StringPrelude,
    ty: crate::ExprId,
    u: usize,
    a: crate::ExprId,
    b: crate::ExprId,
    h: crate::ExprId,
) -> crate::ExprId {
    let anon = k.anon();
    // motive := λ (x : ty) (_ : Eq ty a x), Eq ty x a.
    let motive = {
        let x1 = k.bvar(1);
        let eq_x_a = mk_eq(k, sp, ty, u, x1, a);
        let x0 = k.bvar(0);
        let eq_a_x = mk_eq(k, sp, ty, u, a, x0);
        let inner = k.lam(anon, eq_a_x, eq_x_a, BinderInfo::Default);
        k.lam(anon, ty, inner, BinderInfo::Default)
    };
    let refl_case = eq_refl(k, sp, ty, u, a);
    eq_rec(k, sp, ty, u, a, motive, refl_case, b, h)
}

#[allow(clippy::too_many_arguments)]
fn eq_rec(
    k: &mut Kernel,
    sp: &crate::StringPrelude,
    ty: crate::ExprId,
    u: usize,
    p: crate::ExprId,
    motive: crate::ExprId,
    refl_case: crate::ExprId,
    q: crate::ExprId,
    h: crate::ExprId,
) -> crate::ExprId {
    let z = k.level_zero();
    let ulvl = level(k, u);
    let rec = k.const_(sp.logic.eq_rec, vec![z, ulvl]);
    let e = k.app(rec, ty);
    let e = k.app(e, p);
    let e = k.app(e, motive);
    let e = k.app(e, refl_case);
    let e = k.app(e, q);
    k.app(e, h)
}

#[allow(clippy::too_many_arguments)]
fn congr_arg_str_bool(
    k: &mut Kernel,
    sp: &crate::StringPrelude,
    str_ty: crate::ExprId,
    bool_ty: crate::ExprId,
    u: usize,
    f: crate::ExprId,
    x: crate::ExprId,
    y: crate::ExprId,
    h: crate::ExprId,
) -> crate::ExprId {
    let anon = k.anon();
    let fx = k.app(f, x);
    // motive := λ (z : Str) (_ : Eq Str x z), Eq Bool (f x) (f z).
    let motive = {
        let z1 = k.bvar(1);
        let fz = k.app(f, z1);
        let eq_fx_fz = mk_eq(k, sp, bool_ty, u, fx, fz);
        let z0 = k.bvar(0);
        let eq_x_z = mk_eq(k, sp, str_ty, u, x, z0);
        let inner = k.lam(anon, eq_x_z, eq_fx_fz, BinderInfo::Default);
        k.lam(anon, str_ty, inner, BinderInfo::Default)
    };
    let refl_case = eq_refl(k, sp, bool_ty, u, fx);
    eq_rec(k, sp, str_ty, u, x, motive, refl_case, y, h)
}

fn bool_true_ne_false(
    k: &mut Kernel,
    sp: &crate::StringPrelude,
    bool_ty: crate::ExprId,
    u: usize,
    lhs: crate::ExprId,
    h: crate::ExprId,
) -> crate::ExprId {
    let anon = k.anon();
    let prop = k.sort_zero();
    let true_const = k.const_(sp.logic.true_, vec![]);
    let false_const = k.const_(sp.logic.false_, vec![]);
    let z = k.level_zero();
    let one = k.level_succ(z);
    let rec = k.const_(sp.logic.bool_rec, vec![one]);
    let motive = k.lam(anon, bool_ty, prop, BinderInfo::Default);
    // discr := λ b, Bool.rec (λ _ => Prop) False True b.  discr true ↝ False, discr false ↝ True.
    let discr = {
        let e = k.app(rec, motive);
        let e = k.app(e, false_const); // minor for Bool.true
        let e = k.app(e, true_const); // minor for Bool.false
        let b = k.bvar(0);
        let body = k.app(e, b);
        k.lam(anon, bool_ty, body, BinderInfo::Default)
    };
    let bool_true = k.const_(sp.logic.bool_true, vec![]);
    let transport_motive = {
        let x = k.bvar(1);
        let discr_x = k.app(discr, x);
        let x0 = k.bvar(0);
        let eq_lhs_x = mk_eq(k, sp, bool_ty, u, lhs, x0);
        let inner = k.lam(anon, eq_lhs_x, discr_x, BinderInfo::Default);
        k.lam(anon, bool_ty, inner, BinderInfo::Default)
    };
    let refl_case = k.const_(sp.logic.true_intro, vec![]);
    let rec_eq = k.const_(sp.logic.eq_rec, vec![z, one]);
    let e = k.app(rec_eq, bool_ty);
    let e = k.app(e, lhs);
    let e = k.app(e, transport_motive);
    let e = k.app(e, refl_case);
    let e = k.app(e, bool_true);
    k.app(e, h)
}

// ---------------------------------------------------------------------------
// Lexicographic-order builders (`char_eq_fn` / `char_lt_fn` / `lex_cmp_fn`).
// ---------------------------------------------------------------------------

/// Declare a fresh opaque `Str` constant (a variable tail), returning its term.
fn opaque_str(k: &mut Kernel, sp: &crate::StringPrelude, tag: &str) -> crate::ExprId {
    let anon = k.anon();
    let name = k.name_str(anon, tag);
    let ty = sp.str_const(k);
    k.add_declaration(crate::Declaration::Axiom {
        name,
        uparams: vec![],
        ty,
    })
    .expect("opaque Str axiom admits");
    k.const_(name, vec![])
}

/// A concrete `Str` from alphabet indices, as a flat `cons`-chain.
fn str_of(k: &mut Kernel, sp: &crate::StringPrelude, idxs: &[usize]) -> crate::ExprId {
    let mut acc = sp.nil(k);
    for &i in idxs.iter().rev() {
        let c = sp.char(k, i);
        acc = sp.cons(k, c, acc);
    }
    acc
}

#[test]
fn char_eq_table_iota_folds() {
    let (mut k, sp) = setup(3);
    let eq = sp.char_eq_fn(&mut k);
    let btrue = k.const_(sp.logic.bool_true, vec![]);
    let bfalse = k.const_(sp.logic.bool_false, vec![]);
    for i in 0..3 {
        for j in 0..3 {
            let a = sp.char(&mut k, i);
            let b = sp.char(&mut k, j);
            let app = {
                let e = k.app(eq, a);
                k.app(e, b)
            };
            let want = if i == j { btrue } else { bfalse };
            assert!(k.def_eq(app, want), "char_eq c{i} c{j} ↝ {}", i == j);
        }
    }
}

#[test]
fn char_lt_table_iota_folds() {
    let (mut k, sp) = setup(4);
    let lt = sp.char_lt_fn(&mut k);
    let btrue = k.const_(sp.logic.bool_true, vec![]);
    let bfalse = k.const_(sp.logic.bool_false, vec![]);
    for i in 0..4 {
        for j in 0..4 {
            let a = sp.char(&mut k, i);
            let b = sp.char(&mut k, j);
            let app = {
                let e = k.app(lt, a);
                k.app(e, b)
            };
            let want = if i < j { btrue } else { bfalse };
            assert!(k.def_eq(app, want), "char_lt c{i} c{j} ↝ {}", i < j);
        }
    }
}

#[test]
fn lex_le_iota_reduces_on_concrete_strings() {
    let (mut k, sp) = setup(4);
    let le = sp.lex_cmp_fn(&mut k, false);
    let btrue = k.const_(sp.logic.bool_true, vec![]);
    let bfalse = k.const_(sp.logic.bool_false, vec![]);

    // First chars differ: [2,..] vs [1,..] ⇒ le false (2 > 1 at pos 0).
    let a = str_of(&mut k, &sp, &[2, 0]);
    let b = str_of(&mut k, &sp, &[1, 3]);
    let app = {
        let e = k.app(le, a);
        k.app(e, b)
    };
    assert!(k.def_eq(app, bfalse), "le [2,0] [1,3] ↝ false");

    // Equal first char, second decides: [1,2] vs [1,0] ⇒ false (2 > 0 at pos 1).
    let a = str_of(&mut k, &sp, &[1, 2]);
    let b = str_of(&mut k, &sp, &[1, 0]);
    let app = {
        let e = k.app(le, a);
        k.app(e, b)
    };
    assert!(k.def_eq(app, bfalse), "le [1,2] [1,0] ↝ false");

    // Smaller-left: [0,3] vs [1,0] ⇒ true (0 < 1 at pos 0).
    let a = str_of(&mut k, &sp, &[0, 3]);
    let b = str_of(&mut k, &sp, &[1, 0]);
    let app = {
        let e = k.app(le, a);
        k.app(e, b)
    };
    assert!(k.def_eq(app, btrue), "le [0,3] [1,0] ↝ true");
}

#[test]
fn lex_lt_iota_reduces_at_clash_ignoring_opaque_tail() {
    // The load-bearing property for a first-clash refutation: `lt A B` ι-reduces to
    // `false` when A > B at the first differing DETERMINED position, even though the
    // tails past that position are opaque `Str` variables (never forced).
    let (mut k, sp) = setup(3);
    let lt = sp.lex_cmp_fn(&mut k, true);
    let bfalse = k.const_(sp.logic.bool_false, vec![]);

    // A = cons c2 (cons c1 tailA),  B = cons c2 (cons c0 tailB): equal at pos0,
    // clash at pos1 (1 > 0), tails opaque.
    let tail_a = opaque_str(&mut k, &sp, "tailA");
    let tail_b = opaque_str(&mut k, &sp, "tailB");
    let a = {
        let c1 = sp.char(&mut k, 1);
        let inner = sp.cons(&mut k, c1, tail_a);
        let c2 = sp.char(&mut k, 2);
        sp.cons(&mut k, c2, inner)
    };
    let b = {
        let c0 = sp.char(&mut k, 0);
        let inner = sp.cons(&mut k, c0, tail_b);
        let c2 = sp.char(&mut k, 2);
        sp.cons(&mut k, c2, inner)
    };
    let app = {
        let e = k.app(lt, a);
        k.app(e, b)
    };
    assert!(
        k.def_eq(app, bfalse),
        "lt (c2 c1 …) (c2 c0 …) ↝ false regardless of opaque tails"
    );
}
