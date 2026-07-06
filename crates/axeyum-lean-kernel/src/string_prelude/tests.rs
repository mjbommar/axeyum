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
    let logic = build_logic_prelude(&mut k);
    let sp = build_string_prelude(&mut k, logic, num_chars);
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
fn append_is_opaque_binary_function() {
    // append typechecks as Str → Str → Str and does not reduce (opaque axiom):
    // `append nil nil` infers to `Str` and is NOT def_eq to `nil`.
    let (mut k, sp) = setup(1);
    let nil = sp.nil(&mut k);
    let nil2 = sp.nil(&mut k);
    let ap = sp.append_app(&mut k, nil, nil2);
    let inferred = k.infer(ap).expect("append nil nil : Str");
    let str_const = sp.str_const(&mut k);
    assert!(k.def_eq(inferred, str_const), "append nil nil : Str");
    let nil3 = sp.nil(&mut k);
    assert!(
        !k.def_eq(ap, nil3),
        "append is opaque — does not compute to nil"
    );
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
