//! **P0 soundness exploit**: derive `False` through the trusted admission gate.
//!
//! This is the escalation of `prop_large_elim_soundness.rs`. That test shows the
//! two ingredients are live; this one uses them to get `add_declaration` — the
//! trusted gate (`tc.rs:565`) — to accept `theorem bad : False`.
//!
//! The recipe is the textbook one for impredicative `Prop` + proof irrelevance +
//! unrestricted large elimination:
//!
//! 1. `Two : Prop` with two constructors `a`, `b`. Proof irrelevance
//!    (`tc.rs:735`) gives `a === b`.
//! 2. Large elimination (`inductive.rs:37` — "the motive is always allowed to
//!    eliminate into an arbitrary `Sort v`") builds `f : Two -> Answer` with
//!    `f a === yes` and `f b === no` by iota.
//! 3. `h : Eq Two a b := Eq.refl Two a` typechecks, *because* `a === b`.
//! 4. Transport along `h` with motive `fun idx _ => D (f idx)`, where
//!    `D yes === True` and `D no === False`, turns `trivial : True` into a
//!    proof of `False`.
//!
//! NOTE: this is NOT a Lean-compatibility complaint. It is an internal
//! inconsistency in the type theory this kernel actually implements: proof
//! irrelevance plus impredicative `Prop` plus unrestricted large elimination is
//! inconsistent in *any* such theory. Lean restricts large elimination to
//! subsingletons (at most one constructor, all fields proofs) precisely to
//! block this.
//!
//! EXPECTED once fixed: `add_inductive` for `Two` should still succeed, but the
//! generated `Two.rec` must be restricted to eliminate only into `Prop`, so that
//! step (2) fails to typecheck. This test should then be inverted into a
//! negative test asserting that rejection.

use axeyum_lean_kernel::{BinderInfo, Declaration, ExprId, Kernel, NameId};

/// Declare a nullary-constructor inductive at sort level `level`
/// (`0` = `Prop`, `1` = `Type`).
fn declare_enum_at(
    k: &mut Kernel,
    name: &str,
    ctor_strs: &[&str],
    level: usize,
) -> (NameId, Vec<NameId>) {
    let anon = k.anon();
    let ind_name = k.name_str(anon, name);
    let mut lvl = k.level_zero();
    for _ in 0..level {
        lvl = k.level_succ(lvl);
    }
    let ty = k.sort(lvl);
    let ind_const = k.const_(ind_name, vec![]);
    let ctor_names: Vec<_> = ctor_strs.iter().map(|s| k.name_str(anon, *s)).collect();
    let ctors: Vec<_> = ctor_names.iter().map(|&cn| (cn, ind_const)).collect();
    k.add_inductive(ind_name, &[], 0, ty, &ctors)
        .unwrap_or_else(|e| panic!("{name} should admit: {e:?}"));
    (ind_name, ctor_names)
}

/// `Eq.{u} : Pi (a : Sort u) (x : a), a -> Prop` with `Eq.refl : Pi a x, Eq a x x`.
/// 2 params, 1 index — the backbone case `inductive.rs:12` names as its target.
fn declare_eq(k: &mut Kernel) -> (NameId, NameId, NameId) {
    let anon = k.anon();
    let eq_name = k.name_str(anon, "Eq");
    let u = k.name_str(anon, "u");
    let u_lvl = k.level_param(u);
    let sort_u = k.sort(u_lvl);
    let prop = k.sort_zero();

    // Eq : Pi (α : Sort u) (x : α), α -> Prop
    let b0 = k.bvar(0);
    let b1 = k.bvar(1);
    let inner = k.pi(anon, b1, prop, BinderInfo::Default);
    let mid = k.pi(anon, b0, inner, BinderInfo::Default);
    let eq_ty = k.pi(anon, sort_u, mid, BinderInfo::Default);

    // Eq.refl : Pi (α : Sort u) (x : α), Eq.{u} α x x
    let refl_name = k.name_str(eq_name, "refl");
    let eq_const = k.const_(eq_name, vec![u_lvl]);
    let b0 = k.bvar(0);
    let b1 = k.bvar(1);
    let app1 = k.app(eq_const, b1);
    let app2 = k.app(app1, b0);
    let app3 = k.app(app2, b0);
    let b0b = k.bvar(0);
    let refl_mid = k.pi(anon, b0b, app3, BinderInfo::Default);
    let refl_ty = k.pi(anon, sort_u, refl_mid, BinderInfo::Default);

    k.add_inductive(eq_name, &[u], 2, eq_ty, &[(refl_name, refl_ty)])
        .expect("Eq should admit");
    let eq_rec = k.name_str(eq_name, "rec");
    (eq_name, refl_name, eq_rec)
}

#[test]
#[ignore = "P0 REPRODUCTION: this test FAILS because the kernel is unsound. \
            Ignored only so it does not break other lanes' `just check` in this \
            shared checkout — NOT because it is unimportant. See \
            docs/prover-track/research/09-P0-kernel-unsoundness.md. Run with \
            `cargo test -p axeyum-lean-kernel --test prop_large_elim_derives_false \
            -- --ignored --nocapture`. Un-ignore and invert once the subsingleton \
            restriction lands."]
fn prop_large_elimination_derives_false() {
    let mut k = Kernel::new();
    let anon = k.anon();
    let zero = k.level_zero();
    let one = k.level_succ(zero);

    let (eq_name, refl_name, eq_rec) = declare_eq(&mut k);
    let (two_name, two_c) = declare_enum_at(&mut k, "Two", &["a", "b"], 0); // Prop
    let (answer_name, ans_c) = declare_enum_at(&mut k, "Answer", &["yes", "no"], 1); // Type
    let (true_name, true_c) = declare_enum_at(&mut k, "True", &["trivial"], 0); // Prop
    let (false_name, _) = declare_enum_at(&mut k, "False", &[], 0); // Prop, no ctors

    let a = k.const_(two_c[0], vec![]);
    let b = k.const_(two_c[1], vec![]);
    let yes = k.const_(ans_c[0], vec![]);
    let no = k.const_(ans_c[1], vec![]);
    let two_const = k.const_(two_name, vec![]);
    let answer_const = k.const_(answer_name, vec![]);
    let true_const = k.const_(true_name, vec![]);
    let false_const = k.const_(false_name, vec![]);
    let trivial = k.const_(true_c[0], vec![]);
    let prop = k.sort_zero();

    // f : Two -> Answer  :=  fun t => Two.rec.{1} (fun _ => Answer) yes no t
    // THE ILLEGAL STEP: a two-constructor Prop eliminating into Sort 1.
    let two_rec = k.name_str(two_name, "rec");
    let two_rec_c = k.const_(two_rec, vec![one]);
    let f_motive = k.lam(anon, two_const, answer_const, BinderInfo::Default);
    let r = k.app(two_rec_c, f_motive);
    let r = k.app(r, yes);
    let r = k.app(r, no);
    let b0 = k.bvar(0);
    let r_applied = k.app(r, b0);
    let f = k.lam(anon, two_const, r_applied, BinderInfo::Default);

    // D : Answer -> Prop := fun x => Answer.rec.{1} (fun _ => Prop) True False x
    // Answer is a Type, so this elimination is entirely legitimate.
    let ans_rec = k.name_str(answer_name, "rec");
    let ans_rec_c = k.const_(ans_rec, vec![one]);
    let d_motive = k.lam(anon, answer_const, prop, BinderInfo::Default);
    let d = k.app(ans_rec_c, d_motive);
    let d = k.app(d, true_const);
    let d = k.app(d, false_const);
    let b0 = k.bvar(0);
    let d_applied = k.app(d, b0);
    let big_d = k.lam(anon, answer_const, d_applied, BinderInfo::Default);

    let apply = |k: &mut Kernel, f: ExprId, x: ExprId| k.app(f, x);

    // h : Eq.{0} Two a b  :=  Eq.refl.{0} Two a
    // Typechecks ONLY because proof irrelevance gives a === b.
    let refl_c = k.const_(refl_name, vec![zero]);
    let h_val = apply(&mut k, refl_c, two_const);
    let h_val = apply(&mut k, h_val, a);
    let eq_c = k.const_(eq_name, vec![zero]);
    let h_ty = apply(&mut k, eq_c, two_const);
    let h_ty = apply(&mut k, h_ty, a);
    let h_ty = apply(&mut k, h_ty, b);

    let inferred = k.infer(h_val).expect("Eq.refl Two a should infer");
    println!("inferred type of `Eq.refl Two a` vs ascribed `Eq Two a b`:");
    println!("  def_eq = {}", k.def_eq(inferred, h_ty));
    assert!(
        k.def_eq(inferred, h_ty),
        "proof irrelevance should let `Eq.refl Two a : Eq Two a b`"
    );

    // motive := fun (idx : Two) (_ : Eq.{0} Two a idx) => D (f idx)
    let eq_c2 = k.const_(eq_name, vec![zero]);
    let e1 = k.app(eq_c2, two_const);
    let e2 = k.app(e1, a);
    let b0 = k.bvar(0);
    let eq_ty_idx = k.app(e2, b0);
    let b1 = k.bvar(1);
    let f_idx = k.app(f, b1);
    let d_f_idx = k.app(big_d, f_idx);
    let inner_lam = k.lam(anon, eq_ty_idx, d_f_idx, BinderInfo::Default);
    let motive = k.lam(anon, two_const, inner_lam, BinderInfo::Default);

    // Eq.rec.{u:=0, v:=0} Two a motive (trivial : D (f a) === True) b h : D (f b) === False
    let eq_rec_c = k.const_(eq_rec, vec![zero, zero]);
    let t = apply(&mut k, eq_rec_c, two_const);
    let t = apply(&mut k, t, a);
    let t = apply(&mut k, t, motive);
    let t = apply(&mut k, t, trivial);
    let t = apply(&mut k, t, b);
    let absurd = apply(&mut k, t, h_val);

    match k.infer(absurd) {
        Ok(ty) => {
            let w = k.whnf(ty);
            println!("inferred type of the transported term: {:?}", k.expr_node(w));
            println!("  def_eq(.., False) = {}", k.def_eq(w, false_const));
        }
        Err(e) => println!("infer failed: {e:?}"),
    }

    // THE GATE. If this admits, the kernel has accepted a proof of `False`.
    let bad = k.name_str(anon, "bad");
    let res = k.add_declaration(Declaration::Theorem {
        name: bad,
        uparams: vec![],
        ty: false_const,
        value: absurd,
    });
    println!("add_declaration(theorem bad : False) => {res:?}");
    assert!(
        res.is_ok(),
        "EXPLOIT FAILED (good news!) — gate rejected: {res:?}"
    );
    panic!("UNSOUND: the trusted admission gate accepted `theorem bad : False`");
}
