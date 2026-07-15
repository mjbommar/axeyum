//! TEMPORARY scratch probe - delete after use.
use axeyum_lean_kernel::{BinderInfo, Kernel};

#[test]
fn probe_prop_large_elimination() {
    let mut k = Kernel::new();
    let anon = k.anon();

    // inductive Bool2 : Prop | tt : Bool2 | ff : Bool2
    let b2 = k.name_str(anon, "Bool2");
    let prop = k.sort_zero();
    let b2_const = k.const_(b2, vec![]);
    let tt = k.name_str(anon, "tt");
    let ff = k.name_str(anon, "ff");

    let r = k.add_inductive(b2, &[], 0, prop, &[(tt, b2_const), (ff, b2_const)]);
    println!("add_inductive(Bool2 : Prop) = {r:?}");
    assert!(r.is_ok(), "kernel accepted a Prop inductive with 2 ctors?");

    // Does Bool2.rec exist and what is its type?
    let rec = k.name_str(b2, "rec");
    let env_has = k.environment().get(rec).is_some();
    println!("Bool2.rec present: {env_has}");

    // Bool2.rec.{v} : {motive : Bool2 -> Sort v} -> motive tt -> motive ff -> (t : Bool2) -> motive t
    // Instantiate motive := fun _ : Bool2 => Prop  (i.e. Sort 0), so v := 1.
    let zero = k.level_zero();
    let one = k.level_succ(zero);
    let rec_const = k.const_(rec, vec![one]); // elim level v := 1

    let sort0 = k.sort_zero();
    let motive = k.lam(anon, b2_const, sort0, BinderInfo::Default); // fun _ => Prop

    // Need two Props: True and False. Use axioms? Use Prop-level constants.
    // Declare: axiom P : Prop, axiom Q : Prop  (two distinct Props)
    let pn = k.name_str(anon, "P");
    let qn = k.name_str(anon, "Q");
    let prop2 = k.sort_zero();
    k.add_declaration(axeyum_lean_kernel::Declaration::Axiom { name: pn, uparams: vec![], ty: prop2 }).unwrap();
    k.add_declaration(axeyum_lean_kernel::Declaration::Axiom { name: qn, uparams: vec![], ty: prop2 }).unwrap();
    let p = k.const_(pn, vec![]);
    let q = k.const_(qn, vec![]);

    let tt_c = k.const_(tt, vec![]);
    let ff_c = k.const_(ff, vec![]);

    // f := fun b => Bool2.rec motive P Q b   -- eliminates Prop into Prop-valued Type
    // f tt  ==> P ,  f ff ==> Q
    let app_tt = {
        let a = k.app(rec_const, motive);
        let a = k.app(a, p);
        let a = k.app(a, q);
        k.app(a, tt_c)
    };
    let app_ff = {
        let a = k.app(rec_const, motive);
        let a = k.app(a, p);
        let a = k.app(a, q);
        k.app(a, ff_c)
    };

    let w_tt = k.whnf(app_tt);
    let w_ff = k.whnf(app_ff);
    println!("whnf(rec .. tt) == P ? {}", w_tt == p);
    println!("whnf(rec .. ff) == Q ? {}", w_ff == q);

    // The smoking gun: are P and Q now definitionally equal?
    let bad = k.def_eq(app_tt, app_ff);
    println!("def_eq(rec..tt, rec..ff) [i.e. P == Q] = {bad}");

    // also directly: is tt def_eq ff via proof irrelevance?
    let irrel = k.def_eq(tt_c, ff_c);
    println!("def_eq(tt, ff) via proof irrelevance = {irrel}");
}
