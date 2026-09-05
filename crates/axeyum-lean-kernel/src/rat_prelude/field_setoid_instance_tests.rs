//! Tests for [`super`] — ℚ as an `AlgS.Field`.

use crate::Kernel;
use crate::build_rat_prelude;
use crate::env::Declaration;
use crate::name::NameId;

fn names(k: &mut Kernel) -> [(NameId, &'static str); 8] {
    let anon = k.anon();
    let rat = k.name_str(anon, "Rat");
    [
        (k.name_str(rat, "ne_of_lt"), "Rat.ne_of_lt"),
        (k.name_str(rat, "apart"), "Rat.apart"),
        (k.name_str(rat, "apart_symm"), "Rat.apart_symm"),
        (k.name_str(rat, "apart_cotrans"), "Rat.apart_cotrans"),
        (k.name_str(rat, "apart_compat"), "Rat.apart_compat"),
        (k.name_str(rat, "mulInvEx"), "Rat.mulInvEx"),
        (k.name_str(rat, "fieldS"), "Rat.fieldS"),
        (k.name_str(rat, "fieldS_isTight"), "Rat.fieldS_isTight"),
    ]
}

/// Every declaration is present, and `Rat.fieldS`'s type IS `AlgS.Field` —
/// read from the environment, not from the source.
#[test]
fn rat_is_a_field_over_the_setoid_spine() {
    let mut k = Kernel::new();
    build_rat_prelude(&mut k).expect("rat prelude must build");
    for (n, label) in names(&mut k) {
        assert!(
            k.environment().get(n).is_some(),
            "{label} missing from the environment"
        );
    }
    let anon = k.anon();
    let rat = k.name_str(anon, "Rat");
    let field_s = k.name_str(rat, "fieldS");
    let decl = k.environment().get(field_s).expect("must exist").clone();
    let Declaration::Definition { ty, .. } = decl else {
        panic!("Rat.fieldS must be a Definition")
    };
    let rendered = k.render_lean(ty);
    assert_eq!(
        rendered.trim(),
        "AlgS.Field",
        "Rat.fieldS must be an AlgS.Field"
    );
}

/// **The headline claim**, read from `Kernel::axiom_footprint`.
#[test]
fn the_rat_field_instance_is_axiom_free() {
    let mut k = Kernel::new();
    build_rat_prelude(&mut k).expect("rat prelude must build");
    for (n, label) in names(&mut k) {
        let fp = k.axiom_footprint(n);
        assert!(
            fp.is_empty(),
            "{label} axiom footprint must be empty, got {} entries",
            fp.len()
        );
    }
}

/// The `AlgS.Field` selectors, applied to `Rat.fieldS`, must reduce to ℚ's own
/// constants — an **evaluation test** for the instance. A `Rat.fieldS` built
/// from the wrong ring, or with the arguments in the wrong order, would still
/// have type `AlgS.Field` and would fail here.
#[test]
fn the_rat_field_selectors_reduce_to_rats_own_constants() {
    let mut k = Kernel::new();
    build_rat_prelude(&mut k).expect("rat prelude must build");
    let anon = k.anon();
    let rat = k.name_str(anon, "Rat");
    let algs = k.name_str(anon, "AlgS");
    let field = k.name_str(algs, "Field");
    let field_s = {
        let n = k.name_str(rat, "fieldS");
        k.const_(n, vec![])
    };

    for (suffix, target) in [
        ("carrier", "Rat"),
        ("zero", "Rat.zero"),
        ("one", "Rat.one"),
        ("mul", "Rat.mul"),
        ("add", "Rat.add"),
        ("neg", "Rat.neg"),
        ("apart", "Rat.apart"),
    ] {
        let selname = k.name_str(field, suffix);
        let sel = k.const_(selname, vec![]);
        let lhs = k.app(sel, field_s);
        let target_name = {
            let mut parts = target.split('.');
            let head = parts.next().expect("non-empty");
            let mut n = k.name_str(anon, head);
            for part in parts {
                n = k.name_str(n, part);
            }
            n
        };
        let rhs = k.const_(target_name, vec![]);
        assert!(
            k.def_eq(lhs, rhs),
            "AlgS.Field.{suffix} Rat.fieldS must reduce to {target}"
        );
    }

    // ...and `apart` must NOT be the ring's own equality: apartness is data.
    let selname = k.name_str(field, "apart");
    let sel = k.const_(selname, vec![]);
    let lhs = k.app(sel, field_s);
    let l0 = k.level_zero();
    let l1 = k.level_succ(l0);
    let logic_eq = {
        let eq = k.name_str(anon, "Eq");
        let c = k.const_(eq, vec![l1]);
        let rat_ty = k.const_(rat, vec![]);
        k.app(c, rat_ty)
    };
    assert!(
        !k.def_eq(lhs, logic_eq),
        "AlgS.Field.apart Rat.fieldS must not be `Eq Rat` — it is its NEGATION"
    );
}

/// `Rat.fieldS_isTight` is a `Theorem` whose type is `AlgS.Field.IsTight
/// Rat.fieldS` — so ℚ's apartness really is tight, and the `IsTight`
/// predicate is not vacuous.
#[test]
fn rats_apartness_is_tight() {
    let mut k = Kernel::new();
    build_rat_prelude(&mut k).expect("rat prelude must build");
    let anon = k.anon();
    let rat = k.name_str(anon, "Rat");
    let n = k.name_str(rat, "fieldS_isTight");
    let decl = k.environment().get(n).expect("must exist").clone();
    let Declaration::Theorem { ty, .. } = decl else {
        panic!("Rat.fieldS_isTight must be a Theorem")
    };
    let rendered = k.render_lean(ty);
    println!("Rat.fieldS_isTight : {rendered}");
    assert!(
        rendered.contains("AlgS.Field.IsTight"),
        "must be the IsTight predicate, got: {rendered}"
    );
    assert!(
        rendered.contains("Rat.fieldS"),
        "must be about Rat.fieldS, got: {rendered}"
    );
}

/// **Negative control.** `Rat.apart_cotrans` is what decidability buys; its
/// proof resolves `Rat.lt_trichotomy`'s first branch into the LEFT disjunct.
/// Introducing that branch on the RIGHT instead — one constant changed — must
/// be refused, because `a < c` says nothing about `c` and `b`.
#[test]
fn control_cotransitivity_cannot_put_the_first_branch_on_the_right() {
    let mut k = Kernel::new();
    let p = build_rat_prelude(&mut k).expect("rat prelude must build");
    let anon = k.anon();
    let rat = k.name_str(anon, "Rat");
    let apart_n = k.name_str(rat, "apart");
    let ne_of_lt_n = k.name_str(rat, "ne_of_lt");
    let rat_ty = k.const_(rat, vec![]);
    let lg = p.int.nat.logic;

    let a = k.fvar(96_000);
    let b = k.fvar(96_001);
    let c = k.fvar(96_002);
    let lt = k.const_(p.lt, vec![]);
    let lt_ac = {
        let e = k.app(lt, a);
        k.app(e, c)
    };
    let h = k.fvar(96_003);
    let ap = k.const_(apart_n, vec![]);
    let goal_l = {
        let e = k.app(ap, a);
        k.app(e, c)
    };
    let goal_r = {
        let e = k.app(ap, c);
        k.app(e, b)
    };
    let or_c = k.const_(lg.or, vec![]);
    let goal = {
        let e = k.app(or_c, goal_l);
        k.app(e, goal_r)
    };
    let ne = {
        let t = k.const_(ne_of_lt_n, vec![]);
        let e = k.app(t, a);
        let e = k.app(e, c);
        k.app(e, h)
    };
    // MUTATION: `Or.inr` where the real proof uses `Or.inl`.
    let inr = k.const_(lg.or_inr, vec![]);
    let bad = {
        let e = k.app(inr, goal_l);
        let e = k.app(e, goal_r);
        k.app(e, ne)
    };
    let value = {
        let v = crate::nat_prelude::structures::lam_over(&mut k, 96_003, lt_ac, bad);
        let v = crate::nat_prelude::structures::lam_over(&mut k, 96_002, rat_ty, v);
        let v = crate::nat_prelude::structures::lam_over(&mut k, 96_001, rat_ty, v);
        crate::nat_prelude::structures::lam_over(&mut k, 96_000, rat_ty, v)
    };
    let ty = {
        let t = crate::nat_prelude::structures::arrow(&mut k, lt_ac, goal);
        let t = crate::nat_prelude::structures::pi_over(&mut k, 96_002, rat_ty, t);
        let t = crate::nat_prelude::structures::pi_over(&mut k, 96_001, rat_ty, t);
        crate::nat_prelude::structures::pi_over(&mut k, 96_000, rat_ty, t)
    };
    let ns = k.name_str(rat, "FieldSControl");
    let name = k.name_str(ns, "cotrans_wrong_disjunct");
    let got = k.add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    });
    assert!(
        got.is_err(),
        "`Rat.ne_of_lt a c h : apart a c` must not be accepted as `apart c b`"
    );
    // Positive twin: the real theorem is in the environment.
    let real = k.name_str(rat, "apart_cotrans");
    assert!(
        k.environment().get(real).is_some(),
        "the real Rat.apart_cotrans must be present"
    );
}
