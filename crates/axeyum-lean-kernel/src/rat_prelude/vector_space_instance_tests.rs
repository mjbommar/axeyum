//! Tests for [`super`] — ℚ as a vector space over itself.

use crate::Kernel;
use crate::build_rat_prelude;
use crate::env::Declaration;
use crate::name::NameId;

fn n(k: &mut Kernel, suffix: &str) -> NameId {
    let anon = k.anon();
    let rat = k.name_str(anon, "Rat");
    k.name_str(rat, suffix)
}

/// The four declarations exist and are axiom-free.
#[test]
fn the_rat_vector_space_instance_admits_and_is_axiom_free() {
    let mut k = Kernel::new();
    build_rat_prelude(&mut k).expect("rat prelude must build");
    for suffix in [
        "commRingS",
        "addCommGroupS",
        "vectorSpaceS",
        "linComb_eq_sumRange",
    ] {
        let name = n(&mut k, suffix);
        assert!(
            k.environment().get(name).is_some(),
            "Rat.{suffix} missing from the environment"
        );
        let fp = k.axiom_footprint(name);
        assert!(
            fp.is_empty(),
            "Rat.{suffix} footprint must be empty, got {} entries",
            fp.len()
        );
    }
}

/// **ℚ is a vector space over itself** — `Rat.vectorSpaceS` is a `Theorem`
/// whose type is `AlgS.VectorSpace.IsVectorSpace Rat.fieldS …`.
#[test]
fn rat_is_a_vector_space_over_itself() {
    let mut k = Kernel::new();
    build_rat_prelude(&mut k).expect("rat prelude must build");
    let name = n(&mut k, "vectorSpaceS");
    let decl = k.environment().get(name).expect("must exist").clone();
    let Declaration::Theorem { ty, .. } = decl else {
        panic!("Rat.vectorSpaceS must be a Theorem")
    };
    let rendered = k.render_lean(ty);
    println!("Rat.vectorSpaceS : {rendered}");
    assert!(
        rendered.contains("AlgS.VectorSpace.IsVectorSpace"),
        "must be the vector-space predicate, got: {rendered}"
    );
    assert!(
        rendered.contains("Rat.fieldS"),
        "the scalars must be Rat.fieldS, got: {rendered}"
    );
}

/// **The bridge, and the measurement that made it cheap.** `linComb` at ℚ is
/// `Rat.sumRange` — and it is `Eq.refl`, which this test checks by asserting
/// the two sides are `def_eq` directly, independently of the declaration.
#[test]
fn lin_comb_at_rat_is_definitionally_sum_range() {
    let mut k = Kernel::new();
    let p = build_rat_prelude(&mut k).expect("rat prelude must build");
    let anon = k.anon();
    let rat_root = k.name_str(anon, "Rat");
    let algs = k.name_str(anon, "AlgS");
    let module = k.name_str(algs, "Module");
    let lin_comb = k.name_str(module, "linComb");

    let rat = k.const_(p.int.rat, vec![]);
    let nat = k.const_(p.int.nat.logic.nat, vec![]);
    let mul = k.const_(p.int.rat_mul, vec![]);
    let ring = {
        let x = k.name_str(rat_root, "commRingS");
        k.const_(x, vec![])
    };
    let group = {
        let x = k.name_str(rat_root, "addCommGroupS");
        k.const_(x, vec![])
    };
    let c = k.fvar(99_000);
    let v = k.fvar(99_001);
    let n_fv = k.fvar(99_002);

    let lhs = {
        let t = k.const_(lin_comb, vec![]);
        let mut e = t;
        for x in [ring, group, mul, c, v, n_fv] {
            e = k.app(e, x);
        }
        e
    };
    let rhs = {
        let g = {
            let i = k.fvar(99_003);
            let ci = k.app(c, i);
            let vi = k.app(v, i);
            let prod = {
                let e = k.app(mul, ci);
                k.app(e, vi)
            };
            crate::nat_prelude::structures::lam_over(&mut k, 99_003, nat, prod)
        };
        let t = k.const_(p.sum_range, vec![]);
        let e = k.app(t, g);
        k.app(e, n_fv)
    };
    assert!(
        k.def_eq(lhs, rhs),
        "AlgS.Module.linComb at ℚ must be DEFINITIONALLY Rat.sumRange"
    );

    // Negative control: `sumRange` of the coefficients alone (the `v` factor
    // dropped) is a SMALL change and must NOT be def_eq.
    let wrong = {
        let t = k.const_(p.sum_range, vec![]);
        let e = k.app(t, c);
        k.app(e, n_fv)
    };
    assert!(
        !k.def_eq(lhs, wrong),
        "dropping the vector factor must break the agreement — otherwise the \
         bridge is measuring nothing"
    );
    let _ = rat;

    // Print the declared bridge's rendered type, and assert it really names
    // both sides so the print cannot be of an empty render.
    let name = k.name_str(rat_root, "linComb_eq_sumRange");
    let decl = k.environment().get(name).expect("must exist").clone();
    let Declaration::Theorem { ty, .. } = decl else {
        panic!("Rat.linComb_eq_sumRange must be a Theorem")
    };
    let rendered = k.render_lean(ty);
    println!("Rat.linComb_eq_sumRange : {rendered}");
    assert!(
        rendered.contains("AlgS.Module.linComb") && rendered.contains("Rat.sumRange"),
        "the bridge must name both sides, got: {rendered}"
    );
}
