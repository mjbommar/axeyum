//! Tests for [`super`] — `AlgS.VectorSpace`.

use super::*;
use crate::build_logic_prelude;
use crate::nat_prelude::field_setoid::{FieldDeps, FieldNames, declare_field_setoid};
use crate::nat_prelude::module_setoid::{ModuleDeps, declare_module_setoid};
use crate::nat_prelude::polynomial_setoid::{PolyDeps, declare_poly_setoid};
use crate::nat_prelude::structures as algeq;
use crate::nat_prelude::structures_setoid::{
    StructuresSRecordNames, declare_structures_s_all, declare_structures_s_extra,
    intern_structures_s_names,
};

struct Fixture {
    lg: LogicPrelude,
    st: StructuresSRecordNames,
    fld: FieldNames,
    m: ModuleNames,
    vs: VectorSpaceNames,
}

fn build(k: &mut Kernel) -> Fixture {
    let lg = build_logic_prelude(k).expect("logic prelude must build");
    let alg_p = algeq::intern_structures_names(k);
    let alg_st = algeq::declare_structures_all(k, &alg_p, &lg).expect("Alg spine builds");
    let p = intern_structures_s_names(k);
    let st = declare_structures_s_all(k, &p, &lg).expect("AlgS spine builds");
    let extra = declare_structures_s_extra(k, &lg, &p, &st, &alg_p, &alg_st)
        .expect("AlgS extras must admit");
    let poly = declare_poly_setoid(
        k,
        &lg,
        &st.comm_ring,
        &st.comm_group,
        PolyDeps {
            comm_ring_to_ring_s: extra.comm_ring_to_ring_s,
            mul_zero: extra.mul_zero,
        },
        p.algs,
    )
    .expect("AlgS.Poly must admit");
    let m = declare_module_setoid(
        k,
        &lg,
        &st.comm_ring,
        &st.comm_group,
        &st.group,
        ModuleDeps {
            add_left_cancel: extra.add_left_cancel,
            inv_unique: extra.inv_unique,
            comm_ring_to_comm_group_s: extra.comm_ring_to_comm_group_s,
            comm_group_to_group_s: extra.comm_group_to_group_s,
            poly_comm_group: poly.comm_group,
            poly_smul: poly.ops.smul,
            poly_equiv: poly.ops.equiv,
        },
        p.algs,
    )
    .expect("AlgS.Module must admit");
    let fld = declare_field_setoid(
        k,
        &lg,
        &st.comm_ring,
        FieldDeps {
            comm_ring_to_ring_s: extra.comm_ring_to_ring_s,
            mul_neg_one: extra.mul_neg_one,
        },
        p.algs,
    )
    .expect("AlgS.Field must admit");
    let vs = declare_vector_space(k, &lg, &fld, &st.comm_group, &m, p.algs)
        .expect("AlgS.VectorSpace must admit over an abstract field");
    Fixture {
        lg,
        st,
        fld,
        m,
        vs,
    }
}

#[test]
fn the_vector_space_layer_admits() {
    let mut k = Kernel::new();
    let f = build(&mut k);
    for name in f.vs.all() {
        assert!(
            k.environment().get(name).is_some(),
            "declaration missing from the environment"
        );
    }
}

/// **The headline claim**, read from `Kernel::axiom_footprint`.
#[test]
fn the_vector_space_layer_is_axiom_free() {
    let mut k = Kernel::new();
    let f = build(&mut k);
    for name in f.vs.all() {
        let footprint = k.axiom_footprint(name);
        assert!(
            footprint.is_empty(),
            "axiom footprint must be empty, got {} entries",
            footprint.len()
        );
    }
}

/// The three results are `Theorem`s — the kernel checked their proof terms.
#[test]
fn the_three_results_are_checked_theorems() {
    let mut k = Kernel::new();
    let f = build(&mut k);
    for name in [
        f.vs.smul_left_cancel,
        f.vs.solve_smul,
        f.vs.basis_zero_unique,
    ] {
        let decl = k.environment().get(name).expect("must exist").clone();
        assert!(
            matches!(decl, Declaration::Theorem { .. }),
            "{name:?} must be a Theorem"
        );
    }
}

/// Print the rendered types and assert each really mentions the objects it is
/// about, so the test cannot pass on an empty render.
#[test]
fn the_vector_space_types_render() {
    let mut k = Kernel::new();
    let f = build(&mut k);
    for name in f.vs.all() {
        let decl = k
            .environment()
            .get(name)
            .expect("declaration must exist")
            .clone();
        let ty = match &decl {
            Declaration::Definition { ty, .. } | Declaration::Theorem { ty, .. } => *ty,
            _ => panic!("unexpected declaration kind"),
        };
        let rendered = k.render_lean(ty);
        println!("decl {name:?} :\n  {rendered}\n");
        assert!(
            rendered.contains("AlgS.Field"),
            "rendered type must mention AlgS.Field — a vector space is over a FIELD"
        );
    }
    // `basis_zero_unique` is the dimension statement: it must mention the
    // basis predicate and conclude an equation between two `Nat`s.
    let decl = k
        .environment()
        .get(f.vs.basis_zero_unique)
        .expect("must exist")
        .clone();
    let Declaration::Theorem { ty, .. } = decl else {
        panic!("basis_zero_unique must be a Theorem")
    };
    let rendered = k.render_lean(ty);
    assert!(
        rendered.contains("AlgS.Module.isBasis"),
        "the dimension statement must be about isBasis, got: {rendered}"
    );
    assert!(
        rendered.contains("Nat.zero"),
        "the dimension statement must conclude at Nat.zero, got: {rendered}"
    );
}

/// `IsVectorSpace F M smul` unfolds to
/// `AlgS.Module.IsModule (AlgS.Field.toCommRing F) M smul` — checked with
/// `def_eq` against the hand-built right-hand side, so a definition that
/// unfolded to `True` would be caught.
#[test]
fn is_vector_space_unfolds_to_is_module_over_the_underlying_ring() {
    let mut k = Kernel::new();
    let f = build(&mut k);
    let fv = k.fvar(93_000);
    let mv = k.fvar(93_001);
    let sv = k.fvar(93_002);

    let lhs = {
        let c = k.const_(f.vs.is_vector_space, vec![]);
        let e = k.app(c, fv);
        let e = k.app(e, mv);
        k.app(e, sv)
    };
    let rhs = {
        let to_c = k.const_(f.fld.to_comm_ring, vec![]);
        let ring = k.app(to_c, fv);
        let c = k.const_(f.m.is_module, vec![]);
        let e = k.app(c, ring);
        let e = k.app(e, mv);
        k.app(e, sv)
    };
    assert!(
        k.def_eq(lhs, rhs),
        "IsVectorSpace must unfold to IsModule over `toCommRing F`"
    );

    let true_c = k.const_(f.lg.true_, vec![]);
    assert!(
        !k.def_eq(lhs, true_c),
        "IsVectorSpace must not be vacuously True"
    );
}

/// **Negative control for `basis_zero_unique`.** The proof's contradiction is
/// `apartCompat one zero <equiv one zero> oneApartZero`. Feeding
/// `equivRefl one` where the derived `equiv one zero` belongs — a SMALL change,
/// one subterm — must be refused: `apart one zero` is not `apart one one`.
#[test]
fn control_the_contradiction_needs_equiv_one_zero_not_reflexivity() {
    let mut k = Kernel::new();
    let f = build(&mut k);
    let fr = f.fld.field;
    let field_ty = k.const_(fr.ind, vec![]);
    let fv = k.fvar(94_000);
    let one = sel(&mut k, &fr, super::ix::ONE, fv);
    let refl = sel(&mut k, &fr, super::ix::EQUIV_REFL, fv);
    let compat = sel(&mut k, &fr, super::ix::APART_COMPAT, fv);
    let one_apart_zero = sel(&mut k, &fr, super::ix::ONE_APART_ZERO, fv);

    // MUTATION: `equivRefl one : equiv one one` in place of `equiv one zero`.
    let bad_eq = k.app(refl, one);
    let bad = {
        let e = k.app(compat, one);
        let e = k.app(e, one);
        let e = k.app(e, bad_eq);
        k.app(e, one_apart_zero)
    };
    let false_ty = k.const_(f.lg.false_, vec![]);
    let value = lam_over(&mut k, 94_000, field_ty, bad);
    let ty = pi_over(&mut k, 94_000, field_ty, false_ty);
    let ns = k.name_str(f.st.comm_ring.ind, "VectorSpaceControl");
    let name = k.name_str(ns, "reflexivity_is_not_a_contradiction");
    let got = k.add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    });
    assert!(
        got.is_err(),
        "`apartCompat one one (equivRefl one) oneApartZero` must be refused — \
         `oneApartZero : apart one zero` does not fit the `apart one one` slot"
    );
    assert!(
        k.environment().get(f.vs.basis_zero_unique).is_some(),
        "the real basis_zero_unique must be present"
    );
}

/// **Negative control for `solve_smul`.** Its existential witness is the
/// inverse `b`; introducing the existential at `a` instead must be refused.
#[test]
fn control_solve_smul_witness_must_be_the_inverse() {
    let mut k = Kernel::new();
    let f = build(&mut k);
    let fr = f.fld.field;
    let cg = f.st.comm_group;
    let field_ty = k.const_(fr.ind, vec![]);
    let group_ty = k.const_(cg.ind, vec![]);
    let fv = k.fvar(95_000);
    let mv = k.fvar(95_001);
    let fc = sel(&mut k, &fr, super::ix::CARRIER, fv);
    let mc = sel(&mut k, &cg, idx::comm_group::CARRIER, mv);
    let meq = sel(&mut k, &cg, idx::comm_group::EQUIV, mv);
    let mrefl = sel(&mut k, &cg, idx::comm_group::EQUIV_REFL, mv);
    let smul_ty = {
        let inner = arrow(&mut k, mc, mc);
        arrow(&mut k, fc, inner)
    };
    let sv = k.fvar(95_002);
    let a = k.fvar(95_003);
    let v = k.fvar(95_004);

    // `goal := Exists (fun c => M.equiv (smul a v) (smul c v))`, whose only
    // honest witness here is `a` itself; the control introduces at `v`, which
    // is not even a scalar.
    let pred = {
        let cc = k.fvar(95_005);
        let cv = app2(&mut k, sv, cc, v);
        let av = app2(&mut k, sv, a, v);
        let body = app2(&mut k, meq, av, cv);
        lam_over(&mut k, 95_005, fc, body)
    };
    let l0 = k.level_zero();
    let l1 = k.level_succ(l0);
    let ex = k.const_(f.lg.exists_, vec![l1]);
    let goal = app2(&mut k, ex, fc, pred);
    let intro = k.const_(f.lg.exists_intro, vec![l1]);
    let av = app2(&mut k, sv, a, v);
    let r = k.app(mrefl, av);
    // MUTATION: the witness is `v : M.carrier`, not a scalar.
    let bad = {
        let e = k.app(intro, fc);
        let e = k.app(e, pred);
        let e = k.app(e, v);
        k.app(e, r)
    };
    let value = lam_over(&mut k, 95_004, mc, bad);
    let value = lam_over(&mut k, 95_003, fc, value);
    let value = lam_over(&mut k, 95_002, smul_ty, value);
    let value = lam_over(&mut k, 95_001, group_ty, value);
    let value = lam_over(&mut k, 95_000, field_ty, value);
    let ty = pi_over(&mut k, 95_004, mc, goal);
    let ty = pi_over(&mut k, 95_003, fc, ty);
    let ty = pi_over(&mut k, 95_002, smul_ty, ty);
    let ty = pi_over(&mut k, 95_001, group_ty, ty);
    let ty = pi_over(&mut k, 95_000, field_ty, ty);
    let ns = k.name_str(f.st.comm_ring.ind, "VectorSpaceControl");
    let name = k.name_str(ns, "solve_smul_wrong_witness_sort");
    let got = k.add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    });
    assert!(
        got.is_err(),
        "a vector cannot be the scalar witness of `Exists (fun c : F.carrier => …)`"
    );
    assert!(
        k.environment().get(f.vs.solve_smul).is_some(),
        "the real solve_smul must be present"
    );
}
