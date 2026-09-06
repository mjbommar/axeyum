//! Tests for [`super`] — `AlgS.Exchange.*`.

use super::*;
use crate::build_logic_prelude;
use crate::nat_prelude::module_setoid::{ModuleDeps, declare_module_setoid};
use crate::nat_prelude::polynomial_setoid::{PolyDeps, declare_poly_setoid};
use crate::nat_prelude::structures as algeq;
use crate::nat_prelude::structures_setoid::{
    StructuresSRecordNames, declare_structures_s_all, declare_structures_s_extra,
    intern_structures_s_names,
};
use crate::nat_prelude::vector_space_exchange::declare_index_surgery;

struct Fixture {
    st: StructuresSRecordNames,
    ex: ExchangeNames,
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
    let ix = declare_index_surgery(k, &lg, p.algs).expect("AlgS.Index must admit");
    let ex = declare_exchange(k, &lg, &st.comm_ring, &st.comm_group, &m, &ix, p.algs)
        .expect("AlgS.Exchange must admit over an abstract module");
    Fixture { st, ex }
}

/// Each result is declared on its OWN, in dependency order, so a rejection
/// names one declaration instead of the whole bundle. One bad declaration
/// poisons a shared build, and the bundled `expect` cannot say which.
#[test]
fn each_result_is_admitted_on_its_own() {
    let mut k = Kernel::new();
    let lg = build_logic_prelude(&mut k).expect("logic prelude must build");
    let alg_p = algeq::intern_structures_names(&mut k);
    let alg_st = algeq::declare_structures_all(&mut k, &alg_p, &lg).expect("Alg spine builds");
    let p = intern_structures_s_names(&mut k);
    let st = declare_structures_s_all(&mut k, &p, &lg).expect("AlgS spine builds");
    let extra = declare_structures_s_extra(&mut k, &lg, &p, &st, &alg_p, &alg_st)
        .expect("AlgS extras must admit");
    let poly = declare_poly_setoid(
        &mut k,
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
        &mut k,
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
    let ix = declare_index_surgery(&mut k, &lg, p.algs).expect("AlgS.Index must admit");
    let ns = k.name_str(p.algs, "Exchange");
    let osl = declare_op_swap_last(&mut k, &st.comm_group, ns);
    println!("op_swap_last: {:?}", osl.as_ref().err());
    let osl = osl.expect("op_swap_last");
    let ext = declare_lin_comb_ext_below(&mut k, &lg, &st.comm_ring, &st.comm_group, &m, &ix, ns);
    println!("linComb_ext_below: {:?}", ext.as_ref().err());
    let ext = ext.expect("linComb_ext_below");
    let ins = declare_lin_comb_insert_at(
        &mut k,
        &lg,
        &st.comm_ring,
        &st.comm_group,
        &m,
        &ix,
        osl,
        ext,
        ns,
    );
    println!("linComb_insertAt: {:?}", ins.as_ref().err());
    let ins = ins.expect("linComb_insertAt");
    let sp = declare_lin_comb_remove_at_insert_at(
        &mut k,
        &lg,
        &st.comm_ring,
        &st.comm_group,
        &m,
        &ix,
        ext,
        ins,
        ns,
    );
    println!("linComb_removeAt_insertAt: {:?}", sp.as_ref().err());
    sp.expect("linComb_removeAt_insertAt");
}

#[test]
fn the_exchange_layer_admits() {
    let mut k = Kernel::new();
    let f = build(&mut k);
    for name in f.ex.owned_names() {
        assert!(
            k.environment().get(name).is_some(),
            "declaration missing from the environment"
        );
    }
}

/// The headline claim, read from `Kernel::axiom_footprint` — after
/// `Environment::contains`, because a MISSING name also returns an empty
/// footprint.
#[test]
fn the_exchange_layer_is_axiom_free() {
    let mut k = Kernel::new();
    let f = build(&mut k);
    for name in f.ex.owned_names() {
        assert!(
            k.environment().get(name).is_some(),
            "the name must exist before its footprint means anything"
        );
        let footprint = k.axiom_footprint(name);
        assert!(
            footprint.is_empty(),
            "axiom footprint must be empty, got {} entries",
            footprint.len()
        );
    }
}

/// All four results are `Theorem`s and the count is derived from
/// `owned_names`, the authority.
#[test]
fn every_exchange_result_is_a_checked_theorem() {
    let mut k = Kernel::new();
    let f = build(&mut k);
    let mut seen = 0usize;
    for name in f.ex.owned_names() {
        let decl = k.environment().get(name).expect("must exist").clone();
        assert!(
            matches!(decl, Declaration::Theorem { .. }),
            "{name:?} must be a Theorem"
        );
        seen += 1;
    }
    assert_eq!(seen, f.ex.owned_names().len());
}

/// **The inventory for ADR-1657's fact ledger entries.** Prints every name
/// as `EXCHANGE-INVENTORY|<name>|<rendered type>`, read from
/// `Kernel::environment`.
#[test]
fn the_exchange_declaration_inventory() {
    let mut k = Kernel::new();
    let f = build(&mut k);
    let expected = f.ex.owned_names().len();
    let mut printed = 0usize;
    for name in f.ex.owned_names() {
        let decl = k.environment().get(name).expect("must exist").clone();
        let Declaration::Theorem { ty, .. } = decl else {
            panic!("{name:?} must be a Theorem")
        };
        let rendered = k.render_lean(ty);
        assert!(!rendered.trim().is_empty(), "{name:?} rendered empty");
        println!("EXCHANGE-INVENTORY|{name:?}|{rendered}");
        printed += 1;
    }
    assert_eq!(printed, expected, "every owned name must have printed");
}

/// The split lemma must be about the things it claims to be about: a
/// `linComb`, a `removeAt` on BOTH the coefficients and the vectors, and an
/// `AlgS.Index.le` bound. A version that had lost the bound, or that
/// removed only from the coefficient family, would render differently.
#[test]
fn the_split_lemma_is_about_what_it_claims() {
    let mut k = Kernel::new();
    let f = build(&mut k);
    let decl = k
        .environment()
        .get(f.ex.lin_comb_remove_at_insert_at)
        .expect("must exist")
        .clone();
    let Declaration::Theorem { ty, .. } = decl else {
        panic!("must be a Theorem")
    };
    let r = k.render_lean(ty);
    assert!(
        r.contains("AlgS.Module.linComb"),
        "the split is about linComb, got: {r}"
    );
    assert!(
        r.contains("AlgS.Index.removeAt"),
        "the split is about removeAt, got: {r}"
    );
    assert!(
        r.contains("AlgS.Index.le"),
        "the split carries the order bound `le i n`, got: {r}"
    );
    assert!(
        r.contains("AlgS.Module.IsModule"),
        "the split needs the module axioms, got: {r}"
    );
    // `removeAt` must appear at BOTH carriers: the coefficient family and the
    // vector family are cut at the same index.
    assert!(
        r.matches("AlgS.Index.removeAt").count() >= 2,
        "removeAt must be applied to both families, got: {r}"
    );
    // `op_swap_last` must NOT need the module: it is a pure group fact.
    let decl = k
        .environment()
        .get(f.ex.op_swap_last)
        .expect("must exist")
        .clone();
    let Declaration::Theorem { ty, .. } = decl else {
        panic!("must be a Theorem")
    };
    let r = k.render_lean(ty);
    assert!(
        !r.contains("AlgS.Module"),
        "op_swap_last is a CommGroup fact and must not mention the module, got: {r}"
    );
    assert!(
        r.contains("AlgS.CommGroup"),
        "op_swap_last must be over AlgS.CommGroup, got: {r}"
    );
}

/// **Negative control for `op_swap_last`.** Its middle step rewrites the
/// SECOND factor with `comm b c`. Supplying `comm` at the wrong pair — `a`
/// and `c` instead of `b` and `c`, a one-argument change — must be refused:
/// `equiv (op a c) (op c a)` does not fit the `equiv (op b c) (op c b)` slot.
#[test]
fn control_op_swap_last_needs_comm_at_the_inner_pair() {
    let mut k = Kernel::new();
    let f = build(&mut k);
    let cg = f.st.comm_group;
    use idx::comm_group as g;
    let group_ty = k.const_(cg.ind, vec![]);
    let gv = k.fvar(96_000);
    let carrier = sel(&mut k, &cg, g::CARRIER, gv);
    let equiv = sel(&mut k, &cg, g::EQUIV, gv);
    let refl = sel(&mut k, &cg, g::EQUIV_REFL, gv);
    let op = sel(&mut k, &cg, g::OP, gv);
    let op_congr = sel(&mut k, &cg, g::OP_CONGR, gv);
    let comm = sel(&mut k, &cg, g::COMM, gv);

    let a = k.fvar(96_001);
    let b = k.fvar(96_002);
    let c = k.fvar(96_003);
    let bc = app2(&mut k, op, b, c);
    let cb = app2(&mut k, op, c, b);
    let a_bc = app2(&mut k, op, a, bc);
    let a_cb = app2(&mut k, op, a, cb);
    let goal = app2(&mut k, equiv, a_bc, a_cb);

    // MUTATION: `comm a c` where `comm b c` belongs.
    let bad_comm = t_app(&mut k, comm, &[a, c]);
    let ra = k.app(refl, a);
    let bad = t_app(&mut k, op_congr, &[a, a, bc, cb, ra, bad_comm]);

    let value = lam_over(&mut k, 96_003, carrier, bad);
    let value = lam_over(&mut k, 96_002, carrier, value);
    let value = lam_over(&mut k, 96_001, carrier, value);
    let value = lam_over(&mut k, 96_000, group_ty, value);
    let ty = pi_over(&mut k, 96_003, carrier, goal);
    let ty = pi_over(&mut k, 96_002, carrier, ty);
    let ty = pi_over(&mut k, 96_001, carrier, ty);
    let ty = pi_over(&mut k, 96_000, group_ty, ty);

    let ns = k.name_str(cg.ind, "ExchangeControl");
    let name = k.name_str(ns, "comm_at_the_wrong_pair");
    let got = k.add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    });
    assert!(
        got.is_err(),
        "`comm a c` must not be accepted where `comm b c` is required"
    );
    assert!(
        k.environment().get(f.ex.op_swap_last).is_some(),
        "the real op_swap_last must be present"
    );
}
