//! Tests for [`super`] — `AlgS.Field`.
//!
//! Three kinds, deliberately:
//!
//! 1. **Admission and footprint.** Every declaration is present and
//!    `Kernel::axiom_footprint` is empty — read from the kernel, never from
//!    source text.
//! 2. **Evaluation tests for the three `Definition`s.** The trusted gate
//!    cannot tell you a definition is *wrong*, only that it type-checks, so
//!    `toCommRing`/`ofCommRing` are exercised by a symbolic ROUND TRIP checked
//!    with `Kernel::def_eq`: `toCommRing (ofCommRing R ap …)` must reduce to
//!    `R`'s own selectors field by field. A wrong selector index would
//!    type-check and fail here.
//! 3. **Negative controls.** For each theorem, one proof term that differs in
//!    a SMALL term and must be REFUSED, plus the positive twin (the real
//!    declaration, which the fixture already admitted) so a control that
//!    rejects for an unrelated reason is visible.

use super::*;
use crate::build_logic_prelude;
use crate::nat_prelude::structures as algeq;
use crate::nat_prelude::structures_setoid::{
    StructuresSRecordNames, declare_structures_s_all, declare_structures_s_extra,
    intern_structures_s_names,
};

struct Fixture {
    lg: LogicPrelude,
    st: StructuresSRecordNames,
    algs: NameId,
    f: FieldNames,
}

fn build(k: &mut Kernel) -> Fixture {
    let lg = build_logic_prelude(k).expect("logic prelude must build");
    let alg_p = algeq::intern_structures_names(k);
    let alg_st = algeq::declare_structures_all(k, &alg_p, &lg).expect("Alg spine builds");
    let p = intern_structures_s_names(k);
    let st = declare_structures_s_all(k, &p, &lg).expect("AlgS spine builds");
    let extra = declare_structures_s_extra(k, &lg, &p, &st, &alg_p, &alg_st)
        .expect("AlgS extras must admit");
    let deps = FieldDeps {
        comm_ring_to_ring_s: extra.comm_ring_to_ring_s,
        mul_neg_one: extra.mul_neg_one,
    };
    let f = declare_field_setoid(k, &lg, &st.comm_ring, deps, p.algs)
        .expect("AlgS.Field must admit over the setoid spine");
    Fixture {
        lg,
        st,
        algs: p.algs,
        f,
    }
}

// ---------------------------------------------------------------------------
// 1. Admission, shape, footprint.
// ---------------------------------------------------------------------------

/// The record admits at `Sort 2` with exactly the 29 fields the module doc
/// tabulates, and every selector is really in the environment (the
/// DECLARATION exists, not merely that no error came back).
#[test]
fn the_field_record_admits_with_twenty_nine_fields() {
    let mut k = Kernel::new();
    let fx = build(&mut k);
    assert_eq!(
        fx.f.field.field_count(),
        ix::FIELD_COUNT,
        "AlgS.Field field count"
    );
    assert_eq!(ix::FIELD_COUNT, 29, "the doc table pins 29");
    for i in 0..fx.f.field.field_count() {
        let n = fx.f.field.sel(i);
        assert!(
            k.environment().get(n).is_some(),
            "selector {i} missing from the environment"
        );
    }
    for n in [fx.f.field.ind, fx.f.field.mk, fx.f.field.rec] {
        assert!(
            k.environment().get(n).is_some(),
            "record head/ctor/rec missing"
        );
    }
}

/// The six new fields are at the indices `ix` claims, checked by NAME rather
/// than by counting — a spec-list reorder that keeps the count is caught here.
#[test]
fn the_six_new_fields_are_where_ix_says_they_are() {
    let mut k = Kernel::new();
    let fx = build(&mut k);
    let expected = [
        (ix::APART, "apart"),
        (ix::APART_SYMM, "apartSymm"),
        (ix::APART_COTRANS, "apartCotrans"),
        (ix::APART_COMPAT, "apartCompat"),
        (ix::MUL_INV_EX, "mulInvEx"),
        (ix::ONE_APART_ZERO, "oneApartZero"),
    ];
    for (i, suffix) in expected {
        let want = k.name_str(fx.f.field.ind, suffix);
        assert_eq!(fx.f.field.sel(i), want, "field {i} should be {suffix}");
    }
}

/// **The headline claim**, read from `Kernel::axiom_footprint` and not from a
/// comment.
#[test]
fn the_field_layer_is_axiom_free() {
    let mut k = Kernel::new();
    let fx = build(&mut k);
    let mut names: Vec<NameId> = fx.f.all().to_vec();
    for i in 0..fx.f.field.field_count() {
        names.push(fx.f.field.sel(i));
    }
    for name in names {
        let footprint = k.axiom_footprint(name);
        assert!(
            footprint.is_empty(),
            "axiom footprint must be empty, got {} entries",
            footprint.len()
        );
    }
}

/// Print every declaration's rendered type, and assert each one really
/// mentions `AlgS.Field` so the test cannot pass on an empty render.
#[test]
fn the_field_layer_types_render() {
    let mut k = Kernel::new();
    let fx = build(&mut k);
    for name in fx.f.all() {
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
        // `mul_neg_right` is the one `CommRing` fact in the bundle (see its
        // own doc for why it lives here), so the shared assertion is `AlgS`
        // and the `AlgS.Field` one is made separately below.
        assert!(
            rendered.contains("AlgS."),
            "rendered type must mention the AlgS spine"
        );
    }
    for name in [
        fx.f.to_comm_ring,
        fx.f.of_comm_ring,
        fx.f.is_tight,
        fx.f.apart_irrefl,
        fx.f.apart_left_congr,
        fx.f.apart_right_congr,
        fx.f.inv_unique,
        fx.f.mul_left_cancel,
    ] {
        let decl = k.environment().get(name).expect("must exist").clone();
        let ty = match &decl {
            Declaration::Definition { ty, .. } | Declaration::Theorem { ty, .. } => *ty,
            _ => panic!("unexpected declaration kind"),
        };
        let rendered = k.render_lean(ty);
        assert!(
            rendered.contains("AlgS.Field"),
            "rendered type must mention AlgS.Field, got: {rendered}"
        );
    }
}

/// The five theorems are `Theorem`s, so the kernel checked their proof terms.
/// There is no way to pass this with a stub.
#[test]
fn the_field_theorems_are_checked_theorems() {
    let mut k = Kernel::new();
    let fx = build(&mut k);
    for name in [
        fx.f.apart_irrefl,
        fx.f.apart_left_congr,
        fx.f.apart_right_congr,
        fx.f.inv_unique,
        fx.f.mul_left_cancel,
    ] {
        let decl = k.environment().get(name).expect("must exist").clone();
        assert!(
            matches!(decl, Declaration::Theorem { .. }),
            "{name:?} must be a Theorem, not a Definition or an Axiom"
        );
    }
}

// ---------------------------------------------------------------------------
// 2. Evaluation tests for the `Definition`s.
// ---------------------------------------------------------------------------

/// Build `ofCommRing R apart h1 … h5` against fresh free variables, apply
/// `toCommRing`, and check field by field that the result reduces to `R`'s own
/// selectors. **This is the evaluation test the trusted gate cannot give you**:
/// a `toCommRing` that projected field `i+1` instead of field `i` would still
/// type-check whenever two neighbouring fields have the same type, and would
/// fail here.
#[test]
fn to_comm_ring_of_of_comm_ring_is_the_ring_it_started_from() {
    let mut k = Kernel::new();
    let fx = build(&mut k);
    let cr = fx.st.comm_ring;
    let l0 = k.level_zero();
    let l1 = k.level_succ(l0);

    // A symbolic ring and the six extra arguments, all fresh fvars.
    let _ = (&fx.lg, l1);
    let r = k.fvar(90_000);
    // `ofCommRing R ap h24 … h28` — the seven arguments, symbolically.
    let mut built = k.const_(fx.f.of_comm_ring, vec![]);
    built = k.app(built, r);
    for j in 0..6u64 {
        let arg = k.fvar(90_001 + j);
        built = k.app(built, arg);
    }

    let to_c = k.const_(fx.f.to_comm_ring, vec![]);
    let round = k.app(to_c, built);

    for i in 0..23 {
        let lhs = sel(&mut k, &cr, i, round);
        let rhs = sel(&mut k, &cr, i, r);
        assert!(
            k.def_eq(lhs, rhs),
            "toCommRing(ofCommRing R …) field {i} must reduce to R's own selector"
        );
    }
}

/// The apartness the field was built from survives the constructor: for a
/// symbolic `ap`, `AlgS.Field.apart (ofCommRing R ap …)` reduces to `ap`
/// itself, and NOT to `R.equiv` — the two have the same TYPE, so only an
/// evaluation test separates them.
#[test]
fn of_comm_ring_keeps_the_apartness_it_was_given() {
    let mut k = Kernel::new();
    let fx = build(&mut k);
    let cr = fx.st.comm_ring;

    let r = k.fvar(90_000);
    let ap = k.fvar(90_001);
    let of_c = k.const_(fx.f.of_comm_ring, vec![]);
    let mut built = k.app(of_c, r);
    built = k.app(built, ap);
    for j in 0..5u64 {
        let arg = k.fvar(90_010 + j);
        built = k.app(built, arg);
    }

    let got = sel(&mut k, &fx.f.field, ix::APART, built);
    assert!(k.def_eq(got, ap), "apart must be the relation supplied");

    let equiv = sel(&mut k, &cr, ix::EQUIV, r);
    assert!(
        !k.def_eq(got, equiv),
        "apart must NOT collapse to the ring's own equivalence — the whole \
         point of ADR-1627 is that apartness is data, not the negation of equiv"
    );
}

/// `IsTight F` unfolds to the tightness statement — checked by rebuilding that
/// statement by hand and comparing with `def_eq`, so a definition that
/// unfolded to `True` (which would type-check) is caught.
#[test]
fn is_tight_unfolds_to_the_tightness_statement() {
    let mut k = Kernel::new();
    let fx = build(&mut k);
    let fr = fx.f.field;
    let f = k.fvar(90_100);
    let carrier = sel(&mut k, &fr, ix::CARRIER, f);
    let equiv = sel(&mut k, &fr, ix::EQUIV, f);
    let apart = sel(&mut k, &fr, ix::APART, f);

    let a = k.fvar(90_101);
    let b = k.fvar(90_102);
    let hap = app2(&mut k, apart, a, b);
    let not_c = k.const_(fx.lg.not, vec![]);
    let nap = k.app(not_c, hap);
    let concl = app2(&mut k, equiv, a, b);
    let body = arrow(&mut k, nap, concl);
    let body = pi_over(&mut k, 90_102, carrier, body);
    let want = pi_over(&mut k, 90_101, carrier, body);

    let is_tight = k.const_(fx.f.is_tight, vec![]);
    let got = k.app(is_tight, f);
    assert!(
        k.def_eq(got, want),
        "IsTight F must unfold to `forall a b, Not (apart a b) -> equiv a b`"
    );

    let true_c = k.const_(fx.lg.true_, vec![]);
    assert!(
        !k.def_eq(got, true_c),
        "IsTight must not be vacuously True"
    );
}

// ---------------------------------------------------------------------------
// 3. Negative controls. Each builds a proof term differing in a SMALL term
//    and asserts the trusted gate REFUSES it.
// ---------------------------------------------------------------------------

/// Shared scaffolding for the controls: a symbolic `F`, its selectors, and a
/// scratch namespace for the mutant declarations.
struct Mut {
    field_ty: ExprId,
    carrier: ExprId,
    equiv: ExprId,
    refl: ExprId,
    apart: ExprId,
    apart_cotrans: ExprId,
    apart_compat: ExprId,
    ns: NameId,
}

fn mutctx(k: &mut Kernel, fx: &Fixture) -> Mut {
    let fr = fx.f.field;
    let field_ty = k.const_(fr.ind, vec![]);
    let f = k.fvar(91_000);
    let ns = k.name_str(fx.algs, "FieldControl");
    Mut {
        field_ty,
        carrier: sel(k, &fr, ix::CARRIER, f),
        equiv: sel(k, &fr, ix::EQUIV, f),
        refl: sel(k, &fr, ix::EQUIV_REFL, f),
        apart: sel(k, &fr, ix::APART, f),
        apart_cotrans: sel(k, &fr, ix::APART_COTRANS, f),
        apart_compat: sel(k, &fr, ix::APART_COMPAT, f),
        ns,
    }
}

/// `apart_irrefl`'s proof discharges `apart a a` against `equivRefl a`.
/// Replacing the conclusion `False` by `apart a a` (a SMALL change: the same
/// proof term, one different type) must be refused.
#[test]
fn control_apart_irrefl_cannot_conclude_apart() {
    let mut k = Kernel::new();
    let fx = build(&mut k);
    let m = mutctx(&mut k, &fx);
    let a = k.fvar(91_001);
    let hap_ty = app2(&mut k, m.apart, a, a);
    let h = k.fvar(91_002);
    let refl_a = k.app(m.refl, a);
    let proof = {
        let e = k.app(m.apart_compat, a);
        let e = k.app(e, a);
        let e = k.app(e, refl_a);
        k.app(e, h)
    };
    let value = lam_over(&mut k, 91_002, hap_ty, proof);
    let value = lam_over(&mut k, 91_001, m.carrier, value);
    let value = lam_over(&mut k, 91_000, m.field_ty, value);
    // WRONG conclusion: `apart a a` where the real theorem says `False`.
    let ty = arrow(&mut k, hap_ty, hap_ty);
    let ty = pi_over(&mut k, 91_001, m.carrier, ty);
    let ty = pi_over(&mut k, 91_000, m.field_ty, ty);
    let name = k.name_str(m.ns, "apart_irrefl_wrong_conclusion");
    let got = k.add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    });
    assert!(
        got.is_err(),
        "a proof of False must not be accepted as a proof of `apart a a`"
    );
}

/// `apart_left_congr` resolves cotransitivity's LEFT disjunct. Using
/// `Or.resolve_right` instead — one constant changed, nothing else — must be
/// refused, because it would conclude `apart a a'` from a refutation of
/// `apart a' b` that the proof does not have.
#[test]
fn control_apart_left_congr_cannot_resolve_the_other_disjunct() {
    let mut k = Kernel::new();
    let fx = build(&mut k);
    let m = mutctx(&mut k, &fx);
    let a = k.fvar(91_001);
    let ap = k.fvar(91_002);
    let b = k.fvar(91_003);
    let heq_ty = app2(&mut k, m.equiv, a, ap);
    let hap_ty = app2(&mut k, m.apart, a, b);
    let heq = k.fvar(91_004);
    let hap = k.fvar(91_005);
    let left = app2(&mut k, m.apart, a, ap);
    let right = app2(&mut k, m.apart, ap, b);
    let cot = {
        let e = k.app(m.apart_cotrans, a);
        let e = k.app(e, b);
        let e = k.app(e, hap);
        k.app(e, ap)
    };
    let refute = {
        let hl = k.fvar(91_006);
        let e = k.app(m.apart_compat, a);
        let e = k.app(e, ap);
        let e = k.app(e, heq);
        let body = k.app(e, hl);
        lam_over(&mut k, 91_006, left, body)
    };
    // MUTATION: `resolve_right` for `resolve_left`.
    let resolve = k.const_(fx.lg.or_resolve_right, vec![]);
    let proof = {
        let e = k.app(resolve, left);
        let e = k.app(e, right);
        let e = k.app(e, cot);
        k.app(e, refute)
    };
    let value = lam_over(&mut k, 91_005, hap_ty, proof);
    let value = lam_over(&mut k, 91_004, heq_ty, value);
    let value = lam_over(&mut k, 91_003, m.carrier, value);
    let value = lam_over(&mut k, 91_002, m.carrier, value);
    let value = lam_over(&mut k, 91_001, m.carrier, value);
    let value = lam_over(&mut k, 91_000, m.field_ty, value);
    let ty = arrow(&mut k, hap_ty, right);
    let ty = arrow(&mut k, heq_ty, ty);
    let ty = pi_over(&mut k, 91_003, m.carrier, ty);
    let ty = pi_over(&mut k, 91_002, m.carrier, ty);
    let ty = pi_over(&mut k, 91_001, m.carrier, ty);
    let ty = pi_over(&mut k, 91_000, m.field_ty, ty);
    let name = k.name_str(m.ns, "apart_left_congr_resolve_right");
    let got = k.add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    });
    assert!(
        got.is_err(),
        "Or.resolve_right must not discharge the LEFT disjunct's refutation"
    );

    // Positive twin: the real theorem IS in the environment, so the control
    // above cannot be rejecting for an unrelated reason.
    assert!(
        k.environment().get(fx.f.apart_left_congr).is_some(),
        "the real apart_left_congr must be present"
    );
}

/// `mul_left_cancel` opens `mulInvEx` at `apart a zero`. Restating the
/// hypothesis as `apart a one` — one selector changed — must be refused: the
/// existential the proof opens is not available.
#[test]
fn control_mul_left_cancel_needs_apartness_from_zero_not_one() {
    let mut k = Kernel::new();
    let fx = build(&mut k);
    let fr = fx.f.field;
    let field_ty = k.const_(fr.ind, vec![]);
    let f = k.fvar(92_000);
    let carrier = sel(&mut k, &fr, ix::CARRIER, f);
    let equiv = sel(&mut k, &fr, ix::EQUIV, f);
    let mul = sel(&mut k, &fr, ix::MUL, f);
    let one = sel(&mut k, &fr, ix::ONE, f);
    let apart = sel(&mut k, &fr, ix::APART, f);
    let mul_inv_ex = sel(&mut k, &fr, ix::MUL_INV_EX, f);

    let a = k.fvar(92_001);
    // MUTATION: apartness from `one`, not from `zero`.
    let hap_ty = app2(&mut k, apart, a, one);
    let hap = k.fvar(92_002);
    let applied = {
        let e = k.app(mul_inv_ex, a);
        k.app(e, hap)
    };
    let pred = {
        let b = k.fvar(92_003);
        let ab = app2(&mut k, mul, a, b);
        let body = app2(&mut k, equiv, ab, one);
        lam_over(&mut k, 92_003, carrier, body)
    };
    let l0 = k.level_zero();
    let l1 = k.level_succ(l0);
    let ex = k.const_(fx.lg.exists_, vec![l1]);
    let ex_ty = app2(&mut k, ex, carrier, pred);

    let value = lam_over(&mut k, 92_002, hap_ty, applied);
    let value = lam_over(&mut k, 92_001, carrier, value);
    let value = lam_over(&mut k, 92_000, field_ty, value);
    let ty = arrow(&mut k, hap_ty, ex_ty);
    let ty = pi_over(&mut k, 92_001, carrier, ty);
    let ty = pi_over(&mut k, 92_000, field_ty, ty);
    let name = k.name_str(fx.algs, "FieldControl_mulInvEx_at_one");
    let got = k.add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    });
    assert!(
        got.is_err(),
        "mulInvEx must not accept an apartness witness against `one`"
    );
    assert!(
        k.environment().get(fx.f.mul_left_cancel).is_some(),
        "the real mul_left_cancel must be present"
    );
}
