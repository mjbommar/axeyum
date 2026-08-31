//! Proof-term tests for the logical prelude (ADR-0036, the P3.7 foundation).
//!
//! These tests are the real deliverable: they **build proof terms** with the
//! kernel and `infer` them to the proposition they prove. A test passes only if
//! the trusted type-checker genuinely accepts the proof — exactly what
//! Alethe→Lean reconstruction will do. Covered proofs: and-introduction,
//! and-elimination (left/right), or-introduction + or case-analysis,
//! `Eq.refl` + `Eq` transport (symmetry, which also ι-reduces on `refl`), modus
//! ponens, ex-falso via `False.rec`, and an `And.comm`-style composite built
//! from the smaller pieces.
//!
//! Convention for the abstract propositions: `A`, `B`, `C : Prop` are declared
//! as axioms (so they are genuine `Const`s of type `Prop`), and hypotheses
//! `ha : A`, `hb : B` are axioms too. A proof "checks" when `infer` returns the
//! expected proposition (compared with `def_eq`, since the kernel may return a
//! β/ι-equal but not syntactically identical normal form).
#![allow(clippy::similar_names, clippy::many_single_char_names)]

use crate::env::Declaration;
use crate::expr::ExprNode;
use crate::prelude::{RecField, RecursiveDatatypeFamily};
use crate::{BinderInfo, Kernel, LogicPrelude, build_logic_prelude};

fn apply_all(
    k: &mut Kernel,
    mut function: crate::ExprId,
    arguments: &[crate::ExprId],
) -> crate::ExprId {
    for &argument in arguments {
        function = k.app(function, argument);
    }
    function
}

fn lam_fvar(k: &mut Kernel, fvar: u64, ty: crate::ExprId, body: crate::ExprId) -> crate::ExprId {
    let body = k.abstract_fvars(body, &[fvar]);
    let anon = k.anon();
    k.lam(anon, ty, body, BinderInfo::Default)
}

fn pi_fvar(k: &mut Kernel, fvar: u64, ty: crate::ExprId, body: crate::ExprId) -> crate::ExprId {
    let body = k.abstract_fvars(body, &[fvar]);
    let anon = k.anon();
    k.pi(anon, ty, body, BinderInfo::Default)
}

// `LogicPrelude` grew past clippy's by-value size threshold once the
// `Decidable` infrastructure was added; it is `Copy` and cheap to move, so
// this is a size-lint override, not a real inefficiency.
#[allow(clippy::large_types_passed_by_value)]
fn empty_relation(k: &mut Kernel, p: LogicPrelude, carrier: crate::ExprId) -> crate::ExprId {
    let anon = k.anon();
    let false_prop = k.const_(p.false_, vec![]);
    let inner = k.lam(anon, carrier, false_prop, BinderInfo::Default);
    k.lam(anon, carrier, inner, BinderInfo::Default)
}

#[allow(clippy::large_types_passed_by_value)]
fn empty_well_founded(
    k: &mut Kernel,
    p: LogicPrelude,
    carrier: crate::ExprId,
    carrier_level: crate::LevelId,
    relation: crate::ExprId,
) -> crate::ExprId {
    let value_fvar = 30_000;
    let predecessor_fvar = 30_001;
    let impossible_fvar = 30_002;
    let motive_proof_fvar = 30_003;
    let value = k.fvar(value_fvar);
    let predecessor = k.fvar(predecessor_fvar);
    let impossible = k.fvar(impossible_fvar);
    let false_prop = k.const_(p.false_, vec![]);
    let acc = k.const_(p.acc, vec![carrier_level]);
    let accessible_predecessor = apply_all(k, acc, &[carrier, relation, predecessor]);
    let false_motive = lam_fvar(k, motive_proof_fvar, false_prop, accessible_predecessor);
    let zero_level = k.level_zero();
    let false_rec = k.const_(p.false_rec, vec![zero_level]);
    let absurd = apply_all(k, false_rec, &[false_motive, impossible]);
    let relation_proof_ty = apply_all(k, relation, &[predecessor, value]);
    let with_impossible = lam_fvar(k, impossible_fvar, relation_proof_ty, absurd);
    let no_predecessors = lam_fvar(k, predecessor_fvar, carrier, with_impossible);
    let acc_intro = k.const_(p.acc_intro, vec![carrier_level]);
    let accessible = apply_all(k, acc_intro, &[carrier, relation, value, no_predecessors]);
    lam_fvar(k, value_fvar, carrier, accessible)
}

struct WellFoundedFixExample {
    p: LogicPrelude,
    zero_level: crate::LevelId,
    one_level: crate::LevelId,
    carrier: crate::ExprId,
    point: crate::ExprId,
    nat: crate::ExprId,
    zero: crate::ExprId,
    one: crate::ExprId,
    relation: crate::ExprId,
    well_founded: crate::ExprId,
    family: crate::ExprId,
    step: crate::ExprId,
    fix: crate::ExprId,
    computed: crate::ExprId,
}

fn well_founded_fix_example(k: &mut Kernel) -> WellFoundedFixExample {
    let p = build_logic_prelude(k).expect("logic prelude must build");
    let zero_level = k.level_zero();
    let one_level = k.level_succ(zero_level);
    let carrier = k.const_(p.true_, vec![]);
    let point = k.const_(p.true_intro, vec![]);
    let nat = k.const_(p.nat, vec![]);
    let zero = k.const_(p.nat_zero, vec![]);
    let successor = k.const_(p.nat_succ, vec![]);
    let one = k.app(successor, zero);
    let relation = empty_relation(k, p, carrier);
    let well_founded = empty_well_founded(k, p, carrier, zero_level, relation);
    let family = lam_fvar(k, 31_000, carrier, nat);
    let step_value = k.fvar(31_001);
    let step_predecessor = k.fvar(31_002);
    let relation_proof_ty = apply_all(k, relation, &[step_predecessor, step_value]);
    let recursive_at_relation = pi_fvar(k, 31_003, relation_proof_ty, nat);
    let recursive_values = pi_fvar(k, 31_002, carrier, recursive_at_relation);
    let step_with_recursive = lam_fvar(k, 31_004, recursive_values, one);
    let step = lam_fvar(k, 31_001, carrier, step_with_recursive);
    let fix = k.const_(p.well_founded_fix, vec![zero_level, one_level]);
    let computed = apply_all(
        k,
        fix,
        &[carrier, relation, family, well_founded, step, point],
    );
    WellFoundedFixExample {
        p,
        zero_level,
        one_level,
        carrier,
        point,
        nat,
        zero,
        one,
        relation,
        well_founded,
        family,
        step,
        fix,
        computed,
    }
}

/// A test fixture: a kernel with the prelude plus abstract `A, B, C : Prop` and
/// `ha : A`, `hb : B` axioms.
struct Fixture {
    k: Kernel,
    p: LogicPrelude,
    a: crate::NameId,
    b: crate::NameId,
    c: crate::NameId,
    ha: crate::NameId,
    hb: crate::NameId,
}

fn fixture() -> Fixture {
    let mut k = Kernel::new();
    let p = build_logic_prelude(&mut k).expect("logic prelude must build");
    let anon = k.anon();

    // A, B, C : Prop.
    let prop_axiom = |k: &mut Kernel, s: &str| -> crate::NameId {
        let name = k.name_str(anon, s);
        let prop = k.sort_zero();
        k.add_declaration(Declaration::Axiom {
            name,
            uparams: vec![],
            ty: prop,
        })
        .unwrap();
        name
    };
    let a = prop_axiom(&mut k, "A");
    let b = prop_axiom(&mut k, "B");
    let c = prop_axiom(&mut k, "C");

    // ha : A, hb : B.
    let a_const = k.const_(a, vec![]);
    let b_const = k.const_(b, vec![]);
    let ha = k.name_str(anon, "ha");
    k.add_declaration(Declaration::Axiom {
        name: ha,
        uparams: vec![],
        ty: a_const,
    })
    .unwrap();
    let hb = k.name_str(anon, "hb");
    k.add_declaration(Declaration::Axiom {
        name: hb,
        uparams: vec![],
        ty: b_const,
    })
    .unwrap();

    Fixture {
        k,
        p,
        a,
        b,
        c,
        ha,
        hb,
    }
}

impl Fixture {
    fn a_const(&mut self) -> crate::ExprId {
        self.k.const_(self.a, vec![])
    }
    fn b_const(&mut self) -> crate::ExprId {
        self.k.const_(self.b, vec![])
    }
    fn c_const(&mut self) -> crate::ExprId {
        self.k.const_(self.c, vec![])
    }
    fn ha_const(&mut self) -> crate::ExprId {
        self.k.const_(self.ha, vec![])
    }
    fn hb_const(&mut self) -> crate::ExprId {
        self.k.const_(self.hb, vec![])
    }
    /// `And A B` (the proposition).
    fn and_ab(&mut self) -> crate::ExprId {
        let and = self.k.const_(self.p.and, vec![]);
        let a = self.a_const();
        let b = self.b_const();
        let e = self.k.app(and, a);
        self.k.app(e, b)
    }
}

/// The prelude admits: every declaration type-checked through the trusted gate,
/// and the expected names are present with the expected recursor metadata. A
/// green build of `build_logic_prelude` already *is* the well-formedness proof;
/// this asserts the environment shape.
#[test]
#[allow(clippy::too_many_lines)]
fn prelude_admits_all_declarations() {
    let mut k = Kernel::new();
    let p = build_logic_prelude(&mut k).expect("logic prelude must build");

    for name in [
        p.true_,
        p.true_intro,
        p.true_rec,
        p.false_,
        p.false_rec,
        p.and,
        p.and_intro,
        p.and_rec,
        p.or,
        p.or_inl,
        p.or_inr,
        p.or_rec,
        p.iff,
        p.iff_intro,
        p.iff_rec,
        p.eq,
        p.eq_refl,
        p.eq_rec,
        p.acc,
        p.acc_intro,
        p.acc_rec,
        p.acc_inv,
        p.well_founded,
        p.well_founded_fix,
        p.well_founded_fix_eq,
        p.not,
        p.and_left,
        p.and_right,
        p.or_elim,
        p.or_resolve_left,
        p.or_resolve_right,
        p.iff_mp,
        p.iff_mpr,
        p.congr_fun_prime,
        p.absurd,
        p.mt,
        p.not_not_intro,
        p.noncontradiction,
        p.not_not_not,
        p.demorgan_not_or,
        p.demorgan_not_or_converse,
        p.demorgan_or_not_and,
        p.not_not_em,
        p.dne_of_em,
        p.em_of_dne,
        p.peirce_of_em,
        p.em_of_peirce,
        p.not_not_not_intro,
        p.not_not_and,
        p.not_not_imp,
        p.bool_false_ne_true,
        p.bool_true_ne_false,
        p.decidable,
        p.decidable_is_false,
        p.decidable_is_true,
        p.decidable_rec,
        p.decide,
        p.of_decide_eq_true,
        p.of_decide_eq_false,
        p.decidable_em,
        p.decidable_by_cases,
        p.decidable_pred,
    ] {
        assert!(
            k.environment().contains(name),
            "prelude should declare {}",
            k.display_name(name)
        );
    }

    // False is a genuine zero-constructor inductive.
    match k.environment().get(p.false_).unwrap() {
        Declaration::Inductive { ctor_names, .. } => {
            assert!(ctor_names.is_empty(), "False has no constructors");
        }
        _ => panic!("False should be an inductive"),
    }
    // And has 2 params, 0 indices, 1 minor (intro).
    match k.environment().get(p.and_rec).unwrap() {
        Declaration::Recursor {
            num_params,
            num_indices,
            num_minors,
            ..
        } => {
            assert_eq!(*num_params, 2);
            assert_eq!(*num_indices, 0);
            assert_eq!(*num_minors, 1);
        }
        _ => panic!("And.rec should be a recursor"),
    }
    // Or has 2 minors (inl, inr).
    match k.environment().get(p.or_rec).unwrap() {
        Declaration::Recursor {
            num_minors,
            uparams,
            ..
        } => {
            assert_eq!(*num_minors, 2);
            assert!(uparams.is_empty(), "Or eliminates only into Prop");
        }
        _ => panic!("Or.rec should be a recursor"),
    }
    // Eq has 2 params and 1 index.
    match k.environment().get(p.eq_rec).unwrap() {
        Declaration::Recursor {
            num_params,
            num_indices,
            uparams,
            ..
        } => {
            assert_eq!(*num_params, 2);
            assert_eq!(*num_indices, 1);
            assert_eq!(uparams.len(), 2, "Eq retains large elimination");
        }
        _ => panic!("Eq.rec should be a recursor"),
    }
    // Exists is declared with its constructor and recursor.
    for name in [p.exists_, p.exists_intro, p.exists_rec] {
        assert!(
            k.environment().contains(name),
            "prelude should declare {}",
            k.display_name(name)
        );
    }
    // Exists has 2 params, 0 indices, 1 minor (intro).
    match k.environment().get(p.exists_rec).unwrap() {
        Declaration::Recursor {
            num_params,
            num_indices,
            num_minors,
            uparams,
            ..
        } => {
            assert_eq!(*num_params, 2);
            assert_eq!(*num_indices, 0);
            assert_eq!(*num_minors, 1);
            assert_eq!(uparams.len(), 1, "Exists retains only its own universe");
        }
        _ => panic!("Exists.rec should be a recursor"),
    }
    // Acc has two parameters, one index, one minor, and retains large
    // elimination because its sole constructor fields are proofs.
    match k.environment().get(p.acc_rec).unwrap() {
        Declaration::Recursor {
            num_params,
            num_indices,
            num_minors,
            uparams,
            ..
        } => {
            assert_eq!(*num_params, 2);
            assert_eq!(*num_indices, 1);
            assert_eq!(*num_minors, 1);
            assert_eq!(uparams.len(), 2, "Acc retains large elimination");
        }
        _ => panic!("Acc.rec should be a recursor"),
    }

    for (name, expected_uparams) in [
        (p.true_rec, 1),
        (p.false_rec, 1),
        (p.and_rec, 1),
        (p.iff_rec, 1),
    ] {
        match k.environment().get(name).expect("prelude recursor") {
            Declaration::Recursor { uparams, .. } => {
                assert_eq!(uparams.len(), expected_uparams);
            }
            _ => panic!("expected recursor"),
        }
    }

    // Decidable has 1 param, 0 indices, 2 minors (isFalse, isTrue), and
    // retains large elimination -- it lives in `Type`, not `Prop`, unlike
    // `Or` above.
    match k.environment().get(p.decidable_rec).unwrap() {
        Declaration::Recursor {
            num_params,
            num_indices,
            num_minors,
            uparams,
            ..
        } => {
            assert_eq!(*num_params, 1);
            assert_eq!(*num_indices, 0);
            assert_eq!(*num_minors, 2);
            assert_eq!(uparams.len(), 1, "Decidable retains large elimination");
        }
        _ => panic!("Decidable.rec should be a recursor"),
    }
}

/// The actual prelude `Acc.rec`, not merely a lookalike construct-matrix row,
/// computes through an empty predecessor relation. The same proof also checks
/// that `WellFounded` unfolds to pointwise accessibility and that an index
/// mutation cannot reuse the accepted accessibility proof.
#[test]
#[allow(clippy::too_many_lines)]
fn accessibility_recursion_computes_and_retains_its_index() {
    let mut k = Kernel::new();
    let p = build_logic_prelude(&mut k).expect("logic prelude must build");
    let anon = k.anon();
    let zero_level = k.level_zero();
    let one_level = k.level_succ(zero_level);
    let prop = k.sort_zero();
    let nat = k.const_(p.nat, vec![]);
    let zero = k.const_(p.nat_zero, vec![]);
    let false_prop = k.const_(p.false_, vec![]);
    let true_prop = k.const_(p.true_, vec![]);

    // emptyRelation := fun _ _ : Nat => False.
    let relation = {
        let inner = k.lam(anon, nat, false_prop, BinderInfo::Default);
        k.lam(anon, nat, inner, BinderInfo::Default)
    };
    let acc_const = k.const_(p.acc, vec![one_level]);
    let acc_at = |k: &mut Kernel, value| apply_all(k, acc_const, &[nat, relation, value]);

    // h : ∀ y, emptyRelation y zero → Acc emptyRelation y, by False.rec.
    let predecessor_fvar = 10_000;
    let impossible_fvar = 10_001;
    let predecessor = k.fvar(predecessor_fvar);
    let impossible = k.fvar(impossible_fvar);
    let relation_proof_ty = apply_all(&mut k, relation, &[predecessor, zero]);
    let accessible_predecessor = acc_at(&mut k, predecessor);
    let false_motive_fvar = 10_002;
    let false_motive = lam_fvar(
        &mut k,
        false_motive_fvar,
        false_prop,
        accessible_predecessor,
    );
    let false_rec = k.const_(p.false_rec, vec![zero_level]);
    let absurd = apply_all(&mut k, false_rec, &[false_motive, impossible]);
    let with_impossible = lam_fvar(&mut k, impossible_fvar, relation_proof_ty, absurd);
    let no_predecessors = lam_fvar(&mut k, predecessor_fvar, nat, with_impossible);

    let acc_intro = k.const_(p.acc_intro, vec![one_level]);
    let accessible_zero = apply_all(&mut k, acc_intro, &[nat, relation, zero, no_predecessors]);
    let accessible_zero_ty = acc_at(&mut k, zero);
    let inferred_accessible = k
        .infer(accessible_zero)
        .expect("the empty relation should make zero accessible");
    assert!(k.def_eq(inferred_accessible, accessible_zero_ty));

    // motive := fun _ _ => Prop; minor := fun _ _ _ => True.
    let motive_index_fvar = 10_010;
    let motive_proof_fvar = 10_011;
    let motive_index = k.fvar(motive_index_fvar);
    let motive_proof_ty = acc_at(&mut k, motive_index);
    let motive_with_proof = lam_fvar(&mut k, motive_proof_fvar, motive_proof_ty, prop);
    let motive = lam_fvar(&mut k, motive_index_fvar, nat, motive_with_proof);

    let minor_index_fvar = 10_020;
    let minor_field_fvar = 10_021;
    let minor_ih_fvar = 10_022;
    let minor_index = k.fvar(minor_index_fvar);
    let field_predecessor_fvar = 10_023;
    let field_relation_fvar = 10_024;
    let field_predecessor = k.fvar(field_predecessor_fvar);
    let field_relation_ty = apply_all(&mut k, relation, &[field_predecessor, minor_index]);
    let field_result = acc_at(&mut k, field_predecessor);
    let field_with_relation = pi_fvar(&mut k, field_relation_fvar, field_relation_ty, field_result);
    let recursive_field_ty = pi_fvar(&mut k, field_predecessor_fvar, nat, field_with_relation);

    let ih_predecessor_fvar = 10_025;
    let ih_relation_fvar = 10_026;
    let ih_predecessor = k.fvar(ih_predecessor_fvar);
    let ih_relation_ty = apply_all(&mut k, relation, &[ih_predecessor, minor_index]);
    let ih_with_relation = pi_fvar(&mut k, ih_relation_fvar, ih_relation_ty, prop);
    let recursive_hypothesis_ty = pi_fvar(&mut k, ih_predecessor_fvar, nat, ih_with_relation);
    let minor_with_ih = lam_fvar(&mut k, minor_ih_fvar, recursive_hypothesis_ty, true_prop);
    let minor_with_field = lam_fvar(&mut k, minor_field_fvar, recursive_field_ty, minor_with_ih);
    let minor = lam_fvar(&mut k, minor_index_fvar, nat, minor_with_field);

    let acc_rec = k.const_(p.acc_rec, vec![one_level, one_level]);
    let computed = apply_all(
        &mut k,
        acc_rec,
        &[nat, relation, motive, minor, zero, accessible_zero],
    );
    let inferred = k.infer(computed).expect("Acc.rec application should infer");
    assert!(k.def_eq(inferred, prop), "Acc.rec should return a Prop");
    assert!(
        k.def_eq(computed, true_prop),
        "Acc.rec should iota-reduce through Acc.intro"
    );

    let well_founded = k.const_(p.well_founded, vec![one_level]);
    let well_founded_empty = apply_all(&mut k, well_founded, &[nat, relation]);
    let arbitrary_fvar = 10_030;
    let arbitrary = k.fvar(arbitrary_fvar);
    let expected_body = acc_at(&mut k, arbitrary);
    let expected_well_founded = pi_fvar(&mut k, arbitrary_fvar, nat, expected_body);
    assert!(
        k.def_eq(well_founded_empty, expected_well_founded),
        "WellFounded should unfold to pointwise Acc"
    );

    let successor = k.const_(p.nat_succ, vec![]);
    let one = k.app(successor, zero);
    let wrong_index_ty = acc_at(&mut k, one);
    let wrong_name = k.name_str(anon, "acc_wrong_index");
    let error = k
        .add_declaration(Declaration::Theorem {
            name: wrong_name,
            uparams: vec![],
            ty: wrong_index_ty,
            value: accessible_zero,
        })
        .expect_err("an accessibility proof cannot change indices");
    assert!(!k.environment().contains(wrong_name));
    assert!(
        matches!(error, crate::KernelError::DeclarationValueMismatch { .. }),
        "unexpected rejection: {error:?}"
    );
}

/// `Acc.inv` extracts the predecessor index selected by the relation proof.
/// Test-only abstract accessibility isolates that theorem contract; the
/// prelude's separate axiom audit still requires the declaration itself to be
/// a checked theorem.
#[test]
fn accessibility_inverse_selects_the_related_predecessor() {
    let mut k = Kernel::new();
    let p = build_logic_prelude(&mut k).expect("logic prelude must build");
    let anon = k.anon();
    let zero_level = k.level_zero();
    let one_level = k.level_succ(zero_level);
    let bool_ty = k.const_(p.bool_, vec![]);
    let source = k.const_(p.bool_true, vec![]);
    let predecessor = k.const_(p.bool_false, vec![]);
    let true_prop = k.const_(p.true_, vec![]);
    let related = k.const_(p.true_intro, vec![]);
    let relation = {
        let inner = k.lam(anon, bool_ty, true_prop, BinderInfo::Default);
        k.lam(anon, bool_ty, inner, BinderInfo::Default)
    };
    let acc = k.const_(p.acc, vec![one_level]);
    let accessible_source_ty = apply_all(&mut k, acc, &[bool_ty, relation, source]);
    let accessible_source = k.name_str(anon, "abstract_accessible_source");
    k.add_declaration(Declaration::Axiom {
        name: accessible_source,
        uparams: vec![],
        ty: accessible_source_ty,
    })
    .expect("test fixture accessibility should admit");

    let inverse = k.const_(p.acc_inv, vec![one_level]);
    let accessible_source = k.const_(accessible_source, vec![]);
    let proof = apply_all(
        &mut k,
        inverse,
        &[
            bool_ty,
            relation,
            source,
            predecessor,
            accessible_source,
            related,
        ],
    );
    let expected = apply_all(&mut k, acc, &[bool_ty, relation, predecessor]);
    let inferred = k.infer(proof).expect("Acc.inv should infer");
    assert!(k.def_eq(inferred, expected));

    let wrong = apply_all(&mut k, acc, &[bool_ty, relation, source]);
    let wrong_name = k.name_str(anon, "acc_inv_wrong_predecessor");
    let error = k
        .add_declaration(Declaration::Theorem {
            name: wrong_name,
            uparams: vec![],
            ty: wrong,
            value: proof,
        })
        .expect_err("Acc.inv cannot change the selected predecessor index");
    assert!(
        matches!(error, crate::KernelError::DeclarationValueMismatch { .. }),
        "unexpected rejection: {error:?}"
    );
    assert!(!k.environment().contains(wrong_name));
}

#[test]
fn logic_prelude_with_accessibility_declares_no_axioms() {
    let mut k = Kernel::new();
    build_logic_prelude(&mut k).expect("logic prelude must build");
    // Checked against the WHOLE environment, not a hand-maintained list: this
    // is the base prelude (nothing built here depends on anything else), so a
    // scan finding no `Axiom`/`Opaque`/`Quotient` declaration ANYWHERE proves
    // every declaration's `axiom_footprint` is empty automatically -- there is
    // no assumed name left for any proof term to reach. Widened from
    // `Axiom`-only (matching `int_prelude_tests.rs`'s
    // `the_only_trusted_declarations_are_the_asserted_laws`, which also
    // treats `Opaque`/`Quotient` as "admitted without a checked proof body"):
    // measured 2026-08-26, this build has zero of all three (78 declarations:
    // 14 constructor, 10 definition, 11 inductive, 11 recursor, 32 theorem),
    // so this is a real, not vacuous, check.
    let assumed: Vec<_> = k
        .environment()
        .iter()
        .filter_map(|(_, declaration)| match declaration {
            Declaration::Axiom { name, .. }
            | Declaration::Opaque { name, .. }
            | Declaration::Quotient { name, .. } => Some(k.display_name(*name).to_string()),
            _ => None,
        })
        .collect();
    assert!(
        assumed.is_empty(),
        "logic prelude assumed declarations: {assumed:?}"
    );
}

/// The negation toolkit, the three valid De Morgan directions, and the
/// classical-principle interderivability theorems: every one of them must be
/// **present** (a name interned but never declared would pass an
/// `axiom_footprint` check vacuously) and every one of them must have an
/// **empty** `axiom_footprint` -- in particular, none of them may reach
/// `Classical.em`, `propext`, `funext`, or `Quot.sound`, none of which this
/// kernel declares anywhere.
#[test]
fn classical_equivalences_are_present_and_axiom_free() {
    let mut k = Kernel::new();
    let p = build_logic_prelude(&mut k).expect("logic prelude must build");

    for name in [
        p.not_not_intro,
        p.noncontradiction,
        p.not_not_not,
        p.demorgan_not_or,
        p.demorgan_not_or_converse,
        p.demorgan_or_not_and,
        p.not_not_em,
        p.dne_of_em,
        p.em_of_dne,
        p.peirce_of_em,
        p.em_of_peirce,
    ] {
        assert!(
            k.environment().contains(name),
            "prelude should declare {}",
            k.display_name(name)
        );
        let footprint = k.axiom_footprint(name);
        assert!(
            footprint.is_empty(),
            "{} is not axiom-free: {:?}",
            k.display_name(name),
            footprint
                .iter()
                .map(|n| k.display_name(*n).to_string())
                .collect::<Vec<_>>()
        );
    }
}

#[test]
fn accessibility_prelude_build_is_deterministic() {
    let render = |kernel: &mut Kernel| {
        let prelude = build_logic_prelude(kernel).expect("logic prelude must build");
        [
            prelude.acc,
            prelude.acc_intro,
            prelude.acc_rec,
            prelude.acc_inv,
            prelude.well_founded,
            prelude.well_founded_fix,
            prelude.well_founded_fix_eq,
        ]
        .into_iter()
        .map(|name| {
            let declaration = kernel
                .environment()
                .get(name)
                .expect("promised accessibility declaration");
            kernel.render_lean_decl(declaration)
        })
        .collect::<Vec<_>>()
    };
    let first = render(&mut Kernel::new());
    let second = render(&mut Kernel::new());
    assert_eq!(
        first, second,
        "accessibility declarations must repeat exactly"
    );
}

/// `WellFounded.fix` is universe-polymorphic and computes through the generic
/// `Acc.rec` path. A `Prop`-level carrier and `Type`-level result deliberately
/// distinguish its two universe arguments instead of testing only `u = v`.
#[test]
fn well_founded_fix_computes_across_universes() {
    let mut k = Kernel::new();
    let e = well_founded_fix_example(&mut k);
    let inferred = k.infer(e.computed).expect("WellFounded.fix should infer");
    assert!(k.def_eq(inferred, e.nat), "the result should have type Nat");
    assert!(
        k.def_eq(e.computed, e.one),
        "WellFounded.fix should delta/iota-reduce through the accessibility proof"
    );
    assert!(
        !k.def_eq(e.computed, e.zero),
        "the computation control must distinguish the selected step result"
    );
}

#[test]
fn well_founded_fix_equation_checks_and_rejects_a_changed_rhs() {
    let mut k = Kernel::new();
    let e = well_founded_fix_example(&mut k);
    let recursive_predecessor_fvar = 31_005;
    let recursive_relation_fvar = 31_006;
    let recursive_predecessor = k.fvar(recursive_predecessor_fvar);
    let recursive_relation_ty = apply_all(&mut k, e.relation, &[recursive_predecessor, e.point]);
    let fix_at_predecessor = apply_all(
        &mut k,
        e.fix,
        &[
            e.carrier,
            e.relation,
            e.family,
            e.well_founded,
            e.step,
            recursive_predecessor,
        ],
    );
    let recursive_with_relation = lam_fvar(
        &mut k,
        recursive_relation_fvar,
        recursive_relation_ty,
        fix_at_predecessor,
    );
    let recursive = lam_fvar(
        &mut k,
        recursive_predecessor_fvar,
        e.carrier,
        recursive_with_relation,
    );
    let unfolded = apply_all(&mut k, e.step, &[e.point, recursive]);
    let eq = k.const_(e.p.eq, vec![e.one_level]);
    let equation = apply_all(&mut k, eq, &[e.nat, e.computed, unfolded]);
    let fix_eq = k.const_(e.p.well_founded_fix_eq, vec![e.zero_level, e.one_level]);
    let equation_proof = apply_all(
        &mut k,
        fix_eq,
        &[
            e.carrier,
            e.relation,
            e.family,
            e.well_founded,
            e.step,
            e.point,
        ],
    );
    let inferred_equation = k
        .infer(equation_proof)
        .expect("WellFounded.fix_eq should infer");
    assert!(
        k.def_eq(inferred_equation, equation),
        "WellFounded.fix_eq should expose the generic unfolding equation"
    );

    let wrong_equation = apply_all(&mut k, eq, &[e.nat, e.computed, e.zero]);
    let anon = k.anon();
    let wrong_name = k.name_str(anon, "well_founded_fix_eq_wrong_rhs");
    let error = k
        .add_declaration(Declaration::Theorem {
            name: wrong_name,
            uparams: vec![],
            ty: wrong_equation,
            value: equation_proof,
        })
        .expect_err("fix_eq must not prove a changed right-hand side");
    assert!(
        matches!(error, crate::KernelError::DeclarationValueMismatch { .. }),
        "unexpected rejection: {error:?}"
    );
    assert!(!k.environment().contains(wrong_name));
}

/// `False.rec` (zero-constructor recursor) exists and its generated type
/// infer-checks to a `Sort` — confirming the kernel handles the ex-falso
/// eliminator (the empty-constructor recursor) rather than choking on it.
#[test]
fn false_rec_exists_and_self_checks() {
    let mut k = Kernel::new();
    let p = build_logic_prelude(&mut k).expect("logic prelude must build");
    assert!(k.environment().contains(p.false_rec));
    let rec_ty = k.environment().get(p.false_rec).unwrap().ty();
    let inferred = k.infer(rec_ty).unwrap();
    assert!(
        matches!(k.expr_node(inferred), ExprNode::Sort(_)),
        "False.rec type should infer to a Sort"
    );
    // It has zero minors (one per constructor; False has none).
    match k.environment().get(p.false_rec).unwrap() {
        Declaration::Recursor { num_minors, .. } => {
            assert_eq!(*num_minors, 0, "False.rec has no minor premises");
        }
        _ => panic!("False.rec should be a recursor"),
    }
}

/// **and-introduction**: `And.intro A B ha hb : And A B`. We build the proof
/// term and `infer` it; the inferred type is `And A B`.
#[test]
fn and_intro_checks() {
    let mut f = fixture();
    let a = f.a_const();
    let b = f.b_const();
    let ha = f.ha_const();
    let hb = f.hb_const();

    // And.intro A B ha hb.
    let intro = f.k.const_(f.p.and_intro, vec![]);
    let proof = {
        let e = f.k.app(intro, a);
        let e = f.k.app(e, b);
        let e = f.k.app(e, ha);
        f.k.app(e, hb)
    };
    let inferred = f.k.infer(proof).unwrap();
    let expected = f.and_ab();
    assert!(
        f.k.def_eq(inferred, expected),
        "And.intro A B ha hb : And A B"
    );
}

/// **and-elimination (left)**: the proof `fun (h : And A B) =>
/// And.rec A B (fun _ => A) (fun ha hb => ha) h` infers `And A B → A`. The motive
/// is the constant `A`, and the minor projects the first field.
#[test]
fn and_elim_left_checks() {
    let mut f = fixture();
    let a = f.a_const();
    let b = f.b_const();
    let and_ab = f.and_ab();

    // motive := fun (_ : And A B) => A.
    let anon = f.k.anon();
    let motive = f.k.lam(anon, and_ab, a, BinderInfo::Default);
    // minor := fun (ha : A) (hb : B) => ha   (ha is BVar 1).
    let minor = {
        let v1 = f.k.bvar(1);
        let inner = f.k.lam(anon, b, v1, BinderInfo::Default);
        f.k.lam(anon, a, inner, BinderInfo::Default)
    };
    // proof := fun (h : And A B) => And.rec.{0} A B motive minor h.
    // Elimination into Prop ⇒ v := 0.
    let z = f.k.level_zero();
    let proof = {
        let rec = f.k.const_(f.p.and_rec, vec![z]);
        let e = f.k.app(rec, a);
        let e = f.k.app(e, b);
        let e = f.k.app(e, motive);
        let e = f.k.app(e, minor);
        let h = f.k.bvar(0);
        let body = f.k.app(e, h);
        f.k.lam(anon, and_ab, body, BinderInfo::Default)
    };
    let inferred = f.k.infer(proof).unwrap();
    // Expected: And A B → A.
    let a2 = f.a_const();
    let and_ab2 = f.and_ab();
    let expected = f.k.pi(anon, and_ab2, a2, BinderInfo::Default);
    assert!(
        f.k.def_eq(inferred, expected),
        "and-elim-left : And A B → A"
    );
}

/// **and-elimination (right)**: same shape, projecting the second field:
/// `fun (h : And A B) => And.rec A B (fun _ => B) (fun ha hb => hb) h :
/// And A B → B`.
#[test]
fn and_elim_right_checks() {
    let mut f = fixture();
    let a = f.a_const();
    let b = f.b_const();
    let and_ab = f.and_ab();
    let anon = f.k.anon();

    let motive = f.k.lam(anon, and_ab, b, BinderInfo::Default);
    // minor := fun (ha : A) (hb : B) => hb   (hb is BVar 0).
    let minor = {
        let v0 = f.k.bvar(0);
        let inner = f.k.lam(anon, b, v0, BinderInfo::Default);
        f.k.lam(anon, a, inner, BinderInfo::Default)
    };
    let z = f.k.level_zero();
    let proof = {
        let rec = f.k.const_(f.p.and_rec, vec![z]);
        let e = f.k.app(rec, a);
        let e = f.k.app(e, b);
        let e = f.k.app(e, motive);
        let e = f.k.app(e, minor);
        let h = f.k.bvar(0);
        let body = f.k.app(e, h);
        f.k.lam(anon, and_ab, body, BinderInfo::Default)
    };
    let inferred = f.k.infer(proof).unwrap();
    let b2 = f.b_const();
    let and_ab2 = f.and_ab();
    let expected = f.k.pi(anon, and_ab2, b2, BinderInfo::Default);
    assert!(
        f.k.def_eq(inferred, expected),
        "and-elim-right : And A B → B"
    );
}

/// **or-introduction**: `Or.inl A B ha : Or A B`.
#[test]
fn or_inl_checks() {
    let mut f = fixture();
    let a = f.a_const();
    let b = f.b_const();
    let ha = f.ha_const();

    let inl = f.k.const_(f.p.or_inl, vec![]);
    let proof = {
        let e = f.k.app(inl, a);
        let e = f.k.app(e, b);
        f.k.app(e, ha)
    };
    let inferred = f.k.infer(proof).unwrap();
    // Expected: Or A B.
    let or = f.k.const_(f.p.or, vec![]);
    let a2 = f.a_const();
    let b2 = f.b_const();
    let expected = {
        let e = f.k.app(or, a2);
        f.k.app(e, b2)
    };
    assert!(f.k.def_eq(inferred, expected), "Or.inl A B ha : Or A B");
}

/// **or case-analysis**: `fun (h : Or A B) => Or.rec A B (fun _ => C) f g h`
/// infers `Or A B → C`, where `f : A → C` and `g : B → C` are abstract
/// eliminators (axioms). This is the disjunction eliminator checking.
#[test]
fn or_case_analysis_checks() {
    let mut f = fixture();
    let anon = f.k.anon();
    let a = f.a_const();
    let c = f.c_const();

    // f : A → C, g : B → C  (axioms).
    let ac = f.k.pi(anon, a, c, BinderInfo::Default);
    let f_name = f.k.name_str(anon, "f");
    f.k.add_declaration(Declaration::Axiom {
        name: f_name,
        uparams: vec![],
        ty: ac,
    })
    .unwrap();
    let bc = {
        let b2 = f.b_const();
        let c2 = f.c_const();
        f.k.pi(anon, b2, c2, BinderInfo::Default)
    };
    let g_name = f.k.name_str(anon, "g");
    f.k.add_declaration(Declaration::Axiom {
        name: g_name,
        uparams: vec![],
        ty: bc,
    })
    .unwrap();

    // Or A B.
    let or = f.k.const_(f.p.or, vec![]);
    let a3 = f.a_const();
    let b3 = f.b_const();
    let or_ab = {
        let e = f.k.app(or, a3);
        f.k.app(e, b3)
    };
    // motive := fun (_ : Or A B) => C.
    let c3 = f.c_const();
    let motive = f.k.lam(anon, or_ab, c3, BinderInfo::Default);
    // minor_inl := fun (ha : A) => f ha ;  minor_inr := fun (hb : B) => g hb.
    let f_const = f.k.const_(f_name, vec![]);
    let a4 = f.a_const();
    let minor_inl = {
        let v0 = f.k.bvar(0);
        let body = f.k.app(f_const, v0);
        f.k.lam(anon, a4, body, BinderInfo::Default)
    };
    let g_const = f.k.const_(g_name, vec![]);
    let b4 = f.b_const();
    let minor_inr = {
        let v0 = f.k.bvar(0);
        let body = f.k.app(g_const, v0);
        f.k.lam(anon, b4, body, BinderInfo::Default)
    };

    // proof := fun (h : Or A B) => Or.rec A B motive minor_inl minor_inr h.
    // `Or.rec` has no elimination-universe parameter: a two-constructor Prop
    // can eliminate only into Prop.
    let a5 = f.a_const();
    let b5 = f.b_const();
    let or_ab2 = {
        let or2 = f.k.const_(f.p.or, vec![]);
        let e = f.k.app(or2, a5);
        f.k.app(e, b5)
    };
    let proof = {
        let rec = f.k.const_(f.p.or_rec, vec![]);
        let e = f.k.app(rec, a5);
        let e = f.k.app(e, b5);
        let e = f.k.app(e, motive);
        let e = f.k.app(e, minor_inl);
        let e = f.k.app(e, minor_inr);
        let h = f.k.bvar(0);
        let body = f.k.app(e, h);
        f.k.lam(anon, or_ab2, body, BinderInfo::Default)
    };
    let inferred = f.k.infer(proof).unwrap();
    // Expected: Or A B → C.
    let c4 = f.c_const();
    let a6 = f.a_const();
    let b6 = f.b_const();
    let or_ab3 = {
        let or3 = f.k.const_(f.p.or, vec![]);
        let e = f.k.app(or3, a6);
        f.k.app(e, b6)
    };
    let expected = f.k.pi(anon, or_ab3, c4, BinderInfo::Default);
    assert!(
        f.k.def_eq(inferred, expected),
        "or case-analysis : Or A B → C"
    );
}

/// **`Eq.refl`**: `Eq.refl A ha : Eq A ha ha` for a carrier and a point.
/// Uses `A : Sort 1` (a `Type`) and `x : A` so the universe `u := 1`.
#[test]
fn eq_refl_checks() {
    let mut k = Kernel::new();
    let p = build_logic_prelude(&mut k).expect("logic prelude must build");
    let anon = k.anon();

    // A : Sort 1, x : A.
    let one = {
        let z = k.level_zero();
        k.level_succ(z)
    };
    let s1 = k.sort(one);
    let a_carrier = k.name_str(anon, "Carrier");
    k.add_declaration(Declaration::Axiom {
        name: a_carrier,
        uparams: vec![],
        ty: s1,
    })
    .unwrap();
    let big_a = k.const_(a_carrier, vec![]);
    let x_name = k.name_str(anon, "x");
    k.add_declaration(Declaration::Axiom {
        name: x_name,
        uparams: vec![],
        ty: big_a,
    })
    .unwrap();
    let x = k.const_(x_name, vec![]);

    // Eq.refl.{1} A x : Eq.{1} A x x.
    let refl = k.const_(p.eq_refl, vec![one]);
    let proof = {
        let e = k.app(refl, big_a);
        k.app(e, x)
    };
    let inferred = k.infer(proof).unwrap();
    // Expected: Eq A x x.
    let eq = k.const_(p.eq, vec![one]);
    let expected = {
        let e = k.app(eq, big_a);
        let e = k.app(e, x);
        k.app(e, x)
    };
    assert!(k.def_eq(inferred, expected), "Eq.refl A x : Eq A x x");
}

/// **`Eq` transport (symmetry)**: from `h : Eq A x y` derive `Eq A y x`. We
/// build `Eq.symm := fun (y) (h : Eq A x y) => Eq.rec A x (motive) (refl A x) y h`
/// with `motive := fun (b) (_ : Eq A x b) => Eq A b x`, and check it type-checks.
/// We then check the eliminator **computes** on `refl`: applied to `x` and
/// `Eq.refl A x`, it ι-reduces to `Eq.refl A x`.
#[test]
fn eq_symm_checks_and_computes_on_refl() {
    let mut k = Kernel::new();
    let p = build_logic_prelude(&mut k).expect("logic prelude must build");
    let anon = k.anon();

    // A : Sort 1, x : A.
    let one = {
        let z = k.level_zero();
        k.level_succ(z)
    };
    let s1 = k.sort(one);
    let a_carrier = k.name_str(anon, "Carrier");
    k.add_declaration(Declaration::Axiom {
        name: a_carrier,
        uparams: vec![],
        ty: s1,
    })
    .unwrap();
    let big_a = k.const_(a_carrier, vec![]);
    let x_name = k.name_str(anon, "x");
    k.add_declaration(Declaration::Axiom {
        name: x_name,
        uparams: vec![],
        ty: big_a,
    })
    .unwrap();
    let x = k.const_(x_name, vec![]);

    let eq = |k: &mut Kernel, ty: crate::ExprId, l: crate::ExprId, r: crate::ExprId| {
        let e = k.const_(p.eq, vec![one]);
        let e = k.app(e, ty);
        let e = k.app(e, l);
        k.app(e, r)
    };

    // motive := fun (b : A) (_ : Eq A x b) => Eq A b x.
    //   Under binders b, h (innermost = 0): b = BVar 1 in the body `Eq A b x`,
    //   b = BVar 0 in the h domain `Eq A x b`.
    let motive = {
        let b1 = k.bvar(1);
        let eq_bx = eq(&mut k, big_a, b1, x);
        let b0 = k.bvar(0);
        let eq_xb = eq(&mut k, big_a, x, b0);
        let inner_h = k.lam(anon, eq_xb, eq_bx, BinderInfo::Default);
        k.lam(anon, big_a, inner_h, BinderInfo::Default)
    };
    // refl_case := Eq.refl A x : Eq A x x = motive x (refl A x) (after β).
    let refl_ax = {
        let refl = k.const_(p.eq_refl, vec![one]);
        let e = k.app(refl, big_a);
        k.app(e, x)
    };

    // The transport applied to x and (refl A x):
    //   Eq.rec.{0,1} A x motive (refl A x) x (refl A x)  ι→  refl A x.
    let z = k.level_zero();
    let app = {
        let rec = k.const_(p.eq_rec, vec![z, one]);
        let e = k.app(rec, big_a);
        let e = k.app(e, x);
        let e = k.app(e, motive);
        let e = k.app(e, refl_ax);
        let e = k.app(e, x); // index arg b := x
        k.app(e, refl_ax) // major
    };
    // It type-checks to `motive x (refl A x)` = `Eq A x x` (β/ι-equal).
    let inferred = k.infer(app).unwrap();
    let eq_xx = eq(&mut k, big_a, x, x);
    assert!(
        k.def_eq(inferred, eq_xx),
        "transport on refl proves Eq A x x"
    );
    // And it ι-reduces to `refl A x`.
    assert_eq!(k.whnf(app), refl_ax, "Eq.rec on refl ι→ the refl_case");
}

/// **modus ponens**: `fun (h : A → B) (ha : A) => h ha : (A → B) → A → B`.
/// Trivial but foundational — function application is the proof rule.
#[test]
fn modus_ponens_checks() {
    let mut f = fixture();
    let anon = f.k.anon();
    let a = f.a_const();
    let b = f.b_const();

    // A → B.
    let ab = f.k.pi(anon, a, b, BinderInfo::Default);
    // proof := fun (h : A → B) (ha : A) => h ha.  h = BVar 1, ha = BVar 0.
    let a2 = f.a_const();
    let proof = {
        let h = f.k.bvar(1);
        let ha = f.k.bvar(0);
        let body = f.k.app(h, ha);
        let inner = f.k.lam(anon, a2, body, BinderInfo::Default);
        f.k.lam(anon, ab, inner, BinderInfo::Default)
    };
    let inferred = f.k.infer(proof).unwrap();
    // Expected: (A → B) → A → B.
    let a3 = f.a_const();
    let b3 = f.b_const();
    let ab2 = f.k.pi(anon, a3, b3, BinderInfo::Default);
    let a4 = f.a_const();
    let b4 = f.b_const();
    let ab3 = f.k.pi(anon, a4, b4, BinderInfo::Default);
    let expected = f.k.pi(anon, ab2, ab3, BinderInfo::Default);
    assert!(
        f.k.def_eq(inferred, expected),
        "modus ponens : (A → B) → A → B"
    );
}

/// **ex-falso** via `False.rec`: `fun (h : False) => False.rec (fun _ => C) h`
/// infers `False → C`. The zero-constructor recursor takes only the motive and
/// the major (no minors), so it eliminates any `False` into any `C`.
#[test]
fn ex_falso_checks() {
    let mut f = fixture();
    let anon = f.k.anon();
    let c = f.c_const();
    let false_const = f.k.const_(f.p.false_, vec![]);

    // motive := fun (_ : False) => C.
    let motive = f.k.lam(anon, false_const, c, BinderInfo::Default);
    // proof := fun (h : False) => False.rec.{0} motive h.
    let z = f.k.level_zero();
    let false_const2 = f.k.const_(f.p.false_, vec![]);
    let proof = {
        let rec = f.k.const_(f.p.false_rec, vec![z]);
        let e = f.k.app(rec, motive);
        let h = f.k.bvar(0);
        let body = f.k.app(e, h);
        f.k.lam(anon, false_const2, body, BinderInfo::Default)
    };
    let inferred = f.k.infer(proof).unwrap();
    // Expected: False → C.
    let c2 = f.c_const();
    let false_const3 = f.k.const_(f.p.false_, vec![]);
    let expected = f.k.pi(anon, false_const3, c2, BinderInfo::Default);
    assert!(f.k.def_eq(inferred, expected), "ex-falso : False → C");
}

/// **`True.intro`**: the trivial proof `True.intro : True` checks.
#[test]
fn true_intro_checks() {
    let mut k = Kernel::new();
    let p = build_logic_prelude(&mut k).expect("logic prelude must build");
    let intro = k.const_(p.true_intro, vec![]);
    let inferred = k.infer(intro).unwrap();
    let true_const = k.const_(p.true_, vec![]);
    assert!(k.def_eq(inferred, true_const), "True.intro : True");
}

/// **`Not` unfolds**: `Not A` is def-eq to `A → False` (the definition
/// δ-unfolds), so a proof `fun (h : Not A) (ha : A) => h ha : Not A → A → False`
/// checks — `Not` is genuinely the function-to-`False`.
#[test]
fn not_unfolds_to_arrow_false() {
    let mut f = fixture();
    let anon = f.k.anon();
    let a = f.a_const();

    // Not A.
    let not = f.k.const_(f.p.not, vec![]);
    let not_a = f.k.app(not, a);
    // A → False  (what Not A should unfold to).
    let a2 = f.a_const();
    let false_const = f.k.const_(f.p.false_, vec![]);
    let arrow_false = f.k.pi(anon, a2, false_const, BinderInfo::Default);
    assert!(
        f.k.def_eq(not_a, arrow_false),
        "Not A def-eq A → False (δ-unfold)"
    );

    // proof := fun (h : Not A) (ha : A) => h ha : Not A → A → False.
    let a3 = f.a_const();
    let proof = {
        let h = f.k.bvar(1);
        let ha = f.k.bvar(0);
        let body = f.k.app(h, ha);
        let inner = f.k.lam(anon, a3, body, BinderInfo::Default);
        let not2 = f.k.const_(f.p.not, vec![]);
        let a4 = f.a_const();
        let not_a2 = f.k.app(not2, a4);
        f.k.lam(anon, not_a2, inner, BinderInfo::Default)
    };
    assert!(f.k.infer(proof).is_ok(), "Not-application proof checks");
}

/// **Composite proof — `And.comm`**: `fun (h : And A B) =>
/// And.intro B A (and-elim-right h) (and-elim-left h) : And A B → And B A`.
/// A genuine multi-step proof assembled from the pieces: it eliminates the
/// hypothesis twice and re-introduces the conjunction with the operands swapped.
/// The kernel verifies the whole term.
#[test]
fn and_comm_composite_checks() {
    let mut f = fixture();
    let anon = f.k.anon();
    let z = f.k.level_zero();

    // Helper: and-elim that, given the conjunction term `h_expr : And A B`,
    // projects field `which` (0 = left/A, 1 = right/B) by applying And.rec
    // directly (no outer lambda — we want the projected proof of A or B).
    //   And.rec A B (fun _ => P) (fun ha hb => field) h_expr
    // where P, field depend on `which`.
    // We inline both projections below.

    // The conjunction proposition `And A B` (rebuilt fresh as needed).
    let and_ab = f.and_ab();

    // h : And A B is the lambda's BVar 0.
    // and-elim-right h : B.
    let a1 = f.a_const();
    let b1 = f.b_const();
    let and_ab_motive_r = f.and_ab();
    let motive_r = f.k.lam(anon, and_ab_motive_r, b1, BinderInfo::Default);
    let minor_r = {
        let v0 = f.k.bvar(0); // hb
        let inner = f.k.lam(anon, b1, v0, BinderInfo::Default);
        f.k.lam(anon, a1, inner, BinderInfo::Default)
    };
    // and-elim-left h : A.
    let a2 = f.a_const();
    let b2 = f.b_const();
    let and_ab_motive_l = f.and_ab();
    let motive_l = f.k.lam(anon, and_ab_motive_l, a2, BinderInfo::Default);
    let minor_l = {
        let v1 = f.k.bvar(1); // ha
        let inner = f.k.lam(anon, b2, v1, BinderInfo::Default);
        f.k.lam(anon, a2, inner, BinderInfo::Default)
    };

    // Build, inside the outer `fun (h : And A B) => …`, the body:
    //   And.intro B A (And.rec A B motive_r minor_r h) (And.rec A B motive_l minor_l h)
    let a3 = f.a_const();
    let b3 = f.b_const();
    // proof_right := And.rec.{0} A B motive_r minor_r h   (: B)
    let elim_right = {
        let rec = f.k.const_(f.p.and_rec, vec![z]);
        let e = f.k.app(rec, a3);
        let e = f.k.app(e, b3);
        let e = f.k.app(e, motive_r);
        let e = f.k.app(e, minor_r);
        let h = f.k.bvar(0);
        f.k.app(e, h)
    };
    let a4 = f.a_const();
    let b4 = f.b_const();
    let elim_left = {
        let rec = f.k.const_(f.p.and_rec, vec![z]);
        let e = f.k.app(rec, a4);
        let e = f.k.app(e, b4);
        let e = f.k.app(e, motive_l);
        let e = f.k.app(e, minor_l);
        let h = f.k.bvar(0);
        f.k.app(e, h)
    };
    // And.intro B A elim_right elim_left  : And B A.
    let b5 = f.b_const();
    let a5 = f.a_const();
    let body = {
        let intro = f.k.const_(f.p.and_intro, vec![]);
        let e = f.k.app(intro, b5);
        let e = f.k.app(e, a5);
        let e = f.k.app(e, elim_right);
        f.k.app(e, elim_left)
    };
    // proof := fun (h : And A B) => body.
    let proof = f.k.lam(anon, and_ab, body, BinderInfo::Default);

    let inferred = f.k.infer(proof).unwrap();
    // Expected: And A B → And B A.
    let and_ab_dom = f.and_ab();
    let and_ba = {
        let and = f.k.const_(f.p.and, vec![]);
        let b6 = f.b_const();
        let a6 = f.a_const();
        let e = f.k.app(and, b6);
        f.k.app(e, a6)
    };
    let expected = f.k.pi(anon, and_ab_dom, and_ba, BinderInfo::Default);
    assert!(
        f.k.def_eq(inferred, expected),
        "And.comm : And A B → And B A"
    );
}

/// **`Iff.intro`**: from `mp : A → B` and `mpr : B → A` (axioms), the proof
/// `Iff.intro A B mp mpr : Iff A B` checks — both directions packaged.
#[test]
fn iff_intro_checks() {
    let mut f = fixture();
    let anon = f.k.anon();
    let a = f.a_const();
    let b = f.b_const();

    // mp : A → B, mpr : B → A.
    let ab = f.k.pi(anon, a, b, BinderInfo::Default);
    let mp_name = f.k.name_str(anon, "mp");
    f.k.add_declaration(Declaration::Axiom {
        name: mp_name,
        uparams: vec![],
        ty: ab,
    })
    .unwrap();
    let ba = {
        let b2 = f.b_const();
        let a2 = f.a_const();
        f.k.pi(anon, b2, a2, BinderInfo::Default)
    };
    let mpr_name = f.k.name_str(anon, "mpr");
    f.k.add_declaration(Declaration::Axiom {
        name: mpr_name,
        uparams: vec![],
        ty: ba,
    })
    .unwrap();

    // Iff.intro A B mp mpr.
    let a3 = f.a_const();
    let b3 = f.b_const();
    let mp = f.k.const_(mp_name, vec![]);
    let mpr = f.k.const_(mpr_name, vec![]);
    let proof = {
        let intro = f.k.const_(f.p.iff_intro, vec![]);
        let e = f.k.app(intro, a3);
        let e = f.k.app(e, b3);
        let e = f.k.app(e, mp);
        f.k.app(e, mpr)
    };
    let inferred = f.k.infer(proof).unwrap();
    // Expected: Iff A B.
    let iff = f.k.const_(f.p.iff, vec![]);
    let a4 = f.a_const();
    let b4 = f.b_const();
    let expected = {
        let e = f.k.app(iff, a4);
        f.k.app(e, b4)
    };
    assert!(
        f.k.def_eq(inferred, expected),
        "Iff.intro A B mp mpr : Iff A B"
    );
}

/// **`Exists.intro`**: with `α : Type`, `p : α → Prop`, a witness `a : α` and a
/// proof `hpa : p a`, the term `Exists.intro.{1} α p a hpa : Exists.{1} α p`
/// type-checks — the existential introduction rule.
#[test]
fn exists_intro_checks() {
    let mut k = Kernel::new();
    let p = build_logic_prelude(&mut k).expect("logic prelude must build");
    let anon = k.anon();
    let one = {
        let z = k.level_zero();
        k.level_succ(z)
    };

    // α : Sort 1, p : α → Prop, a : α, hpa : p a.
    let s1 = k.sort(one);
    let alpha_n = k.name_str(anon, "α");
    k.add_declaration(Declaration::Axiom {
        name: alpha_n,
        uparams: vec![],
        ty: s1,
    })
    .unwrap();
    let alpha = k.const_(alpha_n, vec![]);
    let prop = k.sort_zero();
    let p_ty = k.pi(anon, alpha, prop, BinderInfo::Default);
    let pred_n = k.name_str(anon, "p");
    k.add_declaration(Declaration::Axiom {
        name: pred_n,
        uparams: vec![],
        ty: p_ty,
    })
    .unwrap();
    let pred = k.const_(pred_n, vec![]);
    let a_n = k.name_str(anon, "a");
    k.add_declaration(Declaration::Axiom {
        name: a_n,
        uparams: vec![],
        ty: alpha,
    })
    .unwrap();
    let a = k.const_(a_n, vec![]);
    // p a : Prop.
    let pa = k.app(pred, a);
    let hpa_n = k.name_str(anon, "hpa");
    k.add_declaration(Declaration::Axiom {
        name: hpa_n,
        uparams: vec![],
        ty: pa,
    })
    .unwrap();
    let hpa = k.const_(hpa_n, vec![]);

    // Exists.intro.{1} α p a hpa.
    let intro = k.const_(p.exists_intro, vec![one]);
    let proof = {
        let e = k.app(intro, alpha);
        let e = k.app(e, pred);
        let e = k.app(e, a);
        k.app(e, hpa)
    };
    let inferred = k.infer(proof).unwrap();
    // Expected: Exists.{1} α p.
    let exists_const = k.const_(p.exists_, vec![one]);
    let expected = {
        let e = k.app(exists_const, alpha);
        k.app(e, pred)
    };
    assert!(
        k.def_eq(inferred, expected),
        "Exists.intro α p a hpa : Exists α p"
    );
}

/// **`Exists.elim`** (= `Exists.rec` with a constant `Prop` motive): given
/// `h : Exists.{1} α p` and `f : ∀ (w : α), p w → C`, the term
/// `Exists.rec.{1} α p (fun _ => C) (fun w hw => f w hw) h : C` type-checks.
/// This is THE eliminator used to certify existential skolemization: the
/// skolemized refutation `R(sk)` becomes the minor `fun w hw => …`, wrapped over
/// the existential hypothesis to land in `C` (here `C := False` in practice).
#[test]
fn exists_elim_checks() {
    let mut k = Kernel::new();
    let p = build_logic_prelude(&mut k).expect("logic prelude must build");
    let anon = k.anon();
    let one = {
        let z = k.level_zero();
        k.level_succ(z)
    };
    // α : Sort 1, p : α → Prop, C : Prop.
    let s1 = k.sort(one);
    let alpha_n = k.name_str(anon, "α");
    k.add_declaration(Declaration::Axiom {
        name: alpha_n,
        uparams: vec![],
        ty: s1,
    })
    .unwrap();
    let alpha = k.const_(alpha_n, vec![]);
    let prop = k.sort_zero();
    let p_ty = k.pi(anon, alpha, prop, BinderInfo::Default);
    let pred_n = k.name_str(anon, "p");
    k.add_declaration(Declaration::Axiom {
        name: pred_n,
        uparams: vec![],
        ty: p_ty,
    })
    .unwrap();
    let pred = k.const_(pred_n, vec![]);
    let c_n = k.name_str(anon, "C");
    k.add_declaration(Declaration::Axiom {
        name: c_n,
        uparams: vec![],
        ty: prop,
    })
    .unwrap();
    let c = k.const_(c_n, vec![]);

    // f : Π (w : α), p w → C.   Under w, `p w` = App(p, BVar 0); under w + the
    // arrow's domain binder, `C` is closed (a Const), so it does not shift.
    let f_ty = {
        let w0 = k.bvar(0);
        let pw = k.app(pred, w0);
        let arrow = k.pi(anon, pw, c, BinderInfo::Default);
        k.pi(anon, alpha, arrow, BinderInfo::Default)
    };
    let f_n = k.name_str(anon, "f");
    k.add_declaration(Declaration::Axiom {
        name: f_n,
        uparams: vec![],
        ty: f_ty,
    })
    .unwrap();
    let f = k.const_(f_n, vec![]);

    // Exists.{1} α p.
    let exists_ap = {
        let exists_const = k.const_(p.exists_, vec![one]);
        let e = k.app(exists_const, alpha);
        k.app(e, pred)
    };
    // motive := fun (_ : Exists α p) => C.
    let motive = k.lam(anon, exists_ap, c, BinderInfo::Default);
    // minor := fun (w : α) (hw : p w) => f w hw.   w = BVar 1, hw = BVar 0.
    let minor = {
        let w1 = k.bvar(1);
        let hw0 = k.bvar(0);
        let app = k.app(f, w1);
        let app = k.app(app, hw0);
        // domain of the inner binder `hw : p w` — w = BVar 0 here.
        let w0 = k.bvar(0);
        let pw = k.app(pred, w0);
        let inner = k.lam(anon, pw, app, BinderInfo::Default);
        k.lam(anon, alpha, inner, BinderInfo::Default)
    };

    // proof := fun (h : Exists α p) =>
    //          Exists.rec.{1} α p motive minor h : C.
    // `Exists.rec` retains only the inductive's `u` parameter: its hidden
    // witness prevents large elimination, so the motive universe is fixed at 0.
    let proof = {
        let rec = k.const_(p.exists_rec, vec![one]);
        let e = k.app(rec, alpha);
        let e = k.app(e, pred);
        let e = k.app(e, motive);
        let e = k.app(e, minor);
        let h = k.bvar(0);
        let body = k.app(e, h);
        k.lam(anon, exists_ap, body, BinderInfo::Default)
    };
    let inferred = k.infer(proof).unwrap();
    // Expected: Exists α p → C.
    let expected = k.pi(anon, exists_ap, c, BinderInfo::Default);
    assert!(
        k.def_eq(inferred, expected),
        "Exists.elim : (Exists α p) → C"
    );
}

/// **Datatype inductive selector ι-reduces (route-A foundation).** Declare a
/// carrier `α : Type` and a 2-field datatype `Pair : Type` with
/// `Pair.mk : α → α → Pair` via [`Kernel::add_datatype_inductive`]; then for
/// concrete carrier atoms `x, y : α`, the selectors built by
/// [`Kernel::datatype_selector`] satisfy `select_0 (mk x y)` `def_eq` `x` and
/// `select_1 (mk x y)` `def_eq` `y` — the read-over-construct projection is
/// **ι-reduction**, not an axiom. This is the zero-trust datatype foundation:
/// the projection equation `Eq α (select_i (mk x y)) x_i` is `Eq.refl`.
#[test]
fn datatype_selector_iota_reduces_to_field() {
    let mut k = Kernel::new();
    let p = build_logic_prelude(&mut k).expect("logic prelude must build");
    let anon = k.anon();

    // α : Sort 1 (= Type) as an axiom carrier.
    let z = k.level_zero();
    let one = k.level_succ(z);
    let type_ = k.sort(one);
    let alpha_name = k.name_str(anon, "α");
    k.add_declaration(Declaration::Axiom {
        name: alpha_name,
        uparams: vec![],
        ty: type_,
    })
    .unwrap();
    let alpha = k.const_(alpha_name, vec![]);

    // Pair : Type with mk : α → α → Pair.
    let pair_name = k.name_str(anon, "Pair");
    let dt = k
        .add_datatype_inductive(pair_name, alpha, one, 2)
        .expect("Pair datatype should admit");

    // Concrete carrier atoms x, y : α.
    let x = {
        let n = k.name_str(anon, "x");
        k.add_declaration(Declaration::Axiom {
            name: n,
            uparams: vec![],
            ty: alpha,
        })
        .unwrap();
        k.const_(n, vec![])
    };
    let y = {
        let n = k.name_str(anon, "y");
        k.add_declaration(Declaration::Axiom {
            name: n,
            uparams: vec![],
            ty: alpha,
        })
        .unwrap();
        k.const_(n, vec![])
    };

    // mk x y : Pair.
    let mk_xy = {
        let mk = k.const_(dt.ctor, vec![]);
        let e = k.app(mk, x);
        k.app(e, y)
    };

    // select_0 (mk x y) def_eq x ;  select_1 (mk x y) def_eq y.
    for (index, field) in [(0usize, x), (1usize, y)] {
        let sel = k.datatype_selector(dt, alpha, one, index);
        let applied = k.app(sel, mk_xy);
        assert!(
            k.def_eq(applied, field),
            "select_{index}(mk x y) must ι-reduce to field {index}"
        );

        // The projection equation Eq α (select_i (mk x y)) field is Eq.refl.
        let eq_lhs = applied;
        let eq_prop = {
            let eq = k.const_(p.eq, vec![one]);
            let e = k.app(eq, alpha);
            let e = k.app(e, eq_lhs);
            k.app(e, field)
        };
        let refl = {
            let r = k.const_(p.eq_refl, vec![one]);
            let e = k.app(r, alpha);
            k.app(e, field)
        };
        let inferred = k.infer(refl).expect("Eq.refl infers");
        assert!(
            k.def_eq(inferred, eq_prop),
            "Eq.refl proves the select_{index} projection (ι-reduction)"
        );
    }
}

/// A carrier-axiom helper: declare an `α : Type` axiom and return `(name, α)`.
#[cfg(test)]
fn declare_carrier(k: &mut Kernel, name: &str, sort: crate::LevelId) -> crate::ExprId {
    let anon = k.anon();
    let type_ = k.sort(sort);
    let n = k.name_str(anon, name);
    k.add_declaration(Declaration::Axiom {
        name: n,
        uparams: vec![],
        ty: type_,
    })
    .unwrap();
    k.const_(n, vec![])
}

/// The **computational `Bool`** declared by `build_logic_prelude` is a genuine
/// two-element enum: `Bool.true`/`Bool.false` both infer to `Bool`, and they are
/// **distinct** (not `def_eq`). This is the carrier the is-tester eliminates into.
#[test]
fn computational_bool_has_two_distinct_values() {
    let mut k = Kernel::new();
    let p = build_logic_prelude(&mut k).expect("logic prelude must build");
    let bool_const = k.const_(p.bool_, vec![]);
    let t = k.const_(p.bool_true, vec![]);
    let f = k.const_(p.bool_false, vec![]);
    let t_ty = k.infer(t).expect("Bool.true infers");
    let f_ty = k.infer(f).expect("Bool.false infers");
    assert!(k.def_eq(t_ty, bool_const), "Bool.true : Bool");
    assert!(k.def_eq(f_ty, bool_const), "Bool.false : Bool");
    assert!(
        !k.def_eq(t, f),
        "Bool.true and Bool.false must be distinct values"
    );
}

/// The **is-tester** route, mirroring the selector route: declare a
/// two-constructor family `Color : Type` (`Red : α → Color | Green : α → Color`);
/// then for a carrier atom `a : α`, the is-testers built by
/// [`Kernel::datatype_tester`] satisfy `is_Green (Green a)` `def_eq` `Bool.true`,
/// `is_Green (Red a)` `def_eq` `Bool.false`, etc. — the is-tester fold is
/// **ι-reduction**, so `Eq Bool (is_C (cⱼ a)) (true/false)` is `Eq.refl`.
#[test]
fn datatype_tester_iota_reduces_to_bool() {
    let mut k = Kernel::new();
    let p = build_logic_prelude(&mut k).expect("logic prelude must build");
    let anon = k.anon();
    let z = k.level_zero();
    let one = k.level_succ(z);
    let alpha = declare_carrier(&mut k, "α", one);

    // Color : Type with Red : α → Color | Green : α → Color  (each arity 1).
    let color_name = k.name_str(anon, "Color");
    let red_name = k.name_str(color_name, "Red");
    let green_name = k.name_str(color_name, "Green");
    let family = k
        .add_datatype_family(color_name, alpha, one, &[(red_name, 1), (green_name, 1)])
        .expect("Color family should admit");

    // Carrier atom a : α.
    let a = {
        let n = k.name_str(anon, "a");
        k.add_declaration(Declaration::Axiom {
            name: n,
            uparams: vec![],
            ty: alpha,
        })
        .unwrap();
        k.const_(n, vec![])
    };

    let bool_const = k.const_(p.bool_, vec![]);
    let tt = k.const_(p.bool_true, vec![]);
    let ff = k.const_(p.bool_false, vec![]);

    // For each (tested ctor, applied ctor) pair, `is_tested (applied a)` must
    // ι-reduce to `Bool.true` iff tested == applied, else `Bool.false`; and the
    // fold equation `Eq Bool (is_tested (applied a)) value` is `Eq.refl Bool value`.
    for tested in 0..2usize {
        let tester = k.datatype_tester(&family, p.bool_, p.bool_true, p.bool_false, alpha, tested);
        for (applied, ctor) in family.ctors.clone().iter().enumerate() {
            let con = {
                let c = k.const_(*ctor, vec![]);
                k.app(c, a)
            };
            let folded = k.app(tester, con);
            let expected = if tested == applied { tt } else { ff };
            assert!(
                k.def_eq(folded, expected),
                "is_{tested}({applied} a) must ι-reduce to the right Bool value"
            );

            // Eq.refl Bool value : Eq Bool (is_tested (applied a)) value.
            let eq_prop = {
                let eq = k.const_(p.eq, vec![one]);
                let e = k.app(eq, bool_const);
                let e = k.app(e, folded);
                k.app(e, expected)
            };
            let refl = {
                let r = k.const_(p.eq_refl, vec![one]);
                let e = k.app(r, bool_const);
                k.app(e, expected)
            };
            let inferred = k.infer(refl).expect("Eq.refl infers");
            assert!(
                k.def_eq(inferred, eq_prop),
                "Eq.refl proves the is_{tested}({applied}) fold (ι-reduction)"
            );
        }
    }
}

/// The **family selector** route (the injectivity foundation), the family
/// analogue of [`datatype_selector_iota_reduces_to_field`]: declare a
/// two-constructor family `Box : Type` (`B2 : α → α → Box | B0 : Box`); then for
/// carrier atoms `x, y : α`, the selectors built by
/// [`Kernel::datatype_family_selector`] over constructor `B2` satisfy
/// `sel_0 (B2 x y)` `def_eq` `x` and `sel_1 (B2 x y)` `def_eq` `y` — the
/// read-over-construct projection is **ι-reduction**, so
/// `Eq α (sel_i (B2 x y)) x_i` is `Eq.refl`. The other constructor's minor (a
/// supplied `default` inhabitant) only types the recursor; it never reduces here.
#[test]
fn datatype_family_selector_iota_reduces_to_field() {
    let mut k = Kernel::new();
    let p = build_logic_prelude(&mut k).expect("logic prelude must build");
    let anon = k.anon();
    let z = k.level_zero();
    let one = k.level_succ(z);
    let alpha = declare_carrier(&mut k, "α", one);

    // Box : Type with B2 : α → α → Box | B0 : Box (arities 2 and 0).
    let box_name = k.name_str(anon, "Box");
    let b2_name = k.name_str(box_name, "B2");
    let b0_name = k.name_str(box_name, "B0");
    let family = k
        .add_datatype_family(box_name, alpha, one, &[(b2_name, 2), (b0_name, 0)])
        .expect("Box family should admit");

    // Carrier atoms x, y : α; a `default` inhabitant d : α for the B0 minor.
    let atom = |k: &mut Kernel, name: &str| {
        let n = k.name_str(anon, name);
        k.add_declaration(Declaration::Axiom {
            name: n,
            uparams: vec![],
            ty: alpha,
        })
        .unwrap();
        k.const_(n, vec![])
    };
    let x = atom(&mut k, "x");
    let y = atom(&mut k, "y");
    let d = atom(&mut k, "d");

    // B2 x y : Box.
    let b2_xy = {
        let c = k.const_(b2_name, vec![]);
        let e = k.app(c, x);
        k.app(e, y)
    };

    // sel_0 (B2 x y) def_eq x ; sel_1 (B2 x y) def_eq y.
    for (index, field) in [(0usize, x), (1usize, y)] {
        let sel = k.datatype_family_selector(&family, alpha, one, 0, index, d);
        let applied = k.app(sel, b2_xy);
        assert!(
            k.def_eq(applied, field),
            "sel_{index}(B2 x y) must ι-reduce to field {index}"
        );

        // The projection equation Eq α (sel_i (B2 x y)) field is Eq.refl.
        let eq_prop = {
            let eq = k.const_(p.eq, vec![one]);
            let e = k.app(eq, alpha);
            let e = k.app(e, applied);
            k.app(e, field)
        };
        let refl = {
            let r = k.const_(p.eq_refl, vec![one]);
            let e = k.app(r, alpha);
            k.app(e, field)
        };
        let inferred = k.infer(refl).expect("Eq.refl infers");
        assert!(
            k.def_eq(inferred, eq_prop),
            "Eq.refl proves the sel_{index} family projection (ι-reduction)"
        );
    }
}

/// The prelude's **computational `Nat`** is a genuine recursive inductive: both
/// constructors infer to `Nat` and are distinct, and `Nat.rec` ι-computes —
/// `Nat.rec C z s (Nat.succ (Nat.succ Nat.zero))` whnf's (through an
/// identity-by-recursion `s := fun _ ih => succ ih`) back to
/// `Nat.succ (Nat.succ Nat.zero)`. This is the engine the size measure rides on.
#[test]
fn prelude_nat_recursor_computes() {
    let mut k = Kernel::new();
    let p = build_logic_prelude(&mut k).expect("logic prelude must build");
    let anon = k.anon();
    let z = k.level_zero();
    let one = k.level_succ(z);

    let nat_const = k.const_(p.nat, vec![]);
    let zero_c = k.const_(p.nat_zero, vec![]);
    let succ_c = k.const_(p.nat_succ, vec![]);

    // Both constructors infer to `Nat` and are distinct.
    let zero_ty = k.infer(zero_c).expect("Nat.zero infers");
    assert!(k.def_eq(zero_ty, nat_const), "Nat.zero : Nat");
    let one_val = k.app(succ_c, zero_c);
    let one_ty = k.infer(one_val).expect("Nat.succ Nat.zero infers");
    assert!(k.def_eq(one_ty, nat_const), "Nat.succ Nat.zero : Nat");
    assert!(!k.def_eq(zero_c, one_val), "Nat.zero != Nat.succ Nat.zero");

    // C := fun (_ : Nat) => Nat ; z := zero ; s := fun (_ : Nat)(ih : Nat) => succ ih.
    let big_c = k.lam(anon, nat_const, nat_const, BinderInfo::Default);
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
    // Nat.rec.{1} C z s two  whnf's (identity-by-recursion) back to `two`.
    let rec_const = k.const_(p.nat_rec, vec![one]);
    let app = {
        let e = k.app(rec_const, big_c);
        let e = k.app(e, zero_c);
        let e = k.app(e, s_min);
        k.app(e, two)
    };
    let computed = whnf_deep(&mut k, app);
    assert_eq!(computed, two, "Nat.rec identity on 2 computes to 2");
}

/// Fully normalize `e` by WHNF-ing the head and then recursively each spine
/// argument (a test-only deep normalizer for closed first-order terms).
fn whnf_deep(k: &mut Kernel, e: crate::ExprId) -> crate::ExprId {
    let e = k.whnf(e);
    let mut spine = Vec::new();
    let mut h = e;
    while let ExprNode::App(f, a) = k.expr_node(h).clone() {
        spine.push(a);
        h = f;
    }
    let mut rebuilt = h;
    for a in spine.into_iter().rev() {
        let a = whnf_deep(k, a);
        rebuilt = k.app(rebuilt, a);
    }
    rebuilt
}

/// Declare a fresh carrier atom `name : ty` and return its `Const`.
fn declare_carrier_atom(k: &mut Kernel, name: &str, ty: crate::ExprId) -> crate::ExprId {
    let anon = k.anon();
    let n = k.name_str(anon, name);
    k.add_declaration(Declaration::Axiom {
        name: n,
        uparams: vec![],
        ty,
    })
    .unwrap();
    k.const_(n, vec![])
}

/// Build `IntList = nil | cons (head : α) (tail : IntList)` — a **recursive**
/// datatype family with a carrier head and a `D`-typed (recursive) tail. Returns
/// the family plus its `nil`/`cons` constructor names.
fn int_list_family(
    k: &mut Kernel,
    alpha: crate::ExprId,
    carrier_sort: crate::LevelId,
) -> (RecursiveDatatypeFamily, crate::NameId, crate::NameId) {
    let anon = k.anon();
    let list_name = k.name_str(anon, "IntList");
    let nil_name = k.name_str(list_name, "nil");
    let cons_name = k.name_str(list_name, "cons");
    let family = k
        .add_recursive_datatype_family(
            list_name,
            alpha,
            carrier_sort,
            &[
                (nil_name, vec![]),
                (cons_name, vec![RecField::Carrier, RecField::Recursive]),
            ],
        )
        .expect("recursive IntList family should admit");
    (family, nil_name, cons_name)
}

/// The **recursive datatype family** admits (a genuine inductive with a `D`-typed
/// tail field), and its structural **size** measure ι-reduces:
/// `size nil = Nat.zero`, `size (cons h nil) = Nat.succ Nat.zero`,
/// `size (cons h (cons g nil)) = Nat.succ (Nat.succ Nat.zero)`, and — the crux of
/// acyclicity — `size (cons h x) = Nat.succ (size x)` for an OPAQUE list atom
/// `x : IntList` (a stuck recursor whose `Nat.succ` shell is exposed by one ι
/// step). This is the occurs-check descent the acyclicity refutation rides on.
#[test]
fn recursive_family_size_iota_reduces() {
    let mut k = Kernel::new();
    let p = build_logic_prelude(&mut k).expect("logic prelude must build");
    let z = k.level_zero();
    let one = k.level_succ(z);
    let alpha = declare_carrier(&mut k, "α", one);

    let (family, nil_name, cons_name) = int_list_family(&mut k, alpha, one);

    // Carrier atoms h, g : α and an OPAQUE list atom x : IntList.
    let h = declare_carrier_atom(&mut k, "h", alpha);
    let g = declare_carrier_atom(&mut k, "g", alpha);
    let list_const = k.const_(family.ind, vec![]);
    let x = declare_carrier_atom(&mut k, "x", list_const);

    let nil = k.const_(nil_name, vec![]);
    let cons = |k: &mut Kernel, head: crate::ExprId, tail: crate::ExprId| {
        let c = k.const_(cons_name, vec![]);
        let e = k.app(c, head);
        k.app(e, tail)
    };
    let cons_h_nil = cons(&mut k, h, nil);
    let cons_g_nil = cons(&mut k, g, nil);
    let cons_h_cons_g_nil = cons(&mut k, h, cons_g_nil);
    let cons_h_x = cons(&mut k, h, x);

    let size = k.recursive_datatype_size(&family, alpha, p.nat, p.nat_zero, p.nat_succ);

    let zero = k.const_(p.nat_zero, vec![]);
    let succ = |k: &mut Kernel, n: crate::ExprId| {
        let s = k.const_(p.nat_succ, vec![]);
        k.app(s, n)
    };
    let one_nat = succ(&mut k, zero);
    let two_nat = succ(&mut k, one_nat);

    // size nil ι→ zero.
    let s_nil = k.app(size, nil);
    assert!(k.def_eq(s_nil, zero), "size nil = zero");
    // size (cons h nil) ι→ succ zero.
    let s_chn = k.app(size, cons_h_nil);
    assert!(k.def_eq(s_chn, one_nat), "size (cons h nil) = succ zero");
    // size (cons h (cons g nil)) ι→ succ (succ zero).
    let s_chcgn = k.app(size, cons_h_cons_g_nil);
    assert!(
        k.def_eq(s_chcgn, two_nat),
        "size (cons h (cons g nil)) = succ (succ zero)"
    );
    // size (cons h x) def_eq succ (size x) for the OPAQUE x — the size of a
    // `cons` is one more than the size of its tail, even when the tail is abstract.
    let s_chx = k.app(size, cons_h_x);
    let s_x = k.app(size, x);
    let succ_s_x = succ(&mut k, s_x);
    assert!(
        k.def_eq(s_chx, succ_s_x),
        "size (cons h x) = succ (size x) for opaque x"
    );
}

/// **`And.left`/`And.right`**: `And.left A B (And.intro A B ha hb)` ι-reduces
/// to exactly `ha` (not `hb`), and symmetrically for `And.right` — a stronger
/// check than an inferred-type comparison, since it confirms the projections
/// are not swapped.
#[test]
fn and_left_and_right_project_the_correct_field() {
    let mut f = fixture();
    let a = f.a_const();
    let b = f.b_const();
    let ha = f.ha_const();
    let hb = f.hb_const();

    let intro = f.k.const_(f.p.and_intro, vec![]);
    let and_ab_proof = apply_all(&mut f.k, intro, &[a, b, ha, hb]);

    let and_left = f.k.const_(f.p.and_left, vec![]);
    let left = apply_all(&mut f.k, and_left, &[a, b, and_ab_proof]);
    assert!(
        f.k.def_eq(left, ha),
        "And.left A B (And.intro A B ha hb) = ha"
    );

    let and_right = f.k.const_(f.p.and_right, vec![]);
    let right = apply_all(&mut f.k, and_right, &[a, b, and_ab_proof]);
    assert!(
        f.k.def_eq(right, hb),
        "And.right A B (And.intro A B ha hb) = hb"
    );
}

/// **`Or.elim`**: on `Or.inl A B ha` it ι-reduces to `f ha`; on
/// `Or.inr A B hb` it ι-reduces to `g hb` — confirming the two branches are
/// wired to the matching case, not swapped.
#[test]
fn or_elim_selects_the_correct_branch() {
    let mut f = fixture();
    let anon = f.k.anon();
    let a = f.a_const();
    let b = f.b_const();
    let c = f.c_const();

    // f : A → C, g : B → C  (axioms).
    let ac = f.k.pi(anon, a, c, BinderInfo::Default);
    let f_name = f.k.name_str(anon, "f");
    f.k.add_declaration(Declaration::Axiom {
        name: f_name,
        uparams: vec![],
        ty: ac,
    })
    .unwrap();
    let bc = f.k.pi(anon, b, c, BinderInfo::Default);
    let g_name = f.k.name_str(anon, "g");
    f.k.add_declaration(Declaration::Axiom {
        name: g_name,
        uparams: vec![],
        ty: bc,
    })
    .unwrap();
    let f_const = f.k.const_(f_name, vec![]);
    let g_const = f.k.const_(g_name, vec![]);

    let or_elim = f.k.const_(f.p.or_elim, vec![]);

    // Or.elim A B C (Or.inl A B ha) f g = f ha.
    let ha = f.ha_const();
    let or_inl = f.k.const_(f.p.or_inl, vec![]);
    let or_ab_left = apply_all(&mut f.k, or_inl, &[a, b, ha]);
    let result_left = apply_all(&mut f.k, or_elim, &[a, b, c, or_ab_left, f_const, g_const]);
    let expected_left = f.k.app(f_const, ha);
    assert!(
        f.k.def_eq(result_left, expected_left),
        "Or.elim on Or.inl reduces to f ha"
    );

    // Or.elim A B C (Or.inr A B hb) f g = g hb.
    let hb = f.hb_const();
    let or_inr = f.k.const_(f.p.or_inr, vec![]);
    let or_ab_right = apply_all(&mut f.k, or_inr, &[a, b, hb]);
    let result_right = apply_all(&mut f.k, or_elim, &[a, b, c, or_ab_right, f_const, g_const]);
    let expected_right = f.k.app(g_const, hb);
    assert!(
        f.k.def_eq(result_right, expected_right),
        "Or.elim on Or.inr reduces to g hb"
    );
}

/// **`Or.resolve_left`/`Or.resolve_right`**: on the surviving disjunct they
/// ι-reduce to exactly that proof (no dependency on the opaque refutation);
/// on the refuted disjunct the refutation is genuinely applied, and the
/// result is still well-typed (stuck, since the refutation is an opaque
/// axiom, but not ill-typed).
#[test]
fn or_resolve_left_and_right_pick_the_surviving_branch() {
    let mut f = fixture();
    let anon = f.k.anon();
    let a = f.a_const();
    let b = f.b_const();
    let ha = f.ha_const();
    let hb = f.hb_const();

    // na : A → False, nb : B → False  (opaque refutations).
    let false_const = f.k.const_(f.p.false_, vec![]);
    let na_ty = f.k.pi(anon, a, false_const, BinderInfo::Default);
    let na_name = f.k.name_str(anon, "na");
    f.k.add_declaration(Declaration::Axiom {
        name: na_name,
        uparams: vec![],
        ty: na_ty,
    })
    .unwrap();
    let nb_ty = f.k.pi(anon, b, false_const, BinderInfo::Default);
    let nb_name = f.k.name_str(anon, "nb");
    f.k.add_declaration(Declaration::Axiom {
        name: nb_name,
        uparams: vec![],
        ty: nb_ty,
    })
    .unwrap();
    let na = f.k.const_(na_name, vec![]);
    let nb = f.k.const_(nb_name, vec![]);

    let or_inl = f.k.const_(f.p.or_inl, vec![]);
    let or_ab_left = apply_all(&mut f.k, or_inl, &[a, b, ha]);
    let or_inr = f.k.const_(f.p.or_inr, vec![]);
    let or_ab_right = apply_all(&mut f.k, or_inr, &[a, b, hb]);

    let or_resolve_left = f.k.const_(f.p.or_resolve_left, vec![]);
    let or_resolve_right = f.k.const_(f.p.or_resolve_right, vec![]);

    // Or.resolve_left on the surviving Or.inr reduces to hb.
    let result = apply_all(&mut f.k, or_resolve_left, &[a, b, or_ab_right, na]);
    assert!(
        f.k.def_eq(result, hb),
        "Or.resolve_left A B (Or.inr ... hb) na = hb"
    );
    // Or.resolve_left on the refuted Or.inl still checks, at type B.
    let result2 = apply_all(&mut f.k, or_resolve_left, &[a, b, or_ab_left, na]);
    let inferred2 = f.k.infer(result2).unwrap();
    assert!(
        f.k.def_eq(inferred2, b),
        "Or.resolve_left A B (Or.inl ... ha) na : B"
    );

    // Or.resolve_right on the surviving Or.inl reduces to ha.
    let result3 = apply_all(&mut f.k, or_resolve_right, &[a, b, or_ab_left, nb]);
    assert!(
        f.k.def_eq(result3, ha),
        "Or.resolve_right A B (Or.inl ... ha) nb = ha"
    );
    // Or.resolve_right on the refuted Or.inr still checks, at type A.
    let result4 = apply_all(&mut f.k, or_resolve_right, &[a, b, or_ab_right, nb]);
    let inferred4 = f.k.infer(result4).unwrap();
    assert!(
        f.k.def_eq(inferred4, a),
        "Or.resolve_right A B (Or.inr ... hb) nb : A"
    );
}

/// **`Iff.mp`/`Iff.mpr`**: `Iff.mp A B (Iff.intro A B mp mpr)` ι-reduces to
/// exactly `mp` (not `mpr`), and symmetrically for `Iff.mpr`.
#[test]
fn iff_mp_and_mpr_project_the_correct_direction() {
    let mut f = fixture();
    let anon = f.k.anon();
    let a = f.a_const();
    let b = f.b_const();

    let ab = f.k.pi(anon, a, b, BinderInfo::Default);
    let mp_name = f.k.name_str(anon, "mp_fn");
    f.k.add_declaration(Declaration::Axiom {
        name: mp_name,
        uparams: vec![],
        ty: ab,
    })
    .unwrap();
    let ba = f.k.pi(anon, b, a, BinderInfo::Default);
    let mpr_name = f.k.name_str(anon, "mpr_fn");
    f.k.add_declaration(Declaration::Axiom {
        name: mpr_name,
        uparams: vec![],
        ty: ba,
    })
    .unwrap();
    let mp_fn = f.k.const_(mp_name, vec![]);
    let mpr_fn = f.k.const_(mpr_name, vec![]);

    let iff_intro = f.k.const_(f.p.iff_intro, vec![]);
    let iff_ab_proof = apply_all(&mut f.k, iff_intro, &[a, b, mp_fn, mpr_fn]);

    let iff_mp = f.k.const_(f.p.iff_mp, vec![]);
    let mp_result = apply_all(&mut f.k, iff_mp, &[a, b, iff_ab_proof]);
    assert!(
        f.k.def_eq(mp_result, mp_fn),
        "Iff.mp A B (Iff.intro A B mp mpr) = mp"
    );

    let iff_mpr = f.k.const_(f.p.iff_mpr, vec![]);
    let mpr_result = apply_all(&mut f.k, iff_mpr, &[a, b, iff_ab_proof]);
    assert!(
        f.k.def_eq(mpr_result, mpr_fn),
        "Iff.mpr A B (Iff.intro A B mp mpr) = mpr"
    );

    // The projected direction genuinely composes: Iff.mp ... ha = mp_fn ha.
    let ha = f.ha_const();
    let applied_mp = f.k.app(mp_result, ha);
    let expected = f.k.app(mp_fn, ha);
    assert!(
        f.k.def_eq(applied_mp, expected),
        "Iff.mp A B (Iff.intro A B mp mpr) ha = mp_fn ha"
    );
}

/// **`` congrFun' ``**: transports a function equality along application at a
/// point. Checked two ways: the general (opaque `h : Eq f g`) case infers the
/// expected `Eq C (f a) (g a)`, and the reflexivity case
/// `congrFun' (Eq.refl f) ha` genuinely ι-reduces to `Eq.refl C (f ha)`.
#[test]
fn congr_fun_prime_transports_along_function_equality() {
    let mut f = fixture();
    let anon = f.k.anon();
    let a = f.a_const();
    let c = f.c_const();
    let ha = f.ha_const();
    let zero = f.k.level_zero();

    let ac = f.k.pi(anon, a, c, BinderInfo::Default);
    let f_name = f.k.name_str(anon, "cf_f");
    f.k.add_declaration(Declaration::Axiom {
        name: f_name,
        uparams: vec![],
        ty: ac,
    })
    .unwrap();
    let g_name = f.k.name_str(anon, "cf_g");
    f.k.add_declaration(Declaration::Axiom {
        name: g_name,
        uparams: vec![],
        ty: ac,
    })
    .unwrap();
    let f_fn = f.k.const_(f_name, vec![]);
    let g_fn = f.k.const_(g_name, vec![]);

    let eq_const = f.k.const_(f.p.eq, vec![zero]);
    let hyp_ty = apply_all(&mut f.k, eq_const, &[ac, f_fn, g_fn]);
    let h_name = f.k.name_str(anon, "cf_h");
    f.k.add_declaration(Declaration::Axiom {
        name: h_name,
        uparams: vec![],
        ty: hyp_ty,
    })
    .unwrap();
    let h = f.k.const_(h_name, vec![]);

    let congr_fun_prime = f.k.const_(f.p.congr_fun_prime, vec![zero, zero]);
    let applied = apply_all(&mut f.k, congr_fun_prime, &[a, c, f_fn, g_fn, h, ha]);

    let f_ha = f.k.app(f_fn, ha);
    let g_ha = f.k.app(g_fn, ha);
    let eq_const2 = f.k.const_(f.p.eq, vec![zero]);
    let expected = apply_all(&mut f.k, eq_const2, &[c, f_ha, g_ha]);
    let inferred = f.k.infer(applied).unwrap();
    assert!(
        f.k.def_eq(inferred, expected),
        "congrFun' A C f g h ha : Eq C (f ha) (g ha)"
    );

    // Reflexivity case: congrFun' (Eq.refl f) ha reduces to Eq.refl (f ha).
    let eq_refl_const = f.k.const_(f.p.eq_refl, vec![zero]);
    let refl_f = apply_all(&mut f.k, eq_refl_const, &[ac, f_fn]);
    let congr_fun_prime2 = f.k.const_(f.p.congr_fun_prime, vec![zero, zero]);
    let applied_refl = apply_all(&mut f.k, congr_fun_prime2, &[a, c, f_fn, f_fn, refl_f, ha]);
    let eq_refl_const2 = f.k.const_(f.p.eq_refl, vec![zero]);
    let expected_refl = apply_all(&mut f.k, eq_refl_const2, &[c, f_ha]);
    assert!(
        f.k.def_eq(applied_refl, expected_refl),
        "congrFun' A C f f (Eq.refl f) ha = Eq.refl C (f ha)"
    );
}

/// **`absurd`/`mt`**: `absurd A C ha na : C` for any target `C`, and
/// `mt A B f nb ha` genuinely applies both: it ι-reduces to `nb (f ha)`.
#[test]
fn absurd_and_mt_check() {
    let mut f = fixture();
    let anon = f.k.anon();
    let a = f.a_const();
    let b = f.b_const();
    let c = f.c_const();
    let ha = f.ha_const();
    let hb = f.hb_const();

    // na : A → False, for `absurd`.
    let false_const = f.k.const_(f.p.false_, vec![]);
    let na_ty = f.k.pi(anon, a, false_const, BinderInfo::Default);
    let na_name = f.k.name_str(anon, "na");
    f.k.add_declaration(Declaration::Axiom {
        name: na_name,
        uparams: vec![],
        ty: na_ty,
    })
    .unwrap();
    let na = f.k.const_(na_name, vec![]);

    let zero = f.k.level_zero();
    let absurd = f.k.const_(f.p.absurd, vec![zero]);
    let result = apply_all(&mut f.k, absurd, &[a, c, ha, na]);
    let inferred = f.k.infer(result).unwrap();
    assert!(f.k.def_eq(inferred, c), "absurd A C ha na : C");

    // nb : B → False, for `mt`.
    let nb_ty = f.k.pi(anon, b, false_const, BinderInfo::Default);
    let nb_name = f.k.name_str(anon, "nb");
    f.k.add_declaration(Declaration::Axiom {
        name: nb_name,
        uparams: vec![],
        ty: nb_ty,
    })
    .unwrap();
    let nb = f.k.const_(nb_name, vec![]);

    // const_b_fn := fun (_ : A) => hb : A → B.
    let dummy_fv = 99_000u64;
    let const_b_fn = lam_fvar(&mut f.k, dummy_fv, a, hb);

    let mt = f.k.const_(f.p.mt, vec![]);
    let mt_partial = apply_all(&mut f.k, mt, &[a, b, const_b_fn, nb]);
    let inferred_mt = f.k.infer(mt_partial).unwrap();
    let expected_mt_ty = f.k.pi(anon, a, false_const, BinderInfo::Default);
    assert!(
        f.k.def_eq(inferred_mt, expected_mt_ty),
        "mt A B f nb : A → False"
    );

    // mt A B const_b_fn nb ha  ι-reduces to nb (const_b_fn ha) = nb hb.
    let mt_applied = f.k.app(mt_partial, ha);
    let expected_applied = f.k.app(nb, hb);
    assert!(
        f.k.def_eq(mt_applied, expected_applied),
        "mt A B f nb ha = nb hb"
    );
}

/// The double-negation toolkit and the `Decidable` infrastructure: every one
/// of them must be **present** (a name interned but never declared would
/// pass an `axiom_footprint` check vacuously) and every one of them must
/// have an **empty** `axiom_footprint` -- in particular, none of them may
/// reach `Classical.em`, `propext`, `funext`, or `Quot.sound`.
#[test]
fn double_negation_and_decidable_are_present_and_axiom_free() {
    let mut k = Kernel::new();
    let p = build_logic_prelude(&mut k).expect("logic prelude must build");

    for name in [
        p.not_not_not_intro,
        p.not_not_and,
        p.not_not_imp,
        p.bool_false_ne_true,
        p.bool_true_ne_false,
        p.decidable,
        p.decidable_is_false,
        p.decidable_is_true,
        p.decidable_rec,
        p.decide,
        p.of_decide_eq_true,
        p.of_decide_eq_false,
        p.decidable_em,
        p.decidable_by_cases,
        p.decidable_pred,
    ] {
        assert!(
            k.environment().contains(name),
            "prelude should declare {}",
            k.display_name(name)
        );
        let footprint = k.axiom_footprint(name);
        assert!(
            footprint.is_empty(),
            "{} is not axiom-free: {:?}",
            k.display_name(name),
            footprint
                .iter()
                .map(|n| k.display_name(*n).to_string())
                .collect::<Vec<_>>()
        );
    }
}

/// `Decidable.decide` genuinely computes: `decide A (isTrue A ha) ≡ Bool.true`
/// and `decide A (isFalse A na) ≡ Bool.false`, both by ι-reduction through
/// `Decidable.rec` (checked with `def_eq`, mirroring
/// `computational_bool_has_two_distinct_values`).
#[test]
fn decidable_decide_computes_on_both_constructors() {
    let mut f = fixture();
    let anon = f.k.anon();
    let a = f.a_const();
    let ha = f.ha_const();
    let false_const = f.k.const_(f.p.false_, vec![]);

    // na : A → False, a fresh axiom (the fixture has no negative witness).
    let na_ty = f.k.pi(anon, a, false_const, BinderInfo::Default);
    let na_name = f.k.name_str(anon, "na");
    f.k.add_declaration(Declaration::Axiom {
        name: na_name,
        uparams: vec![],
        ty: na_ty,
    })
    .unwrap();
    let na = f.k.const_(na_name, vec![]);

    let is_true_const = f.k.const_(f.p.decidable_is_true, vec![]);
    let d_true = apply_all(&mut f.k, is_true_const, &[a, ha]);
    let is_false_const = f.k.const_(f.p.decidable_is_false, vec![]);
    let d_false = apply_all(&mut f.k, is_false_const, &[a, na]);

    let decide_const = f.k.const_(f.p.decide, vec![]);
    let decide_true = apply_all(&mut f.k, decide_const, &[a, d_true]);
    let decide_const2 = f.k.const_(f.p.decide, vec![]);
    let decide_false = apply_all(&mut f.k, decide_const2, &[a, d_false]);

    let bool_true = f.k.const_(f.p.bool_true, vec![]);
    let bool_false = f.k.const_(f.p.bool_false, vec![]);

    assert!(
        f.k.def_eq(decide_true, bool_true),
        "decide A (isTrue A ha) = Bool.true"
    );
    assert!(
        f.k.def_eq(decide_false, bool_false),
        "decide A (isFalse A na) = Bool.false"
    );
    assert!(
        !f.k.def_eq(decide_true, decide_false),
        "the two branches must remain distinct"
    );
}

/// `Decidable.em` selects the matching `Or` branch by ι-reduction: on
/// `isTrue A ha` it is `Or.inl A (A→False) ha`, on `isFalse A na` it is
/// `Or.inr A (A→False) na`.
#[test]
fn decidable_em_selects_the_correct_branch() {
    let mut f = fixture();
    let anon = f.k.anon();
    let a = f.a_const();
    let ha = f.ha_const();
    let false_const = f.k.const_(f.p.false_, vec![]);
    let na_ty = f.k.pi(anon, a, false_const, BinderInfo::Default);
    let na_name = f.k.name_str(anon, "na");
    f.k.add_declaration(Declaration::Axiom {
        name: na_name,
        uparams: vec![],
        ty: na_ty,
    })
    .unwrap();
    let na = f.k.const_(na_name, vec![]);

    let is_true_const = f.k.const_(f.p.decidable_is_true, vec![]);
    let d_true = apply_all(&mut f.k, is_true_const, &[a, ha]);
    let is_false_const = f.k.const_(f.p.decidable_is_false, vec![]);
    let d_false = apply_all(&mut f.k, is_false_const, &[a, na]);

    let em_const = f.k.const_(f.p.decidable_em, vec![]);
    let em_true = apply_all(&mut f.k, em_const, &[a, d_true]);
    let em_const2 = f.k.const_(f.p.decidable_em, vec![]);
    let em_false = apply_all(&mut f.k, em_const2, &[a, d_false]);

    let or_inl_const = f.k.const_(f.p.or_inl, vec![]);
    let expected_true = apply_all(&mut f.k, or_inl_const, &[a, na_ty, ha]);
    let or_inr_const = f.k.const_(f.p.or_inr, vec![]);
    let expected_false = apply_all(&mut f.k, or_inr_const, &[a, na_ty, na]);

    assert!(
        f.k.def_eq(em_true, expected_true),
        "Decidable.em A (isTrue A ha) = Or.inl A (A→False) ha"
    );
    assert!(
        f.k.def_eq(em_false, expected_false),
        "Decidable.em A (isFalse A na) = Or.inr A (A→False) na"
    );
}

/// `Decidable.of_decide_eq_true`/`of_decide_eq_false` genuinely extract a
/// proof of (the negation of) `A` from a computed `Bool.true`/`Bool.false`
/// equality, at both `Decidable` constructors -- the "spec direction" that
/// ties `decide` back to the proposition it decided.
#[test]
fn of_decide_eq_true_and_false_apply_at_both_constructors() {
    let mut f = fixture();
    let anon = f.k.anon();
    let a = f.a_const();
    let ha = f.ha_const();
    let false_const = f.k.const_(f.p.false_, vec![]);
    let na_ty = f.k.pi(anon, a, false_const, BinderInfo::Default);
    let na_name = f.k.name_str(anon, "na");
    f.k.add_declaration(Declaration::Axiom {
        name: na_name,
        uparams: vec![],
        ty: na_ty,
    })
    .unwrap();
    let na = f.k.const_(na_name, vec![]);

    let is_true_const = f.k.const_(f.p.decidable_is_true, vec![]);
    let d_true = apply_all(&mut f.k, is_true_const, &[a, ha]);
    let is_false_const = f.k.const_(f.p.decidable_is_false, vec![]);
    let d_false = apply_all(&mut f.k, is_false_const, &[a, na]);

    let bool_const = f.k.const_(f.p.bool_, vec![]);
    let bool_true = f.k.const_(f.p.bool_true, vec![]);
    let bool_false = f.k.const_(f.p.bool_false, vec![]);
    let one = {
        let z = f.k.level_zero();
        f.k.level_succ(z)
    };
    let eq_refl_const = f.k.const_(f.p.eq_refl, vec![one]);

    // of_decide_eq_true A d_true (Eq.refl Bool Bool.true) : A -- the
    // hypothesis type-checks against `Eq Bool (decide A d_true) Bool.true`
    // only because `decide A d_true` reduces to `Bool.true`.
    let refl_true = apply_all(&mut f.k, eq_refl_const, &[bool_const, bool_true]);
    let of_true_const = f.k.const_(f.p.of_decide_eq_true, vec![]);
    let applied_true = apply_all(&mut f.k, of_true_const, &[a, d_true, refl_true]);
    let inferred_true = f.k.infer(applied_true).expect("of_decide_eq_true checks");
    assert!(
        f.k.def_eq(inferred_true, a),
        "of_decide_eq_true A d_true refl : A"
    );

    // of_decide_eq_false A d_false (Eq.refl Bool Bool.false) : A → False.
    let refl_false = apply_all(&mut f.k, eq_refl_const, &[bool_const, bool_false]);
    let of_false_const = f.k.const_(f.p.of_decide_eq_false, vec![]);
    let applied_false = apply_all(&mut f.k, of_false_const, &[a, d_false, refl_false]);
    let inferred_false = f.k.infer(applied_false).expect("of_decide_eq_false checks");
    assert!(
        f.k.def_eq(inferred_false, na_ty),
        "of_decide_eq_false A d_false refl : A → False"
    );
}

/// `Decidable.byCases` selects the matching branch by ι-reduction, at a
/// `Type`-valued motive (`Bool`) -- exactly the "select data" capability
/// `Or.rec` structurally cannot offer.
#[test]
fn decidable_by_cases_selects_data_at_a_type_valued_motive() {
    let mut f = fixture();
    let anon = f.k.anon();
    let a = f.a_const();
    let ha = f.ha_const();
    let false_const = f.k.const_(f.p.false_, vec![]);
    let na_ty = f.k.pi(anon, a, false_const, BinderInfo::Default);
    let na_name = f.k.name_str(anon, "na");
    f.k.add_declaration(Declaration::Axiom {
        name: na_name,
        uparams: vec![],
        ty: na_ty,
    })
    .unwrap();
    let na = f.k.const_(na_name, vec![]);

    let is_true_const = f.k.const_(f.p.decidable_is_true, vec![]);
    let d_true = apply_all(&mut f.k, is_true_const, &[a, ha]);
    let is_false_const = f.k.const_(f.p.decidable_is_false, vec![]);
    let d_false = apply_all(&mut f.k, is_false_const, &[a, na]);

    let bool_const = f.k.const_(f.p.bool_, vec![]);
    let bool_true = f.k.const_(f.p.bool_true, vec![]);
    let bool_false = f.k.const_(f.p.bool_false, vec![]);

    // hpos := fun (_:A) => Bool.true ; hneg := fun (_:A→False) => Bool.false.
    let dummy1 = 98_100u64;
    let hpos = lam_fvar(&mut f.k, dummy1, a, bool_true);
    let dummy2 = 98_101u64;
    let hneg = lam_fvar(&mut f.k, dummy2, na_ty, bool_false);

    let zero = f.k.level_zero();
    let by_cases_const = f.k.const_(f.p.decidable_by_cases, vec![zero]);
    let applied_true = apply_all(
        &mut f.k,
        by_cases_const,
        &[a, bool_const, d_true, hpos, hneg],
    );
    let by_cases_const2 = f.k.const_(f.p.decidable_by_cases, vec![zero]);
    let hpos2 = lam_fvar(&mut f.k, dummy1, a, bool_true);
    let hneg2 = lam_fvar(&mut f.k, dummy2, na_ty, bool_false);
    let applied_false = apply_all(
        &mut f.k,
        by_cases_const2,
        &[a, bool_const, d_false, hpos2, hneg2],
    );

    assert!(
        f.k.def_eq(applied_true, bool_true),
        "byCases A Bool d_true hpos hneg = Bool.true"
    );
    assert!(
        f.k.def_eq(applied_false, bool_false),
        "byCases A Bool d_false hpos hneg = Bool.false"
    );
}
