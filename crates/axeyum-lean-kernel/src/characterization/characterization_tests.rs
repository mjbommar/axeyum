//! Tests for the characterization package.
//!
//! Three kinds, and the third is the one that matters: the package **builds**
//! and every witness is axiom-free; the theorems are **not vacuous** (their
//! hypotheses are instantiated at a structure we actually have); and every
//! injected [`Weakening`] is **rejected**, so each hypothesis is load-bearing
//! rather than decorative.

use super::int::{iadd, ineg, ione, izero};
use super::ops::CharDev;
use super::{CharacterizationKind, Weakening, build_characterization_with};
use crate::env::Declaration;
use crate::expr::ExprId;
use crate::nat_prelude::NatOps;
use crate::{Kernel, build_characterization};

/// Render a footprint for an assertion message.
fn footprint_of(kernel: &Kernel, name: crate::name::NameId) -> Vec<String> {
    kernel
        .axiom_footprint(name)
        .into_iter()
        .map(|a| kernel.display_name(a).to_string())
        .collect()
}

#[test]
fn the_characterization_package_builds_and_every_witness_is_axiom_free() {
    let mut kernel = Kernel::new();
    let package = build_characterization(&mut kernel).expect("the characterization must build");
    assert_eq!(
        package.entries.len(),
        34,
        "the reported population must match the declared one"
    );
    for entry in &package.entries {
        let rendered = kernel.display_name(entry.name).to_string();
        assert!(
            matches!(
                kernel.environment().get(entry.name),
                Some(Declaration::Theorem { .. })
            ),
            "{rendered} is not a checked theorem"
        );
        let footprint = footprint_of(&kernel, entry.name);
        assert!(
            footprint.is_empty(),
            "{rendered} ({}) rests on {footprint:?}",
            entry.kind.label()
        );
    }
}

#[test]
fn the_characterization_namespaces_declare_nothing_trusted() {
    let mut kernel = Kernel::new();
    let package = build_characterization(&mut kernel).expect("the characterization must build");
    let roots = [
        kernel.display_name(package.nat.root).to_string(),
        kernel.display_name(package.int.root).to_string(),
    ];
    let mut checked = 0usize;
    for (name, declaration) in kernel.environment().iter() {
        let rendered = kernel.display_name(*name).to_string();
        if !roots
            .iter()
            .any(|root| rendered.starts_with(&format!("{root}.")))
        {
            continue;
        }
        checked += 1;
        assert!(
            !matches!(
                declaration,
                Declaration::Axiom { .. }
                    | Declaration::Opaque { .. }
                    | Declaration::Quotient { .. }
            ),
            "{rendered} is a trusted declaration inside a characterization namespace"
        );
    }
    assert!(
        checked >= 34,
        "the namespace sweep saw only {checked} declarations; it was pointed at the wrong names"
    );
}

#[test]
fn nat_induction_rests_on_the_kernel_generated_recursor() {
    let mut kernel = Kernel::new();
    let package = build_characterization(&mut kernel).expect("the characterization must build");
    let nat = package.int_prelude.nat;
    match kernel.environment().get(nat.nat) {
        Some(Declaration::Inductive { ctor_names, .. }) => {
            assert_eq!(
                ctor_names.len(),
                2,
                "Nat must have exactly two constructors"
            );
        }
        other => panic!("Nat is not an inductive declaration: {other:?}"),
    }
    match kernel.environment().get(nat.rec) {
        Some(Declaration::Recursor {
            rec_rules,
            num_minors,
            ..
        }) => {
            assert_eq!(
                rec_rules.len(),
                2,
                "Nat.rec must carry one iota rule per constructor"
            );
            assert_eq!(*num_minors, 2);
        }
        other => panic!("Nat.rec is not a kernel-generated recursor: {other:?}"),
    }
    match kernel.environment().get(package.int_prelude.z) {
        Some(Declaration::Inductive { ctor_names, .. }) => {
            assert_eq!(
                ctor_names.len(),
                2,
                "Int must have exactly two constructors"
            );
        }
        other => panic!("Int is not an inductive declaration: {other:?}"),
    }
}

#[test]
fn the_iterator_computes() {
    // `iter Nat zero succ` is the identity on numerals, definitionally: this is
    // the iota rule actually firing, not a comment claiming it does.
    let mut kernel = Kernel::new();
    let package = build_characterization(&mut kernel).expect("the characterization must build");
    let mut dev = CharDev::new(&mut kernel, package.int_prelude);
    let level = dev.level_one();
    let nat_ty = dev.nat_ty();
    let zero = dev.zero();
    let succ = {
        let name = dev.prelude().succ;
        dev.kernel().const_(name, vec![])
    };
    let iter = dev.kernel().const_(package.nat.iter, vec![level]);
    let three = dev.num(3);
    let applied = dev.apply(iter, &[nat_ty, zero, succ, three]);
    assert!(
        dev.kernel().def_eq(applied, three),
        "iter Nat zero succ 3 must reduce to 3"
    );
    let four = dev.num(4);
    assert!(
        !dev.kernel().def_eq(applied, four),
        "the reduction check must be able to fail"
    );
}

#[test]
fn categoricity_is_not_vacuous_it_instantiates_at_nat_itself() {
    // A categoricity theorem whose hypotheses no structure satisfies would be
    // worthless and would still be axiom-free. This instantiates it at
    // `(Nat, zero, succ)` using the three Peano theorems as the hypotheses and
    // pushes the result back through the trusted gate.
    let mut kernel = Kernel::new();
    let package = build_characterization(&mut kernel).expect("the characterization must build");
    let witness = {
        let mut dev = CharDev::new(&mut kernel, package.int_prelude);
        let level = dev.level_one();
        let nat_ty = dev.nat_ty();
        let zero = dev.zero();
        let succ = {
            let name = dev.prelude().succ;
            dev.kernel().const_(name, vec![])
        };
        let zero_ne_succ = dev.kernel().const_(package.nat.zero_ne_succ, vec![]);
        let succ_injective = dev.kernel().const_(package.nat.succ_injective, vec![]);
        let induction = dev.kernel().const_(package.nat.induction, vec![]);
        let head = dev.kernel().const_(package.nat.categorical, vec![level]);
        let applied = dev.apply(
            head,
            &[nat_ty, zero, succ, zero_ne_succ, succ_injective, induction],
        );
        let ty = dev
            .kernel()
            .infer(applied)
            .expect("categoricity must accept Nat's own Peano theorems as its hypotheses");
        let anon = dev.anon_name();
        let root = dev.kernel().name_str(anon, "Characterization");
        let name = dev.kernel().name_str(root, "categorical_at_nat");
        dev.declare_theorem_u(name, vec![], ty, applied)
            .expect("the instantiated categoricity theorem must be admitted");
        name
    };
    let footprint = footprint_of(&kernel, witness);
    assert!(
        footprint.is_empty(),
        "the instantiated categoricity theorem rests on {footprint:?}"
    );
}

#[test]
#[allow(clippy::too_many_lines)]
fn the_int_hypothesis_shapes_are_satisfiable() {
    // Companion to the `Nat` non-vacuity check: a theorem whose premises no
    // instance satisfies is axiom-free and worthless. This instantiates the
    // `+1` / `-1` premises of `Int.Characterization.induction` and the whole
    // premise list of `rec_unique`, and pushes both results back through the
    // trusted gate.
    let mut kernel = Kernel::new();
    let package = build_characterization(&mut kernel).expect("the characterization must build");
    let (induction_witness, unique_witness) = {
        let mut dev = CharDev::new(&mut kernel, package.int_prelude);
        let level = dev.level_one();
        let int_ty = dev.int_ty();
        let int_zero = {
            let name = package.int_prelude.zero;
            dev.kernel().const_(name, vec![])
        };
        let int_one = {
            let name = package.int_prelude.one;
            dev.kernel().const_(name, vec![])
        };
        let anon = dev.anon_name();
        let root = dev.kernel().name_str(anon, "Characterization");

        // `fun t => t + 1` and `fun t => t + (-1)`.
        let shift = |dev: &mut CharDev<'_>, upward: bool| {
            let t_fv = dev.fresh_fvar();
            let t = dev.kernel().fvar(t_fv);
            let delta = if upward {
                int_one
            } else {
                let name = package.int_prelude.neg;
                dev.const_app(name, &[int_one])
            };
            let name = package.int_prelude.add;
            let body = dev.const_app(name, &[t, delta]);
            dev.lam_fv(t_fv, int_ty, body)
        };
        let up = shift(&mut dev, true);
        let down = shift(&mut dev, false);

        // `Int.Characterization.induction` at `P := fun t => t = t`.
        let induction_witness = {
            let t_fv = dev.fresh_fvar();
            let t = dev.kernel().fvar(t_fv);
            let body = dev.eq_at(level, int_ty, t, t);
            let motive = dev.lam_fv(t_fv, int_ty, body);
            let base = dev.refl_at(level, int_ty, int_zero);
            let trivial_step = |dev: &mut CharDev<'_>, upward: bool| {
                let t_fv = dev.fresh_fvar();
                let t = dev.kernel().fvar(t_fv);
                let ih_ty = dev.eq_at(level, int_ty, t, t);
                let ih_fv = dev.fresh_fvar();
                let shifted = if upward { up } else { down };
                let shifted = dev.apply(shifted, &[t]);
                let body = dev.refl_at(level, int_ty, shifted);
                let inner = dev.lam_fv(ih_fv, ih_ty, body);
                dev.lam_fv(t_fv, int_ty, inner)
            };
            let successor = trivial_step(&mut dev, true);
            let predecessor = trivial_step(&mut dev, false);
            let head = dev.kernel().const_(package.int.induction, vec![]);
            let applied = dev.apply(head, &[motive, base, successor, predecessor]);
            let ty = dev
                .kernel()
                .infer(applied)
                .expect("the +1 / -1 premises must be satisfiable");
            let name = dev.kernel().name_str(root, "int_induction_instance");
            dev.declare_theorem_u(name, vec![], ty, applied)
                .expect("the instantiated induction principle must be admitted");
            name
        };

        // `rec_unique` with `f = g = id`, `up`/`down` as above: every premise
        // holds by reflexivity, so the premise list is inhabited.
        let unique_witness = {
            let identity = {
                let t_fv = dev.fresh_fvar();
                let t = dev.kernel().fvar(t_fv);
                dev.lam_fv(t_fv, int_ty, t)
            };
            let agree_zero = dev.refl_at(level, int_ty, int_zero);
            let recurrence = |dev: &mut CharDev<'_>, upward: bool| {
                let t_fv = dev.fresh_fvar();
                let t = dev.kernel().fvar(t_fv);
                let shifted = if upward { up } else { down };
                let shifted = dev.apply(shifted, &[t]);
                let body = dev.refl_at(level, int_ty, shifted);
                dev.lam_fv(t_fv, int_ty, body)
            };
            let f_up = recurrence(&mut dev, true);
            let g_up = recurrence(&mut dev, true);
            let f_down = recurrence(&mut dev, false);
            let g_down = recurrence(&mut dev, false);
            let head = dev.kernel().const_(package.int.rec_unique, vec![level]);
            let applied = dev.apply(
                head,
                &[
                    int_ty, identity, identity, up, down, agree_zero, f_up, g_up, f_down, g_down,
                ],
            );
            let ty = dev
                .kernel()
                .infer(applied)
                .expect("rec_unique's premise list must be satisfiable");
            let name = dev.kernel().name_str(root, "int_rec_unique_instance");
            dev.declare_theorem_u(name, vec![], ty, applied)
                .expect("the instantiated uniqueness theorem must be admitted");
            name
        };
        (induction_witness, unique_witness)
    };
    for witness in [induction_witness, unique_witness] {
        let footprint = footprint_of(&kernel, witness);
        assert!(
            footprint.is_empty(),
            "{} rests on {footprint:?}",
            kernel.display_name(witness)
        );
    }
}

#[test]
fn every_injected_defect_is_rejected() {
    // The positive control first: without a defect the same builder succeeds,
    // so a build that always failed could not pass this test.
    let mut kernel = Kernel::new();
    build_characterization_with(&mut kernel, Weakening::None)
        .expect("the unweakened package must build");

    let defects = Weakening::defects();
    assert!(defects.len() >= 24, "the defect sweep shrank");
    for &defect in defects {
        let mut kernel = Kernel::new();
        let outcome = build_characterization_with(&mut kernel, defect);
        assert!(
            outcome.is_err(),
            "{defect:?} was ACCEPTED: the weakened hypothesis is not load-bearing, \
             so the characterization does not depend on it"
        );
        // ... and it died at the declaration it was aimed at, not at some
        // earlier one it happened to break on the way.
        let target = defect
            .refused_declaration()
            .expect("every defect names the declaration it must kill");
        assert!(
            !is_declared(&kernel, target),
            "{defect:?} failed, but {target} was still admitted"
        );
        // ... and it got all the way there: the declaration immediately before
        // it in build order is present, so the failure is bracketed rather than
        // merely "somewhere at or before the target".
        if let Some(reached) = defect.reached_declaration() {
            assert!(
                is_declared(&kernel, reached),
                "{defect:?} failed before reaching {target}: {reached} is absent"
            );
        }
    }
}

/// Whether the environment carries a declaration with this dotted name.
fn is_declared(kernel: &Kernel, dotted: &str) -> bool {
    kernel
        .environment()
        .iter()
        .any(|(name, _)| kernel.display_name(*name).to_string() == dotted)
}

#[test]
fn every_characterization_kind_is_represented() {
    let mut kernel = Kernel::new();
    let package = build_characterization(&mut kernel).expect("the characterization must build");
    for kind in [
        CharacterizationKind::PeanoAxiom,
        CharacterizationKind::NatUniversalProperty,
        CharacterizationKind::NatCategoricity,
        CharacterizationKind::IntNoJunk,
        CharacterizationKind::IntGeneration,
        CharacterizationKind::IntUniversalProperty,
        CharacterizationKind::IntOrder,
    ] {
        assert!(
            package.entries.iter().any(|entry| entry.kind == kind),
            "no entry contributes {}",
            kind.label()
        );
    }
}

#[test]
#[allow(clippy::too_many_lines)]
fn initial_is_not_vacuous_it_instantiates_at_the_carrier_itself() {
    // Companion to `categoricity_is_not_vacuous_it_instantiates_at_nat_itself`
    // and `the_int_hypothesis_shapes_are_satisfiable`: a universal-property
    // theorem whose hypothesis list nothing satisfies is axiom-free and
    // worthless. `Nat.Peano.initial` needs no hypothesis at all, so it is
    // instantiated directly at `(Nat, zero, succ)`; `Int.Characterization.initial`
    // needs the two inverse laws, discharged here exactly as
    // `categorical_at_int` discharges them — by the ring laws.
    let mut kernel = Kernel::new();
    let package = build_characterization(&mut kernel).expect("the characterization must build");
    let (nat_witness, int_witness) = {
        let mut dev = CharDev::new(&mut kernel, package.int_prelude);
        let level = dev.level_one();

        let nat_witness = {
            let nat_ty = dev.nat_ty();
            let zero = dev.zero();
            let succ = {
                let name = dev.prelude().succ;
                dev.kernel().const_(name, vec![])
            };
            let head = dev
                .kernel()
                .const_(package.nat_universal_property.initial, vec![level]);
            let applied = dev.apply(head, &[nat_ty, zero, succ]);
            let ty = dev
                .kernel()
                .infer(applied)
                .expect("Nat.Peano.initial needs no hypothesis and must accept (Nat, zero, succ)");
            let anon = dev.anon_name();
            let root = dev.kernel().name_str(anon, "Characterization");
            let name = dev.kernel().name_str(root, "initial_at_nat");
            dev.declare_theorem_u(name, vec![], ty, applied)
                .expect("the instantiated Nat.Peano.initial must be admitted");
            name
        };

        let int_witness = {
            let int_ty = dev.int_ty();
            let prelude = dev.int_prelude();
            let one = ione(&mut dev);
            let zero = izero(&mut dev);
            let minus = ineg(&mut dev, one);
            let int_up = {
                let t_fv = dev.fresh_fvar();
                let t = dev.kernel().fvar(t_fv);
                let body = iadd(&mut dev, t, one);
                dev.lam_fv(t_fv, int_ty, body)
            };
            let int_down = {
                let t_fv = dev.fresh_fvar();
                let t = dev.kernel().fvar(t_fv);
                let body = iadd(&mut dev, t, minus);
                dev.lam_fv(t_fv, int_ty, body)
            };
            // `(x + a) + b = x` given `a + b = 0`.
            let cancel =
                |d: &mut CharDev<'_>, first: ExprId, second: ExprId, zero_proof: ExprId| {
                    let x_fv = d.fresh_fvar();
                    let x = d.kernel().fvar(x_fv);
                    let shifted = iadd(d, x, first);
                    let restored = iadd(d, shifted, second);
                    let inner_sum = iadd(d, first, second);
                    let regrouped = iadd(d, x, inner_sum);
                    let with_zero = iadd(d, x, zero);
                    let int_ty = d.int_ty();
                    let assoc = d.const_app(prelude.add_assoc, &[x, first, second]);
                    let collapsed = d.congr_at(
                        level,
                        int_ty,
                        level,
                        int_ty,
                        inner_sum,
                        zero,
                        zero_proof,
                        &|d2, z| iadd(d2, x, z),
                    );
                    let absorbed = d.const_app(prelude.add_zero, &[x]);
                    let prefix = d.trans_at(
                        level, int_ty, restored, regrouped, with_zero, assoc, collapsed,
                    );
                    let body = d.trans_at(level, int_ty, restored, with_zero, x, prefix, absorbed);
                    d.lam_fv(x_fv, int_ty, body)
                };
            let one_minus = iadd(&mut dev, one, minus);
            let minus_one_sum = iadd(&mut dev, minus, one);
            let add_neg_one = dev.const_app(prelude.add_neg, &[one]);
            let commuted = dev.const_app(prelude.add_comm, &[minus, one]);
            let flipped = dev.trans_at(
                level,
                int_ty,
                minus_one_sum,
                one_minus,
                zero,
                commuted,
                add_neg_one,
            );
            let left_proof = cancel(&mut dev, one, minus, add_neg_one);
            let right_proof = cancel(&mut dev, minus, one, flipped);

            let head = dev
                .kernel()
                .const_(package.int_universal_property.initial, vec![level]);
            let applied = dev.apply(
                head,
                &[int_ty, zero, int_up, int_down, left_proof, right_proof],
            );
            let ty = dev.kernel().infer(applied).expect(
                "Int.Characterization.initial's two inverse-law hypotheses must be satisfiable",
            );
            let anon = dev.anon_name();
            let root = dev.kernel().name_str(anon, "Characterization");
            let name = dev.kernel().name_str(root, "initial_at_int");
            dev.declare_theorem_u(name, vec![], ty, applied)
                .expect("the instantiated Int.Characterization.initial must be admitted");
            name
        };
        (nat_witness, int_witness)
    };
    for witness in [nat_witness, int_witness] {
        let footprint = footprint_of(&kernel, witness);
        assert!(
            footprint.is_empty(),
            "{} rests on {footprint:?}",
            kernel.display_name(witness)
        );
    }
}
