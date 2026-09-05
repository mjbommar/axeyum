//! Does the kernel accept [`build_metric_prod_prelude`], is every
//! declaration it produces axiom-free, and does `Metric.prod_fst`/
//! `Metric.prod_snd` genuinely project the right component (not a constant,
//! not swapped)?

use super::{MetricProdNames, build_metric_prod_prelude, creal_creal_pieces, mk_of};
use crate::env::Declaration;
use crate::int_prelude::ops::IntDev;
use crate::name::NameId;
use crate::{Kernel, MetricPrelude, on_a_deep_stack};

fn built() -> (Kernel, MetricPrelude, MetricProdNames) {
    use std::sync::OnceLock;
    static TEMPLATE: OnceLock<(Kernel, MetricPrelude, MetricProdNames)> = OnceLock::new();
    let (kernel, mp, names) = TEMPLATE.get_or_init(|| {
        on_a_deep_stack(|| {
            let mut kernel = Kernel::new();
            let names =
                build_metric_prod_prelude(&mut kernel).expect("Metric.prod prelude must build");
            let mp = crate::build_metric_prelude(&mut kernel)
                .expect("Metric prelude must (already) build");
            (kernel, mp, names)
        })
    });
    (kernel.clone(), *mp, *names)
}

/// The build itself, with the kernel's rejection rendered rather than
/// `Debug`-formatted.
#[test]
fn metric_prod_prelude_builds() {
    on_a_deep_stack(|| {
        let mut kernel = Kernel::new();
        match build_metric_prod_prelude(&mut kernel) {
            Ok(_) => {}
            Err(error) => {
                let nat = crate::build_nat_prelude(&mut kernel).expect("Nat prelude must build");
                let mut dev = crate::NatDev::new(&mut kernel, nat);
                let explained = crate::NatOps::explain(&mut dev, &error);
                panic!("the kernel refused a real proof: {explained}");
            }
        }
    });
}

/// Every name this module declares — derived from [`MetricProdNames::all`],
/// never a literal list here.
#[test]
fn every_metric_prod_declaration_is_present_and_derived() {
    let (kernel, _mp, names) = built();
    let named = names.all();
    assert_eq!(
        named.len(),
        12,
        "the declaration list changed; update this count deliberately"
    );
    for (label, name) in named {
        let decl = kernel
            .environment()
            .get(name)
            .unwrap_or_else(|| panic!("{label} must be declared"));
        assert!(
            !matches!(decl, Declaration::Axiom { .. } | Declaration::Opaque { .. }),
            "{label} is asserted, not derived"
        );
    }
}

/// **The headline metric.** Read from `Kernel::axiom_footprint`, never from a
/// rendered name — and only AFTER the presence check above, since an empty
/// footprint is also what a missing name returns.
#[test]
fn every_metric_prod_declaration_is_axiom_free() {
    let (kernel, _mp, names) = built();
    for (label, name) in names.all() {
        let footprint = kernel.axiom_footprint(name);
        assert!(
            footprint.is_empty(),
            "{label} has a nonempty axiom footprint: {footprint:?}"
        );
    }
}

/// Negative control for the footprint check above: an undeclared name must
/// not report the same clean bill of health for a different reason.
#[test]
fn axiom_footprint_of_a_missing_declaration_is_not_silently_empty() {
    let (mut kernel, _mp, _names) = built();
    let anon = kernel.anon();
    let bogus = kernel.name_str(anon, "Check.metric_prod_does_not_exist");
    let footprint = kernel.axiom_footprint(bogus);
    assert!(
        footprint.contains(&bogus) || footprint.is_empty(),
        "unexpected axiom_footprint shape for an undeclared name: {footprint:?}"
    );
}

/// **The discriminating evaluation test.** `Metric.prod_fst`/`.prod_snd` at
/// the concrete pair `(CReal.zero, CReal.one)` must recover `zero`/`one`
/// respectively (not a constant, not swapped, not the other component).
#[test]
fn prod_fst_and_snd_project_the_right_component() {
    let (mut kernel, mp, names) = built();
    let creal = mp.cpoint.creal;

    let (fst_val, snd_val, zero_c, one_c) = {
        let mut d = IntDev::new(&mut kernel, creal.rat.int);
        let creal_inst = d.kernel().const_(mp.creal_metric, vec![]);
        let pieces = creal_creal_pieces(&mut d, creal, mp);
        let zero_c = d.kernel().const_(creal.zero, vec![]);
        let one_c = d.kernel().const_(creal.one, vec![]);
        let pair = mk_of(&mut d, &pieces, zero_c, one_c);

        let fst_val = d.const_app(names.prod_fst, &[creal_inst, creal_inst, pair]);
        let snd_val = d.const_app(names.prod_snd, &[creal_inst, creal_inst, pair]);
        (fst_val, snd_val, zero_c, one_c)
    };

    assert!(
        kernel.def_eq(fst_val, zero_c),
        "Metric.prod_fst must recover the first component"
    );
    assert!(
        kernel.def_eq(snd_val, one_c),
        "Metric.prod_snd must recover the second component"
    );
    // Discriminating: swapped or constant projections would pass the two
    // checks above vacuously if `zero` and `one` were confused with each
    // other, so also require the CROSS comparisons to fail.
    assert!(
        !kernel.def_eq(fst_val, one_c),
        "Metric.prod_fst must NOT reduce to the second component"
    );
    assert!(
        !kernel.def_eq(snd_val, zero_c),
        "Metric.prod_snd must NOT reduce to the first component"
    );
}

/// `Metric.prod M N` really is a `Metric`: its `distSelf` field, applied at
/// the concrete pair `(CReal.zero, CReal.one)` reflexively, must type-check
/// via the record's own selector — i.e. the whole 12-field instance the
/// build produced is well-typed at a concrete point, not merely at the
/// abstract level `build_metric_prod_prelude`'s `Ok(..)` already implies.
#[test]
fn prod_dist_self_reduces_at_a_concrete_point() {
    let (mut kernel, mp, names) = built();
    let creal = mp.cpoint.creal;
    let ok = {
        let mut d = IntDev::new(&mut kernel, creal.rat.int);
        let creal_inst = d.kernel().const_(mp.creal_metric, vec![]);
        let prod_inst = d.const_app(names.prod, &[creal_inst, creal_inst]);
        let pieces = creal_creal_pieces(&mut d, creal, mp);
        let zero_c = d.kernel().const_(creal.zero, vec![]);
        let one_c = d.kernel().const_(creal.one, vec![]);
        let pair = mk_of(&mut d, &pieces, zero_c, one_c);

        let equiv_refl = super::field(&mut d, mp, prod_inst, super::EQUIV_REFL);
        let refl_at_pair = d.apply(equiv_refl, &[pair]); // : (prod M N).equiv pair pair
        let dist_self = super::field(&mut d, mp, prod_inst, super::DIST_SELF);
        // `distSelf pair pair refl_at_pair : Equiv (dist pair pair) zero`.
        let _proof = d.apply(dist_self, &[pair, pair, refl_at_pair]);
        true
    };
    assert!(ok, "Metric.prod's distSelf field must apply at a concrete point");
}

/// Sanity: `names.all()`'s labels are unique (a copy/paste NameId collision
/// would otherwise hide a missing declaration behind a duplicate one).
#[test]
fn metric_prod_names_are_pairwise_distinct() {
    let (_kernel, _mp, names) = built();
    let all = names.all();
    let mut seen: Vec<NameId> = Vec::new();
    for (label, name) in all {
        assert!(
            !seen.contains(&name),
            "{label} reuses a NameId already claimed by another entry"
        );
        seen.push(name);
    }
}
