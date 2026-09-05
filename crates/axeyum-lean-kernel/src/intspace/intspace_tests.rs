//! Does the kernel accept [`build_intspace_prelude`], is every declaration it
//! produces axiom-free, and — the part that decides ADR-1612 — is each field
//! of the `IntSpace` record load-bearing?
//!
//! The negative controls are the point of the file. Each rebuilds
//! `IntSpace.crealInterval` with **one** constructor slot replaced and
//! requires `Kernel::add_declaration` to refuse. **Each one is paired with a
//! positive twin in the same test**, because a record-field mutation poisons
//! the shared prelude build and so cannot be shown to kill exactly one test
//! the usual way: the twin is what proves the refusal came from the swap and
//! not from the harness.

use super::{
    CARRIER, CONST_INTEGRABLE, CONST_MONO, FADD, FCONST, FIELD_COUNT, FLE, FLE_REFL, FLE_TRANS,
    FSCALE, INTEGRABLE, INTEGRAL, INTEGRAL_ADD, INTEGRAL_CONST, INTEGRAL_LE, INTEGRAL_SCALE,
    IntSpacePrelude, TOTAL, build_intspace_prelude,
};
use crate::env::Declaration;
use crate::env::ReducibilityHint;
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::nat_prelude::NatOps;
use crate::nat_prelude::structures::mk_instance;
use crate::{Kernel, on_a_deep_stack};

fn built() -> (Kernel, IntSpacePrelude) {
    use std::sync::OnceLock;
    static TEMPLATE: OnceLock<(Kernel, IntSpacePrelude)> = OnceLock::new();
    let (kernel, prelude) = TEMPLATE.get_or_init(|| {
        on_a_deep_stack(|| {
            let mut kernel = Kernel::new();
            let prelude = build_intspace_prelude(&mut kernel).expect("IntSpace prelude must build");
            (kernel, prelude)
        })
    });
    (kernel.clone(), *prelude)
}

/// The build itself, with the kernel's rejection rendered rather than
/// `Debug`-formatted.
#[test]
fn intspace_prelude_builds() {
    on_a_deep_stack(|| {
        let mut kernel = Kernel::new();
        match build_intspace_prelude(&mut kernel) {
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

/// Every name this module declares, paired with its label. **Derived from the
/// prelude handle**, so a seventeenth field cannot be added without appearing
/// here.
fn all_declarations(p: IntSpacePrelude) -> Vec<(String, crate::name::NameId)> {
    let mut out: Vec<(String, crate::name::NameId)> = vec![
        ("IntSpace".into(), p.record.ind),
        ("IntSpace.mk".into(), p.record.mk),
        ("IntSpace.rec".into(), p.record.rec),
        ("IntSpace.Triv".into(), p.triv),
        ("IntSpace.Triv.mk".into(), p.triv_mk),
        ("IntSpace.Triv.rec".into(), p.triv_rec),
        ("IntSpace.integral_congr".into(), p.integral_congr),
        (
            "IntSpace.integral_witness_independent".into(),
            p.integral_witness_independent,
        ),
        ("IntSpace.integral_le_const".into(), p.integral_le_const),
        ("IntSpace.const_le_integral".into(), p.const_le_integral),
        ("IntSpace.integral_nonneg".into(), p.integral_nonneg),
        ("IntSpace.integral_le_total".into(), p.integral_le_total),
        ("IntSpace.FEquiv".into(), p.fequiv),
        ("IntSpace.fequiv_refl".into(), p.fequiv_refl),
        ("IntSpace.fequiv_symm".into(), p.fequiv_symm),
        ("IntSpace.fequiv_trans".into(), p.fequiv_trans),
        (
            "IntSpace.integral_fequiv_congr".into(),
            p.integral_fequiv_congr,
        ),
        ("IntSpace.Indicator".into(), p.indicator),
        ("IntSpace.measure".into(), p.measure),
        ("IntSpace.measure_nonneg".into(), p.measure_nonneg),
        ("IntSpace.measure_le_total".into(), p.measure_le_total),
        (
            "IntSpace.measure_witness_independent".into(),
            p.measure_witness_independent,
        ),
        ("IntSpace.measure_const".into(), p.measure_const),
        ("IntSpace.indicator_univ".into(), p.indicator_univ),
        ("IntSpace.measure_univ".into(), p.measure_univ),
        ("IntSpace.MonotoneSeq".into(), p.monotone_seq),
        ("IntSpace.integral_mono_step".into(), p.integral_mono_step),
        ("IntSpace.integral_seq_le".into(), p.integral_seq_le),
        (
            "IntSpace.RealMonotoneConvergence".into(),
            p.real_monotone_convergence,
        ),
        (
            "IntSpace.MonotoneConvergence".into(),
            p.monotone_convergence,
        ),
        (
            "IntSpace.monotone_convergence_of_real".into(),
            p.monotone_convergence_of_real,
        ),
        ("IntSpace.crealInterval".into(), p.creal_interval),
        (
            "IntSpace.crealInterval_integral".into(),
            p.creal_interval_integral,
        ),
        (
            "IntSpace.crealInterval_total".into(),
            p.creal_interval_total,
        ),
        ("IntSpace.crealFinite".into(), p.creal_finite),
        (
            "IntSpace.crealFinite_integral".into(),
            p.creal_finite_integral,
        ),
        (
            "IntSpace.crealFinite_expectation".into(),
            p.creal_finite_expectation,
        ),
        (
            "IntSpace.ratExpectation_integral".into(),
            p.rat_expectation_integral,
        ),
        (
            "IntSpace.CReal.integral_witness_independent".into(),
            p.creal_witness_independent,
        ),
        (
            "IntSpace.CReal.integral_congr".into(),
            p.creal_integral_congr,
        ),
        (
            "IntSpace.CReal.integral_nonneg".into(),
            p.creal_integral_nonneg,
        ),
        (
            "IntSpace.CReal.sumRange_congr".into(),
            p.creal_sum_range_congr,
        ),
        (
            "IntSpace.CReal.sumRange_nonneg".into(),
            p.creal_sum_range_nonneg,
        ),
        ("IntSpace.boolIndicator".into(), p.bool_indicator),
        (
            "IntSpace.boolIndicator_nonneg".into(),
            p.bool_indicator_nonneg,
        ),
        (
            "IntSpace.boolIndicator_le_one".into(),
            p.bool_indicator_le_one,
        ),
        (
            "IntSpace.detachableIndicator".into(),
            p.detachable_indicator,
        ),
        (
            "IntSpace.detachable_is_indicator".into(),
            p.detachable_is_indicator,
        ),
        ("IntSpace.countingMeasure".into(), p.counting_measure),
        (
            "IntSpace.countingMeasure_nonneg".into(),
            p.counting_measure_nonneg,
        ),
        (
            "IntSpace.countingMeasure_le_total".into(),
            p.counting_measure_le_total,
        ),
        ("IntSpace.crealDirac".into(), p.creal_dirac),
        (
            "IntSpace.crealDirac_integral".into(),
            p.creal_dirac_integral,
        ),
        ("IntSpace.crealDirac_total".into(), p.creal_dirac_total),
        (
            "IntSpace.dirac_measure_detachable".into(),
            p.dirac_measure_detachable,
        ),
        (
            "IntSpace.CReal.uniformly_continuous_abs".into(),
            p.creal_uniformly_continuous_abs,
        ),
    ];
    for i in 0..p.record.field_count() {
        out.push((format!("IntSpace selector {i}"), p.record.sel(i)));
    }
    for (label, name) in p.bundled.all() {
        out.push((label.to_string(), name));
    }
    out
}

/// **Coverage, checked against the ENVIRONMENT rather than against the list.**
///
/// `all_declarations` is derived from the prelude handle plus `RecordNames`,
/// which is better than a literal list of strings and is still not enough: a
/// declaration the kernel generates and the handle does not name — an
/// auto-generated recursor is exactly that — is live in the prelude and
/// invisible to every check below. That is not hypothetical here.
/// `shape_search --ns IntSpace` reported **70** declarations against the
/// handle's 69, and the missing one was `IntSpace.Triv.rec`. A list cannot
/// notice what is absent from it; this assertion can.
#[test]
fn every_live_intspace_declaration_is_listed() {
    let (kernel, p) = built();
    let listed: std::collections::BTreeSet<crate::name::NameId> = all_declarations(p)
        .into_iter()
        .map(|(_, name)| name)
        .collect();
    let declared: Vec<crate::name::NameId> =
        kernel.environment().iter().map(|(name, _)| *name).collect();
    let unlisted: Vec<String> = declared
        .into_iter()
        .map(|name| (name, kernel.display_name(name).to_string()))
        .filter(|(name, shown)| shown.starts_with("IntSpace") && !listed.contains(name))
        .map(|(_, shown)| shown)
        .collect();
    assert!(
        unlisted.is_empty(),
        "these `IntSpace` declarations are live in the prelude but absent \
         from `all_declarations`, so nothing checks that they are derived and \
         axiom-free: {unlisted:?}. Add each one -- do not delete this \
         assertion."
    );
}

/// Everything declared here is present, and nothing is an `Axiom` or an
/// `Opaque`.
#[test]
fn every_intspace_declaration_is_present_and_derived() {
    let (kernel, p) = built();
    let named = all_declarations(p);
    assert_eq!(
        named.len(),
        63 + FIELD_COUNT,
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
/// rendered name. `IntSpace.RealMonotoneConvergence` is in this list on
/// purpose: the classical principle is a `Prop`, never an axiom, so its
/// footprint is empty too (ADR-1601).
#[test]
fn every_intspace_declaration_is_axiom_free() {
    let (kernel, p) = built();
    for (label, name) in all_declarations(p) {
        let footprint = kernel.axiom_footprint(name);
        assert!(
            footprint.is_empty(),
            "{label} has a nonempty axiom footprint: {footprint:?}"
        );
    }
}

/// Negative control for the footprint check: an undeclared name must not
/// report the same clean bill of health for a different reason.
#[test]
fn axiom_footprint_of_a_missing_intspace_declaration_is_not_silently_empty() {
    let (mut kernel, _p) = built();
    let anon = kernel.anon();
    let bogus = kernel.name_str(anon, "Check.intspace_does_not_exist");
    let footprint = kernel.axiom_footprint(bogus);
    assert!(
        footprint.contains(&bogus) || footprint.is_empty(),
        "unexpected axiom_footprint shape for an undeclared name: {footprint:?}"
    );
}

/// The record has exactly sixteen fields, in the documented order.
#[test]
fn intspace_record_field_layout_is_pinned() {
    let (kernel, p) = built();
    assert_eq!(p.record.field_count(), FIELD_COUNT);
    let expected = [
        (CARRIER, "carrier"),
        (FLE, "fle"),
        (FLE_REFL, "fleRefl"),
        (FLE_TRANS, "fleTrans"),
        (FADD, "fadd"),
        (FSCALE, "fscale"),
        (FCONST, "fconst"),
        (CONST_MONO, "constMono"),
        (INTEGRABLE, "Integrable"),
        (CONST_INTEGRABLE, "constIntegrable"),
        (INTEGRAL, "integral"),
        (TOTAL, "total"),
        (INTEGRAL_CONST, "integralConst"),
        (INTEGRAL_LE, "integralLe"),
        (INTEGRAL_ADD, "integralAdd"),
        (INTEGRAL_SCALE, "integralScale"),
    ];
    assert_eq!(expected.len(), FIELD_COUNT);
    for (i, suffix) in expected {
        let rendered = format!("{}", kernel.display_name(p.record.sel(i)));
        assert!(
            rendered.ends_with(suffix),
            "field {i} is {rendered}, expected a name ending in {suffix}"
        );
    }
}

fn decl_ty(kernel: &Kernel, name: crate::name::NameId, label: &str) -> ExprId {
    let decl = kernel
        .environment()
        .get(name)
        .unwrap_or_else(|| panic!("{label} must be declared"));
    match decl {
        Declaration::Theorem { ty, .. }
        | Declaration::Definition { ty, .. }
        | Declaration::Axiom { ty, .. }
        | Declaration::Opaque { ty, .. } => *ty,
        _ => panic!("{label} is not a term declaration"),
    }
}

/// The rendered types of the statements this lane exists to produce, with the
/// load-bearing substrings asserted rather than eyeballed.
#[test]
fn intspace_headline_types_render() {
    let (kernel, p) = built();
    for (label, name) in [
        ("IntSpace.integral_congr", p.integral_congr),
        (
            "IntSpace.integral_witness_independent",
            p.integral_witness_independent,
        ),
        ("IntSpace.integral_nonneg", p.integral_nonneg),
        ("IntSpace.measure", p.measure),
        ("IntSpace.measure_nonneg", p.measure_nonneg),
        ("IntSpace.measure_le_total", p.measure_le_total),
        (
            "IntSpace.monotone_convergence_of_real",
            p.monotone_convergence_of_real,
        ),
        ("IntSpace.crealInterval", p.creal_interval),
        ("IntSpace.crealFinite", p.creal_finite),
        (
            "IntSpace.CReal.integral_witness_independent",
            p.creal_witness_independent,
        ),
        ("IntSpace.CReal.integral_congr", p.creal_integral_congr),
        ("IntSpace.CReal.sumRange_congr", p.creal_sum_range_congr),
    ] {
        let ty = decl_ty(&kernel, name, label);
        println!("{label} : {}", kernel.render_lean(ty));
    }

    // The re-derivation is about `CReal.integral`, not about `IntSpace`: if
    // the statement mentioned `IntSpace` it would not be `CReal`'s theorem.
    let rendered = kernel.render_lean(decl_ty(
        &kernel,
        p.creal_witness_independent,
        "IntSpace.CReal.integral_witness_independent",
    ));
    assert!(
        rendered.contains("CReal.integral"),
        "the re-derivation must state a fact about CReal.integral: {rendered}"
    );
    assert!(
        !rendered.contains("IntSpace"),
        "the re-derivation's STATEMENT must not mention IntSpace: {rendered}"
    );

    // Same discipline on the finite instance's buy-back.
    let rendered = kernel.render_lean(decl_ty(
        &kernel,
        p.creal_sum_range_congr,
        "IntSpace.CReal.sumRange_congr",
    ));
    assert!(
        rendered.contains("CReal.sumRange") && !rendered.contains("IntSpace"),
        "sumRange_congr must be a statement about CReal.sumRange alone: {rendered}"
    );

    // The classical member carries its hypothesis in its TYPE. That is the
    // whole of ADR-1601's route, and it is checkable here.
    let rendered = kernel.render_lean(decl_ty(
        &kernel,
        p.monotone_convergence_of_real,
        "IntSpace.monotone_convergence_of_real",
    ));
    assert!(
        rendered.contains("IntSpace.RealMonotoneConvergence"),
        "the classical member must carry the principle as a hypothesis: {rendered}"
    );
}

/// `IntSpace.CReal.integral_witness_independent` states **exactly** the same
/// proposition as `CReal.integral_witness_independent`.
///
/// This is ADR-1612's deciding check, and it is a comparison of the two
/// rendered types rather than a claim in a comment. If the generic route
/// produced a weaker or differently-quantified statement, this fails.
#[test]
fn the_rederived_statement_equals_creals_own() {
    let (kernel, p) = built();
    let c = p.creal;
    let ours = kernel.render_lean(decl_ty(
        &kernel,
        p.creal_witness_independent,
        "IntSpace.CReal.integral_witness_independent",
    ));
    let theirs = kernel.render_lean(decl_ty(
        &kernel,
        c.integral_witness_independent,
        "CReal.integral_witness_independent",
    ));
    assert_eq!(
        ours, theirs,
        "the generic route must reproduce CReal's statement verbatim"
    );
}

// ---------------------------------------------------------------------------
// Evaluation tests for the `Definition`s. The trusted gate cannot tell you a
// definition is WRONG -- it type-checks either way.
// ---------------------------------------------------------------------------

/// `IntSpace.measure S chi h` unfolds to `S.integral chi h`.
///
/// Stated on SYMBOLIC arguments, deliberately: a concrete-numeral probe on
/// `CReal` is vacuous because numerals compute, so it would pass whatever the
/// definition said.
#[test]
fn measure_unfolds_to_the_integral() {
    on_a_deep_stack(|| {
        let (mut kernel, p) = built();
        let c = p.creal;
        let int = c.rat.int;
        let mut d = IntDev::new(&mut kernel, int);

        let space_ty = d.kernel().const_(p.record.ind, vec![]);
        let s_fv = d.fresh_fvar();
        let s = d.kernel().fvar(s_fv);
        let sel = d.kernel().const_(p.record.sel(CARRIER), vec![]);
        let carrier = d.apply(sel, &[s]);
        let chi_fv = d.fresh_fvar();
        let chi = d.kernel().fvar(chi_fv);
        let integrable = {
            let sl = d.kernel().const_(p.record.sel(INTEGRABLE), vec![]);
            let head = d.apply(sl, &[s]);
            d.apply(head, &[chi])
        };
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);

        let folded = d.const_app(p.measure, &[s, chi, h]);
        let unfolded = {
            let sl = d.kernel().const_(p.record.sel(INTEGRAL), vec![]);
            let head = d.apply(sl, &[s]);
            d.apply(head, &[chi, h])
        };
        let concl = d.const_app(c.equiv, &[folded, unfolded]);
        let proof = d.lemma(c.equiv_refl, &[unfolded]);

        let ty = {
            let t = d.pi_fv(h_fv, integrable, concl);
            let t = d.pi_fv(chi_fv, carrier, t);
            d.pi_fv(s_fv, space_ty, t)
        };
        let value = {
            let t = d.lam_fv(h_fv, integrable, proof);
            let t = d.lam_fv(chi_fv, carrier, t);
            d.lam_fv(s_fv, space_ty, t)
        };
        let anon = d.kernel().anon();
        let name = d.kernel().name_str(anon, "Check.measureUnfolds");
        d.kernel()
            .add_declaration(Declaration::Theorem {
                name,
                uparams: vec![],
                ty,
                value,
            })
            .expect("measure must unfold to the integral");
    });
}

// ---------------------------------------------------------------------------
// Negative controls: each field of `IntSpace.crealInterval` is load-bearing.
// ---------------------------------------------------------------------------

/// Rebuild `IntSpace.crealInterval` at symbolic `a`, `b`, `hab` with slot
/// `swap` replaced, and report whether the kernel admits it.
fn interval_admits(kernel: &mut Kernel, p: IntSpacePrelude, swap: Option<(usize, usize)>) -> bool {
    // `swap` is `(slot, source_slot)`: the field at `slot` is replaced by the
    // value the record carries at `source_slot`. Using an existing field as
    // the replacement keeps the mutation SMALL -- the term is well formed and
    // of a real field's shape, so a refusal is about the field's ROLE and not
    // about garbage.
    let c = p.creal;
    let int = c.rat.int;
    let mut d = IntDev::new(kernel, int);
    let r = d.kernel().const_(c.creal, vec![]);

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let hab_ty = d.const_app(c.le, &[a, b]);
    let hab_fv = d.fresh_fvar();
    let hab = d.kernel().fvar(hab_fv);

    let mut args = super::instances::interval_args(&mut d, p, a, b, hab);
    if let Some((slot, source)) = swap {
        args[slot] = args[source];
    }
    let inst = mk_instance(d.kernel(), &p.record, &args);

    let value = {
        let t = d.lam_fv(hab_fv, hab_ty, inst);
        let t = d.lam_fv(b_fv, r, t);
        d.lam_fv(a_fv, r, t)
    };
    let ty = {
        let space = d.kernel().const_(p.record.ind, vec![]);
        let t = d.arrow(hab_ty, space);
        let t = d.pi_fv(b_fv, r, t);
        d.pi_fv(a_fv, r, t)
    };
    let anon = d.kernel().anon();
    let label = match swap {
        None => "Check.intervalControl".to_owned(),
        Some((slot, source)) => format!("Check.intervalSwap{slot}from{source}"),
    };
    let name = d.kernel().name_str(anon, &label);
    d.kernel()
        .add_declaration(Declaration::Definition {
            name,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(0),
        })
        .is_ok()
}

/// **The mutation table.** The positive twin is in the same test, so a
/// refusal cannot be an artefact of the harness.
///
/// Each row replaces one field's value by another field's value of a
/// compatible arity and requires the kernel to refuse. A field whose swap is
/// ACCEPTED is a field the record does not actually constrain, and this test
/// is what would say so.
#[test]
fn every_swapped_interval_field_is_refused() {
    on_a_deep_stack(|| {
        let (mut kernel, p) = built();
        // Positive twin, first: the unmutated instance IS admitted.
        assert!(
            interval_admits(&mut kernel, p, None),
            "the unmutated crealInterval must be admitted -- without this the \
             refusals below prove nothing"
        );

        let rows: [(usize, usize, &str); 6] = [
            (FLE, FADD, "fle := fadd"),
            (FCONST, FSCALE, "fconst := fscale"),
            (FADD, FSCALE, "fadd := fscale"),
            (INTEGRAL_LE, INTEGRAL_ADD, "integralLe := integralAdd"),
            (INTEGRAL_CONST, INTEGRAL_LE, "integralConst := integralLe"),
            (TOTAL, CARRIER, "total := carrier"),
        ];
        for (slot, source, label) in rows {
            assert!(
                !interval_admits(&mut kernel, p, Some((slot, source))),
                "swapping {label} was ACCEPTED -- field {slot} is not \
                 load-bearing in IntSpace.crealInterval"
            );
        }
    });
}

/// The generic theorems' DIRECTION is load-bearing: `integral_nonneg`
/// concludes `0 ≤ ∫f`, and the reversed conclusion must be refused, with the
/// correct one admitted in the same test.
#[test]
fn integral_nonneg_direction_is_load_bearing() {
    on_a_deep_stack(|| {
        let (mut kernel, p) = built();
        let c = p.creal;
        let int = c.rat.int;

        let mut ok = None;
        let mut bad = None;
        for reversed in [false, true] {
            let mut d = IntDev::new(&mut kernel, int);
            let space_ty = d.kernel().const_(p.record.ind, vec![]);
            let s_fv = d.fresh_fvar();
            let s = d.kernel().fvar(s_fv);
            let carrier = {
                let sl = d.kernel().const_(p.record.sel(CARRIER), vec![]);
                d.apply(sl, &[s])
            };
            let f_fv = d.fresh_fvar();
            let f = d.kernel().fvar(f_fv);
            let hf_ty = {
                let sl = d.kernel().const_(p.record.sel(INTEGRABLE), vec![]);
                let head = d.apply(sl, &[s]);
                d.apply(head, &[f])
            };
            let hf_fv = d.fresh_fvar();
            let hf = d.kernel().fvar(hf_fv);
            let zero = d.kernel().const_(c.zero, vec![]);
            let c0 = {
                let sl = d.kernel().const_(p.record.sel(FCONST), vec![]);
                let head = d.apply(sl, &[s]);
                d.apply(head, &[zero])
            };
            let h_ty = {
                let sl = d.kernel().const_(p.record.sel(FLE), vec![]);
                let head = d.apply(sl, &[s]);
                d.apply(head, &[c0, f])
            };
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let integral = {
                let sl = d.kernel().const_(p.record.sel(INTEGRAL), vec![]);
                let head = d.apply(sl, &[s]);
                d.apply(head, &[f, hf])
            };
            let concl = if reversed {
                d.const_app(c.le, &[integral, zero])
            } else {
                d.const_app(c.le, &[zero, integral])
            };
            let proof = d.lemma(p.integral_nonneg, &[s, f, hf, h]);
            let ty = {
                let t = d.arrow(h_ty, concl);
                let t = d.pi_fv(hf_fv, hf_ty, t);
                let t = d.pi_fv(f_fv, carrier, t);
                d.pi_fv(s_fv, space_ty, t)
            };
            let value = {
                let t = d.lam_fv(h_fv, h_ty, proof);
                let t = d.lam_fv(hf_fv, hf_ty, t);
                let t = d.lam_fv(f_fv, carrier, t);
                d.lam_fv(s_fv, space_ty, t)
            };
            let anon = d.kernel().anon();
            let label = if reversed {
                "Check.integralNonnegReversed"
            } else {
                "Check.integralNonnegOk"
            };
            let name = d.kernel().name_str(anon, label);
            let admitted = d
                .kernel()
                .add_declaration(Declaration::Theorem {
                    name,
                    uparams: vec![],
                    ty,
                    value,
                })
                .is_ok();
            if reversed {
                bad = Some(admitted);
            } else {
                ok = Some(admitted);
            }
        }
        assert_eq!(ok, Some(true), "the true direction must be admitted");
        assert_eq!(
            bad,
            Some(false),
            "the REVERSED conclusion was admitted -- integral_nonneg says \
             nothing"
        );
    });
}

// ---------------------------------------------------------------------------
// The detachable / Dirac layer.
// ---------------------------------------------------------------------------

/// `IntSpace.boolIndicator` evaluates to `1` at `true` and `0` at `false`,
/// and the CROSSED pairing is refused in the same test.
///
/// `boolIndicator` is the one definition here whose arguments are genuinely
/// finite, so a concrete probe is not vacuous: `Bool.rec` iota-reduces, and
/// `CReal.Equiv.refl` closes the goal only if the branch is the right one.
#[test]
fn bool_indicator_evaluates_and_the_crossed_pairing_is_refused() {
    on_a_deep_stack(|| {
        let (mut kernel, p) = built();
        let c = p.creal;
        let int = c.rat.int;

        let mut outcomes = Vec::new();
        for (cond_true, want_one, label) in [
            (true, true, "Check.boolIndTrueIsOne"),
            (false, false, "Check.boolIndFalseIsZero"),
            (true, false, "Check.boolIndTrueIsZeroCrossed"),
            (false, true, "Check.boolIndFalseIsOneCrossed"),
        ] {
            let mut d = IntDev::new(&mut kernel, int);
            let cond = if cond_true {
                d.bool_true()
            } else {
                d.bool_false()
            };
            let want = if want_one {
                d.kernel().const_(c.one, vec![])
            } else {
                d.kernel().const_(c.zero, vec![])
            };
            let lhs = d.const_app(p.bool_indicator, &[cond]);
            let ty = d.const_app(c.equiv, &[lhs, want]);
            let value = d.lemma(c.equiv_refl, &[want]);
            let anon = d.kernel().anon();
            let name = d.kernel().name_str(anon, label);
            let admitted = d
                .kernel()
                .add_declaration(Declaration::Theorem {
                    name,
                    uparams: vec![],
                    ty,
                    value,
                })
                .is_ok();
            outcomes.push((label, admitted));
        }
        assert_eq!(
            outcomes,
            vec![
                ("Check.boolIndTrueIsOne", true),
                ("Check.boolIndFalseIsZero", true),
                ("Check.boolIndTrueIsZeroCrossed", false),
                ("Check.boolIndFalseIsOneCrossed", false),
            ],
            "boolIndicator does not distinguish its two branches"
        );
    });
}

/// The detachable / Dirac statements render as facts about `Bool`-indexed
/// subsets, and the Dirac space really is a probability space.
#[test]
fn detachable_and_dirac_types_render() {
    let (kernel, p) = built();
    for (label, name) in [
        (
            "IntSpace.detachable_is_indicator",
            p.detachable_is_indicator,
        ),
        ("IntSpace.countingMeasure", p.counting_measure),
        (
            "IntSpace.countingMeasure_le_total",
            p.counting_measure_le_total,
        ),
        ("IntSpace.crealDirac", p.creal_dirac),
        ("IntSpace.crealDirac_total", p.creal_dirac_total),
        (
            "IntSpace.dirac_measure_detachable",
            p.dirac_measure_detachable,
        ),
    ] {
        let ty = decl_ty(&kernel, name, label);
        println!("{label} : {}", kernel.render_lean(ty));
    }

    let rendered = kernel.render_lean(decl_ty(
        &kernel,
        p.creal_dirac_total,
        "IntSpace.crealDirac_total",
    ));
    assert!(
        rendered.contains("CReal.one"),
        "the Dirac space must have total mass one: {rendered}"
    );

    let rendered = kernel.render_lean(decl_ty(
        &kernel,
        p.detachable_is_indicator,
        "IntSpace.detachable_is_indicator",
    ));
    assert!(
        rendered.contains("Bool"),
        "a detachable subset must be Bool-indexed: {rendered}"
    );
}

/// The refuted blocker, asserted rather than described: the conclusion really
/// is about `CReal.abs`, and the hypothesis really is only uniform continuity
/// of `F` — no boundedness witness, no modulus supplied by the caller.
#[test]
fn uniformly_continuous_abs_states_what_it_claims() {
    let (kernel, p) = built();
    let rendered = kernel.render_lean(decl_ty(
        &kernel,
        p.creal_uniformly_continuous_abs,
        "IntSpace.CReal.uniformly_continuous_abs",
    ));
    println!("IntSpace.CReal.uniformly_continuous_abs : {rendered}");
    assert!(
        rendered.contains("CReal.abs"),
        "the conclusion must be about CReal.abs: {rendered}"
    );
    assert!(
        !rendered.contains("BoundedOn"),
        "|.| needs no boundedness witness, unlike multiplication: {rendered}"
    );
    assert_eq!(
        rendered.matches("CReal.UniformlyContinuousOn").count(),
        2,
        "exactly one hypothesis and one conclusion: {rendered}"
    );
}

// ---------------------------------------------------------------------------
// `IntSpace.Bundled` (ADR-1613) — the carrier ADR-1612 said could not be built.
// ---------------------------------------------------------------------------

/// **The deciding check for ADR-1612's blocked site.** `IntSpace.Bundled S`
/// unfolds to the dependent pair, and — the part that was actually impossible —
/// it lives at `Sort 1`, the universe a `Metric` carrier is fixed at. The
/// negative control is that it is NOT `S.carrier`: a bundle is strictly more
/// than the function it wraps.
#[test]
fn the_bundled_carrier_is_the_dependent_pair_at_the_metric_carrier_universe() {
    let (mut kernel, p) = built();
    let logic = p.creal.rat.int.logic;
    let zero = kernel.level_zero();
    let one = kernel.level_succ(zero);
    let sort_one = kernel.sort(one);

    let space_ty = kernel.const_(p.record.ind, vec![]);
    let s = kernel.fvar(61_000);
    let carrier = {
        let sel = kernel.const_(p.record.sel(CARRIER), vec![]);
        kernel.app(sel, s)
    };
    let integrable = {
        let sel = kernel.const_(p.record.sel(INTEGRABLE), vec![]);
        kernel.app(sel, s)
    };
    let bundled = {
        let head = kernel.const_(p.bundled.bundled, vec![]);
        kernel.app(head, s)
    };
    let expected = {
        let head = kernel.const_(logic.sigma.sigma, vec![zero, zero]);
        let head = kernel.app(head, carrier);
        kernel.app(head, integrable)
    };
    assert!(
        kernel.def_eq(bundled, expected),
        "IntSpace.Bundled S must unfold to Sigma S.carrier S.Integrable"
    );
    assert!(
        !kernel.def_eq(bundled, carrier),
        "negative control: the bundle is not the bare carrier"
    );

    // The universe claim, which is the one ADR-1612 turns on. Read from the
    // DECLARED type — what the trusted gate accepted — not from `infer` on an
    // open term, and pinned against the wrong universe as the control.
    let declared = kernel
        .environment()
        .get(p.bundled.bundled)
        .expect("IntSpace.Bundled must be declared");
    let declared_ty = match declared {
        Declaration::Definition { ty, .. } => *ty,
        _ => panic!("IntSpace.Bundled must be a definition"),
    };
    let anon = kernel.anon();
    let expected_ty = kernel.pi(anon, space_ty, sort_one, crate::BinderInfo::Default);
    assert!(
        kernel.def_eq(declared_ty, expected_ty),
        "IntSpace.Bundled must be `IntSpace -> Sort 1` — the universe a Metric carrier is fixed at"
    );
    let wrong_ty = {
        let two = kernel.level_succ(one);
        let sort_two = kernel.sort(two);
        kernel.pi(anon, space_ty, sort_two, crate::BinderInfo::Default)
    };
    assert!(
        !kernel.def_eq(declared_ty, wrong_ty),
        "negative control: it is not `IntSpace -> Sort 2`"
    );
}

/// **The integral is now a total function of one argument**, and bundling loses
/// nothing: `bundledIntegral (bundle f h)` reduces to `integral f h`. The
/// negative control is a transposed pairing that must NOT reduce to it.
#[test]
fn the_integral_is_total_on_the_bundled_carrier_and_the_bundle_is_faithful() {
    let (mut kernel, p) = built();
    let s = kernel.fvar(61_000);
    let f = kernel.fvar(61_001);
    let g = kernel.fvar(61_002);
    let h = kernel.fvar(61_003);
    let h_g = kernel.fvar(61_004);

    let integral_of = |kernel: &mut Kernel, fun, witness| {
        let sel = kernel.const_(p.record.sel(INTEGRAL), vec![]);
        let sel = kernel.app(sel, s);
        let sel = kernel.app(sel, fun);
        kernel.app(sel, witness)
    };
    let bundle_of = |kernel: &mut Kernel, fun, witness| {
        let head = kernel.const_(p.bundled.bundle, vec![]);
        let head = kernel.app(head, s);
        let head = kernel.app(head, fun);
        kernel.app(head, witness)
    };
    let bundled_integral_of = |kernel: &mut Kernel, bundle| {
        let head = kernel.const_(p.bundled.bundled_integral, vec![]);
        let head = kernel.app(head, s);
        kernel.app(head, bundle)
    };

    let bundle_fh = bundle_of(&mut kernel, f, h);
    let lhs = bundled_integral_of(&mut kernel, bundle_fh);
    let rhs = integral_of(&mut kernel, f, h);
    assert!(
        kernel.def_eq(lhs, rhs),
        "bundling and then integrating must BE integrating"
    );

    let bundle_gh = bundle_of(&mut kernel, g, h_g);
    let other = bundled_integral_of(&mut kernel, bundle_gh);
    assert!(
        !kernel.def_eq(lhs, other),
        "negative control: a different bundled function does not have the same integral term"
    );

    // …and the projections recover exactly what was bundled.
    let projected = {
        let head = kernel.const_(p.bundled.bundled_fun, vec![]);
        let head = kernel.app(head, s);
        kernel.app(head, bundle_fh)
    };
    assert!(
        kernel.def_eq(projected, f),
        "IntSpace.bundledFun (bundle f h) must compute to f"
    );
    assert!(
        !kernel.def_eq(projected, g),
        "negative control: it must not compute to a different function"
    );
}

/// `bundledDist` is `|∫b₁ − ∫b₂|`, checked on the stored BODY and not only on
/// the type: its declared type is `Bundled → Bundled → CReal` however the body
/// is wired, so the type test would pass a body that added the two integrals
/// instead of subtracting them.
///
/// The check is syntactic on purpose. The obvious form — `def_eq` against a
/// rebuilt `|∫b₁ + ∫b₂|` and requiring it to FAIL — does not terminate in
/// useful time: refuting definitional equality of two open `CReal` terms drives
/// both to normal form. So the body is read instead, and the query is shown to
/// be capable of a negative answer by running it against a body that genuinely
/// has no `CReal.neg` in it.
#[test]
fn the_bundled_distance_subtracts_and_the_body_says_so() {
    let (kernel, p) = built();

    let body_of = |name, label: &str| match kernel.environment().get(name) {
        Some(Declaration::Definition { value, .. }) => kernel.render_lean(*value),
        _ => panic!("{label} must be a definition"),
    };

    let distance = body_of(p.bundled.bundled_dist, "IntSpace.bundledDist");
    for needle in [
        "CReal.abs",
        "CReal.add",
        "CReal.neg",
        "IntSpace.bundledIntegral",
    ] {
        assert!(
            distance.contains(needle),
            "IntSpace.bundledDist's body must mention {needle}: {distance}"
        );
    }

    // The control that makes `contains` mean something: the same query over
    // `bundledIntegral`, whose body genuinely has no negation in it, comes back
    // NEGATIVE. Without this, "the body mentions CReal.neg" could be true of
    // every body in the layer.
    let integral = body_of(p.bundled.bundled_integral, "IntSpace.bundledIntegral");
    assert!(
        !integral.contains("CReal.neg"),
        "control: IntSpace.bundledIntegral's body has no negation, so the query above can \
         come back negative: {integral}"
    );
}

/// The types render as claimed, and `bundledDist` really is the shape
/// `Metric.dist` demands on the bundled carrier.
#[test]
fn the_bundled_types_render() {
    let (kernel, p) = built();
    for (label, name) in p.bundled.all() {
        let decl = kernel.environment().get(name).expect("declared");
        let ty = match decl {
            Declaration::Theorem { ty, .. } | Declaration::Definition { ty, .. } => *ty,
            _ => panic!("{label} is not a term declaration"),
        };
        println!("{label} : {}", kernel.render_lean(ty));
    }

    let dist = kernel
        .environment()
        .get(p.bundled.bundled_dist)
        .expect("declared");
    let ty = match dist {
        Declaration::Definition { ty, .. } => *ty,
        _ => panic!("IntSpace.bundledDist must be a definition"),
    };
    let rendered = kernel.render_lean(ty);
    for needle in ["IntSpace.Bundled", "CReal"] {
        assert!(
            rendered.contains(needle),
            "IntSpace.bundledDist's type must mention {needle}: {rendered}"
        );
    }
}
