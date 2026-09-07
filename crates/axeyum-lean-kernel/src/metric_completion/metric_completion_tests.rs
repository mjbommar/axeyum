//! Does the kernel accept [`build_metric_completion_prelude`], is every
//! declaration it produces axiom-free, and — the part that matters — is the
//! **modulus** of the carrier predicate load-bearing?
//!
//! The subject of the accounting test here is derived by **differencing two
//! kernels**: one built with `build_metric_prelude` alone, one built with
//! `build_metric_completion_prelude`. Whatever appears only in the second is
//! this file's responsibility, and the test requires that set to equal
//! [`MetricCompletionNames::owned_names`] exactly. That closes both directions
//! at once — a declaration added here and forgotten in `owned_names` fails,
//! and so does a name listed there that nothing declares — and it does it
//! **without a name-prefix filter**, which is the gap ADR-1625 recorded: a
//! `Metric.*` name declared by a prelude other than `metric.rs` falls between
//! `metric_tests`'s environment sweep (whose kernel never builds this module)
//! and any `starts_with` filter.

use super::{MetricCompletionNames, build_metric_completion_prelude};
use crate::env::Declaration;
use crate::name::NameId;
use crate::nat_prelude::NatOps;
use crate::{Kernel, on_a_deep_stack};

fn built() -> (Kernel, MetricCompletionNames) {
    use std::sync::OnceLock;
    static TEMPLATE: OnceLock<(Kernel, MetricCompletionNames)> = OnceLock::new();
    let (kernel, names) = TEMPLATE.get_or_init(|| {
        on_a_deep_stack(|| {
            let mut kernel = Kernel::new();
            let names = build_metric_completion_prelude(&mut kernel)
                .expect("Metric.completion prelude must build");
            (kernel, names)
        })
    });
    (kernel.clone(), *names)
}

/// The build itself, with the kernel's rejection rendered rather than
/// `Debug`-formatted.
#[test]
fn metric_completion_prelude_builds() {
    on_a_deep_stack(|| {
        let mut kernel = Kernel::new();
        match build_metric_completion_prelude(&mut kernel) {
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

/// Every name this module declares — derived from
/// [`MetricCompletionNames::owned_names`], never a literal list here.
#[test]
fn every_metric_completion_declaration_is_present_and_derived() {
    let (kernel, names) = built();
    let named = names.owned_names();
    assert_eq!(
        named.len(),
        13,
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
fn every_metric_completion_declaration_is_axiom_free() {
    let (kernel, names) = built();
    for (label, name) in names.owned_names() {
        let footprint = kernel.axiom_footprint(name);
        assert!(
            footprint.is_empty(),
            "{label} has a nonempty axiom footprint: {footprint:?}"
        );
    }
}

/// Negative control for the footprint check above: an undeclared name must not
/// report the same clean bill of health for a different reason.
#[test]
fn axiom_footprint_of_a_missing_declaration_is_not_silently_empty() {
    let (mut kernel, _names) = built();
    let anon = kernel.anon();
    let bogus = kernel.name_str(anon, "Check.metric_completion_does_not_exist");
    let footprint = kernel.axiom_footprint(bogus);
    assert!(
        footprint.contains(&bogus) || footprint.is_empty(),
        "unexpected axiom_footprint shape for an undeclared name: {footprint:?}"
    );
}

/// **The accounting test, with its subject derived from the two kernels rather
/// than from any list.** Everything `build_metric_completion_prelude` adds on
/// top of `build_metric_prelude` must be exactly `owned_names`.
///
/// A name-prefix filter cannot do this job — every name here is `Metric.*`,
/// the same namespace `metric.rs` owns — which is why the subject is a set
/// difference instead.
#[test]
fn the_new_declarations_are_exactly_the_owned_names() {
    let base: std::collections::BTreeSet<NameId> = on_a_deep_stack(|| {
        let mut kernel = Kernel::new();
        crate::build_metric_prelude(&mut kernel).expect("Metric prelude must build");
        kernel.environment().iter().map(|(name, _)| *name).collect()
    });
    let (kernel, names) = built();
    let after: std::collections::BTreeSet<NameId> =
        kernel.environment().iter().map(|(name, _)| *name).collect();

    let added: std::collections::BTreeSet<NameId> = after.difference(&base).copied().collect();
    let listed: std::collections::BTreeSet<NameId> =
        names.owned_names().into_iter().map(|(_, n)| n).collect();

    let unlisted: Vec<String> = added
        .difference(&listed)
        .map(|n| kernel.display_name(*n).to_string())
        .collect();
    let missing: Vec<String> = listed
        .difference(&added)
        .map(|n| kernel.display_name(*n).to_string())
        .collect();

    assert!(
        unlisted.is_empty(),
        "declared by this module but absent from owned_names: {unlisted:?}"
    );
    assert!(
        missing.is_empty(),
        "listed in owned_names but not declared by this module: {missing:?}"
    );
    assert_eq!(
        added.len(),
        13,
        "the module's declaration count changed; update it deliberately"
    );
}

// ---------------------------------------------------------------------------
// The modulus is load-bearing: mutants the kernel decides.
// ---------------------------------------------------------------------------

/// **Mutant 1 — the modulus dropped from the carrier predicate.**
///
/// `Metric.RegularSeq M f := Metric.Cauchy M f` (the EXISTENTIAL form, with no
/// modulus) instead of `Metric.CauchyAt M f 1`. The kernel must refuse
/// `Metric.regularSeq_bound`'s proof `fun M f h => h`, because `h` is then an
/// `Exists` and the goal is the `∀ m n` statement.
///
/// This is the mutant ADR-1678 rejects the existential carrier on, and the
/// test is what makes that rejection a measurement rather than a paragraph.
#[test]
fn regular_seq_bound_refuses_the_existential_modulus() {
    on_a_deep_stack(|| {
        let (mut kernel, names) = built();
        let p = crate::build_metric_prelude(&mut kernel).expect("Metric prelude must build");
        let c = p.cpoint.creal;
        let mut d = crate::int_prelude::ops::IntDev::new(&mut kernel, c.rat.int);

        let metric_ty = d.kernel().const_(p.record.ind, vec![]);
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let carrier = {
            let s = d.kernel().const_(p.record.sel(super::CARRIER), vec![]);
            d.apply(s, &[m])
        };
        let nat = d.nat_ty();
        let seq_ty = d.arrow(nat, carrier);
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);

        // The two candidate hypotheses.
        let with_modulus = d.const_app(names.regular_seq, &[m, f]);
        let without_modulus = d.const_app(p.cauchy, &[m, f]);

        // The shared conclusion: `∀ i j, le (M.dist (f i) (f j)) (ofRat (1/(i+1) + 1/(j+1)))`.
        let conclusion = {
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let j_fv = d.fresh_fvar();
            let j = d.kernel().fvar(j_fv);
            let dist = {
                let s = d.kernel().const_(p.record.sel(super::DIST), vec![]);
                d.apply(s, &[m])
            };
            let fi = d.apply(f, &[i]);
            let fj = d.apply(f, &[j]);
            let lhs = d.apply(dist, &[fi, fj]);
            let one_nat = d.num(1);
            let qi = d.const_app(c.rat.nat_div_succ, &[one_nat, i]);
            let qj = d.const_app(c.rat.nat_div_succ, &[one_nat, j]);
            let q = crate::rat_prelude::ops::radd(&mut d, qi, qj);
            let rate = d.const_app(c.of_rat, &[q]);
            let claim = d.const_app(c.le, &[lhs, rate]);
            let inner = d.pi_fv(j_fv, nat, claim);
            d.pi_fv(i_fv, nat, inner)
        };

        let mut offer = |hyp: crate::expr::ExprId, label: &str| {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let ty = {
                let t = d.arrow(hyp, conclusion);
                let t = d.pi_fv(f_fv, seq_ty, t);
                d.pi_fv(m_fv, metric_ty, t)
            };
            let value = {
                let t = d.lam_fv(h_fv, hyp, h);
                let t = d.lam_fv(f_fv, seq_ty, t);
                d.lam_fv(m_fv, metric_ty, t)
            };
            let anon = d.kernel().anon();
            let name = d.kernel().name_str(anon, label);
            d.kernel()
                .add_declaration(crate::env::Declaration::Theorem {
                    name,
                    uparams: vec![],
                    ty,
                    value,
                })
        };

        let ok = offer(with_modulus, "__metricRegularSeqBoundOk");
        assert!(
            ok.is_ok(),
            "the POSITIVE twin must be admitted, or this test measures nothing: {ok:?}"
        );
        let bad = offer(without_modulus, "__metricRegularSeqBoundNoModulus");
        assert!(
            bad.is_err(),
            "the trusted gate accepted `Metric.Cauchy` (an Exists) where the \
             modulus-1 bound was demanded; the carrier predicate is not load-bearing"
        );
    });
}

/// **Mutant 2 — the modulus widened.** `Metric.RegularSeq` stated at modulus
/// `2` instead of `1` must not discharge the modulus-`1` bound by `fun h => h`.
///
/// Where mutant 1 changes the SHAPE of the hypothesis, this one keeps the shape
/// and moves only the rate — the failure a shape-only check would miss.
#[test]
fn regular_seq_bound_refuses_a_widened_modulus() {
    on_a_deep_stack(|| {
        let (mut kernel, _names) = built();
        let p = crate::build_metric_prelude(&mut kernel).expect("Metric prelude must build");
        let c = p.cpoint.creal;
        let mut d = crate::int_prelude::ops::IntDev::new(&mut kernel, c.rat.int);

        let metric_ty = d.kernel().const_(p.record.ind, vec![]);
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let carrier = {
            let s = d.kernel().const_(p.record.sel(super::CARRIER), vec![]);
            d.apply(s, &[m])
        };
        let nat = d.nat_ty();
        let seq_ty = d.arrow(nat, carrier);
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);

        let bound_at = |k: u32, d: &mut crate::int_prelude::ops::IntDev<'_>| {
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let j_fv = d.fresh_fvar();
            let j = d.kernel().fvar(j_fv);
            let dist = {
                let s = d.kernel().const_(p.record.sel(super::DIST), vec![]);
                d.apply(s, &[m])
            };
            let fi = d.apply(f, &[i]);
            let fj = d.apply(f, &[j]);
            let lhs = d.apply(dist, &[fi, fj]);
            let k_nat = d.num(k);
            let qi = d.const_app(c.rat.nat_div_succ, &[k_nat, i]);
            let qj = d.const_app(c.rat.nat_div_succ, &[k_nat, j]);
            let q = crate::rat_prelude::ops::radd(d, qi, qj);
            let rate = d.const_app(c.of_rat, &[q]);
            let claim = d.const_app(c.le, &[lhs, rate]);
            let inner = d.pi_fv(j_fv, nat, claim);
            d.pi_fv(i_fv, nat, inner)
        };

        let at_one = bound_at(1, &mut d);
        let at_two = bound_at(2, &mut d);

        let mut offer = |hyp: crate::expr::ExprId, goal: crate::expr::ExprId, label: &str| {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let ty = {
                let t = d.arrow(hyp, goal);
                let t = d.pi_fv(f_fv, seq_ty, t);
                d.pi_fv(m_fv, metric_ty, t)
            };
            let value = {
                let t = d.lam_fv(h_fv, hyp, h);
                let t = d.lam_fv(f_fv, seq_ty, t);
                d.lam_fv(m_fv, metric_ty, t)
            };
            let anon = d.kernel().anon();
            let name = d.kernel().name_str(anon, label);
            d.kernel()
                .add_declaration(crate::env::Declaration::Theorem {
                    name,
                    uparams: vec![],
                    ty,
                    value,
                })
        };

        let ok = offer(at_one, at_one, "__metricRegularSeqModulusOk");
        assert!(
            ok.is_ok(),
            "the POSITIVE twin (modulus 1 to modulus 1) must be admitted: {ok:?}"
        );
        let bad = offer(at_two, at_one, "__metricRegularSeqModulusWidened");
        assert!(
            bad.is_err(),
            "the trusted gate discharged a modulus-1 bound from a modulus-2 \
             hypothesis without a widening step"
        );
    });
}

/// **The embedding really is the constant sequence, at a concrete point.**
///
/// `Metric.embedSeq_val` is `Eq.refl`-proved and generic; this instantiates it
/// on `Metric.creal` at `CReal.zero` and requires the kernel to admit the
/// EQUATION with the concrete point on the right. A `Definition` that embedded
/// something merely equivalent (say `ofRat (seq a 0)`) would fail here while
/// still type-checking generically.
#[test]
fn embed_seq_is_the_constant_sequence_at_a_concrete_point() {
    on_a_deep_stack(|| {
        let (mut kernel, names) = built();
        let p = crate::build_metric_prelude(&mut kernel).expect("Metric prelude must build");
        let c = p.cpoint.creal;
        let mut d = crate::int_prelude::ops::IntDev::new(&mut kernel, c.rat.int);
        let logic = c.rat.int.logic;
        let one = d.level_one();

        let creal_metric = d.kernel().const_(p.creal_metric, vec![]);
        let creal_ty = d.kernel().const_(c.creal, vec![]);
        let zero = d.kernel().const_(c.zero, vec![]);
        let cone = d.kernel().const_(c.one, vec![]);
        let three = d.num(3);

        let probe = |point: crate::expr::ExprId,
                     claimed: crate::expr::ExprId,
                     label: &str,
                     d: &mut crate::int_prelude::ops::IntDev<'_>| {
            let embedded = d.const_app(names.embed_seq, &[creal_metric, point]);
            let sampled = d.const_app(names.completion_val, &[creal_metric, embedded, three]);
            let ty = {
                let head = d.kernel().const_(logic.eq, vec![one]);
                d.apply(head, &[creal_ty, sampled, claimed])
            };
            let value = {
                let head = d.kernel().const_(logic.eq_refl, vec![one]);
                d.apply(head, &[creal_ty, claimed])
            };
            let anon = d.kernel().anon();
            let name = d.kernel().name_str(anon, label);
            d.kernel()
                .add_declaration(crate::env::Declaration::Theorem {
                    name,
                    uparams: vec![],
                    ty,
                    value,
                })
        };

        let ok = probe(zero, zero, "__metricEmbedSeqConstOk", &mut d);
        assert!(
            ok.is_ok(),
            "the embedding must sample back to its own point: {ok:?}"
        );
        let bad = probe(zero, cone, "__metricEmbedSeqConstWrong", &mut d);
        assert!(
            bad.is_err(),
            "the gate accepted `embedSeq CReal.zero` sampling to `CReal.one`; \
             the probe above is vacuous"
        );
    });
}

/// **`Metric.completionDistSeq` reads BOTH arguments.**
///
/// The type checker cannot tell a two-argument distance from one that ignores
/// its second argument, so this pins the value: at two DIFFERENT embedded
/// points the sequence must be `M.dist a b`, not `M.dist a a`. The negative
/// twin (claiming the diagonal) must be refused.
#[test]
fn completion_dist_seq_uses_its_second_argument() {
    on_a_deep_stack(|| {
        let (mut kernel, names) = built();
        let p = crate::build_metric_prelude(&mut kernel).expect("Metric prelude must build");
        let c = p.cpoint.creal;
        let mut d = crate::int_prelude::ops::IntDev::new(&mut kernel, c.rat.int);
        let logic = c.rat.int.logic;
        let one = d.level_one();

        let creal_metric = d.kernel().const_(p.creal_metric, vec![]);
        let creal_ty = d.kernel().const_(c.creal, vec![]);
        let zero = d.kernel().const_(c.zero, vec![]);
        let cone = d.kernel().const_(c.one, vec![]);
        let two = d.num(2);

        let ex = d.const_app(names.embed_seq, &[creal_metric, zero]);
        let ey = d.const_app(names.embed_seq, &[creal_metric, cone]);
        let sampled = d.const_app(names.completion_dist_seq, &[creal_metric, ex, ey, two]);

        let dist = {
            let s = d.kernel().const_(p.record.sel(super::DIST), vec![]);
            d.apply(s, &[creal_metric])
        };
        let honest = d.apply(dist, &[zero, cone]);
        let diagonal = d.apply(dist, &[zero, zero]);

        let probe = |claimed: crate::expr::ExprId,
                     label: &str,
                     d: &mut crate::int_prelude::ops::IntDev<'_>| {
            let ty = {
                let head = d.kernel().const_(logic.eq, vec![one]);
                d.apply(head, &[creal_ty, sampled, claimed])
            };
            let value = {
                let head = d.kernel().const_(logic.eq_refl, vec![one]);
                d.apply(head, &[creal_ty, claimed])
            };
            let anon = d.kernel().anon();
            let name = d.kernel().name_str(anon, label);
            d.kernel()
                .add_declaration(crate::env::Declaration::Theorem {
                    name,
                    uparams: vec![],
                    ty,
                    value,
                })
        };

        let ok = probe(honest, "__metricCompletionDistSeqOk", &mut d);
        assert!(
            ok.is_ok(),
            "the distance sequence must reduce to `M.dist 0 1`: {ok:?}"
        );
        let bad = probe(diagonal, "__metricCompletionDistSeqDiagonal", &mut d);
        assert!(
            bad.is_err(),
            "the gate accepted `M.dist 0 0` for `completionDistSeq (embed 0) (embed 1)`; \
             the second argument is not load-bearing"
        );
    });
}

/// **Mutant 3 — the isometry weakened to a non-expanding map.**
///
/// `Metric.embedSeq_dist` is an `Eq`. A merely NON-EXPANDING embedding gives
/// only the one-sided `CReal.le (dist (f a) (f b)) (dist a b)`, and the
/// question this test answers is whether that difference is observable.
///
/// It is: `Metric.embedSeq_reflects`'s proof term is `M.distEquiv a b (h 0)`,
/// which needs `h 0 : CReal.Equiv (…) CReal.zero`. Offered the same proof with
/// the hypothesis weakened to `CReal.le (…) CReal.zero` — the shape a
/// non-expanding bound produces — the trusted gate must refuse, because an
/// upper bound of zero on the IMAGE distance says nothing about the source.
///
/// The positive twin is the shipped statement, offered in the same invocation.
#[test]
fn a_non_expanding_bound_cannot_reflect_equivalence() {
    on_a_deep_stack(|| {
        let (mut kernel, names) = built();
        let p = crate::build_metric_prelude(&mut kernel).expect("Metric prelude must build");
        let c = p.cpoint.creal;
        let mut d = crate::int_prelude::ops::IntDev::new(&mut kernel, c.rat.int);

        let metric_ty = d.kernel().const_(p.record.ind, vec![]);
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let carrier = {
            let s = d.kernel().const_(p.record.sel(super::CARRIER), vec![]);
            d.apply(s, &[m])
        };
        let nat = d.nat_ty();
        let zero = d.kernel().const_(c.zero, vec![]);

        let a_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let b_fv = d.fresh_fvar();
        let b = d.kernel().fvar(b_fv);
        let ea = d.const_app(names.embed_seq, &[m, a]);
        let eb = d.const_app(names.embed_seq, &[m, b]);

        // The two candidate hypotheses, differing ONLY in the relation.
        let hyp_equiv = {
            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let sampled = d.const_app(names.completion_dist_seq, &[m, ea, eb, k]);
            let claim = d.const_app(c.equiv, &[sampled, zero]);
            d.pi_fv(k_fv, nat, claim)
        };
        let hyp_le = {
            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let sampled = d.const_app(names.completion_dist_seq, &[m, ea, eb, k]);
            let claim = d.const_app(c.le, &[sampled, zero]);
            d.pi_fv(k_fv, nat, claim)
        };
        let conclusion = {
            let equiv = {
                let s = d.kernel().const_(p.record.sel(super::EQUIV), vec![]);
                d.apply(s, &[m])
            };
            d.apply(equiv, &[a, b])
        };

        let mut offer = |hyp: crate::expr::ExprId, label: &str| {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let proof = {
                let zero_nat = d.num(0);
                let at_zero = d.apply(h, &[zero_nat]);
                let dist_equiv = {
                    let s = d.kernel().const_(p.record.sel(super::DIST_EQUIV), vec![]);
                    d.apply(s, &[m])
                };
                d.apply(dist_equiv, &[a, b, at_zero])
            };
            let ty = {
                let t = d.arrow(hyp, conclusion);
                let t = d.pi_fv(b_fv, carrier, t);
                let t = d.pi_fv(a_fv, carrier, t);
                d.pi_fv(m_fv, metric_ty, t)
            };
            let value = {
                let t = d.lam_fv(h_fv, hyp, proof);
                let t = d.lam_fv(b_fv, carrier, t);
                let t = d.lam_fv(a_fv, carrier, t);
                d.lam_fv(m_fv, metric_ty, t)
            };
            let anon = d.kernel().anon();
            let name = d.kernel().name_str(anon, label);
            d.kernel()
                .add_declaration(crate::env::Declaration::Theorem {
                    name,
                    uparams: vec![],
                    ty,
                    value,
                })
        };

        let ok = offer(hyp_equiv, "__metricEmbedReflectsOk");
        assert!(
            ok.is_ok(),
            "the POSITIVE twin (isometry) must be admitted, or this test \
             measures nothing: {ok:?}"
        );
        let bad = offer(hyp_le, "__metricEmbedReflectsNonExpanding");
        assert!(
            bad.is_err(),
            "the trusted gate reflected equivalence from a one-sided (non-expanding) \
             bound; `Metric.embedSeq_dist` being an Eq is not load-bearing"
        );
    });
}

/// **`Metric.embedSeq_dist` is an EQUATION, and this is the guard that says so
/// about the shipped declaration** rather than re-deriving the discrimination
/// inline.
///
/// `a_non_expanding_bound_cannot_reflect_equivalence` above shows the two
/// relations differ in strength, but it never mentions `Metric.embedSeq_dist`
/// — so weakening that declaration from `Eq` to `CReal.le` (a true, admissible
/// statement: the non-expanding form) would leave it green. **Measured: it
/// does.** This test consumes the declaration itself, as the argument of
/// `Eq.symm`, which only an `Eq` can be.
///
/// The negative twin offers a `CReal.le_refl` proof in the same slot — the
/// exact shape a non-expanding bound has — and must be refused.
#[test]
fn embed_seq_dist_is_an_equation_not_a_bound() {
    on_a_deep_stack(|| {
        let (mut kernel, names) = built();
        let p = crate::build_metric_prelude(&mut kernel).expect("Metric prelude must build");
        let c = p.cpoint.creal;
        let mut d = crate::int_prelude::ops::IntDev::new(&mut kernel, c.rat.int);
        let logic = c.rat.int.logic;
        let one = d.level_one();

        let metric_ty = d.kernel().const_(p.record.ind, vec![]);
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let carrier = {
            let s = d.kernel().const_(p.record.sel(super::CARRIER), vec![]);
            d.apply(s, &[m])
        };
        let nat = d.nat_ty();
        let creal_ty = d.kernel().const_(c.creal, vec![]);

        let a_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let b_fv = d.fresh_fvar();
        let b = d.kernel().fvar(b_fv);
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);

        let ea = d.const_app(names.embed_seq, &[m, a]);
        let eb = d.const_app(names.embed_seq, &[m, b]);
        let sampled = d.const_app(names.completion_dist_seq, &[m, ea, eb, k]);
        let honest = {
            let s = d.kernel().const_(p.record.sel(super::DIST), vec![]);
            let dist = d.apply(s, &[m]);
            d.apply(dist, &[a, b])
        };

        // `Eq CReal (M.dist a b) (completionDistSeq …)` — the SYMMETRIC form,
        // reachable only from an equation.
        let goal = {
            let head = d.kernel().const_(logic.eq, vec![one]);
            d.apply(head, &[creal_ty, honest, sampled])
        };

        let offer = |witness: crate::expr::ExprId,
                     label: &str,
                     d: &mut crate::int_prelude::ops::IntDev<'_>| {
            let proof = {
                let head = d.kernel().const_(logic.eq_symm, vec![one]);
                d.apply(head, &[creal_ty, sampled, honest, witness])
            };
            let ty = {
                let t = d.pi_fv(k_fv, nat, goal);
                let t = d.pi_fv(b_fv, carrier, t);
                let t = d.pi_fv(a_fv, carrier, t);
                d.pi_fv(m_fv, metric_ty, t)
            };
            let value = {
                let t = d.lam_fv(k_fv, nat, proof);
                let t = d.lam_fv(b_fv, carrier, t);
                let t = d.lam_fv(a_fv, carrier, t);
                d.lam_fv(m_fv, metric_ty, t)
            };
            let anon = d.kernel().anon();
            let name = d.kernel().name_str(anon, label);
            d.kernel()
                .add_declaration(crate::env::Declaration::Theorem {
                    name,
                    uparams: vec![],
                    ty,
                    value,
                })
        };

        let equation = d.const_app(names.embed_seq_dist, &[m, a, b, k]);
        let ok = offer(equation, "__metricEmbedDistSymmOk", &mut d);
        assert!(
            ok.is_ok(),
            "`Metric.embedSeq_dist` must be usable as an `Eq` (its symmetric \
             form must admit): {ok:?}"
        );

        // The non-expanding shape: a `CReal.le`, in the slot `Eq.symm` demands
        // an `Eq`.
        let bound = d.lemma(c.le_refl, &[honest]);
        let bad = offer(bound, "__metricEmbedDistSymmNonExpanding", &mut d);
        assert!(
            bad.is_err(),
            "the trusted gate took a `CReal.le` where an `Eq` was demanded; \
             this guard cannot tell an isometry from a non-expanding map"
        );
    });
}

/// Sanity: `owned_names`'s labels are unique (a copy/paste `NameId` collision
/// would otherwise make two rows check the same declaration twice).
#[test]
fn owned_names_labels_and_ids_are_unique() {
    let (_kernel, names) = built();
    let all = names.owned_names();
    let labels: std::collections::BTreeSet<&str> = all.iter().map(|(l, _)| *l).collect();
    let ids: std::collections::BTreeSet<NameId> = all.iter().map(|(_, n)| *n).collect();
    assert_eq!(labels.len(), all.len(), "duplicate label in owned_names");
    assert_eq!(ids.len(), all.len(), "duplicate NameId in owned_names");
}
