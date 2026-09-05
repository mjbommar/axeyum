//! Is the L¹ distance the thing this module claims it is?
//!
//! `IntSpace.bundledL1` type-checking says only that a twelve-field record was
//! built. What has to be checked is the *value*: that
//! `Metric.dist (crealIntervalL1 a b hab)` on two bundled functions really is
//! `∫ₐᵇ |F − G|`, and not the integral of some other expression with the same
//! type.
//!
//! Both mutation tables below are over an `Eq.refl` probe: the statement
//! `Eq CReal <the metric's distance> <a candidate right-hand side>` is offered
//! to the trusted gate with `Eq.refl` as its proof, so the gate accepts exactly
//! when the two sides are **definitionally** equal. **Each table opens with its
//! positive twin in the same test**, for the reason
//! `intspace_tests.rs` records: a refusal alone is indistinguishable from a
//! broken harness.
//!
//! The mutations are deliberately small and *mathematically plausible*. Two of
//! them are `CReal.Equiv`-true and definitionally false — `|G − F|` for
//! `|F − G|`, which any correct L¹ development proves equal — so a probe that
//! passed them would be measuring nothing.

use super::{IntSpacePrelude, build_intspace_prelude};
use crate::env::Declaration;
use crate::int_prelude::ops::IntDev;
use crate::nat_prelude::NatOps;
use crate::{Kernel, MetricPrelude, build_metric_prelude, on_a_deep_stack};

fn built() -> (Kernel, IntSpacePrelude, MetricPrelude) {
    use std::sync::OnceLock;
    static TEMPLATE: OnceLock<(Kernel, IntSpacePrelude, MetricPrelude)> = OnceLock::new();
    let (kernel, prelude, metric) = TEMPLATE.get_or_init(|| {
        on_a_deep_stack(|| {
            let mut kernel = Kernel::new();
            let prelude = build_intspace_prelude(&mut kernel).expect("IntSpace prelude must build");
            let metric = build_metric_prelude(&mut kernel).expect("Metric prelude must build");
            (kernel, prelude, metric)
        })
    });
    (kernel.clone(), *prelude, *metric)
}

/// Which right-hand side the generic probe is offered.
#[derive(Clone, Copy, Debug)]
enum GenericRhs {
    /// `S.integral (fdist f g) (hI f g hf hg)` — the claim. MUST be admitted.
    Correct,
    /// `S.integral (fdist g f) …` — the arguments swapped. `CReal.Equiv`-true
    /// (that is `IntSpace.l1Dist_comm`, proved in the same file) and
    /// definitionally FALSE, which makes this the sharpest row in the table.
    SwappedIntegrand,
    /// `S.integral (fdist f f) …` — the diagonal. Refused.
    DiagonalIntegrand,
    /// The correct right-hand side against the bundles swapped on the LEFT.
    /// Refused, for the same reason as `SwappedIntegrand` and from the other
    /// side of the equation.
    SwappedBundles,
}

/// Offer `Eq CReal (l1Dist S fdist hI (bundle f hf) (bundle g hg)) <rhs>` with
/// `Eq.refl`, at an ARBITRARY integration space and an ARBITRARY `fdist`, and
/// report whether the trusted gate took it.
///
/// # Why the discrimination is done here and not at `crealIntervalL1`
///
/// The obvious probe is the concrete one: offer
/// `Metric.dist (crealIntervalL1 a b hab) (bundle F hF) (bundle G hG) =
/// CReal.integral |F − G| …` with the integrand perturbed. The positive
/// direction of that is fine and is already a declaration
/// (`IntSpace.crealIntervalL1_dist`, admitted during the prelude build). The
/// **negatives are pathological**: to refuse `∫F₁ ≡ ∫F₂` the kernel unfolds
/// `CReal.integral`, and it is still working after ten minutes. Measured
/// 2026-09-05, and the reason this table is stated over a bound `S` instead —
/// where nothing can unfold, so every row settles immediately. The finite
/// instance's table below IS concrete and is cheap, because its integral is a
/// `Nat.rec` over `CReal.sumRange` rather than a Riemann sum with a modulus.
fn generic_probe_admits(kernel: &mut Kernel, p: IntSpacePrelude, rhs: GenericRhs) -> bool {
    let c = p.creal;
    let logic = c.rat.int.logic;
    let int = c.rat.int;
    let mut d = IntDev::new(kernel, int);
    let real = d.kernel().const_(c.creal, vec![]);
    let zero = d.kernel().level_zero();
    let one = d.kernel().level_succ(zero);

    let space_ty = d.kernel().const_(p.record.ind, vec![]);
    let s_fv = d.fresh_fvar();
    let s = d.kernel().fvar(s_fv);
    let carrier = {
        let sel = d.kernel().const_(p.record.sel(super::CARRIER), vec![]);
        d.apply(sel, &[s])
    };
    let integrable = {
        let sel = d.kernel().const_(p.record.sel(super::INTEGRABLE), vec![]);
        d.apply(sel, &[s])
    };
    let integral = {
        let sel = d.kernel().const_(p.record.sel(super::INTEGRAL), vec![]);
        d.apply(sel, &[s])
    };

    let fdist_ty = {
        let inner = d.arrow(carrier, carrier);
        d.arrow(carrier, inner)
    };
    let fdist_fv = d.fresh_fvar();
    let fdist = d.kernel().fvar(fdist_fv);

    let hi_ty = {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let y_fv = d.fresh_fvar();
        let y = d.kernel().fvar(y_fv);
        let hx_ty = d.apply(integrable, &[x]);
        let hy_ty = d.apply(integrable, &[y]);
        let combined = d.apply(fdist, &[x, y]);
        let concl = d.apply(integrable, &[combined]);
        let hy_fv = d.fresh_fvar();
        let t = d.pi_fv(hy_fv, hy_ty, concl);
        let hx_fv = d.fresh_fvar();
        let t = d.pi_fv(hx_fv, hx_ty, t);
        let t = d.pi_fv(y_fv, carrier, t);
        d.pi_fv(x_fv, carrier, t)
    };
    let hi_fv = d.fresh_fvar();
    let hi = d.kernel().fvar(hi_fv);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let g_fv = d.fresh_fvar();
    let gg = d.kernel().fvar(g_fv);
    let hf_ty = d.apply(integrable, &[f]);
    let hf_fv = d.fresh_fvar();
    let hf = d.kernel().fvar(hf_fv);
    let hg_ty = d.apply(integrable, &[gg]);
    let hg_fv = d.fresh_fvar();
    let hg = d.kernel().fvar(hg_fv);

    let (left_arg, right_arg, left_wit, right_wit) = match rhs {
        GenericRhs::Correct | GenericRhs::SwappedBundles => (f, gg, hf, hg),
        GenericRhs::SwappedIntegrand => (gg, f, hg, hf),
        GenericRhs::DiagonalIntegrand => (f, f, hf, hf),
    };
    let right = {
        let integrand = d.apply(fdist, &[left_arg, right_arg]);
        let witness = d.apply(hi, &[left_arg, right_arg, left_wit, right_wit]);
        d.apply(integral, &[integrand, witness])
    };

    let left = {
        let bundle = p.bundled.bundle;
        let b1 = d.const_app(bundle, &[s, f, hf]);
        let b2 = d.const_app(bundle, &[s, gg, hg]);
        let (first, second) = if matches!(rhs, GenericRhs::SwappedBundles) {
            (b2, b1)
        } else {
            (b1, b2)
        };
        let name = p.l1.l1_dist;
        d.const_app(name, &[s, fdist, hi, first, second])
    };

    let stmt = {
        let head = d.kernel().const_(logic.eq, vec![one]);
        d.apply(head, &[real, left, right])
    };
    let proof = {
        let head = d.kernel().const_(logic.eq_refl, vec![one]);
        d.apply(head, &[real, right])
    };
    let ty = {
        let t = d.pi_fv(hg_fv, hg_ty, stmt);
        let t = d.pi_fv(hf_fv, hf_ty, t);
        let t = d.pi_fv(g_fv, carrier, t);
        let t = d.pi_fv(f_fv, carrier, t);
        let t = d.pi_fv(hi_fv, hi_ty, t);
        let t = d.pi_fv(fdist_fv, fdist_ty, t);
        d.pi_fv(s_fv, space_ty, t)
    };
    let value = {
        let t = d.lam_fv(hg_fv, hg_ty, proof);
        let t = d.lam_fv(hf_fv, hf_ty, t);
        let t = d.lam_fv(g_fv, carrier, t);
        let t = d.lam_fv(f_fv, carrier, t);
        let t = d.lam_fv(hi_fv, hi_ty, t);
        let t = d.lam_fv(fdist_fv, fdist_ty, t);
        d.lam_fv(s_fv, space_ty, t)
    };

    let anon = d.kernel().anon();
    let name = d.kernel().name_str(anon, format!("Check.l1Dist{rhs:?}"));
    d.kernel()
        .add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty,
            value,
        })
        .is_ok()
}

/// **The seminorm is pinned to its integrand.** `l1Dist (bundle f hf)
/// (bundle g hg)` IS `S.integral (fdist f g)`, and three perturbations of that
/// — the integrand's arguments swapped, the integrand taken on the diagonal,
/// and the two bundles swapped on the left — are each refused, with the
/// unmutated probe admitted in the same test.
#[test]
fn the_l1_seminorm_is_pinned_to_its_integrand() {
    on_a_deep_stack(|| {
        let (mut kernel, p, _) = built();
        assert!(
            generic_probe_admits(&mut kernel, p, GenericRhs::Correct),
            "the unmutated probe must be admitted -- without this the refusals \
             below prove nothing"
        );
        for row in [
            GenericRhs::SwappedIntegrand,
            GenericRhs::DiagonalIntegrand,
            GenericRhs::SwappedBundles,
        ] {
            assert!(
                !generic_probe_admits(&mut kernel, p, row),
                "{row:?} was ACCEPTED -- IntSpace.l1Dist does not pin the \
                 integrand it claims to"
            );
        }
    });
}

/// Which right-hand side the finite probe is offered.
#[derive(Clone, Copy, Debug)]
enum FiniteRhs {
    /// `Σ_{i<m+1} |f i − g i|` — the claim. MUST be admitted.
    Correct,
    /// The same summand over `m` indices rather than `m+1`. Refused.
    ShortBound,
    /// `Σ |f i + g i|` — the negation dropped. Refused.
    NoNegation,
    /// `Σ |g i − f i|` — swapped; `Equiv`-true, definitionally false.
    Swapped,
}

fn finite_probe_admits(
    kernel: &mut Kernel,
    p: IntSpacePrelude,
    m: MetricPrelude,
    rhs: FiniteRhs,
) -> bool {
    let c = p.creal;
    let logic = c.rat.int.logic;
    let int = c.rat.int;
    let mut d = IntDev::new(kernel, int);
    let real = d.kernel().const_(c.creal, vec![]);
    let nat = d.nat_ty();
    let carrier = d.arrow(nat, real);
    let zero = d.kernel().level_zero();
    let one = d.kernel().level_succ(zero);

    let m_fv = d.fresh_fvar();
    let mm = d.kernel().fvar(m_fv);
    let n = d.succ(mm);
    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let g_fv = d.fresh_fvar();
    let gg = d.kernel().fvar(g_fv);

    let (left_fn, right_fn, negate) = match rhs {
        FiniteRhs::Correct | FiniteRhs::ShortBound => (f, gg, true),
        FiniteRhs::NoNegation => (f, gg, false),
        FiniteRhs::Swapped => (gg, f, true),
    };
    let summand = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let li = d.apply(left_fn, &[i]);
        let ri = d.apply(right_fn, &[i]);
        let ri = if negate {
            d.const_app(c.neg, &[ri])
        } else {
            ri
        };
        let sum = d.const_app(c.add, &[li, ri]);
        let body = d.const_app(c.abs, &[sum]);
        d.lam_fv(i_fv, nat, body)
    };
    let bound = if matches!(rhs, FiniteRhs::ShortBound) {
        mm
    } else {
        n
    };
    let right = d.const_app(c.sum_range, &[summand, bound]);

    let space = d.const_app(p.creal_finite, &[mm]);
    let triv_mk = d.kernel().const_(p.triv_mk, vec![]);
    let left = {
        let bundle = p.bundled.bundle;
        let b1 = d.const_app(bundle, &[space, f, triv_mk]);
        let b2 = d.const_app(bundle, &[space, gg, triv_mk]);
        let inst = d.const_app(p.l1.creal_finite_l1, &[mm]);
        let sel = d.kernel().const_(m.record.sel(crate::METRIC_DIST), vec![]);
        let head = d.apply(sel, &[inst]);
        d.apply(head, &[b1, b2])
    };

    let stmt = {
        let head = d.kernel().const_(logic.eq, vec![one]);
        d.apply(head, &[real, left, right])
    };
    let proof = {
        let head = d.kernel().const_(logic.eq_refl, vec![one]);
        d.apply(head, &[real, right])
    };
    let ty = {
        let t = d.pi_fv(g_fv, carrier, stmt);
        let t = d.pi_fv(f_fv, carrier, t);
        d.pi_fv(m_fv, nat, t)
    };
    let value = {
        let t = d.lam_fv(g_fv, carrier, proof);
        let t = d.lam_fv(f_fv, carrier, t);
        d.lam_fv(m_fv, nat, t)
    };

    let anon = d.kernel().anon();
    let name = d.kernel().name_str(anon, format!("Check.finiteL1{rhs:?}"));
    d.kernel()
        .add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty,
            value,
        })
        .is_ok()
}

/// The finite counterpart, including the index bound: `E|X − Y|` over `m+1`
/// points, not `m`.
#[test]
fn the_finite_l1_distance_is_the_sum_of_absolute_differences() {
    on_a_deep_stack(|| {
        let (mut kernel, p, m) = built();
        assert!(
            finite_probe_admits(&mut kernel, p, m, FiniteRhs::Correct),
            "the unmutated probe must be admitted -- without this the refusals \
             below prove nothing"
        );
        for row in [
            FiniteRhs::ShortBound,
            FiniteRhs::NoNegation,
            FiniteRhs::Swapped,
        ] {
            assert!(
                !finite_probe_admits(&mut kernel, p, m, row),
                "{row:?} was ACCEPTED -- the finite L1 distance does not pin \
                 the sum it claims to"
            );
        }
    });
}

/// The headline types, read from the environment rather than from a doc
/// comment.
#[test]
fn l1_headline_types_render() {
    let (kernel, p, _) = built();
    let rendered = |name| {
        let declaration = kernel
            .environment()
            .get(name)
            .expect("declaration must be present");
        kernel.render_lean(declaration.ty()).replace('\n', " ")
    };

    // The metric is a `Metric`, and its carrier is the bundled one.
    let bundled_l1 = rendered(p.l1.bundled_l1);
    assert!(
        bundled_l1.trim_end_matches(')').ends_with("Metric"),
        "IntSpace.bundledL1 must land in `Metric`: {bundled_l1}"
    );
    let carrier = rendered(p.l1.bundled_l1_carrier);
    assert!(
        carrier.contains("Metric.carrier (IntSpace.bundledL1")
            && carrier.contains("(IntSpace.Bundled x0)"),
        "IntSpace.bundledL1_carrier must equate the metric carrier with the \
         bundled carrier: {carrier}"
    );

    // The seminorm is TOTAL on the bundled carrier -- two `Bundled` arguments
    // and no integrability argument between them.
    let dist = rendered(p.l1.l1_dist);
    assert!(
        dist.contains("(x3 : IntSpace.Bundled x0) -> ((x4 : IntSpace.Bundled x0) -> CReal)"),
        "IntSpace.l1Dist must be total on IntSpace.Bundled: {dist}"
    );

    // The interval instance's statement mentions `CReal.integral` and the
    // negation, and does NOT mention `IntSpace.bundledDist` (ADR-1613's
    // explicitly-not-L1 pseudometric).
    let interval = rendered(p.l1.creal_interval_l1_dist);
    for needle in [
        "CReal.integral",
        "CReal.abs",
        "CReal.neg",
        "Metric.dist (IntSpace.crealIntervalL1",
    ] {
        assert!(
            interval.contains(needle),
            "IntSpace.crealIntervalL1_dist must mention {needle}: {interval}"
        );
    }
    assert!(
        !interval.contains("bundledDist"),
        "the L1 distance must not be IntSpace.bundledDist: {interval}"
    );
    // The integrand VERBATIM, in the right argument order. This is the cheap
    // stand-in for the concrete mutation table `generic_probe_admits` explains
    // is pathological: a swapped integrand renders `(x4 x7)` before `(x3 x7)`,
    // and a dropped negation renders no `CReal.neg` at all.
    assert!(
        interval
            .contains("(fun (x7 : CReal) => CReal.abs (CReal.add (x3 x7) (CReal.neg (x4 x7))))"),
        "IntSpace.crealIntervalL1_dist must integrate |F - G| in that argument \
         order: {interval}"
    );

    // The finite instance's statement is a `CReal.sumRange` at `succ m`.
    let finite = rendered(p.l1.creal_finite_l1_dist);
    assert!(
        finite.contains("CReal.sumRange") && finite.contains("succ x0"),
        "IntSpace.crealFiniteL1_dist must be a sumRange at succ m: {finite}"
    );
}
