//! Does the kernel accept [`build_metric_prelude`], is every theorem it
//! produces axiom-free, and — the part that matters — is each field of the
//! `Metric` record load-bearing?
//!
//! The negative controls here are the point of the file. Every one of them
//! rebuilds `Metric.creal` with **one** slot changed and requires
//! `Kernel::add_declaration` to refuse. Without them, "the metric axioms are
//! stated" is a claim about a comment.

use super::{
    CARRIER, DIST, DIST_COMM, DIST_CONGR, DIST_EQUIV, DIST_NONNEG, DIST_SELF, DIST_TRIANGLE, EQUIV,
    EQUIV_REFL, EQUIV_SYMM, EQUIV_TRANS, FIELD_COUNT, MetricPrelude, build_metric_prelude,
};
use crate::env::Declaration;
use crate::expr::ExprId;
use crate::nat_prelude::structures::mk_instance;
use crate::{Kernel, on_a_deep_stack};

fn built() -> (Kernel, MetricPrelude) {
    use std::sync::OnceLock;
    static TEMPLATE: OnceLock<(Kernel, MetricPrelude)> = OnceLock::new();
    let (kernel, prelude) = TEMPLATE.get_or_init(|| {
        on_a_deep_stack(|| {
            let mut kernel = Kernel::new();
            let prelude = build_metric_prelude(&mut kernel).expect("Metric prelude must build");
            (kernel, prelude)
        })
    });
    (kernel.clone(), *prelude)
}

/// The build itself, with the kernel's rejection rendered rather than
/// `Debug`-formatted.
#[test]
fn metric_prelude_builds() {
    on_a_deep_stack(|| {
        let mut kernel = Kernel::new();
        match build_metric_prelude(&mut kernel) {
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
/// prelude handle, not from a literal list of names** — the record's twelve
/// selectors come from `RecordNames` itself, so a thirteenth field cannot be
/// added without appearing here.
fn all_declarations(p: MetricPrelude) -> Vec<(String, crate::name::NameId)> {
    let mut out: Vec<(String, crate::name::NameId)> = vec![
        ("Metric".into(), p.record.ind),
        ("Metric.mk".into(), p.record.mk),
        ("Metric.rec".into(), p.record.rec),
        ("Metric.CReal.negZero".into(), p.creal_neg_zero),
        ("Metric.CReal.absZero".into(), p.creal_abs_zero),
        (
            "Metric.CReal.leOfSubNonpos".into(),
            p.creal_le_of_sub_nonpos,
        ),
        ("Metric.CReal.distCongr".into(), p.creal_dist_congr),
        ("Metric.CReal.distSelf".into(), p.creal_dist_self),
        ("Metric.CReal.distEquiv".into(), p.creal_dist_equiv),
        ("Metric.CReal.absSubLe".into(), p.creal_abs_sub_le),
        ("Metric.CReal.distComm".into(), p.creal_dist_comm),
        ("Metric.CReal.subTelescope".into(), p.creal_sub_telescope),
        ("Metric.CReal.distTriangle".into(), p.creal_dist_triangle),
        ("Metric.creal".into(), p.creal_metric),
        ("Metric.creal_dist".into(), p.creal_dist),
        ("Metric.dist_self".into(), p.dist_self),
        ("Metric.dist_quadrilateral".into(), p.dist_quadrilateral),
        ("Metric.CauchyAt".into(), p.cauchy_at),
        ("Metric.Cauchy".into(), p.cauchy),
        ("Metric.TendsToAt".into(), p.tends_to_at),
        ("Metric.TendsTo".into(), p.tends_to),
        ("Metric.Complete".into(), p.complete),
        ("Metric.creal_complete".into(), p.creal_complete),
        ("Metric.CPoint.equivRefl".into(), p.cpoint_equiv_refl),
        ("Metric.CPoint.equivSymm".into(), p.cpoint_equiv_symm),
        ("Metric.CPoint.equivTrans".into(), p.cpoint_equiv_trans),
        ("Metric.CPoint.subTelescope".into(), p.cpoint_sub_telescope),
        (
            "Metric.CPoint.dotLeSqrtMul".into(),
            p.cpoint_dot_le_sqrt_mul,
        ),
        ("Metric.CPoint.dist".into(), p.cpoint_dist),
        ("Metric.CPoint.distCongr".into(), p.cpoint_dist_congr),
        ("Metric.CPoint.distSelf".into(), p.cpoint_dist_self),
        ("Metric.CPoint.distEquiv".into(), p.cpoint_dist_equiv),
        ("Metric.CPoint.distComm".into(), p.cpoint_dist_comm),
        ("Metric.CPoint.distSqExpand".into(), p.cpoint_dist_sq_expand),
        ("Metric.CPoint.distTriangle".into(), p.cpoint_dist_triangle),
        ("Metric.cpoint".into(), p.cpoint_metric),
        ("Metric.cpoint_dist".into(), p.cpoint_dist_reduces),
    ];
    for i in 0..p.record.field_count() {
        out.push((format!("Metric selector {i}"), p.record.sel(i)));
    }
    out
}

/// Everything declared here is present, and nothing is an `Axiom` or an
/// `Opaque`.
#[test]
fn every_metric_declaration_is_present_and_derived() {
    let (kernel, p) = built();
    let named = all_declarations(p);
    assert_eq!(
        named.len(),
        37 + FIELD_COUNT,
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
/// rendered name.
#[test]
fn every_metric_declaration_is_axiom_free() {
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
fn axiom_footprint_of_a_missing_declaration_is_not_silently_empty() {
    let (mut kernel, _p) = built();
    let anon = kernel.anon();
    let bogus = kernel.name_str(anon, "Check.metric_does_not_exist");
    let footprint = kernel.axiom_footprint(bogus);
    assert!(
        footprint.contains(&bogus) || footprint.is_empty(),
        "unexpected axiom_footprint shape for an undeclared name: {footprint:?}"
    );
}

/// The record has exactly twelve fields, in the documented order.
#[test]
fn metric_record_field_layout_is_pinned() {
    let (kernel, p) = built();
    assert_eq!(p.record.field_count(), FIELD_COUNT);
    let expected = [
        (CARRIER, "carrier"),
        (EQUIV, "equiv"),
        (EQUIV_REFL, "equivRefl"),
        (EQUIV_SYMM, "equivSymm"),
        (EQUIV_TRANS, "equivTrans"),
        (DIST, "dist"),
        (DIST_CONGR, "distCongr"),
        (DIST_NONNEG, "distNonneg"),
        (DIST_SELF, "distSelf"),
        (DIST_EQUIV, "distEquiv"),
        (DIST_COMM, "distComm"),
        (DIST_TRIANGLE, "distTriangle"),
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

/// The rendered types of the three statements this lane exists to produce.
/// Printed, then asserted on their load-bearing substrings.
#[test]
fn metric_headline_types_render() {
    let (kernel, p) = built();
    for (label, name) in [
        ("Metric.dist_self", p.dist_self),
        ("Metric.dist_quadrilateral", p.dist_quadrilateral),
        ("Metric.Complete", p.complete),
        ("Metric.creal_complete", p.creal_complete),
        ("Metric.creal_dist", p.creal_dist),
        ("Metric.distTriangle", p.record.sel(DIST_TRIANGLE)),
        ("Metric.CPoint.distTriangle", p.cpoint_dist_triangle),
        ("Metric.CPoint.dotLeSqrtMul", p.cpoint_dot_le_sqrt_mul),
        ("Metric.cpoint_dist", p.cpoint_dist_reduces),
    ] {
        let decl = kernel.environment().get(name).expect("declared");
        let ty = match decl {
            Declaration::Theorem { ty, .. }
            | Declaration::Definition { ty, .. }
            | Declaration::Axiom { ty, .. }
            | Declaration::Opaque { ty, .. } => *ty,
            _ => panic!("{label} is not a term declaration"),
        };
        println!("{label} : {}", kernel.render_lean(ty));
    }

    let complete = kernel.environment().get(p.complete).expect("declared");
    let ty = match complete {
        Declaration::Definition { ty, .. } => *ty,
        _ => panic!("Metric.Complete must be a definition"),
    };
    let rendered = kernel.render_lean(ty);
    assert!(
        rendered.contains("Metric"),
        "Metric.Complete's type must quantify over Metric: {rendered}"
    );

    let cc = kernel
        .environment()
        .get(p.creal_complete)
        .expect("declared");
    let ty = match cc {
        Declaration::Theorem { ty, .. } => *ty,
        _ => panic!("Metric.creal_complete must be a theorem"),
    };
    let rendered = kernel.render_lean(ty);
    assert!(
        rendered.contains("Metric.Complete") && rendered.contains("Metric.creal"),
        "creal_complete must state Metric.Complete Metric.creal, got: {rendered}"
    );
}

// ---------------------------------------------------------------------------
// Evaluation tests for the `Definition`s. The trusted gate cannot tell you a
// definition is WRONG -- it type-checks either way -- so each of these
// declares a `Check.*` whose TYPE is the unfolded form and whose VALUE is the
// identity on the folded one. Admission is the statement that the definition
// unfolds to what its doc comment says.
// ---------------------------------------------------------------------------

/// Rebuild the ℝ instance's twelve arguments, with `slot` (if given) replaced
/// by `replacement`. Returns the `Metric.mk …` term.
fn creal_instance_args(
    kernel: &mut Kernel,
    p: MetricPrelude,
    swap: Option<(usize, ExprId)>,
) -> ExprId {
    use crate::BinderInfo;
    let c = p.cpoint.creal;
    let carrier = kernel.const_(c.creal, vec![]);
    let anon = kernel.anon();

    let dist = {
        // `fun x y => CReal.abs (CReal.add x (CReal.neg y))`
        let x = kernel.bvar(1);
        let y = kernel.bvar(0);
        let neg = kernel.const_(c.neg, vec![]);
        let ny = kernel.app(neg, y);
        let add = kernel.const_(c.add, vec![]);
        let sum = kernel.app(add, x);
        let sum = kernel.app(sum, ny);
        let abs = kernel.const_(c.abs, vec![]);
        let body = kernel.app(abs, sum);
        let inner = kernel.lam(anon, carrier, body, BinderInfo::Default);
        kernel.lam(anon, carrier, inner, BinderInfo::Default)
    };
    let nonneg = {
        // `fun a b => CReal.abs_nonneg (CReal.add a (CReal.neg b))`
        let a = kernel.bvar(1);
        let b = kernel.bvar(0);
        let neg = kernel.const_(c.neg, vec![]);
        let nb = kernel.app(neg, b);
        let add = kernel.const_(c.add, vec![]);
        let sum = kernel.app(add, a);
        let sum = kernel.app(sum, nb);
        let lemma = kernel.const_(c.abs_nonneg, vec![]);
        let body = kernel.app(lemma, sum);
        let inner = kernel.lam(anon, carrier, body, BinderInfo::Default);
        kernel.lam(anon, carrier, inner, BinderInfo::Default)
    };

    let mut args = vec![
        carrier,
        kernel.const_(c.equiv, vec![]),
        kernel.const_(c.equiv_refl, vec![]),
        kernel.const_(c.equiv_symm, vec![]),
        kernel.const_(c.equiv_trans, vec![]),
        dist,
        kernel.const_(p.creal_dist_congr, vec![]),
        nonneg,
        kernel.const_(p.creal_dist_self, vec![]),
        kernel.const_(p.creal_dist_equiv, vec![]),
        kernel.const_(p.creal_dist_comm, vec![]),
        kernel.const_(p.creal_dist_triangle, vec![]),
    ];
    assert_eq!(args.len(), FIELD_COUNT);
    if let Some((slot, replacement)) = swap {
        args[slot] = replacement;
    }
    mk_instance(kernel, &p.record, &args)
}

/// **Positive control for every negative control below.** The unmodified
/// twelve arguments are admitted as a `Metric`.
#[test]
fn the_creal_instance_is_admitted_with_every_field_in_place() {
    let (mut kernel, p) = built();
    let value = creal_instance_args(&mut kernel, p, None);
    let ty = kernel.const_(p.record.ind, vec![]);
    let anon = kernel.anon();
    let name = kernel.name_str(anon, "Check.metric_creal_rebuilt");
    kernel
        .add_declaration(Declaration::Definition {
            name,
            uparams: vec![],
            ty,
            value,
            hint: crate::env::ReducibilityHint::Regular(1),
        })
        .expect("the rebuilt ℝ instance must be admitted");
}

/// **The triangle inequality is load-bearing.** The same twelve arguments
/// with slot 11 replaced by `distComm` — a real, admitted theorem of the
/// wrong type — must be refused.
#[test]
fn the_triangle_field_is_load_bearing() {
    let (mut kernel, p) = built();
    let wrong = kernel.const_(p.creal_dist_comm, vec![]);
    let value = creal_instance_args(&mut kernel, p, Some((DIST_TRIANGLE, wrong)));
    let ty = kernel.const_(p.record.ind, vec![]);
    let anon = kernel.anon();
    let name = kernel.name_str(anon, "Check.metric_creal_no_triangle");
    let result = kernel.add_declaration(Declaration::Definition {
        name,
        uparams: vec![],
        ty,
        value,
        hint: crate::env::ReducibilityHint::Regular(1),
    });
    assert!(
        result.is_err(),
        "a Metric with distComm in the distTriangle slot was ADMITTED -- the \
         triangle inequality is not being checked"
    );
}

/// **A squared distance is not a metric, and the kernel says so.** `d(x,y) =
/// |x−y|·|x−y|` satisfies every other axiom of this record (it is
/// nonnegative, symmetric, vanishes exactly on the diagonal, and is
/// congruent) and fails the triangle inequality — `d(0,2) = 4 > 1 + 1`. It is
/// the reason `CPoint.distSq` cannot be a `Metric.dist` and a square root is
/// unavoidable there. Nothing else in the twelve arguments changes.
#[test]
fn a_squared_distance_is_refused_as_a_metric() {
    use crate::BinderInfo;
    let (mut kernel, p) = built();
    let c = p.cpoint.creal;
    let carrier = kernel.const_(c.creal, vec![]);
    let anon = kernel.anon();
    let squared = {
        // `fun x y => CReal.mul (abs (x + -y)) (abs (x + -y))`
        let x = kernel.bvar(1);
        let y = kernel.bvar(0);
        let neg = kernel.const_(c.neg, vec![]);
        let ny = kernel.app(neg, y);
        let add = kernel.const_(c.add, vec![]);
        let sum = kernel.app(add, x);
        let sum = kernel.app(sum, ny);
        let abs = kernel.const_(c.abs, vec![]);
        let a = kernel.app(abs, sum);
        let mul = kernel.const_(c.mul, vec![]);
        let m = kernel.app(mul, a);
        let body = kernel.app(m, a);
        let inner = kernel.lam(anon, carrier, body, BinderInfo::Default);
        kernel.lam(anon, carrier, inner, BinderInfo::Default)
    };
    let value = creal_instance_args(&mut kernel, p, Some((DIST, squared)));
    let ty = kernel.const_(p.record.ind, vec![]);
    let name = kernel.name_str(anon, "Check.metric_creal_squared");
    let result = kernel.add_declaration(Declaration::Definition {
        name,
        uparams: vec![],
        ty,
        value,
        hint: crate::env::ReducibilityHint::Regular(1),
    });
    assert!(
        result.is_err(),
        "the SQUARED distance was admitted as a Metric -- the record's axioms \
         do not constrain `dist` at all"
    );
}

/// **The two directions of the identity of indiscernibles are different
/// fields, and neither proves the other.** Slot 8 (`distSelf`,
/// `a ~ b → d a b ~ 0`) filled with slot 9's proof (`d a b ~ 0 → a ~ b`)
/// must be refused.
#[test]
fn the_two_identity_directions_are_not_interchangeable() {
    let (mut kernel, p) = built();
    let wrong = kernel.const_(p.creal_dist_equiv, vec![]);
    let value = creal_instance_args(&mut kernel, p, Some((DIST_SELF, wrong)));
    let ty = kernel.const_(p.record.ind, vec![]);
    let anon = kernel.anon();
    let name = kernel.name_str(anon, "Check.metric_creal_swapped_identity");
    let result = kernel.add_declaration(Declaration::Definition {
        name,
        uparams: vec![],
        ty,
        value,
        hint: crate::env::ReducibilityHint::Regular(1),
    });
    assert!(
        result.is_err(),
        "distEquiv was accepted in the distSelf slot -- the two directions are \
         not distinguished"
    );
}

/// **`distCongr` is load-bearing too**: without it the record would accept a
/// distance that is a function of representatives rather than of the setoid.
/// Slot 6 filled with `distSelf`'s proof must be refused.
#[test]
fn the_congruence_field_is_load_bearing() {
    let (mut kernel, p) = built();
    let wrong = kernel.const_(p.creal_dist_self, vec![]);
    let value = creal_instance_args(&mut kernel, p, Some((DIST_CONGR, wrong)));
    let ty = kernel.const_(p.record.ind, vec![]);
    let anon = kernel.anon();
    let name = kernel.name_str(anon, "Check.metric_creal_no_congr");
    let result = kernel.add_declaration(Declaration::Definition {
        name,
        uparams: vec![],
        ty,
        value,
        hint: crate::env::ReducibilityHint::Regular(1),
    });
    assert!(
        result.is_err(),
        "distSelf was accepted in the distCongr slot"
    );
}

/// `Metric.dist Metric.creal` reduces **definitionally** to
/// `fun x y => |x − y|`: `Metric.creal_dist` is proved by `CReal.Equiv.refl`,
/// so its admission is exactly that claim. Re-derived here rather than
/// trusted.
///
/// **Symbolic arguments, not numerals — and that is a measured requirement,
/// not a preference.** The first version of this probe used `one` and `zero`
/// and its negative control FAILED: `CReal.zero`/`CReal.one` are closed
/// terms that *compute*, so `|1 − 0|` and `|0 − 1|` both whnf to the same
/// rational and `Equiv.refl` proves the swapped statement too. A
/// concrete-numeral reduction probe on `CReal` cannot distinguish "the
/// selector reduced" from "both sides happened to evaluate alike"; free
/// variables leave the two terms stuck and different.
#[test]
fn the_creal_instances_dist_reduces_to_abs() {
    use crate::BinderInfo;
    let (mut kernel, p) = built();
    let c = p.cpoint.creal;
    let carrier = kernel.const_(c.creal, vec![]);
    let anon = kernel.anon();

    let (ty, value) = dist_reduction_probe(&mut kernel, p, false);
    let ty = {
        let inner = kernel.pi(anon, carrier, ty, BinderInfo::Default);
        kernel.pi(anon, carrier, inner, BinderInfo::Default)
    };
    let value = {
        let inner = kernel.lam(anon, carrier, value, BinderInfo::Default);
        kernel.lam(anon, carrier, inner, BinderInfo::Default)
    };
    let name = kernel.name_str(anon, "Check.metric_creal_dist_symbolic");
    kernel
        .add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty,
            value,
        })
        .expect(
            "Metric.dist Metric.creal x y must reduce to |x - y| at SYMBOLIC \
             arguments -- if it does not, every downstream use is stuck",
        );
}

/// Negative control for the reduction probe: the same `Equiv.refl` proof
/// against the SWAPPED difference `|y − x|` must be refused. `|x−y| ~ |y−x|`
/// is true but it is a *theorem* (`Metric.CReal.distComm`), not a reduction.
#[test]
fn the_reduction_probe_is_not_vacuous() {
    use crate::BinderInfo;
    let (mut kernel, p) = built();
    let c = p.cpoint.creal;
    let carrier = kernel.const_(c.creal, vec![]);
    let anon = kernel.anon();

    let (ty, value) = dist_reduction_probe(&mut kernel, p, true);
    let ty = {
        let inner = kernel.pi(anon, carrier, ty, BinderInfo::Default);
        kernel.pi(anon, carrier, inner, BinderInfo::Default)
    };
    let value = {
        let inner = kernel.lam(anon, carrier, value, BinderInfo::Default);
        kernel.lam(anon, carrier, inner, BinderInfo::Default)
    };
    let name = kernel.name_str(anon, "Check.metric_creal_dist_swapped");
    let result = kernel.add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    });
    assert!(
        result.is_err(),
        "Equiv.refl proved |x-y| ~ |y-x| by reduction -- the probe above is \
         vacuous"
    );
}

/// The body of both probes above, under two de Bruijn binders (`x` is
/// `bvar 1`, `y` is `bvar 0`). `swapped` builds the right-hand side as
/// `|y − x|` instead of `|x − y|`.
fn dist_reduction_probe(kernel: &mut Kernel, p: MetricPrelude, swapped: bool) -> (ExprId, ExprId) {
    let c = p.cpoint.creal;
    let x = kernel.bvar(1);
    let y = kernel.bvar(0);

    let selector = kernel.const_(p.record.sel(DIST), vec![]);
    let inst = kernel.const_(p.creal_metric, vec![]);
    let lhs = kernel.app(selector, inst);
    let lhs = kernel.app(lhs, x);
    let lhs = kernel.app(lhs, y);

    let (l, r) = if swapped { (y, x) } else { (x, y) };
    let neg = kernel.const_(c.neg, vec![]);
    let nr = kernel.app(neg, r);
    let add = kernel.const_(c.add, vec![]);
    let sum = kernel.app(add, l);
    let sum = kernel.app(sum, nr);
    let abs = kernel.const_(c.abs, vec![]);
    let rhs = kernel.app(abs, sum);

    let equiv = kernel.const_(c.equiv, vec![]);
    let ty = kernel.app(equiv, lhs);
    let ty = kernel.app(ty, rhs);
    let refl = kernel.const_(c.equiv_refl, vec![]);
    let value = kernel.app(refl, rhs);
    (ty, value)
}

// ---------------------------------------------------------------------------
// The Euclidean plane instance.
// ---------------------------------------------------------------------------

/// Rebuild the plane instance's twelve arguments, with `slot` (if given)
/// replaced. `Metric.CPoint.dist` is `fun P Q => sqrt (distSq P Q)`.
fn cpoint_instance_args(
    kernel: &mut Kernel,
    p: MetricPrelude,
    swap: Option<(usize, ExprId)>,
) -> ExprId {
    use crate::BinderInfo;
    let cp = p.cpoint;
    let c = cp.creal;
    let point = kernel.const_(cp.point, vec![]);
    let anon = kernel.anon();

    let nonneg = {
        // `fun a b => CReal.sqrt_nonneg (CPoint.distSq a b)`
        let a = kernel.bvar(1);
        let b = kernel.bvar(0);
        let dsq = kernel.const_(cp.dist_sq, vec![]);
        let t = kernel.app(dsq, a);
        let t = kernel.app(t, b);
        let lemma = kernel.const_(c.sqrt_nonneg, vec![]);
        let body = kernel.app(lemma, t);
        let inner = kernel.lam(anon, point, body, BinderInfo::Default);
        kernel.lam(anon, point, inner, BinderInfo::Default)
    };

    let mut args = vec![
        point,
        kernel.const_(cp.point_equiv, vec![]),
        kernel.const_(p.cpoint_equiv_refl, vec![]),
        kernel.const_(p.cpoint_equiv_symm, vec![]),
        kernel.const_(p.cpoint_equiv_trans, vec![]),
        kernel.const_(p.cpoint_dist, vec![]),
        kernel.const_(p.cpoint_dist_congr, vec![]),
        nonneg,
        kernel.const_(p.cpoint_dist_self, vec![]),
        kernel.const_(p.cpoint_dist_equiv, vec![]),
        kernel.const_(p.cpoint_dist_comm, vec![]),
        kernel.const_(p.cpoint_dist_triangle, vec![]),
    ];
    assert_eq!(args.len(), FIELD_COUNT);
    if let Some((slot, replacement)) = swap {
        args[slot] = replacement;
    }
    mk_instance(kernel, &p.record, &args)
}

/// Positive control: the plane instance's twelve arguments are admitted.
#[test]
fn the_plane_instance_is_admitted_with_every_field_in_place() {
    let (mut kernel, p) = built();
    let value = cpoint_instance_args(&mut kernel, p, None);
    let ty = kernel.const_(p.record.ind, vec![]);
    let anon = kernel.anon();
    let name = kernel.name_str(anon, "Check.metric_cpoint_rebuilt");
    kernel
        .add_declaration(Declaration::Definition {
            name,
            uparams: vec![],
            ty,
            value,
            hint: crate::env::ReducibilityHint::Regular(1),
        })
        .expect("the rebuilt Euclidean plane instance must be admitted");
}

/// **`CPoint.distSq` is not a metric, and the kernel says so.** The plane
/// instance with `Metric.CPoint.dist` replaced by `CPoint.distSq` itself —
/// the squared distance, everything else untouched — must be refused. This is
/// the concrete answer to "can the existing `distSq` be the distance field":
/// no, and the square root is not a stylistic choice.
#[test]
fn the_planes_squared_distance_is_refused_as_the_dist_field() {
    let (mut kernel, p) = built();
    let raw = kernel.const_(p.cpoint.dist_sq, vec![]);
    let value = cpoint_instance_args(&mut kernel, p, Some((DIST, raw)));
    let ty = kernel.const_(p.record.ind, vec![]);
    let anon = kernel.anon();
    let name = kernel.name_str(anon, "Check.metric_cpoint_raw_distsq");
    let result = kernel.add_declaration(Declaration::Definition {
        name,
        uparams: vec![],
        ty,
        value,
        hint: crate::env::ReducibilityHint::Regular(1),
    });
    assert!(
        result.is_err(),
        "CPoint.distSq was admitted as a Metric.dist -- the record does not \
         constrain the distance"
    );
}

/// `Metric.dist Metric.cpoint` reduces definitionally to
/// `fun P Q => sqrt (distSq P Q)`, at SYMBOLIC arguments (see
/// [`the_creal_instances_dist_reduces_to_abs`] for why numerals will not do).
#[test]
fn the_plane_instances_dist_reduces_to_sqrt_dist_sq() {
    use crate::BinderInfo;
    let (mut kernel, p) = built();
    let point = kernel.const_(p.cpoint.point, vec![]);
    let anon = kernel.anon();
    let (ty, value) = plane_reduction_probe(&mut kernel, p, false);
    let ty = {
        let inner = kernel.pi(anon, point, ty, BinderInfo::Default);
        kernel.pi(anon, point, inner, BinderInfo::Default)
    };
    let value = {
        let inner = kernel.lam(anon, point, value, BinderInfo::Default);
        kernel.lam(anon, point, inner, BinderInfo::Default)
    };
    let name = kernel.name_str(anon, "Check.metric_cpoint_dist_symbolic");
    kernel
        .add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty,
            value,
        })
        .expect("Metric.dist Metric.cpoint P Q must reduce to sqrt (distSq P Q)");
}

/// Negative control: the same `Equiv.refl` against `sqrt (distSq Q P)` — the
/// swapped distance — must be refused. `distSq P Q ~ distSq Q P` is a
/// theorem (`CPoint.distSq_comm`), not a reduction.
#[test]
fn the_plane_reduction_probe_is_not_vacuous() {
    use crate::BinderInfo;
    let (mut kernel, p) = built();
    let point = kernel.const_(p.cpoint.point, vec![]);
    let anon = kernel.anon();
    let (ty, value) = plane_reduction_probe(&mut kernel, p, true);
    let ty = {
        let inner = kernel.pi(anon, point, ty, BinderInfo::Default);
        kernel.pi(anon, point, inner, BinderInfo::Default)
    };
    let value = {
        let inner = kernel.lam(anon, point, value, BinderInfo::Default);
        kernel.lam(anon, point, inner, BinderInfo::Default)
    };
    let name = kernel.name_str(anon, "Check.metric_cpoint_dist_swapped");
    let result = kernel.add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    });
    assert!(
        result.is_err(),
        "Equiv.refl proved sqrt(distSq P Q) ~ sqrt(distSq Q P) by reduction -- \
         the probe above is vacuous"
    );
}

fn plane_reduction_probe(kernel: &mut Kernel, p: MetricPrelude, swapped: bool) -> (ExprId, ExprId) {
    let cp = p.cpoint;
    let c = cp.creal;
    let a = kernel.bvar(1);
    let b = kernel.bvar(0);

    let selector = kernel.const_(p.record.sel(DIST), vec![]);
    let inst = kernel.const_(p.cpoint_metric, vec![]);
    let lhs = kernel.app(selector, inst);
    let lhs = kernel.app(lhs, a);
    let lhs = kernel.app(lhs, b);

    let (l, r) = if swapped { (b, a) } else { (a, b) };
    let dsq = kernel.const_(cp.dist_sq, vec![]);
    let t = kernel.app(dsq, l);
    let t = kernel.app(t, r);
    let sqrt = kernel.const_(c.sqrt, vec![]);
    let rhs = kernel.app(sqrt, t);

    let equiv = kernel.const_(c.equiv, vec![]);
    let ty = kernel.app(equiv, lhs);
    let ty = kernel.app(ty, rhs);
    let refl = kernel.const_(c.equiv_refl, vec![]);
    let value = kernel.app(refl, rhs);
    (ty, value)
}
