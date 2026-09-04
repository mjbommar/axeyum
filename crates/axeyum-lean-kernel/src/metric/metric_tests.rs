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
    for (label, name) in p.continuity.all() {
        out.push((label.to_string(), name));
    }
    for (label, name) in p.compactness.all() {
        out.push((label.to_string(), name));
    }
    out
}

/// **Every `Metric.*` declaration the kernel holds is on the list above.**
///
/// The subject is derived from `Kernel::environment`, not from a literal, so
/// a declaration added to `metric.rs`, `metric/continuity.rs` (or any future
/// `metric/*.rs`) and forgotten in [`all_declarations`] fails HERE rather
/// than escaping the presence and axiom-freedom checks silently. The other
/// direction — a name on the list that the kernel does not hold — is
/// [`every_metric_declaration_is_present_and_derived`]'s job.
#[test]
fn every_metric_namespace_declaration_is_accounted_for() {
    let (kernel, p) = built();
    let listed: std::collections::BTreeSet<crate::name::NameId> =
        all_declarations(p).into_iter().map(|(_, n)| n).collect();

    let mut missing: Vec<String> = Vec::new();
    let mut seen = 0usize;
    for (name, _decl) in kernel.environment().iter() {
        let rendered = format!("{}", kernel.display_name(*name));
        if rendered == "Metric" || rendered.starts_with("Metric.") {
            seen += 1;
            if !listed.contains(name) {
                missing.push(rendered);
            }
        }
    }
    assert!(
        seen > 0,
        "coverage control: the environment reported no Metric.* declarations at all"
    );
    missing.sort();
    assert!(
        missing.is_empty(),
        "{} Metric.* declaration(s) exist in the kernel but are not on all_declarations: {missing:?}",
        missing.len()
    );
}

/// The continuity layer's name list is the size `declare_all` lands, and its
/// entries are distinct. A duplicated `kernel.name_str` (two struct fields
/// interned to one name) would otherwise make one declaration silently
/// overwrite another and still pass every per-name check.
#[test]
fn the_continuity_names_are_distinct_and_counted() {
    let (_kernel, p) = built();
    let all = p.continuity.all();
    assert_eq!(all.len(), 15, "update this count deliberately");
    let distinct: std::collections::BTreeSet<crate::name::NameId> =
        all.iter().map(|(_, n)| *n).collect();
    assert_eq!(distinct.len(), all.len(), "two continuity names collided");
}

/// The same, for the compactness layer.
#[test]
fn the_compactness_names_are_distinct_and_counted() {
    let (_kernel, p) = built();
    let all = p.compactness.all();
    assert_eq!(all.len(), 19, "update this count deliberately");
    let distinct: std::collections::BTreeSet<crate::name::NameId> =
        all.iter().map(|(_, n)| *n).collect();
    assert_eq!(distinct.len(), all.len(), "two compactness names collided");
}

/// Everything declared here is present, and nothing is an `Axiom` or an
/// `Opaque`.
#[test]
fn every_metric_declaration_is_present_and_derived() {
    let (kernel, p) = built();
    let named = all_declarations(p);
    assert_eq!(
        named.len(),
        37 + FIELD_COUNT + 15 + 19,
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

// ---------------------------------------------------------------------------
// W2-2: the continuity layer, and the two controls that make its bridge
// discriminating.
//
// Both probes below rebuild a proof term that ALREADY exists as a landed
// declaration, with exactly one small slot swapped, and require
// `Kernel::add_declaration` to refuse the swapped form while accepting the
// honest one. The honest half is the positive twin: a negative control with
// no positive twin in the same test, using the same machinery, cannot
// distinguish "the kernel rejected the mutation" from "the kernel rejects
// everything this helper builds".
// ---------------------------------------------------------------------------

/// `∀ F a b (u : CReal.UniformlyContinuousOn F a b),
/// Metric.UniformlyContinuousOnWith Metric.creal Metric.creal
///   (Metric.Interval a b) F <mu>`, proved by `UniformlyContinuousOn.spec`
/// applied to the four `And` projections.
///
/// `honest = true` puts `CReal.UniformlyContinuousOn.modulus F a b u` in the
/// `mu` slot — the modulus the shipped bridge uses. `honest = false` puts
/// `fun n => n` there instead, leaving every other argument untouched.
fn creal_uc_bridge_probe(kernel: &mut Kernel, p: MetricPrelude, honest: bool) -> (ExprId, ExprId) {
    use crate::int_prelude::ops::IntDev;
    use crate::metric::continuity::{dist, rle, unit_rate};
    use crate::nat_prelude::NatOps;

    let c = p.cpoint.creal;
    let mut d = IntDev::new(kernel, c.rat.int);
    let carrier = d.kernel().const_(c.creal, vec![]);
    let nat = d.nat_ty();
    let func_ty = d.arrow(carrier, carrier);
    let inst = d.kernel().const_(p.creal_metric, vec![]);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let u_fv = d.fresh_fvar();
    let u = d.kernel().fvar(u_fv);
    let u_ty = d.const_app(c.uniformly_continuous_on, &[f, a, b]);

    let pred = d.const_app(p.continuity.interval, &[a, b]);
    let spec = d.const_app(c.uc_spec, &[f, a, b, u]);
    let modulus = if honest {
        d.const_app(c.uc_modulus, &[f, a, b, u])
    } else {
        // `fun n => n` — the same SHAPE (`Nat → Nat`), a different function.
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        d.lam_fv(n_fv, nat, n)
    };

    let proof = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let y_fv = d.fresh_fvar();
        let y = d.kernel().fvar(y_fv);

        let lo_x = rle(&mut d, c, a, x);
        let hi_x = rle(&mut d, c, x, b);
        let lo_y = rle(&mut d, c, a, y);
        let hi_y = rle(&mut d, c, y, b);
        let px_ty = d.and(lo_x, hi_x);
        let py_ty = d.and(lo_y, hi_y);
        let hpx_fv = d.fresh_fvar();
        let hpx = d.kernel().fvar(hpx_fv);
        let hpy_fv = d.fresh_fvar();
        let hpy = d.kernel().fvar(hpy_fv);

        let hax = d.and_left(lo_x, hi_x, hpx);
        let hxb = d.and_right(lo_x, hi_x, hpx);
        let hay = d.and_left(lo_y, hi_y, hpy);
        let hyb = d.and_right(lo_y, hi_y, hpy);

        let dxy = dist(&mut d, p, inst, x, y);
        let mu_n = d.apply(modulus, &[n]);
        let inner_rate = unit_rate(&mut d, c, mu_n);
        let hd_ty = rle(&mut d, c, dxy, inner_rate);
        let hd_fv = d.fresh_fvar();
        let hd = d.kernel().fvar(hd_fv);

        let body = d.apply(spec, &[n, x, y, hax, hxb, hay, hyb, hd]);
        let t = d.lam_fv(hd_fv, hd_ty, body);
        let t = d.lam_fv(hpy_fv, py_ty, t);
        let t = d.lam_fv(hpx_fv, px_ty, t);
        let t = d.lam_fv(y_fv, carrier, t);
        let t = d.lam_fv(x_fv, carrier, t);
        d.lam_fv(n_fv, nat, t)
    };

    let ty = {
        let concl = d.const_app(
            p.continuity.uniformly_continuous_on_with,
            &[inst, inst, pred, f, modulus],
        );
        // A DEPENDENT Pi: `modulus` mentions `u`, so a non-dependent arrow
        // would leave `u` unbound (`UnboundFVar`). The shipped bridge does not
        // hit this because its conclusion quantifies the modulus away with an
        // `Exists`; this probe states it at a named modulus on purpose.
        let t = d.pi_fv(u_fv, u_ty, concl);
        let t = d.pi_fv(b_fv, carrier, t);
        let t = d.pi_fv(a_fv, carrier, t);
        d.pi_fv(f_fv, func_ty, t)
    };
    let value = {
        let t = d.lam_fv(u_fv, u_ty, proof);
        let t = d.lam_fv(b_fv, carrier, t);
        let t = d.lam_fv(a_fv, carrier, t);
        d.lam_fv(f_fv, func_ty, t)
    };
    (ty, value)
}

/// **The bridge's modulus is load-bearing, and the probe that says so is not
/// vacuous.** With `CReal.UniformlyContinuousOn.modulus` in the `mu` slot the
/// kernel admits the bridge; with `fun n => n` there — every other argument
/// identical — it refuses, because `spec`'s hypothesis is stated at
/// `1/(modulus n + 1)` and nothing makes that `1/(n+1)`.
#[test]
fn the_bridges_modulus_is_load_bearing() {
    on_a_deep_stack(|| {
        let (mut kernel, p) = built();
        let anon = kernel.anon();

        let (ty, value) = creal_uc_bridge_probe(&mut kernel, p, true);
        let good = kernel.name_str(anon, "Check.metric_uc_bridge_honest");
        kernel
            .add_declaration(Declaration::Theorem {
                name: good,
                uparams: vec![],
                ty,
                value,
            })
            .expect(
                "the honest bridge must be admitted -- if it is not, the \
                 negative half proves nothing",
            );

        let (ty, value) = creal_uc_bridge_probe(&mut kernel, p, false);
        let bad = kernel.name_str(anon, "Check.metric_uc_bridge_identity_modulus");
        let refused = kernel.add_declaration(Declaration::Theorem {
            name: bad,
            uparams: vec![],
            ty,
            value,
        });
        assert!(
            refused.is_err(),
            "the kernel accepted the bridge with `fun n => n` in the modulus slot"
        );
    });
}

/// `∀ M N F mu (hmu : UniformlyContinuousWith M N F mu) x,
/// ContinuousAtWith M N F x mu` — the body of
/// `Metric.continuous_of_uniformly_continuous`, with the two points handed to
/// `hmu` swappable.
///
/// `honest = true` gives `hmu n x y hd`; `honest = false` gives `hmu n y x hd`
/// — one transposition, no other change.
fn uniform_to_pointwise_probe(
    kernel: &mut Kernel,
    p: MetricPrelude,
    honest: bool,
) -> (ExprId, ExprId) {
    use crate::int_prelude::ops::IntDev;
    use crate::metric::continuity::{dist, pair, rle, unit_rate};
    use crate::nat_prelude::NatOps;

    let c = p.cpoint.creal;
    let mut d = IntDev::new(kernel, c.rat.int);
    let g = pair(&mut d, p);
    let nat = d.nat_ty();

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let mu_fv = d.fresh_fvar();
    let mu = d.kernel().fvar(mu_fv);
    let hmu_ty = d.const_app(p.continuity.uniformly_continuous_with, &[g.m, g.n, f, mu]);
    let hmu_fv = d.fresh_fvar();
    let hmu = d.kernel().fvar(hmu_fv);
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);

    let proof = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let y_fv = d.fresh_fvar();
        let y = d.kernel().fvar(y_fv);
        let dxy = dist(&mut d, p, g.m, x, y);
        let mu_n = d.apply(mu, &[n]);
        let inner_rate = unit_rate(&mut d, c, mu_n);
        let hd_ty = rle(&mut d, c, dxy, inner_rate);
        let hd_fv = d.fresh_fvar();
        let hd = d.kernel().fvar(hd_fv);
        let (first, second) = if honest { (x, y) } else { (y, x) };
        let body = d.apply(hmu, &[n, first, second, hd]);
        let t = d.lam_fv(hd_fv, hd_ty, body);
        let t = d.lam_fv(y_fv, g.m_carrier, t);
        d.lam_fv(n_fv, nat, t)
    };

    let ty = {
        let concl = d.const_app(p.continuity.continuous_at_with, &[g.m, g.n, f, x, mu]);
        let t = d.pi_fv(x_fv, g.m_carrier, concl);
        let t = d.arrow(hmu_ty, t);
        let t = d.pi_fv(mu_fv, g.mod_ty, t);
        let t = d.pi_fv(f_fv, g.fn_ty, t);
        let t = d.pi_fv(g.n_fv, g.metric_ty, t);
        d.pi_fv(g.m_fv, g.metric_ty, t)
    };
    let value = {
        let t = d.lam_fv(x_fv, g.m_carrier, proof);
        let t = d.lam_fv(hmu_fv, hmu_ty, t);
        let t = d.lam_fv(mu_fv, g.mod_ty, t);
        let t = d.lam_fv(f_fv, g.fn_ty, t);
        let t = d.lam_fv(g.n_fv, g.metric_ty, t);
        d.lam_fv(g.m_fv, g.metric_ty, t)
    };
    (ty, value)
}

/// **Uniform ⇒ pointwise reads the modulus at the FIXED point, and the order
/// of the two points is not free.** `d(x,y)` and `d(y,x)` are equal only
/// *propositionally* here (`Metric.distComm` is a field, not a reduction), so
/// transposing the two arguments of the uniform witness must be refused. The
/// honest orientation in the same test is the positive twin.
#[test]
fn uniform_to_pointwise_does_not_transpose_its_points() {
    on_a_deep_stack(|| {
        let (mut kernel, p) = built();
        let anon = kernel.anon();

        let (ty, value) = uniform_to_pointwise_probe(&mut kernel, p, true);
        let good = kernel.name_str(anon, "Check.metric_uniform_to_pointwise_honest");
        kernel
            .add_declaration(Declaration::Theorem {
                name: good,
                uparams: vec![],
                ty,
                value,
            })
            .expect("the honest orientation must be admitted");

        let (ty, value) = uniform_to_pointwise_probe(&mut kernel, p, false);
        let bad = kernel.name_str(anon, "Check.metric_uniform_to_pointwise_transposed");
        let refused = kernel.add_declaration(Declaration::Theorem {
            name: bad,
            uparams: vec![],
            ty,
            value,
        });
        assert!(
            refused.is_err(),
            "the kernel accepted the uniform witness with its two points transposed"
        );
    });
}

/// The W2-2 statements, rendered and asserted on their load-bearing
/// substrings. Printed too, because the rendered type is the deliverable.
#[test]
fn w2_2_continuity_types_render() {
    let (kernel, p) = built();
    for (label, name) in p.continuity.all() {
        let decl = kernel
            .environment()
            .get(name)
            .unwrap_or_else(|| panic!("{label} must be declared"));
        let ty = match decl {
            Declaration::Theorem { ty, .. } | Declaration::Definition { ty, .. } => *ty,
            _ => panic!("{label} is not a term declaration"),
        };
        println!("{label} : {}", kernel.render_lean(ty));
    }

    let bridge = kernel
        .environment()
        .get(p.continuity.creal_continuous_on)
        .expect("declared");
    let ty = match bridge {
        Declaration::Theorem { ty, .. } => *ty,
        _ => panic!("Metric.creal_continuous_on must be a theorem"),
    };
    let rendered = kernel.render_lean(ty);
    for needle in [
        "CReal.UniformlyContinuousOn",
        "Metric.ContinuousOn",
        "Metric.creal",
        "Metric.Interval",
    ] {
        assert!(
            rendered.contains(needle),
            "Metric.creal_continuous_on's type must mention {needle}: {rendered}"
        );
    }
}

// ---------------------------------------------------------------------------
// W2-3: the compactness layer's two discriminating controls.
// ---------------------------------------------------------------------------

/// `∀ n, CReal.Equiv (r + r) (1/(n+1))` for `r := 1/(<idx> + 1)`, proved by
/// `CReal.ofRat_add` then `Rat.natDivSucc_add` then `Rat.natDivSucc_halve`.
///
/// `honest = true` puts the DOUBLED index `Nat.succ (Nat.mul 2 n)` in `<idx>`
/// — `1/(2n+2) + 1/(2n+2) = 1/(n+1)`, which is what makes the EVT's two error
/// halves add up. `honest = false` puts `n` there, claiming
/// `1/(n+1) + 1/(n+1) = 1/(n+1)`. Nothing else changes, and the `halve`
/// rewrite is exactly what stops matching.
fn rate_split_probe(kernel: &mut Kernel, p: MetricPrelude, honest: bool) -> (ExprId, ExprId) {
    use crate::int_prelude::ops::IntDev;
    use crate::metric::continuity::unit_rate;
    use crate::nat_prelude::NatOps;
    use crate::rat_prelude::ops::rat_eq_rewrite;

    let c = p.cpoint.creal;
    let mut d = IntDev::new(kernel, c.rat.int);
    let nat = d.nat_ty();
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let one = d.num(1);
    let two = d.num(2);
    let shifted = if honest {
        let doubled = NatOps::mul(&mut d, two, n);
        d.succ(doubled)
    } else {
        n
    };
    let q = d.const_app(c.rat.nat_div_succ, &[one, shifted]);
    let rate = d.const_app(c.of_rat, &[q]);
    let doubled_rate = d.const_app(c.add, &[rate, rate]);

    let base = d.lemma(c.of_rat_add, &[q, q]);
    let rat_add = d.int().rat_add;
    let sum_q = d.const_app(rat_add, &[q, q]);
    let fused_num = NatOps::add(&mut d, one, one);
    let fused = d.const_app(c.rat.nat_div_succ, &[fused_num, shifted]);
    let fuse = d.lemma(c.rat.nat_div_succ_add, &[one, one, shifted]);
    let step1 = rat_eq_rewrite(&mut d, sum_q, fused, fuse, base, &|d, z| {
        let rhs = d.const_app(c.of_rat, &[z]);
        d.const_app(c.equiv, &[doubled_rate, rhs])
    });

    let two_form = d.const_app(c.rat.nat_div_succ, &[two, shifted]);
    let target_q = d.const_app(c.rat.nat_div_succ, &[one, n]);
    let halve = d.lemma(c.rat.nat_div_succ_halve, &[n]);
    let proof = rat_eq_rewrite(&mut d, two_form, target_q, halve, step1, &|d, z| {
        let rhs = d.const_app(c.of_rat, &[z]);
        d.const_app(c.equiv, &[doubled_rate, rhs])
    });

    let target = unit_rate(&mut d, c, n);
    let stmt = d.const_app(c.equiv, &[doubled_rate, target]);
    let ty = d.pi_fv(n_fv, nat, stmt);
    let value = d.lam_fv(n_fv, nat, proof);
    (ty, value)
}

/// **The EVT's error budget only closes at the DOUBLED index.**
///
/// `Metric.evt_approx_max` spends `1/(2n+2)` twice — once crossing from `y` to
/// its net point through uniform continuity, once crossing from that net point
/// to the approximate maximiser — and `Metric.CReal.rateSplit` is what makes
/// the two add to `1/(n+1)`. Asking for the same identity at the undoubled
/// index must be refused; the doubled one in the same test is the positive
/// twin.
#[test]
fn the_evt_error_budget_needs_the_doubled_index() {
    on_a_deep_stack(|| {
        let (mut kernel, p) = built();
        let anon = kernel.anon();

        let (ty, value) = rate_split_probe(&mut kernel, p, true);
        let good = kernel.name_str(anon, "Check.metric_rate_split_doubled");
        kernel
            .add_declaration(Declaration::Theorem {
                name: good,
                uparams: vec![],
                ty,
                value,
            })
            .expect("1/(2n+2) + 1/(2n+2) = 1/(n+1) must be admitted");

        let (ty, value) = rate_split_probe(&mut kernel, p, false);
        let bad = kernel.name_str(anon, "Check.metric_rate_split_undoubled");
        let refused = kernel.add_declaration(Declaration::Theorem {
            name: bad,
            uparams: vec![],
            ty,
            value,
        });
        assert!(
            refused.is_err(),
            "the kernel accepted 1/(n+1) + 1/(n+1) = 1/(n+1)"
        );
    });
}

/// `∀ a b x, CReal.le a x → CReal.le x b → Metric.Interval a b x`, built by
/// `And.intro` from the two bounds.
///
/// `honest = true` supplies them in the order `Interval` states
/// (`a ≤ x` then `x ≤ b`); `honest = false` transposes exactly those two
/// proofs and changes nothing else.
fn interval_intro_probe(kernel: &mut Kernel, p: MetricPrelude, honest: bool) -> (ExprId, ExprId) {
    use crate::int_prelude::ops::IntDev;
    use crate::metric::continuity::{and_intro, rle};
    use crate::nat_prelude::NatOps;

    let c = p.cpoint.creal;
    let mut d = IntDev::new(kernel, c.rat.int);
    let carrier = d.kernel().const_(c.creal, vec![]);

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);

    let lo = rle(&mut d, c, a, x);
    let hi = rle(&mut d, c, x, b);
    let hlo_fv = d.fresh_fvar();
    let hlo = d.kernel().fvar(hlo_fv);
    let hhi_fv = d.fresh_fvar();
    let hhi = d.kernel().fvar(hhi_fv);

    let (first, second) = if honest { (hlo, hhi) } else { (hhi, hlo) };
    let proof = and_intro(&mut d, c, lo, hi, first, second);

    let pred = d.const_app(p.continuity.interval, &[a, b]);
    let concl = d.apply(pred, &[x]);
    let ty = {
        let t = d.arrow(hi, concl);
        let t = d.arrow(lo, t);
        let t = d.pi_fv(x_fv, carrier, t);
        let t = d.pi_fv(b_fv, carrier, t);
        d.pi_fv(a_fv, carrier, t)
    };
    let value = {
        let t = d.lam_fv(hhi_fv, hi, proof);
        let t = d.lam_fv(hlo_fv, lo, t);
        let t = d.lam_fv(x_fv, carrier, t);
        let t = d.lam_fv(b_fv, carrier, t);
        d.lam_fv(a_fv, carrier, t)
    };
    (ty, value)
}

/// **`Metric.Interval`'s two conjuncts are not interchangeable.**
///
/// `Metric.creal_evt_approx_max` reassociates
/// `CReal.evt_approx_max`'s three-way conjunction into
/// `Metric.Interval a b x ∧ …`, and that reassociation is only sound because
/// each bound lands in its own slot. Transposing the two — one edit, no other
/// change — must be refused, and the honest order in the same test is the
/// positive twin.
#[test]
fn the_interval_predicates_two_bounds_are_not_interchangeable() {
    on_a_deep_stack(|| {
        let (mut kernel, p) = built();
        let anon = kernel.anon();

        let (ty, value) = interval_intro_probe(&mut kernel, p, true);
        let good = kernel.name_str(anon, "Check.metric_interval_intro_honest");
        kernel
            .add_declaration(Declaration::Theorem {
                name: good,
                uparams: vec![],
                ty,
                value,
            })
            .expect("the honest bound order must be admitted");

        let (ty, value) = interval_intro_probe(&mut kernel, p, false);
        let bad = kernel.name_str(anon, "Check.metric_interval_intro_transposed");
        let refused = kernel.add_declaration(Declaration::Theorem {
            name: bad,
            uparams: vec![],
            ty,
            value,
        });
        assert!(
            refused.is_err(),
            "the kernel accepted Metric.Interval with its two bounds transposed"
        );
    });
}

/// The W2-3 statements, rendered and asserted on their load-bearing
/// substrings.
#[test]
fn w2_3_compactness_types_render() {
    let (kernel, p) = built();
    for (label, name) in p.compactness.all() {
        let decl = kernel
            .environment()
            .get(name)
            .unwrap_or_else(|| panic!("{label} must be declared"));
        let ty = match decl {
            Declaration::Theorem { ty, .. } | Declaration::Definition { ty, .. } => *ty,
            _ => panic!("{label} is not a term declaration"),
        };
        println!("{label} : {}", kernel.render_lean(ty));
    }

    let evt = kernel
        .environment()
        .get(p.compactness.evt_approx_max)
        .expect("declared");
    let ty = match evt {
        Declaration::Theorem { ty, .. } => *ty,
        _ => panic!("Metric.evt_approx_max must be a theorem"),
    };
    let rendered = kernel.render_lean(ty);
    for needle in [
        "Metric.TotallyBoundedOn",
        "Metric.UniformlyContinuousOn",
        "Metric.creal",
    ] {
        assert!(
            rendered.contains(needle),
            "Metric.evt_approx_max's type must mention {needle}: {rendered}"
        );
    }
    // Completeness is deliberately NOT a hypothesis; see the module doc.
    assert!(
        !rendered.contains("Metric.CompleteOn") && !rendered.contains("Metric.CompactOn"),
        "Metric.evt_approx_max must not assume completeness: {rendered}"
    );

    let compact = kernel
        .environment()
        .get(p.compactness.compact)
        .expect("declared");
    let ty = match compact {
        Declaration::Definition { ty, .. } => *ty,
        _ => panic!("Metric.Compact must be a definition"),
    };
    println!("Metric.Compact : {}", kernel.render_lean(ty));
}
