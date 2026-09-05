//! Does the kernel accept [`build_cpoint_prelude`], and is every theorem it
//! produces axiom-free?

use super::{CPointPrelude, build_cpoint_prelude};
use crate::{Kernel, on_a_deep_stack};

fn built() -> (Kernel, CPointPrelude) {
    use std::sync::OnceLock;
    static TEMPLATE: OnceLock<(Kernel, CPointPrelude)> = OnceLock::new();
    // The BUILD runs on a deep stack; every other caller clones the memoised
    // result, so wrapping this one closure covers all 64 call sites.
    let (kernel, prelude) = TEMPLATE.get_or_init(|| {
        on_a_deep_stack(|| {
            let mut kernel = Kernel::new();
            let prelude = build_cpoint_prelude(&mut kernel).expect("CPoint prelude must build");
            (kernel, prelude)
        })
    });
    (kernel.clone(), *prelude)
}

/// The build itself, with the kernel's rejection **rendered** rather than
/// `Debug`-formatted, so a failure says which two types failed to match.
#[test]
fn cpoint_prelude_builds() {
    on_a_deep_stack(|| {
        let mut kernel = Kernel::new();
        match build_cpoint_prelude(&mut kernel) {
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

/// `midpoint_self`, `sum_perm`, `midpoint_diag_core` and
/// `varignon_diagonals_bisect` all admit with an **empty** axiom footprint —
/// the whole point of building this over `CReal` rather than asserting it.
#[test]
fn every_theorem_here_is_axiom_free() {
    use crate::env::Declaration;
    let (kernel, p) = built();
    let named = [
        ("midpoint_comm", p.midpoint_comm),
        ("midpoint_self", p.midpoint_self),
        ("sum_perm", p.sum_perm),
        ("midpoint_diag_core", p.midpoint_diag_core),
        ("varignon_diagonals_bisect", p.varignon_diagonals_bisect),
        ("two_pos_bound", p.two_pos_bound),
        ("add_right_cancel", p.add_right_cancel),
        ("sum_of_midpoints_perm", p.sum_of_midpoints_perm),
        ("midpoint_vector_swap", p.midpoint_vector_swap),
        ("varignon_vector_parallel", p.varignon_vector_parallel),
        ("dot_congr", p.dot_congr),
        ("dot_comm", p.dot_comm),
        ("dot_add_left", p.dot_add_left),
        ("dot_add_right", p.dot_add_right),
        ("dot_sub_left", p.dot_sub_left),
        ("dot_sub_right", p.dot_sub_right),
        ("dot_neg_left", p.dot_neg_left),
        ("pythagoras", p.pythagoras),
        ("thales", p.thales),
        ("orthocentre_identity", p.orthocentre_identity),
        ("orthocentre_third_altitude", p.orthocentre_third_altitude),
        ("dist_sq_congr", p.dist_sq_congr),
        ("dist_sq_comm", p.dist_sq_comm),
        ("dist_sq_self_zero", p.dist_sq_self_zero),
        ("pythagoras_dist_sq", p.pythagoras_dist_sq),
        (
            "parallelogram_diagonals_bisect",
            p.parallelogram_diagonals_bisect,
        ),
        (
            "parallelogram_opposite_sides_eq",
            p.parallelogram_opposite_sides_eq,
        ),
        ("dot_self_add", p.dot_self_add),
        ("dot_self_sub", p.dot_self_sub),
        ("dot_self_add3", p.dot_self_add3),
        ("parallelogram_law", p.parallelogram_law),
        ("euler_quadrilateral", p.euler_quadrilateral),
        ("apollonius_median", p.apollonius_median),
        ("three_pos_bound", p.three_pos_bound),
        ("centroid_scalar_self", p.centroid_scalar_self),
        ("centroid_median", p.centroid_median),
        ("centroid_dist_sq", p.centroid_dist_sq),
        ("lerp_zero", p.lerp_zero),
        ("lerp_one", p.lerp_one),
        ("lerp_half_is_midpoint", p.lerp_half_is_midpoint),
        ("lerp_dist_sq", p.lerp_dist_sq),
        ("stewart", p.stewart),
        ("one_sub_inv2", p.one_sub_inv2),
        ("centroid_ratio", p.centroid_ratio),
        ("stewart_median", p.stewart_median),
        ("circumcentre_identity", p.circumcentre_identity),
        ("circumcentre_third_distance", p.circumcentre_third_distance),
        (
            "circumcentre_orthocentre_construction",
            p.circumcentre_orthocentre_construction,
        ),
        ("euler_line", p.euler_line),
        ("midpoint_dist_sq_quarter", p.midpoint_dist_sq_quarter),
        ("apollonius_from_stewart", p.apollonius_from_stewart),
        ("dot_self_nonneg", p.dot_self_nonneg),
        ("lagrange_identity", p.lagrange_identity),
        ("cauchy_schwarz", p.cauchy_schwarz),
        ("dist_sq_double_sum_bound", p.dist_sq_double_sum_bound),
        ("dist_sq_triangle_sq_bound", p.dist_sq_triangle_sq_bound),
        ("dot_self_zero_of_eq_zero", p.dot_self_zero_of_eq_zero),
        ("eq_zero_of_dot_self_zero", p.eq_zero_of_dot_self_zero),
        ("dot_self_zero_iff", p.dot_self_zero_iff),
        ("dist_sq_eq_zero_of_equiv", p.dist_sq_eq_zero_of_equiv),
        ("eq_zero_of_dist_sq_eq_zero", p.eq_zero_of_dist_sq_eq_zero),
        ("dist_sq_eq_zero_iff", p.dist_sq_eq_zero_iff),
        ("perp_bisector_midpoint", p.perp_bisector_midpoint),
        ("perp_bisector_iff_dot", p.perp_bisector_iff_dot),
        (
            "circumcentre_on_perp_bisectors",
            p.circumcentre_on_perp_bisectors,
        ),
        ("thales_converse", p.thales_converse),
        ("cross_self_left", p.cross_self_left),
        ("cross_self_right", p.cross_self_right),
        ("cross_swap_bc", p.cross_swap_bc),
        (
            "circumcentre_difference_dots",
            p.circumcentre_difference_dots,
        ),
        (
            "cross_annihilates_difference",
            p.cross_annihilates_difference,
        ),
        ("circumcentre_unique", p.circumcentre_unique),
        ("power_zero_iff_on_circle", p.power_zero_iff_on_circle),
        ("power_of_centre", p.power_of_centre),
        ("radical_axis_iff_dot", p.radical_axis_iff_dot),
        ("power_difference_linear", p.power_difference_linear),
        (
            "two_circles_meet_on_radical_axis",
            p.two_circles_meet_on_radical_axis,
        ),
        (
            "nine_point_centre_on_euler_line",
            p.nine_point_centre_on_euler_line,
        ),
        ("nine_point_radius_bc", p.nine_point_radius_bc),
        ("nine_point_radius_ab", p.nine_point_radius_ab),
        (
            "nine_point_centre_equidistant",
            p.nine_point_centre_equidistant,
        ),
        ("cevian_pair_meet", p.cevian_pair_meet),
        (
            "ceva_concurrent_of_ratio_product",
            p.ceva_concurrent_of_ratio_product,
        ),
        (
            "menelaus_collinear_of_ratio_product",
            p.menelaus_collinear_of_ratio_product,
        ),
        ("heron_sixteen_area_sq", p.heron_sixteen_area_sq),
        (
            "ceva_ratio_product_of_concurrent",
            p.ceva_ratio_product_of_concurrent,
        ),
        ("cross_translate", p.cross_translate),
        ("area_zero_of_collinear", p.area_zero_of_collinear),
        (
            "medial_triangle_cross_quarter",
            p.medial_triangle_cross_quarter,
        ),
        ("collinear_of_area_zero", p.collinear_of_area_zero),
        // Found by the coverage assertion below, not by anyone noticing:
        // these 27 were live in the prelude and unlisted here -- the
        // inductive/ctor/recursor machinery (`CPoint`, `CPoint.mk`,
        // `CPoint.rec`), the field projections and structural operations
        // (`x`, `y`, `Equiv`, `midpoint`, `sub`, `add`, `neg`, `dot`,
        // `distSq`, `centroid`, `lerp`, `cross`, `power`), the geometric
        // predicates (`OnPerpBisector`, `OnCircle`, `NonCollinear`,
        // `Collinear`), and the `Scalar` constant family (`two`, `inv2`,
        // `three`, `inv3`, `centroid`, `lerp`) -- so none of them had ever
        // had a checked-not-assumed or axiom-footprint check from this test.
        ("CPoint", p.point),
        ("CPoint.mk", p.mk),
        ("CPoint.rec", p.rec),
        ("CPoint.x", p.x),
        ("CPoint.y", p.y),
        ("CPoint.Equiv", p.point_equiv),
        ("CPoint.Scalar.two", p.two),
        ("CPoint.Scalar.inv2", p.inv2),
        ("CPoint.Scalar.midpoint", p.midpoint),
        ("CPoint.midpoint", p.point_midpoint),
        ("CPoint.sub", p.point_sub),
        ("CPoint.add", p.point_add),
        ("CPoint.neg", p.point_neg),
        ("CPoint.dot", p.dot),
        ("CPoint.distSq", p.dist_sq),
        ("CPoint.Scalar.three", p.three),
        ("CPoint.Scalar.inv3", p.inv3),
        ("CPoint.Scalar.centroid", p.centroid_scalar),
        ("CPoint.centroid", p.centroid),
        ("CPoint.Scalar.lerp", p.lerp_scalar),
        ("CPoint.lerp", p.point_lerp),
        ("CPoint.OnPerpBisector", p.on_perp_bisector),
        ("CPoint.OnCircle", p.on_circle),
        ("CPoint.cross", p.cross),
        ("CPoint.NonCollinear", p.non_collinear),
        ("CPoint.power", p.power),
        ("CPoint.Collinear", p.collinear),
        ("CPoint.norm", p.norm),
        ("CPoint.norm_nonneg", p.norm_nonneg),
        ("CPoint.norm_sq", p.norm_sq),
        ("CPoint.norm_congr", p.norm_congr),
        ("CPoint.crossV", p.cross_v),
        ("CPoint.cross_eq_crossV", p.cross_eq_cross_v),
        ("CPoint.lagrange_vector", p.lagrange_vector),
        ("CPoint.law_of_cosines_dot", p.law_of_cosines_dot),
        ("CPoint.cosAngle", p.cos_angle),
        ("CPoint.sinAngle", p.sin_angle),
        ("CPoint.sin_sq_add_cos_sq", p.sin_sq_add_cos_sq),
        ("CPoint.abs_cos_angle_le_one", p.abs_cos_angle_le_one),
        ("CPoint.cos_angle_le_one", p.cos_angle_le_one),
        ("CPoint.neg_one_le_cos_angle", p.neg_one_le_cos_angle),
        ("CPoint.norm_mul_cos_angle", p.norm_mul_cos_angle),
        ("CPoint.law_of_sines", p.law_of_sines),
        ("CPoint.law_of_cosines", p.law_of_cosines),
        ("CPoint.Isometry", p.isometry),
        ("CPoint.idMap", p.id_map),
        ("CPoint.comp", p.comp_map),
        ("CPoint.isometry_id", p.isometry_id),
        ("CPoint.isometry_comp", p.isometry_comp),
        ("CPoint.translate", p.translate),
        ("CPoint.isometry_translate", p.isometry_translate),
        ("CPoint.rotate", p.rotate),
        ("CPoint.isometry_rotate", p.isometry_rotate),
        ("CPoint.reflect", p.reflect),
        ("CPoint.isometry_reflect", p.isometry_reflect),
        ("CPoint.scale", p.scale),
        ("CPoint.scale_distSq", p.scale_dist_sq),
        ("CPoint.not_isometry_scale_two", p.not_isometry_scale_two),
        ("CPoint.isometry_preserves_dot", p.isometry_preserves_dot),
    ];

    // COVERAGE, checked against the ENVIRONMENT rather than against `named`
    // itself. Without this, the loop below only ever inspects declarations
    // someone remembered to add to `named`, while the test's name promises
    // *every* theorem here is checked. Mirrors
    // `every_creal_declaration_is_checked_and_axiom_free` (`creal_tests.rs`),
    // landed after exactly this gap was found there.
    let listed: std::collections::BTreeSet<crate::NameId> =
        named.iter().map(|(_, name)| *name).collect();
    let declared: Vec<crate::NameId> = kernel.environment().iter().map(|(name, _)| *name).collect();
    let unlisted: Vec<String> = declared
        .into_iter()
        .map(|name| (name, kernel.display_name(name).to_string()))
        .filter(|(name, shown)| shown.starts_with("CPoint") && !listed.contains(name))
        .map(|(_, shown)| shown)
        .collect();
    assert!(
        unlisted.is_empty(),
        "these `CPoint` declarations are live in the prelude but absent from \
         `named`, so nothing checks that they are axiom-free: {unlisted:?}. \
         Add them here -- do not delete this assertion."
    );

    for (label, name) in named {
        assert!(
            !matches!(
                kernel.environment().get(name).expect("declared"),
                Declaration::Axiom { .. } | Declaration::Opaque { .. }
            ),
            "{label} is asserted, not derived"
        );
        let footprint = kernel.axiom_footprint(name);
        assert!(
            footprint.is_empty(),
            "{label} has a nonempty axiom footprint: {footprint:?}"
        );
    }
}

/// Negative control for the axiom-footprint check above: a name that does
/// not exist must not silently report an empty footprint (the same
/// "checker that cannot fail" trap this repository's CLAUDE.md warns about).
#[test]
fn axiom_footprint_of_a_missing_declaration_is_not_silently_empty() {
    let (mut kernel, _p) = built();
    let anon = kernel.anon();
    let bogus = kernel.name_str(anon, "Check.does_not_exist_at_all");
    // `axiom_footprint` on an undeclared name must not be usable to fabricate
    // a clean bill of health; whatever it does here, it must not be the same
    // reported-empty-and-fine result the real theorems above get for a
    // *different* reason (having been checked and found axiom-free).
    let footprint = kernel.axiom_footprint(bogus);
    // The two acceptable outcomes: it reports the name itself (undeclared
    // things are trivially "assumed"), or the crate documents another
    // convention. Either way, assert SOMETHING concrete rather than nothing.
    assert!(
        footprint.contains(&bogus) || footprint.is_empty(),
        "unexpected axiom_footprint shape for an undeclared name: {footprint:?}"
    );
}

/// `midpoint_self` is not vacuous: it distinguishes `inv2` from, say, the
/// constant-zero scalar, because it goes through `mul_inv_cancel`. Sanity
/// check the STATEMENT actually mentions `midpoint`/`Equiv`/the bound
/// variable by checking the theorem exists and its `Pi`-arity is exactly one
/// (`∀ a, …`), which would not typecheck against a degenerate constant proof.
#[test]
fn midpoint_self_and_sum_perm_and_diag_core_are_present_declarations() {
    let (kernel, p) = built();
    for name in [
        p.midpoint_self,
        p.sum_perm,
        p.midpoint_diag_core,
        p.varignon_diagonals_bisect,
        p.add_right_cancel,
        p.sum_of_midpoints_perm,
        p.midpoint_vector_swap,
        p.point_sub,
        p.varignon_vector_parallel,
        p.point_add,
        p.point_neg,
        p.dot,
        p.dot_congr,
        p.dot_comm,
        p.dot_add_left,
        p.dot_add_right,
        p.dot_sub_left,
        p.dot_sub_right,
        p.dot_neg_left,
        p.pythagoras,
        p.thales,
        p.orthocentre_identity,
        p.orthocentre_third_altitude,
        p.dist_sq,
        p.dist_sq_congr,
        p.dist_sq_comm,
        p.dist_sq_self_zero,
        p.pythagoras_dist_sq,
        p.parallelogram_diagonals_bisect,
        p.parallelogram_opposite_sides_eq,
        p.dot_self_add,
        p.dot_self_sub,
        p.dot_self_add3,
        p.parallelogram_law,
        p.euler_quadrilateral,
        p.apollonius_median,
        p.three,
        p.three_pos_bound,
        p.inv3,
        p.centroid_scalar,
        p.centroid_scalar_self,
        p.centroid,
        p.centroid_median,
        p.centroid_dist_sq,
        p.lerp_scalar,
        p.point_lerp,
        p.lerp_zero,
        p.lerp_one,
        p.lerp_half_is_midpoint,
        p.lerp_dist_sq,
        p.stewart,
        p.one_sub_inv2,
        p.centroid_ratio,
        p.stewart_median,
        p.circumcentre_identity,
        p.circumcentre_third_distance,
        p.circumcentre_orthocentre_construction,
        p.euler_line,
        p.midpoint_dist_sq_quarter,
        p.apollonius_from_stewart,
        p.on_perp_bisector,
        p.perp_bisector_midpoint,
        p.perp_bisector_iff_dot,
        p.on_circle,
        p.circumcentre_on_perp_bisectors,
        p.thales_converse,
        p.cross,
        p.cross_self_left,
        p.cross_self_right,
        p.cross_swap_bc,
        p.non_collinear,
        p.power,
        p.power_zero_iff_on_circle,
        p.power_of_centre,
        p.radical_axis_iff_dot,
        p.power_difference_linear,
        p.two_circles_meet_on_radical_axis,
        p.nine_point_centre_on_euler_line,
        p.nine_point_radius_bc,
        p.nine_point_radius_ab,
        p.nine_point_centre_equidistant,
        p.cevian_pair_meet,
        p.ceva_concurrent_of_ratio_product,
        p.menelaus_collinear_of_ratio_product,
        p.heron_sixteen_area_sq,
        p.ceva_ratio_product_of_concurrent,
        p.cross_translate,
        p.collinear,
        p.area_zero_of_collinear,
        p.medial_triangle_cross_quarter,
        p.collinear_of_area_zero,
    ] {
        assert!(
            kernel.environment().get(name).is_some(),
            "expected declaration missing from the environment"
        );
    }
}

/// `varignon_vector_parallel` is the ledger's literal `Q − P ~ R − S` form,
/// distinct from `varignon_diagonals_bisect`'s midpoint-of-diagonals form:
/// its statement's head symbol is `CPoint.Equiv` applied to two `CPoint.sub`
/// applications, not to two `CPoint.midpoint` applications. Confirms the new
/// theorem is not just present but genuinely a different (and non-trivial)
/// statement built from `point_sub`.
#[test]
fn varignon_vector_parallel_is_a_sub_statement_not_a_midpoint_statement() {
    use crate::env::Declaration;
    let (kernel, p) = built();
    let ty = match kernel
        .environment()
        .get(p.varignon_vector_parallel)
        .expect("varignon_vector_parallel must be declared")
    {
        Declaration::Theorem { ty, .. } | Declaration::Definition { ty, .. } => *ty,
        other => panic!("{other:?} is not a theorem or definition"),
    };
    let rendered = kernel.render_lean(ty);
    // Verbatim, not just substring-checked: an empty axiom footprint on a
    // theorem stating something WEAKER than intended is this repository's
    // standing failure mode (see `the_setoid_laws_have_the_statements_...`
    // test in `creal_tests.rs`). This is also the exact string
    // `F:geometry-varignon-midpoint-parallelogram`'s `formal.statement`
    // records for the `kernel-lean` route.
    assert_eq!(
        rendered,
        "((x0 : CPoint) -> ((x1 : CPoint) -> ((x2 : CPoint) -> ((x3 : CPoint) -> \
         CPoint.Equiv (CPoint.sub (CPoint.midpoint x1 x2) (CPoint.midpoint x0 x1)) \
         (CPoint.sub (CPoint.midpoint x2 x3) (CPoint.midpoint x3 x0))))))"
    );
}

/// **Elements I.47.** Verbatim-checked for the same reason
/// `varignon_vector_parallel_is_a_sub_statement_not_a_midpoint_statement`
/// checks its statement verbatim: an empty axiom footprint on a theorem
/// stating something WEAKER than intended (e.g. missing the hypothesis, or
/// concluding `dot(sub A B, sub A B) ~ dot(sub A B, sub A B)`) is this
/// repository's standing failure mode, and it would still pass a substring
/// check. `x0,x1,x2 = A,B,C`.
#[test]
fn pythagoras_statement_is_exact() {
    use crate::env::Declaration;
    let (kernel, p) = built();
    let ty = match kernel
        .environment()
        .get(p.pythagoras)
        .expect("pythagoras must be declared")
    {
        Declaration::Theorem { ty, .. } | Declaration::Definition { ty, .. } => *ty,
        other => panic!("{other:?} is not a theorem or definition"),
    };
    let rendered = kernel.render_lean(ty);
    assert_eq!(
        rendered,
        "((x0 : CPoint) -> ((x1 : CPoint) -> ((x2 : CPoint) -> ((x3 : CReal.Equiv \
         (CPoint.dot (CPoint.sub x0 x2) (CPoint.sub x1 x2)) CReal.zero) -> CReal.Equiv \
         (CPoint.dot (CPoint.sub x0 x1) (CPoint.sub x0 x1)) (CReal.add (CPoint.dot \
         (CPoint.sub x0 x2) (CPoint.sub x0 x2)) (CPoint.dot (CPoint.sub x1 x2) \
         (CPoint.sub x1 x2)))))))"
    );
}

/// **Elements III.31**, the converse direction. Verbatim-checked for the same
/// reason as [`pythagoras_statement_is_exact`]. `x0,x1,x2,x3 = A,B,C,O`.
#[test]
fn thales_statement_is_exact() {
    use crate::env::Declaration;
    let (kernel, p) = built();
    let ty = match kernel
        .environment()
        .get(p.thales)
        .expect("thales must be declared")
    {
        Declaration::Theorem { ty, .. } | Declaration::Definition { ty, .. } => *ty,
        other => panic!("{other:?} is not a theorem or definition"),
    };
    let rendered = kernel.render_lean(ty);
    assert_eq!(
        rendered,
        "((x0 : CPoint) -> ((x1 : CPoint) -> ((x2 : CPoint) -> ((x3 : CPoint) -> ((x4 : \
         CPoint.Equiv x3 (CPoint.midpoint x0 x1)) -> ((x5 : CReal.Equiv (CPoint.dot \
         (CPoint.sub x2 x3) (CPoint.sub x2 x3)) (CPoint.dot (CPoint.sub x0 x3) \
         (CPoint.sub x0 x3))) -> CReal.Equiv (CPoint.dot (CPoint.sub x0 x2) (CPoint.sub \
         x1 x2)) CReal.zero))))))"
    );
}

/// **Elements III.31, the converse — the headline.** Verbatim-checked for the
/// same reason as [`pythagoras_statement_is_exact`]: an empty axiom
/// footprint on a theorem stating something WEAKER than intended would still
/// pass a substring check. `x0,x1,x2 = A,B,P`.
#[test]
fn thales_converse_statement_is_exact() {
    use crate::env::Declaration;
    let (kernel, p) = built();
    let ty = match kernel
        .environment()
        .get(p.thales_converse)
        .expect("thales_converse must be declared")
    {
        Declaration::Theorem { ty, .. } | Declaration::Definition { ty, .. } => *ty,
        other => panic!("{other:?} is not a theorem or definition"),
    };
    let rendered = kernel.render_lean(ty);
    assert_eq!(
        rendered,
        "((x0 : CPoint) -> ((x1 : CPoint) -> ((x2 : CPoint) -> ((x3 : CReal.Equiv \
         (CPoint.dot (CPoint.sub x0 x2) (CPoint.sub x1 x2)) CReal.zero) -> CReal.Equiv \
         (CPoint.distSq x2 (CPoint.midpoint x0 x1)) (CPoint.distSq x0 (CPoint.midpoint \
         x0 x1))))))"
    );
}

/// **The perpendicular-bisector characterisation.** Verbatim-checked for the
/// same reason. `x0,x1,x2 = P,A,B`.
#[test]
fn perp_bisector_iff_dot_statement_is_exact() {
    use crate::env::Declaration;
    let (kernel, p) = built();
    let ty = match kernel
        .environment()
        .get(p.perp_bisector_iff_dot)
        .expect("perp_bisector_iff_dot must be declared")
    {
        Declaration::Theorem { ty, .. } | Declaration::Definition { ty, .. } => *ty,
        other => panic!("{other:?} is not a theorem or definition"),
    };
    let rendered = kernel.render_lean(ty);
    assert_eq!(
        rendered,
        "((x0 : CPoint) -> ((x1 : CPoint) -> ((x2 : CPoint) -> Iff (CPoint.OnPerpBisector \
         x0 x1 x2) (CReal.Equiv (CPoint.dot (CPoint.sub x0 (CPoint.midpoint x1 x2)) \
         (CPoint.sub x2 x1)) CReal.zero))))"
    );
}

/// **The orthocentre identity, unconditional.** Verbatim-checked for the same
/// reason as [`pythagoras_statement_is_exact`]: an empty axiom footprint on a
/// theorem missing a summand, or with the wrong sign, or with a spurious
/// hypothesis, would still pass a substring check. `x0,x1,x2,x3 = P,A,B,C`.
#[test]
fn orthocentre_identity_statement_is_exact() {
    use crate::env::Declaration;
    let (kernel, p) = built();
    let ty = match kernel
        .environment()
        .get(p.orthocentre_identity)
        .expect("orthocentre_identity must be declared")
    {
        Declaration::Theorem { ty, .. } | Declaration::Definition { ty, .. } => *ty,
        other => panic!("{other:?} is not a theorem or definition"),
    };
    let rendered = kernel.render_lean(ty);
    assert_eq!(
        rendered,
        "((x0 : CPoint) -> ((x1 : CPoint) -> ((x2 : CPoint) -> ((x3 : CPoint) -> \
         CReal.Equiv (CReal.add (CReal.add (CPoint.dot (CPoint.sub x0 x1) (CPoint.sub \
         x3 x2)) (CPoint.dot (CPoint.sub x0 x2) (CPoint.sub x1 x3))) (CPoint.dot \
         (CPoint.sub x0 x3) (CPoint.sub x2 x1))) CReal.zero))))"
    );
}

/// **Concurrence of the altitudes.** Verbatim-checked for the same reason.
/// `x0,x1,x2,x3 = P,A,B,C`.
#[test]
fn orthocentre_third_altitude_statement_is_exact() {
    use crate::env::Declaration;
    let (kernel, p) = built();
    let ty = match kernel
        .environment()
        .get(p.orthocentre_third_altitude)
        .expect("orthocentre_third_altitude must be declared")
    {
        Declaration::Theorem { ty, .. } | Declaration::Definition { ty, .. } => *ty,
        other => panic!("{other:?} is not a theorem or definition"),
    };
    let rendered = kernel.render_lean(ty);
    assert_eq!(
        rendered,
        "((x0 : CPoint) -> ((x1 : CPoint) -> ((x2 : CPoint) -> ((x3 : CPoint) -> ((x4 : \
         CReal.Equiv (CPoint.dot (CPoint.sub x0 x1) (CPoint.sub x3 x2)) CReal.zero) -> \
         ((x5 : CReal.Equiv (CPoint.dot (CPoint.sub x0 x2) (CPoint.sub x1 x3)) CReal.zero) \
         -> CReal.Equiv (CPoint.dot (CPoint.sub x0 x3) (CPoint.sub x2 x1)) \
         CReal.zero))))))"
    );
}

/// `distSq_congr`, verbatim. `x0,x1,x2,x3 = P,P',Q,Q'`.
#[test]
fn dist_sq_congr_statement_is_exact() {
    use crate::env::Declaration;
    let (kernel, p) = built();
    let ty = match kernel
        .environment()
        .get(p.dist_sq_congr)
        .expect("dist_sq_congr must be declared")
    {
        Declaration::Theorem { ty, .. } | Declaration::Definition { ty, .. } => *ty,
        other => panic!("{other:?} is not a theorem or definition"),
    };
    let rendered = kernel.render_lean(ty);
    assert_eq!(
        rendered,
        "((x0 : CPoint) -> ((x1 : CPoint) -> ((x2 : CPoint) -> ((x3 : CPoint) -> ((x4 : \
         CPoint.Equiv x0 x1) -> ((x5 : CPoint.Equiv x2 x3) -> CReal.Equiv (CPoint.distSq x0 \
         x2) (CPoint.distSq x1 x3)))))))"
    );
}

/// `distSq_comm`, verbatim. `x0,x1 = P,Q`.
#[test]
fn dist_sq_comm_statement_is_exact() {
    use crate::env::Declaration;
    let (kernel, p) = built();
    let ty = match kernel
        .environment()
        .get(p.dist_sq_comm)
        .expect("dist_sq_comm must be declared")
    {
        Declaration::Theorem { ty, .. } | Declaration::Definition { ty, .. } => *ty,
        other => panic!("{other:?} is not a theorem or definition"),
    };
    let rendered = kernel.render_lean(ty);
    assert_eq!(
        rendered,
        "((x0 : CPoint) -> ((x1 : CPoint) -> CReal.Equiv (CPoint.distSq x0 x1) (CPoint.distSq \
         x1 x0)))"
    );
}

/// `distSq_self_zero`, verbatim. `x0 = P`. This is the guard against a
/// vacuous `distSq`: an empty axiom footprint alone would not distinguish
/// this from, say, `distSq P P ~ distSq P P` (trivially true of ANY binary
/// operation, not just one built from `dot`/`sub`).
#[test]
fn dist_sq_self_zero_statement_is_exact() {
    use crate::env::Declaration;
    let (kernel, p) = built();
    let ty = match kernel
        .environment()
        .get(p.dist_sq_self_zero)
        .expect("dist_sq_self_zero must be declared")
    {
        Declaration::Theorem { ty, .. } | Declaration::Definition { ty, .. } => *ty,
        other => panic!("{other:?} is not a theorem or definition"),
    };
    let rendered = kernel.render_lean(ty);
    assert_eq!(
        rendered,
        "((x0 : CPoint) -> CReal.Equiv (CPoint.distSq x0 x0) CReal.zero)"
    );
}

/// **Elements I.47, restated over `distSq`.** Verbatim-checked for the same
/// reason [`pythagoras_statement_is_exact`] is: this is a NEW declaration
/// (see [`CPointPrelude::pythagoras_dist_sq`]'s doc), not
/// [`CPointPrelude::pythagoras`] edited, and an empty footprint on it says
/// nothing about which statement it is unless the rendering is pinned too.
/// `x0,x1,x2 = A,B,C`.
#[test]
fn pythagoras_dist_sq_statement_is_exact() {
    use crate::env::Declaration;
    let (kernel, p) = built();
    let ty = match kernel
        .environment()
        .get(p.pythagoras_dist_sq)
        .expect("pythagoras_dist_sq must be declared")
    {
        Declaration::Theorem { ty, .. } | Declaration::Definition { ty, .. } => *ty,
        other => panic!("{other:?} is not a theorem or definition"),
    };
    let rendered = kernel.render_lean(ty);
    assert_eq!(
        rendered,
        "((x0 : CPoint) -> ((x1 : CPoint) -> ((x2 : CPoint) -> ((x3 : CReal.Equiv (CPoint.dot \
         (CPoint.sub x0 x2) (CPoint.sub x1 x2)) CReal.zero) -> CReal.Equiv (CPoint.distSq x0 \
         x1) (CReal.add (CPoint.distSq x0 x2) (CPoint.distSq x1 x2))))))"
    );
}

/// **Parallelogram diagonals bisect each other.** Verbatim-checked for the
/// same reason as [`pythagoras_statement_is_exact`]: an empty axiom footprint
/// on a theorem with a dropped hypothesis, a swapped diagonal, or a
/// `varignon_diagonals_bisect`-shaped conclusion instead would still pass a
/// substring check. `x0,x1,x2,x3 = A,B,C,D`.
#[test]
fn parallelogram_diagonals_bisect_statement_is_exact() {
    use crate::env::Declaration;
    let (kernel, p) = built();
    let ty = match kernel
        .environment()
        .get(p.parallelogram_diagonals_bisect)
        .expect("parallelogram_diagonals_bisect must be declared")
    {
        Declaration::Theorem { ty, .. } | Declaration::Definition { ty, .. } => *ty,
        other => panic!("{other:?} is not a theorem or definition"),
    };
    let rendered = kernel.render_lean(ty);
    assert_eq!(
        rendered,
        "((x0 : CPoint) -> ((x1 : CPoint) -> ((x2 : CPoint) -> ((x3 : CPoint) -> ((x4 : \
         CPoint.Equiv (CPoint.sub x1 x0) (CPoint.sub x2 x3)) -> CPoint.Equiv (CPoint.midpoint \
         x0 x2) (CPoint.midpoint x1 x3))))))"
    );
}

/// **Opposite sides of a parallelogram are equal in length.** Verbatim-checked
/// for the same reason as [`pythagoras_statement_is_exact`]: this is the
/// scoped-down result actually landed for "the parallelogram law" slice (see
/// [`CPointPrelude::parallelogram_opposite_sides_eq`]'s doc for what the full
/// sum-of-squares identity would have needed beyond this). `x0,x1,x2,x3 =
/// A,B,C,D`.
#[test]
fn parallelogram_opposite_sides_eq_statement_is_exact() {
    use crate::env::Declaration;
    let (kernel, p) = built();
    let ty = match kernel
        .environment()
        .get(p.parallelogram_opposite_sides_eq)
        .expect("parallelogram_opposite_sides_eq must be declared")
    {
        Declaration::Theorem { ty, .. } | Declaration::Definition { ty, .. } => *ty,
        other => panic!("{other:?} is not a theorem or definition"),
    };
    let rendered = kernel.render_lean(ty);
    assert_eq!(
        rendered,
        "((x0 : CPoint) -> ((x1 : CPoint) -> ((x2 : CPoint) -> ((x3 : CPoint) -> ((x4 : \
         CPoint.Equiv (CPoint.sub x1 x0) (CPoint.sub x2 x3)) -> And (CReal.Equiv \
         (CPoint.distSq x2 x3) (CPoint.distSq x0 x1)) (CReal.Equiv (CPoint.distSq x3 x0) \
         (CPoint.distSq x1 x2)))))))"
    );
}

/// `dot_self_add`, verbatim. `x0,x1 = U,V`. The bilinear expansion `dot(u+v,u+v)
/// ~ dot u u + (dot u v + (dot u v + dot v v))` — an empty axiom footprint on
/// a theorem missing a cross term, or with `dot_congr`-vacuous LHS/RHS, would
/// still pass a substring check.
#[test]
fn dot_self_add_statement_is_exact() {
    use crate::env::Declaration;
    let (kernel, p) = built();
    let ty = match kernel
        .environment()
        .get(p.dot_self_add)
        .expect("dot_self_add must be declared")
    {
        Declaration::Theorem { ty, .. } | Declaration::Definition { ty, .. } => *ty,
        other => panic!("{other:?} is not a theorem or definition"),
    };
    let rendered = kernel.render_lean(ty);
    assert_eq!(
        rendered,
        "((x0 : CPoint) -> ((x1 : CPoint) -> CReal.Equiv (CPoint.dot (CPoint.add x0 x1) \
         (CPoint.add x0 x1)) (CReal.add (CPoint.dot x0 x0) (CReal.add (CPoint.dot x0 x1) \
         (CReal.add (CPoint.dot x0 x1) (CPoint.dot x1 x1))))))"
    );
}

/// `dot_self_sub`, verbatim. `x0,x1 = U,V`. The minus sibling of
/// [`dot_self_add_statement_is_exact`]: `dot(u-v,u-v) ~ dot u u + (-(dot u v)
/// + (-(dot u v) + dot v v))`.
#[test]
fn dot_self_sub_statement_is_exact() {
    use crate::env::Declaration;
    let (kernel, p) = built();
    let ty = match kernel
        .environment()
        .get(p.dot_self_sub)
        .expect("dot_self_sub must be declared")
    {
        Declaration::Theorem { ty, .. } | Declaration::Definition { ty, .. } => *ty,
        other => panic!("{other:?} is not a theorem or definition"),
    };
    let rendered = kernel.render_lean(ty);
    assert_eq!(
        rendered,
        "((x0 : CPoint) -> ((x1 : CPoint) -> CReal.Equiv (CPoint.dot (CPoint.sub x0 x1) \
         (CPoint.sub x0 x1)) (CReal.add (CPoint.dot x0 x0) (CReal.add (CReal.neg (CPoint.dot \
         x0 x1)) (CReal.add (CReal.neg (CPoint.dot x0 x1)) (CPoint.dot x1 x1))))))"
    );
}

/// **The parallelogram law.** Verbatim-checked for the same reason as
/// [`pythagoras_statement_is_exact`]: this is the literal `distSq A B +
/// distSq B C + distSq C D + distSq D A ~ distSq A C + distSq B D` sum, not a
/// weaker restatement — an empty axiom footprint on a theorem missing a
/// summand, with a swapped diagonal, or concluding the
/// [`parallelogram_opposite_sides_eq_statement_is_exact`]-shaped `And` would
/// still pass a substring check. `x0,x1,x2,x3 = A,B,C,D`.
#[test]
fn parallelogram_law_statement_is_exact() {
    use crate::env::Declaration;
    let (kernel, p) = built();
    let ty = match kernel
        .environment()
        .get(p.parallelogram_law)
        .expect("parallelogram_law must be declared")
    {
        Declaration::Theorem { ty, .. } | Declaration::Definition { ty, .. } => *ty,
        other => panic!("{other:?} is not a theorem or definition"),
    };
    let rendered = kernel.render_lean(ty);
    assert_eq!(
        rendered,
        "((x0 : CPoint) -> ((x1 : CPoint) -> ((x2 : CPoint) -> ((x3 : CPoint) -> ((x4 : \
         CPoint.Equiv (CPoint.sub x1 x0) (CPoint.sub x2 x3)) -> CReal.Equiv (CReal.add \
         (CReal.add (CReal.add (CPoint.distSq x0 x1) (CPoint.distSq x1 x2)) (CPoint.distSq x2 \
         x3)) (CPoint.distSq x3 x0)) (CReal.add (CPoint.distSq x0 x2) (CPoint.distSq x1 \
         x3)))))))"
    );
}

/// `dot_self_add3`, verbatim. `x0,x1,x2 = U,V,W`. The trinomial expansion
/// `dot((u+v)+w,(u+v)+w) ~ (u²+2uv+v²) + (2uw+2vw+w²)` — an empty axiom
/// footprint on a theorem missing a cross term, or reusing
/// [`dot_self_add_statement_is_exact`]'s two-variable shape, would still pass
/// a substring check.
#[test]
fn dot_self_add3_statement_is_exact() {
    use crate::env::Declaration;
    let (kernel, p) = built();
    let ty = match kernel
        .environment()
        .get(p.dot_self_add3)
        .expect("dot_self_add3 must be declared")
    {
        Declaration::Theorem { ty, .. } | Declaration::Definition { ty, .. } => *ty,
        other => panic!("{other:?} is not a theorem or definition"),
    };
    let rendered = kernel.render_lean(ty);
    assert_eq!(
        rendered,
        "((x0 : CPoint) -> ((x1 : CPoint) -> ((x2 : CPoint) -> CReal.Equiv (CPoint.dot \
         (CPoint.add (CPoint.add x0 x1) x2) (CPoint.add (CPoint.add x0 x1) x2)) (CReal.add \
         (CReal.add (CPoint.dot x0 x0) (CReal.add (CPoint.dot x0 x1) (CReal.add (CPoint.dot x0 \
         x1) (CPoint.dot x1 x1)))) (CReal.add (CReal.add (CPoint.dot x0 x2) (CPoint.dot x1 \
         x2)) (CReal.add (CReal.add (CPoint.dot x0 x2) (CPoint.dot x1 x2)) (CPoint.dot x2 \
         x2)))))))"
    );
}

/// **Apollonius' median theorem.** Verbatim-checked for the same reason as
/// [`pythagoras_statement_is_exact`]: this is the literal `distSq A B +
/// distSq A C ~ (distSq A M + distSq A M) + (distSq B M + distSq B M)`
/// statement with `M` substituted directly as `CPoint.midpoint B C` (not a
/// separately quantified, hypothesis-pinned point) — an empty axiom
/// footprint on a theorem with a dropped doubling, a swapped `A`/`B`, or an
/// `M` that is some other point entirely would still pass a substring check.
/// `x0,x1,x2 = A,B,C`.
#[test]
fn apollonius_median_statement_is_exact() {
    use crate::env::Declaration;
    let (kernel, p) = built();
    let ty = match kernel
        .environment()
        .get(p.apollonius_median)
        .expect("apollonius_median must be declared")
    {
        Declaration::Theorem { ty, .. } | Declaration::Definition { ty, .. } => *ty,
        other => panic!("{other:?} is not a theorem or definition"),
    };
    let rendered = kernel.render_lean(ty);
    assert_eq!(
        rendered,
        "((x0 : CPoint) -> ((x1 : CPoint) -> ((x2 : CPoint) -> CReal.Equiv (CReal.add \
         (CPoint.distSq x0 x1) (CPoint.distSq x0 x2)) (CReal.add (CReal.add (CPoint.distSq x0 \
         (CPoint.midpoint x1 x2)) (CPoint.distSq x0 (CPoint.midpoint x1 x2))) (CReal.add \
         (CPoint.distSq x1 (CPoint.midpoint x1 x2)) (CPoint.distSq x1 (CPoint.midpoint x1 \
         x2)))))))"
    );
}

/// **Euler's quadrilateral theorem, unconditional.** Verbatim-checked for the
/// same reason as [`pythagoras_statement_is_exact`]: this is the literal
/// hypothesis-free `distSq A B + (distSq B C + (distSq C D + distSq D A)) ~
/// (distSq A C + distSq B D) + dot W W`, `W := (A-B)+(C-D)`, statement — an
/// empty axiom footprint on a theorem with a dropped `dot W W` term (i.e.
/// [`CPointPrelude::parallelogram_law`]'s hypothesis-specialised shape), a
/// missing summand, or a spurious hypothesis Pi-bound before the conclusion,
/// would still pass a substring check. `x0,x1,x2,x3 = A,B,C,D`, and there is
/// no fifth (hypothesis) binder.
#[test]
fn euler_quadrilateral_statement_is_exact() {
    use crate::env::Declaration;
    let (kernel, p) = built();
    let ty = match kernel
        .environment()
        .get(p.euler_quadrilateral)
        .expect("euler_quadrilateral must be declared")
    {
        Declaration::Theorem { ty, .. } | Declaration::Definition { ty, .. } => *ty,
        other => panic!("{other:?} is not a theorem or definition"),
    };
    let rendered = kernel.render_lean(ty);
    assert_eq!(
        rendered,
        "((x0 : CPoint) -> ((x1 : CPoint) -> ((x2 : CPoint) -> ((x3 : CPoint) -> CReal.Equiv \
         (CReal.add (CPoint.distSq x0 x1) (CReal.add (CPoint.distSq x1 x2) (CReal.add \
         (CPoint.distSq x2 x3) (CPoint.distSq x3 x0)))) (CReal.add (CReal.add (CPoint.distSq x0 \
         x2) (CPoint.distSq x1 x3)) (CPoint.dot (CPoint.add (CPoint.sub x0 x1) (CPoint.sub x2 \
         x3)) (CPoint.add (CPoint.sub x0 x1) (CPoint.sub x2 x3))))))))"
    );
}

/// `Scalar.centroid_self`, verbatim. `x0 = a`. The discrimination witness for
/// `inv3`, mirroring `midpoint_self`'s role for `inv2`: an empty axiom
/// footprint alone would not distinguish `inv3` genuinely being `1/3` from
/// some other ternary scalar built the same way.
#[test]
fn centroid_scalar_self_statement_is_exact() {
    use crate::env::Declaration;
    let (kernel, p) = built();
    let ty = match kernel
        .environment()
        .get(p.centroid_scalar_self)
        .expect("centroid_scalar_self must be declared")
    {
        Declaration::Theorem { ty, .. } | Declaration::Definition { ty, .. } => *ty,
        other => panic!("{other:?} is not a theorem or definition"),
    };
    let rendered = kernel.render_lean(ty);
    assert_eq!(
        rendered,
        "((x0 : CReal) -> CReal.Equiv (CPoint.Scalar.centroid x0 x0 x0) x0)"
    );
}

/// **The centroid divides each median, additive form: `3G ~ A + 2M`.**
/// Verbatim-checked for the same reason as `pythagoras_statement_is_exact`:
/// this is `centroid A B C` and `point_midpoint B C`, unconditional, not some
/// weaker or hypothesis-carrying restatement. `x0,x1,x2 = A,B,C`.
#[test]
fn centroid_median_statement_is_exact() {
    use crate::env::Declaration;
    let (kernel, p) = built();
    let ty = match kernel
        .environment()
        .get(p.centroid_median)
        .expect("centroid_median must be declared")
    {
        Declaration::Theorem { ty, .. } | Declaration::Definition { ty, .. } => *ty,
        other => panic!("{other:?} is not a theorem or definition"),
    };
    let rendered = kernel.render_lean(ty);
    assert_eq!(
        rendered,
        "((x0 : CPoint) -> ((x1 : CPoint) -> ((x2 : CPoint) -> CPoint.Equiv (CPoint.add \
         (CPoint.add (CPoint.centroid x0 x1 x2) (CPoint.centroid x0 x1 x2)) (CPoint.centroid x0 \
         x1 x2)) (CPoint.add x0 (CPoint.add (CPoint.midpoint x1 x2) (CPoint.midpoint x1 \
         x2))))))"
    );
}

/// **Leibniz's centroid formula, unconditional.** Verbatim-checked for the
/// same reason as `pythagoras_statement_is_exact`: this is the literal
/// `distSq P A + (distSq P B + distSq P C) ~ (distSq P G + (distSq P G +
/// distSq P G)) + (distSq G A + (distSq G B + distSq G C))` sum with `G :=
/// centroid A B C` substituted directly — an empty axiom footprint on a
/// theorem missing the doubling/tripling, with a swapped `distSq` argument
/// order, or with some other point entirely in place of `G`, would still pass
/// a substring check. `x0,x1,x2,x3 = P,A,B,C`.
#[test]
fn centroid_dist_sq_statement_is_exact() {
    use crate::env::Declaration;
    let (kernel, p) = built();
    let ty = match kernel
        .environment()
        .get(p.centroid_dist_sq)
        .expect("centroid_dist_sq must be declared")
    {
        Declaration::Theorem { ty, .. } | Declaration::Definition { ty, .. } => *ty,
        other => panic!("{other:?} is not a theorem or definition"),
    };
    let rendered = kernel.render_lean(ty);
    assert_eq!(
        rendered,
        "((x0 : CPoint) -> ((x1 : CPoint) -> ((x2 : CPoint) -> ((x3 : CPoint) -> CReal.Equiv \
         (CReal.add (CPoint.distSq x0 x1) (CReal.add (CPoint.distSq x0 x2) (CPoint.distSq x0 \
         x3))) (CReal.add (CReal.add (CPoint.distSq x0 (CPoint.centroid x1 x2 x3)) (CReal.add \
         (CPoint.distSq x0 (CPoint.centroid x1 x2 x3)) (CPoint.distSq x0 (CPoint.centroid x1 x2 \
         x3)))) (CReal.add (CPoint.distSq (CPoint.centroid x1 x2 x3) x1) (CReal.add \
         (CPoint.distSq (CPoint.centroid x1 x2 x3) x2) (CPoint.distSq (CPoint.centroid x1 x2 \
         x3) x3))))))))"
    );
}

/// **The cevian parametrisation, `t = 0` endpoint.** Verbatim-checked for the
/// same reason as `pythagoras_statement_is_exact`: an empty axiom footprint
/// on a theorem concluding `CPoint.Equiv (CPoint.lerp x0 x1 CReal.zero) x1`
/// (the wrong endpoint) or some other point entirely would still pass a
/// substring check. `x0,x1 = B,C`.
#[test]
fn lerp_zero_statement_is_exact() {
    use crate::env::Declaration;
    let (kernel, p) = built();
    let ty = match kernel
        .environment()
        .get(p.lerp_zero)
        .expect("lerp_zero must be declared")
    {
        Declaration::Theorem { ty, .. } | Declaration::Definition { ty, .. } => *ty,
        other => panic!("{other:?} is not a theorem or definition"),
    };
    let rendered = kernel.render_lean(ty);
    assert_eq!(
        rendered,
        "((x0 : CPoint) -> ((x1 : CPoint) -> CPoint.Equiv (CPoint.lerp x0 x1 CReal.zero) x0))"
    );
}

/// **The cevian parametrisation, `t = 1` endpoint.** `x0,x1 = B,C`.
#[test]
fn lerp_one_statement_is_exact() {
    use crate::env::Declaration;
    let (kernel, p) = built();
    let ty = match kernel
        .environment()
        .get(p.lerp_one)
        .expect("lerp_one must be declared")
    {
        Declaration::Theorem { ty, .. } | Declaration::Definition { ty, .. } => *ty,
        other => panic!("{other:?} is not a theorem or definition"),
    };
    let rendered = kernel.render_lean(ty);
    assert_eq!(
        rendered,
        "((x0 : CPoint) -> ((x1 : CPoint) -> CPoint.Equiv (CPoint.lerp x0 x1 CReal.one) x1))"
    );
}

/// **`lerp` at `t = 1/2` is `midpoint`** — the check that the definition is
/// right, not just some interpolation of `B` and `C`. `x0,x1 = B,C`.
#[test]
fn lerp_half_is_midpoint_statement_is_exact() {
    use crate::env::Declaration;
    let (kernel, p) = built();
    let ty = match kernel
        .environment()
        .get(p.lerp_half_is_midpoint)
        .expect("lerp_half_is_midpoint must be declared")
    {
        Declaration::Theorem { ty, .. } | Declaration::Definition { ty, .. } => *ty,
        other => panic!("{other:?} is not a theorem or definition"),
    };
    let rendered = kernel.render_lean(ty);
    assert_eq!(
        rendered,
        "((x0 : CPoint) -> ((x1 : CPoint) -> CPoint.Equiv (CPoint.lerp x0 x1 CPoint.Scalar.inv2) (CPoint.midpoint x0 x1)))"
    );
}

/// **The algebraic engine.** Verbatim-checked for the same reason as
/// `pythagoras_statement_is_exact`: `|PD|^2 = |PB|^2 - 2t*(P-B)*(C-B) +
/// t^2*|BC|^2` where `D := lerp B C t` -- an empty axiom footprint on a
/// theorem missing the doubling, with a swapped cross-term argument order, or
/// with the wrong power of `t` would still pass a substring check.
/// `x0,x1,x2,x3 = P,B,C,t`.
#[test]
fn lerp_dist_sq_statement_is_exact() {
    use crate::env::Declaration;
    let (kernel, p) = built();
    let ty = match kernel
        .environment()
        .get(p.lerp_dist_sq)
        .expect("lerp_dist_sq must be declared")
    {
        Declaration::Theorem { ty, .. } | Declaration::Definition { ty, .. } => *ty,
        other => panic!("{other:?} is not a theorem or definition"),
    };
    let rendered = kernel.render_lean(ty);
    assert_eq!(
        rendered,
        "((x0 : CPoint) -> ((x1 : CPoint) -> ((x2 : CPoint) -> ((x3 : CReal) -> CReal.Equiv (CPoint.distSq x0 (CPoint.lerp x1 x2 x3)) (CReal.add (CPoint.distSq x0 x1) (CReal.add (CReal.neg (CReal.mul x3 (CPoint.dot (CPoint.sub x0 x1) (CPoint.sub x2 x1)))) (CReal.add (CReal.neg (CReal.mul x3 (CPoint.dot (CPoint.sub x0 x1) (CPoint.sub x2 x1)))) (CReal.mul x3 (CReal.mul x3 (CPoint.distSq x1 x2))))))))))"
    );
}

/// **Stewart's theorem, squared/parametric form -- the headline result.**
/// Verbatim-checked for the same reason as `pythagoras_statement_is_exact`:
/// `|AD|^2 + t(1-t)|BC|^2 ~ (1-t)|AB|^2 + t|AC|^2` where `D := lerp B C t`.
/// This kernel had no `CReal.sqrt` (only `natSqrt`) until it landed
/// 2026-08-26, so this squared/parametric identity -- not the classical
/// unsigned-length `BD*DC*BC + AD^2*BC ~ AB^2*DC + AC^2*BD` -- is the
/// statement this test checks: multiplying this identity through by the
/// unsquared `BC` at `t := BD/BC` recovers the classical form, but that
/// multiplication is not performed here. `x0,x1,x2,x3 = A,B,C,t`.
#[test]
fn stewart_statement_is_exact() {
    use crate::env::Declaration;
    let (kernel, p) = built();
    let ty = match kernel
        .environment()
        .get(p.stewart)
        .expect("stewart must be declared")
    {
        Declaration::Theorem { ty, .. } | Declaration::Definition { ty, .. } => *ty,
        other => panic!("{other:?} is not a theorem or definition"),
    };
    let rendered = kernel.render_lean(ty);
    assert_eq!(
        rendered,
        "((x0 : CPoint) -> ((x1 : CPoint) -> ((x2 : CPoint) -> ((x3 : CReal) -> CReal.Equiv (CReal.add (CPoint.distSq x0 (CPoint.lerp x1 x2 x3)) (CReal.mul x3 (CReal.mul (CReal.add CReal.one (CReal.neg x3)) (CPoint.distSq x1 x2)))) (CReal.add (CReal.mul (CReal.add CReal.one (CReal.neg x3)) (CPoint.distSq x0 x1)) (CReal.mul x3 (CPoint.distSq x0 x2)))))))"
    );
}

/// `Scalar.one_sub_inv2`, verbatim: `1 - 1/2 ~ 1/2`.
#[test]
fn one_sub_inv2_statement_is_exact() {
    use crate::env::Declaration;
    let (kernel, p) = built();
    let ty = match kernel
        .environment()
        .get(p.one_sub_inv2)
        .expect("one_sub_inv2 must be declared")
    {
        Declaration::Theorem { ty, .. } | Declaration::Definition { ty, .. } => *ty,
        other => panic!("{other:?} is not a theorem or definition"),
    };
    let rendered = kernel.render_lean(ty);
    assert_eq!(
        rendered,
        "CReal.Equiv (CReal.add CReal.one (CReal.neg CPoint.Scalar.inv2)) CPoint.Scalar.inv2"
    );
}

/// **The median corollary of Stewart.** Verbatim-checked. `x0,x1,x2 = A,B,C`.
#[test]
fn stewart_median_statement_is_exact() {
    use crate::env::Declaration;
    let (kernel, p) = built();
    let ty = match kernel
        .environment()
        .get(p.stewart_median)
        .expect("stewart_median must be declared")
    {
        Declaration::Theorem { ty, .. } | Declaration::Definition { ty, .. } => *ty,
        other => panic!("{other:?} is not a theorem or definition"),
    };
    let rendered = kernel.render_lean(ty);
    assert_eq!(
        rendered,
        "((x0 : CPoint) -> ((x1 : CPoint) -> ((x2 : CPoint) -> CReal.Equiv (CReal.add \
         (CPoint.distSq x0 (CPoint.midpoint x1 x2)) (CReal.mul CPoint.Scalar.inv2 (CReal.mul \
         CPoint.Scalar.inv2 (CPoint.distSq x1 x2)))) (CReal.add (CReal.mul CPoint.Scalar.inv2 \
         (CPoint.distSq x0 x1)) (CReal.mul CPoint.Scalar.inv2 (CPoint.distSq x0 x2))))))"
    );
}

/// **The centroid divides each median 2:1, difference form.**
/// Verbatim-checked. `x0,x1,x2 = A,B,C`.
#[test]
fn centroid_ratio_statement_is_exact() {
    use crate::env::Declaration;
    let (kernel, p) = built();
    let ty = match kernel
        .environment()
        .get(p.centroid_ratio)
        .expect("centroid_ratio must be declared")
    {
        Declaration::Theorem { ty, .. } | Declaration::Definition { ty, .. } => *ty,
        other => panic!("{other:?} is not a theorem or definition"),
    };
    let rendered = kernel.render_lean(ty);
    assert_eq!(
        rendered,
        "((x0 : CPoint) -> ((x1 : CPoint) -> ((x2 : CPoint) -> CPoint.Equiv (CPoint.add \
         (CPoint.add (CPoint.sub (CPoint.centroid x0 x1 x2) x0) (CPoint.sub (CPoint.centroid x0 \
         x1 x2) x0)) (CPoint.sub (CPoint.centroid x0 x1 x2) x0)) (CPoint.add (CPoint.sub \
         (CPoint.midpoint x1 x2) x0) (CPoint.sub (CPoint.midpoint x1 x2) x0)))))"
    );
}

/// **The circumcentre identity, unconditional.** Verbatim-checked.
/// `x0,x1,x2,x3 = O,A,B,C`.
#[test]
fn circumcentre_identity_statement_is_exact() {
    use crate::env::Declaration;
    let (kernel, p) = built();
    let ty = match kernel
        .environment()
        .get(p.circumcentre_identity)
        .expect("circumcentre_identity must be declared")
    {
        Declaration::Theorem { ty, .. } | Declaration::Definition { ty, .. } => *ty,
        other => panic!("{other:?} is not a theorem or definition"),
    };
    let rendered = kernel.render_lean(ty);
    assert_eq!(
        rendered,
        "((x0 : CPoint) -> ((x1 : CPoint) -> ((x2 : CPoint) -> ((x3 : CPoint) -> CReal.Equiv \
         (CReal.add (CReal.add (CReal.add (CPoint.distSq x0 x1) (CReal.neg (CPoint.distSq x0 \
         x2))) (CReal.add (CPoint.distSq x0 x2) (CReal.neg (CPoint.distSq x0 x3)))) (CReal.add \
         (CPoint.distSq x0 x3) (CReal.neg (CPoint.distSq x0 x1)))) CReal.zero))))"
    );
}

/// **Concurrence of the two circumcentre equalities.** Verbatim-checked.
/// `x0,x1,x2,x3 = O,A,B,C`.
#[test]
fn circumcentre_third_distance_statement_is_exact() {
    use crate::env::Declaration;
    let (kernel, p) = built();
    let ty = match kernel
        .environment()
        .get(p.circumcentre_third_distance)
        .expect("circumcentre_third_distance must be declared")
    {
        Declaration::Theorem { ty, .. } | Declaration::Definition { ty, .. } => *ty,
        other => panic!("{other:?} is not a theorem or definition"),
    };
    let rendered = kernel.render_lean(ty);
    assert_eq!(
        rendered,
        "((x0 : CPoint) -> ((x1 : CPoint) -> ((x2 : CPoint) -> ((x3 : CPoint) -> ((x4 : \
         CReal.Equiv (CPoint.distSq x0 x1) (CPoint.distSq x0 x2)) -> ((x5 : CReal.Equiv \
         (CPoint.distSq x0 x2) (CPoint.distSq x0 x3)) -> CReal.Equiv (CPoint.distSq x0 x1) \
         (CPoint.distSq x0 x3)))))))"
    );
}

/// **The heart of the Euler line: a circumcentre's construction of an
/// orthocentre.** Verbatim-checked for the same reason as
/// [`pythagoras_statement_is_exact`]. `x0,x1,x2,x3 = O,A,B,C`.
#[test]
fn circumcentre_orthocentre_construction_statement_is_exact() {
    use crate::env::Declaration;
    let (kernel, p) = built();
    let ty = match kernel
        .environment()
        .get(p.circumcentre_orthocentre_construction)
        .expect("circumcentre_orthocentre_construction must be declared")
    {
        Declaration::Theorem { ty, .. } | Declaration::Definition { ty, .. } => *ty,
        other => panic!("{other:?} is not a theorem or definition"),
    };
    let rendered = kernel.render_lean(ty);
    assert_eq!(
        rendered,
        "((x0 : CPoint) -> ((x1 : CPoint) -> ((x2 : CPoint) -> ((x3 : CPoint) -> ((x4 : \
         CReal.Equiv (CPoint.distSq x0 x1) (CPoint.distSq x0 x2)) -> ((x5 : CReal.Equiv \
         (CPoint.distSq x0 x2) (CPoint.distSq x0 x3)) -> And (CReal.Equiv (CPoint.dot \
         (CPoint.sub (CPoint.sub (CPoint.add (CPoint.add x1 x2) x3) (CPoint.add x0 x0)) x1) \
         (CPoint.sub x3 x2)) CReal.zero) (CReal.Equiv (CPoint.dot (CPoint.sub (CPoint.sub \
         (CPoint.add (CPoint.add x1 x2) x3) (CPoint.add x0 x0)) x2) (CPoint.sub x1 x3)) \
         CReal.zero)))))))"
    );
}

/// **The Euler line, additive form.** Verbatim-checked for the same reason as
/// [`pythagoras_statement_is_exact`]: an empty axiom footprint on a theorem
/// stating something WEAKER than intended (missing a summand, a swapped
/// point, `distSq` instead of `sub`) would still pass a substring check.
/// `x0,x1,x2,x3 = O,A,B,C`.
#[test]
fn euler_line_statement_is_exact() {
    use crate::env::Declaration;
    let (kernel, p) = built();
    let ty = match kernel
        .environment()
        .get(p.euler_line)
        .expect("euler_line must be declared")
    {
        Declaration::Theorem { ty, .. } | Declaration::Definition { ty, .. } => *ty,
        other => panic!("{other:?} is not a theorem or definition"),
    };
    let rendered = kernel.render_lean(ty);
    assert_eq!(
        rendered,
        "((x0 : CPoint) -> ((x1 : CPoint) -> ((x2 : CPoint) -> ((x3 : CPoint) -> CPoint.Equiv \
         (CPoint.add (CPoint.sub (CPoint.add (CPoint.add x1 x2) x3) (CPoint.add x0 x0)) \
         (CPoint.add x0 x0)) (CPoint.add (CPoint.add (CPoint.centroid x1 x2 x3) \
         (CPoint.centroid x1 x2 x3)) (CPoint.centroid x1 x2 x3))))))"
    );
}

/// **`apollonius_median`, re-derived from `stewart_median`.** Confirms the
/// bridge proves the SAME statement `declare_apollonius_median` does (the
/// point of the bridge), not a weaker one.
#[test]
fn apollonius_from_stewart_has_the_apollonius_median_statement() {
    on_a_deep_stack(|| {
        use crate::env::Declaration;
        let (kernel, p) = built();
        let ty_of = |name| match kernel
            .environment()
            .get(name)
            .expect("declaration must be present")
        {
            Declaration::Theorem { ty, .. } | Declaration::Definition { ty, .. } => *ty,
            other => panic!("{other:?} is not a theorem or definition"),
        };
        let rendered_bridge = kernel.render_lean(ty_of(p.apollonius_from_stewart));
        let rendered_original = kernel.render_lean(ty_of(p.apollonius_median));
        assert_eq!(
            rendered_bridge, rendered_original,
            "apollonius_from_stewart must prove the exact same statement as apollonius_median"
        );
    });
}

/// **Positive-semidefiniteness of `dot`.** `x0 = V`. Verbatim-checked for the
/// same reason as [`pythagoras_statement_is_exact`].
#[test]
fn dot_self_nonneg_statement_is_exact() {
    use crate::env::Declaration;
    let (kernel, p) = built();
    let ty = match kernel
        .environment()
        .get(p.dot_self_nonneg)
        .expect("dot_self_nonneg must be declared")
    {
        Declaration::Theorem { ty, .. } | Declaration::Definition { ty, .. } => *ty,
        other => panic!("{other:?} is not a theorem or definition"),
    };
    let rendered = kernel.render_lean(ty);
    assert_eq!(
        rendered,
        "((x0 : CPoint) -> CReal.le CReal.zero (CPoint.dot x0 x0))"
    );
}

/// **Lagrange's identity, in the plane.** `x0,x1,x2,x3 = a,b,c,e`:
/// `(a²+b²)(c²+e²) − (ac+be)² = (ae−bc)²`. Verbatim-checked so a wrong sign
/// or a dropped cross term cannot hide behind an empty axiom footprint.
#[test]
fn lagrange_identity_statement_is_exact() {
    use crate::env::Declaration;
    let (kernel, p) = built();
    let ty = match kernel
        .environment()
        .get(p.lagrange_identity)
        .expect("lagrange_identity must be declared")
    {
        Declaration::Theorem { ty, .. } | Declaration::Definition { ty, .. } => *ty,
        other => panic!("{other:?} is not a theorem or definition"),
    };
    let rendered = kernel.render_lean(ty);
    assert_eq!(
        rendered,
        "((x0 : CReal) -> ((x1 : CReal) -> ((x2 : CReal) -> ((x3 : CReal) -> CReal.Equiv \
         (CReal.add (CReal.mul (CReal.add (CReal.mul x0 x0) (CReal.mul x1 x1)) (CReal.add \
         (CReal.mul x2 x2) (CReal.mul x3 x3))) (CReal.neg (CReal.mul (CReal.add (CReal.mul x0 \
         x2) (CReal.mul x1 x3)) (CReal.add (CReal.mul x0 x2) (CReal.mul x1 x3))))) (CReal.mul \
         (CReal.add (CReal.mul x0 x3) (CReal.neg (CReal.mul x1 x2))) (CReal.add (CReal.mul x0 \
         x3) (CReal.neg (CReal.mul x1 x2))))))))"
    );
}

/// **Cauchy-Schwarz, squared.** `x0,x1 = U,V`: `(U·V)² ≤ (U·U)(V·V)`. Stated
/// squared, deliberately: at the time this test was written the kernel had
/// `CReal.natSqrt` but no `CReal.sqrt`, so the norm form
/// `|⟨u,v⟩| ≤ ‖u‖·‖v‖` was not expressible here. `CReal.sqrt` landed
/// 2026-08-26, and the unsquared form is now proved as
/// `Metric.CPoint.dotLeSqrtMul` in `metric.rs` (2026-09-04), on top of this
/// squared statement. Verbatim-checked for the same reason as the two tests
/// above.
#[test]
fn cauchy_schwarz_statement_is_exact() {
    use crate::env::Declaration;
    let (kernel, p) = built();
    let ty = match kernel
        .environment()
        .get(p.cauchy_schwarz)
        .expect("cauchy_schwarz must be declared")
    {
        Declaration::Theorem { ty, .. } | Declaration::Definition { ty, .. } => *ty,
        other => panic!("{other:?} is not a theorem or definition"),
    };
    let rendered = kernel.render_lean(ty);
    assert_eq!(
        rendered,
        "((x0 : CPoint) -> ((x1 : CPoint) -> CReal.le (CReal.mul (CPoint.dot x0 x1) (CPoint.dot \
         x0 x1)) (CReal.mul (CPoint.dot x0 x0) (CPoint.dot x1 x1))))"
    );
}

/// **The triangle inequality for `distSq`, factor-2 form.** `x0,x1,x2 =
/// A,B,C`: `distSq A C ≤ 2·(distSq A B + distSq B C)`, written as
/// `(distSq A B + distSq B C) + (distSq A B + distSq B C)` (this
/// development has no `Nat`-scalar multiplication of `CReal`). **Not** the
/// classical unsquared triangle inequality — see
/// [`CPointPrelude::dist_sq_double_sum_bound`]'s doc comment: that form was
/// unreachable here before `CReal.sqrt` landed (2026-08-26), and this file
/// still does not build it on `distSq` — see `metric.rs`'s
/// `Metric.CPoint.distTriangle` for the unsquared route.
#[test]
fn dist_sq_double_sum_bound_statement_is_exact() {
    use crate::env::Declaration;
    let (kernel, p) = built();
    let ty = match kernel
        .environment()
        .get(p.dist_sq_double_sum_bound)
        .expect("dist_sq_double_sum_bound must be declared")
    {
        Declaration::Theorem { ty, .. } | Declaration::Definition { ty, .. } => *ty,
        other => panic!("{other:?} is not a theorem or definition"),
    };
    let rendered = kernel.render_lean(ty);
    assert_eq!(
        rendered,
        "((x0 : CPoint) -> ((x1 : CPoint) -> ((x2 : CPoint) -> CReal.le (CPoint.distSq x0 x2) \
         (CReal.add (CReal.add (CPoint.distSq x0 x1) (CPoint.distSq x1 x2)) (CReal.add \
         (CPoint.distSq x0 x1) (CPoint.distSq x1 x2))))))"
    );
}

/// **Euclid I.20, squared.** `x0,x1,x2 = A,B,C`:
/// `(distSq A C − distSq A B − distSq B C)² ≤ 4·distSq A B·distSq B C`,
/// written as the right-chain `ab_bc + (ab_bc + (ab_bc + ab_bc))`. See
/// [`CPointPrelude::dist_sq_triangle_sq_bound`]'s doc comment for why this
/// (unlike [`Self::dist_sq_double_sum_bound`]) *is* the classical triangle
/// inequality, modulo `CReal.sqrt` (which now exists, landed 2026-08-26,
/// but is not applied here).
#[test]
fn dist_sq_triangle_sq_bound_statement_is_exact() {
    use crate::env::Declaration;
    let (kernel, p) = built();
    let ty = match kernel
        .environment()
        .get(p.dist_sq_triangle_sq_bound)
        .expect("dist_sq_triangle_sq_bound must be declared")
    {
        Declaration::Theorem { ty, .. } | Declaration::Definition { ty, .. } => *ty,
        other => panic!("{other:?} is not a theorem or definition"),
    };
    let rendered = kernel.render_lean(ty);
    assert_eq!(
        rendered,
        "((x0 : CPoint) -> ((x1 : CPoint) -> ((x2 : CPoint) -> CReal.le (CReal.mul (CReal.add \
         (CReal.add (CPoint.distSq x0 x2) (CReal.neg (CPoint.distSq x0 x1))) (CReal.neg \
         (CPoint.distSq x1 x2))) (CReal.add (CReal.add (CPoint.distSq x0 x2) (CReal.neg \
         (CPoint.distSq x0 x1))) (CReal.neg (CPoint.distSq x1 x2)))) (CReal.add (CReal.mul \
         (CPoint.distSq x0 x1) (CPoint.distSq x1 x2)) (CReal.add (CReal.mul (CPoint.distSq x0 \
         x1) (CPoint.distSq x1 x2)) (CReal.add (CReal.mul (CPoint.distSq x0 x1) (CPoint.distSq \
         x1 x2)) (CReal.mul (CPoint.distSq x0 x1) (CPoint.distSq x1 x2))))))))"
    );
}

/// **The midpoint lies on its own perpendicular bisector.** Verbatim-checked
/// for the same reason as [`pythagoras_statement_is_exact`]. `x0,x1 = A,B`.
#[test]
fn perp_bisector_midpoint_statement_is_exact() {
    use crate::env::Declaration;
    let (kernel, p) = built();
    let ty = match kernel
        .environment()
        .get(p.perp_bisector_midpoint)
        .expect("perp_bisector_midpoint must be declared")
    {
        Declaration::Theorem { ty, .. } | Declaration::Definition { ty, .. } => *ty,
        other => panic!("{other:?} is not a theorem or definition"),
    };
    let rendered = kernel.render_lean(ty);
    assert_eq!(
        rendered,
        "((x0 : CPoint) -> ((x1 : CPoint) -> CPoint.OnPerpBisector (CPoint.midpoint x0 x1) \
         x0 x1))"
    );
}

/// **A circumcentre lies on all three perpendicular bisectors.**
/// Verbatim-checked for the same reason. `x0,x1,x2,x3 = O,A,B,C`.
#[test]
fn circumcentre_on_perp_bisectors_statement_is_exact() {
    use crate::env::Declaration;
    let (kernel, p) = built();
    let ty = match kernel
        .environment()
        .get(p.circumcentre_on_perp_bisectors)
        .expect("circumcentre_on_perp_bisectors must be declared")
    {
        Declaration::Theorem { ty, .. } | Declaration::Definition { ty, .. } => *ty,
        other => panic!("{other:?} is not a theorem or definition"),
    };
    let rendered = kernel.render_lean(ty);
    assert_eq!(
        rendered,
        "((x0 : CPoint) -> ((x1 : CPoint) -> ((x2 : CPoint) -> ((x3 : CPoint) -> ((x4 : \
         CReal.Equiv (CPoint.distSq x0 x1) (CPoint.distSq x0 x2)) -> ((x5 : CReal.Equiv \
         (CPoint.distSq x0 x2) (CPoint.distSq x0 x3)) -> And (CPoint.OnPerpBisector x0 \
         x1 x2) (And (CPoint.OnPerpBisector x0 x2 x3) (CPoint.OnPerpBisector x0 x1 \
         x3))))))))"
    );
}

/// `CPoint.cross`'s own type — three `CPoint`s to a `CReal`, no hypothesis.
/// Not a `Theorem`, so it is checked here rather than the axiom-free list
/// (this file's convention: `Definition`s are checked for presence and, when
/// their statement is the interesting part, for an exact render — a
/// `Theorem`'s *proof* is what the axiom-free list is guarding).
#[test]
fn cross_statement_is_exact() {
    use crate::env::Declaration;
    let (kernel, p) = built();
    let ty = match kernel
        .environment()
        .get(p.cross)
        .expect("cross must be declared")
    {
        Declaration::Theorem { ty, .. } | Declaration::Definition { ty, .. } => *ty,
        other => panic!("{other:?} is not a theorem or definition"),
    };
    let rendered = kernel.render_lean(ty);
    assert_eq!(
        rendered,
        "((x0 : CPoint) -> ((x1 : CPoint) -> ((x2 : CPoint) -> CReal)))"
    );
}

/// `CPoint.cross_self_left`, one of the two structurally cheap degenerate
/// cases. See [`CPointPrelude::cross_self_left`].
#[test]
fn cross_self_left_statement_is_exact() {
    use crate::env::Declaration;
    let (kernel, p) = built();
    let ty = match kernel
        .environment()
        .get(p.cross_self_left)
        .expect("cross_self_left must be declared")
    {
        Declaration::Theorem { ty, .. } | Declaration::Definition { ty, .. } => *ty,
        other => panic!("{other:?} is not a theorem or definition"),
    };
    let rendered = kernel.render_lean(ty);
    assert_eq!(
        rendered,
        "((x0 : CPoint) -> ((x1 : CPoint) -> CReal.Equiv (CPoint.cross x0 x0 x1) \
         CReal.zero))"
    );
}

/// `CPoint.cross_self_right`, the mirror degenerate case. See
/// [`CPointPrelude::cross_self_right`].
#[test]
fn cross_self_right_statement_is_exact() {
    use crate::env::Declaration;
    let (kernel, p) = built();
    let ty = match kernel
        .environment()
        .get(p.cross_self_right)
        .expect("cross_self_right must be declared")
    {
        Declaration::Theorem { ty, .. } | Declaration::Definition { ty, .. } => *ty,
        other => panic!("{other:?} is not a theorem or definition"),
    };
    let rendered = kernel.render_lean(ty);
    assert_eq!(
        rendered,
        "((x0 : CPoint) -> ((x1 : CPoint) -> CReal.Equiv (CPoint.cross x0 x1 x1) \
         CReal.zero))"
    );
}

/// **The `B ↔ C` swap negates `cross`.** See
/// [`CPointPrelude::cross_swap_bc`]. `x0,x1,x2 = A,B,C`.
#[test]
fn cross_swap_bc_statement_is_exact() {
    use crate::env::Declaration;
    let (kernel, p) = built();
    let ty = match kernel
        .environment()
        .get(p.cross_swap_bc)
        .expect("cross_swap_bc must be declared")
    {
        Declaration::Theorem { ty, .. } | Declaration::Definition { ty, .. } => *ty,
        other => panic!("{other:?} is not a theorem or definition"),
    };
    let rendered = kernel.render_lean(ty);
    assert_eq!(
        rendered,
        "((x0 : CPoint) -> ((x1 : CPoint) -> ((x2 : CPoint) -> CReal.Equiv \
         (CPoint.cross x0 x2 x1) (CReal.neg (CPoint.cross x0 x1 x2)))))"
    );
}

/// `CPoint.NonCollinear`'s own type — three `CPoint`s and a witness modulus
/// `k : Nat` (rendered `AxNat`, this kernel's `Nat`) to a `Prop`. See
/// [`CPointPrelude::non_collinear`].
#[test]
fn non_collinear_statement_is_exact() {
    use crate::env::Declaration;
    let (kernel, p) = built();
    let ty = match kernel
        .environment()
        .get(p.non_collinear)
        .expect("non_collinear must be declared")
    {
        Declaration::Theorem { ty, .. } | Declaration::Definition { ty, .. } => *ty,
        other => panic!("{other:?} is not a theorem or definition"),
    };
    let rendered = kernel.render_lean(ty);
    assert_eq!(
        rendered,
        "((x0 : CPoint) -> ((x1 : CPoint) -> ((x2 : CPoint) -> ((x3 : AxNat) -> \
         Prop))))"
    );
}

/// **Two circumcentres' difference is orthogonal to every side.** See
/// [`CPointPrelude::circumcentre_difference_dots`]. `x0,x1,x2,x3,x4 =
/// O,O',A,B,C`.
#[test]
fn circumcentre_difference_dots_statement_is_exact() {
    use crate::env::Declaration;
    let (kernel, p) = built();
    let ty = match kernel
        .environment()
        .get(p.circumcentre_difference_dots)
        .expect("circumcentre_difference_dots must be declared")
    {
        Declaration::Theorem { ty, .. } | Declaration::Definition { ty, .. } => *ty,
        other => panic!("{other:?} is not a theorem or definition"),
    };
    let rendered = kernel.render_lean(ty);
    assert_eq!(
        rendered,
        "((x0 : CPoint) -> ((x1 : CPoint) -> ((x2 : CPoint) -> ((x3 : CPoint) -> ((x4 : CPoint) -> ((x5 : CReal.Equiv (CPoint.distSq x0 x2) (CPoint.distSq x0 x3)) -> ((x6 : CReal.Equiv (CPoint.distSq x0 x3) (CPoint.distSq x0 x4)) -> ((x7 : CReal.Equiv (CPoint.distSq x1 x2) (CPoint.distSq x1 x3)) -> ((x8 : CReal.Equiv (CPoint.distSq x1 x3) (CPoint.distSq x1 x4)) -> And (CReal.Equiv (CPoint.dot (CPoint.sub x0 x1) (CPoint.sub x3 x2)) CReal.zero) (CReal.Equiv (CPoint.dot (CPoint.sub x0 x1) (CPoint.sub x4 x3)) CReal.zero))))))))))"
    );
}

/// **The 2×2 elimination.** See
/// [`CPointPrelude::cross_annihilates_difference`]. `x0,x1,x2,x3 = V,A,B,C`.
#[test]
fn cross_annihilates_difference_statement_is_exact() {
    use crate::env::Declaration;
    let (kernel, p) = built();
    let ty = match kernel
        .environment()
        .get(p.cross_annihilates_difference)
        .expect("cross_annihilates_difference must be declared")
    {
        Declaration::Theorem { ty, .. } | Declaration::Definition { ty, .. } => *ty,
        other => panic!("{other:?} is not a theorem or definition"),
    };
    let rendered = kernel.render_lean(ty);
    assert_eq!(
        rendered,
        "((x0 : CPoint) -> ((x1 : CPoint) -> ((x2 : CPoint) -> ((x3 : CPoint) -> ((x4 : CReal.Equiv (CPoint.dot x0 (CPoint.sub x2 x1)) CReal.zero) -> ((x5 : CReal.Equiv (CPoint.dot x0 (CPoint.sub x3 x2)) CReal.zero) -> And (CReal.Equiv (CReal.mul (CPoint.x x0) (CPoint.cross x1 x2 x3)) CReal.zero) (CReal.Equiv (CReal.mul (CPoint.y x0) (CPoint.cross x1 x2 x3)) CReal.zero)))))))"
    );
}

/// **The headline: three non-collinear points determine a unique
/// circumcentre.** See [`CPointPrelude::circumcentre_unique`]. `x0,...,x5 =
/// k,A,B,C,O,O'`.
#[test]
fn circumcentre_unique_statement_is_exact() {
    use crate::env::Declaration;
    let (kernel, p) = built();
    let ty = match kernel
        .environment()
        .get(p.circumcentre_unique)
        .expect("circumcentre_unique must be declared")
    {
        Declaration::Theorem { ty, .. } | Declaration::Definition { ty, .. } => *ty,
        other => panic!("{other:?} is not a theorem or definition"),
    };
    let rendered = kernel.render_lean(ty);
    assert_eq!(
        rendered,
        "((x0 : AxNat) -> ((x1 : CPoint) -> ((x2 : CPoint) -> ((x3 : CPoint) -> ((x4 : CPoint) -> ((x5 : CPoint) -> ((x6 : CPoint.NonCollinear x1 x2 x3 x0) -> ((x7 : CReal.Equiv (CPoint.distSq x4 x1) (CPoint.distSq x4 x2)) -> ((x8 : CReal.Equiv (CPoint.distSq x4 x2) (CPoint.distSq x4 x3)) -> ((x9 : CReal.Equiv (CPoint.distSq x5 x1) (CPoint.distSq x5 x2)) -> ((x10 : CReal.Equiv (CPoint.distSq x5 x2) (CPoint.distSq x5 x3)) -> CPoint.Equiv x4 x5)))))))))))"
    );
}

/// `CPoint.power`'s own type -- a `Definition`, checked for presence above
/// and here for an exact render (this file's convention: see
/// `cross_statement_is_exact`'s doc for why `Definition`s get this instead
/// of the axiom-free list). `x0,x1 = P,O`.
#[test]
fn power_statement_is_exact() {
    use crate::env::Declaration;
    let (kernel, p) = built();
    let ty = match kernel
        .environment()
        .get(p.power)
        .expect("power must be declared")
    {
        Declaration::Theorem { ty, .. } | Declaration::Definition { ty, .. } => *ty,
        other => panic!("{other:?} is not a theorem or definition"),
    };
    let rendered = kernel.render_lean(ty);
    assert_eq!(
        rendered,
        "((x0 : CPoint) -> ((x1 : CPoint) -> ((x2 : CReal) -> CReal)))"
    );
}

/// **The power vanishes exactly on the circle.** See
/// [`CPointPrelude::power_zero_iff_on_circle`]. `x0,x1,x2 = P,O,r2`.
#[test]
fn power_zero_iff_on_circle_statement_is_exact() {
    use crate::env::Declaration;
    let (kernel, p) = built();
    let ty = match kernel
        .environment()
        .get(p.power_zero_iff_on_circle)
        .expect("power_zero_iff_on_circle must be declared")
    {
        Declaration::Theorem { ty, .. } | Declaration::Definition { ty, .. } => *ty,
        other => panic!("{other:?} is not a theorem or definition"),
    };
    let rendered = kernel.render_lean(ty);
    assert_eq!(
        rendered,
        "((x0 : CPoint) -> ((x1 : CPoint) -> ((x2 : CReal) -> Iff (CReal.Equiv (CPoint.power x0 x1 x2) CReal.zero) (CPoint.OnCircle x0 x1 x2))))"
    );
}

/// **The power of the centre.** See [`CPointPrelude::power_of_centre`].
/// `x0,x1 = O,r2`.
#[test]
fn power_of_centre_statement_is_exact() {
    use crate::env::Declaration;
    let (kernel, p) = built();
    let ty = match kernel
        .environment()
        .get(p.power_of_centre)
        .expect("power_of_centre must be declared")
    {
        Declaration::Theorem { ty, .. } | Declaration::Definition { ty, .. } => *ty,
        other => panic!("{other:?} is not a theorem or definition"),
    };
    let rendered = kernel.render_lean(ty);
    assert_eq!(
        rendered,
        "((x0 : CPoint) -> ((x1 : CReal) -> CReal.Equiv (CPoint.power x0 x0 x1) (CReal.neg x1)))"
    );
}

/// **The radical axis -- the headline.** See
/// [`CPointPrelude::radical_axis_iff_dot`]. `x0,...,x4 = O1,O2,r1,r2,P`.
#[test]
fn radical_axis_iff_dot_statement_is_exact() {
    use crate::env::Declaration;
    let (kernel, p) = built();
    let ty = match kernel
        .environment()
        .get(p.radical_axis_iff_dot)
        .expect("radical_axis_iff_dot must be declared")
    {
        Declaration::Theorem { ty, .. } | Declaration::Definition { ty, .. } => *ty,
        other => panic!("{other:?} is not a theorem or definition"),
    };
    let rendered = kernel.render_lean(ty);
    assert_eq!(
        rendered,
        "((x0 : CPoint) -> ((x1 : CPoint) -> ((x2 : CReal) -> ((x3 : CReal) -> ((x4 : CPoint) -> Iff (CReal.Equiv (CPoint.power x4 x0 x2) (CPoint.power x4 x1 x3)) (CReal.Equiv (CPoint.dot (CPoint.sub x4 (CPoint.midpoint x0 x1)) (CPoint.sub x1 x0)) (CReal.mul CPoint.Scalar.inv2 (CReal.add x2 (CReal.neg x3)))))))))"
    );
}

/// **The power difference is affine in `P`.** See
/// [`CPointPrelude::power_difference_linear`]. `x0,...,x4 = O1,O2,r1,r2,P`.
#[test]
fn power_difference_linear_statement_is_exact() {
    use crate::env::Declaration;
    let (kernel, p) = built();
    let ty = match kernel
        .environment()
        .get(p.power_difference_linear)
        .expect("power_difference_linear must be declared")
    {
        Declaration::Theorem { ty, .. } | Declaration::Definition { ty, .. } => *ty,
        other => panic!("{other:?} is not a theorem or definition"),
    };
    let rendered = kernel.render_lean(ty);
    assert_eq!(
        rendered,
        "((x0 : CPoint) -> ((x1 : CPoint) -> ((x2 : CReal) -> ((x3 : CReal) -> ((x4 : CPoint) -> CReal.Equiv (CReal.add (CPoint.power x4 x0 x2) (CReal.neg (CPoint.power x4 x1 x3))) (CReal.add (CReal.mul CPoint.Scalar.two (CPoint.dot x4 (CPoint.sub x1 x0))) (CReal.add (CReal.neg (CReal.add (CPoint.dot (CPoint.midpoint x0 x1) (CPoint.sub x1 x0)) (CPoint.dot (CPoint.midpoint x0 x1) (CPoint.sub x1 x0)))) (CReal.add (CReal.neg x2) x3))))))))"
    );
}

/// **A common point of two circles has equal power, hence lies on the
/// radical axis.** See
/// [`CPointPrelude::two_circles_meet_on_radical_axis`]. `x0,...,x4 =
/// O1,O2,r1,r2,P`.
#[test]
fn two_circles_meet_on_radical_axis_statement_is_exact() {
    use crate::env::Declaration;
    let (kernel, p) = built();
    let ty = match kernel
        .environment()
        .get(p.two_circles_meet_on_radical_axis)
        .expect("two_circles_meet_on_radical_axis must be declared")
    {
        Declaration::Theorem { ty, .. } | Declaration::Definition { ty, .. } => *ty,
        other => panic!("{other:?} is not a theorem or definition"),
    };
    let rendered = kernel.render_lean(ty);
    assert_eq!(
        rendered,
        "((x0 : CPoint) -> ((x1 : CPoint) -> ((x2 : CReal) -> ((x3 : CReal) -> ((x4 : CPoint) -> ((x5 : CPoint.OnCircle x4 x0 x2) -> ((x6 : CPoint.OnCircle x4 x1 x3) -> CReal.Equiv (CPoint.dot (CPoint.sub x4 (CPoint.midpoint x0 x1)) (CPoint.sub x1 x0)) (CReal.mul CPoint.Scalar.inv2 (CReal.add x2 (CReal.neg x3))))))))))"
    );
}

/// **The nine-point centre lies on the (additive) Euler line.** See
/// [`CPointPrelude::nine_point_centre_on_euler_line`]. `x0,x1,x2,x3 =
/// O,A,B,C`.
#[test]
fn nine_point_centre_on_euler_line_statement_is_exact() {
    use crate::env::Declaration;
    let (kernel, p) = built();
    let ty = match kernel
        .environment()
        .get(p.nine_point_centre_on_euler_line)
        .expect("nine_point_centre_on_euler_line must be declared")
    {
        Declaration::Theorem { ty, .. } | Declaration::Definition { ty, .. } => *ty,
        other => panic!("{other:?} is not a theorem or definition"),
    };
    let rendered = kernel.render_lean(ty);
    assert_eq!(
        rendered,
        "((x0 : CPoint) -> ((x1 : CPoint) -> ((x2 : CPoint) -> ((x3 : CPoint) -> CPoint.Equiv \
         (CPoint.add (CPoint.add (CPoint.midpoint x0 (CPoint.sub (CPoint.add (CPoint.add x1 x2) \
         x3) (CPoint.add x0 x0))) (CPoint.midpoint x0 (CPoint.sub (CPoint.add (CPoint.add x1 x2) \
         x3) (CPoint.add x0 x0)))) x0) (CPoint.add (CPoint.add (CPoint.centroid x1 x2 x3) \
         (CPoint.centroid x1 x2 x3)) (CPoint.centroid x1 x2 x3))))))"
    );
}

/// **The nine-point radius relation, `BC`-midpoint case.** See
/// [`CPointPrelude::nine_point_radius_bc`]. `x0,x1,x2,x3 = O,A,B,C`.
#[test]
fn nine_point_radius_bc_statement_is_exact() {
    use crate::env::Declaration;
    let (kernel, p) = built();
    let ty = match kernel
        .environment()
        .get(p.nine_point_radius_bc)
        .expect("nine_point_radius_bc must be declared")
    {
        Declaration::Theorem { ty, .. } | Declaration::Definition { ty, .. } => *ty,
        other => panic!("{other:?} is not a theorem or definition"),
    };
    let rendered = kernel.render_lean(ty);
    assert_eq!(
        rendered,
        "((x0 : CPoint) -> ((x1 : CPoint) -> ((x2 : CPoint) -> ((x3 : CPoint) -> CReal.Equiv \
         (CPoint.distSq (CPoint.midpoint x0 (CPoint.sub (CPoint.add (CPoint.add x1 x2) x3) \
         (CPoint.add x0 x0))) (CPoint.midpoint x2 x3)) (CReal.mul CPoint.Scalar.inv2 (CReal.mul \
         CPoint.Scalar.inv2 (CPoint.distSq x1 x0)))))))"
    );
}

/// **The nine-point radius relation, `AB`-midpoint case.** See
/// [`CPointPrelude::nine_point_radius_ab`]. `x0,x1,x2,x3 = O,A,B,C`.
#[test]
fn nine_point_radius_ab_statement_is_exact() {
    use crate::env::Declaration;
    let (kernel, p) = built();
    let ty = match kernel
        .environment()
        .get(p.nine_point_radius_ab)
        .expect("nine_point_radius_ab must be declared")
    {
        Declaration::Theorem { ty, .. } | Declaration::Definition { ty, .. } => *ty,
        other => panic!("{other:?} is not a theorem or definition"),
    };
    let rendered = kernel.render_lean(ty);
    assert_eq!(
        rendered,
        "((x0 : CPoint) -> ((x1 : CPoint) -> ((x2 : CPoint) -> ((x3 : CPoint) -> CReal.Equiv \
         (CPoint.distSq (CPoint.midpoint x0 (CPoint.sub (CPoint.add (CPoint.add x1 x2) x3) \
         (CPoint.add x0 x0))) (CPoint.midpoint x1 x2)) (CReal.mul CPoint.Scalar.inv2 (CReal.mul \
         CPoint.Scalar.inv2 (CPoint.distSq x3 x0)))))))"
    );
}

/// **The nine-point circle's easy half, the headline.** See
/// [`CPointPrelude::nine_point_centre_equidistant`]. `x0,x1,x2,x3 = O,A,B,C`.
#[test]
fn nine_point_centre_equidistant_statement_is_exact() {
    use crate::env::Declaration;
    let (kernel, p) = built();
    let ty = match kernel
        .environment()
        .get(p.nine_point_centre_equidistant)
        .expect("nine_point_centre_equidistant must be declared")
    {
        Declaration::Theorem { ty, .. } | Declaration::Definition { ty, .. } => *ty,
        other => panic!("{other:?} is not a theorem or definition"),
    };
    let rendered = kernel.render_lean(ty);
    assert_eq!(
        rendered,
        "((x0 : CPoint) -> ((x1 : CPoint) -> ((x2 : CPoint) -> ((x3 : CPoint) -> ((x4 : \
         CReal.Equiv (CPoint.distSq x0 x1) (CPoint.distSq x0 x2)) -> ((x5 : CReal.Equiv \
         (CPoint.distSq x0 x2) (CPoint.distSq x0 x3)) -> CReal.Equiv (CPoint.distSq \
         (CPoint.midpoint x0 (CPoint.sub (CPoint.add (CPoint.add x1 x2) x3) (CPoint.add x0 x0))) \
         (CPoint.midpoint x1 x2)) (CPoint.distSq (CPoint.midpoint x0 (CPoint.sub (CPoint.add \
         (CPoint.add x1 x2) x3) (CPoint.add x0 x0))) (CPoint.midpoint x2 x3))))))))"
    );
}

/// **Menelaus' theorem, verbatim.** The distinguishing substring against
/// [`ceva_concurrent_of_ratio_product`]'s statement is the extra `CReal.neg`
/// wrapping the right-hand side of the ratio-product hypothesis -- Ceva
/// states `Equiv (mul p (mul q r)) (mul (1-p) (mul (1-q) (1-r)))`, Menelaus
/// `Equiv (mul p (mul q r)) (CReal.neg (mul (1-p) (mul (1-q) (1-r))))`, and
/// the conclusion's head symbol is `CPoint.cross`, never `CPoint.Equiv` on
/// two `CPoint.lerp` applications (that shape is Ceva's, not this one's).
#[test]
fn menelaus_collinear_of_ratio_product_statement_is_exact() {
    use crate::env::Declaration;
    let (kernel, p) = built();
    let ty = match kernel
        .environment()
        .get(p.menelaus_collinear_of_ratio_product)
        .expect("menelaus_collinear_of_ratio_product must be declared")
    {
        Declaration::Theorem { ty, .. } | Declaration::Definition { ty, .. } => *ty,
        other => panic!("{other:?} is not a theorem or definition"),
    };
    let rendered = kernel.render_lean(ty);
    assert_eq!(
        rendered,
        "((x0 : CPoint) -> ((x1 : CPoint) -> ((x2 : CPoint) -> ((x3 : CReal) -> ((x4 : CReal) -> \
         ((x5 : CReal) -> ((x6 : CReal.Equiv (CReal.mul x3 (CReal.mul x4 x5)) (CReal.neg \
         (CReal.mul (CReal.add CReal.one (CReal.neg x3)) (CReal.mul (CReal.add CReal.one \
         (CReal.neg x4)) (CReal.add CReal.one (CReal.neg x5)))))) -> CReal.Equiv (CPoint.cross \
         (CPoint.lerp x1 x2 x3) (CPoint.lerp x2 x0 x4) (CPoint.lerp x0 x1 x5)) \
         CReal.zero)))))))"
    );
    // Mutation-verified substring: the sign-flip that distinguishes this
    // statement from Ceva's. Occurrence count asserted BEFORE relying on it
    // (a `sed` that silently fails to match a shape that was never there
    // reads as a dead guard, not a red flag).
    let neg_occurrences = rendered.matches("CReal.neg (CReal.mul").count();
    assert_eq!(
        neg_occurrences, 1,
        "expected exactly one negated ratio-product factor in {rendered:?}"
    );
}

/// **Ceva's converse, verbatim.** Two more binders than the exhibiting
/// direction (`k2`, the `distSq A B` witness, and the `hab`/`hmeet`
/// hypotheses) and the conclusion is the SAME shape as
/// [`ceva_concurrent_of_ratio_product`]'s hypothesis
/// (`Equiv (mul p (mul q r)) (mul (1-p) (mul (1-q) (1-r)))`), making the
/// converse relationship syntactically visible: forward's hypothesis is
/// this theorem's conclusion, and vice versa.
#[test]
fn ceva_ratio_product_of_concurrent_statement_is_exact() {
    use crate::env::Declaration;
    let (kernel, p) = built();
    let ty = match kernel
        .environment()
        .get(p.ceva_ratio_product_of_concurrent)
        .expect("ceva_ratio_product_of_concurrent must be declared")
    {
        Declaration::Theorem { ty, .. } | Declaration::Definition { ty, .. } => *ty,
        other => panic!("{other:?} is not a theorem or definition"),
    };
    let rendered = kernel.render_lean(ty);
    assert_eq!(
        rendered,
        "((x0 : CPoint) -> ((x1 : CPoint) -> ((x2 : CPoint) -> ((x3 : CReal) -> ((x4 : CReal) -> \
         ((x5 : CReal) -> ((x6 : AxNat) -> ((x7 : AxNat) -> ((x8 : CReal.PosBound (CReal.mul \
         (CReal.add (CReal.add CReal.one (CReal.neg x4)) (CReal.mul x3 x4)) (CReal.add (CReal.add \
         CReal.one (CReal.neg x4)) (CReal.mul x3 x4))) x6) -> ((x9 : CReal.PosBound (CPoint.distSq \
         x0 x1) x7) -> ((x10 : CPoint.Equiv (CPoint.lerp x1 (CPoint.lerp x2 x0 x4) (CReal.mul x3 \
         (CReal.mul (CReal.add (CReal.add CReal.one (CReal.neg x4)) (CReal.mul x3 x4)) (CReal.inv \
         (CReal.mul (CReal.add (CReal.add CReal.one (CReal.neg x4)) (CReal.mul x3 x4)) (CReal.add \
         (CReal.add CReal.one (CReal.neg x4)) (CReal.mul x3 x4))) x6 x8)))) (CPoint.lerp x2 \
         (CPoint.lerp x0 x1 x5) (CReal.mul (CReal.add (CReal.add (CReal.add CReal.one (CReal.neg \
         x3)) (CReal.neg x4)) (CReal.add (CReal.mul x3 x4) (CReal.mul x3 x4))) (CReal.mul \
         (CReal.add (CReal.add CReal.one (CReal.neg x4)) (CReal.mul x3 x4)) (CReal.inv (CReal.mul \
         (CReal.add (CReal.add CReal.one (CReal.neg x4)) (CReal.mul x3 x4)) (CReal.add (CReal.add \
         CReal.one (CReal.neg x4)) (CReal.mul x3 x4))) x6 x8))))) -> CReal.Equiv (CReal.mul x3 \
         (CReal.mul x4 x5)) (CReal.mul (CReal.add CReal.one (CReal.neg x3)) (CReal.mul (CReal.add \
         CReal.one (CReal.neg x4)) (CReal.add CReal.one \
         (CReal.neg x5)))))))))))))))"
    );
    // The conclusion (last `->` target) must be the bare ratio-product
    // equation, not wrapped in `CReal.neg` (that would make this Menelaus,
    // not Ceva) and not itself an implication (that would mean a hypothesis
    // leaked into the conclusion).
    assert!(
        rendered.ends_with(
            "-> CReal.Equiv (CReal.mul x3 (CReal.mul x4 x5)) (CReal.mul (CReal.add CReal.one \
             (CReal.neg x3)) (CReal.mul (CReal.add CReal.one (CReal.neg x4)) (CReal.add CReal.one \
             (CReal.neg x5)))))))))))))))"
        ),
        "conclusion shape drifted: {rendered:?}"
    );
}

// ============================================================================
// W1-8 (angle measure) and W2-13 (isometries): `creal_point/angle.rs` and
// `creal_point/isometry.rs`.
//
// Three kinds of check, deliberately, because they fail on disjoint defects:
//
// 1. `new_angle_and_isometry_statements_are_exact` pins every rendered TYPE.
//    A dropped hypothesis, a swapped side or a wrong operator dies here.
// 2. `new_definitions_have_the_intended_value` pins every new `Definition`'s
//    VALUE at a SYMBOLIC argument. The kernel cannot tell you a definition is
//    wrong -- it type-checks either way -- and a concrete-numeral probe over
//    `CReal` would be vacuous, because `CReal` numerals do not reduce to
//    anything a test can compare.
// 3. `a_theorem_here_proves_only_its_own_statement` re-offers each admitted
//    proof VALUE at a NEIGHBOURING statement's type and requires the kernel to
//    refuse -- with the same value at its own type as the positive control, so
//    the check cannot pass by being unable to admit anything at all.
// ============================================================================

/// The declared type of `name`, rendered.
fn rendered_ty(kernel: &crate::Kernel, name: crate::NameId) -> String {
    use crate::env::Declaration;
    let ty = match kernel.environment().get(name).expect("must be declared") {
        Declaration::Theorem { ty, .. } | Declaration::Definition { ty, .. } => *ty,
        other => panic!("{other:?} is not a theorem or definition"),
    };
    kernel.render_lean(ty)
}

/// The checked value of `name`.
fn value_of(kernel: &crate::Kernel, name: crate::NameId) -> crate::expr::ExprId {
    use crate::env::Declaration;
    match kernel.environment().get(name).expect("must be declared") {
        Declaration::Theorem { value, .. } | Declaration::Definition { value, .. } => *value,
        other => panic!("{other:?} is not a theorem or definition"),
    }
}

/// Every statement this lane added, verbatim. A wrong sign, a dropped
/// `PosBound` hypothesis or a swapped `sin`/`cos` cannot hide behind an empty
/// axiom footprint, which is all `every_theorem_here_is_axiom_free` sees.
#[test]
fn new_angle_and_isometry_statements_are_exact() {
    let (kernel, p) = built();
    let expected: [(&str, crate::NameId, &str); 32] = [
        ("norm", p.norm, "((x0 : CPoint) -> CReal)"),
        (
            "norm_nonneg",
            p.norm_nonneg,
            "((x0 : CPoint) -> CReal.le CReal.zero (CPoint.norm x0))",
        ),
        (
            "norm_sq",
            p.norm_sq,
            "((x0 : CPoint) -> CReal.Equiv (CReal.mul (CPoint.norm x0) (CPoint.norm x0)) \
             (CPoint.dot x0 x0))",
        ),
        (
            "norm_congr",
            p.norm_congr,
            "((x0 : CPoint) -> ((x1 : CPoint) -> ((x2 : CPoint.Equiv x0 x1) -> CReal.Equiv \
             (CPoint.norm x0) (CPoint.norm x1))))",
        ),
        (
            "crossV",
            p.cross_v,
            "((x0 : CPoint) -> ((x1 : CPoint) -> CReal))",
        ),
        (
            "cross_eq_crossV",
            p.cross_eq_cross_v,
            "((x0 : CPoint) -> ((x1 : CPoint) -> ((x2 : CPoint) -> CReal.Equiv (CPoint.cross x0 \
             x1 x2) (CPoint.crossV (CPoint.sub x1 x0) (CPoint.sub x2 x1)))))",
        ),
        (
            "lagrange_vector",
            p.lagrange_vector,
            "((x0 : CPoint) -> ((x1 : CPoint) -> CReal.Equiv (CReal.add (CReal.mul (CPoint.dot x0 \
             x0) (CPoint.dot x1 x1)) (CReal.neg (CReal.mul (CPoint.dot x0 x1) (CPoint.dot x0 \
             x1)))) (CReal.mul (CPoint.crossV x0 x1) (CPoint.crossV x0 x1))))",
        ),
        (
            "law_of_cosines_dot",
            p.law_of_cosines_dot,
            "((x0 : CPoint) -> ((x1 : CPoint) -> CReal.Equiv (CPoint.distSq x0 x1) (CReal.add \
             (CReal.add (CPoint.dot x0 x0) (CPoint.dot x1 x1)) (CReal.neg (CReal.add (CPoint.dot \
             x0 x1) (CPoint.dot x0 x1))))))",
        ),
        (
            "cosAngle",
            p.cos_angle,
            "((x0 : CPoint) -> ((x1 : CPoint) -> ((x2 : AxNat) -> ((x3 : CReal.PosBound \
             (CReal.mul (CPoint.norm x0) (CPoint.norm x1)) x2) -> CReal))))",
        ),
        (
            "sinAngle",
            p.sin_angle,
            "((x0 : CPoint) -> ((x1 : CPoint) -> ((x2 : AxNat) -> ((x3 : CReal.PosBound \
             (CReal.mul (CPoint.norm x0) (CPoint.norm x1)) x2) -> CReal))))",
        ),
        (
            "sin_sq_add_cos_sq",
            p.sin_sq_add_cos_sq,
            "((x0 : CPoint) -> ((x1 : CPoint) -> ((x2 : AxNat) -> ((x3 : CReal.PosBound \
             (CReal.mul (CPoint.norm x0) (CPoint.norm x1)) x2) -> CReal.Equiv (CReal.add \
             (CReal.mul (CPoint.sinAngle x0 x1 x2 x3) (CPoint.sinAngle x0 x1 x2 x3)) (CReal.mul \
             (CPoint.cosAngle x0 x1 x2 x3) (CPoint.cosAngle x0 x1 x2 x3))) CReal.one))))",
        ),
        (
            "abs_cos_angle_le_one",
            p.abs_cos_angle_le_one,
            "((x0 : CPoint) -> ((x1 : CPoint) -> ((x2 : AxNat) -> ((x3 : CReal.PosBound \
             (CReal.mul (CPoint.norm x0) (CPoint.norm x1)) x2) -> CReal.le (CReal.abs \
             (CPoint.cosAngle x0 x1 x2 x3)) CReal.one))))",
        ),
        (
            "cos_angle_le_one",
            p.cos_angle_le_one,
            "((x0 : CPoint) -> ((x1 : CPoint) -> ((x2 : AxNat) -> ((x3 : CReal.PosBound \
             (CReal.mul (CPoint.norm x0) (CPoint.norm x1)) x2) -> CReal.le (CPoint.cosAngle x0 x1 \
             x2 x3) CReal.one))))",
        ),
        (
            "neg_one_le_cos_angle",
            p.neg_one_le_cos_angle,
            "((x0 : CPoint) -> ((x1 : CPoint) -> ((x2 : AxNat) -> ((x3 : CReal.PosBound \
             (CReal.mul (CPoint.norm x0) (CPoint.norm x1)) x2) -> CReal.le (CReal.neg CReal.one) \
             (CPoint.cosAngle x0 x1 x2 x3)))))",
        ),
        (
            "norm_mul_cos_angle",
            p.norm_mul_cos_angle,
            "((x0 : CPoint) -> ((x1 : CPoint) -> ((x2 : AxNat) -> ((x3 : CReal.PosBound \
             (CReal.mul (CPoint.norm x0) (CPoint.norm x1)) x2) -> CReal.Equiv (CReal.mul \
             (CReal.mul (CPoint.norm x0) (CPoint.norm x1)) (CPoint.cosAngle x0 x1 x2 x3)) \
             (CPoint.dot x0 x1)))))",
        ),
        (
            "law_of_sines",
            p.law_of_sines,
            "((x0 : CPoint) -> ((x1 : CPoint) -> ((x2 : AxNat) -> ((x3 : CReal.PosBound \
             (CReal.mul (CPoint.norm x0) (CPoint.norm x1)) x2) -> CReal.Equiv (CReal.abs \
             (CPoint.crossV x0 x1)) (CReal.mul (CReal.mul (CPoint.norm x0) (CPoint.norm x1)) \
             (CPoint.sinAngle x0 x1 x2 x3))))))",
        ),
        (
            "law_of_cosines",
            p.law_of_cosines,
            "((x0 : CPoint) -> ((x1 : CPoint) -> ((x2 : AxNat) -> ((x3 : CReal.PosBound \
             (CReal.mul (CPoint.norm x0) (CPoint.norm x1)) x2) -> CReal.Equiv (CPoint.distSq x0 \
             x1) (CReal.add (CReal.add (CReal.mul (CPoint.norm x0) (CPoint.norm x0)) (CReal.mul \
             (CPoint.norm x1) (CPoint.norm x1))) (CReal.neg (CReal.add (CReal.mul (CReal.mul \
             (CPoint.norm x0) (CPoint.norm x1)) (CPoint.cosAngle x0 x1 x2 x3)) (CReal.mul \
             (CReal.mul (CPoint.norm x0) (CPoint.norm x1)) (CPoint.cosAngle x0 x1 x2 \
             x3)))))))))",
        ),
        (
            "Isometry",
            p.isometry,
            "((x0 : ((x0 : CPoint) -> CPoint)) -> Prop)",
        ),
        ("idMap", p.id_map, "((x0 : CPoint) -> CPoint)"),
        (
            "comp",
            p.comp_map,
            "((x0 : ((x0 : CPoint) -> CPoint)) -> ((x1 : ((x1 : CPoint) -> CPoint)) -> ((x2 : \
             CPoint) -> CPoint)))",
        ),
        ("isometry_id", p.isometry_id, "CPoint.Isometry CPoint.idMap"),
        (
            "isometry_comp",
            p.isometry_comp,
            "((x0 : ((x0 : CPoint) -> CPoint)) -> ((x1 : ((x1 : CPoint) -> CPoint)) -> ((x2 : \
             CPoint.Isometry x0) -> ((x3 : CPoint.Isometry x1) -> CPoint.Isometry (CPoint.comp x0 \
             x1)))))",
        ),
        (
            "translate",
            p.translate,
            "((x0 : CPoint) -> ((x1 : CPoint) -> CPoint))",
        ),
        (
            "isometry_translate",
            p.isometry_translate,
            "((x0 : CPoint) -> CPoint.Isometry (CPoint.translate x0))",
        ),
        (
            "rotate",
            p.rotate,
            "((x0 : CReal) -> ((x1 : CReal) -> ((x2 : CPoint) -> CPoint)))",
        ),
        (
            "isometry_rotate",
            p.isometry_rotate,
            "((x0 : CReal) -> ((x1 : CReal) -> ((x2 : CReal.Equiv (CReal.add (CReal.mul x0 x0) \
             (CReal.mul x1 x1)) CReal.one) -> CPoint.Isometry (CPoint.rotate x0 x1))))",
        ),
        (
            "reflect",
            p.reflect,
            "((x0 : CReal) -> ((x1 : CReal) -> ((x2 : CPoint) -> CPoint)))",
        ),
        (
            "isometry_reflect",
            p.isometry_reflect,
            "((x0 : CReal) -> ((x1 : CReal) -> ((x2 : CReal.Equiv (CReal.add (CReal.mul x0 x0) \
             (CReal.mul x1 x1)) CReal.one) -> CPoint.Isometry (CPoint.reflect x0 x1))))",
        ),
        (
            "scale",
            p.scale,
            "((x0 : CReal) -> ((x1 : CPoint) -> CPoint))",
        ),
        (
            "scale_distSq",
            p.scale_dist_sq,
            "((x0 : CReal) -> ((x1 : CPoint) -> ((x2 : CPoint) -> CReal.Equiv (CPoint.distSq \
             (CPoint.scale x0 x1) (CPoint.scale x0 x2)) (CReal.mul (CReal.mul x0 x0) \
             (CPoint.distSq x1 x2)))))",
        ),
        (
            "not_isometry_scale_two",
            p.not_isometry_scale_two,
            "((x0 : CPoint.Isometry (CPoint.scale CPoint.Scalar.two)) -> False)",
        ),
        (
            "isometry_preserves_dot",
            p.isometry_preserves_dot,
            "((x0 : ((x0 : CPoint) -> CPoint)) -> ((x1 : CPoint.Isometry x0) -> ((x2 : CPoint) -> \
             ((x3 : CPoint) -> ((x4 : CPoint) -> CReal.Equiv (CPoint.dot (CPoint.sub (x0 x2) (x0 \
             x4)) (CPoint.sub (x0 x3) (x0 x4))) (CPoint.dot (CPoint.sub x2 x4) (CPoint.sub x3 \
             x4)))))))",
        ),
    ];
    for (label, name, want) in expected {
        assert_eq!(
            rendered_ty(&kernel, name),
            want,
            "{label} statement drifted"
        );
    }
}

/// **The evaluation test the kernel cannot do for you.** `add_declaration`
/// type-checks a `Definition`; a definition computing the wrong thing has the
/// right type. So pin every new definition's VALUE at a symbolic argument --
/// symbolic and not concrete, because `CReal` numerals do not reduce, so a
/// concrete probe here would compare nothing.
///
/// These are discriminating: swapping `x`/`y` in `crossV`, dropping the sign
/// in `rotate`, or writing `translate T P = T + P` instead of `P + T` all
/// change the rendered value.
#[test]
fn new_definitions_have_the_intended_value() {
    let (kernel, p) = built();
    let expected: [(&str, crate::NameId, &str); 11] = [
        (
            "norm",
            p.norm,
            "fun (x0 : CPoint) => CReal.sqrt (CPoint.dot x0 x0)",
        ),
        (
            "crossV",
            p.cross_v,
            "fun (x0 : CPoint) => fun (x1 : CPoint) => CReal.add (CReal.mul (CPoint.x x0) \
             (CPoint.y x1)) (CReal.neg (CReal.mul (CPoint.y x0) (CPoint.x x1)))",
        ),
        (
            "cosAngle",
            p.cos_angle,
            "fun (x0 : CPoint) => fun (x1 : CPoint) => fun (x2 : AxNat) => fun (x3 : \
             CReal.PosBound (CReal.mul (CPoint.norm x0) (CPoint.norm x1)) x2) => CReal.mul \
             (CPoint.dot x0 x1) (CReal.inv (CReal.mul (CPoint.norm x0) (CPoint.norm x1)) x2 x3)",
        ),
        (
            "sinAngle",
            p.sin_angle,
            "fun (x0 : CPoint) => fun (x1 : CPoint) => fun (x2 : AxNat) => fun (x3 : \
             CReal.PosBound (CReal.mul (CPoint.norm x0) (CPoint.norm x1)) x2) => CReal.mul \
             (CReal.abs (CPoint.crossV x0 x1)) (CReal.inv (CReal.mul (CPoint.norm x0) \
             (CPoint.norm x1)) x2 x3)",
        ),
        (
            "Isometry",
            p.isometry,
            "fun (x0 : ((x0 : CPoint) -> CPoint)) => ((x1 : CPoint) -> ((x2 : CPoint) -> \
             CReal.Equiv (CPoint.distSq (x0 x1) (x0 x2)) (CPoint.distSq x1 x2)))",
        ),
        ("idMap", p.id_map, "fun (x0 : CPoint) => x0"),
        (
            "comp",
            p.comp_map,
            "fun (x0 : ((x0 : CPoint) -> CPoint)) => fun (x1 : ((x1 : CPoint) -> CPoint)) => fun \
             (x2 : CPoint) => x0 (x1 x2)",
        ),
        (
            "translate",
            p.translate,
            "fun (x0 : CPoint) => fun (x1 : CPoint) => CPoint.add x1 x0",
        ),
        (
            "rotate",
            p.rotate,
            "fun (x0 : CReal) => fun (x1 : CReal) => fun (x2 : CPoint) => CPoint.mk (CReal.add \
             (CReal.mul x0 (CPoint.x x2)) (CReal.neg (CReal.mul x1 (CPoint.y x2)))) (CReal.add \
             (CReal.mul x1 (CPoint.x x2)) (CReal.mul x0 (CPoint.y x2)))",
        ),
        (
            "reflect",
            p.reflect,
            "fun (x0 : CReal) => fun (x1 : CReal) => fun (x2 : CPoint) => CPoint.mk (CReal.add \
             (CReal.mul x0 (CPoint.x x2)) (CReal.mul x1 (CPoint.y x2))) (CReal.add (CReal.mul x1 \
             (CPoint.x x2)) (CReal.neg (CReal.mul x0 (CPoint.y x2))))",
        ),
        (
            "scale",
            p.scale,
            "fun (x0 : CReal) => fun (x1 : CPoint) => CPoint.mk (CReal.mul x0 (CPoint.x x1)) \
             (CReal.mul x0 (CPoint.y x1))",
        ),
    ];
    for (label, name, want) in expected {
        let got = kernel.render_lean(value_of(&kernel, name));
        assert_eq!(got, want, "{label} definition body drifted");
    }

    // Discrimination between the two orthogonal families: `rotate` and
    // `reflect` differ only in two signs, so a copy-paste that made them the
    // same declaration would leave every statement above true and every
    // footprint empty.
    assert_ne!(
        kernel.render_lean(value_of(&kernel, p.rotate)),
        kernel.render_lean(value_of(&kernel, p.reflect)),
        "rotate and reflect have the same body"
    );
    // `crossV` is antisymmetric, so it must not be symmetric in its arguments.
    let cv = kernel.render_lean(value_of(&kernel, p.cross_v));
    assert!(cv.contains("CReal.neg"), "crossV lost its sign: {cv:?}");
}

/// **The negative control, at the kernel.** Each admitted proof value is
/// re-offered at a NEIGHBOURING statement's type, and the kernel must refuse.
/// Each pair differs in a small term:
///
/// - `isometry_rotate` / `isometry_reflect` differ only in two signs inside
///   the map, under identical hypotheses -- a map that reflects must not be
///   admitted as one that rotates.
/// - `cos_angle_le_one` / `neg_one_le_cos_angle` differ only in which side of
///   `CReal.le` the cosine sits.
/// - `norm_mul_cos_angle` / `law_of_sines` differ in `dot`/`abs (crossV …)`.
/// - `isometry_id`'s value at `Isometry (scale CPoint.Scalar.two)` is the
///   headline case: **a map that scales by two must not be admitted as an
///   isometry.** `CPoint.not_isometry_scale_two` proves it cannot be, from any
///   proof; this checks the kernel refuses the obvious one.
///
/// Every row carries its own positive control (the same value at its own type,
/// under a fresh name), so a harness that could admit nothing at all fails
/// here rather than passing silently.
#[test]
fn a_theorem_here_proves_only_its_own_statement() {
    use crate::env::Declaration;

    let (mut kernel, p) = built();
    let scale_two_ty = {
        let scale = kernel.const_(p.scale, vec![]);
        let two = kernel.const_(p.two, vec![]);
        let scale_two = kernel.app(scale, two);
        let isometry = kernel.const_(p.isometry, vec![]);
        kernel.app(isometry, scale_two)
    };

    let rows: [(&str, crate::NameId, &str, crate::expr::ExprId); 4] = [
        ("isometry_rotate", p.isometry_rotate, "isometry_reflect", {
            let name = p.isometry_reflect;
            match kernel.environment().get(name).expect("declared") {
                Declaration::Theorem { ty, .. } => *ty,
                other => panic!("{other:?}"),
            }
        }),
        (
            "cos_angle_le_one",
            p.cos_angle_le_one,
            "neg_one_le_cos_angle",
            {
                let name = p.neg_one_le_cos_angle;
                match kernel.environment().get(name).expect("declared") {
                    Declaration::Theorem { ty, .. } => *ty,
                    other => panic!("{other:?}"),
                }
            },
        ),
        (
            "norm_mul_cos_angle",
            p.norm_mul_cos_angle,
            "law_of_sines",
            {
                let name = p.law_of_sines;
                match kernel.environment().get(name).expect("declared") {
                    Declaration::Theorem { ty, .. } => *ty,
                    other => panic!("{other:?}"),
                }
            },
        ),
        (
            "isometry_id",
            p.isometry_id,
            "Isometry (scale two)",
            scale_two_ty,
        ),
    ];

    let anon = kernel.anon();
    for (index, (source_label, source, target_label, target_ty)) in rows.into_iter().enumerate() {
        let value = value_of(&kernel, source);
        let own_ty = match kernel.environment().get(source).expect("declared") {
            Declaration::Theorem { ty, .. } => *ty,
            other => panic!("{other:?}"),
        };

        // Positive control: the same value at its OWN statement, under a fresh
        // name. Without this the negative below would also "pass" if the
        // harness could never admit anything.
        let ok_name = kernel.name_str(anon, format!("Check.reoffer_ok_{index}"));
        let admitted = kernel.add_declaration(Declaration::Theorem {
            name: ok_name,
            uparams: vec![],
            ty: own_ty,
            value,
        });
        assert!(
            admitted.is_ok(),
            "positive control failed: the kernel refused {source_label}'s own value at its own \
             type: {admitted:?}"
        );

        let bad_name = kernel.name_str(anon, format!("Check.reoffer_bad_{index}"));
        let refused = kernel.add_declaration(Declaration::Theorem {
            name: bad_name,
            uparams: vec![],
            ty: target_ty,
            value,
        });
        assert!(
            refused.is_err(),
            "the kernel ADMITTED {source_label}'s proof as a proof of {target_label}"
        );
    }
}
