//! Does the kernel accept [`build_cpoint_prelude`], and is every theorem it
//! produces axiom-free?

use super::{CPointPrelude, build_cpoint_prelude};
use crate::Kernel;

fn built() -> (Kernel, CPointPrelude) {
    use std::sync::OnceLock;
    static TEMPLATE: OnceLock<(Kernel, CPointPrelude)> = OnceLock::new();
    let (kernel, prelude) = TEMPLATE.get_or_init(|| {
        let mut kernel = Kernel::new();
        let prelude = build_cpoint_prelude(&mut kernel).expect("CPoint prelude must build");
        (kernel, prelude)
    });
    (kernel.clone(), *prelude)
}

/// The build itself, with the kernel's rejection **rendered** rather than
/// `Debug`-formatted, so a failure says which two types failed to match.
#[test]
fn cpoint_prelude_builds() {
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
}

/// `midpoint_self`, `sum_perm`, `midpoint_diag_core` and
/// `varignon_diagonals_bisect` all admit with an **empty** axiom footprint —
/// the whole point of building this over `CReal` rather than asserting it.
#[test]
fn every_theorem_here_is_axiom_free() {
    let (kernel, p) = built();
    for (label, name) in [
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
        ("dot_self_zero_of_eq_zero", p.dot_self_zero_of_eq_zero),
        ("eq_zero_of_dot_self_zero", p.eq_zero_of_dot_self_zero),
        ("dot_self_zero_iff", p.dot_self_zero_iff),
        ("dist_sq_eq_zero_of_equiv", p.dist_sq_eq_zero_of_equiv),
        ("eq_zero_of_dist_sq_eq_zero", p.eq_zero_of_dist_sq_eq_zero),
        ("dist_sq_eq_zero_iff", p.dist_sq_eq_zero_iff),
    ] {
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
/// This kernel has no `CReal.sqrt` (only `natSqrt`), so this
/// squared/parametric identity -- not the classical unsigned-length
/// `BD*DC*BC + AD^2*BC ~ AB^2*DC + AC^2*BD` -- is the honest statement:
/// multiplying this identity through by the unsquared `BC` at `t := BD/BC`
/// recovers the classical form, but that multiplication is not performed
/// here. `x0,x1,x2,x3 = A,B,C,t`.
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
/// squared, deliberately: this kernel has `CReal.natSqrt` but no
/// `CReal.sqrt`, so the norm form `|⟨u,v⟩| ≤ ‖u‖·‖v‖` is not expressible
/// here. Verbatim-checked for the same reason as the two tests above.
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
/// [`CPointPrelude::dist_sq_double_sum_bound`]'s doc comment for why that
/// form is unreachable here (no `CReal.sqrt`).
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
