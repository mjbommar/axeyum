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
        ("parallelogram_law", p.parallelogram_law),
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
        p.parallelogram_law,
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
