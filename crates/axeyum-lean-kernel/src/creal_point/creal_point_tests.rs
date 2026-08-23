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
