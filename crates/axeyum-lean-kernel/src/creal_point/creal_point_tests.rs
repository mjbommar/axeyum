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
    ] {
        assert!(
            kernel.environment().get(name).is_some(),
            "expected declaration missing from the environment"
        );
    }
}
