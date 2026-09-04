//! Print — and **check** — the characterization status of the constructed `Nat`
//! and `Int`.
//!
//! `nat_axiom_inventory` answers "how many trusted declarations does the `Nat`
//! development have" (zero) and stops there. That number does not say the
//! object is *the* natural numbers: an inductive type named `Nat` with a subtly
//! wrong `lt` would report the same zero, typecheck the same modules, and be
//! worthless. This example answers the next question — is there a machine-checked
//! statement pinning the object?
//!
//! Each row is one admitted characterization theorem: what it contributes, its
//! `Kernel::axiom_footprint` (empty is the claim), and its statement as the
//! kernel holds it. The statements are printed, not paraphrased, because the
//! whole point is that a claim about what was proved should be readable off the
//! environment rather than off a comment.
//!
//! # Printing a number is not asserting it
//!
//! This example is a checker, with no flag to turn that off. It exits non-zero
//! when any of the following fails, so a regression cannot pass as a tidy
//! report:
//!
//! * every entry is a `Declaration::Theorem` (not an axiom, not missing);
//! * every entry has an **empty** axiom footprint;
//! * the entry population matches the declared one;
//! * every injected [`Weakening`] is **refused by the kernel, at the
//!   declaration it was aimed at** — a characterization whose hypotheses are
//!   not load-bearing is a characterization of nothing.
//!
//! ```sh
//! cargo run --release -q -p axeyum-lean-kernel --example characterization_status
//! ```

use std::process::ExitCode;

use axeyum_lean_kernel::{
    Declaration, Kernel, Weakening, build_characterization, build_characterization_with,
};

/// The number of characterization theorems this example expects to find.
/// Asserted, not printed: a package that silently lost a theorem must fail.
const EXPECTED_ENTRIES: usize = 34;

#[allow(clippy::too_many_lines)]
fn main() -> ExitCode {
    let mut kernel = Kernel::new();
    let package = match build_characterization(&mut kernel) {
        Ok(package) => package,
        Err(error) => {
            eprintln!("FAIL: the kernel refused a characterization proof: {error:?}");
            return ExitCode::from(1);
        }
    };

    let mut failures: Vec<String> = Vec::new();

    println!("kind\tname\tfootprint\tstatement");
    for entry in &package.entries {
        let name = kernel.display_name(entry.name).to_string();
        let declaration = kernel.environment().get(entry.name);
        let statement = match declaration {
            Some(Declaration::Theorem { ty, .. }) => kernel.render_lean(*ty).replace('\n', " "),
            Some(other) => {
                failures.push(format!("{name} is not a checked theorem: {other:?}"));
                "<not a theorem>".to_string()
            }
            None => {
                failures.push(format!("{name} is not in the environment"));
                "<absent>".to_string()
            }
        };
        let footprint: Vec<String> = kernel
            .axiom_footprint(entry.name)
            .into_iter()
            .map(|a| kernel.display_name(a).to_string())
            .collect();
        if !footprint.is_empty() {
            failures.push(format!("{name} rests on {footprint:?}"));
        }
        let rendered = if footprint.is_empty() {
            "[]".to_string()
        } else {
            footprint.join(",")
        };
        println!("{}\t{name}\t{rendered}\t{statement}", entry.kind.label());
    }

    if package.entries.len() != EXPECTED_ENTRIES {
        failures.push(format!(
            "expected {EXPECTED_ENTRIES} characterization theorems, found {}",
            package.entries.len()
        ));
    }

    // The negative controls, run here rather than only in `cargo test`: this
    // example is what a referee runs, and "the theorems are admitted" is not
    // the claim — "the hypotheses are load-bearing" is half of it.
    let defects = Weakening::defects();
    let mut refused = 0usize;
    for &defect in defects {
        let mut probe = Kernel::new();
        let outcome = build_characterization_with(&mut probe, defect);
        let target = defect.refused_declaration().unwrap_or("<unnamed>");
        if outcome.is_ok() {
            failures.push(format!(
                "negative control {defect:?} was ACCEPTED; {target} does not depend on it"
            ));
        } else {
            let declared = |dotted: &str| {
                probe
                    .environment()
                    .iter()
                    .any(|(name, _)| probe.display_name(*name).to_string() == dotted)
            };
            if declared(target) {
                failures.push(format!(
                    "negative control {defect:?} failed, but {target} was still admitted"
                ));
            } else if defect.reached_declaration().is_some_and(|r| !declared(r)) {
                // The build died before the declaration the defect was aimed at,
                // so its absence proves nothing about that hypothesis.
                failures.push(format!(
                    "negative control {defect:?} failed BEFORE reaching {target}: {} is absent",
                    defect.reached_declaration().unwrap_or("<unnamed>")
                ));
            } else {
                refused += 1;
            }
        }
    }

    eprintln!(
        "Nat: 3 Peano axioms + the universal property + categoricity (universe-polymorphic); \
         Int: no-junk + generation by 1 + discreteness + total order + BOTH halves of the \
         universal property + categoricity (universe-polymorphic), instantiated at Int itself"
    );
    eprintln!(
        "{}/{} theorems admitted with an EMPTY axiom footprint; {refused}/{} injected defects \
         refused by the kernel at the declaration they were aimed at",
        package.entries.len(),
        EXPECTED_ENTRIES,
        defects.len()
    );
    eprintln!(
        "NOT proved: that an inverse FUNCTION can be extracted. Both categoricity theorems \
         prove the comparison map injective and surjective, and surjectivity is a Prop-level \
         exists -- a Prop-valued generation principle on the target cannot define a map back. \
         Int.Characterization.iso is the stronger, constructed form, and it HYPOTHESISES the \
         back-map: given any structure-preserving psi it proves both composites are the \
         identity."
    );

    if failures.is_empty() {
        ExitCode::SUCCESS
    } else {
        for failure in &failures {
            eprintln!("FAIL: {failure}");
        }
        ExitCode::from(1)
    }
}
