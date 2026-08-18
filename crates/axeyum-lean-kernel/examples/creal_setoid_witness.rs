//! **ℝ, constructed, at trusted cost zero** — the finding, with the exit status
//! depending on it (ADR-0468 phase R1).
//!
//! [`creal_shape_probe`](creal_shape_probe.rs) answered the *expressibility*
//! question before `ℚ` had an order, by admitting the carrier parametrically in
//! its regularity predicate. This is the same measurement on the real thing:
//! `CReal` over the constructed `Rat`, with regularity and closeness as
//! definitions, and with the three setoid laws — reflexivity, symmetry and
//! **transitivity** — proved.
//!
//! ```sh
//! cargo run -q -p axeyum-lean-kernel --example creal_setoid_witness
//! ```
//!
//! # What the exit status depends on
//!
//! Four things, and the last two are what stop this being a green light on a
//! vacuous claim:
//!
//! 1. every declaration is a **checked** `Definition`/`Theorem` — never an
//!    `Axiom`, never an `Opaque`;
//! 2. every one has an **empty** `Kernel::axiom_footprint`, and the whole
//!    environment's trusted surface (`Axiom` + `Opaque` + `Quotient`) is still
//!    empty afterwards;
//! 3. `CReal.ofRat` is present, so `CReal.Regular` has a **solution** and the
//!    carrier is inhabited. Without it, `refl`/`symm`/`trans` could all hold
//!    for the empty type with empty footprints; and
//! 4. `CReal.Equiv.not_zero_one` is present, so `CReal.Equiv` is **not** the
//!    total relation. An equivalence relation that relates everything is still
//!    an equivalence relation.
//!
//! # What this does NOT claim
//!
//! `Eq CReal` is not the equality of real numbers — `CReal.Equiv` is, and every
//! statement about reals will say so. The ordered-field structure over `Equiv`
//! (ADR-0468 phase R2) is not built here; nor is completeness, division, or
//! `√`, each of which is a separate ADR. And the `Real` package's 30 axioms are
//! **unchanged** by this: ADR-0468 retires them by *deletion* in phase R3, once
//! consumers are generalized, not by exhibiting a model.

#![allow(clippy::too_many_lines)]

use axeyum_lean_kernel::{Declaration, Kernel, build_creal_prelude};

fn main() {
    let mut kernel = Kernel::new();
    let p = build_creal_prelude(&mut kernel).expect("the CReal development must build");

    let admitted = [
        ("CReal.Within", p.within),
        ("CReal.Regular", p.regular_pred),
        ("CReal", p.creal),
        ("CReal.mk", p.mk),
        ("CReal.rec", p.rec),
        ("CReal.seq", p.seq),
        ("CReal.regular", p.regular),
        ("CReal.Equiv", p.equiv),
        ("CReal.Equiv.refl", p.equiv_refl),
        ("CReal.Equiv.symm", p.equiv_symm),
        ("CReal.Equiv.trans", p.equiv_trans),
        ("CReal.ofRat", p.of_rat),
        ("CReal.Equiv.not_zero_one", p.not_zero_one),
    ];

    let mut failed = false;
    println!("declaration\tkind\tfootprint");
    for (label, name) in admitted {
        let Some(declaration) = kernel.environment().get(name) else {
            println!("{label}\tMISSING\t-");
            failed = true;
            continue;
        };
        let kind = match declaration {
            Declaration::Theorem { .. } => "theorem",
            Declaration::Definition { .. } => "definition",
            Declaration::Inductive { .. } => "inductive",
            Declaration::Constructor { .. } => "constructor",
            Declaration::Recursor { .. } => "recursor",
            Declaration::Axiom { .. } => "AXIOM",
            Declaration::Opaque { .. } => "OPAQUE",
            Declaration::Quotient { .. } => "QUOTIENT",
        };
        if matches!(
            declaration,
            Declaration::Axiom { .. } | Declaration::Opaque { .. } | Declaration::Quotient { .. }
        ) {
            failed = true;
        }
        let footprint: Vec<String> = kernel
            .axiom_footprint(name)
            .into_iter()
            .map(|entry| kernel.display_name(entry).to_string())
            .collect();
        if !footprint.is_empty() {
            failed = true;
        }
        println!(
            "{label}\t{kind}\t{}",
            if footprint.is_empty() {
                "-".to_owned()
            } else {
                footprint.join(",")
            }
        );
    }

    // (3) and (4): the two claims that stop this being vacuous.
    let inhabited = matches!(
        kernel.environment().get(p.of_rat),
        Some(Declaration::Definition { .. })
    );
    let discriminating = matches!(
        kernel.environment().get(p.not_zero_one),
        Some(Declaration::Theorem { .. })
    );
    if !inhabited {
        eprintln!(
            "FAIL: CReal.ofRat is not a checked definition, so CReal.Regular has no \
             exhibited solution. The carrier may be EMPTY and every setoid law above \
             vacuous — with empty footprints throughout."
        );
        failed = true;
    }
    if !discriminating {
        eprintln!(
            "FAIL: CReal.Equiv.not_zero_one is not a checked theorem, so nothing says \
             CReal.Equiv separates any two reals. The total relation is an equivalence \
             relation too."
        );
        failed = true;
    }

    let trusted: Vec<String> = kernel
        .environment()
        .iter()
        .filter_map(|(_, declaration)| match declaration {
            Declaration::Axiom { name, .. }
            | Declaration::Opaque { name, .. }
            | Declaration::Quotient { name, .. } => Some(kernel.display_name(*name).to_string()),
            _ => None,
        })
        .collect();
    if !trusted.is_empty() {
        failed = true;
    }

    eprintln!(
        "ℝ as a Bishop setoid over the constructed ℚ: {} declarations admitted, \
         trusted surface = {} ({}); carrier inhabited = {inhabited}, \
         Equiv discriminates = {discriminating}",
        admitted.len(),
        trusted.len(),
        if trusted.is_empty() {
            "empty".to_owned()
        } else {
            trusted.join(",")
        }
    );
    if failed {
        eprintln!(
            "FAIL: the constructed reals are NOT free, or not inhabited, or not \
             discriminating — see above. ADR-0468's cost claim does not hold as stated."
        );
        std::process::exit(1);
    }
    eprintln!(
        "reflexivity, symmetry and transitivity of CReal.Equiv all hold at ZERO \
         trusted declarations; transitivity is the only consumer of \
         Rat.le_of_le_add_natDivSucc (the Archimedean property of ℚ)"
    );
}
