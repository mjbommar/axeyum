//! The ordered-ring interface, pinned as a **30-binder telescope** rather than
//! as 30 axioms — and the measurement that says the two say the same thing.
//!
//! ## Why
//!
//! `real: axiom=30` is this repository's entire remaining trusted surface, and
//! [ADR-0480](../../../docs/research/09-decisions/adr-0480-the-trusted-surface-is-measured-as-reached-not-only-declared.md)
//! records why the package is retained anyway: it is the *specification* — 30
//! kernel-checked declarations whose canonical types the axiom ledger pins by
//! SHA-256 — and the *negative control* for every axiom-freedom measurement
//! here.
//!
//! The first of those two reasons is dischargeable, and this example is the
//! discharge. `generalize_over_ordered_ring` already produces a theorem whose
//! type opens into 30 `∀`-binders carrying exactly those 30 statements; its
//! prefix is a function of the signature's declaration *types* alone, so
//! [`ring_interface_telescope`](axeyum_solver::ring_interface_telescope)
//! computes it without a refutation. Read off the **axiom-free** `Int`
//! development, that telescope is the interface stated in the kernel while
//! assuming nothing.
//!
//! It is only a discharge if the two telescopes are the *same statements*. That
//! is a measurement, and it is this example's exit status:
//!
//! ```sh
//! cargo run --release -q -p axeyum-solver --features full \
//!     --example ring_interface_pin -- --require-identical
//! ```
//!
//! Without the flag the rows are emitted as
//! `source<TAB>binder<TAB>declaration<TAB>canonical-type-utf8-as-hex`, the same
//! shape `prelude_axiom_inventory` emits, so the ledger can digest them by the
//! same rule.
//!
//! ## What a disagreement would mean
//!
//! Not a bug in this example: a genuine divergence between what the `Real`
//! package assumes and what the `Int` development proves. The two are supposed
//! to be the same interface — `build_int_model_of_arith` reports
//! `identical: true` for all 22 laws — so a differing row is the honest report
//! that the axiom-free telescope is *not* the same specification, and pinning
//! the ledger onto it would be a silent weakening.

use std::process::ExitCode;

use axeyum_lean_kernel::{Kernel, build_arith_prelude, build_int_prelude};
use axeyum_solver::{RingInterfaceBinder, RingSignature, ring_interface_telescope};

fn hex(bytes: &[u8]) -> String {
    const DIGITS: &[u8; 16] = b"0123456789abcdef";
    let mut output = String::with_capacity(bytes.len() * 2);
    for &byte in bytes {
        output.push(char::from(DIGITS[usize::from(byte >> 4)]));
        output.push(char::from(DIGITS[usize::from(byte & 0x0f)]));
    }
    output
}

/// The telescope over the axiomatized `Real` package.
fn real_telescope() -> Result<Vec<RingInterfaceBinder>, String> {
    let mut kernel = Kernel::new();
    let arith = build_arith_prelude(&mut kernel).map_err(|e| format!("Real prelude: {e:?}"))?;
    ring_interface_telescope(&mut kernel, &RingSignature::from(arith))
        .map_err(|e| format!("Real telescope: {e:?}"))
}

/// The telescope over the constructed, axiom-free `Int` development.
fn int_telescope() -> Result<Vec<RingInterfaceBinder>, String> {
    let mut kernel = Kernel::new();
    let int = build_int_prelude(&mut kernel).map_err(|e| format!("Int prelude: {e:?}"))?;
    ring_interface_telescope(&mut kernel, &RingSignature::from(int))
        .map_err(|e| format!("Int telescope: {e:?}"))
}

fn main() -> ExitCode {
    match run() {
        Ok(()) => ExitCode::SUCCESS,
        Err(message) => {
            eprintln!("ring_interface_pin: {message}");
            ExitCode::FAILURE
        }
    }
}

fn run() -> Result<(), String> {
    let require_identical = std::env::args().any(|a| a == "--require-identical");

    let real = real_telescope()?;
    let int = int_telescope()?;

    if real.len() != 30 || int.len() != 30 {
        return Err(format!(
            "the interface must be 30 binders; measured real={} int={}",
            real.len(),
            int.len()
        ));
    }

    for (origin, rows) in [("real", &real), ("int", &int)] {
        for row in rows {
            println!(
                "{origin}\t{}\t{}\t{}",
                row.binder,
                row.source,
                hex(row.rendered.as_bytes())
            );
        }
    }

    let differing: Vec<&RingInterfaceBinder> = real
        .iter()
        .zip(int.iter())
        .filter(|(r, i)| r.rendered != i.rendered)
        .map(|(r, _)| r)
        .collect();

    eprintln!(
        "ring interface telescope: 30 binders, {} identical, {} differing",
        30 - differing.len(),
        differing.len()
    );
    for row in &differing {
        let other = int
            .iter()
            .find(|i| i.binder == row.binder)
            .map_or("<missing>", |i| i.rendered.as_str());
        eprintln!(
            "DIFFERS {}\n  real: {}\n  int:  {}",
            row.binder, row.rendered, other
        );
    }

    if require_identical && !differing.is_empty() {
        return Err(format!(
            "{} of 30 interface binders differ between the axiomatized `Real` package and the \
             axiom-free `Int` development; the telescope is NOT the same specification",
            differing.len()
        ));
    }
    Ok(())
}
