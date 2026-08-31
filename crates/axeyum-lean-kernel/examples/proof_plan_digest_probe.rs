//! L3 D5 identity/footprint evidence: for each of the six theorems whose
//! proof body was rewritten to go through `crate::proof_plan` instead of a
//! local `pred_iff_of_eq`/`iff_trans`/`iff_symm` copy, print
//! `name<TAB>axiom_footprint_len<TAB>sha256(rendered type | rendered value)`.
//!
//! Run against the working tree and against a snapshot of the pre-refactor
//! commit (`scripts/lane-snapshot.sh HEAD` before the rewrite) and diff the
//! two outputs: identical lines are the "byte/digest deterministic, footprint
//! unchanged" evidence L3 D5's exit criterion asks for.
//!
//! # Asking for a theorem and finding none is a FAILURE
//!
//! Every one of the six names below is looked up as a field on the built
//! `NatPrelude`, which does not compile if the field is renamed or removed —
//! so unlike a string-keyed inventory, this probe cannot silently list zero
//! rows for a missing subject; it fails to build instead.

use axeyum_lean_kernel::{Declaration, Kernel, NameId, build_nat_prelude};
use sha2::{Digest, Sha256};
use std::fmt::Write as _;
use std::process::ExitCode;

fn digest_of(kernel: &Kernel, name: NameId) -> Option<(usize, String)> {
    let decl = kernel.environment().get(name)?;
    let Declaration::Theorem { ty, value, .. } = decl else {
        return None;
    };
    let rendered = format!("{}|{}", kernel.render_lean(*ty), kernel.render_lean(*value));
    let mut hasher = Sha256::new();
    hasher.update(rendered.as_bytes());
    let digest = hasher.finalize();
    let hex = digest.iter().fold(String::new(), |mut acc, b| {
        let _ = write!(acc, "{b:02x}");
        acc
    });
    let footprint_len = kernel.axiom_footprint(name).len();
    Some((footprint_len, hex))
}

fn main() -> ExitCode {
    let mut kernel = Kernel::new();
    let p = match build_nat_prelude(&mut kernel) {
        Ok(p) => p,
        Err(e) => {
            eprintln!("Nat prelude failed to build: {e:?}");
            return ExitCode::FAILURE;
        }
    };

    let subjects: [(&str, NameId); 6] = [
        ("dvd_add_iff_left", p.dvd_add_iff_left),
        ("dvd_mod_iff_gen", p.dvd_mod_iff_gen),
        ("dvd_iff_mod_eq_zero", p.dvd_iff_mod_eq_zero),
        ("dvd_gcd_mul_iff_dvd_mul", p.dvd_gcd_mul_iff_dvd_mul),
        ("dvd_mul_gcd_iff_dvd_mul", p.dvd_mul_gcd_iff_dvd_mul),
        ("dvd_gcd_mul_gcd_iff_dvd_mul", p.dvd_gcd_mul_gcd_iff_dvd_mul),
    ];

    let mut ok = true;
    for (label, name) in subjects {
        if let Some((footprint_len, hex)) = digest_of(&kernel, name) {
            println!("{label}\t{footprint_len}\t{hex}");
        } else {
            eprintln!("MISSING: {label}");
            ok = false;
        }
    }

    if ok {
        ExitCode::SUCCESS
    } else {
        ExitCode::FAILURE
    }
}
