//! Compose the two admitted Fibonacci/GCD roots and report the proof surface.

use std::fmt::Write as _;
use std::fs;
use std::io::Cursor;
use std::path::{Path, PathBuf};

use axeyum_lean_import::{
    ImportLimits, canonical_declaration_sha256, compose_checked_theorem_slice, import_ndjson,
    verify_checked_theorem_composition,
};
use axeyum_lean_kernel::{Declaration, Kernel, NameId};
use serde_json::{Value, json};
use sha2::{Digest, Sha256};

const GREATEST: &str = "Nat.gcd_greatest";
const GREATEST_SHA256: &str = "c233478948b4d4aedc01c839ef9013c3feb2ddb0009d8b57699d7efb755375e6";
const SHIFT: &str = "Nat.gcd_fib_add_self";
const SHIFT_SHA256: &str = "279dc4db5daa6dc2f532f9876052500a7e278c54264b32ccbc9d4256907dfc24";
const CANDIDATES: [&str; 12] = [
    "Nat.gcd_greatest",
    "Nat.gcd_fib_add_self",
    "Nat.gcd.induction",
    "Axeyum.Autogenesis.modQuotientWitnessV4",
    "Nat.gcd_zero_left",
    "Nat.gcd_succ",
    "Nat.add_zero",
    "Nat.zero_add",
    "Nat.add_assoc",
    "Nat.mul_succ",
    "Nat.mul_comm",
    "congrArg",
];
const USAGE: &str = "usage: nat_fib_gcd_surface_audit <gcd-greatest.ndjson> <gcd-fib-shift.ndjson>";

fn main() {
    if let Err(error) = run() {
        eprintln!("nat-fib-gcd-surface-audit: {error}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), String> {
    let mut arguments = std::env::args_os().skip(1);
    let greatest_path = arguments.next().map(PathBuf::from).ok_or(USAGE)?;
    let shift_path = arguments.next().map(PathBuf::from).ok_or(USAGE)?;
    if arguments.next().is_some() {
        return Err(USAGE.to_owned());
    }
    let greatest = import_bound(&greatest_path, "gcd-greatest", GREATEST_SHA256)?;
    let shift = import_bound(&shift_path, "gcd-fib-shift", SHIFT_SHA256)?;
    require_empty_root(greatest.kernel(), GREATEST)?;
    require_empty_root(shift.kernel(), SHIFT)?;
    let composed = compose_checked_theorem_slice(shift.kernel(), greatest.kernel(), &[SHIFT])
        .map_err(|error| format!("root composition declined: {error:?}"))?;
    verify_checked_theorem_composition(
        shift.kernel(),
        greatest.kernel(),
        composed.kernel(),
        composed.receipt(),
    )
    .map_err(|error| format!("root composition did not replay: {error:?}"))?;
    require_empty_root(composed.kernel(), GREATEST)?;
    require_empty_root(composed.kernel(), SHIFT)?;

    let mut present = Vec::new();
    let mut missing = Vec::new();
    for candidate in CANDIDATES {
        match optional_name(composed.kernel(), candidate)? {
            Some(name) => present.push(declaration_evidence(composed.kernel(), name)?),
            None => missing.push(candidate),
        }
    }
    println!(
        "{}",
        serde_json::to_string_pretty(&json!({
            "schema_version": 1,
            "kind": "axeyum-autogenesis-mathlib-nat-fib-gcd-surface-result-v1",
            "state": "two-admitted-roots-composed-proof-surface-measured-no-target-submission",
            "inputs": {
                "gcd_greatest_capsule_sha256": GREATEST_SHA256,
                "gcd_fib_add_self_capsule_sha256": SHIFT_SHA256,
                "fresh_imports": 2
            },
            "composition": {
                "root": SHIFT,
                "receipt_sha256": composed.receipt().receipt_sha256,
                "added_theorems": composed.receipt().added_theorems.len()
            },
            "surface": {
                "candidate_count": CANDIDATES.len(),
                "present": present,
                "missing": missing
            },
            "authority": {
                "proof_bodies_rendered": 0,
                "proof_search_invocations": 0,
                "helper_theorem_submissions": 0,
                "target_theorem_submissions": 0,
                "target_credit": 0,
                "ledger_writes": 0
            }
        }))
        .map_err(|error| error.to_string())?
    );
    Ok(())
}

fn import_bound(
    path: &Path,
    label: &str,
    expected_sha256: &str,
) -> Result<axeyum_lean_import::CompletedImport, String> {
    let bytes = fs::read(path).map_err(|error| format!("{label} read failed: {error}"))?;
    let actual = hex_sha256(&bytes);
    if actual != expected_sha256 {
        return Err(format!(
            "{label} identity changed: expected {expected_sha256}, got {actual}"
        ));
    }
    import_ndjson(Cursor::new(bytes), ImportLimits::default())
        .map_err(|error| format!("{label} import failed: {error:?}"))
}

fn require_empty_root(kernel: &Kernel, expected: &str) -> Result<(), String> {
    let name = find_name(kernel, expected)?;
    if !matches!(
        kernel.environment().get(name),
        Some(Declaration::Theorem { .. })
    ) || !kernel.axiom_footprint(name).is_empty()
    {
        return Err(format!(
            "{expected} is absent, not a theorem, or assumption-bearing"
        ));
    }
    Ok(())
}

fn declaration_evidence(kernel: &Kernel, name: NameId) -> Result<Value, String> {
    let declaration = kernel
        .environment()
        .get(name)
        .ok_or_else(|| "declaration disappeared".to_owned())?;
    let kind = match declaration {
        Declaration::Axiom { .. } => "axiom",
        Declaration::Definition { .. } => "definition",
        Declaration::Theorem { .. } => "theorem",
        Declaration::Opaque { .. } => "opaque",
        Declaration::Quotient { .. } => "quotient",
        Declaration::Inductive { .. } => "inductive",
        Declaration::Constructor { .. } => "constructor",
        Declaration::Recursor { .. } => "recursor",
    };
    let mut footprint = if matches!(declaration, Declaration::Theorem { .. }) {
        kernel
            .axiom_footprint(name)
            .into_iter()
            .map(|dependency| kernel.display_name(dependency).to_string())
            .collect::<Vec<_>>()
    } else {
        Vec::new()
    };
    footprint.sort();
    if !footprint.is_empty() {
        return Err(format!(
            "present theorem {} is assumption-bearing: {footprint:?}",
            kernel.display_name(name)
        ));
    }
    Ok(json!({
        "name": kernel.display_name(name).to_string(),
        "kind": kind,
        "declaration_sha256": canonical_declaration_sha256(kernel, name)?,
        "axiom_footprint": footprint
    }))
}

fn optional_name(kernel: &Kernel, expected: &str) -> Result<Option<NameId>, String> {
    let matches = kernel
        .environment()
        .iter()
        .filter_map(|(&name, _)| {
            (kernel.display_name(name).to_string() == expected).then_some(name)
        })
        .collect::<Vec<_>>();
    match matches.as_slice() {
        [name] => Ok(Some(*name)),
        [] => Ok(None),
        _ => Err(format!("declaration is ambiguous: {expected}")),
    }
}

fn find_name(kernel: &Kernel, expected: &str) -> Result<NameId, String> {
    optional_name(kernel, expected)?.ok_or_else(|| format!("declaration is absent: {expected}"))
}

fn hex_sha256(bytes: &[u8]) -> String {
    let mut digest = String::with_capacity(64);
    for byte in Sha256::digest(bytes) {
        write!(&mut digest, "{byte:02x}").expect("writing a digest into a String cannot fail");
    }
    digest
}
