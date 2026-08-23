//! Compose the seven qualified contracts into the exact integer Fibonacci recurrence.

use std::fmt::Write as _;
use std::fs;
use std::io::Cursor;
use std::path::{Path, PathBuf};

use axeyum_lean_import::{
    ImportLimits, canonical_declaration_sha256, compose_checked_theorem_slice, import_ndjson,
    specialize_checked_theorem, verify_checked_theorem_composition,
    verify_checked_theorem_specialization,
};
use axeyum_lean_kernel::{Declaration, Kernel, Lean4ExportMetadata, NameId};
use serde_json::{Value, json};
use sha2::{Digest, Sha256};

const RESIDUAL_SHA256: &str = "3d20dc04f7598a1625ab87efd2456901fe322ccb0e19cd51f82a04dd37c3bfc9";
const ADDITION_SHA256: &str = "5220ace53dcbf0b89121ba72c8e63cc7dcb2a2d7836b313bc597607859d78674";
const PARITY_SHA256: &str = "0e310823ba37adfbd9087c0da2f85ad57261228d601d9388800cf069b5b2ce82";
const CAST_SHA256: &str = "0fa66a39f3caec4c4bd00cfefa402b328b37a3fcbd4dd840e17e3f7f292439a5";
const CANCELLATION_SHA256: &str =
    "40e8ea3b85312f3067808a0772ecedb6689b656999ce86acd2602d9a114d9076";

const RESIDUAL: &str = "Int.fib_add_two_residual";
const ADDITION: &str = "Axeyum.Autogenesis.fibAddTwo";
const MOD_CASES: &str = "Axeyum.IntFib.modCases";
const SUCC_ONE: &str = "Axeyum.IntFib.succOne";
const SUCC_ZERO: &str = "Axeyum.IntFib.succZero";
const CAST_ADD: &str = "Axeyum.IntFib.castAdd";
const EVEN_ADD: &str = "Axeyum.IntFib.evenAdd";
const ODD_ADD: &str = "Axeyum.IntFib.oddAdd";
const TARGET: &str = "Int.fib_add_two";

const USAGE: &str = "usage: int_fib_add_two_composition <residual.ndjson> <addition.ndjson> <parity.ndjson> <cast.ndjson> <cancellation.ndjson> <output.ndjson>";

fn main() {
    if let Err(error) = run() {
        eprintln!("int-fib-add-two-composition: {error}");
        std::process::exit(1);
    }
}

#[allow(clippy::too_many_lines)]
fn run() -> Result<(), String> {
    let mut arguments = std::env::args_os().skip(1);
    let residual_path = path(&mut arguments)?;
    let addition_path = path(&mut arguments)?;
    let parity_path = path(&mut arguments)?;
    let cast_path = path(&mut arguments)?;
    let cancellation_path = path(&mut arguments)?;
    let output_path = path(&mut arguments)?;
    if arguments.next().is_some() || output_path.exists() {
        return Err(USAGE.to_owned());
    }

    let residual = import_bound(&residual_path, RESIDUAL_SHA256, "residual")?;
    let addition = import_bound(&addition_path, ADDITION_SHA256, "addition")?;
    let parity = import_bound(&parity_path, PARITY_SHA256, "parity")?;
    let cast = import_bound(&cast_path, CAST_SHA256, "cast")?;
    let cancellation = import_bound(&cancellation_path, CANCELLATION_SHA256, "cancellation")?;
    for (label, completed) in [
        ("residual", &residual),
        ("addition", &addition),
        ("parity", &parity),
        ("cancellation", &cancellation),
    ] {
        if !completed.report().axioms.is_empty() {
            return Err(format!("{label} stream reaches assumptions"));
        }
    }
    require_empty(cast.kernel(), find_name(cast.kernel(), CAST_ADD)?, CAST_ADD)?;

    let mut kernel = residual.kernel().clone();
    require_empty(&kernel, find_name(&kernel, RESIDUAL)?, RESIDUAL)?;
    let mut compositions = Vec::new();
    for (source, roots) in [
        (addition.kernel(), &[ADDITION][..]),
        (parity.kernel(), &[MOD_CASES, SUCC_ONE, SUCC_ZERO][..]),
        (cast.kernel(), &[CAST_ADD][..]),
        (cancellation.kernel(), &[EVEN_ADD, ODD_ADD][..]),
    ] {
        let completed = compose_checked_theorem_slice(source, &kernel, roots)
            .map_err(|error| format!("composition declined for {roots:?}: {error:?}"))?;
        verify_checked_theorem_composition(
            source,
            &kernel,
            completed.kernel(),
            completed.receipt(),
        )
        .map_err(|error| format!("composition replay failed for {roots:?}: {error:?}"))?;
        compositions.push(json!({
            "roots": roots,
            "receipt_sha256": completed.receipt().receipt_sha256,
        }));
        kernel = completed.kernel().clone();
    }

    let generic = find_name(&kernel, RESIDUAL)?;
    let arguments = [
        find_name(&kernel, ADDITION)?,
        find_name(&kernel, MOD_CASES)?,
        find_name(&kernel, SUCC_ONE)?,
        find_name(&kernel, SUCC_ZERO)?,
        find_name(&kernel, CAST_ADD)?,
        find_name(&kernel, EVEN_ADD)?,
        find_name(&kernel, ODD_ADD)?,
    ];
    if optional_name(&kernel, TARGET)?.is_some() {
        return Err("exact target already exists before specialization".to_owned());
    }
    let target_name = nested_name(&mut kernel, &["Int", "fib_add_two"]);
    let specialized = specialize_checked_theorem(&kernel, generic, &arguments, target_name)
        .map_err(|error| format!("exact specialization declined: {error:?}"))?;
    verify_checked_theorem_specialization(
        &kernel,
        specialized.kernel(),
        generic,
        &arguments,
        target_name,
        specialized.receipt(),
    )
    .map_err(|error| format!("exact specialization replay failed: {error:?}"))?;
    kernel = specialized.kernel().clone();

    let target = find_name(&kernel, TARGET)?;
    require_empty(&kernel, target, TARGET)?;
    let target_evidence = evidence(&kernel, target)?;
    let expected_dependencies = [
        ADDITION, CAST_ADD, EVEN_ADD, MOD_CASES, ODD_ADD, SUCC_ONE, SUCC_ZERO, RESIDUAL,
    ];
    if names(&kernel, &kernel.theorem_dependencies(target)) != expected_dependencies {
        return Err("exact target dependency set changed".to_owned());
    }

    let bytes = kernel
        .render_lean4export_ndjson_roots(&Lean4ExportMetadata::axeyum("4.30.0"), &[target])
        .map_err(|error| format!("exact target export failed: {error}"))?;
    for pass in 1..=2 {
        let replay = import_ndjson(Cursor::new(bytes.as_bytes()), ImportLimits::default())
            .map_err(|error| format!("fresh target import {pass} failed: {error:?}"))?;
        let replay_target = find_name(replay.kernel(), TARGET)?;
        if evidence(replay.kernel(), replay_target)? != target_evidence {
            return Err(format!("fresh target import {pass} changed evidence"));
        }
    }
    fs::write(&output_path, &bytes).map_err(|error| format!("target write failed: {error}"))?;

    println!(
        "{}",
        serde_json::to_string_pretty(&json!({
            "schema_version": 1,
            "kind": "axeyum-int-fib-add-two-exact-composition",
            "state": "exact-target-specialized-exported-and-reimported-empty-footprint",
            "input_sha256": {
                "residual": RESIDUAL_SHA256,
                "addition": ADDITION_SHA256,
                "parity": PARITY_SHA256,
                "cast": CAST_SHA256,
                "cancellation": CANCELLATION_SHA256,
            },
            "compositions": compositions,
            "specialization_receipt_sha256": specialized.receipt().receipt_sha256,
            "target": target_evidence,
            "capsule": {"bytes": bytes.len(), "sha256": hex_sha256(bytes.as_bytes()), "fresh_imports": 2},
            "execution": {"complete_invocations": 1, "target_submissions": 1, "exports": 1, "fresh_imports": 2, "retries": 0},
            "rendered_material": {"proof_terms": 0, "theorem_types": 0, "theorem_values": 0},
            "fact_status_changes": 0,
            "evaluation_credit": 0,
            "ledger_writes": 0,
        }))
        .map_err(|error| error.to_string())?
    );
    Ok(())
}

fn path(arguments: &mut impl Iterator<Item = std::ffi::OsString>) -> Result<PathBuf, String> {
    arguments
        .next()
        .map(PathBuf::from)
        .ok_or_else(|| USAGE.to_owned())
}

fn import_bound(
    path: &Path,
    expected_sha256: &str,
    label: &str,
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

fn require_empty(kernel: &Kernel, theorem: NameId, label: &str) -> Result<(), String> {
    let footprint = names(kernel, &kernel.axiom_footprint(theorem));
    if footprint.is_empty() {
        Ok(())
    } else {
        Err(format!("{label} reaches assumptions: {footprint:?}"))
    }
}

fn evidence(kernel: &Kernel, theorem: NameId) -> Result<Value, String> {
    if !matches!(
        kernel.environment().get(theorem),
        Some(Declaration::Theorem { .. })
    ) {
        return Err(format!("{} is not a theorem", kernel.display_name(theorem)));
    }
    Ok(json!({
        "name": kernel.display_name(theorem).to_string(),
        "declaration_sha256": canonical_declaration_sha256(kernel, theorem)?,
        "axiom_footprint": names(kernel, &kernel.axiom_footprint(theorem)),
        "direct_theorem_dependencies": names(kernel, &kernel.theorem_dependencies(theorem)),
    }))
}

fn find_name(kernel: &Kernel, expected: &str) -> Result<NameId, String> {
    optional_name(kernel, expected)?.ok_or_else(|| format!("declaration is absent: {expected}"))
}

fn optional_name(kernel: &Kernel, expected: &str) -> Result<Option<NameId>, String> {
    let found = kernel
        .environment()
        .iter()
        .filter_map(|(&name, _)| {
            (kernel.display_name(name).to_string() == expected).then_some(name)
        })
        .collect::<Vec<_>>();
    match found.as_slice() {
        [name] => Ok(Some(*name)),
        [] => Ok(None),
        _ => Err(format!("declaration is ambiguous: {expected}")),
    }
}

fn nested_name(kernel: &mut Kernel, parts: &[&str]) -> NameId {
    parts
        .iter()
        .fold(kernel.anon(), |prefix, part| kernel.name_str(prefix, *part))
}

fn names(kernel: &Kernel, values: &[NameId]) -> Vec<String> {
    let mut rendered = values
        .iter()
        .map(|&name| kernel.display_name(name).to_string())
        .collect::<Vec<_>>();
    rendered.sort();
    rendered
}

fn hex_sha256(bytes: &[u8]) -> String {
    let mut output = String::with_capacity(64);
    for byte in Sha256::digest(bytes) {
        write!(&mut output, "{byte:02x}").expect("String writes cannot fail");
    }
    output
}
