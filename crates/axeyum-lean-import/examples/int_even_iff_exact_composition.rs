//! Reconstruct exact clean `Int.even_iff` from checked direction theorems.

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

const RESIDUAL_SHA256: &str = "71238c494f33b99420351baaed7ed5c3f06e918e6b36cd70db980826a5a04770";
const DIRECTIONS_SHA256: &str = "11e4f56e745c1708855d64ddf7fc256cd20e97391f222e0cb1e993b8e8cb74da";

const RESIDUAL: &str = "Axeyum.Autogenesis.intEvenIffResidualV1";
const FORWARD: &str = "Axeyum.Autogenesis.intEvenToModTwoZeroClosedV1";
const BACKWARD: &str = "Axeyum.Autogenesis.intModTwoZeroToEvenClosedV1";
const TARGET: &str = "Int.even_iff";

const USAGE: &str =
    "usage: int_even_iff_exact_composition <residual.ndjson> <directions.ndjson> <output.ndjson>";

fn main() {
    if let Err(error) = run() {
        eprintln!("int-even-iff-exact-composition: {error}");
        std::process::exit(1);
    }
}

#[allow(clippy::too_many_lines)]
fn run() -> Result<(), String> {
    let mut arguments = std::env::args_os().skip(1);
    let residual_path = path(&mut arguments)?;
    let directions_path = path(&mut arguments)?;
    let output_path = path(&mut arguments)?;
    if arguments.next().is_some() || output_path.exists() {
        return Err(USAGE.to_owned());
    }

    let residual = import_bound(&residual_path, RESIDUAL_SHA256, "Iff residual")?;
    let directions = import_bound(&directions_path, DIRECTIONS_SHA256, "directions")?;
    for (label, completed) in [("Iff residual", &residual), ("directions", &directions)] {
        if !completed.report().axioms.is_empty() {
            return Err(format!("{label} stream reaches assumptions"));
        }
    }
    require_empty(
        residual.kernel(),
        find_name(residual.kernel(), RESIDUAL)?,
        RESIDUAL,
    )?;

    let direction_roots = [FORWARD, BACKWARD];
    let composition =
        compose_checked_theorem_slice(directions.kernel(), residual.kernel(), &direction_roots)
            .map_err(|error| format!("direction composition declined: {error:?}"))?;
    verify_checked_theorem_composition(
        directions.kernel(),
        residual.kernel(),
        composition.kernel(),
        composition.receipt(),
    )
    .map_err(|error| format!("direction composition replay failed: {error:?}"))?;
    let composition_receipt = composition.receipt().receipt_sha256.clone();
    let kernel = composition.kernel();

    if optional_name(kernel, TARGET)?.is_some() {
        return Err("exact Int.even_iff exists before specialization".to_owned());
    }
    let generic = find_name(kernel, RESIDUAL)?;
    let specialization_arguments = [find_name(kernel, FORWARD)?, find_name(kernel, BACKWARD)?];
    let mut staging = kernel.clone();
    let target_name = nested_name(&mut staging, &["Int", "even_iff"]);
    let specialized =
        specialize_checked_theorem(&staging, generic, &specialization_arguments, target_name)
            .map_err(|error| format!("exact Int.even_iff specialization declined: {error:?}"))?;
    verify_checked_theorem_specialization(
        &staging,
        specialized.kernel(),
        generic,
        &specialization_arguments,
        target_name,
        specialized.receipt(),
    )
    .map_err(|error| format!("exact Int.even_iff specialization replay failed: {error:?}"))?;
    let specialization_receipt = specialized.receipt().receipt_sha256.clone();
    let kernel = specialized.kernel();

    let target = find_name(kernel, TARGET)?;
    require_empty(kernel, target, TARGET)?;
    let target_evidence = evidence(kernel, target)?;
    let mut expected_dependencies = [RESIDUAL, FORWARD, BACKWARD];
    expected_dependencies.sort_unstable();
    if names(kernel, &kernel.theorem_dependencies(target)) != expected_dependencies {
        return Err("exact Int.even_iff dependency set changed".to_owned());
    }

    let bytes = kernel
        .render_lean4export_ndjson_roots(&Lean4ExportMetadata::axeyum("4.30.0"), &[target])
        .map_err(|error| format!("exact Int.even_iff export failed: {error}"))?;
    for pass in 1..=2 {
        let replay = import_ndjson(Cursor::new(bytes.as_bytes()), ImportLimits::default())
            .map_err(|error| format!("fresh exact import {pass} failed: {error:?}"))?;
        let replay_target = find_name(replay.kernel(), TARGET)?;
        if evidence(replay.kernel(), replay_target)? != target_evidence {
            return Err(format!("fresh exact import {pass} changed evidence"));
        }
    }
    fs::write(&output_path, &bytes).map_err(|error| format!("target write failed: {error}"))?;

    println!(
        "{}",
        serde_json::to_string_pretty(&json!({
            "schema_version": 1,
            "kind": "axeyum-exact-clean-int-even-iff-composition",
            "state": "exact-target-specialized-exported-and-reimported-empty-footprint",
            "input_sha256": {
                "residual": RESIDUAL_SHA256,
                "directions": DIRECTIONS_SHA256,
            },
            "composition_receipt_sha256": composition_receipt,
            "specialization_receipt_sha256": specialization_receipt,
            "target": target_evidence,
            "capsule": {
                "path": output_path,
                "bytes": bytes.len(),
                "sha256": hex_sha256(bytes.as_bytes()),
                "fresh_imports": 2,
            },
            "execution": {
                "complete_invocations": 1,
                "input_stream_reads": 2,
                "composition_operations": 1,
                "composition_replays": 1,
                "specialization_operations": 1,
                "specialization_replays": 1,
                "target_submissions": 1,
                "capsule_exports": 1,
                "fresh_target_imports": 2,
                "retries": 0,
                "ledger_writes": 0,
            },
            "rendered_material": {
                "proof_terms": 0,
                "theorem_types": 0,
                "theorem_values": 0,
            },
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
