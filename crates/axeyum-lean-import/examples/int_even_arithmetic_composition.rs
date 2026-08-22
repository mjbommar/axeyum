//! Close target-owned integer parity arithmetic over checked natural supports.

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

const LIFTS_SHA256: &str = "a00d0b93b55500c04928939ea2ff00c4d0d35b4caa0e0fa96fefeebf1be3f3c6";
const NAT_SHA256: &str = "e2593bac01c81881c4fcace0133f93c7bdb5fd9884e2aed035083f1af9bfb77d";
const PARITY_SHA256: &str = "0e310823ba37adfbd9087c0da2f85ad57261228d601d9388800cf069b5b2ce82";

const DOUBLE_GENERIC: &str = "Axeyum.Autogenesis.intDoubleModTwoZeroLiftV1";
const HALF_GENERIC: &str = "Axeyum.Autogenesis.intHalfWitnessOfModTwoZeroLiftV1";
const NAT_DOUBLE: &str = "Axeyum.Autogenesis.natDoubleModTwoZeroClosedV1";
const NAT_HALF: &str = "Axeyum.Autogenesis.natHalfWitnessOfModTwoZeroClosedV1";
const MOD_CASES: &str = "Axeyum.IntFib.modCases";
const SUCC_ONE: &str = "Axeyum.IntFib.succOne";
const SUCC_ZERO: &str = "Axeyum.IntFib.succZero";
const DOUBLE_TARGET: &str = "Axeyum.Autogenesis.intDoubleModTwoZeroClosedV1";
const HALF_TARGET: &str = "Axeyum.Autogenesis.intHalfWitnessOfModTwoZeroClosedV1";

const USAGE: &str = "usage: int_even_arithmetic_composition <lifts.ndjson> <closed-nat.ndjson> <parity.ndjson> <output.ndjson>";

fn main() {
    if let Err(error) = run() {
        eprintln!("int-even-arithmetic-composition: {error}");
        std::process::exit(1);
    }
}

#[allow(clippy::too_many_lines)]
fn run() -> Result<(), String> {
    let mut arguments = std::env::args_os().skip(1);
    let lifts_path = path(&mut arguments)?;
    let nat_path = path(&mut arguments)?;
    let parity_path = path(&mut arguments)?;
    let output_path = path(&mut arguments)?;
    if arguments.next().is_some() || output_path.exists() {
        return Err(USAGE.to_owned());
    }

    let lifts = import_bound(&lifts_path, LIFTS_SHA256, "lifts")?;
    let nat = import_bound(&nat_path, NAT_SHA256, "closed Nat")?;
    let parity = import_bound(&parity_path, PARITY_SHA256, "parity")?;
    for (label, completed) in [("lifts", &lifts), ("closed Nat", &nat), ("parity", &parity)] {
        if !completed.report().axioms.is_empty() {
            return Err(format!("{label} stream reaches assumptions"));
        }
    }
    for root in [DOUBLE_GENERIC, HALF_GENERIC] {
        require_empty(lifts.kernel(), find_name(lifts.kernel(), root)?, root)?;
    }

    let nat_roots = [NAT_DOUBLE, NAT_HALF];
    let nat_composition = compose_checked_theorem_slice(nat.kernel(), lifts.kernel(), &nat_roots)
        .map_err(|error| format!("Nat composition declined: {error:?}"))?;
    verify_checked_theorem_composition(
        nat.kernel(),
        lifts.kernel(),
        nat_composition.kernel(),
        nat_composition.receipt(),
    )
    .map_err(|error| format!("Nat composition replay failed: {error:?}"))?;
    let nat_receipt = nat_composition.receipt().receipt_sha256.clone();

    let parity_roots = [MOD_CASES, SUCC_ONE, SUCC_ZERO];
    let parity_composition =
        compose_checked_theorem_slice(parity.kernel(), nat_composition.kernel(), &parity_roots)
            .map_err(|error| format!("parity composition declined: {error:?}"))?;
    verify_checked_theorem_composition(
        parity.kernel(),
        nat_composition.kernel(),
        parity_composition.kernel(),
        parity_composition.receipt(),
    )
    .map_err(|error| format!("parity composition replay failed: {error:?}"))?;
    let parity_receipt = parity_composition.receipt().receipt_sha256.clone();
    let mut kernel = parity_composition.kernel().clone();

    let double_arguments = [NAT_DOUBLE, SUCC_ONE];
    let (next, double_receipt) =
        specialize(&kernel, DOUBLE_GENERIC, &double_arguments, DOUBLE_TARGET)?;
    kernel = next;
    let half_arguments = [NAT_HALF, MOD_CASES, SUCC_ZERO];
    let (next, half_receipt) = specialize(&kernel, HALF_GENERIC, &half_arguments, HALF_TARGET)?;
    kernel = next;

    let targets = [
        find_name(&kernel, DOUBLE_TARGET)?,
        find_name(&kernel, HALF_TARGET)?,
    ];
    let target_evidence = targets
        .iter()
        .map(|&target| evidence(&kernel, target))
        .collect::<Result<Vec<_>, _>>()?;
    let bytes = kernel
        .render_lean4export_ndjson_roots(&Lean4ExportMetadata::axeyum("4.30.0"), &targets)
        .map_err(|error| format!("closed Int export failed: {error}"))?;
    for pass in 1..=2 {
        let replay = import_ndjson(Cursor::new(bytes.as_bytes()), ImportLimits::default())
            .map_err(|error| format!("fresh target import {pass} failed: {error:?}"))?;
        let replay_evidence = [DOUBLE_TARGET, HALF_TARGET]
            .iter()
            .map(|name| evidence(replay.kernel(), find_name(replay.kernel(), name)?))
            .collect::<Result<Vec<_>, _>>()?;
        if replay_evidence != target_evidence {
            return Err(format!("fresh target import {pass} changed evidence"));
        }
    }
    fs::write(&output_path, &bytes).map_err(|error| format!("target write failed: {error}"))?;

    println!(
        "{}",
        serde_json::to_string_pretty(&json!({
            "schema_version": 1,
            "kind": "axeyum-closed-integer-parity-arithmetic-composition",
            "state": "two-closed-int-targets-specialized-exported-and-reimported-empty-footprint",
            "input_sha256": {
                "lifts": LIFTS_SHA256,
                "closed_nat": NAT_SHA256,
                "parity": PARITY_SHA256,
            },
            "composition_receipt_sha256": {
                "closed_nat": nat_receipt,
                "parity": parity_receipt,
            },
            "specialization_receipt_sha256": {
                "double_mod_zero": double_receipt,
                "half_witness": half_receipt,
            },
            "targets": target_evidence,
            "capsule": {
                "path": output_path,
                "bytes": bytes.len(),
                "sha256": hex_sha256(bytes.as_bytes()),
                "fresh_imports": 2,
            },
            "execution": {
                "complete_invocations": 1,
                "input_stream_reads": 3,
                "composition_operations": 2,
                "composition_replays": 2,
                "specialization_operations": 2,
                "specialization_replays": 2,
                "capsule_exports": 1,
                "fresh_capsule_imports": 2,
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

fn specialize(
    kernel: &Kernel,
    generic_name: &str,
    argument_names: &[&str],
    target_name: &str,
) -> Result<(Kernel, String), String> {
    if optional_name(kernel, target_name)?.is_some() {
        return Err(format!(
            "target exists before specialization: {target_name}"
        ));
    }
    let generic = find_name(kernel, generic_name)?;
    let arguments = argument_names
        .iter()
        .map(|name| find_name(kernel, name))
        .collect::<Result<Vec<_>, _>>()?;
    let mut staging = kernel.clone();
    let target = nested_name(&mut staging, &target_name.split('.').collect::<Vec<_>>());
    let completed = specialize_checked_theorem(&staging, generic, &arguments, target)
        .map_err(|error| format!("{target_name} specialization declined: {error:?}"))?;
    verify_checked_theorem_specialization(
        &staging,
        completed.kernel(),
        generic,
        &arguments,
        target,
        completed.receipt(),
    )
    .map_err(|error| format!("{target_name} specialization replay failed: {error:?}"))?;
    require_empty(completed.kernel(), target, target_name)?;
    let observed = names(
        completed.kernel(),
        &completed.kernel().theorem_dependencies(target),
    );
    let mut expected = argument_names
        .iter()
        .map(|value| (*value).to_owned())
        .chain(std::iter::once(generic_name.to_owned()))
        .collect::<Vec<_>>();
    expected.sort();
    if observed != expected {
        return Err(format!(
            "{target_name} dependencies changed: expected {expected:?}, got {observed:?}"
        ));
    }
    Ok((
        completed.kernel().clone(),
        completed.receipt().receipt_sha256.clone(),
    ))
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
