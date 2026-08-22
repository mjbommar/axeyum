//! Compose the decision-free branch supports into exact `Int.fib_neg_natCast`.

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

const HASHES: [&str; 7] = [
    "0fbbb4d55ed862f7feb1b8efa3bf45eed24269067b3702c727d05e45c8947219",
    "ee38fd2ff6e2427e349846e49ec603145d4f71bc1676bcfd8cd61bf061a088c0",
    "6701a7a2c7da44ad48d4efacdc255af514276ae027fb56ea7b35545026c89045",
    "dbe29125ed7ffd5e66e33da9da236b22b472fa4c5527f87146adc0ca25f9faa0",
    "dcf683e222dae0ac7e0bb28931855a69ed97463afb3bac189402298b80ab879d",
    "9b5f442a5fa98cf1116cbe8976aa23b2cae22278c56ef226b51f715b84d1f041",
    "16e90aa1e7bd22f81050add555523628171d89382a96e5f047fbd4e833d0b995",
];
const LABELS: [&str; 7] = [
    "recurrence base",
    "negative presentation",
    "negative adapters",
    "power parity",
    "power adapters",
    "multiplication leaves",
    "decision-free residual",
];

const PRESENTATION: &str = "Int.fib_neg_natCast_presentation";
const NEG_EVEN_GENERIC: &str = "Axeyum.Autogenesis.intFibNegativeEvenAdapterV1";
const NEG_ODD_GENERIC: &str = "Axeyum.Autogenesis.intFibNegativeOddAdapterV1";
const POWER: &str = "Axeyum.Autogenesis.intNegOnePowParityV1";
const POWER_EVEN_GENERIC: &str = "Axeyum.Autogenesis.intFibPowerEvenAdapterV2";
const POWER_ODD_GENERIC: &str = "Axeyum.Autogenesis.intFibPowerOddAdapterV2";
const MOD_CASES: &str = "Axeyum.IntFib.modCases";
const NEG_ONE_MUL: &str = "Int.neg_one_mul";
const ONE_MUL: &str = "Int.one_mul";
const RESIDUAL: &str = "Axeyum.Autogenesis.intFibNegNatCastDecisionFreeResidualV1";
const TARGET: &str = "Int.fib_neg_natCast";
const USAGE: &str = "usage: int_fib_neg_natcast_decision_free_exact <base> <presentation> <negative-adapters> <power> <power-adapters> <multiplication> <residual> <output>";

fn main() {
    if let Err(error) = run() {
        eprintln!("int-fib-neg-natcast-decision-free-exact: {error}");
        std::process::exit(1);
    }
}

#[allow(clippy::too_many_lines)]
fn run() -> Result<(), String> {
    let mut arguments = std::env::args_os().skip(1);
    let paths = (0..8)
        .map(|_| path(&mut arguments))
        .collect::<Result<Vec<_>, _>>()?;
    if arguments.next().is_some() || paths[7].exists() {
        return Err(USAGE.to_owned());
    }

    let imports = paths[..7]
        .iter()
        .zip(HASHES)
        .zip(LABELS)
        .map(|((path, hash), label)| import_bound(path, hash, label))
        .collect::<Result<Vec<_>, _>>()?;
    for (completed, label) in imports.iter().zip(LABELS) {
        if !completed.report().axioms.is_empty() {
            return Err(format!("{label} stream reaches assumptions"));
        }
    }

    let mut kernel = imports[0].kernel().clone();
    let mut composition_receipts = Vec::new();
    let mut specialization_receipts = Vec::new();

    composition_receipts.push(compose(
        imports[1].kernel(),
        &mut kernel,
        &[PRESENTATION],
        "negative presentation",
    )?);
    composition_receipts.push(compose(
        imports[2].kernel(),
        &mut kernel,
        &[NEG_EVEN_GENERIC, NEG_ODD_GENERIC],
        "negative adapters",
    )?);
    specialization_receipts.push(specialize(
        &mut kernel,
        NEG_EVEN_GENERIC,
        &[PRESENTATION],
        &["Axeyum", "Autogenesis", "intFibNegativeEvenV1"],
        "negative-even adapter",
    )?);
    specialization_receipts.push(specialize(
        &mut kernel,
        NEG_ODD_GENERIC,
        &[PRESENTATION],
        &["Axeyum", "Autogenesis", "intFibNegativeOddV1"],
        "negative-odd adapter",
    )?);

    composition_receipts.push(compose(
        imports[3].kernel(),
        &mut kernel,
        &[POWER],
        "power parity",
    )?);
    composition_receipts.push(compose(
        imports[4].kernel(),
        &mut kernel,
        &[POWER_EVEN_GENERIC, POWER_ODD_GENERIC],
        "power adapters",
    )?);
    specialization_receipts.push(specialize(
        &mut kernel,
        POWER_EVEN_GENERIC,
        &[POWER],
        &["Axeyum", "Autogenesis", "intFibPowerEvenV1"],
        "power-even adapter",
    )?);
    specialization_receipts.push(specialize(
        &mut kernel,
        POWER_ODD_GENERIC,
        &[POWER],
        &["Axeyum", "Autogenesis", "intFibPowerOddV1"],
        "power-odd adapter",
    )?);

    composition_receipts.push(compose(
        imports[5].kernel(),
        &mut kernel,
        &[NEG_ONE_MUL, ONE_MUL],
        "multiplication leaves",
    )?);
    composition_receipts.push(compose(
        imports[6].kernel(),
        &mut kernel,
        &[RESIDUAL],
        "decision-free residual",
    )?);

    let final_arguments = [
        "Int.fib",
        "Nat.fib",
        MOD_CASES,
        "Axeyum.Autogenesis.intFibNegativeEvenV1",
        "Axeyum.Autogenesis.intFibNegativeOddV1",
        "Axeyum.Autogenesis.intFibPowerEvenV1",
        "Axeyum.Autogenesis.intFibPowerOddV1",
        NEG_ONE_MUL,
        ONE_MUL,
    ];
    let target_receipt = specialize(
        &mut kernel,
        RESIDUAL,
        &final_arguments,
        &["Int", "fib_neg_natCast"],
        "exact target",
    )?;

    let target = find_name(&kernel, TARGET)?;
    require_empty(&kernel, target, TARGET)?;
    let target_evidence = evidence(&kernel, target)?;
    let expected_dependencies = [
        MOD_CASES,
        "Axeyum.Autogenesis.intFibNegativeEvenV1",
        "Axeyum.Autogenesis.intFibNegativeOddV1",
        "Axeyum.Autogenesis.intFibPowerEvenV1",
        "Axeyum.Autogenesis.intFibPowerOddV1",
        RESIDUAL,
        NEG_ONE_MUL,
        ONE_MUL,
    ];
    if names(&kernel, &kernel.theorem_dependencies(target)) != sorted(&expected_dependencies) {
        return Err("exact target dependency set changed".to_owned());
    }

    let bytes = kernel
        .render_lean4export_ndjson_roots(&Lean4ExportMetadata::axeyum("4.30.0"), &[target])
        .map_err(|error| format!("target export failed: {error}"))?;
    for pass in 1..=2 {
        let imported = import_ndjson(Cursor::new(bytes.as_bytes()), ImportLimits::default())
            .map_err(|error| format!("fresh target import {pass} failed: {error:?}"))?;
        let replay_target = find_name(imported.kernel(), TARGET)?;
        if evidence(imported.kernel(), replay_target)? != target_evidence {
            return Err(format!("fresh target import {pass} changed evidence"));
        }
    }
    fs::write(&paths[7], &bytes).map_err(|error| format!("target write failed: {error}"))?;

    println!(
        "{}",
        serde_json::to_string_pretty(&json!({
            "schema_version": 1,
            "kind": "axeyum-int-fib-neg-natcast-decision-free-exact",
            "state": "exact-target-specialized-exported-and-twice-reimported-empty-footprint",
            "input_sha256": HASHES,
            "composition_receipt_sha256": composition_receipts,
            "support_specialization_receipt_sha256": specialization_receipts,
            "target_specialization_receipt_sha256": target_receipt,
            "target": target_evidence,
            "capsule": {"path": paths[7], "bytes": bytes.len(), "sha256": hex_sha256(bytes.as_bytes()), "fresh_imports": 2},
            "execution": {"complete_invocations": 1, "input_stream_reads": 7, "composition_operations": 6, "composition_replays": 6, "support_specializations": 4, "support_specialization_replays": 4, "target_specializations": 1, "target_specialization_replays": 1, "target_exports": 1, "fresh_target_imports": 2, "retries": 0, "ledger_writes": 0},
            "rendered_material": {"proof_terms": 0, "theorem_types": 0, "theorem_values": 0}
        }))
        .map_err(|error| error.to_string())?
    );
    Ok(())
}

fn compose(
    source: &Kernel,
    target: &mut Kernel,
    roots: &[&str],
    label: &str,
) -> Result<String, String> {
    let completed = compose_checked_theorem_slice(source, target, roots)
        .map_err(|error| format!("{label} composition declined: {error:?}"))?;
    verify_checked_theorem_composition(source, target, completed.kernel(), completed.receipt())
        .map_err(|error| format!("{label} composition replay failed: {error:?}"))?;
    let receipt = completed.receipt().receipt_sha256.clone();
    *target = completed.kernel().clone();
    Ok(receipt)
}

fn specialize(
    kernel: &mut Kernel,
    generic: &str,
    arguments: &[&str],
    target_parts: &[&str],
    label: &str,
) -> Result<String, String> {
    let generic_name = find_name(kernel, generic)?;
    let argument_names = arguments
        .iter()
        .map(|argument| find_name(kernel, argument))
        .collect::<Result<Vec<_>, _>>()?;
    let target_name = nested_name(kernel, target_parts);
    if kernel.environment().get(target_name).is_some() {
        return Err(format!("{label} target exists before specialization"));
    }
    let completed = specialize_checked_theorem(kernel, generic_name, &argument_names, target_name)
        .map_err(|error| format!("{label} specialization declined: {error:?}"))?;
    verify_checked_theorem_specialization(
        kernel,
        completed.kernel(),
        generic_name,
        &argument_names,
        target_name,
        completed.receipt(),
    )
    .map_err(|error| format!("{label} specialization replay failed: {error:?}"))?;
    let receipt = completed.receipt().receipt_sha256.clone();
    *kernel = completed.kernel().clone();
    Ok(receipt)
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
    Ok(
        json!({"name": kernel.display_name(theorem).to_string(), "declaration_sha256": canonical_declaration_sha256(kernel, theorem)?, "axiom_footprint": names(kernel, &kernel.axiom_footprint(theorem)), "direct_theorem_dependencies": names(kernel, &kernel.theorem_dependencies(theorem))}),
    )
}

fn find_name(kernel: &Kernel, expected: &str) -> Result<NameId, String> {
    let found = kernel
        .environment()
        .iter()
        .filter_map(|(&name, _)| {
            (kernel.display_name(name).to_string() == expected).then_some(name)
        })
        .collect::<Vec<_>>();
    match found.as_slice() {
        [name] => Ok(*name),
        [] => Err(format!("declaration is absent: {expected}")),
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

fn sorted(values: &[&str]) -> Vec<String> {
    let mut rendered = values
        .iter()
        .map(|value| (*value).to_owned())
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
