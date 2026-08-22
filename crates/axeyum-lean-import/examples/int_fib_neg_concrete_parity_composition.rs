//! Compose exact clean parity adapters needed by `Int.fib_neg`.

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

const HASHES: [&str; 5] = [
    "29053dba3b90cecf5a70ba347ea7dba81a19990f715e69d5fc0a1c60cb9a6c07",
    "a00d0b93b55500c04928939ea2ff00c4d0d35b4caa0e0fa96fefeebf1be3f3c6",
    "22a7252af7c92318170aa9712fbdaeaf75fe094c371b95033e7c582cba65bb6f",
    "0547aedeece1147719fc8adfae83a517daca460a8125c087e15989811184b098",
    "e26dbda36de1c09154da8e761dfedfec08c21b61c8be4669830fc6729e9d0715",
];
const LABELS: [&str; 5] = [
    "clean decision",
    "natural double negation",
    "double negation wrapper",
    "integer double-negation residual",
    "parity residuals",
];

const NAT_DOUBLE: &str = "Axeyum.Autogenesis.intNegNatDoubleV2";
const NEG_NEG: &str = "Axeyum.Autogenesis.intNegNegV2";
const NEG_DOUBLE_RESIDUAL: &str = "Axeyum.Autogenesis.intNegDoubleResidualV1";
const NEG_DOUBLE: &str = "Axeyum.Autogenesis.intNegDoubleV1";
const EVEN_NEG_RESIDUAL: &str = "Axeyum.Autogenesis.intEvenNegResidualV2";
const EVEN_POS_RESIDUAL: &str = "Axeyum.Autogenesis.intEvenOfNatModTwoResidualV2";
const EVEN_NEG_NAT_RESIDUAL: &str = "Axeyum.Autogenesis.intEvenNegOfNatModTwoResidualV2";
const EVEN_NEG: &str = "Axeyum.Autogenesis.intEvenNegV1";
const EVEN_POS: &str = "Axeyum.Autogenesis.intEvenOfNatModTwoV1";
const EVEN_NEG_NAT: &str = "Axeyum.Autogenesis.intEvenNegOfNatModTwoV1";
const EVEN_IFF: &str = "Int.even_iff";
const ROOTS: [&str; 4] = [NEG_DOUBLE, EVEN_NEG, EVEN_POS, EVEN_NEG_NAT];

const USAGE: &str = "usage: int_fib_neg_concrete_parity_composition \
    <decision.ndjson> <nat-double.ndjson> <neg-neg.ndjson> \
    <neg-double-residual.ndjson> <parity-residuals.ndjson> <output.ndjson>";

fn main() {
    if let Err(error) = run() {
        eprintln!("int-fib-neg-concrete-parity-composition: {error}");
        std::process::exit(1);
    }
}

#[allow(clippy::too_many_lines)]
fn run() -> Result<(), String> {
    let mut arguments = std::env::args_os().skip(1);
    let paths = (0..6)
        .map(|_| path(&mut arguments))
        .collect::<Result<Vec<_>, _>>()?;
    if arguments.next().is_some() || paths[5].exists() {
        return Err(USAGE.to_owned());
    }

    let imports = paths[..5]
        .iter()
        .zip(HASHES)
        .zip(LABELS)
        .map(|((path, hash), label)| import_bound(path, hash, label))
        .collect::<Result<Vec<_>, _>>()?;
    if !imports[0].report().axioms.is_empty()
        || !imports[1].report().axioms.is_empty()
        || !imports[3].report().axioms.is_empty()
        || !imports[4].report().axioms.is_empty()
    {
        return Err("a required clean input stream reaches assumptions".to_owned());
    }
    require_empty(
        imports[2].kernel(),
        find_name(imports[2].kernel(), NEG_NEG)?,
        NEG_NEG,
    )?;

    let mut kernel = imports[0].kernel().clone();
    let mut composition_receipts = Vec::new();
    let mut specialization_receipts = Vec::new();
    composition_receipts.push(compose(
        imports[1].kernel(),
        &mut kernel,
        &[NAT_DOUBLE],
        "natural double negation",
    )?);
    composition_receipts.push(compose(
        imports[2].kernel(),
        &mut kernel,
        &[NEG_NEG],
        "double negation wrapper",
    )?);
    composition_receipts.push(compose(
        imports[3].kernel(),
        &mut kernel,
        &[NEG_DOUBLE_RESIDUAL],
        "integer double-negation residual",
    )?);
    specialization_receipts.push(specialize(
        &mut kernel,
        NEG_DOUBLE_RESIDUAL,
        &[NAT_DOUBLE, NEG_NEG],
        &["Axeyum", "Autogenesis", "intNegDoubleV1"],
        "integer negated double",
    )?);

    composition_receipts.push(compose(
        imports[4].kernel(),
        &mut kernel,
        &[EVEN_NEG_RESIDUAL, EVEN_POS_RESIDUAL, EVEN_NEG_NAT_RESIDUAL],
        "parity residuals",
    )?);
    specialization_receipts.push(specialize(
        &mut kernel,
        EVEN_NEG_RESIDUAL,
        &[NEG_DOUBLE, NEG_NEG],
        &["Axeyum", "Autogenesis", "intEvenNegV1"],
        "even negation",
    )?);
    specialization_receipts.push(specialize(
        &mut kernel,
        EVEN_POS_RESIDUAL,
        &[EVEN_IFF],
        &["Axeyum", "Autogenesis", "intEvenOfNatModTwoV1"],
        "positive-cast parity",
    )?);
    specialization_receipts.push(specialize(
        &mut kernel,
        EVEN_NEG_NAT_RESIDUAL,
        &[EVEN_NEG, EVEN_POS],
        &["Axeyum", "Autogenesis", "intEvenNegOfNatModTwoV1"],
        "negative-cast parity",
    )?);

    let evidence = ROOTS
        .iter()
        .map(|root| {
            let name = find_name(&kernel, root)?;
            require_empty(&kernel, name, root)?;
            theorem_evidence(&kernel, name)
        })
        .collect::<Result<Vec<_>, String>>()?;
    let root_ids = ROOTS
        .iter()
        .map(|root| find_name(&kernel, root))
        .collect::<Result<Vec<_>, _>>()?;
    let bytes = kernel
        .render_lean4export_ndjson_roots(&Lean4ExportMetadata::axeyum("4.30.0"), &root_ids)
        .map_err(|error| format!("concrete parity export failed: {error}"))?;
    for pass in 1..=2 {
        let replay = import_ndjson(Cursor::new(bytes.as_bytes()), ImportLimits::default())
            .map_err(|error| format!("fresh parity import {pass} failed: {error:?}"))?;
        let replay_evidence = ROOTS
            .iter()
            .map(|root| theorem_evidence(replay.kernel(), find_name(replay.kernel(), root)?))
            .collect::<Result<Vec<_>, String>>()?;
        if replay_evidence != evidence {
            return Err(format!("fresh parity import {pass} changed evidence"));
        }
    }
    fs::write(&paths[5], &bytes).map_err(|error| format!("parity write failed: {error}"))?;

    println!(
        "{}",
        serde_json::to_string_pretty(&json!({
            "schema_version": 1,
            "kind": "axeyum-int-fib-neg-concrete-parity-composition",
            "state": "four-concrete-parity-supports-specialized-exported-and-reimported-empty-footprint",
            "input_sha256": HASHES,
            "composition_receipt_sha256": composition_receipts,
            "specialization_receipt_sha256": specialization_receipts,
            "roots": evidence,
            "capsule": {
                "path": paths[5],
                "bytes": bytes.len(),
                "sha256": hex_sha256(bytes.as_bytes()),
                "fresh_imports": 2,
            },
            "execution": {
                "complete_invocations": 1,
                "input_stream_reads": 5,
                "composition_operations": 4,
                "composition_replays": 4,
                "specialization_operations": 4,
                "specialization_replays": 4,
                "capsule_exports": 1,
                "fresh_imports": 2,
                "retries": 0,
                "exact_target_submissions": 0,
                "ledger_writes": 0,
            },
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
    let mut staging = kernel.clone();
    let target = nested_name(&mut staging, target_parts);
    let completed = specialize_checked_theorem(&staging, generic_name, &argument_names, target)
        .map_err(|error| format!("{label} specialization declined: {error:?}"))?;
    verify_checked_theorem_specialization(
        &staging,
        completed.kernel(),
        generic_name,
        &argument_names,
        target,
        completed.receipt(),
    )
    .map_err(|error| format!("{label} specialization replay failed: {error:?}"))?;
    let receipt = completed.receipt().receipt_sha256.clone();
    *kernel = completed.kernel().clone();
    Ok(receipt)
}

fn require_empty(kernel: &Kernel, theorem: NameId, label: &str) -> Result<(), String> {
    if !matches!(
        kernel.environment().get(theorem),
        Some(Declaration::Theorem { .. })
    ) {
        return Err(format!("{label} is not a theorem"));
    }
    let footprint = names(kernel, &kernel.axiom_footprint(theorem));
    if footprint.is_empty() {
        Ok(())
    } else {
        Err(format!("{label} reaches assumptions: {footprint:?}"))
    }
}

fn theorem_evidence(kernel: &Kernel, theorem: NameId) -> Result<Value, String> {
    Ok(json!({
        "name": kernel.display_name(theorem).to_string(),
        "declaration_sha256": canonical_declaration_sha256(kernel, theorem)?,
        "axiom_footprint": names(kernel, &kernel.axiom_footprint(theorem)),
        "direct_theorem_dependencies": names(kernel, &kernel.theorem_dependencies(theorem)),
    }))
}

fn path(arguments: &mut impl Iterator<Item = std::ffi::OsString>) -> Result<PathBuf, String> {
    arguments
        .next()
        .map(PathBuf::from)
        .ok_or_else(|| USAGE.to_owned())
}

fn import_bound(
    path: &Path,
    expected: &str,
    label: &str,
) -> Result<axeyum_lean_import::CompletedImport, String> {
    let bytes = fs::read(path).map_err(|error| format!("{label} read failed: {error}"))?;
    let actual = hex_sha256(&bytes);
    if actual != expected {
        return Err(format!(
            "{label} identity changed: expected {expected}, got {actual}"
        ));
    }
    import_ndjson(Cursor::new(bytes), ImportLimits::default())
        .map_err(|error| format!("{label} import failed: {error:?}"))
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

fn hex_sha256(bytes: &[u8]) -> String {
    let mut output = String::with_capacity(64);
    for byte in Sha256::digest(bytes) {
        write!(&mut output, "{byte:02x}").expect("String writes cannot fail");
    }
    output
}
