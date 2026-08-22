//! Compose the two exact constructor branches needed by `Int.fib_neg`.

use std::fmt::Write as _;
use std::fs;
use std::io::Cursor;
use std::path::{Path, PathBuf};

use axeyum_lean_import::{
    ImportLimits, canonical_declaration_sha256, compose_checked_theorem_slice,
    compose_checked_theorem_slice_with_target_leaves, import_ndjson, specialize_checked_theorem,
    verify_checked_theorem_composition, verify_checked_theorem_composition_with_target_leaves,
    verify_checked_theorem_specialization,
};
use axeyum_lean_kernel::{Declaration, Kernel, Lean4ExportMetadata, NameId};
use serde_json::{Value, json};
use sha2::{Digest, Sha256};

const HASHES: [&str; 5] = [
    "6c803eff520a62d6925db5ed30f78714d9923281becfd78239cc28278bc9159f",
    "f0e34ecb1dff747938b7f1079c307af5f4e79e7a67e3bc514feee03e4f30656d",
    "e1ab008fd4b32ff2d2a6d39f0a2797031092eba39d6678b9496f07a3222897ae",
    "22a7252af7c92318170aa9712fbdaeaf75fe094c371b95033e7c582cba65bb6f",
    "0803256ec044d9e3ce59d2fb33c0465f464c9ac754d85ac471410adb8502f060",
];
const LABELS: [&str; 5] = [
    "clean negative natCast",
    "clean fib natCast",
    "concrete parity",
    "clean double negation",
    "constructor branch residuals",
];

const FIB: &str = "Int.fib";
const NAT_FIB: &str = "Nat.fib";
const FIB_NATCAST: &str = "Int.fib_natCast";
const NEG_EVEN: &str = "Axeyum.Autogenesis.intFibNegativeEvenV1";
const NEG_ODD: &str = "Axeyum.Autogenesis.intFibNegativeOddV1";
const MOD_CASES: &str = "Axeyum.IntFib.modCases";
const EVEN_POS: &str = "Axeyum.Autogenesis.intEvenOfNatModTwoV1";
const EVEN_NEG_NAT: &str = "Axeyum.Autogenesis.intEvenNegOfNatModTwoV1";
const NEG_NEG: &str = "Axeyum.Autogenesis.intNegNegV2";
const EVEN_IFF: &str = "Int.even_iff";
const POS_RESIDUAL: &str = "Axeyum.Autogenesis.intFibNegPositiveBranchResidualV1";
const NEG_RESIDUAL: &str = "Axeyum.Autogenesis.intFibNegNegativeBranchResidualV1";
const POS_BRANCH: &str = "Axeyum.Autogenesis.intFibNegPositiveBranchV1";
const NEG_BRANCH: &str = "Axeyum.Autogenesis.intFibNegNegativeBranchV1";
const ROOTS: [&str; 2] = [POS_BRANCH, NEG_BRANCH];

const USAGE: &str = "usage: int_fib_neg_concrete_branches_composition \
    <negative-natcast.ndjson> <fib-natcast.ndjson> <parity.ndjson> \
    <neg-neg.ndjson> <branch-residuals.ndjson> <output.ndjson>";

fn main() {
    if let Err(error) = run() {
        eprintln!("int-fib-neg-concrete-branches-composition: {error}");
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
    for (completed, label) in imports.iter().zip(LABELS) {
        if !completed.report().axioms.is_empty() {
            return Err(format!("{label} stream reaches assumptions"));
        }
    }

    let mut kernel = imports[0].kernel().clone();
    let mut ordinary_receipts = Vec::new();
    ordinary_receipts.push(compose(
        imports[1].kernel(),
        &mut kernel,
        &[FIB_NATCAST],
        "clean fib natCast",
    )?);
    ordinary_receipts.push(compose(
        imports[3].kernel(),
        &mut kernel,
        &[NEG_NEG],
        "clean double negation",
    )?);
    ordinary_receipts.push(compose(
        imports[2].kernel(),
        &mut kernel,
        &[EVEN_POS, EVEN_NEG_NAT],
        "concrete parity",
    )?);

    let branch_composition = compose_checked_theorem_slice_with_target_leaves(
        imports[4].kernel(),
        &kernel,
        &[POS_RESIDUAL, NEG_RESIDUAL],
        &[EVEN_IFF],
    )
    .map_err(|error| format!("branch target-leaf composition declined: {error:?}"))?;
    verify_checked_theorem_composition_with_target_leaves(
        imports[4].kernel(),
        &kernel,
        branch_composition.kernel(),
        branch_composition.receipt(),
    )
    .map_err(|error| format!("branch target-leaf replay failed: {error:?}"))?;
    if branch_composition.receipt().target_theorem_leaves != [EVEN_IFF] {
        return Err("branch target-leaf receipt changed".to_owned());
    }
    let target_leaf_receipt = branch_composition.receipt().receipt_sha256.clone();
    kernel = branch_composition.kernel().clone();

    let positive_receipt = specialize(
        &mut kernel,
        POS_RESIDUAL,
        &[
            FIB,
            NAT_FIB,
            FIB_NATCAST,
            NEG_EVEN,
            NEG_ODD,
            MOD_CASES,
            EVEN_POS,
        ],
        &["Axeyum", "Autogenesis", "intFibNegPositiveBranchV1"],
        "positive constructor branch",
    )?;
    let negative_receipt = specialize(
        &mut kernel,
        NEG_RESIDUAL,
        &[
            FIB,
            NAT_FIB,
            FIB_NATCAST,
            NEG_EVEN,
            NEG_ODD,
            MOD_CASES,
            EVEN_NEG_NAT,
            NEG_NEG,
        ],
        &["Axeyum", "Autogenesis", "intFibNegNegativeBranchV1"],
        "negative constructor branch",
    )?;

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
        .map_err(|error| format!("concrete branch export failed: {error}"))?;
    for pass in 1..=2 {
        let replay = import_ndjson(Cursor::new(bytes.as_bytes()), ImportLimits::default())
            .map_err(|error| format!("fresh branch import {pass} failed: {error:?}"))?;
        let replay_evidence = ROOTS
            .iter()
            .map(|root| theorem_evidence(replay.kernel(), find_name(replay.kernel(), root)?))
            .collect::<Result<Vec<_>, String>>()?;
        if replay_evidence != evidence {
            return Err(format!("fresh branch import {pass} changed evidence"));
        }
    }
    fs::write(&paths[5], &bytes).map_err(|error| format!("branch write failed: {error}"))?;

    println!(
        "{}",
        serde_json::to_string_pretty(&json!({
            "schema_version": 1,
            "kind": "axeyum-int-fib-neg-concrete-branches-composition",
            "state": "both-concrete-constructor-branches-specialized-exported-and-reimported-empty-footprint",
            "input_sha256": HASHES,
            "ordinary_composition_receipt_sha256": ordinary_receipts,
            "target_leaf_composition_receipt_sha256": target_leaf_receipt,
            "specialization_receipt_sha256": [positive_receipt, negative_receipt],
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
                "ordinary_compositions": 3,
                "ordinary_replays": 3,
                "target_leaf_compositions": 1,
                "target_leaf_replays": 1,
                "specialization_operations": 2,
                "specialization_replays": 2,
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
        .map_err(|error| format!("{label} replay failed: {error:?}"))?;
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
        .map(|name| find_name(kernel, name))
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
    .map_err(|error| format!("{label} replay failed: {error:?}"))?;
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
    Ok(
        json!({"name": kernel.display_name(theorem).to_string(), "declaration_sha256": canonical_declaration_sha256(kernel, theorem)?, "axiom_footprint": names(kernel, &kernel.axiom_footprint(theorem)), "direct_theorem_dependencies": names(kernel, &kernel.theorem_dependencies(theorem))}),
    )
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
    let mut names = values
        .iter()
        .map(|&name| kernel.display_name(name).to_string())
        .collect::<Vec<_>>();
    names.sort();
    names
}

fn hex_sha256(bytes: &[u8]) -> String {
    let mut output = String::with_capacity(64);
    for byte in Sha256::digest(bytes) {
        write!(&mut output, "{byte:02x}").expect("String writes cannot fail");
    }
    output
}
