//! Construct exact, empty-footprint `Nat.fib_pos` from admitted library inputs.

use std::fmt::Write as _;
use std::fs;
use std::io::Cursor;
use std::path::{Path, PathBuf};

use axeyum_lean_import::{
    ImportLimits, canonical_declaration_sha256, compose_checked_theorem_slice, import_ndjson,
    specialize_checked_theorem, verify_checked_theorem_composition,
    verify_checked_theorem_specialization,
};
use axeyum_lean_kernel::{Declaration, ExprId, Kernel, Lean4ExportMetadata, NameId};
use serde_json::{Value, json};
use sha2::{Digest, Sha256};

const HASHES: [&str; 4] = [
    "8b2913beb2896442e86e2f5840aaf5bf31c46a4f4ce2a2469ad6a2b0bfd052bc",
    "7f59cee9c23e306ad0f45b1ae0cc02908aafd26338fea01020eb66da84f0d81d",
    "065d5ed0ea1d6c02a24775bdc4bc7607392c5fad50e728b256a2ab9692d05f5d",
    "755cc8963198446f567622465e0ad87e1496d83fcaacf2362e1da0e7d8e6bb4f",
];
const LABELS: [&str; 4] = [
    "recurrence",
    "core positivity",
    "main residual",
    "step residual",
];
const RECURRENCE: &str = "Nat.fib_add_two";
const ZERO_LT_SUCC: &str = "Nat.zero_lt_succ";
const ADD_POS_RIGHT: &str = "Nat.add_pos_right";
const MAIN_RESIDUAL: &str = "Axeyum.Autogenesis.natFibPosResidualV1";
const STEP_RESIDUAL: &str = "Axeyum.Autogenesis.natFibStepPositiveResidualV1";
const ZERO_SUPPORT: &str = "Axeyum.Autogenesis.natFibZeroV1";
const ONE_SUPPORT: &str = "Axeyum.Autogenesis.natFibOnePositiveV1";
const STEP_SUPPORT: &str = "Axeyum.Autogenesis.natFibStepPositiveV1";
const TARGET: &str = "Nat.fib_pos";
const USAGE: &str = "usage: nat_fib_pos_exact <recurrence.ndjson> <core.ndjson> <main-residual.ndjson> <step-residual.ndjson> <output.ndjson>";

fn main() {
    if let Err(error) = run() {
        eprintln!("nat-fib-pos-exact: {error}");
        std::process::exit(1);
    }
}

#[allow(clippy::too_many_lines)]
fn run() -> Result<(), String> {
    let mut arguments = std::env::args_os().skip(1);
    let paths = (0..5)
        .map(|_| path(&mut arguments))
        .collect::<Result<Vec<_>, _>>()?;
    if arguments.next().is_some() || paths[4].exists() {
        return Err(USAGE.to_owned());
    }
    let imports = paths[..4]
        .iter()
        .zip(HASHES)
        .zip(LABELS)
        .map(|((path, hash), label)| import_bound(path, hash, label))
        .collect::<Result<Vec<_>, _>>()?;
    if imports
        .iter()
        .any(|completed| !completed.report().axioms.is_empty())
    {
        return Err("an input stream reaches assumptions".to_owned());
    }

    let mut kernel = imports[1].kernel().clone();
    if optional_name(&kernel, TARGET)?.is_some() {
        return Err("exact target exists before construction".to_owned());
    }
    let compositions = [
        compose(
            imports[0].kernel(),
            &mut kernel,
            &["Nat.fib", RECURRENCE],
            "recurrence",
        )?,
        compose(
            imports[2].kernel(),
            &mut kernel,
            &[MAIN_RESIDUAL],
            "main residual",
        )?,
        compose(
            imports[3].kernel(),
            &mut kernel,
            &[STEP_RESIDUAL],
            "step residual",
        )?,
    ];

    add_zero_support(&mut kernel)?;
    add_one_support(&mut kernel)?;
    let step_receipt = specialize(
        &mut kernel,
        STEP_RESIDUAL,
        &["Nat.fib", RECURRENCE, ADD_POS_RIGHT],
        &["Axeyum", "Autogenesis", "natFibStepPositiveV1"],
        "step positivity",
    )?;
    let target_receipt = specialize(
        &mut kernel,
        MAIN_RESIDUAL,
        &[
            "Nat.fib",
            ZERO_SUPPORT,
            ONE_SUPPORT,
            STEP_SUPPORT,
            ZERO_LT_SUCC,
        ],
        &["Nat", "fib_pos"],
        "exact target",
    )?;

    let target = find_name(&kernel, TARGET)?;
    require_empty(&kernel, target, TARGET)?;
    let target_evidence = evidence(&kernel, target)?;
    let expected_dependencies = [
        ONE_SUPPORT,
        MAIN_RESIDUAL,
        STEP_SUPPORT,
        ZERO_SUPPORT,
        ZERO_LT_SUCC,
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
    fs::write(&paths[4], &bytes).map_err(|error| format!("target write failed: {error}"))?;

    println!(
        "{}",
        serde_json::to_string_pretty(&json!({
            "schema_version": 1,
            "kind": "axeyum-nat-fib-pos-exact",
            "state": "exact-target-specialized-exported-and-twice-reimported-empty-footprint",
            "input_sha256": HASHES,
            "composition_receipt_sha256": compositions,
            "support": {"zero": evidence(&kernel, find_name(&kernel, ZERO_SUPPORT)?)?, "one": evidence(&kernel, find_name(&kernel, ONE_SUPPORT)?)?, "step": evidence(&kernel, find_name(&kernel, STEP_SUPPORT)?)?},
            "step_specialization_receipt_sha256": step_receipt,
            "target_specialization_receipt_sha256": target_receipt,
            "target": target_evidence,
            "capsule": {"path": paths[4], "bytes": bytes.len(), "sha256": hex_sha256(bytes.as_bytes()), "fresh_imports": 2},
            "execution": {"complete_invocations": 1, "input_stream_reads": 4, "composition_operations": 3, "composition_replays": 3, "support_theorem_submissions": 2, "specializations": 2, "specialization_replays": 2, "target_exports": 1, "fresh_imports": 2, "retries": 0, "fact_status_changes": 0, "ledger_writes": 0},
            "rendered_material": {"proof_terms": 0, "theorem_types": 0, "theorem_values": 0}
        }))
        .map_err(|error| error.to_string())?
    );
    Ok(())
}

fn add_zero_support(kernel: &mut Kernel) -> Result<(), String> {
    let name = nested_name(kernel, &["Axeyum", "Autogenesis", "natFibZeroV1"]);
    if kernel.environment().get(name).is_some() {
        return Err("zero support exists before submission".to_owned());
    }
    let nat = kernel.const_(find_name(kernel, "Nat")?, vec![]);
    let zero = kernel.const_(find_name(kernel, "Nat.zero")?, vec![]);
    let fib_name = find_name(kernel, "Nat.fib")?;
    let fib = kernel.const_(fib_name, vec![]);
    let fib_zero = kernel.app(fib, zero);
    let ty = equality(kernel, nat, fib_zero, zero)?;
    let refl_name = find_name(kernel, "Eq.refl")?;
    let zero_level = kernel.level_zero();
    let successor_level = kernel.level_succ(zero_level);
    let mut value = kernel.const_(refl_name, vec![successor_level]);
    value = kernel.app(value, nat);
    value = kernel.app(value, zero);
    kernel
        .add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty,
            value,
        })
        .map_err(|error| format!("zero support submission failed: {error:?}"))
}

fn add_one_support(kernel: &mut Kernel) -> Result<(), String> {
    let name = nested_name(kernel, &["Axeyum", "Autogenesis", "natFibOnePositiveV1"]);
    if kernel.environment().get(name).is_some() {
        return Err("one support exists before submission".to_owned());
    }
    let zero = kernel.const_(find_name(kernel, "Nat.zero")?, vec![]);
    let zero_lt_succ_name = find_name(kernel, ZERO_LT_SUCC)?;
    let zero_lt_succ = kernel.const_(zero_lt_succ_name, vec![]);
    let value = kernel.app(zero_lt_succ, zero);
    let ty = kernel
        .infer(value)
        .map_err(|error| format!("one support inference failed: {error:?}"))?;
    kernel
        .add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty,
            value,
        })
        .map_err(|error| format!("one support submission failed: {error:?}"))
}

fn equality(
    kernel: &mut Kernel,
    carrier: ExprId,
    left: ExprId,
    right: ExprId,
) -> Result<ExprId, String> {
    let eq_name = find_name(kernel, "Eq")?;
    let zero_level = kernel.level_zero();
    let successor_level = kernel.level_succ(zero_level);
    let mut eq = kernel.const_(eq_name, vec![successor_level]);
    eq = kernel.app(eq, carrier);
    eq = kernel.app(eq, left);
    Ok(kernel.app(eq, right))
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
        .map(|name| find_name(kernel, name))
        .collect::<Result<Vec<_>, _>>()?;
    let target_name = nested_name(kernel, target_parts);
    if kernel.environment().get(target_name).is_some() {
        return Err(format!("{label} exists before specialization"));
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

fn optional_name(kernel: &Kernel, expected: &str) -> Result<Option<NameId>, String> {
    match find_name(kernel, expected) {
        Ok(name) => Ok(Some(name)),
        Err(error) if error == format!("declaration is absent: {expected}") => Ok(None),
        Err(error) => Err(error),
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
