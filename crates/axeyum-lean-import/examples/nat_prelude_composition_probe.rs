//! Measure whether the axiom-free native Nat library composes with an import.

use std::collections::BTreeMap;
use std::fmt::Write as _;
use std::fs;
use std::io::Cursor;
use std::path::PathBuf;

use axeyum_lean_import::{
    ImportLimits, canonical_alpha_expression_sha256, canonical_declaration_sha256,
    canonical_expression_sha256, canonical_kernel_type_shape_sha256, import_ndjson,
};
use axeyum_lean_kernel::{Declaration, Kernel, KernelError, build_nat_prelude};
use serde_json::json;
use sha2::{Digest, Sha256};

fn main() {
    if let Err(error) = run() {
        eprintln!("nat-prelude-composition-probe: {error}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), String> {
    let mut arguments = std::env::args_os().skip(1);
    let path = arguments
        .next()
        .map(PathBuf::from)
        .ok_or("usage: nat_prelude_composition_probe <stream.ndjson> [output.json]")?;
    let output_path = arguments.next().map(PathBuf::from);
    if arguments.next().is_some() {
        return Err("unexpected trailing argument".to_owned());
    }
    let stream = fs::read(path).map_err(|error| error.to_string())?;
    let completed = import_ndjson(Cursor::new(&stream), ImportLimits::default())
        .map_err(|error| format!("source import failed: {error:?}"))?;
    let (mut kernel, report) = completed.into_parts();
    if !report.axioms.is_empty() {
        return Err("source stream unexpectedly contains axioms".to_owned());
    }
    let declarations_before = kernel.environment().len();
    let theorems_before = kernel
        .environment()
        .iter()
        .filter(|(_, declaration)| matches!(declaration, Declaration::Theorem { .. }))
        .count();
    let required_names = [
        "Nat.rec",
        "Nat.add_comm",
        "Nat.gcd_zero_left",
        "Nat.gcd_dvd_left",
        "Nat.gcd_dvd_right",
        "Nat.dvd_add_iff_right",
        "Nat.dvd_gcd",
        "Nat.eq_one_of_dvd_one",
    ];
    let required = required_names
        .into_iter()
        .map(|required| {
            let present = kernel
                .environment()
                .iter()
                .any(|(&name, _)| kernel.display_name(name).to_string() == required);
            (required.to_owned(), json!(present))
        })
        .collect::<serde_json::Map<_, _>>();
    let overlaps = compare_native_overlaps(&kernel)?;
    let result = match build_nat_prelude(&mut kernel) {
        Ok(_) => json!({"outcome": "composed"}),
        Err(error) => {
            let conflicting_name = match &error {
                KernelError::DeclarationExists { name } => {
                    Some(kernel.display_name(*name).to_string())
                }
                _ => None,
            };
            json!({
                "outcome": "rejected",
                "error": format!("{error:?}"),
                "conflicting_name": conflicting_name,
            })
        }
    };
    let rendered = serde_json::to_string(&json!({
        "schema_version": 1,
        "kind": "axeyum-native-nat-prelude-import-composition-probe",
        "source": {
            "stream_sha256": hex_sha256(&stream),
            "lean_version": report.lean_version,
            "lean_githash": report.lean_githash,
            "axioms": report.axioms,
            "declarations_before": declarations_before,
            "theorems_before": theorems_before,
            "required_declarations_present": required,
            "native_declarations": overlaps.native_declarations,
            "exact_overlap_names": overlaps.exact,
            "alpha_type_compatible_content_mismatched_names": overlaps.alpha_type_compatible_content_mismatched,
            "kernel_type_shape_compatible_content_mismatched_names": overlaps.kernel_type_shape_compatible_content_mismatched,
            "type_mismatched_overlaps": overlaps.type_mismatched,
        },
        "result": result,
        "authority": {
            "proof_bodies_displayed": false,
            "proof_search_invocations": 0,
            "kernel_submissions": 0,
            "ledger_writes": 0,
        },
    }))
    .map_err(|error| error.to_string())?;
    if let Some(output_path) = output_path {
        fs::write(output_path, format!("{rendered}\n")).map_err(|error| error.to_string())?;
    }
    println!("{rendered}");
    Ok(())
}

fn declaration_names(kernel: &Kernel) -> BTreeMap<String, axeyum_lean_kernel::NameId> {
    kernel
        .environment()
        .iter()
        .map(|(&name, _)| (kernel.display_name(name).to_string(), name))
        .collect()
}

struct OverlapReport {
    native_declarations: usize,
    exact: Vec<String>,
    alpha_type_compatible_content_mismatched: Vec<String>,
    kernel_type_shape_compatible_content_mismatched: Vec<String>,
    type_mismatched: Vec<serde_json::Value>,
}

fn compare_native_overlaps(imported: &Kernel) -> Result<OverlapReport, String> {
    let imported_names = declaration_names(imported);
    let mut native = Kernel::new();
    build_nat_prelude(&mut native)
        .map_err(|error| format!("native Nat prelude failed to build: {error:?}"))?;
    let native_names = declaration_names(&native);
    let mut exact = Vec::new();
    let mut alpha_type_compatible_content_mismatched = Vec::new();
    let mut kernel_type_shape_compatible_content_mismatched = Vec::new();
    let mut type_mismatched = Vec::new();
    for (name, &native_id) in &native_names {
        let Some(&imported_id) = imported_names.get(name) else {
            continue;
        };
        let native_digest = canonical_declaration_sha256(&native, native_id)?;
        let imported_digest = canonical_declaration_sha256(imported, imported_id)?;
        if native_digest == imported_digest {
            exact.push(name.clone());
        } else {
            let native_type_id = native
                .environment()
                .get(native_id)
                .expect("native name")
                .ty();
            let imported_type_id = imported
                .environment()
                .get(imported_id)
                .expect("imported name")
                .ty();
            let native_type = canonical_expression_sha256(&native, native_type_id)?;
            let imported_type = canonical_expression_sha256(imported, imported_type_id)?;
            let native_alpha_type = canonical_alpha_expression_sha256(&native, native_type_id)?;
            let imported_alpha_type =
                canonical_alpha_expression_sha256(imported, imported_type_id)?;
            if native_alpha_type == imported_alpha_type {
                alpha_type_compatible_content_mismatched.push(name.clone());
            } else {
                let native_kernel_type_shape =
                    canonical_kernel_type_shape_sha256(&native, native_type_id)?;
                let imported_kernel_type_shape =
                    canonical_kernel_type_shape_sha256(imported, imported_type_id)?;
                if native_kernel_type_shape == imported_kernel_type_shape {
                    kernel_type_shape_compatible_content_mismatched.push(name.clone());
                } else {
                    type_mismatched.push(json!({
                        "name": name,
                        "native_content_sha256": native_digest,
                        "imported_content_sha256": imported_digest,
                        "native_type_sha256": native_type,
                        "imported_type_sha256": imported_type,
                        "native_alpha_type_sha256": native_alpha_type,
                        "imported_alpha_type_sha256": imported_alpha_type,
                        "native_kernel_type_shape_sha256": native_kernel_type_shape,
                        "imported_kernel_type_shape_sha256": imported_kernel_type_shape,
                        "native_type": native.render_lean(native_type_id),
                        "imported_type": imported.render_lean(imported_type_id),
                    }));
                }
            }
        }
    }
    Ok(OverlapReport {
        native_declarations: native.environment().len(),
        exact,
        alpha_type_compatible_content_mismatched,
        kernel_type_shape_compatible_content_mismatched,
        type_mismatched,
    })
}

fn hex_sha256(bytes: &[u8]) -> String {
    let digest = Sha256::digest(bytes);
    let mut hex = String::with_capacity(digest.len() * 2);
    for byte in digest {
        let _ = write!(hex, "{byte:02x}");
    }
    hex
}
