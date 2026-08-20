//! Measure whether the axiom-free native Nat library composes with an import.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;
use std::fs;
use std::io::Cursor;
use std::path::PathBuf;

use axeyum_lean_import::{
    AddedTheoremReceipt, CheckedTheoremCompositionReceipt, ImportLimits, ReusedDeclarationReceipt,
    canonical_alpha_expression_sha256, canonical_declaration_sha256, canonical_expression_sha256,
    canonical_kernel_type_shape_sha256, checked_reused_declaration_compatibility,
    compose_checked_theorem_slice, import_ndjson,
};
use axeyum_lean_kernel::{BinderInfo, Declaration, Kernel, KernelError, build_nat_prelude};
use serde_json::json;
use sha2::{Digest, Sha256};

fn main() {
    if let Err(error) = run() {
        eprintln!("nat-prelude-composition-probe: {error}");
        std::process::exit(1);
    }
}

struct ControlObservations {
    composition: serde_json::Value,
    singleton: serde_json::Value,
    acc: serde_json::Value,
    definition: serde_json::Value,
    mod_lt_compatibility: serde_json::Value,
    negative: serde_json::Value,
    kernel_submissions: usize,
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
    let imported_division_declaration_names = imported_division_declaration_names(&kernel);
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
    let controls = exercise_composition_controls(&mut kernel)?;
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
            "imported_division_declaration_names": imported_division_declaration_names,
            "native_declarations": overlaps.native_declarations,
            "exact_overlap_names": overlaps.exact,
            "alpha_type_compatible_content_mismatched_names": overlaps.alpha_type_compatible_content_mismatched,
            "kernel_type_shape_compatible_content_mismatched_names": overlaps.kernel_type_shape_compatible_content_mismatched,
            "type_mismatched_overlaps": overlaps.type_mismatched,
            "required_native_theorem_dependency_closures": overlaps.required_theorem_dependency_closures,
            "composition_control": controls.composition,
            "singleton_inductive_control": controls.singleton,
            "acc_inductive_control": controls.acc,
            "definition_control": controls.definition,
            "mod_lt_compatibility_control": controls.mod_lt_compatibility,
            "structural_mismatch_control": controls.negative,
        },
        "result": result,
        "authority": {
            "proof_bodies_displayed": false,
            "proof_search_invocations": 0,
            "kernel_submissions": controls.kernel_submissions,
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

fn imported_division_declaration_names(kernel: &Kernel) -> Vec<String> {
    let mut names = kernel
        .environment()
        .iter()
        .map(|(&name, _)| kernel.display_name(name).to_string())
        .filter(|name| {
            [
                "Nat.div",
                "Nat.mod",
                "Nat.instDiv",
                "Nat.instMod",
                "HDiv",
                "HMod",
            ]
            .iter()
            .any(|prefix| name.starts_with(prefix))
        })
        .collect::<Vec<_>>();
    names.sort();
    names
}

fn exercise_composition_controls(kernel: &mut Kernel) -> Result<ControlObservations, String> {
    let mut native = Kernel::new();
    let prelude = build_nat_prelude(&mut native)
        .map_err(|error| format!("native Nat prelude failed to build: {error:?}"))?;
    let singleton_root = add_exists_control_theorem(&mut native, prelude.logic)?;
    let mod_lt_compatibility =
        checked_reused_declaration_compatibility(&native, kernel, "Nat.mod_lt")
            .map_err(|error| format!("Nat.mod_lt compatibility failed: {error:?}"))?;
    let native_names = declaration_names(&native);
    let imported_names = declaration_names(kernel);
    let dvd_gcd = native_names
        .get("Nat.dvd_gcd")
        .copied()
        .ok_or("native Nat.dvd_gcd is missing")?;
    let full_closure = native
        .root_declaration_closure(&[dvd_gcd])
        .map_err(|error| format!("full Nat.dvd_gcd closure failed: {error:?}"))?;
    let div_mod_exec = native_names
        .get("Nat.div_mod_exec")
        .copied()
        .ok_or("native Nat.div_mod_exec is missing")?;
    let (reused_div_mod_exec_direct_consumers, missing_div_mod_exec_direct_consumers): (
        Vec<_>,
        Vec<_>,
    ) = full_closure
        .iter()
        .copied()
        .filter(|&name| native.theorem_dependencies(name).contains(&div_mod_exec))
        .map(|name| native.display_name(name).to_string())
        .partition(|name| imported_names.contains_key(name));
    let negative_before = environment_sha256(kernel)?;
    let negative_error = compose_checked_theorem_slice(&native, kernel, &["Nat.dvd_gcd"])
        .expect_err("the unresolved composition control must decline");
    let negative_after = environment_sha256(kernel)?;
    if negative_before != negative_after {
        return Err("failed composition changed the caller kernel".to_owned());
    }
    let singleton_completed = compose_checked_theorem_slice(&native, kernel, &[singleton_root])
        .map_err(|error| format!("singleton inductive composition failed: {error:?}"))?;
    let singleton = singleton_control_json(singleton_completed.receipt());
    let acc_completed = compose_checked_theorem_slice(&native, kernel, &["Acc.inv"])
        .map_err(|error| format!("Acc inductive composition failed: {error:?}"))?;
    let acc = singleton_control_json(acc_completed.receipt());
    let definition_completed =
        compose_checked_theorem_slice(&native, kernel, &["Nat.eq_one_of_dvd_one"])
            .map_err(|error| format!("definition composition failed: {error:?}"))?;
    let definition_receipt = definition_completed.receipt();
    let definition = definition_control_json(definition_receipt);
    let completed = compose_checked_theorem_slice(&native, kernel, &["Nat.add_comm"])
        .map_err(|error| format!("checked composition failed: {error:?}"))?;
    let positive = positive_control_json(completed.receipt());
    let kernel_submissions = receipt_kernel_submissions(singleton_completed.receipt())
        + receipt_kernel_submissions(acc_completed.receipt())
        + receipt_kernel_submissions(definition_receipt)
        + receipt_kernel_submissions(completed.receipt());
    let (composed_kernel, _) = completed.into_parts();
    *kernel = composed_kernel;
    let negative = json!({
        "root": "Nat.dvd_gcd",
        "outcome": "declined",
        "error": format!("{negative_error:?}"),
        "source_closure_count": full_closure.len(),
        "reused_nat_div_mod_exec_direct_consumers": reused_div_mod_exec_direct_consumers,
        "missing_nat_div_mod_exec_direct_consumers": missing_div_mod_exec_direct_consumers,
        "environment_sha256_before": negative_before,
        "environment_sha256_after": negative_after,
    });
    Ok(ControlObservations {
        composition: positive,
        singleton,
        acc,
        definition,
        mod_lt_compatibility: reused_receipt_json(&mod_lt_compatibility),
        negative,
        kernel_submissions,
    })
}

fn receipt_kernel_submissions(receipt: &CheckedTheoremCompositionReceipt) -> usize {
    receipt.added_theorems.len()
        + receipt.added_definitions.len()
        + receipt
            .added_singleton_inductives
            .iter()
            .map(|package| package.constructors.len() + 2)
            .sum::<usize>()
}

fn add_exists_control_theorem(
    kernel: &mut Kernel,
    logic: axeyum_lean_kernel::LogicPrelude,
) -> Result<&'static str, String> {
    let zero = kernel.level_zero();
    let true_type = kernel.const_(logic.true_, vec![]);
    let true_intro = kernel.const_(logic.true_intro, vec![]);
    let exists = kernel.const_(logic.exists_, vec![zero]);
    let anon = kernel.anon();
    let predicate = kernel.lam(anon, true_type, true_type, BinderInfo::Default);
    let exists_true = {
        let applied = kernel.app(exists, true_type);
        kernel.app(applied, predicate)
    };
    let intro = kernel.const_(logic.exists_intro, vec![zero]);
    let proof = [true_type, predicate, true_intro, true_intro]
        .into_iter()
        .fold(intro, |term, argument| kernel.app(term, argument));
    let composition = kernel.name_str(anon, "Composition");
    let name = kernel.name_str(composition, "existsTrue");
    kernel
        .add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty: exists_true,
            value: proof,
        })
        .map_err(|error| format!("Exists control theorem failed: {error:?}"))?;
    Ok("Composition.existsTrue")
}

fn added_digests(rows: &[AddedTheoremReceipt]) -> BTreeMap<&str, &str> {
    rows.iter()
        .map(|row| (row.name.as_str(), row.target_declaration_sha256.as_str()))
        .collect()
}

fn added_footprints(rows: &[AddedTheoremReceipt]) -> BTreeMap<&str, &[String]> {
    rows.iter()
        .map(|row| (row.name.as_str(), row.axiom_footprint.as_slice()))
        .collect()
}

fn singleton_control_json(receipt: &CheckedTheoremCompositionReceipt) -> serde_json::Value {
    json!({
        "roots": receipt.roots,
        "outcome": "composed",
        "added_theorem_names": receipt.added_theorems.iter().map(|row| &row.name).collect::<Vec<_>>(),
        "added_axiom_footprints": added_footprints(&receipt.added_theorems),
        "added_singleton_inductives": singleton_package_rows(receipt),
        "environment_sha256_before": receipt.target_environment_sha256_before,
        "environment_sha256_after": receipt.target_environment_sha256_after,
        "receipt_schema": receipt.schema_version,
        "receipt_sha256": receipt.receipt_sha256,
    })
}

fn definition_control_json(receipt: &CheckedTheoremCompositionReceipt) -> serde_json::Value {
    json!({
        "roots": receipt.roots,
        "source_closure": receipt.source_closure,
        "outcome": "composed",
        "added_definitions": definition_rows(receipt),
        "added_theorem_names": receipt.added_theorems.iter().map(|row| &row.name).collect::<Vec<_>>(),
        "added_axiom_footprints": added_footprints(&receipt.added_theorems),
        "added_singleton_inductives": singleton_package_rows(receipt),
        "reused_declaration_receipts": reused_receipts(&receipt.reused_declarations),
        "environment_sha256_before": receipt.target_environment_sha256_before,
        "environment_sha256_after": receipt.target_environment_sha256_after,
        "receipt_schema": receipt.schema_version,
        "receipt_sha256": receipt.receipt_sha256,
    })
}

fn positive_control_json(receipt: &CheckedTheoremCompositionReceipt) -> serde_json::Value {
    json!({
        "roots": receipt.roots,
        "source_closure": receipt.source_closure,
        "outcome": "composed",
        "reused_dependency_names": receipt.reused_declarations.iter().map(|row| &row.name).collect::<Vec<_>>(),
        "declarations_absent_before": receipt.added_theorems.iter().map(|row| &row.name).collect::<Vec<_>>(),
        "added_theorem_names": receipt.added_theorems.iter().map(|row| &row.name).collect::<Vec<_>>(),
        "added_declaration_sha256": added_digests(&receipt.added_theorems),
        "added_axiom_footprints": added_footprints(&receipt.added_theorems),
        "added_definitions": definition_rows(receipt),
        "added_singleton_inductives": singleton_package_rows(receipt),
        "reused_declaration_receipts": reused_receipts(&receipt.reused_declarations),
        "environment_sha256_before": receipt.target_environment_sha256_before,
        "environment_sha256_after": receipt.target_environment_sha256_after,
        "receipt_schema": receipt.schema_version,
        "receipt_sha256": receipt.receipt_sha256,
    })
}

fn definition_rows(receipt: &CheckedTheoremCompositionReceipt) -> Vec<serde_json::Value> {
    receipt
        .added_definitions
        .iter()
        .map(|row| {
            json!({
                "name": row.name,
                "source_declaration_sha256": row.source_declaration_sha256,
                "target_declaration_sha256": row.target_declaration_sha256,
                "reducibility": row.reducibility,
            })
        })
        .collect()
}

fn singleton_package_rows(receipt: &CheckedTheoremCompositionReceipt) -> Vec<serde_json::Value> {
    receipt
        .added_singleton_inductives
        .iter()
        .map(|row| {
            json!({
                "family": row.family,
                "constructors": row.constructors,
                "recursor": row.recursor,
                "source_declaration_sha256": row.source_declaration_sha256,
                "target_declaration_sha256": row.target_declaration_sha256,
            })
        })
        .collect()
}

fn reused_receipts(rows: &[ReusedDeclarationReceipt]) -> Vec<serde_json::Value> {
    rows.iter().map(reused_receipt_json).collect()
}

fn reused_receipt_json(row: &ReusedDeclarationReceipt) -> serde_json::Value {
    json!({
        "name": row.name,
        "source_declaration_sha256": row.source_declaration_sha256,
        "target_declaration_sha256": row.target_declaration_sha256,
        "source_type_shape_sha256": row.source_type_shape_sha256,
        "target_type_shape_sha256": row.target_type_shape_sha256,
        "compatibility": row.compatibility.as_str(),
    })
}

fn environment_sha256(kernel: &Kernel) -> Result<String, String> {
    let mut entries: Vec<(String, String)> = kernel
        .environment()
        .iter()
        .map(|(&name, _)| {
            Ok((
                kernel.display_name(name).to_string(),
                canonical_declaration_sha256(kernel, name)?,
            ))
        })
        .collect::<Result<_, String>>()?;
    entries.sort();
    let mut encoded = String::new();
    for (name, digest) in entries {
        let _ = writeln!(encoded, "{name}\t{digest}");
    }
    Ok(hex_sha256(encoded.as_bytes()))
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
    required_theorem_dependency_closures: Vec<serde_json::Value>,
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
    let required_theorem_dependency_closures = required_theorem_dependency_closures(
        &native,
        &native_names,
        &imported_names,
        &exact,
        &alpha_type_compatible_content_mismatched,
        &kernel_type_shape_compatible_content_mismatched,
        &type_mismatched,
    )?;
    Ok(OverlapReport {
        native_declarations: native.environment().len(),
        exact,
        alpha_type_compatible_content_mismatched,
        kernel_type_shape_compatible_content_mismatched,
        type_mismatched,
        required_theorem_dependency_closures,
    })
}

#[allow(clippy::too_many_arguments)]
fn required_theorem_dependency_closures(
    native: &Kernel,
    native_names: &BTreeMap<String, axeyum_lean_kernel::NameId>,
    imported_names: &BTreeMap<String, axeyum_lean_kernel::NameId>,
    exact: &[String],
    alpha_compatible: &[String],
    kernel_shape_compatible: &[String],
    type_mismatched: &[serde_json::Value],
) -> Result<Vec<serde_json::Value>, String> {
    let exact: BTreeSet<&str> = exact.iter().map(String::as_str).collect();
    let alpha_compatible: BTreeSet<&str> = alpha_compatible.iter().map(String::as_str).collect();
    let kernel_shape_compatible: BTreeSet<&str> =
        kernel_shape_compatible.iter().map(String::as_str).collect();
    let type_mismatched: BTreeSet<&str> = type_mismatched
        .iter()
        .map(|row| {
            row["name"]
                .as_str()
                .expect("type mismatch rows always carry a name")
        })
        .collect();
    let required = [
        "Nat.add_comm",
        "Nat.dvd_add_iff_right",
        "Nat.dvd_gcd",
        "Nat.eq_one_of_dvd_one",
        "Nat.gcd_dvd_left",
        "Nat.gcd_dvd_right",
        "Nat.gcd_zero_left",
    ];
    required
        .into_iter()
        .map(|theorem| {
            let root = native_names
                .get(theorem)
                .copied()
                .ok_or_else(|| format!("required native theorem missing: {theorem}"))?;
            let dependencies: Vec<String> = native
                .declaration_dependency_closure(root)
                .into_iter()
                .map(|name| native.display_name(name).to_string())
                .collect();
            let mut missing = Vec::new();
            let mut exact_dependencies = Vec::new();
            let mut alpha_dependencies = Vec::new();
            let mut kernel_shape_dependencies = Vec::new();
            let mut type_mismatched_dependencies = Vec::new();
            for dependency in &dependencies {
                if !imported_names.contains_key(dependency) {
                    missing.push(dependency.clone());
                } else if exact.contains(dependency.as_str()) {
                    exact_dependencies.push(dependency.clone());
                } else if alpha_compatible.contains(dependency.as_str()) {
                    alpha_dependencies.push(dependency.clone());
                } else if kernel_shape_compatible.contains(dependency.as_str()) {
                    kernel_shape_dependencies.push(dependency.clone());
                } else if type_mismatched.contains(dependency.as_str()) {
                    type_mismatched_dependencies.push(dependency.clone());
                } else {
                    return Err(format!(
                        "shared dependency was absent from overlap partition: {dependency}"
                    ));
                }
            }
            Ok(json!({
                "theorem": theorem,
                "native_dependency_count": dependencies.len(),
                "missing_dependency_names": missing,
                "exact_dependency_names": exact_dependencies,
                "alpha_type_compatible_dependency_names": alpha_dependencies,
                "kernel_type_shape_compatible_dependency_names": kernel_shape_dependencies,
                "type_mismatched_dependency_names": type_mismatched_dependencies,
            }))
        })
        .collect()
}

fn hex_sha256(bytes: &[u8]) -> String {
    let digest = Sha256::digest(bytes);
    let mut hex = String::with_capacity(digest.len() * 2);
    for byte in digest {
        let _ = write!(hex, "{byte:02x}");
    }
    hex
}
