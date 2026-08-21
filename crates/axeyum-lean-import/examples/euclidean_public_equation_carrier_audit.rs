//! Audit one dependency layer beneath the two public Euclidean equations.
//!
//! The sealed proof stream is read once into the importer. This example emits
//! declaration identities, theorem dependencies, and axiom footprints only;
//! it never renders expressions or theorem values.

use std::collections::BTreeMap;
use std::fmt::Write as _;
use std::fs;
use std::io::Cursor;
use std::path::PathBuf;

use axeyum_lean_import::{ImportLimits, canonical_declaration_sha256, import_ndjson};
use axeyum_lean_kernel::{Declaration, Kernel};
use serde_json::{Value, json};
use sha2::{Digest, Sha256};

const STREAM_SHA256: &str = "d71692e97b7bae7ab43043ed4490a79b2134650b4bfe4d8e20220693fe033844";
const PLAN_SHA256: &str = "9dd589df594ee950f2f81faa23f3e5622d2e0ac1e1ffd5bedaff9edcfb1903ec";
const POPULATION: [&str; 23] = [
    "Eq.symm",
    "Eq.trans",
    "Nat.div.go.eq_1",
    "Nat.div_rec_fuel_lemma",
    "Nat.lt_succ_self",
    "Nat.modCore_eq",
    "Nat.modCore_eq_mod",
    "_private.Init.Data.Nat.Div.Basic.0.Nat.div.go.fuel_congr",
    "and_false",
    "and_self",
    "congr",
    "congrArg",
    "congrFun'",
    "dif_neg",
    "dif_pos",
    "eq_false",
    "eq_self",
    "eq_true",
    "false_and",
    "ite_cond_eq_false",
    "ite_cond_eq_true",
    "ite_congr",
    "of_eq_true",
];

fn main() {
    if let Err(error) = run() {
        eprintln!("euclidean-public-equation-carrier-audit: {error}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), String> {
    let mut arguments = std::env::args_os().skip(1);
    let path = arguments.next().map(PathBuf::from).ok_or(
        "usage: euclidean_public_equation_carrier_audit \
         <bounded-induction-stream.ndjson>",
    )?;
    if arguments.next().is_some() {
        return Err("usage: euclidean_public_equation_carrier_audit \
             <bounded-induction-stream.ndjson>"
            .to_owned());
    }
    let bytes = fs::read(&path).map_err(|error| error.to_string())?;
    let mut stream_sha256 = String::with_capacity(64);
    for byte in Sha256::digest(&bytes) {
        write!(&mut stream_sha256, "{byte:02x}")
            .expect("writing a digest into a String cannot fail");
    }
    if stream_sha256 != STREAM_SHA256 {
        return Err("proof-bearing stream identity changed".to_owned());
    }
    let completed = import_ndjson(Cursor::new(bytes), ImportLimits::default())
        .map_err(|error| format!("stream import failed: {error:?}"))?;
    if completed.report().axioms != ["propext"] {
        return Err(format!(
            "bounded-induction stream axiom inventory changed: {:?}",
            completed.report().axioms
        ));
    }
    let kernel = completed.kernel();
    let rows = POPULATION
        .iter()
        .map(|name| audit_theorem(kernel, name))
        .collect::<Result<Vec<_>, _>>()?;
    let mut counts = BTreeMap::from([
        ("empty-footprint", 0_u64),
        ("other-assumption-bearing", 0),
        ("propext-bearing", 0),
    ]);
    for row in &rows {
        let classification = row["class"].as_str().ok_or("audit row lacks a class")?;
        *counts
            .get_mut(classification)
            .ok_or("audit row has an unknown class")? += 1;
    }
    let result = json!({
        "schema_version": 1,
        "kind": "axeyum-autogenesis-euclidean-public-equation-carrier-audit-result",
        "state": "public-equation-direct-closure-classified-no-replacement-authority",
        "plan": {
            "path": "artifacts/autogenesis/euclidean-public-equation-carrier-audit-plan-v1.json",
            "sha256": PLAN_SHA256,
        },
        "input": {
            "path": path,
            "sha256": STREAM_SHA256,
            "bytes": 715_764,
            "mode": "0444",
            "stream_axioms": ["propext"],
        },
        "parent_carriers": ["Nat.div_eq", "Nat.mod_eq"],
        "summary": {
            "population": rows.len(),
            "class_counts": counts,
        },
        "rows": rows,
        "authority": {
            "importer_runs": 1,
            "proof_bearing_stream_reads": 1,
            "proof_terms_rendered": 0,
            "theorem_values_rendered": 0,
            "replacement_source_compilations": 0,
            "new_authored_theorem_submissions": 0,
            "exact_target_submissions": 0,
            "executor_invocations": 0,
            "support_theorem_credit": 0,
            "fact_status_changes": 0,
            "evaluation_credit": 0,
            "ledger_writes": 0,
            "retries": 0,
        },
        "limitations": "The audit descends one direct-dependency layer beneath the two public equation carriers. It does not inspect proof material or authorize adapting either equation proof.",
    });
    println!(
        "{}",
        serde_json::to_string_pretty(&result).map_err(|error| error.to_string())?
    );
    Ok(())
}

fn audit_theorem(kernel: &Kernel, expected_name: &str) -> Result<Value, String> {
    let (name, declaration) = kernel
        .environment()
        .iter()
        .find_map(|(&name, declaration)| {
            (kernel.display_name(name).to_string() == expected_name).then_some((name, declaration))
        })
        .ok_or_else(|| format!("preregistered theorem is absent: {expected_name}"))?;
    if !matches!(declaration, Declaration::Theorem { .. }) {
        return Err(format!(
            "preregistered declaration is not a theorem: {expected_name}"
        ));
    }
    let mut footprint = rendered_names(kernel, &kernel.axiom_footprint(name));
    let mut dependencies = rendered_names(kernel, &kernel.theorem_dependencies(name));
    footprint.sort();
    dependencies.sort();
    let classification = if footprint.is_empty() {
        "empty-footprint"
    } else if footprint.iter().any(|axiom| axiom == "propext") {
        "propext-bearing"
    } else {
        "other-assumption-bearing"
    };
    Ok(json!({
        "name": expected_name,
        "declaration_sha256": canonical_declaration_sha256(kernel, name)
            .map_err(|error| error.clone())?,
        "axiom_footprint": footprint,
        "direct_theorem_dependencies": dependencies,
        "class": classification,
    }))
}

fn rendered_names(kernel: &Kernel, names: &[axeyum_lean_kernel::NameId]) -> Vec<String> {
    names
        .iter()
        .map(|&name| kernel.display_name(name).to_string())
        .collect()
}
