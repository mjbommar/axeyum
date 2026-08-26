//! Classify isolated proof-free statement streams through the bounded
//! reflexivity producer and independent kernel without granting ledger credit.

use std::collections::BTreeMap;
use std::fmt::Write;
use std::fs::File;
use std::io::BufReader;
use std::path::{Path, PathBuf};

use axeyum_lean_import::{
    CompletedStatementImport, ImportLimits, StatementImportError, import_statement_ndjson,
};
use axeyum_lean_kernel::{Declaration, Kernel, NameId};
use serde_json::{Value, json};
use sha2::{Digest, Sha256};

mod statement_reflexivity_support;

use statement_reflexivity_support::{MAX_BINDERS, MAX_CONSTRUCTED_NODES, propose_reflexivity};

fn sha256(text: &str) -> String {
    Sha256::digest(text.as_bytes())
        .iter()
        .fold(String::with_capacity(64), |mut output, byte| {
            write!(output, "{byte:02x}").expect("writing to a String cannot fail");
            output
        })
}

fn required_string<'a>(value: &'a Value, field: &str) -> Result<&'a str, String> {
    value
        .get(field)
        .and_then(Value::as_str)
        .filter(|text| !text.is_empty())
        .ok_or_else(|| format!("mapping row lacks nonempty {field:?}"))
}

fn candidate_name(kernel: &mut Kernel) -> NameId {
    let root = kernel.anon();
    let axeyum = kernel.name_str(root, "Axeyum");
    let autogenesis = kernel.name_str(axeyum, "Autogenesis");
    kernel.name_str(autogenesis, "CoverageCandidate")
}

fn producer_reason(detail: &str) -> &'static str {
    if detail.starts_with("binder budget exceeded") {
        "binder-budget-exceeded"
    } else if detail == "terminal goal is not constant-headed equality" {
        "terminal-not-constant-headed-equality"
    } else if detail == "terminal goal is not an exact Eq application" {
        "terminal-not-exact-equality"
    } else if detail.starts_with("required declaration") {
        "required-declaration-unavailable"
    } else if detail.starts_with("construction budget exceeded") {
        "construction-budget-exceeded"
    } else {
        "unclassified-producer-decline"
    }
}

fn adapter_reason(error: &StatementImportError) -> &'static str {
    match error {
        StatementImportError::Import(_) => "wire-or-kernel-import-failed",
        StatementImportError::TargetCardinality { .. } => "target-cardinality",
        StatementImportError::TargetNotDefinition { .. } => "target-not-definition",
        StatementImportError::TargetUniverseParameters { .. } => "target-universe-parameters",
        StatementImportError::DuplicateCandidate => "duplicate-candidate",
        StatementImportError::CandidateIsTarget { .. } => "candidate-is-target",
        StatementImportError::CandidateCardinality { .. } => "candidate-cardinality",
        StatementImportError::CandidateHasAxioms { .. } => "candidate-has-axioms",
        StatementImportError::TrustedDeclaration { .. } => "trusted-declaration",
        StatementImportError::GoalNotProp { .. } => "goal-not-prop",
    }
}

type Row = serde_json::Map<String, Value>;
type DynError = Box<dyn std::error::Error>;

fn load_inputs() -> Result<(PathBuf, Value), DynError> {
    let mut args = std::env::args_os().skip(1);
    let artifact_root = args
        .next()
        .map(PathBuf::from)
        .ok_or("usage: statement_reflexivity_coverage <artifact-directory> <mapping.json>")?;
    let mapping_path = args
        .next()
        .map(PathBuf::from)
        .ok_or("usage: statement_reflexivity_coverage <artifact-directory> <mapping.json>")?;
    if args.next().is_some() || !artifact_root.is_dir() {
        return Err(
            "usage: statement_reflexivity_coverage <artifact-directory> <mapping.json>".into(),
        );
    }
    let mapping: Value = serde_json::from_reader(BufReader::new(File::open(mapping_path)?))?;
    if mapping.get("schema_version").and_then(Value::as_u64) != Some(1)
        || mapping.get("kind").and_then(Value::as_str)
            != Some("axeyum-autogenesis-reflexivity-coverage-input")
        || mapping.get("state").and_then(Value::as_str) != Some("proof-free-source-input")
    {
        return Err("coverage mapping schema identity is invalid".into());
    }
    let mapping_rows = mapping
        .get("rows")
        .and_then(Value::as_array)
        .ok_or("coverage mapping rows are absent")?;
    if mapping_rows.len() != 138 {
        return Err(format!("expected 138 mapped targets, found {}", mapping_rows.len()).into());
    }
    Ok((artifact_root, mapping))
}

fn decline(mut row: Row, outcome: &str, reason: &str, detail: &str) -> (Value, String) {
    row.insert("outcome".into(), json!(outcome));
    row.insert("reason".into(), json!(reason));
    row.insert("detail".into(), json!(detail));
    (Value::Object(row), format!("{outcome}:{reason}"))
}

fn classify_admitted(
    completed: CompletedStatementImport,
    target: &str,
    mut row: Row,
) -> Result<(Value, String), DynError> {
    let (mut kernel, report, target_name, goal) = completed.into_parts();
    let rendered_goal = kernel.render_lean(goal);
    row.insert("goal_sha256".into(), json!(sha256(&rendered_goal)));
    row.insert(
        "declarations".into(),
        json!(report.declaration_identities.len()),
    );
    row.insert("axioms".into(), json!(report.axiom_identities.len()));
    let identity = report
        .declaration_identities
        .iter()
        .find(|identity| identity.name == target)
        .ok_or("admitted target identity disappeared")?;
    row.insert(
        "target_content_sha256".into(),
        json!(identity.content_sha256),
    );
    let candidate = match propose_reflexivity(&mut kernel, goal) {
        Ok(candidate) => candidate,
        Err(detail) => {
            let reason = producer_reason(&detail);
            return Ok(decline(row, "producer-decline", reason, &detail));
        }
    };
    let rendered_proof = kernel.render_lean(candidate.proof);
    row.insert("proof_sha256".into(), json!(sha256(&rendered_proof)));
    row.insert("binders".into(), json!(candidate.binders));
    row.insert(
        "constructed_nodes".into(),
        json!(candidate.constructed_nodes),
    );
    let name = candidate_name(&mut kernel);
    if let Err(error) = kernel.add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty: goal,
        value: candidate.proof,
    }) {
        return Ok(decline(
            row,
            "kernel-rejection",
            "candidate-typecheck-failed",
            &format!("{error:?}"),
        ));
    }
    let closure = kernel.declaration_dependency_closure(name);
    let target_dependency = closure.contains(&target_name);
    let axioms = kernel.axiom_footprint(name).len();
    let theorem_dependencies = kernel.theorem_dependencies(name).len();
    row.insert("axioms".into(), json!(axioms));
    row.insert("theorem_dependencies".into(), json!(theorem_dependencies));
    row.insert("target_dependency".into(), json!(target_dependency));
    if target_dependency || axioms != 0 || theorem_dependencies != 0 {
        row.insert("outcome".into(), json!("assurance-rejection"));
        row.insert("reason".into(), json!("dependency-audit-failed"));
        Ok((
            Value::Object(row),
            "assurance-rejection:dependency-audit-failed".into(),
        ))
    } else {
        row.insert("outcome".into(), json!("admissible-proof"));
        row.insert("reason".into(), Value::Null);
        Ok((Value::Object(row), "admissible-proof".into()))
    }
}

fn classify_row(artifact_root: &Path, mapped: &Value) -> Result<(Value, String), DynError> {
    let fact_id = required_string(mapped, "fact_id")?;
    let family = required_string(mapped, "family")?;
    let partition = required_string(mapped, "partition")?;
    let target = required_string(mapped, "target_definition")?;
    let artifact_file = required_string(mapped, "artifact_file")?;
    if !matches!(partition, "train" | "development")
        || Path::new(artifact_file).is_absolute()
        || Path::new(artifact_file).components().count() != 1
    {
        return Err("sealed partition or unsafe artifact path entered coverage".into());
    }
    let base = json!({
        "fact_id": fact_id,
        "family": family,
        "partition": partition,
        "target_definition": target,
        "statement_sha256": required_string(mapped, "statement_sha256")?,
        "artifact_file": artifact_file,
        "executor_budget_consumed": 0,
        "ledger_writes": 0,
    });
    let row = base
        .as_object()
        .cloned()
        .ok_or("row base is not an object")?;
    match import_statement_ndjson(
        BufReader::new(File::open(artifact_root.join(artifact_file))?),
        ImportLimits::default(),
        target,
    ) {
        Ok(completed) => classify_admitted(completed, target, row),
        Err(error) => {
            let reason = adapter_reason(&error);
            Ok(decline(
                row,
                "adapter-rejection",
                reason,
                &error.to_string(),
            ))
        }
    }
}

fn main() -> Result<(), DynError> {
    let (artifact_root, mapping) = load_inputs()?;
    let mapping_rows = mapping["rows"]
        .as_array()
        .ok_or("coverage mapping rows are absent")?;
    let mut rows = Vec::with_capacity(mapping_rows.len());
    let mut counts: BTreeMap<String, usize> = BTreeMap::new();
    for mapped in mapping_rows {
        let (row, key) = classify_row(&artifact_root, mapped)?;
        *counts.entry(key).or_default() += 1;
        rows.push(row);
    }

    let output = json!({
        "schema_version": 1,
        "kind": "axeyum-autogenesis-reflexivity-coverage-observation",
        "state": "diagnostic-no-ledger-credit",
        "input_sha256": required_string(&mapping, "input_sha256")?,
        "budget": {
            "max_binders": MAX_BINDERS,
            "max_constructed_nodes": MAX_CONSTRUCTED_NODES,
            "executor_invocations": 0,
            "ledger_writes": 0,
        },
        "coverage": counts,
        "rows": rows,
    });
    println!("{}", serde_json::to_string_pretty(&output)?);
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::{adapter_reason, producer_reason};
    use axeyum_lean_import::StatementImportError;

    #[test]
    fn producer_declines_have_stable_stage_reasons() {
        assert_eq!(
            producer_reason("terminal goal is not an exact Eq application"),
            "terminal-not-exact-equality"
        );
        assert_eq!(
            producer_reason("binder budget exceeded: maximum 8"),
            "binder-budget-exceeded"
        );
    }

    #[test]
    fn adapter_declines_have_stable_stage_reasons() {
        assert_eq!(
            adapter_reason(&StatementImportError::TrustedDeclaration {
                name: "answer".into(),
                kind: axeyum_lean_import::DeclarationKind::Theorem,
            }),
            "trusted-declaration"
        );
        assert_eq!(
            adapter_reason(&StatementImportError::GoalNotProp {
                target: "target".into(),
            }),
            "goal-not-prop"
        );
    }
}
