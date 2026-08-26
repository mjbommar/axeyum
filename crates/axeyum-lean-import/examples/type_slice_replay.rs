//! Train/development-only checked replay for ADR-0484 type slices.

use std::collections::{BTreeMap, BTreeSet};
use std::env;
use std::fs;
use std::io::Cursor;
use std::path::{Path, PathBuf};

use axeyum_lean_import::{
    ImportLimits, generalize_goal_constants, import_ndjson, import_statement_ndjson,
    issue_type_slice_receipt, issue_type_slice_receipt_with_auto_param_normalization,
    select_definition_abstractions_auto_param_binders_v3,
    select_definition_abstractions_auto_param_v2, select_definition_abstractions_v1,
};
use axeyum_lean_kernel::{Declaration, Kernel, Lean4ExportMetadata, NameId, ReducibilityHint};
use serde_json::{Map, Value, json};
use sha2::{Digest, Sha256};

mod statement_reflexivity_support;

use statement_reflexivity_support::{MAX_BINDERS, MAX_CONSTRUCTED_NODES, propose_reflexivity};

const POLICY_V1: &str = "contaminated-definition-boundary-v1";
const POLICY_AUTO_PARAM_V2: &str = "contaminated-definition-boundary-auto-param-v2";
const POLICY_AUTO_PARAM_BINDERS_V3: &str = "contaminated-definition-boundary-auto-param-binders-v3";
const FRESH_TARGET: &str = "Axeyum.Autogenesis.TypeSliceReplay.goal";

#[derive(Debug)]
struct Decline {
    stage: &'static str,
    reason: String,
}

#[derive(Debug)]
struct ReplaySuccess {
    receipt: Value,
    proof_search: Option<Value>,
    proof_outcome: Option<String>,
}

fn main() {
    match run() {
        Ok((output, digest)) => {
            println!("AUTOGENESIS_TYPE_SLICE_REPLAY_OK|{digest}|held_out=0|ledger_writes=0");
            if let Some(path) = output {
                println!("output={}", path.display());
            }
        }
        Err(error) => {
            eprintln!("autogenesis-type-slice-replay: {error}");
            std::process::exit(1);
        }
    }
}

#[allow(clippy::too_many_lines)]
fn run() -> Result<(Option<PathBuf>, String), String> {
    let arguments = parse_arguments()?;
    let streams = if let Some(path) = arguments.get("--streams") {
        PathBuf::from(path)
    } else {
        required_path(&arguments, "--archive")?.join("streams")
    };
    let mapping_path = required_path(&arguments, "--mapping")?;
    let output = arguments.get("--output").map(PathBuf::from);
    let auto_param_v2 = arguments.contains_key("--auto-param-v2");
    let auto_param_binders_v3 = arguments.contains_key("--auto-param-binders-v3");
    let reflexivity_v1 = arguments.contains_key("--reflexivity-v1");
    if reflexivity_v1 && !auto_param_binders_v3 {
        return Err("--reflexivity-v1 requires --auto-param-binders-v3".to_owned());
    }
    if auto_param_v2 && auto_param_binders_v3 {
        return Err("autoParam replay policies are mutually exclusive".to_owned());
    }
    let policy_version = if auto_param_binders_v3 {
        POLICY_AUTO_PARAM_BINDERS_V3
    } else if auto_param_v2 {
        POLICY_AUTO_PARAM_V2
    } else {
        POLICY_V1
    };
    let mapping_bytes = fs::read(&mapping_path)
        .map_err(|error| format!("cannot read {}: {error}", mapping_path.display()))?;
    let mapping: Value = serde_json::from_slice(&mapping_bytes)
        .map_err(|error| format!("mapping is not JSON: {error}"))?;
    let rows = validate_mapping(&mapping)?;
    let population_selection = (mapping.get("kind").and_then(Value::as_str)
        == Some("axeyum-autogenesis-retrieved-induction-type-slice-input"))
    .then(|| {
        json!({
            "source_kind": "axeyum-autogenesis-retrieved-induction-type-slice-input",
            "target_outcomes_accessed": true,
            "selection": "measured type-slice-generalization obstruction rows",
        })
    });

    let mut outcomes = BTreeMap::<String, u64>::new();
    let mut output_rows = Vec::with_capacity(rows.len());
    let mut producer_invocations = 0_u64;
    for (index, row) in rows.iter().enumerate() {
        let artifact = required_string(row, "artifact_file")?;
        if Path::new(artifact)
            .file_name()
            .and_then(|name| name.to_str())
            != Some(artifact)
        {
            return Err(format!("unsafe artifact path {artifact:?}"));
        }
        let target = required_string(row, "target_definition")?;
        let stream_path = streams.join(artifact);
        let stream = fs::read(&stream_path).map_err(|error| {
            format!(
                "cannot read mapped stream {}: {error}",
                stream_path.display()
            )
        })?;
        let stream_sha256 = hex_sha256(&stream);
        let result = replay_row(
            &stream,
            &stream_sha256,
            target,
            auto_param_v2,
            auto_param_binders_v3,
            policy_version,
            reflexivity_v1,
        );
        let (outcome, detail) = match result {
            Ok(success) => {
                let mut detail = json!({ "receipt": success.receipt });
                let outcome = if let (Some(search), Some(outcome)) =
                    (success.proof_search, success.proof_outcome)
                {
                    producer_invocations += 1;
                    detail
                        .as_object_mut()
                        .ok_or_else(|| "row detail is not an object".to_owned())?
                        .insert("proof_search".to_owned(), search);
                    outcome
                } else {
                    "accepted-receipt".to_owned()
                };
                (outcome, detail)
            }
            Err(decline) => {
                let outcome = format!("decline:{}", decline.stage);
                (
                    outcome,
                    json!({ "decline": { "stage": decline.stage, "reason": decline.reason } }),
                )
            }
        };
        *outcomes.entry(outcome.clone()).or_default() += 1;
        let mut output_row = json!({
            "artifact_file": artifact,
            "fact_id": row.get("fact_id").cloned().unwrap_or(Value::Null),
            "family": row.get("family").cloned().unwrap_or(Value::Null),
            "partition": row.get("partition").cloned().unwrap_or(Value::Null),
            "target_definition": target,
            "stream_sha256": stream_sha256,
            "outcome": outcome,
        });
        output_row
            .as_object_mut()
            .ok_or_else(|| "row output is not an object".to_owned())?
            .extend(
                detail
                    .as_object()
                    .ok_or_else(|| "row detail is not an object".to_owned())?
                    .clone(),
            );
        output_rows.push(output_row);
        if (index + 1) % 10 == 0 || index + 1 == rows.len() {
            eprintln!("TYPE_SLICE_REPLAY_PROGRESS|{}/{}", index + 1, rows.len());
        }
    }

    let (observation, digest) = build_observation(
        &output_rows,
        outcomes,
        &mapping_bytes,
        policy_version,
        reflexivity_v1,
        producer_invocations,
        population_selection,
    )?;
    if let Some(path) = &output {
        let mut rendered = serde_json::to_string_pretty(&observation)
            .map_err(|error| format!("cannot render observation: {error}"))?;
        rendered.push('\n');
        fs::write(path, rendered)
            .map_err(|error| format!("cannot write {}: {error}", path.display()))?;
    }
    Ok((output, digest))
}

fn build_observation(
    output_rows: &[Value],
    outcomes: BTreeMap<String, u64>,
    mapping_bytes: &[u8],
    policy_version: &str,
    reflexivity_v1: bool,
    producer_invocations: u64,
    population_selection: Option<Value>,
) -> Result<(Value, String), String> {
    let coverage: Map<String, Value> = outcomes
        .into_iter()
        .map(|(key, count)| (key, Value::from(count)))
        .collect();
    let mut observation = json!({
        "schema_version": 1,
        "kind": "axeyum-autogenesis-checked-type-slice-replay",
        "state": "checked-slice-replay-no-proof-or-ledger-credit",
        "policy_version": policy_version,
        "authority": {
            "partitions_inspected": ["development", "train"],
            "held_out_inspected": false,
            "proof_producers_executed": false,
            "proof_bodies_requested": false,
            "ledger_writes": 0,
            "targets": output_rows.len(),
        },
        "mapping_sha256": hex_sha256(mapping_bytes),
        "coverage": coverage,
        "rows": output_rows,
        "limitations": "A receipt admits only the generalized statement boundary. No proof producer ran, no source fact was proved, held-out remained sealed, and every decline remains uncredited.",
    });
    if reflexivity_v1 {
        let object = observation
            .as_object_mut()
            .ok_or_else(|| "observation is not an object".to_owned())?;
        object.insert(
            "kind".to_owned(),
            json!("axeyum-autogenesis-type-slice-producer-census"),
        );
        object.insert(
            "state".to_owned(),
            json!("diagnostic-fixed-budget-no-ledger-credit"),
        );
        object.insert(
            "producer_policy".to_owned(),
            json!("type-slice-reflexivity-census-v1"),
        );
        object.insert(
            "budget".to_owned(),
            json!({
                "producer": "bounded-pi-equality-reflexivity-v1",
                "max_binders": MAX_BINDERS,
                "max_constructed_nodes": MAX_CONSTRUCTED_NODES,
                "producer_invocations": producer_invocations,
                "retries": 0,
            }),
        );
        object.insert(
            "authority".to_owned(),
            json!({
                "partitions_inspected": ["development", "train"],
                "held_out_inspected": false,
                "proof_producers_executed": true,
                "proof_bodies_requested": false,
                "ledger_writes": 0,
                "targets": output_rows.len(),
            }),
        );
        object.insert(
            "limitations".to_owned(),
            json!("Every row is diagnostic under one fixed reflexivity grammar. No candidate is registered or admitted, held-out remains sealed, and no fact-ledger row changes."),
        );
    }
    if let Some(selection) = population_selection {
        observation
            .as_object_mut()
            .ok_or_else(|| "observation is not an object".to_owned())?
            .insert("population_selection".to_owned(), selection);
    }
    let canonical = serde_json::to_vec(&observation)
        .map_err(|error| format!("cannot serialize observation: {error}"))?;
    let digest = hex_sha256(&canonical);
    observation
        .as_object_mut()
        .ok_or_else(|| "observation is not an object".to_owned())?
        .insert(
            "observation_sha256".to_owned(),
            Value::String(digest.clone()),
        );
    Ok((observation, digest))
}

#[allow(clippy::too_many_lines)]
fn replay_row(
    stream: &[u8],
    stream_sha256: &str,
    target: &str,
    auto_param_v2: bool,
    auto_param_binders_v3: bool,
    policy_version: &str,
    reflexivity_v1: bool,
) -> Result<ReplaySuccess, Decline> {
    let completed = at(
        "source-import",
        import_ndjson(Cursor::new(stream), ImportLimits::default()),
    )?;
    let (mut kernel, report) = completed.into_parts();
    let target_name = find_exact_name(&kernel, target)?;
    let source_goal = match kernel.environment().get(target_name) {
        Some(Declaration::Definition { uparams, value, .. }) if uparams.is_empty() => *value,
        _ => {
            return Err(Decline {
                stage: "source-target",
                reason: "target is not one monomorphic transparent definition".to_owned(),
            });
        }
    };
    let abstractions = at(
        "selection",
        if auto_param_binders_v3 {
            select_definition_abstractions_auto_param_binders_v3(&mut kernel, source_goal)
        } else if auto_param_v2 {
            select_definition_abstractions_auto_param_v2(&mut kernel, source_goal)
        } else {
            select_definition_abstractions_v1(&mut kernel, source_goal)
        },
    )?;
    let generalized = at(
        "generalization",
        generalize_goal_constants(&mut kernel, source_goal, &abstractions),
    )?;
    let arguments: Vec<_> = abstractions
        .iter()
        .map(|binding| kernel.const_(binding.name, binding.levels.clone()))
        .collect();
    let fresh_target = nested_name(&mut kernel, &FRESH_TARGET.split('.').collect::<Vec<_>>());
    if kernel.environment().get(fresh_target).is_some() {
        return Err(Decline {
            stage: "fresh-target",
            reason: format!("reserved target {FRESH_TARGET} already exists"),
        });
    }
    let prop = kernel.sort_zero();
    at(
        "fresh-target",
        kernel.add_declaration(Declaration::Definition {
            name: fresh_target,
            uparams: vec![],
            ty: prop,
            value: generalized.goal,
            hint: ReducibilityHint::Regular(0),
        }),
    )?;
    let metadata = Lean4ExportMetadata::axeyum(report.lean_version.clone());
    let (fresh_stream, normalization) = if auto_param_binders_v3 {
        at(
            "root-export",
            kernel.render_lean4export_ndjson_roots_checked_auto_param_binders(
                &metadata,
                &[fresh_target],
            ),
        )?
    } else if auto_param_v2 {
        at(
            "root-export",
            kernel.render_lean4export_ndjson_roots_checked_auto_param_types(
                &metadata,
                &[fresh_target],
            ),
        )?
    } else {
        (
            at(
                "root-export",
                kernel.render_lean4export_ndjson_roots(&metadata, &[fresh_target]),
            )?,
            axeyum_lean_kernel::AutoParamTypeNormalizationReport {
                normalized_declarations: Vec::new(),
                rewritten_occurrences: 0,
            },
        )
    };
    let fresh = at(
        "fresh-import",
        import_statement_ndjson(
            Cursor::new(fresh_stream),
            ImportLimits::default(),
            FRESH_TARGET,
        ),
    )?;
    let receipt = if normalization.rewritten_occurrences == 0 {
        at(
            "receipt",
            issue_type_slice_receipt(
                &mut kernel,
                &report,
                stream_sha256,
                target_name,
                source_goal,
                &generalized,
                &arguments,
                &fresh,
                policy_version,
            ),
        )?
    } else {
        at(
            "receipt",
            issue_type_slice_receipt_with_auto_param_normalization(
                &mut kernel,
                &report,
                stream_sha256,
                target_name,
                source_goal,
                &generalized,
                &arguments,
                &fresh,
                policy_version,
                &normalization,
            ),
        )?
    };
    let rendered = at("receipt-json", receipt.to_pretty_json())?;
    let receipt = at("receipt-json", serde_json::from_str(&rendered))?;
    let (proof_search, proof_outcome) = if reflexivity_v1 {
        let (search, outcome) = run_reflexivity(fresh);
        (Some(search), Some(outcome))
    } else {
        (None, None)
    };
    Ok(ReplaySuccess {
        receipt,
        proof_search,
        proof_outcome,
    })
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

fn run_reflexivity(fresh: axeyum_lean_import::CompletedStatementImport) -> (Value, String) {
    let (mut kernel, _report, target_name, goal) = fresh.into_parts();
    let candidate = match propose_reflexivity(&mut kernel, goal) {
        Ok(candidate) => candidate,
        Err(detail) => {
            let reason = producer_reason(&detail);
            return (
                json!({
                    "producer": "bounded-pi-equality-reflexivity-v1",
                    "outcome": "producer-decline",
                    "reason": reason,
                    "detail": detail,
                    "max_binders": MAX_BINDERS,
                    "max_constructed_nodes": MAX_CONSTRUCTED_NODES,
                }),
                format!("producer-decline:{reason}"),
            );
        }
    };
    let proof_sha256 = hex_sha256(kernel.render_lean(candidate.proof).as_bytes());
    let candidate_name = nested_name(
        &mut kernel,
        &["Axeyum", "Autogenesis", "TypeSliceReplay", "candidate"],
    );
    if let Err(error) = kernel.add_declaration(Declaration::Theorem {
        name: candidate_name,
        uparams: vec![],
        ty: goal,
        value: candidate.proof,
    }) {
        return (
            json!({
                "producer": "bounded-pi-equality-reflexivity-v1",
                "outcome": "kernel-rejection",
                "reason": "candidate-typecheck-failed",
                "detail": format!("{error:?}"),
                "proof_sha256": proof_sha256,
                "binders": candidate.binders,
                "constructed_nodes": candidate.constructed_nodes,
                "max_binders": MAX_BINDERS,
                "max_constructed_nodes": MAX_CONSTRUCTED_NODES,
            }),
            "kernel-rejection:candidate-typecheck-failed".to_owned(),
        );
    }
    let closure = kernel.declaration_dependency_closure(candidate_name);
    let target_dependency = closure.contains(&target_name);
    let axioms = kernel.axiom_footprint(candidate_name).len();
    let theorem_dependencies = kernel.theorem_dependencies(candidate_name).len();
    let (outcome, reason) = if target_dependency || axioms != 0 || theorem_dependencies != 0 {
        ("assurance-rejection", Some("dependency-audit-failed"))
    } else {
        ("admissible-proof", None)
    };
    let search = json!({
        "producer": "bounded-pi-equality-reflexivity-v1",
        "outcome": outcome,
        "reason": reason,
        "proof_sha256": proof_sha256,
        "binders": candidate.binders,
        "constructed_nodes": candidate.constructed_nodes,
        "max_binders": MAX_BINDERS,
        "max_constructed_nodes": MAX_CONSTRUCTED_NODES,
        "axioms": axioms,
        "theorem_dependencies": theorem_dependencies,
        "target_dependency": target_dependency,
    });
    let key = reason.map_or_else(
        || outcome.to_owned(),
        |reason| format!("{outcome}:{reason}"),
    );
    (search, key)
}

fn at<T, E: std::fmt::Debug>(stage: &'static str, result: Result<T, E>) -> Result<T, Decline> {
    result.map_err(|error| Decline {
        stage,
        reason: format!("{error:?}"),
    })
}

fn find_exact_name(kernel: &Kernel, target: &str) -> Result<NameId, Decline> {
    let matches: Vec<_> = kernel
        .environment()
        .iter()
        .filter_map(|(&name, _)| (kernel.display_name(name).to_string() == target).then_some(name))
        .collect();
    if matches.len() == 1 {
        Ok(matches[0])
    } else {
        Err(Decline {
            stage: "source-target",
            reason: format!("target cardinality is {}", matches.len()),
        })
    }
}

fn validate_mapping(mapping: &Value) -> Result<&[Value], String> {
    let kind = mapping.get("kind").and_then(Value::as_str);
    let legacy = kind == Some("axeyum-autogenesis-reflexivity-coverage-input");
    let measured_obstructions =
        kind == Some("axeyum-autogenesis-retrieved-induction-type-slice-input");
    if (!legacy && !measured_obstructions)
        || mapping.get("state").and_then(Value::as_str) != Some("proof-free-source-input")
        || mapping
            .pointer("/authority/held_out_inspected")
            .and_then(Value::as_bool)
            != Some(false)
        || mapping
            .pointer("/authority/proof_bodies_accessed")
            .and_then(Value::as_bool)
            != Some(false)
        || mapping.pointer("/authority/partitions_inspected")
            != Some(&json!(["development", "train"]))
    {
        return Err("mapping does not preserve the unsealed proof-free authority".to_owned());
    }
    let rows = mapping
        .get("rows")
        .and_then(Value::as_array)
        .ok_or_else(|| "mapping rows are absent".to_owned())?;
    let facts_opened = mapping
        .pointer("/authority/facts_opened")
        .and_then(Value::as_u64)
        .and_then(|value| usize::try_from(value).ok());
    let outcomes_accessed = mapping
        .pointer("/authority/target_outcomes_accessed")
        .and_then(Value::as_bool);
    if rows.is_empty()
        || facts_opened != Some(rows.len())
        || (legacy && (rows.len() != 138 || outcomes_accessed != Some(false)))
        || (measured_obstructions && outcomes_accessed != Some(true))
    {
        return Err("mapping population or outcome-access authority is inconsistent".to_owned());
    }
    let mut artifacts = BTreeSet::new();
    let mut facts = BTreeSet::new();
    let mut targets = BTreeSet::new();
    for row in rows {
        if !matches!(
            row.get("partition").and_then(Value::as_str),
            Some("train" | "development")
        ) {
            return Err("mapping contains a held-out or malformed partition".to_owned());
        }
        let artifact = required_string(row, "artifact_file")?;
        let fact = required_string(row, "fact_id")?;
        let target = required_string(row, "target_definition")?;
        if !artifacts.insert(artifact) || !facts.insert(fact) || !targets.insert(target) {
            return Err("mapping repeats an artifact, fact, or target identity".to_owned());
        }
    }
    Ok(rows)
}

fn parse_arguments() -> Result<BTreeMap<String, String>, String> {
    let mut parsed = BTreeMap::new();
    let mut arguments = env::args().skip(1);
    while let Some(flag) = arguments.next() {
        if matches!(
            flag.as_str(),
            "--auto-param-v2" | "--auto-param-binders-v3" | "--reflexivity-v1"
        ) {
            if parsed.insert(flag.clone(), "true".to_owned()).is_some() {
                return Err(format!("{flag} was supplied more than once"));
            }
            continue;
        }
        if !matches!(
            flag.as_str(),
            "--archive" | "--streams" | "--mapping" | "--output"
        ) {
            return Err(format!("unknown argument {flag}"));
        }
        let value = arguments
            .next()
            .ok_or_else(|| format!("{flag} requires a value"))?;
        if parsed.insert(flag.clone(), value).is_some() {
            return Err(format!("{flag} was supplied more than once"));
        }
    }
    Ok(parsed)
}

fn required_path(arguments: &BTreeMap<String, String>, flag: &str) -> Result<PathBuf, String> {
    arguments
        .get(flag)
        .map(PathBuf::from)
        .ok_or_else(|| format!("missing {flag}"))
}

fn required_string<'a>(row: &'a Value, key: &str) -> Result<&'a str, String> {
    row.get(key)
        .and_then(Value::as_str)
        .filter(|value| !value.is_empty())
        .ok_or_else(|| format!("mapping row has no {key}"))
}

fn nested_name(kernel: &mut Kernel, components: &[&str]) -> NameId {
    let mut name = kernel.anon();
    for component in components {
        name = kernel.name_str(name, *component);
    }
    name
}

fn hex_sha256(bytes: &[u8]) -> String {
    let digest = Sha256::digest(bytes);
    let mut output = String::with_capacity(64);
    for byte in digest {
        use std::fmt::Write;
        write!(output, "{byte:02x}").expect("writing to String cannot fail");
    }
    output
}

#[cfg(test)]
mod tests {
    use super::*;

    fn mapping() -> Value {
        let rows: Vec<_> = (0..138)
            .map(|index| {
                json!({
                    "artifact_file": format!("r{index:03}.ndjson"),
                    "fact_id": format!("F:test-{index:03}"),
                    "family": "control",
                    "partition": if index % 5 == 0 { "development" } else { "train" },
                    "target_definition": format!("Control.r{index:03}"),
                })
            })
            .collect();
        json!({
            "kind": "axeyum-autogenesis-reflexivity-coverage-input",
            "state": "proof-free-source-input",
            "authority": {
                "partitions_inspected": ["development", "train"],
                "held_out_inspected": false,
                "proof_bodies_accessed": false,
                "target_outcomes_accessed": false,
                "facts_opened": 138,
            },
            "rows": rows,
        })
    }

    #[test]
    fn frozen_unsealed_mapping_shape_is_accepted() {
        assert_eq!(
            validate_mapping(&mapping())
                .expect("control must pass")
                .len(),
            138
        );
    }

    #[test]
    fn held_out_authority_is_rejected() {
        let mut value = mapping();
        value["authority"]["held_out_inspected"] = Value::Bool(true);
        assert!(validate_mapping(&value).is_err());
    }

    #[test]
    fn duplicate_population_identity_is_rejected() {
        let mut value = mapping();
        value["rows"][1]["artifact_file"] = value["rows"][0]["artifact_file"].clone();
        assert!(validate_mapping(&value).is_err());
    }

    #[test]
    fn target_outcome_access_is_rejected() {
        let mut value = mapping();
        value["authority"]["target_outcomes_accessed"] = Value::Bool(true);
        assert!(validate_mapping(&value).is_err());
    }

    #[test]
    fn measured_obstruction_population_requires_explicit_outcome_access() {
        let mut value = mapping();
        value["kind"] = json!("axeyum-autogenesis-retrieved-induction-type-slice-input");
        value["rows"] = Value::Array(
            value["rows"]
                .as_array()
                .expect("rows")
                .iter()
                .take(25)
                .cloned()
                .collect(),
        );
        value["authority"]["facts_opened"] = json!(25);
        value["authority"]["target_outcomes_accessed"] = json!(true);
        assert_eq!(validate_mapping(&value).expect("measured input").len(), 25);
        value["authority"]["target_outcomes_accessed"] = json!(false);
        assert!(validate_mapping(&value).is_err());
    }

    #[test]
    fn default_observation_retains_the_historical_no_producer_contract() {
        let (value, _) = build_observation(
            &[],
            BTreeMap::new(),
            b"mapping",
            POLICY_AUTO_PARAM_BINDERS_V3,
            false,
            0,
            None,
        )
        .expect("observation must render");
        assert_eq!(
            value["kind"],
            "axeyum-autogenesis-checked-type-slice-replay"
        );
        assert_eq!(value["authority"]["proof_producers_executed"], false);
        assert!(value.get("producer_policy").is_none());
        assert!(value.get("budget").is_none());
    }

    #[test]
    fn reflexivity_observation_binds_policy_budget_and_invocations() {
        let (value, _) = build_observation(
            &[],
            BTreeMap::new(),
            b"mapping",
            POLICY_AUTO_PARAM_BINDERS_V3,
            true,
            138,
            None,
        )
        .expect("observation must render");
        assert_eq!(
            value["kind"],
            "axeyum-autogenesis-type-slice-producer-census"
        );
        assert_eq!(value["producer_policy"], "type-slice-reflexivity-census-v1");
        assert_eq!(value["budget"]["max_binders"], MAX_BINDERS);
        assert_eq!(value["budget"]["producer_invocations"], 138);
        assert_eq!(value["authority"]["proof_producers_executed"], true);
    }

    #[test]
    fn producer_declines_have_stable_reasons() {
        assert_eq!(
            producer_reason("binder budget exceeded: maximum 8"),
            "binder-budget-exceeded"
        );
        assert_eq!(
            producer_reason("terminal goal is not an exact Eq application"),
            "terminal-not-exact-equality"
        );
        assert_eq!(
            producer_reason("terminal goal is not constant-headed equality"),
            "terminal-not-constant-headed-equality"
        );
    }
}
