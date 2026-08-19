//! Join exact semantic abstractions to statement-side contract demand.

use std::collections::{BTreeMap, BTreeSet, HashSet};
use std::env;
use std::fs;
use std::io::Cursor;
use std::path::PathBuf;

use axeyum_lean_import::{ImportLimits, canonical_declaration_sha256, import_ndjson};
use axeyum_lean_kernel::{Declaration, ExprId, ExprNode, Kernel, NameId};
use serde_json::{Value, json};
use sha2::{Digest, Sha256};

struct Arguments {
    archive: PathBuf,
    producer: PathBuf,
    semantic: PathBuf,
    output: PathBuf,
}

fn main() {
    if let Err(error) = run() {
        eprintln!("semantic-contract-target-census: {error}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), String> {
    let arguments = parse_arguments()?;
    let producer_bytes = fs::read(&arguments.producer).map_err(|error| error.to_string())?;
    let semantic_bytes = fs::read(&arguments.semantic).map_err(|error| error.to_string())?;
    let producer: Value =
        serde_json::from_slice(&producer_bytes).map_err(|error| error.to_string())?;
    let semantic: Value =
        serde_json::from_slice(&semantic_bytes).map_err(|error| error.to_string())?;
    validate_authority(&producer, &semantic)?;
    let producer_rows = producer["rows"]
        .as_array()
        .ok_or_else(|| "producer rows are absent".to_owned())?;
    let by_artifact: BTreeMap<_, _> = producer_rows
        .iter()
        .map(|row| (required_string(row, "artifact_file").to_owned(), row))
        .collect();
    let definitions = semantic["definitions"]
        .as_array()
        .ok_or_else(|| "semantic definitions are absent".to_owned())?;
    let mut rows = Vec::new();
    let mut identity_count = 0_u64;
    for descriptor in definitions {
        if required_string(descriptor, "contract_shape") != "pointwise-function-equation" {
            continue;
        }
        identity_count += 1;
        let artifacts = descriptor["artifacts"]
            .as_array()
            .ok_or_else(|| "definition artifacts are absent".to_owned())?;
        for artifact in artifacts {
            let artifact = artifact
                .as_str()
                .ok_or_else(|| "artifact name is malformed".to_owned())?;
            let producer_row = by_artifact
                .get(artifact)
                .ok_or_else(|| format!("producer row {artifact} is absent"))?;
            let stream = fs::read(arguments.archive.join("streams").join(artifact))
                .map_err(|error| format!("cannot read {artifact}: {error}"))?;
            let completed = import_ndjson(Cursor::new(stream), ImportLimits::default())
                .map_err(|error| format!("cannot import {artifact}: {error:?}"))?;
            let (kernel, _) = completed.into_parts();
            rows.push(describe_row(&kernel, descriptor, producer_row)?);
            eprintln!("CONTRACT_TARGET_CENSUS_PROGRESS|{}", rows.len());
        }
    }
    if identity_count != 15 || rows.len() != 50 {
        return Err(format!(
            "expected 15 identities/50 bindings, found {identity_count}/{}",
            rows.len()
        ));
    }
    rows.sort_by(|left, right| {
        required_string(left, "artifact_file").cmp(required_string(right, "artifact_file"))
    });
    let eligible = rows
        .iter()
        .filter(|row| {
            row["equation_contract"]["all_nonrecursive_dependencies_retained"] == json!(true)
        })
        .count();
    let mut output = json!({
        "schema_version": 1,
        "kind": "axeyum-autogenesis-semantic-contract-target-census",
        "state": "selection-diagnostic-no-contract-proof-or-ledger-credit",
        "source": {
            "producer_file_sha256": hex_sha256(&producer_bytes),
            "producer_observation_sha256": producer["observation_sha256"],
            "semantic_file_sha256": hex_sha256(&semantic_bytes),
            "semantic_observation_sha256": semantic["observation_sha256"],
        },
        "authority": {
            "partitions_inspected": ["development", "train"],
            "held_out_inspected": false,
            "proof_bodies_inspected": false,
            "contracts_generated": 0,
            "producer_invocations": 0,
            "ledger_writes": 0,
        },
        "population": {
            "pointwise_definition_identities": identity_count,
            "affected_rows": rows.len(),
            "direct_equation_environment_eligible_rows": eligible,
        },
        "rows": rows,
        "limitations": "Eligibility means only that every nonrecursive constant named directly by the transparent definition body is already retained in the proof-free slice. It does not establish that the equation is minimal, target-useful, axiom-free after witness checking, or sufficient to prove the statement.",
    });
    let digest = canonical_digest(&output)?;
    output["observation_sha256"] = json!(digest);
    let mut rendered = serde_json::to_string_pretty(&output).map_err(|error| error.to_string())?;
    rendered.push('\n');
    fs::write(&arguments.output, rendered).map_err(|error| error.to_string())?;
    println!(
        "AUTOGENESIS_CONTRACT_TARGET_CENSUS_OK|{digest}|identities=15|rows=50|eligible={eligible}|held_out=0|ledger_writes=0"
    );
    Ok(())
}

fn describe_row(kernel: &Kernel, descriptor: &Value, row: &Value) -> Result<Value, String> {
    let source_name = required_string(descriptor, "name");
    let source = find_name(kernel, source_name)?;
    if canonical_declaration_sha256(kernel, source)?
        != required_string(descriptor, "source_content_sha256")
    {
        return Err(format!("source identity changed for {source_name}"));
    }
    let (source_type, source_value) = match kernel.environment().get(source) {
        Some(Declaration::Definition { ty, value, .. }) => (*ty, *value),
        _ => return Err(format!("{source_name} is not a definition")),
    };
    let target_name = row
        .pointer("/receipt/source/target")
        .and_then(Value::as_str)
        .ok_or_else(|| "target name is absent".to_owned())?;
    let target = find_name(kernel, target_name)?;
    let goal = match kernel.environment().get(target) {
        Some(Declaration::Definition { value, .. }) => *value,
        _ => return Err(format!("{target_name} is not a definition")),
    };
    let direct = direct_constants(kernel, source_value);
    let retained: BTreeSet<_> = row["receipt"]["retained"]
        .as_array()
        .ok_or_else(|| "retained inventory is absent".to_owned())?
        .iter()
        .map(|item| required_string(item, "name").to_owned())
        .collect();
    let mut dependencies = Vec::new();
    let mut missing = Vec::new();
    let mut recursive = false;
    for dependency in direct {
        let rendered = kernel.display_name(dependency).to_string();
        if dependency == source {
            recursive = true;
            continue;
        }
        let is_retained = retained.contains(&rendered);
        if !is_retained {
            missing.push(rendered.clone());
        }
        let declaration = kernel
            .environment()
            .get(dependency)
            .ok_or_else(|| "direct dependency disappeared".to_owned())?;
        dependencies.push(json!({
            "name": rendered,
            "kind": declaration_kind(declaration),
            "retained": is_retained,
        }));
    }
    dependencies
        .sort_by(|left, right| required_string(left, "name").cmp(required_string(right, "name")));
    missing.sort();
    let (_, terminal) = leading_pis(kernel, goal);
    let (terminal_head, terminal_arguments) = app_spine(kernel, terminal);
    let relation = match kernel.expr_node(terminal_head) {
        ExprNode::Const(name, _) => kernel.display_name(*name).to_string(),
        _ => String::new(),
    };
    let source_argument_positions: Vec<_> = terminal_arguments
        .iter()
        .enumerate()
        .filter_map(|(index, expression)| {
            contains_const(kernel, *expression, source).then_some(index)
        })
        .collect();
    Ok(json!({
        "artifact_file": required_string(row, "artifact_file"),
        "fact_id": required_string(row, "fact_id"),
        "family": required_string(row, "family"),
        "partition": required_string(row, "partition"),
        "source_name": source_name,
        "source_content_sha256": required_string(descriptor, "source_content_sha256"),
        "source_type": kernel.render_lean(source_type),
        "source_value": kernel.render_lean(source_value),
        "source_value_nodes": descriptor["value_expression_nodes"],
        "source_axiom_footprint": descriptor["axiom_footprint"],
        "source_direct_theorem_dependencies": descriptor["direct_theorem_dependencies"],
        "goal": kernel.render_lean(goal),
        "terminal_relation": relation,
        "terminal_source_argument_positions": source_argument_positions,
        "source_occurrences": row["receipt"]["abstractions"].as_array().and_then(|items| items.iter().find(|item| required_string(item, "source_name") == source_name)).map_or(json!(0), |item| item["source_occurrences"].clone()),
        "abstraction_count": row["receipt"]["abstractions"].as_array().map_or(0, Vec::len),
        "equation_contract": {
            "self_recursive": recursive,
            "direct_nonrecursive_dependencies": dependencies,
            "missing_from_proof_free_slice": missing,
            "all_nonrecursive_dependencies_retained": missing.is_empty(),
        },
    }))
}

fn direct_constants(kernel: &Kernel, root: ExprId) -> BTreeSet<NameId> {
    let mut output = BTreeSet::new();
    let mut seen = HashSet::new();
    let mut pending = vec![root];
    while let Some(expression) = pending.pop() {
        if !seen.insert(expression) {
            continue;
        }
        match kernel.expr_node(expression) {
            ExprNode::Const(name, _) => {
                output.insert(*name);
            }
            ExprNode::Proj(_, _, value) => pending.push(*value),
            ExprNode::App(function, argument)
            | ExprNode::Lam(_, function, argument, _)
            | ExprNode::Pi(_, function, argument, _) => pending.extend([*function, *argument]),
            ExprNode::Let(_, ty, value, body) => pending.extend([*ty, *value, *body]),
            ExprNode::BVar(_) | ExprNode::FVar(_) | ExprNode::Sort(_) | ExprNode::Lit(_) => {}
        }
    }
    output
}

fn contains_const(kernel: &Kernel, root: ExprId, needle: NameId) -> bool {
    direct_constants(kernel, root).contains(&needle)
}

fn leading_pis(kernel: &Kernel, mut expression: ExprId) -> (usize, ExprId) {
    let mut count = 0;
    while let ExprNode::Pi(_, _, body, _) = kernel.expr_node(expression) {
        count += 1;
        expression = *body;
    }
    (count, expression)
}

fn app_spine(kernel: &Kernel, mut expression: ExprId) -> (ExprId, Vec<ExprId>) {
    let mut arguments = Vec::new();
    while let ExprNode::App(function, argument) = kernel.expr_node(expression) {
        arguments.push(*argument);
        expression = *function;
    }
    arguments.reverse();
    (expression, arguments)
}

fn find_name(kernel: &Kernel, rendered: &str) -> Result<NameId, String> {
    let matches: Vec<_> = kernel
        .environment()
        .iter()
        .filter_map(|(&name, _)| {
            (kernel.display_name(name).to_string() == rendered).then_some(name)
        })
        .collect();
    match matches.as_slice() {
        [name] => Ok(*name),
        _ => Err(format!("{rendered} occurs {} times", matches.len())),
    }
}

fn declaration_kind(declaration: &Declaration) -> &'static str {
    match declaration {
        Declaration::Axiom { .. } => "axiom",
        Declaration::Definition { .. } => "definition",
        Declaration::Theorem { .. } => "theorem",
        Declaration::Opaque { .. } => "opaque",
        Declaration::Inductive { .. } => "inductive",
        Declaration::Constructor { .. } => "constructor",
        Declaration::Recursor { .. } => "recursor",
        Declaration::Quotient { .. } => "quotient",
    }
}

fn validate_authority(producer: &Value, semantic: &Value) -> Result<(), String> {
    if producer["authority"]["held_out_inspected"] != json!(false)
        || semantic["authority"]["held_out_inspected"] != json!(false)
        || producer["authority"]["ledger_writes"] != json!(0)
        || semantic["authority"]["ledger_writes"] != json!(0)
    {
        return Err("source authority changed".to_owned());
    }
    Ok(())
}

fn parse_arguments() -> Result<Arguments, String> {
    let mut values = BTreeMap::new();
    let mut arguments = env::args().skip(1);
    while let Some(flag) = arguments.next() {
        if !matches!(
            flag.as_str(),
            "--archive" | "--producer" | "--semantic" | "--output"
        ) {
            return Err(format!("unknown argument {flag}"));
        }
        let value = arguments
            .next()
            .ok_or_else(|| format!("{flag} requires a value"))?;
        if values.insert(flag.clone(), value).is_some() {
            return Err(format!("duplicate {flag}"));
        }
    }
    Ok(Arguments {
        archive: required_path(&values, "--archive")?,
        producer: required_path(&values, "--producer")?,
        semantic: required_path(&values, "--semantic")?,
        output: required_path(&values, "--output")?,
    })
}

fn required_path(values: &BTreeMap<String, String>, flag: &str) -> Result<PathBuf, String> {
    values
        .get(flag)
        .map(PathBuf::from)
        .ok_or_else(|| format!("missing {flag}"))
}
fn required_string<'a>(value: &'a Value, field: &str) -> &'a str {
    value.get(field).and_then(Value::as_str).unwrap_or("")
}
fn canonical_digest(value: &Value) -> Result<String, String> {
    serde_json::to_vec(value)
        .map(|bytes| hex_sha256(&bytes))
        .map_err(|error| error.to_string())
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
    use super::validate_authority;
    use serde_json::json;

    fn source() -> serde_json::Value {
        json!({"authority": {"held_out_inspected": false, "ledger_writes": 0}})
    }

    #[test]
    fn source_authority_accepts_only_sealed_zero_write_inputs() {
        assert!(validate_authority(&source(), &source()).is_ok());
        let mut held_out = source();
        held_out["authority"]["held_out_inspected"] = json!(true);
        assert!(validate_authority(&held_out, &source()).is_err());
        let mut credited = source();
        credited["authority"]["ledger_writes"] = json!(1);
        assert!(validate_authority(&source(), &credited).is_err());
    }
}
