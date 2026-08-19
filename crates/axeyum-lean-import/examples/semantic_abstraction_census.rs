//! Kernel-backed census of exact definition identities abstracted by type slices.

use std::collections::{BTreeMap, BTreeSet, HashSet};
use std::env;
use std::fs;
use std::io::Cursor;
use std::path::PathBuf;

use axeyum_lean_import::{ImportLimits, canonical_declaration_sha256, import_ndjson};
use axeyum_lean_kernel::{Declaration, ExprId, ExprNode, Kernel, NameId};
use serde_json::{Map, Value, json};
use sha2::{Digest, Sha256};

#[derive(Debug, Clone)]
struct Aggregate {
    name: String,
    source_content_sha256: String,
    instantiated_type_sha256: String,
    universe_sha256: Vec<String>,
    first_artifact: String,
    bindings: u64,
    source_occurrences: u64,
    artifacts: BTreeSet<String>,
    facts: BTreeSet<String>,
    families: BTreeSet<String>,
}

#[derive(Debug)]
struct Arguments {
    archive: PathBuf,
    observation: PathBuf,
    output: Option<PathBuf>,
}

fn main() {
    match run() {
        Ok((digest, output)) => {
            println!(
                "AUTOGENESIS_SEMANTIC_ABSTRACTION_CENSUS_OK|{digest}|identities=32|names=30|bindings=152|held_out=0|ledger_writes=0"
            );
            if let Some(output) = output {
                println!("output={}", output.display());
            }
        }
        Err(error) => {
            eprintln!("autogenesis-semantic-abstraction-census: {error}");
            std::process::exit(1);
        }
    }
}

#[allow(clippy::too_many_lines)]
fn run() -> Result<(String, Option<PathBuf>), String> {
    let arguments = parse_arguments()?;
    let observation_bytes = fs::read(&arguments.observation).map_err(|error| {
        format!(
            "cannot read observation {}: {error}",
            arguments.observation.display()
        )
    })?;
    let observation: Value = serde_json::from_slice(&observation_bytes)
        .map_err(|error| format!("observation is not JSON: {error}"))?;
    let rows = validate_observation(&observation)?;
    let mut aggregates = collect_aggregates(rows)?;
    if aggregates.len() != 32 {
        return Err(format!(
            "expected 32 exact abstraction identities, found {}",
            aggregates.len()
        ));
    }

    let mut artifacts = BTreeMap::<String, Vec<String>>::new();
    for (key, aggregate) in &aggregates {
        artifacts
            .entry(aggregate.first_artifact.clone())
            .or_default()
            .push(key.clone());
    }
    let mut descriptors = Vec::with_capacity(aggregates.len());
    let artifact_count = artifacts.len();
    for (index, (artifact, keys)) in artifacts.into_iter().enumerate() {
        let stream_path = arguments.archive.join("streams").join(&artifact);
        let stream = fs::read(&stream_path)
            .map_err(|error| format!("cannot read {}: {error}", stream_path.display()))?;
        let completed = import_ndjson(Cursor::new(stream), ImportLimits::default())
            .map_err(|error| format!("cannot import {artifact}: {error:?}"))?;
        let (mut kernel, _) = completed.into_parts();
        for key in keys {
            let aggregate = aggregates
                .remove(&key)
                .ok_or_else(|| "abstraction aggregate disappeared".to_owned())?;
            descriptors.push(describe(&mut kernel, &aggregate)?);
        }
        eprintln!(
            "SEMANTIC_ABSTRACTION_CENSUS_PROGRESS|{}/{}",
            index + 1,
            artifact_count
        );
    }
    if !aggregates.is_empty() {
        return Err("not every abstraction identity was described".to_owned());
    }
    descriptors.sort_by(|left, right| {
        required_string(left, "name")
            .cmp(required_string(right, "name"))
            .then_with(|| {
                required_string(left, "source_content_sha256")
                    .cmp(required_string(right, "source_content_sha256"))
            })
    });

    let unique_names: BTreeSet<_> = descriptors
        .iter()
        .map(|row| required_string(row, "name").to_owned())
        .collect();
    let variant_names: Vec<_> = unique_names
        .iter()
        .filter(|name| {
            descriptors
                .iter()
                .filter(|row| required_string(row, "name") == name.as_str())
                .count()
                > 1
        })
        .cloned()
        .collect();
    let mut classes = BTreeMap::<String, u64>::new();
    for row in &descriptors {
        *classes
            .entry(required_string(row, "contract_shape").to_owned())
            .or_default() += row["bindings"]
            .as_u64()
            .ok_or_else(|| "descriptor binding count is malformed".to_owned())?;
    }
    let class_json: Map<String, Value> = classes
        .into_iter()
        .map(|(name, count)| (name, Value::from(count)))
        .collect();
    let mut output = json!({
        "schema_version": 1,
        "kind": "axeyum-autogenesis-semantic-abstraction-census",
        "state": "diagnostic-no-contract-or-ledger-credit",
        "source": {
            "producer_observation_file_sha256": hex_sha256(&observation_bytes),
            "producer_observation_sha256": observation["observation_sha256"],
            "type_slice_policy": observation["policy_version"],
            "producer_policy": observation["producer_policy"],
        },
        "authority": {
            "partitions_inspected": ["development", "train"],
            "held_out_inspected": false,
            "proof_bodies_exposed_to_contracts_or_producers": false,
            "contracts_generated": 0,
            "ledger_writes": 0,
        },
        "population": {
            "abstracted_rows": 114,
            "bindings": 152,
            "source_occurrences": 244,
            "rendered_names": unique_names.len(),
            "exact_definition_identities": descriptors.len(),
            "variant_names": variant_names,
            "bindings_by_contract_shape": class_json,
        },
        "definitions": descriptors,
        "limitations": "The census classifies exact source definition identities and their normalized trusted closures. It generates no semantic contract, proof, operation, or ledger credit.",
    });
    let digest = hex_sha256(
        &serde_json::to_vec(&output).map_err(|error| format!("cannot hash output: {error}"))?,
    );
    output
        .as_object_mut()
        .ok_or_else(|| "output is not an object".to_owned())?
        .insert("observation_sha256".to_owned(), json!(digest));
    if let Some(path) = &arguments.output {
        let mut rendered = serde_json::to_string_pretty(&output)
            .map_err(|error| format!("cannot render output: {error}"))?;
        rendered.push('\n');
        fs::write(path, rendered)
            .map_err(|error| format!("cannot write {}: {error}", path.display()))?;
    }
    Ok((digest, arguments.output))
}

fn collect_aggregates(rows: &[Value]) -> Result<BTreeMap<String, Aggregate>, String> {
    let mut output = BTreeMap::<String, Aggregate>::new();
    let mut abstracted_artifacts = BTreeSet::new();
    for row in rows {
        let artifact = required_string(row, "artifact_file");
        let fact = required_string(row, "fact_id");
        let family = required_string(row, "family");
        if artifact.is_empty() || fact.is_empty() || family.is_empty() {
            return Err("producer row identity is malformed".to_owned());
        }
        let abstractions = row
            .pointer("/receipt/abstractions")
            .and_then(Value::as_array)
            .ok_or_else(|| format!("{artifact} has no abstraction inventory"))?;
        if !abstractions.is_empty() {
            abstracted_artifacts.insert(artifact.to_owned());
        }
        for abstraction in abstractions {
            let name = required_string(abstraction, "source_name");
            if name.is_empty() {
                return Err("abstraction name is malformed".to_owned());
            }
            let source_content_sha256 = required_hash(abstraction, "source_content_sha256")?;
            let instantiated_type_sha256 = required_hash(abstraction, "instantiated_type_sha256")?;
            let universes: Vec<String> = abstraction
                .get("universe_sha256")
                .and_then(Value::as_array)
                .ok_or_else(|| "abstraction universes are absent".to_owned())?
                .iter()
                .map(|value| {
                    value
                        .as_str()
                        .filter(|digest| is_sha256(digest))
                        .map(str::to_owned)
                        .ok_or_else(|| "abstraction universe identity is malformed".to_owned())
                })
                .collect::<Result<_, _>>()?;
            let key = format!(
                "{name}|{source_content_sha256}|{instantiated_type_sha256}|{}",
                universes.join(",")
            );
            let aggregate = output.entry(key).or_insert_with(|| Aggregate {
                name: name.to_owned(),
                source_content_sha256: source_content_sha256.to_owned(),
                instantiated_type_sha256: instantiated_type_sha256.to_owned(),
                universe_sha256: universes.clone(),
                first_artifact: artifact.to_owned(),
                bindings: 0,
                source_occurrences: 0,
                artifacts: BTreeSet::new(),
                facts: BTreeSet::new(),
                families: BTreeSet::new(),
            });
            aggregate.bindings += 1;
            aggregate.source_occurrences += abstraction["source_occurrences"]
                .as_u64()
                .ok_or_else(|| "abstraction occurrence count is malformed".to_owned())?;
            aggregate.artifacts.insert(artifact.to_owned());
            aggregate.facts.insert(fact.to_owned());
            aggregate.families.insert(family.to_owned());
        }
    }
    if abstracted_artifacts.len() != 114 {
        return Err(format!(
            "expected 114 abstracted rows, found {}",
            abstracted_artifacts.len()
        ));
    }
    let bindings: u64 = output.values().map(|row| row.bindings).sum();
    let occurrences: u64 = output.values().map(|row| row.source_occurrences).sum();
    if bindings != 152 || occurrences != 244 {
        return Err(format!(
            "abstraction totals changed: bindings={bindings}, occurrences={occurrences}"
        ));
    }
    Ok(output)
}

fn describe(kernel: &mut Kernel, aggregate: &Aggregate) -> Result<Value, String> {
    let name = find_exact_name(kernel, &aggregate.name)?;
    if canonical_declaration_sha256(kernel, name)? != aggregate.source_content_sha256 {
        return Err(format!(
            "source content identity changed for {} in {}",
            aggregate.name, aggregate.first_artifact
        ));
    }
    let Some(Declaration::Definition { ty, value, .. }) = kernel.environment().get(name) else {
        return Err(format!("{} is not one definition", aggregate.name));
    };
    let (ty, value) = (*ty, *value);
    let (pi_binders, result_type) = leading_binders(kernel, ty, false);
    let (lambda_binders, value_body) = leading_binders(kernel, value, true);
    let prop = kernel.sort_zero();
    let returns_prop = kernel.def_eq(result_type, prop);
    let contract_shape = if returns_prop {
        "predicate-equivalence"
    } else if pi_binders == 0 {
        "nullary-observational-projections"
    } else {
        "pointwise-function-equation"
    };
    let (closure, normalization) = kernel
        .root_declaration_closure_checked_auto_param_binders(&[name])
        .map_err(|error| format!("cannot inspect normalized closure: {error}"))?;
    let mut trusted = BTreeMap::<&str, Vec<String>>::new();
    for dependency in closure {
        let kind = match kernel.environment().get(dependency) {
            Some(Declaration::Axiom { .. }) => "axiom",
            Some(Declaration::Theorem { .. }) => "theorem",
            Some(Declaration::Opaque { .. }) => "opaque",
            Some(Declaration::Quotient { .. }) => "quotient",
            _ => continue,
        };
        trusted
            .entry(kind)
            .or_default()
            .push(kernel.display_name(dependency).to_string());
    }
    if trusted.values().all(Vec::is_empty) {
        return Err(format!(
            "{} no longer has trusted implementation closure",
            aggregate.name
        ));
    }
    for names in trusted.values_mut() {
        names.sort();
        names.dedup();
    }
    let trusted_json: Map<String, Value> = trusted
        .iter()
        .map(|(kind, names)| ((*kind).to_owned(), json!(names)))
        .collect();
    let direct_theorems: Vec<_> = kernel
        .theorem_dependencies(name)
        .into_iter()
        .map(|dependency| kernel.display_name(dependency).to_string())
        .collect();
    let axioms: Vec<_> = kernel
        .axiom_footprint(name)
        .into_iter()
        .map(|dependency| kernel.display_name(dependency).to_string())
        .collect();
    Ok(json!({
        "name": aggregate.name,
        "source_content_sha256": aggregate.source_content_sha256,
        "instantiated_type_sha256": aggregate.instantiated_type_sha256,
        "universe_sha256": aggregate.universe_sha256,
        "first_artifact": aggregate.first_artifact,
        "bindings": aggregate.bindings,
        "source_occurrences": aggregate.source_occurrences,
        "artifacts": aggregate.artifacts,
        "facts": aggregate.facts,
        "families": aggregate.families,
        "type_pi_binders": pi_binders,
        "returns_prop": returns_prop,
        "value_lambda_binders": lambda_binders,
        "value_body_kind": expression_kind(kernel.expr_node(value_body)),
        "value_expression_nodes": expression_nodes(kernel, value),
        "contract_shape": contract_shape,
        "normalization_rewrites": normalization.rewritten_occurrences,
        "trusted_closure": trusted_json,
        "direct_theorem_dependencies": direct_theorems,
        "axiom_footprint": axioms,
    }))
}

fn leading_binders(kernel: &Kernel, mut expression: ExprId, lambda: bool) -> (u64, ExprId) {
    let mut count = 0;
    loop {
        let body = match kernel.expr_node(expression) {
            ExprNode::Lam(_, _, body, _) if lambda => Some(*body),
            ExprNode::Pi(_, _, body, _) if !lambda => Some(*body),
            _ => None,
        };
        let Some(body) = body else {
            return (count, expression);
        };
        count += 1;
        expression = body;
    }
}

fn expression_nodes(kernel: &Kernel, root: ExprId) -> u64 {
    let mut seen = HashSet::new();
    let mut pending = vec![root];
    while let Some(expression) = pending.pop() {
        if !seen.insert(expression) {
            continue;
        }
        match kernel.expr_node(expression) {
            ExprNode::Proj(_, _, structure) => pending.push(*structure),
            ExprNode::App(function, argument)
            | ExprNode::Lam(_, function, argument, _)
            | ExprNode::Pi(_, function, argument, _) => {
                pending.push(*function);
                pending.push(*argument);
            }
            ExprNode::Let(_, ty, value, body) => pending.extend([*ty, *value, *body]),
            ExprNode::BVar(_)
            | ExprNode::FVar(_)
            | ExprNode::Sort(_)
            | ExprNode::Const(_, _)
            | ExprNode::Lit(_) => {}
        }
    }
    u64::try_from(seen.len()).unwrap_or(u64::MAX)
}

fn expression_kind(expression: &ExprNode) -> &'static str {
    match expression {
        ExprNode::BVar(_) => "bvar",
        ExprNode::FVar(_) => "fvar",
        ExprNode::Sort(_) => "sort",
        ExprNode::Const(_, _) => "const",
        ExprNode::Proj(_, _, _) => "projection",
        ExprNode::App(_, _) => "application",
        ExprNode::Lam(_, _, _, _) => "lambda",
        ExprNode::Pi(_, _, _, _) => "pi",
        ExprNode::Let(_, _, _, _) => "let",
        ExprNode::Lit(_) => "literal",
    }
}

fn validate_observation(observation: &Value) -> Result<&[Value], String> {
    if observation.get("kind").and_then(Value::as_str)
        != Some("axeyum-autogenesis-type-slice-producer-census")
        || observation.get("state").and_then(Value::as_str)
            != Some("diagnostic-fixed-budget-no-ledger-credit")
        || observation.get("policy_version").and_then(Value::as_str)
            != Some("contaminated-definition-boundary-auto-param-binders-v3")
        || observation.get("producer_policy").and_then(Value::as_str)
            != Some("type-slice-reflexivity-census-v1")
        || observation.pointer("/authority/held_out_inspected") != Some(&json!(false))
        || observation.pointer("/authority/ledger_writes") != Some(&json!(0))
        || observation.pointer("/authority/targets") != Some(&json!(138))
    {
        return Err("producer observation authority changed".to_owned());
    }
    let rows = observation
        .get("rows")
        .and_then(Value::as_array)
        .ok_or_else(|| "producer observation rows are absent".to_owned())?;
    if rows.len() != 138 {
        return Err(format!("expected 138 producer rows, found {}", rows.len()));
    }
    Ok(rows)
}

fn find_exact_name(kernel: &Kernel, rendered: &str) -> Result<NameId, String> {
    let matches: Vec<_> = kernel
        .environment()
        .iter()
        .filter_map(|(&name, _)| {
            (kernel.display_name(name).to_string() == rendered).then_some(name)
        })
        .collect();
    match matches.as_slice() {
        [name] => Ok(*name),
        _ => Err(format!(
            "required declaration {rendered:?} occurs {} times",
            matches.len()
        )),
    }
}

fn parse_arguments() -> Result<Arguments, String> {
    let mut parsed = BTreeMap::new();
    let mut arguments = env::args().skip(1);
    while let Some(flag) = arguments.next() {
        if !matches!(flag.as_str(), "--archive" | "--observation" | "--output") {
            return Err(format!("unknown argument {flag}"));
        }
        let value = arguments
            .next()
            .ok_or_else(|| format!("{flag} requires a value"))?;
        if parsed.insert(flag.clone(), value).is_some() {
            return Err(format!("{flag} was supplied more than once"));
        }
    }
    Ok(Arguments {
        archive: required_path(&parsed, "--archive")?,
        observation: required_path(&parsed, "--observation")?,
        output: parsed.get("--output").map(PathBuf::from),
    })
}

fn required_path(arguments: &BTreeMap<String, String>, flag: &str) -> Result<PathBuf, String> {
    arguments
        .get(flag)
        .map(PathBuf::from)
        .ok_or_else(|| format!("missing {flag}"))
}

fn required_string<'a>(value: &'a Value, field: &str) -> &'a str {
    value
        .get(field)
        .and_then(Value::as_str)
        .filter(|value| !value.is_empty())
        .unwrap_or("")
}

fn required_hash<'a>(value: &'a Value, field: &str) -> Result<&'a str, String> {
    value
        .get(field)
        .and_then(Value::as_str)
        .filter(|value| is_sha256(value))
        .ok_or_else(|| format!("{field} is not a SHA-256 digest"))
}

fn is_sha256(value: &str) -> bool {
    value.len() == 64
        && value
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
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
    use super::{expression_kind, is_sha256};
    use axeyum_lean_kernel::ExprNode;

    #[test]
    fn digest_shape_is_strict_lowercase_hex() {
        assert!(is_sha256(&"a".repeat(64)));
        assert!(!is_sha256(&"A".repeat(64)));
        assert!(!is_sha256(&"a".repeat(63)));
    }

    #[test]
    fn expression_shape_names_are_stable() {
        assert_eq!(expression_kind(&ExprNode::BVar(0)), "bvar");
    }
}
