//! Derive a proof-isolated implementation graph for type-sliced definitions.
//!
//! This reads only the checked type-slice receipts and the declaration bodies
//! already present in their frozen source streams.  It never requests a target
//! theorem proof and grants no proof or operation authority.

use std::collections::{BTreeMap, BTreeSet};
use std::env;
use std::fmt::Write;
use std::fs;
use std::io::Cursor;
use std::path::PathBuf;

use axeyum_lean_import::{ImportLimits, canonical_declaration_sha256, import_ndjson};
use axeyum_lean_kernel::{Declaration, Kernel};
use serde_json::{Value, json};
use sha2::{Digest, Sha256};

#[derive(Debug)]
struct Arguments {
    streams: PathBuf,
    replay: PathBuf,
    output: PathBuf,
}

#[derive(Debug, Clone)]
struct Root {
    name: String,
    content_sha256: String,
    artifact: String,
    fact_ids: BTreeSet<String>,
}

fn main() {
    if let Err(error) = run() {
        eprintln!("imported-implementation-demand: {error}");
        std::process::exit(1);
    }
}

#[allow(clippy::too_many_lines)]
fn run() -> Result<(), String> {
    let args = parse_arguments()?;
    let replay_bytes = fs::read(&args.replay)
        .map_err(|error| format!("cannot read {}: {error}", args.replay.display()))?;
    let replay: Value = serde_json::from_slice(&replay_bytes)
        .map_err(|error| format!("replay is not JSON: {error}"))?;
    let roots = collect_roots(&replay)?;
    let mut rows = Vec::with_capacity(roots.len());
    for root in roots.values() {
        let stream_path = args.streams.join(&root.artifact);
        let stream_bytes = fs::read(&stream_path)
            .map_err(|error| format!("cannot read {}: {error}", stream_path.display()))?;
        let completed = import_ndjson(Cursor::new(&stream_bytes), ImportLimits::default())
            .map_err(|error| format!("cannot import {}: {error:?}", root.artifact))?;
        let (kernel, _) = completed.into_parts();
        rows.push(describe_root(&kernel, root, &stream_bytes)?);
    }
    rows.sort_by(|left, right| {
        required_string(left, "source_name").cmp(required_string(right, "source_name"))
    });
    let transparent_nodes: usize = rows
        .iter()
        .map(|row| row["transparent_nodes"].as_array().map_or(0, Vec::len))
        .sum();
    let edges: usize = rows
        .iter()
        .map(|row| row["edges"].as_array().map_or(0, Vec::len))
        .sum();
    let mut global_nodes = BTreeMap::<(String, String), Value>::new();
    let mut global_edges = BTreeSet::<(String, String, String, String, String)>::new();
    let mut root_rows = Vec::with_capacity(rows.len());
    for row in &rows {
        let mut reachable = Vec::new();
        for node in row["transparent_nodes"]
            .as_array()
            .ok_or_else(|| "transparent node inventory is malformed".to_owned())?
        {
            let name = required_string(node, "name").to_owned();
            let content = required_string(node, "content_sha256").to_owned();
            global_nodes
                .entry((name.clone(), content.clone()))
                .or_insert_with(|| json!({"name": name, "content_sha256": content}));
            reachable.push(json!({"name": name, "content_sha256": content}));
        }
        for edge in row["edges"]
            .as_array()
            .ok_or_else(|| "edge inventory is malformed".to_owned())?
        {
            global_edges.insert((
                required_string(edge, "from").to_owned(),
                required_string(edge, "from_content_sha256").to_owned(),
                required_string(edge, "to").to_owned(),
                required_string(edge, "to_content_sha256").to_owned(),
                required_string(edge, "to_kind").to_owned(),
            ));
        }
        root_rows.push(json!({
            "source_name": row["source_name"],
            "source_content_sha256": row["source_content_sha256"],
            "representative_artifact": row["representative_artifact"],
            "representative_stream_sha256": row["representative_stream_sha256"],
            "affected_fact_ids": row["affected_fact_ids"],
            "reachable_transparent_nodes": reachable,
            "direct_edge_occurrences": row["edges"].as_array().map_or(0, Vec::len),
        }));
    }
    let node_rows: Vec<_> = global_nodes.into_values().collect();
    let edge_rows: Vec<_> = global_edges
        .into_iter()
        .map(
            |(from, from_content_sha256, to, to_content_sha256, to_kind)| {
                json!({
                    "from": from,
                    "from_content_sha256": from_content_sha256,
                    "to": to,
                    "to_content_sha256": to_content_sha256,
                    "to_kind": to_kind,
                })
            },
        )
        .collect();
    let output = json!({
        "schema_version": 1,
        "kind": "axeyum-autogenesis-imported-implementation-demand",
        "state": "proof-isolated-strategy-graph",
        "authority": "strategy context only; no theorem proof, semantic contract, operation, applicability, or fact-transition authority",
        "source": {
            "type_slice_replay_path": args.replay.to_string_lossy(),
            "type_slice_replay_sha256": sha256(&replay_bytes),
            "external_stream_directory": args.streams.to_string_lossy(),
        },
        "census": {
            "root_definition_identities": rows.len(),
            "transparent_node_occurrences": transparent_nodes,
            "direct_edge_occurrences": edges,
            "distinct_transparent_nodes": node_rows.len(),
            "distinct_direct_edges": edge_rows.len(),
        },
        "roots": root_rows,
        "transparent_nodes": node_rows,
        "edges": edge_rows,
        "limitations": "Edges expose transparent implementation demand only. The global view deduplicates identities that have the same name and structural hash across representative streams while roots retain occurrence reachability; neither equality authorizes declaration transport.",
    });
    let mut rendered = serde_json::to_string_pretty(&output)
        .map_err(|error| format!("cannot render output: {error}"))?;
    rendered.push('\n');
    fs::write(&args.output, rendered)
        .map_err(|error| format!("cannot write {}: {error}", args.output.display()))?;
    println!(
        "AUTOGENESIS_IMPORTED_IMPLEMENTATION_DEMAND_OK|roots={}|transparent_nodes={transparent_nodes}|edges={edges}|ledger_writes=0",
        rows.len()
    );
    Ok(())
}

fn collect_roots(replay: &Value) -> Result<BTreeMap<(String, String), Root>, String> {
    if replay["kind"] != "axeyum-autogenesis-checked-type-slice-replay"
        || replay["authority"]["proof_bodies_requested"] != false
        || replay["authority"]["held_out_inspected"] != false
    {
        return Err("replay does not preserve the proof-isolated population boundary".to_owned());
    }
    let rows = replay["rows"]
        .as_array()
        .ok_or_else(|| "replay rows are absent".to_owned())?;
    let mut roots = BTreeMap::new();
    for row in rows {
        if row["outcome"] != "accepted-receipt" {
            return Err("replay contains a non-accepted row".to_owned());
        }
        let artifact = required_string(row, "artifact_file").to_owned();
        let fact_id = required_string(row, "fact_id").to_owned();
        for abstraction in row["receipt"]["abstractions"]
            .as_array()
            .ok_or_else(|| format!("{fact_id} has no abstraction inventory"))?
        {
            let name = required_string(abstraction, "source_name").to_owned();
            let content = required_string(abstraction, "source_content_sha256").to_owned();
            let entry = roots
                .entry((name.clone(), content.clone()))
                .or_insert_with(|| Root {
                    name,
                    content_sha256: content,
                    artifact: artifact.clone(),
                    fact_ids: BTreeSet::new(),
                });
            entry.fact_ids.insert(fact_id.clone());
        }
    }
    Ok(roots)
}

fn describe_root(kernel: &Kernel, root: &Root, stream: &[u8]) -> Result<Value, String> {
    let root_name = kernel
        .environment()
        .iter()
        .find_map(|(name, _)| {
            (kernel.display_name(*name).to_string() == root.name).then_some(*name)
        })
        .ok_or_else(|| format!("{} is absent from {}", root.name, root.artifact))?;
    if canonical_declaration_sha256(kernel, root_name)? != root.content_sha256 {
        return Err(format!("{} content identity changed", root.name));
    }
    if !matches!(
        kernel.environment().get(root_name),
        Some(Declaration::Definition { .. })
    ) {
        return Err(format!("{} is not a transparent definition", root.name));
    }
    let mut pending = vec![root_name];
    let mut visited = BTreeSet::new();
    let mut nodes = Vec::new();
    let mut edges = Vec::new();
    let mut boundary = BTreeMap::<String, BTreeSet<String>>::new();
    while let Some(name) = pending.pop() {
        let key = kernel.display_name(name).to_string();
        if !visited.insert(key.clone()) {
            continue;
        }
        let declaration = kernel
            .environment()
            .get(name)
            .ok_or_else(|| format!("missing {key}"))?;
        if !matches!(declaration, Declaration::Definition { .. }) {
            continue;
        }
        let source_content_sha256 = canonical_declaration_sha256(kernel, name)?;
        nodes.push(json!({
            "name": key,
            "content_sha256": source_content_sha256,
        }));
        for dependency in kernel.declaration_dependencies(name) {
            let dependency_name = kernel.display_name(dependency).to_string();
            let declaration = kernel
                .environment()
                .get(dependency)
                .ok_or_else(|| format!("missing {dependency_name}"))?;
            let dependency_kind = kind(declaration);
            let dependency_content_sha256 = canonical_declaration_sha256(kernel, dependency)?;
            edges.push(json!({
                "from": key,
                "from_content_sha256": source_content_sha256,
                "to": dependency_name,
                "to_content_sha256": dependency_content_sha256,
                "to_kind": dependency_kind,
            }));
            if matches!(declaration, Declaration::Definition { .. }) {
                pending.push(dependency);
            } else {
                boundary
                    .entry(dependency_kind.to_owned())
                    .or_default()
                    .insert(dependency_name);
            }
        }
    }
    nodes.sort_by(|left, right| required_string(left, "name").cmp(required_string(right, "name")));
    edges.sort_by(|left, right| {
        required_string(left, "from")
            .cmp(required_string(right, "from"))
            .then_with(|| {
                required_string(left, "from_content_sha256")
                    .cmp(required_string(right, "from_content_sha256"))
            })
            .then_with(|| required_string(left, "to").cmp(required_string(right, "to")))
            .then_with(|| {
                required_string(left, "to_content_sha256")
                    .cmp(required_string(right, "to_content_sha256"))
            })
    });
    let boundary: BTreeMap<_, Vec<_>> = boundary
        .into_iter()
        .map(|(kind, names)| (kind, names.into_iter().collect()))
        .collect();
    Ok(json!({
        "source_name": root.name,
        "source_content_sha256": root.content_sha256,
        "representative_artifact": root.artifact,
        "representative_stream_sha256": sha256(stream),
        "affected_fact_ids": root.fact_ids,
        "transparent_nodes": nodes,
        "edges": edges,
        "nontransparent_boundary": boundary,
    }))
}

fn kind(declaration: &Declaration) -> &'static str {
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

fn required_string<'a>(value: &'a Value, key: &str) -> &'a str {
    value[key].as_str().unwrap_or("")
}

fn sha256(bytes: &[u8]) -> String {
    Sha256::digest(bytes)
        .iter()
        .fold(String::with_capacity(64), |mut output, byte| {
            write!(output, "{byte:02x}").expect("writing to a String cannot fail");
            output
        })
}

fn parse_arguments() -> Result<Arguments, String> {
    let mut streams = None;
    let mut replay = None;
    let mut output = None;
    let mut args = env::args().skip(1);
    while let Some(argument) = args.next() {
        let value = args
            .next()
            .ok_or_else(|| format!("{argument} requires a value"))?;
        match argument.as_str() {
            "--streams" => streams = Some(PathBuf::from(value)),
            "--replay" => replay = Some(PathBuf::from(value)),
            "--output" => output = Some(PathBuf::from(value)),
            _ => return Err(format!("unknown argument {argument}")),
        }
    }
    Ok(Arguments {
        streams: streams.ok_or_else(|| "--streams is required".to_owned())?,
        replay: replay.ok_or_else(|| "--replay is required".to_owned())?,
        output: output.ok_or_else(|| "--output is required".to_owned())?,
    })
}
