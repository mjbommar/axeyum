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

type NodeKey = (String, String, String, String);

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
        let (kernel, report) = completed.into_parts();
        let dependency_hashes: BTreeMap<_, _> = report
            .declaration_identities
            .into_iter()
            .map(|identity| (identity.name, identity.dependency_sha256))
            .collect();
        rows.push(describe_root(
            &kernel,
            &dependency_hashes,
            root,
            &stream_bytes,
        )?);
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
    let mut global_nodes = BTreeMap::<NodeKey, String>::new();
    let mut global_edges = BTreeSet::<(NodeKey, NodeKey)>::new();
    let mut root_rows = Vec::with_capacity(rows.len());
    for row in &rows {
        let mut reachable = Vec::new();
        for node in row["transparent_nodes"]
            .as_array()
            .ok_or_else(|| "transparent node inventory is malformed".to_owned())?
        {
            let name = required_string(node, "name").to_owned();
            let content = required_string(node, "content_sha256").to_owned();
            let dependencies = required_string(node, "dependency_sha256").to_owned();
            let context_digest = required_string(node, "context_sha256").to_owned();
            let key = (context_digest, name, content, dependencies);
            global_nodes.insert(key.clone(), "definition".to_owned());
            reachable.push(key);
        }
        for edge in row["edges"]
            .as_array()
            .ok_or_else(|| "edge inventory is malformed".to_owned())?
        {
            let source = (
                required_string(edge, "context_sha256").to_owned(),
                required_string(edge, "from").to_owned(),
                required_string(edge, "from_content_sha256").to_owned(),
                required_string(edge, "from_dependency_sha256").to_owned(),
            );
            let target = (
                required_string(edge, "context_sha256").to_owned(),
                required_string(edge, "to").to_owned(),
                required_string(edge, "to_content_sha256").to_owned(),
                required_string(edge, "to_dependency_sha256").to_owned(),
            );
            global_nodes.insert(source.clone(), "definition".to_owned());
            global_nodes
                .entry(target.clone())
                .or_insert_with(|| required_string(edge, "to_kind").to_owned());
            global_edges.insert((source, target));
        }
        root_rows.push(json!({
            "source_name": row["source_name"],
            "source_content_sha256": row["source_content_sha256"],
            "representative_artifact": row["representative_artifact"],
            "representative_stream_sha256": row["representative_stream_sha256"],
            "affected_fact_ids": row["affected_fact_ids"],
            "reachable_transparent_node_keys": reachable,
            "direct_edge_occurrences": row["edges"].as_array().map_or(0, Vec::len),
        }));
    }
    let node_ids: BTreeMap<_, _> = global_nodes
        .keys()
        .cloned()
        .enumerate()
        .map(|(node_id, key)| (key, node_id))
        .collect();
    let node_rows: Vec<_> = global_nodes
        .into_iter()
        .map(|((context_sha256, name, content_sha256, dependency_sha256), kind)| {
            json!({
                "node_id": node_ids[&(context_sha256.clone(), name.clone(), content_sha256.clone(), dependency_sha256.clone())],
                "context_sha256": context_sha256,
                "name": name,
                "content_sha256": content_sha256,
                "dependency_sha256": dependency_sha256,
                "kind": kind,
            })
        })
        .collect();
    let edge_rows: Vec<_> = global_edges
        .into_iter()
        .map(|(source, target)| json!({"from_node_id": node_ids[&source], "to_node_id": node_ids[&target]}))
        .collect();
    for row in &mut root_rows {
        let keys = row["reachable_transparent_node_keys"]
            .as_array()
            .ok_or_else(|| "root reachability keys are malformed".to_owned())?;
        let ids: Vec<_> = keys
            .iter()
            .map(|key| {
                let values = key
                    .as_array()
                    .ok_or_else(|| "root node key is malformed".to_owned())?;
                let key = (
                    values[0].as_str().unwrap_or("").to_owned(),
                    values[1].as_str().unwrap_or("").to_owned(),
                    values[2].as_str().unwrap_or("").to_owned(),
                    values[3].as_str().unwrap_or("").to_owned(),
                );
                node_ids
                    .get(&key)
                    .copied()
                    .ok_or_else(|| "root node identity is absent".to_owned())
            })
            .collect::<Result<_, _>>()?;
        row.as_object_mut()
            .ok_or_else(|| "root row is malformed".to_owned())?
            .insert("reachable_transparent_node_ids".to_owned(), json!(ids));
        row.as_object_mut()
            .expect("root row was checked")
            .remove("reachable_transparent_node_keys");
    }
    let distinct_transparent_nodes = node_rows
        .iter()
        .filter(|row| row["kind"] == "definition")
        .count();
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
            "distinct_declaration_nodes": node_rows.len(),
            "distinct_transparent_nodes": distinct_transparent_nodes,
            "distinct_direct_edges": edge_rows.len(),
        },
        "roots": root_rows,
        "nodes": node_rows,
        "edges": edge_rows,
        "limitations": "Edges expose transparent implementation demand only. Context-bound node identities prevent declarations from separate representative streams from being merged; integer node IDs compact the graph and grant no declaration transport authority.",
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

#[allow(clippy::too_many_lines)]
fn describe_root(
    kernel: &Kernel,
    dependency_hashes: &BTreeMap<String, String>,
    root: &Root,
    stream: &[u8],
) -> Result<Value, String> {
    let context_sha256 = sha256(stream);
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
        let source_dependency_sha256 = dependency_hashes
            .get(&key)
            .ok_or_else(|| format!("missing dependency identity for {key}"))?;
        nodes.push(json!({
            "context_sha256": context_sha256,
            "name": key,
            "content_sha256": source_content_sha256,
            "dependency_sha256": source_dependency_sha256,
        }));
        for dependency in kernel.declaration_dependencies(name) {
            let dependency_name = kernel.display_name(dependency).to_string();
            let declaration = kernel
                .environment()
                .get(dependency)
                .ok_or_else(|| format!("missing {dependency_name}"))?;
            let dependency_kind = kind(declaration);
            let dependency_content_sha256 = canonical_declaration_sha256(kernel, dependency)?;
            let dependency_dependency_sha256 = dependency_hashes
                .get(&dependency_name)
                .ok_or_else(|| format!("missing dependency identity for {dependency_name}"))?;
            edges.push(json!({
                "context_sha256": context_sha256,
                "from": key,
                "from_content_sha256": source_content_sha256,
                "from_dependency_sha256": source_dependency_sha256,
                "to": dependency_name,
                "to_content_sha256": dependency_content_sha256,
                "to_dependency_sha256": dependency_dependency_sha256,
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
            .then_with(|| {
                required_string(left, "from_dependency_sha256")
                    .cmp(required_string(right, "from_dependency_sha256"))
            })
            .then_with(|| required_string(left, "to").cmp(required_string(right, "to")))
            .then_with(|| {
                required_string(left, "to_content_sha256")
                    .cmp(required_string(right, "to_content_sha256"))
            })
            .then_with(|| {
                required_string(left, "to_dependency_sha256")
                    .cmp(required_string(right, "to_dependency_sha256"))
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
