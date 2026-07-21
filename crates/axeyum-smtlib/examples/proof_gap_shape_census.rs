//! Emit exact source-syntax and parsed-IR feature censuses for SMT-LIB files.
//!
//! This is a diagnostic producer for the generated proof-gap research
//! artifacts, not a solver path. It deliberately traverses only terms reachable
//! from assertions, deduplicated by `TermId`, so parser helper terms and repeated
//! DAG references do not inflate the IR vocabulary.

use std::collections::{BTreeMap, BTreeSet};
use std::env;
use std::fmt::Write as _;
use std::fs;
use std::path::Path;

use axeyum_ir::TermNode;
use axeyum_smtlib::{SExpr, parse_script, read_all};
use serde_json::{Value, json};
use sha2::{Digest, Sha256};

fn variant_name(debug: &str) -> String {
    debug
        .split([' ', '{', '('])
        .next()
        .unwrap_or(debug)
        .to_owned()
}

fn source_head(items: &[SExpr]) -> Option<String> {
    match items.first()? {
        SExpr::Atom(head) => Some(head.clone()),
        SExpr::List(indexed) => {
            let marker = indexed.first()?.atom()?;
            if marker == "_" || marker == "as" {
                indexed.get(1)?.atom().map(str::to_owned)
            } else {
                None
            }
        }
    }
}

fn collect_source_heads(expr: &SExpr, heads: &mut BTreeMap<String, u64>) {
    let SExpr::List(items) = expr else {
        return;
    };
    if let Some(head) = source_head(items) {
        *heads.entry(head).or_default() += 1;
    }
    for item in items {
        collect_source_heads(item, heads);
    }
}

fn assertion_bodies(exprs: &[SExpr]) -> impl Iterator<Item = &SExpr> {
    exprs.iter().filter_map(|expr| {
        let items = expr.list()?;
        (items.first()?.atom()? == "assert")
            .then(|| items.get(1))
            .flatten()
    })
}

fn ir_census(
    script: &axeyum_smtlib::Script,
) -> (usize, BTreeMap<String, u64>, BTreeMap<String, u64>) {
    let mut seen = BTreeSet::new();
    let mut stack = script.assertions.clone();
    let mut ops = BTreeMap::new();
    let mut sorts = BTreeMap::new();
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        let sort_debug = format!("{:?}", script.arena.sort_of(term));
        let sort = variant_name(&sort_debug);
        *sorts.entry(sort).or_default() += 1;
        if let TermNode::App { op, args } = script.arena.node(term) {
            let op_debug = format!("{op:?}");
            let op = variant_name(&op_debug);
            *ops.entry(op).or_default() += 1;
            stack.extend(args.iter().copied());
        }
    }
    (seen.len(), ops, sorts)
}

fn map_value(counts: BTreeMap<String, u64>) -> Value {
    Value::Object(
        counts
            .into_iter()
            .map(|(key, value)| (key, Value::from(value)))
            .collect(),
    )
}

fn inspect(path: &Path) -> Result<Value, String> {
    let bytes = fs::read(path).map_err(|error| format!("{}: {error}", path.display()))?;
    let text = std::str::from_utf8(&bytes)
        .map_err(|error| format!("{}: not UTF-8: {error}", path.display()))?;
    let exprs = read_all(text).map_err(|error| format!("{}: {error}", path.display()))?;
    let mut source_heads = BTreeMap::new();
    let bodies: Vec<&SExpr> = assertion_bodies(&exprs).collect();
    for body in &bodies {
        collect_source_heads(body, &mut source_heads);
    }
    let script = parse_script(text).map_err(|error| format!("{}: {error}", path.display()))?;
    let (unique_terms, ir_ops, ir_sorts) = ir_census(&script);
    let mut sha256 = String::with_capacity(64);
    for byte in Sha256::digest(&bytes) {
        write!(&mut sha256, "{byte:02x}").expect("writing to String cannot fail");
    }
    Ok(json!({
        "file": path.to_string_lossy(),
        "sha256": sha256,
        "logic": script.logic,
        "assertions": script.assertions.len(),
        "source_assertions": bodies.len(),
        "uses_bounded_strings": script.uses_bounded_strings,
        "word_only_fallback": script.word_only_fallback.is_some(),
        "word_problem": script.word_problem.is_some(),
        "word_skeleton_terms": script.word_skeleton.len(),
        "membership_problem": script.membership_problem.is_some(),
        "length_skeleton_terms": script.length_skeleton.len(),
        "len_abstraction_map_entries": script.len_abstraction_map.len(),
        "len_abstraction_fact_terms": script.len_abstraction_facts.len(),
        "len_abstraction_bound_terms": script.len_abstraction_bounds.len(),
        "source_heads": map_value(source_heads),
        "unique_ir_terms": unique_terms,
        "ir_ops": map_value(ir_ops),
        "ir_sorts": map_value(ir_sorts),
    }))
}

fn main() -> Result<(), String> {
    let paths: Vec<_> = env::args_os().skip(1).collect();
    if paths.is_empty() {
        return Err("usage: proof_gap_shape_census <file.smt2>...".to_owned());
    }
    let mut instances = Vec::with_capacity(paths.len());
    for path in paths {
        instances.push(inspect(Path::new(&path))?);
    }
    println!(
        "{}",
        serde_json::to_string_pretty(&json!({"version": 2, "instances": instances}))
            .map_err(|error| error.to_string())?
    );
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn indexed_heads_use_the_operator_name() {
        let exprs = read_all("(assert (= ((_ extract 3 0) x) #b0000))").unwrap();
        let mut heads = BTreeMap::new();
        for body in assertion_bodies(&exprs) {
            collect_source_heads(body, &mut heads);
        }
        assert_eq!(heads.get("extract"), Some(&1));
        assert_eq!(heads.get("="), Some(&1));
    }
}
