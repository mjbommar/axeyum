//! Diagnose the terminal relation exposed by a proof-isolated Mathlib goal.

use std::fmt::Write as _;
use std::fs;
use std::io::Cursor;
use std::path::PathBuf;

use axeyum_lean_import::{ImportLimits, import_ndjson};
use axeyum_lean_kernel::{Declaration, ExprId, ExprNode, Kernel, NameId};
use serde_json::json;
use sha2::{Digest, Sha256};

fn main() {
    if let Err(error) = run() {
        eprintln!("relation-goal-probe: {error}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), String> {
    let mut arguments = std::env::args_os().skip(1);
    let stream_path = arguments
        .next()
        .map(PathBuf::from)
        .ok_or("usage: relation_goal_probe <stream.ndjson> <target-definition>")?;
    let target = arguments
        .next()
        .and_then(|value| value.into_string().ok())
        .ok_or("target definition must be UTF-8")?;
    if arguments.next().is_some() {
        return Err("unexpected trailing argument".to_owned());
    }
    let stream = fs::read(&stream_path).map_err(|error| error.to_string())?;
    let completed = import_ndjson(Cursor::new(&stream), ImportLimits::default())
        .map_err(|error| format!("source import failed: {error:?}"))?;
    let (mut kernel, report) = completed.into_parts();
    if !report.axioms.is_empty() {
        return Err("source stream unexpectedly contains axioms".to_owned());
    }
    let target_name = exact_name(&kernel, &target)?;
    let mut goal = match kernel.environment().get(target_name) {
        Some(Declaration::Definition { uparams, value, .. }) if uparams.is_empty() => *value,
        _ => return Err("target is not a monomorphic statement definition".to_owned()),
    };
    let mut binders = 0_u64;
    while let ExprNode::Pi(_, _, body, _) = kernel.expr_node(goal) {
        goal = *body;
        binders += 1;
    }
    let original_head = rendered_head(&kernel, goal);
    let reduced = kernel.whnf(goal);
    let reduced_head = rendered_head(&kernel, reduced);
    let rendered_reduced = kernel.render_lean(reduced);
    let output = json!({
        "schema_version": 1,
        "kind": "axeyum-autogenesis-relation-goal-probe",
        "source": {
            "stream_sha256": hex_sha256(&stream),
            "lean_version": report.lean_version,
            "lean_githash": report.lean_githash,
            "target_definition": target,
        },
        "result": {
            "binders": binders,
            "original_head": original_head,
            "whnf_head": reduced_head,
            "whnf_goal": rendered_reduced,
        },
        "authority": {
            "proof_search_invocations": 0,
            "kernel_submissions": 0,
            "ledger_writes": 0,
        },
    });
    println!(
        "{}",
        serde_json::to_string(&output).map_err(|error| error.to_string())?
    );
    Ok(())
}

fn rendered_head(kernel: &Kernel, expression: ExprId) -> String {
    let (head, _) = app_spine(kernel, expression);
    match kernel.expr_node(head) {
        ExprNode::Const(name, _) => kernel.display_name(*name).to_string(),
        node => format!("{node:?}"),
    }
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

fn exact_name(kernel: &Kernel, rendered: &str) -> Result<NameId, String> {
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

fn hex_sha256(bytes: &[u8]) -> String {
    let digest = Sha256::digest(bytes);
    let mut hex = String::with_capacity(digest.len() * 2);
    for byte in digest {
        let _ = write!(hex, "{byte:02x}");
    }
    hex
}
