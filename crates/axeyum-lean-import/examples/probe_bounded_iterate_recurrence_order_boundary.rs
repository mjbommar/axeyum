//! Scratch probe (not a producer, not registered in `operations.json`):
//! measure whether `bounded-iterate-recurrence-v3`'s goal-shape requirement
//! (a top-level `Eq` of arity 3 whose LHS is a double-successor unfold of a
//! `Nat.iterate`-based accumulator function) is met by the open ORDER-shaped
//! fact `F:ml430-nat-fib-le-fib-succ-d1ef4a3d`.
//!
//! Reuses the real, already-exported Mathlib v4.30.0 ndjson stream built for
//! the ADR-0523 composition probe (doc 262's fifth amendment),
//! `sha256:d1af65c0c4e0273c90f9deb0299219a78e5ccbaedec7eda99536a7397c09cc10`,
//! mirrored at
//! `/nas3/data/axeyum/autogenesis/sources/mathlib-v4.30.0-premise-composition-probe-v1/nat-fib-le-fib-succ.ndjson`.
//! Does not touch any nursery, operation, or fact file; prints a structural
//! measurement and exits nonzero if the stream identity does not match.

use std::env;
use std::fmt::Write as _;
use std::fs;
use std::io::Cursor;

use axeyum_lean_import::{ImportLimits, import_ndjson};
use axeyum_lean_kernel::{Declaration, ExprId, ExprNode, Kernel};
use sha2::{Digest, Sha256};

const DEFAULT_STREAM: &str = "/nas3/data/axeyum/autogenesis/sources/mathlib-v4.30.0-premise-composition-probe-v1/nat-fib-le-fib-succ.ndjson";
const EXPECTED_SHA256: &str = "d1af65c0c4e0273c90f9deb0299219a78e5ccbaedec7eda99536a7397c09cc10";

fn hex_sha256(bytes: &[u8]) -> String {
    let mut hasher = Sha256::new();
    hasher.update(bytes);
    hasher.finalize().iter().fold(String::new(), |mut out, b| {
        let _ = write!(out, "{b:02x}");
        out
    })
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

fn main() {
    let mut args = env::args().skip(1);
    let stream_path = args.next().unwrap_or_else(|| DEFAULT_STREAM.to_owned());
    // Optional trailing args: dotted name components, e.g.
    //   Axeyum Autogenesis Coverage r080
    // Defaults to the fib_le_fib_succ probe adapter's own namespace.
    let name_parts: Vec<String> = {
        let rest: Vec<String> = args.collect();
        if rest.is_empty() {
            vec![
                "Axeyum".to_owned(),
                "Autogenesis".to_owned(),
                "Statement".to_owned(),
                "natFibLeFibSucc".to_owned(),
            ]
        } else {
            rest
        }
    };
    let skip_hash_check = stream_path != DEFAULT_STREAM;
    let stream = fs::read(&stream_path).unwrap_or_else(|error| {
        panic!("failed to read {stream_path}: {error}");
    });
    let actual_sha256 = hex_sha256(&stream);
    println!("stream={stream_path}");
    println!("stream_sha256={actual_sha256}");
    if !skip_hash_check && actual_sha256 != EXPECTED_SHA256 {
        eprintln!(
            "REFUSED: stream identity changed (expected {EXPECTED_SHA256}, got {actual_sha256})"
        );
        std::process::exit(1);
    }

    let completed = import_ndjson(Cursor::new(&stream), ImportLimits::default())
        .expect("import_ndjson failed on a stream whose hash was just verified");
    let (mut kernel, report) = completed.into_parts();
    println!(
        "lean_version={} lean_githash={} axioms={:?}",
        report.lean_version, report.lean_githash, report.axioms
    );

    // Build the dotted target name the same way the exporter's namespacing
    // does: nested `name_str` calls from the anonymous root.
    println!("target_name={}", name_parts.join("."));
    let mut target_name = kernel.anon();
    for part in &name_parts {
        target_name = kernel.name_str(target_name, part.as_str());
    }

    let goal = match kernel.environment().get(target_name) {
        Some(Declaration::Definition { value, .. }) => *value,
        other => panic!("natFibLeFibSucc is not a plain definition: {other:?}"),
    };

    // Strip leading Pi binders under fresh fvars, exactly as
    // `recurrence_proof` does with its single `n` binder, and report how
    // many there are (the adapter source declares one implicit `{n : ℕ}`).
    let mut current = goal;
    let mut binder_count: u64 = 0;
    loop {
        let node = kernel.expr_node(current).clone();
        match node {
            ExprNode::Pi(_, _, body, _) => {
                binder_count += 1;
                let fv = kernel.fvar(u64::MAX - 900_000 - binder_count);
                current = kernel.instantiate(body, &[fv]);
            }
            _ => break,
        }
    }
    println!("pi_binders_stripped={binder_count}");

    let (head, args) = app_spine(&kernel, current);
    let head_rendered = match kernel.expr_node(head) {
        ExprNode::Const(name, _) => kernel.display_name(*name).to_string(),
        other => format!("{other:?}"),
    };
    println!("goal_body_head={head_rendered}");
    println!("goal_body_spine_arity={}", args.len());

    // The producer's own gate, reproduced verbatim from
    // `nat_fib_iterate_recurrence.rs::recurrence_proof`:
    //   let (_, target_arguments) = app_spine(kernel, target);
    //   if target_arguments.len() != 3 { return Err("target body is not equality".to_owned()); }
    if args.len() == 3 && head_rendered == "Eq" {
        println!(
            "VERDICT: goal body IS a 3-arg Eq application -- would clear recurrence_proof's arity/head gate"
        );
    } else {
        println!(
            "VERDICT: goal body is NOT a 3-arg Eq application (head={head_rendered}, arity={}) -- recurrence_proof's own `target_arguments.len() != 3` (or head) check rejects it before any Eq-only combinator (congr_arg / equality_trans / equality_symm) runs",
            args.len()
        );
    }
}
