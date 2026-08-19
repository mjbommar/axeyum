//! Exact ADR-0490 one-source delta control for Mathlib `Int.gcd` in r018.

use std::collections::{BTreeMap, BTreeSet, HashSet};
use std::env;
use std::fs;
use std::io::Cursor;
use std::path::PathBuf;

use axeyum_lean_import::{
    ConstantInstance, ImportLimits, build_source_delta_step, canonical_declaration_sha256,
    canonical_expression_sha256, import_ndjson, residualize_function_contract_body,
};
use axeyum_lean_kernel::{ExprId, ExprNode, Kernel, NameId};
use serde_json::{Value, json};
use sha2::{Digest, Sha256};

const SOURCE_CONTENT: &str = "1b4460e69780e5080a107bc178b77ffe064585b9712c5f7468a80c02cdee0655";

fn main() {
    if let Err(error) = run() {
        eprintln!("int-gcd-source-delta-trace: {error}");
        std::process::exit(1);
    }
}

#[allow(clippy::too_many_lines)]
fn run() -> Result<(), String> {
    let arguments = parse_arguments()?;
    let stream = fs::read(&arguments.stream).map_err(|error| error.to_string())?;
    let completed = import_ndjson(Cursor::new(&stream), ImportLimits::default())
        .map_err(|error| format!("cannot import source: {error:?}"))?;
    let (mut kernel, report) = completed.into_parts();
    if report.lean_version != "4.30.0"
        || report.lean_githash != "d024af099ca4bf2c86f649261ebf59565dc8c622"
        || !report.axioms.is_empty()
    {
        return Err("source toolchain or axiom authority changed".to_owned());
    }
    let source_name = exact_name(&kernel, "Int.gcd")?;
    if canonical_declaration_sha256(&kernel, source_name)? != SOURCE_CONTENT {
        return Err("exact Int.gcd identity changed".to_owned());
    }
    let nat_gcd = exact_name(&kernel, "Nat.gcd")?;
    let int = exact_name(&kernel, "Int")?;
    let nat_abs = exact_name(&kernel, "Int.natAbs")?;
    let source = instance(&mut kernel, source_name, "intGcd");
    let residual = instance(&mut kernel, nat_gcd, "natGcd");
    let retained = [
        instance(&mut kernel, int, "Int"),
        instance(&mut kernel, nat_abs, "natAbs"),
    ];
    let contract = residualize_function_contract_body(
        &mut kernel,
        &source,
        std::slice::from_ref(&residual),
        &retained,
    )
    .map_err(|error| error.to_string())?;
    let trace = build_source_delta_step(&mut kernel, source_name, &[], &[])
        .map_err(|error| error.to_string())?;
    if trace.source_content_sha256 != SOURCE_CONTENT
        || !trace.levels.is_empty()
        || !trace.arguments.is_empty()
    {
        return Err("bounded source trace identity changed".to_owned());
    }
    let direct_constants = direct_constant_names(&kernel, trace.after);
    if direct_constants != ["Int", "Int.natAbs", "Nat.gcd"] {
        return Err(format!(
            "one-step body constants changed: {}",
            direct_constants.join(",")
        ));
    }
    let template_constants = direct_constant_names(&kernel, contract.generalized.goal);
    if template_constants.contains(&"Int.gcd".to_owned())
        || template_constants.contains(&"Nat.gcd".to_owned())
    {
        return Err("proof-free template retained a generalized function".to_owned());
    }

    let mut output = json!({
        "schema_version": 1,
        "kind": "axeyum-autogenesis-int-gcd-source-delta-control",
        "state": "mechanism-control-no-contract-proof-or-ledger-credit",
        "source": {
            "stream_sha256": hex_sha256(&stream),
            "artifact_file": "r018.ndjson",
            "lean_version": report.lean_version,
            "lean_githash": report.lean_githash,
            "definition": "Int.gcd",
            "definition_content_sha256": SOURCE_CONTENT,
        },
        "proof_free_template": {
            "generalized_contract_sha256": canonical_expression_sha256(&kernel, contract.generalized.goal)?,
            "binders": ["Int.gcd", "Nat.gcd"],
            "source_and_residual_absent_from_direct_constants": true,
            "direct_constants": template_constants,
            "specialization_verified": true,
        },
        "bounded_delta_trace": {
            "rule": "selected-transparent-definition-delta-v1",
            "selected_source": "Int.gcd",
            "consulted_declarations": ["Int.gcd"],
            "universe_arguments": 0,
            "term_arguments": 0,
            "before_sha256": canonical_expression_sha256(&kernel, trace.before)?,
            "after_sha256": canonical_expression_sha256(&kernel, trace.after)?,
            "after_direct_constants": direct_constants,
            "residual_constants_left_opaque": ["Nat.gcd"],
            "recursive_delta_steps": 0,
            "theorem_dependency_walks": 0,
        },
        "authority": {
            "partitions_inspected": ["train"],
            "held_out_inspected": false,
            "proof_bodies_inspected": false,
            "producer_target_attempts": 0,
            "contracts_admitted": 0,
            "ledger_writes": 0,
        },
        "limitations": "This binds one exact structural delta step and the proof-free residual template. It does not yet replace the theorem witness in a semantic function-contract receipt and grants no target, proof, contract, or ledger credit.",
    });
    let digest = canonical_digest(&output)?;
    output["observation_sha256"] = json!(digest);
    let mut rendered = serde_json::to_string_pretty(&output).map_err(|error| error.to_string())?;
    rendered.push('\n');
    fs::write(&arguments.output, rendered).map_err(|error| error.to_string())?;
    println!(
        "AUTOGENESIS_INT_GCD_SOURCE_DELTA_OK|{digest}|source=Int.gcd|consulted=1|residual_opaque=Nat.gcd|held_out=0|ledger_writes=0"
    );
    Ok(())
}

fn direct_constant_names(kernel: &Kernel, root: ExprId) -> Vec<String> {
    let mut names = BTreeSet::new();
    let mut seen = HashSet::new();
    let mut pending = vec![root];
    while let Some(expression) = pending.pop() {
        if !seen.insert(expression) {
            continue;
        }
        match kernel.expr_node(expression) {
            ExprNode::Const(name, _) => {
                names.insert(kernel.display_name(*name).to_string());
            }
            ExprNode::App(function, argument)
            | ExprNode::Lam(_, function, argument, _)
            | ExprNode::Pi(_, function, argument, _) => {
                pending.extend([*function, *argument]);
            }
            ExprNode::Let(_, ty, value, body) => pending.extend([*ty, *value, *body]),
            ExprNode::Proj(_, _, structure) => pending.push(*structure),
            ExprNode::BVar(_) | ExprNode::FVar(_) | ExprNode::Sort(_) | ExprNode::Lit(_) => {}
        }
    }
    names.into_iter().collect()
}

struct Arguments {
    stream: PathBuf,
    output: PathBuf,
}

fn parse_arguments() -> Result<Arguments, String> {
    let mut values = BTreeMap::new();
    let mut arguments = env::args().skip(1);
    while let Some(flag) = arguments.next() {
        if !matches!(flag.as_str(), "--stream" | "--output") {
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
        stream: required_path(&values, "--stream")?,
        output: required_path(&values, "--output")?,
    })
}

fn required_path(values: &BTreeMap<String, String>, flag: &str) -> Result<PathBuf, String> {
    values
        .get(flag)
        .map(PathBuf::from)
        .ok_or_else(|| format!("missing {flag}"))
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

fn instance(kernel: &mut Kernel, name: NameId, binder: &str) -> ConstantInstance {
    ConstantInstance {
        name,
        levels: vec![],
        binder_name: nested_name(kernel, &[binder]),
    }
}

fn nested_name(kernel: &mut Kernel, parts: &[&str]) -> NameId {
    let mut name = kernel.anon();
    for part in parts {
        name = kernel.name_str(name, *part);
    }
    name
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
