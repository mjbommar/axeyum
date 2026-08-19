//! Exact ADR-0489 residualization control for Mathlib `Int.gcd` in r018.

#[path = "statement_reflexivity_support/mod.rs"]
mod reflexivity;

use std::collections::BTreeMap;
use std::env;
use std::fs;
use std::io::Cursor;
use std::path::PathBuf;

use axeyum_lean_import::{
    ConstantInstance, ImportLimits, canonical_declaration_sha256, canonical_expression_sha256,
    import_ndjson, residualize_function_contract_body,
};
use axeyum_lean_kernel::{Declaration, Kernel, NameId};
use serde_json::{Value, json};
use sha2::{Digest, Sha256};

const SOURCE_CONTENT: &str = "1b4460e69780e5080a107bc178b77ffe064585b9712c5f7468a80c02cdee0655";

fn main() {
    if let Err(error) = run() {
        eprintln!("int-gcd-contract-residualization: {error}");
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
    if contract.function_arity != 2 || contract.generalized.binders.len() != 2 {
        return Err("residualized telescope shape changed".to_owned());
    }
    let witness = reflexivity::propose_reflexivity(&mut kernel, contract.source_equation)?;
    let witness_name = nested_name(&mut kernel, &["Axeyum", "Autogenesis", "IntGcdContract"]);
    kernel
        .add_declaration(Declaration::Theorem {
            name: witness_name,
            uparams: vec![],
            ty: contract.source_equation,
            value: witness.proof,
        })
        .map_err(|error| format!("source witness rejected: {error:?}"))?;
    let axioms = rendered_names(&kernel, &kernel.axiom_footprint(witness_name));
    let direct_theorems = rendered_names(&kernel, &kernel.theorem_dependencies(witness_name));
    let transitive_theorems: Vec<_> = kernel
        .declaration_dependency_closure(witness_name)
        .into_iter()
        .filter(|&name| {
            matches!(
                kernel.environment().get(name),
                Some(Declaration::Theorem { .. })
            )
        })
        .map(|name| kernel.display_name(name).to_string())
        .collect();
    let mut output = json!({
        "schema_version": 1,
        "kind": "axeyum-autogenesis-int-gcd-contract-residualization-control",
        "state": "mechanism-control-no-contract-proof-or-ledger-credit",
        "source": {
            "stream_sha256": hex_sha256(&stream),
            "artifact_file": "r018.ndjson",
            "lean_version": report.lean_version,
            "lean_githash": report.lean_githash,
            "definition": "Int.gcd",
            "definition_content_sha256": SOURCE_CONTENT,
        },
        "residualization": {
            "source_binder": "Int.gcd",
            "residual_binders": ["Nat.gcd"],
            "retained_direct_body_constants": ["Int", "Int.natAbs"],
            "function_arity": contract.function_arity,
            "contract_binders": contract.generalized.binders.len(),
            "source_equation_sha256": canonical_expression_sha256(&kernel, contract.source_equation)?,
            "generalized_contract_sha256": canonical_expression_sha256(&kernel, contract.generalized.goal)?,
            "generalized_contract": kernel.render_lean(contract.generalized.goal),
            "specialization_verified": true,
        },
        "source_witness": {
            "producer": "bounded-pi-equality-reflexivity-v1",
            "binders": witness.binders,
            "constructed_nodes": witness.constructed_nodes,
            "proof_sha256": canonical_expression_sha256(&kernel, witness.proof)?,
            "axiom_footprint": axioms,
            "direct_theorem_dependencies": direct_theorems,
            "transitive_theorem_dependencies": transitive_theorems,
        },
        "authority": {
            "partitions_inspected": ["train"],
            "held_out_inspected": false,
            "proof_bodies_inspected": false,
            "producer_target_attempts": 0,
            "contracts_admitted": 0,
            "ledger_writes": 0,
        },
        "limitations": "This proves exact body accounting, residualization, specialization, and source-witness type checking. The witness theorem dependency inventory is diagnostic and grants no premise, target, proof, or ledger credit.",
    });
    let digest = canonical_digest(&output)?;
    output["observation_sha256"] = json!(digest);
    let mut rendered = serde_json::to_string_pretty(&output).map_err(|error| error.to_string())?;
    rendered.push('\n');
    fs::write(&arguments.output, rendered).map_err(|error| error.to_string())?;
    println!(
        "AUTOGENESIS_INT_GCD_CONTRACT_RESIDUALIZATION_OK|{digest}|residual=Nat.gcd|axioms={}|theorems={}|held_out=0|ledger_writes=0",
        axioms.len(),
        transitive_theorems.len()
    );
    Ok(())
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

fn rendered_names(kernel: &Kernel, names: &[NameId]) -> Vec<String> {
    names
        .iter()
        .map(|&name| kernel.display_name(name).to_string())
        .collect()
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
