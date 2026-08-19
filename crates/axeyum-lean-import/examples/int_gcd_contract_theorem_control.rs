//! One preregistered contract-to-theorem bridge invocation for `Int.gcd_def`.

use std::collections::BTreeMap;
use std::env;
use std::fs;
use std::io::Cursor;
use std::path::PathBuf;

use axeyum_lean_import::{
    ConstantInstance, ImportLimits, TRACE_BACKED_SEMANTIC_THEOREM_RECEIPT_VERSION,
    canonical_declaration_sha256, import_ndjson, issue_trace_backed_semantic_theorem_receipt,
    issue_trace_backed_source_contract_receipt, verify_trace_backed_semantic_theorem_receipt,
};
use axeyum_lean_kernel::{Kernel, NameId};
use serde_json::{Value, json};
use sha2::{Digest, Sha256};

const SOURCE_CONTENT: &str = "1b4460e69780e5080a107bc178b77ffe064585b9712c5f7468a80c02cdee0655";
const SOURCE_POLICY: &str = "mathlib-int-gcd-trace-backed-contract-v1";
const SOURCE_RECEIPT: &str = "ae7585751df713ac8fda6f611c3197b0917c9001dc8bda134e9a43416ce3ec82";
const THEOREM_POLICY: &str = "int-gcd-contract-theorem-control-v1";

fn main() {
    if let Err(error) = run() {
        eprintln!("int-gcd-contract-theorem-control: {error}");
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
    let source_receipt = issue_trace_backed_source_contract_receipt(
        &mut kernel,
        &source,
        std::slice::from_ref(&residual),
        &retained,
        SOURCE_POLICY,
    )
    .map_err(|error| error.to_string())?;
    if source_receipt.receipt_sha256 != SOURCE_RECEIPT {
        return Err("preregistered source-contract receipt changed".to_owned());
    }
    let theorem_name = nested_name(&mut kernel, &["Axeyum", "Autogenesis", "IntGcdDef"]);
    let theorem_receipt = issue_trace_backed_semantic_theorem_receipt(
        &mut kernel,
        &source_receipt,
        &source,
        std::slice::from_ref(&residual),
        &retained,
        theorem_name,
        THEOREM_POLICY,
    )
    .map_err(|error| error.to_string())?;
    verify_trace_backed_semantic_theorem_receipt(
        &theorem_receipt,
        &mut kernel,
        &source_receipt,
        &source,
        std::slice::from_ref(&residual),
        &retained,
        theorem_name,
    )
    .map_err(|error| error.to_string())?;
    if theorem_receipt.schema_version != TRACE_BACKED_SEMANTIC_THEOREM_RECEIPT_VERSION
        || theorem_receipt.policy_version != THEOREM_POLICY
        || theorem_receipt.source_contract_receipt_sha256 != SOURCE_RECEIPT
        || theorem_receipt.source_equation_sha256 != source_receipt.source_equation_sha256
        || theorem_receipt.operation != "trace-contract-reflexivity-v1"
        || theorem_receipt.binders != 2
        || theorem_receipt.constructed_nodes != 5
        || theorem_receipt.theorem_name != "Axeyum.Autogenesis.IntGcdDef"
        || !theorem_receipt.axiom_footprint.is_empty()
        || !theorem_receipt.has_valid_digest()
    {
        return Err("exact theorem receipt contract changed".to_owned());
    }
    let receipt_json: Value = serde_json::from_str(
        &theorem_receipt
            .to_pretty_json()
            .map_err(|error| error.to_string())?,
    )
    .map_err(|error| error.to_string())?;
    let mut output = json!({
        "schema_version": 1,
        "kind": "axeyum-autogenesis-int-gcd-contract-theorem-control",
        "state": "calibration-theorem-receipt-issued-no-evaluation-or-ledger-credit",
        "source": {
            "stream_sha256": hex_sha256(&stream),
            "artifact_file": "r018.ndjson",
            "lean_version": report.lean_version,
            "lean_githash": report.lean_githash,
            "definition": "Int.gcd",
            "definition_content_sha256": SOURCE_CONTENT,
        },
        "source_contract_receipt_sha256": SOURCE_RECEIPT,
        "semantic_theorem_receipt": receipt_json,
        "assurance": {
            "source_contract_receipt_replayed": true,
            "producer_operation": "trace-contract-reflexivity-v1",
            "producer_invocations": 1,
            "producer_retries": 0,
            "binders": 2,
            "constructed_nodes": 5,
            "kernel_accepted": true,
            "theorem_axioms": 0,
            "theorem_receipt_reissued_exactly": true,
            "dependency_inventory_is_diagnostic_only": true,
        },
        "authority": {
            "partitions_inspected": ["train"],
            "held_out_inspected": false,
            "proof_bodies_inspected": false,
            "source_contract_receipts_consumed": 1,
            "semantic_theorem_receipts_issued": 1,
            "evaluation_credit": 0,
            "ledger_writes": 0,
        },
        "limitations": "This is one preregistered calibration invocation. It validates the source-contract-to-theorem seam but establishes no evaluation target or fact-ledger row and does not establish either premise of Int.gcd_fib.",
    });
    let digest = canonical_digest(&output)?;
    output["observation_sha256"] = json!(digest);
    let mut rendered = serde_json::to_string_pretty(&output).map_err(|error| error.to_string())?;
    rendered.push('\n');
    fs::write(&arguments.output, rendered).map_err(|error| error.to_string())?;
    println!(
        "AUTOGENESIS_INT_GCD_CONTRACT_THEOREM_CONTROL_OK|{digest}|target=Int.gcd_def|binders=2|nodes=5|invocations=1|axioms=0|theorem_receipts=1|evaluation=0|held_out=0|ledger_writes=0"
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
