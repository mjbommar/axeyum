//! Probe whether checked imported `Nat.fib` can be rebuilt over the native Nat prelude.

use std::fs;
use std::io::Cursor;
use std::path::PathBuf;

use axeyum_lean_import::{
    ImportLimits, canonical_declaration_sha256, compose_checked_theorem_slice, import_ndjson,
    verify_checked_theorem_composition,
};
use axeyum_lean_kernel::{BinderInfo, Declaration, Kernel, NameId, build_nat_prelude};
use serde_json::json;
use sha2::{Digest, Sha256};

const CONTROL: &str = "Axeyum.Autogenesis.fib_definition_probe";
const STREAM_SHA256: &str = "6afa79d79481403d3e3273ea3eea26b4d1194762f9bd623ec019f8e821323cfd";

fn main() {
    if let Err(error) = run() {
        eprintln!("nat-fib-native-definition-probe: {error}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), String> {
    let mut arguments = std::env::args_os().skip(1);
    let path = arguments
        .next()
        .map(PathBuf::from)
        .ok_or("usage: nat_fib_native_definition_probe <r082.ndjson>")?;
    if arguments.next().is_some() {
        return Err("unexpected trailing argument".to_owned());
    }
    let bytes = fs::read(path).map_err(|error| error.to_string())?;
    if hex_sha256(&bytes) != STREAM_SHA256 {
        return Err("r082 stream identity changed".to_owned());
    }
    let imported = import_ndjson(Cursor::new(bytes), ImportLimits::default())
        .map_err(|error| format!("source import failed: {error:?}"))?;
    if imported.report().lean_version != "4.30.0"
        || imported.report().lean_githash != "d024af099ca4bf2c86f649261ebf59565dc8c622"
        || !imported.report().axioms.is_empty()
    {
        return Err("source authority changed".to_owned());
    }
    let (mut source, report) = imported.into_parts();
    let fib_declaration_sha256 =
        canonical_declaration_sha256(&source, find_name(&source, "Nat.fib")?)
            .map_err(|error| error.to_string())?;
    add_fib_reflexivity_control(&mut source)?;

    let mut native = Kernel::new();
    build_nat_prelude(&mut native)
        .map_err(|error| format!("native Nat prelude failed to build: {error:?}"))?;
    let target_before = native.environment().len();
    let root = find_name(&source, CONTROL)?;
    let closure = source
        .root_declaration_closure(&[root])
        .map_err(|error| format!("source closure failed: {error:?}"))?;
    let source_only_declarations = closure
        .iter()
        .filter_map(|name| {
            let rendered = source.display_name(*name).to_string();
            native
                .environment()
                .iter()
                .all(|(&candidate, _)| native.display_name(candidate).to_string() != rendered)
                .then_some(rendered)
        })
        .collect::<Vec<_>>();
    let completed = compose_checked_theorem_slice(&source, &native, &[CONTROL])
        .map_err(|error| format!("checked definition composition declined: {error:?}"))?;
    verify_checked_theorem_composition(&source, &native, completed.kernel(), completed.receipt())
        .map_err(|error| format!("checked definition composition did not replay: {error:?}"))?;
    if native.environment().len() != target_before {
        return Err("composition mutated the native caller".to_owned());
    }
    if completed
        .receipt()
        .added_theorems
        .iter()
        .any(|row| !row.axiom_footprint.is_empty())
    {
        return Err("composition added an assumption-bearing theorem".to_owned());
    }
    if completed
        .receipt()
        .added_definitions
        .iter()
        .all(|row| row.name != "Nat.fib")
        || completed.receipt().added_theorems.len() != 1
        || completed.receipt().added_theorems[0].name != CONTROL
    {
        return Err("composition did not add exactly the requested fib control".to_owned());
    }

    println!(
        "{}",
        serde_json::to_string_pretty(&json!({
            "schema_version": 1,
            "kind": "axeyum-nat-fib-native-definition-probe",
            "lean_version": report.lean_version,
            "lean_githash": report.lean_githash,
            "source_stream_sha256": STREAM_SHA256,
            "nat_fib_declaration_sha256": fib_declaration_sha256,
            "root": CONTROL,
            "source_closure": completed.receipt().source_closure.len(),
            "source_only_declarations": source_only_declarations,
            "reused_declarations": completed.receipt().reused_declarations.len(),
            "added_definitions": completed.receipt().added_definitions.iter().map(|row| &row.name).collect::<Vec<_>>(),
            "added_singleton_inductives": completed.receipt().added_singleton_inductives.iter().map(|row| &row.family).collect::<Vec<_>>(),
            "added_theorems": completed.receipt().added_theorems.iter().map(|row| &row.name).collect::<Vec<_>>(),
            "added_axiom_footprints": completed.receipt().added_theorems.iter().map(|row| (&row.name, &row.axiom_footprint)).collect::<Vec<_>>(),
            "contains_nat_fib_after": find_name(completed.kernel(), "Nat.fib").is_ok(),
            "caller_declarations_before": target_before,
            "caller_declarations_after": native.environment().len(),
            "completed_declarations": completed.kernel().environment().len(),
            "receipt_sha256": completed.receipt().receipt_sha256,
            "proof_search_invocations": 0,
            "ledger_writes": 0,
        }))
        .map_err(|error| error.to_string())?
    );
    Ok(())
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

fn add_fib_reflexivity_control(kernel: &mut Kernel) -> Result<(), String> {
    let nat = find_name(kernel, "Nat")?;
    let fib = find_name(kernel, "Nat.fib")?;
    let eq = find_name(kernel, "Eq")?;
    let eq_refl = find_name(kernel, "Eq.refl")?;
    let zero = kernel.level_zero();
    let nat_level = kernel.level_succ(zero);
    let nat_ty = kernel.const_(nat, vec![]);
    let n = kernel.bvar(0);
    let fib_const = kernel.const_(fib, vec![]);
    let fib_n = kernel.app(fib_const, n);
    let eq_const = kernel.const_(eq, vec![nat_level]);
    let eq_nat = kernel.app(eq_const, nat_ty);
    let eq_nat_fib_n = kernel.app(eq_nat, fib_n);
    let eq_fib_n = kernel.app(eq_nat_fib_n, fib_n);
    let refl_const = kernel.const_(eq_refl, vec![nat_level]);
    let refl_nat = kernel.app(refl_const, nat_ty);
    let refl_fib_n = kernel.app(refl_nat, fib_n);
    let anonymous = kernel.anon();
    let ty = kernel.pi(anonymous, nat_ty, eq_fib_n, BinderInfo::Default);
    let value = kernel.lam(anonymous, nat_ty, refl_fib_n, BinderInfo::Default);
    let control = kernel.name_str(anonymous, CONTROL);
    kernel
        .add_declaration(Declaration::Theorem {
            name: control,
            uparams: vec![],
            ty,
            value,
        })
        .map_err(|error| format!("source control theorem failed: {error:?}"))?;
    Ok(())
}

fn find_name(kernel: &Kernel, rendered: &str) -> Result<NameId, String> {
    kernel
        .environment()
        .iter()
        .find_map(|(&name, _)| (kernel.display_name(name).to_string() == rendered).then_some(name))
        .ok_or_else(|| format!("missing declaration: {rendered}"))
}
