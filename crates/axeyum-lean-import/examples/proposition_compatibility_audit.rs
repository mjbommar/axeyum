//! Proof-free compatibility audit between an imported goal and a native theorem.
//!
//! The imported target must be a monomorphic transparent definition whose
//! value is the goal proposition. The native side is independently rebuilt;
//! neither theorem proof is rendered or copied, and compatibility grants no
//! admission authority.

use std::fs;
use std::io::Cursor;
use std::path::PathBuf;

use axeyum_lean_import::{ImportLimits, checked_proposition_compatibility, import_ndjson};
use axeyum_lean_kernel::{Declaration, Kernel, NameId, build_int_prelude};
use serde_json::json;

const USAGE: &str = "usage: proposition_compatibility_audit <stream.ndjson> <target-definition> <native-theorem>...";

fn main() {
    if let Err(error) = run() {
        eprintln!("proposition-compatibility-audit: {error}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), String> {
    let mut arguments = std::env::args_os().skip(1);
    let path = arguments.next().map(PathBuf::from).ok_or(USAGE)?;
    let target_name = utf8_argument(arguments.next(), USAGE)?;
    let native_names = arguments
        .map(|argument| {
            argument
                .into_string()
                .map_err(|_| "argument is not valid UTF-8".to_owned())
        })
        .collect::<Result<Vec<_>, _>>()?;
    if native_names.is_empty() {
        return Err(USAGE.to_owned());
    }

    let bytes =
        fs::read(&path).map_err(|error| format!("cannot read {}: {error}", path.display()))?;
    let imported = import_ndjson(Cursor::new(bytes), ImportLimits::default())
        .map_err(|error| format!("stream import failed: {error:?}"))?;
    let target_kernel = imported.kernel();
    let target = exact_name(target_kernel, &target_name)?;
    let target_goal = match target_kernel.environment().get(target) {
        Some(Declaration::Definition { uparams, value, .. }) if uparams.is_empty() => *value,
        _ => {
            return Err(format!(
                "target is not a monomorphic transparent definition: {target_name}"
            ));
        }
    };

    let mut native_kernel = Kernel::new();
    build_int_prelude(&mut native_kernel)
        .map_err(|error| format!("native Int/Nat prelude failed: {error:?}"))?;
    let mut compatible = Vec::new();
    let mut declined = Vec::new();
    for native_name in &native_names {
        let native = match exact_name(&native_kernel, native_name) {
            Ok(native) => native,
            Err(error) => {
                declined.push(json!({
                    "native_theorem": native_name,
                    "reason": error,
                }));
                continue;
            }
        };
        let native_goal = match native_kernel.environment().get(native) {
            Some(Declaration::Theorem { ty, .. }) => *ty,
            _ => {
                return Err(format!(
                    "native declaration is not a theorem: {native_name}"
                ));
            }
        };
        match checked_proposition_compatibility(
            &native_kernel,
            native_goal,
            target_kernel,
            target_goal,
        ) {
            Ok(receipt) => compatible.push(json!({
                "native_theorem": native_name,
                "source_proposition_sha256": receipt.source_proposition_sha256,
                "target_proposition_sha256": receipt.target_proposition_sha256,
                "source_shape_sha256": receipt.source_shape_sha256,
                "target_shape_sha256": receipt.target_shape_sha256,
                "compatibility": "translated-definitional-equality",
            })),
            Err(error) => declined.push(json!({
                "native_theorem": native_name,
                "reason": format!("{error:?}"),
            })),
        }
    }
    println!(
        "{}",
        serde_json::to_string_pretty(&json!({
            "schema_version": 1,
            "kind": "axeyum-proposition-compatibility-audit",
            "target_definition": target_name,
            "candidate_count": native_names.len(),
            "compatible": compatible,
            "declined": declined,
            "proofs_read": 0,
            "admission_authority": false,
        }))
        .map_err(|error| error.to_string())?
    );
    Ok(())
}

fn utf8_argument(argument: Option<std::ffi::OsString>, usage: &str) -> Result<String, String> {
    argument
        .ok_or_else(|| usage.to_owned())?
        .into_string()
        .map_err(|_| "argument is not valid UTF-8".to_owned())
}

fn exact_name(kernel: &Kernel, expected: &str) -> Result<NameId, String> {
    let matches = kernel
        .environment()
        .iter()
        .filter_map(|(&name, _)| {
            (kernel.display_name(name).to_string() == expected).then_some(name)
        })
        .collect::<Vec<_>>();
    match matches.as_slice() {
        [name] => Ok(*name),
        [] => Err(format!("declaration is absent: {expected}")),
        _ => Err(format!("declaration is ambiguous: {expected}")),
    }
}
