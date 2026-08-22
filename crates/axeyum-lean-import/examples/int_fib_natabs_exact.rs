//! Compose the exact, empty-footprint integer Fibonacci `natAbs` bridge.

use std::fmt::Write as _;
use std::fs;
use std::io::Cursor;
use std::path::{Path, PathBuf};

use axeyum_lean_import::{
    ImportLimits, canonical_declaration_sha256, compose_checked_theorem_slice, import_ndjson,
    specialize_checked_theorem, verify_checked_theorem_composition,
    verify_checked_theorem_specialization,
};
use axeyum_lean_kernel::{BinderInfo, Declaration, Kernel, Lean4ExportMetadata, NameId};
use serde_json::{Value, json};
use sha2::{Digest, Sha256};

const HASHES: [&str; 5] = [
    "f0e34ecb1dff747938b7f1079c307af5f4e79e7a67e3bc514feee03e4f30656d",
    "6c803eff520a62d6925db5ed30f78714d9923281becfd78239cc28278bc9159f",
    "0e310823ba37adfbd9087c0da2f85ad57261228d601d9388800cf069b5b2ce82",
    "7df7f5dce9c7159f9c468b6f47f13be3e589fb2c1559af554ce73cc48b18730e",
    "03efd3c14aaac8cb610e72283e783dcf4fcf90bb223112a74b1058b0a05fe793",
];
const LABELS: [&str; 5] = [
    "clean Int.fib base",
    "negative presentations",
    "modulo-two cases",
    "natAbs-neg source",
    "function-abstracted residual",
];
const NEGATIVE_EVEN: &str = "Axeyum.Autogenesis.intFibNegativeEvenV1";
const NEGATIVE_ODD: &str = "Axeyum.Autogenesis.intFibNegativeOddV1";
const MOD_CASES: &str = "Axeyum.IntFib.modCases";
const NAT_ABS_NEG: &str = "Int.natAbs_neg";
const RESIDUAL: &str = "Axeyum.Autogenesis.intFibNatAbsResidualV2";
const NAT_ABS_OF_NAT: &str = "Axeyum.Autogenesis.intNatAbsOfNatV1";
const TARGET: &str = "Axeyum.Autogenesis.intFibNatAbsV1";
const USAGE: &str = "usage: int_fib_natabs_exact <base> <negative-presentations> <mod-cases> <natabs-neg> <residual> <output>";

fn main() {
    if let Err(error) = run() {
        eprintln!("int-fib-natabs-exact: {error}");
        std::process::exit(1);
    }
}

#[allow(clippy::too_many_lines)]
fn run() -> Result<(), String> {
    let mut arguments = std::env::args_os().skip(1);
    let paths = (0..6)
        .map(|_| path(&mut arguments))
        .collect::<Result<Vec<_>, _>>()?;
    if arguments.next().is_some() || paths[5].exists() {
        return Err(USAGE.to_owned());
    }

    let imports = paths[..5]
        .iter()
        .zip(HASHES)
        .zip(LABELS)
        .map(|((path, hash), label)| import_bound(path, hash, label))
        .collect::<Result<Vec<_>, _>>()?;
    for (index, (completed, label)) in imports.iter().zip(LABELS).enumerate() {
        // The official source stream is deliberately broad. Its exact root is
        // checked after slicing; assumptions elsewhere in that stream have no
        // authority over the composed kernel.
        if index != 3 && !completed.report().axioms.is_empty() {
            return Err(format!("{label} stream reaches assumptions"));
        }
    }

    require_bound_root(
        imports[1].kernel(),
        NEGATIVE_EVEN,
        "719bfe6684e7903a60c118dd261df37f10dc30372da9935589b9b4030301c9f0",
    )?;
    require_bound_root(
        imports[1].kernel(),
        NEGATIVE_ODD,
        "fcfd9c8b21b97945fddfd59023f9f9ca2718796a1e41b0d9781ca0ee0f72919d",
    )?;
    require_bound_root(
        imports[3].kernel(),
        NAT_ABS_NEG,
        "5e699010815310a983c3ef94d450aa8fd66bb41ba4dd424d073ad552f13fc2a5",
    )?;

    let mut kernel = imports[0].kernel().clone();
    let composition_receipts = vec![
        compose(
            imports[1].kernel(),
            &mut kernel,
            &[NEGATIVE_EVEN, NEGATIVE_ODD],
            "negative presentations",
        )?,
        compose(
            imports[2].kernel(),
            &mut kernel,
            &[MOD_CASES],
            "modulo-two cases",
        )?,
        compose(
            imports[3].kernel(),
            &mut kernel,
            &[NAT_ABS_NEG],
            "natAbs-neg root",
        )?,
        compose(
            imports[4].kernel(),
            &mut kernel,
            &[RESIDUAL],
            "function-abstracted residual",
        )?,
    ];

    add_nat_abs_of_nat(&mut kernel)?;
    let support = find_name(&kernel, NAT_ABS_OF_NAT)?;
    require_empty(&kernel, support, NAT_ABS_OF_NAT)?;

    let target_receipt = specialize(
        &mut kernel,
        RESIDUAL,
        &[
            "Int.fib",
            "Nat.fib",
            "Int.fib_natCast",
            NEGATIVE_EVEN,
            NEGATIVE_ODD,
            MOD_CASES,
            NAT_ABS_NEG,
            NAT_ABS_OF_NAT,
        ],
        &["Axeyum", "Autogenesis", "intFibNatAbsV1"],
        "exact natAbs target",
    )?;

    let target = find_name(&kernel, TARGET)?;
    require_empty(&kernel, target, TARGET)?;
    let target_evidence = evidence(&kernel, target)?;
    let expected_dependencies = [
        RESIDUAL,
        NEGATIVE_EVEN,
        NEGATIVE_ODD,
        NAT_ABS_OF_NAT,
        MOD_CASES,
        "Int.fib_natCast",
        NAT_ABS_NEG,
    ];
    if names(&kernel, &kernel.theorem_dependencies(target)) != sorted(&expected_dependencies) {
        return Err("exact target dependency set changed".to_owned());
    }

    let bytes = kernel
        .render_lean4export_ndjson_roots(&Lean4ExportMetadata::axeyum("4.30.0"), &[target])
        .map_err(|error| format!("target export failed: {error}"))?;
    for pass in 1..=2 {
        let imported = import_ndjson(Cursor::new(bytes.as_bytes()), ImportLimits::default())
            .map_err(|error| format!("fresh target import {pass} failed: {error:?}"))?;
        let replay_target = find_name(imported.kernel(), TARGET)?;
        if evidence(imported.kernel(), replay_target)? != target_evidence {
            return Err(format!("fresh target import {pass} changed evidence"));
        }
    }
    fs::write(&paths[5], &bytes).map_err(|error| format!("target write failed: {error}"))?;

    println!(
        "{}",
        serde_json::to_string_pretty(&json!({
            "schema_version": 1,
            "kind": "axeyum-int-fib-natabs-exact",
            "state": "exact-target-specialized-exported-and-twice-reimported-empty-footprint",
            "input_sha256": HASHES,
            "composition_receipt_sha256": composition_receipts,
            "support": evidence(&kernel, support)?,
            "target_specialization_receipt_sha256": target_receipt,
            "target": target_evidence,
            "capsule": {"path": paths[5], "bytes": bytes.len(), "sha256": hex_sha256(bytes.as_bytes()), "fresh_imports": 2},
            "execution": {"complete_invocations": 1, "input_stream_reads": 5, "composition_operations": 4, "composition_replays": 4, "support_theorem_submissions": 1, "target_specializations": 1, "target_specialization_replays": 1, "target_exports": 1, "fresh_target_imports": 2, "retries": 0, "ledger_writes": 0},
            "rendered_material": {"proof_terms": 0, "theorem_types": 0, "theorem_values": 0}
        }))
        .map_err(|error| error.to_string())?
    );
    Ok(())
}

fn add_nat_abs_of_nat(kernel: &mut Kernel) -> Result<(), String> {
    let name = nested_name(kernel, &["Axeyum", "Autogenesis", "intNatAbsOfNatV1"]);
    if kernel.environment().get(name).is_some() {
        return Err("natAbs-ofNat support exists before submission".to_owned());
    }
    let nat = find_name(kernel, "Nat")?;
    let int_of_nat = find_name(kernel, "Int.ofNat")?;
    let nat_abs = find_name(kernel, "Int.natAbs")?;
    let eq = find_name(kernel, "Eq")?;
    let eq_refl = find_name(kernel, "Eq.refl")?;
    let zero = kernel.level_zero();
    let nat_level = kernel.level_succ(zero);
    let nat_ty = kernel.const_(nat, vec![]);
    let n = kernel.bvar(0);
    let of_nat_const = kernel.const_(int_of_nat, vec![]);
    let of_nat_n = kernel.app(of_nat_const, n);
    let nat_abs_const = kernel.const_(nat_abs, vec![]);
    let nat_abs_of_nat = kernel.app(nat_abs_const, of_nat_n);
    let eq_const = kernel.const_(eq, vec![nat_level]);
    let eq_nat = kernel.app(eq_const, nat_ty);
    let eq_left = kernel.app(eq_nat, nat_abs_of_nat);
    let proposition = kernel.app(eq_left, n);
    let refl_const = kernel.const_(eq_refl, vec![nat_level]);
    let refl_nat = kernel.app(refl_const, nat_ty);
    let refl_n = kernel.app(refl_nat, n);
    let anonymous = kernel.anon();
    let ty = kernel.pi(anonymous, nat_ty, proposition, BinderInfo::Default);
    let value = kernel.lam(anonymous, nat_ty, refl_n, BinderInfo::Default);
    kernel
        .add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty,
            value,
        })
        .map_err(|error| format!("natAbs-ofNat support submission failed: {error:?}"))
}

fn compose(
    source: &Kernel,
    target: &mut Kernel,
    roots: &[&str],
    label: &str,
) -> Result<String, String> {
    let completed = compose_checked_theorem_slice(source, target, roots)
        .map_err(|error| format!("{label} composition declined: {error:?}"))?;
    verify_checked_theorem_composition(source, target, completed.kernel(), completed.receipt())
        .map_err(|error| format!("{label} composition replay failed: {error:?}"))?;
    let receipt = completed.receipt().receipt_sha256.clone();
    *target = completed.kernel().clone();
    Ok(receipt)
}

fn specialize(
    kernel: &mut Kernel,
    generic: &str,
    arguments: &[&str],
    target_parts: &[&str],
    label: &str,
) -> Result<String, String> {
    let generic_name = find_name(kernel, generic)?;
    let argument_names = arguments
        .iter()
        .map(|argument| find_name(kernel, argument))
        .collect::<Result<Vec<_>, _>>()?;
    let target_name = nested_name(kernel, target_parts);
    if kernel.environment().get(target_name).is_some() {
        return Err(format!("{label} exists before specialization"));
    }
    let completed = specialize_checked_theorem(kernel, generic_name, &argument_names, target_name)
        .map_err(|error| format!("{label} specialization declined: {error:?}"))?;
    verify_checked_theorem_specialization(
        kernel,
        completed.kernel(),
        generic_name,
        &argument_names,
        target_name,
        completed.receipt(),
    )
    .map_err(|error| format!("{label} specialization replay failed: {error:?}"))?;
    let receipt = completed.receipt().receipt_sha256.clone();
    *kernel = completed.kernel().clone();
    Ok(receipt)
}

fn path(arguments: &mut impl Iterator<Item = std::ffi::OsString>) -> Result<PathBuf, String> {
    arguments
        .next()
        .map(PathBuf::from)
        .ok_or_else(|| USAGE.to_owned())
}

fn import_bound(
    path: &Path,
    expected_sha256: &str,
    label: &str,
) -> Result<axeyum_lean_import::CompletedImport, String> {
    let bytes = fs::read(path).map_err(|error| format!("{label} read failed: {error}"))?;
    let actual = hex_sha256(&bytes);
    if actual != expected_sha256 {
        return Err(format!(
            "{label} identity changed: expected {expected_sha256}, got {actual}"
        ));
    }
    import_ndjson(Cursor::new(bytes), ImportLimits::default())
        .map_err(|error| format!("{label} import failed: {error:?}"))
}

fn require_bound_root(
    kernel: &Kernel,
    rendered: &str,
    expected_sha256: &str,
) -> Result<(), String> {
    let theorem = find_name(kernel, rendered)?;
    require_empty(kernel, theorem, rendered)?;
    let actual = canonical_declaration_sha256(kernel, theorem)?;
    if actual == expected_sha256 {
        Ok(())
    } else {
        Err(format!(
            "{rendered} identity changed: expected {expected_sha256}, got {actual}"
        ))
    }
}

fn require_empty(kernel: &Kernel, theorem: NameId, label: &str) -> Result<(), String> {
    let footprint = names(kernel, &kernel.axiom_footprint(theorem));
    if footprint.is_empty() {
        Ok(())
    } else {
        Err(format!("{label} reaches assumptions: {footprint:?}"))
    }
}

fn evidence(kernel: &Kernel, theorem: NameId) -> Result<Value, String> {
    if !matches!(
        kernel.environment().get(theorem),
        Some(Declaration::Theorem { .. })
    ) {
        return Err(format!("{} is not a theorem", kernel.display_name(theorem)));
    }
    Ok(json!({
        "name": kernel.display_name(theorem).to_string(),
        "declaration_sha256": canonical_declaration_sha256(kernel, theorem)?,
        "axiom_footprint": names(kernel, &kernel.axiom_footprint(theorem)),
        "direct_theorem_dependencies": names(kernel, &kernel.theorem_dependencies(theorem)),
    }))
}

fn find_name(kernel: &Kernel, expected: &str) -> Result<NameId, String> {
    let found = kernel
        .environment()
        .iter()
        .filter_map(|(&name, _)| {
            (kernel.display_name(name).to_string() == expected).then_some(name)
        })
        .collect::<Vec<_>>();
    match found.as_slice() {
        [name] => Ok(*name),
        [] => Err(format!("declaration is absent: {expected}")),
        _ => Err(format!("declaration is ambiguous: {expected}")),
    }
}

fn nested_name(kernel: &mut Kernel, parts: &[&str]) -> NameId {
    parts
        .iter()
        .fold(kernel.anon(), |prefix, part| kernel.name_str(prefix, *part))
}

fn names(kernel: &Kernel, values: &[NameId]) -> Vec<String> {
    let mut rendered = values
        .iter()
        .map(|&name| kernel.display_name(name).to_string())
        .collect::<Vec<_>>();
    rendered.sort();
    rendered
}

fn sorted(values: &[&str]) -> Vec<String> {
    let mut rendered = values
        .iter()
        .map(|value| (*value).to_owned())
        .collect::<Vec<_>>();
    rendered.sort();
    rendered
}

fn hex_sha256(bytes: &[u8]) -> String {
    let mut output = String::with_capacity(64);
    for byte in Sha256::digest(bytes) {
        write!(&mut output, "{byte:02x}").expect("String writes cannot fail");
    }
    output
}
