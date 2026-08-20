//! Compose and specialize the constructive `Nat.mod` divisibility invariant.

use std::fs;
use std::io::Cursor;
use std::path::PathBuf;

use axeyum_lean_import::{
    CheckedTheoremCompositionError, ImportLimits, checked_reused_declaration_compatibility,
    compose_checked_theorem_slice, compose_checked_theorem_slice_with_target_leaves, import_ndjson,
    specialize_checked_theorem, verify_checked_theorem_composition,
    verify_checked_theorem_specialization,
};
use axeyum_lean_kernel::{Kernel, NameId, build_nat_prelude};
use serde_json::{Value, json};
use sha2::{Digest, Sha256};

const GENERIC_THEOREM: &str = "Axeyum.Autogenesis.modSucc_dvd_iff";
const TARGET_THEOREM: &str = "Nat.dvd_mod_iff";
const HELPER_ROOTS: [&str; 3] = [
    "Nat.dvd_add_iff_right",
    "Nat.sub_add_cancel",
    "Nat.add_comm",
];
const ARGUMENTS: [&str; 4] = [
    "Nat.dvd",
    "Nat.dvd_add_iff_right",
    "Nat.sub_add_cancel",
    "Nat.add_comm",
];

fn main() {
    if let Err(error) = run() {
        eprintln!("nat-mod-invariant-specialization: {error}");
        std::process::exit(1);
    }
}

// This is one linear assurance pipeline; splitting it would hide the exact
// compose -> replay -> specialize -> replay -> compatibility order.
#[allow(clippy::too_many_lines)]
fn run() -> Result<(), String> {
    let mut arguments = std::env::args_os().skip(1);
    let proof_path = arguments
        .next()
        .map(PathBuf::from)
        .ok_or("usage: nat_mod_invariant_specialization <proof.ndjson> <target.ndjson>")?;
    let target_path = arguments
        .next()
        .map(PathBuf::from)
        .ok_or("usage: nat_mod_invariant_specialization <proof.ndjson> <target.ndjson>")?;
    let probe_dvd_gcd = match arguments.next() {
        None => false,
        Some(flag) if flag == "--probe-dvd-gcd" => true,
        Some(_) => return Err("unexpected trailing argument".to_owned()),
    };
    if arguments.next().is_some() {
        return Err("unexpected trailing argument".to_owned());
    }

    let proof_bytes = fs::read(proof_path).map_err(|error| error.to_string())?;
    let target_bytes = fs::read(target_path).map_err(|error| error.to_string())?;
    let proof = import_ndjson(Cursor::new(proof_bytes), ImportLimits::default())
        .map_err(|error| format!("proof import failed: {error:?}"))?;
    let target = import_ndjson(Cursor::new(target_bytes), ImportLimits::default())
        .map_err(|error| format!("target import failed: {error:?}"))?;
    if !proof.report().axioms.is_empty() || !target.report().axioms.is_empty() {
        return Err("both imports must be proof-isolated".to_owned());
    }

    let generic =
        compose_checked_theorem_slice(proof.kernel(), target.kernel(), &[GENERIC_THEOREM])
            .map_err(|error| format!("generic proof composition declined: {error:?}"))?;
    verify_checked_theorem_composition(
        proof.kernel(),
        target.kernel(),
        generic.kernel(),
        generic.receipt(),
    )
    .map_err(|error| format!("generic proof composition did not replay: {error:?}"))?;
    require_empty_added_footprints(
        generic
            .receipt()
            .added_theorems
            .iter()
            .map(|row| (row.name.as_str(), row.axiom_footprint.as_slice())),
    )?;

    let mut native = Kernel::new();
    build_nat_prelude(&mut native)
        .map_err(|error| format!("native Nat reference build failed: {error:?}"))?;
    let helpers = compose_checked_theorem_slice(&native, generic.kernel(), &HELPER_ROOTS)
        .map_err(|error| format!("native helper composition declined: {error:?}"))?;
    verify_checked_theorem_composition(
        &native,
        generic.kernel(),
        helpers.kernel(),
        helpers.receipt(),
    )
    .map_err(|error| format!("native helper composition did not replay: {error:?}"))?;
    require_empty_added_footprints(
        helpers
            .receipt()
            .added_theorems
            .iter()
            .map(|row| (row.name.as_str(), row.axiom_footprint.as_slice())),
    )?;

    let mut prepared = helpers.kernel().clone();
    let generic_name = find_name(&prepared, GENERIC_THEOREM)?;
    let argument_names = ARGUMENTS
        .iter()
        .map(|name| find_name(&prepared, name))
        .collect::<Result<Vec<_>, _>>()?;
    let nat_name = find_name(&prepared, "Nat")?;
    let target_name = prepared.name_str(nat_name, "dvd_mod_iff");
    let specialized =
        specialize_checked_theorem(&prepared, generic_name, &argument_names, target_name)
            .map_err(|error| format!("specialization declined: {error:?}"))?;
    verify_checked_theorem_specialization(
        &prepared,
        specialized.kernel(),
        generic_name,
        &argument_names,
        target_name,
        specialized.receipt(),
    )
    .map_err(|error| format!("specialization did not replay: {error:?}"))?;
    let compatibility =
        checked_reused_declaration_compatibility(&native, specialized.kernel(), TARGET_THEOREM)
            .map_err(|error| format!("native target type compatibility failed: {error:?}"))?;

    let mut output = json!({
        "schema_version": 1,
        "kind": "axeyum-nat-mod-invariant-specialization",
        "lean_version": proof.report().lean_version,
        "generic_composition": {
            "root": GENERIC_THEOREM,
            "source_closure": generic.receipt().source_closure.len(),
            "reused": generic.receipt().reused_declarations.len(),
            "added_theorems": generic.receipt().added_theorems.len(),
            "added_definitions": generic.receipt().added_definitions.len(),
            "receipt_sha256": generic.receipt().receipt_sha256,
        },
        "helper_composition": {
            "roots": HELPER_ROOTS,
            "source_closure": helpers.receipt().source_closure.len(),
            "reused": helpers.receipt().reused_declarations.len(),
            "added_theorems": helpers.receipt().added_theorems.len(),
            "added_definitions": helpers.receipt().added_definitions.len(),
            "receipt_sha256": helpers.receipt().receipt_sha256,
        },
        "specialization": {
            "source": specialized.receipt().source_theorem,
            "arguments": specialized.receipt().arguments.iter().map(|row| &row.name).collect::<Vec<_>>(),
            "target": specialized.receipt().target_theorem,
            "target_sha256": specialized.receipt().target_theorem_sha256,
            "axiom_footprint": specialized.receipt().axiom_footprint,
            "receipt_sha256": specialized.receipt().receipt_sha256,
            "native_type_compatibility": compatibility.compatibility.as_str(),
            "native_type_shape_sha256": compatibility.source_type_shape_sha256,
            "specialized_type_shape_sha256": compatibility.target_type_shape_sha256,
        },
    });
    if probe_dvd_gcd {
        output["target_leaf_probe"] = probe_dvd_gcd_target_leaves(&native, specialized.kernel())?;
    }
    println!(
        "{}",
        serde_json::to_string_pretty(&output).map_err(|error| error.to_string())?
    );
    Ok(())
}

fn probe_dvd_gcd_target_leaves(source: &Kernel, target: &Kernel) -> Result<Value, String> {
    let first = probe_decline(source, target, &["Nat.dvd_mod_iff"], "Nat.div_mod_exec")?;
    let second = probe_decline(
        source,
        target,
        &["Nat.dvd_mod_iff", "Nat.mod_lt"],
        "Nat.gcd_succ",
    )?;
    Ok(json!({
        "root": "Nat.dvd_gcd",
        "single_leaf": first,
        "two_leaves": second,
        "private_clone_publications": 0,
        "proof_search_invocations": 0,
        "ledger_writes": 0,
    }))
}

fn probe_decline(
    source: &Kernel,
    target: &Kernel,
    leaves: &[&str],
    expected_rejected: &str,
) -> Result<Value, String> {
    let root = find_name(source, "Nat.dvd_gcd")?;
    let leaf_ids = leaves
        .iter()
        .map(|leaf| find_name(source, leaf))
        .collect::<Result<Vec<_>, _>>()?;
    let closure = source
        .root_declaration_closure_with_theorem_leaves(&[root], &leaf_ids)
        .map_err(|error| format!("target-leaf closure failed: {error:?}"))?;
    let closure_names = closure
        .iter()
        .map(|&name| source.display_name(name).to_string())
        .collect::<Vec<_>>();
    let target_len = target.environment().len();
    let decline =
        compose_checked_theorem_slice_with_target_leaves(source, target, &["Nat.dvd_gcd"], leaves)
            .expect_err("the measured target-leaf frontier must remain a decline");
    if target.environment().len() != target_len {
        return Err("declined target-leaf composition changed its caller".to_owned());
    }
    let CheckedTheoremCompositionError::AdmissionRejected { name, error } = decline else {
        return Err(format!(
            "target-leaf composition declined at an unexpected boundary: {decline:?}"
        ));
    };
    if name != expected_rejected {
        return Err(format!(
            "target-leaf composition rejected {name}, expected {expected_rejected}"
        ));
    }
    let error_kind = error
        .split_once(' ')
        .map_or(error.as_str(), |(kind, _)| kind);
    Ok(json!({
        "target_theorem_leaves": leaves,
        "source_closure": closure.len(),
        "contains_nat_div_mod_exec": closure_names.iter().any(|name| name == "Nat.div_mod_exec"),
        "contains_nat_gcd_succ": closure_names.iter().any(|name| name == "Nat.gcd_succ"),
        "outcome": "declined",
        "first_rejected": name,
        "error_kind": error_kind,
        "error_sha256": hex_sha256(error.as_bytes()),
        "caller_declarations_before": target_len,
        "caller_declarations_after": target.environment().len(),
    }))
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

fn find_name(kernel: &Kernel, rendered: &str) -> Result<NameId, String> {
    kernel
        .environment()
        .iter()
        .find_map(|(&name, _)| (kernel.display_name(name).to_string() == rendered).then_some(name))
        .ok_or_else(|| format!("missing declaration: {rendered}"))
}

fn require_empty_added_footprints<'a>(
    rows: impl Iterator<Item = (&'a str, &'a [String])>,
) -> Result<(), String> {
    for (name, footprint) in rows {
        if !footprint.is_empty() {
            return Err(format!(
                "composition added assumption-bearing theorem {name}: {footprint:?}"
            ));
        }
    }
    Ok(())
}
