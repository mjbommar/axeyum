//! Reconstruct an axiom-free official `Nat.gcd_succ` theorem and retry the
//! native `Nat.dvd_gcd` composition frontier with it as a target-owned leaf.

use std::fs;
use std::io::Cursor;
use std::path::PathBuf;

use axeyum_lean_import::{
    CheckedTheoremCompositionError, ImportLimits, checked_reused_declaration_compatibility,
    compose_checked_theorem_slice, compose_checked_theorem_slice_with_target_leaves, import_ndjson,
    specialize_checked_theorem, verify_checked_theorem_composition,
    verify_checked_theorem_composition_with_target_leaves, verify_checked_theorem_specialization,
};
use axeyum_lean_kernel::{Kernel, NameId, build_nat_prelude};
use serde_json::{Value, json};

const MOD_INVARIANT_GENERIC: &str = "Axeyum.Autogenesis.modSucc_dvd_iff";
const MOD_INVARIANT_HELPERS: [&str; 3] = [
    "Nat.dvd_add_iff_right",
    "Nat.sub_add_cancel",
    "Nat.add_comm",
];
const MOD_INVARIANT_ARGUMENTS: [&str; 4] = [
    "Nat.dvd",
    "Nat.dvd_add_iff_right",
    "Nat.sub_add_cancel",
    "Nat.add_comm",
];
const MOD_LT_SUCC_GENERIC: &str = "Axeyum.Autogenesis.modLtSucc";
const GCD_SUCC_GENERIC: &str = "Axeyum.Autogenesis.nat_gcd_succ";
const MOD_LT_SUCC_TARGET: &str = "Axeyum.Autogenesis.ModLtSucc";
const GCD_SUCC_TARGET: &str = "Nat.gcd_succ";
const DVD_GCD_LEAVES: [&str; 3] = ["Nat.dvd_mod_iff", "Nat.mod_lt", "Nat.gcd_succ"];

fn main() {
    if let Err(error) = run() {
        eprintln!("nat-gcd-succ-specialization: {error}");
        std::process::exit(1);
    }
}

#[allow(clippy::too_many_lines)]
fn run() -> Result<(), String> {
    let mut arguments = std::env::args_os().skip(1);
    let mod_invariant_path = required_path(&mut arguments, "mod-invariant.ndjson")?;
    let target_path = required_path(&mut arguments, "target.ndjson")?;
    let gcd_bridge_path = required_path(&mut arguments, "gcd-bridge.ndjson")?;
    if arguments.next().is_some() {
        return Err("unexpected trailing argument".to_owned());
    }

    let mod_invariant = import(&mod_invariant_path, "mod-invariant")?;
    let target = import(&target_path, "target")?;
    let gcd_bridge = import(&gcd_bridge_path, "gcd-bridge")?;
    if !mod_invariant.report().axioms.is_empty()
        || !target.report().axioms.is_empty()
        || !gcd_bridge.report().axioms.is_empty()
    {
        return Err("all three imports must be proof-isolated".to_owned());
    }

    let generic_mod = compose_checked_theorem_slice(
        mod_invariant.kernel(),
        target.kernel(),
        &[MOD_INVARIANT_GENERIC],
    )
    .map_err(|error| format!("mod-invariant composition declined: {error:?}"))?;
    verify_checked_theorem_composition(
        mod_invariant.kernel(),
        target.kernel(),
        generic_mod.kernel(),
        generic_mod.receipt(),
    )
    .map_err(|error| format!("mod-invariant composition did not replay: {error:?}"))?;

    let mut native = Kernel::new();
    build_nat_prelude(&mut native)
        .map_err(|error| format!("native Nat reference build failed: {error:?}"))?;
    let helpers =
        compose_checked_theorem_slice(&native, generic_mod.kernel(), &MOD_INVARIANT_HELPERS)
            .map_err(|error| format!("mod-invariant helper composition declined: {error:?}"))?;
    verify_checked_theorem_composition(
        &native,
        generic_mod.kernel(),
        helpers.kernel(),
        helpers.receipt(),
    )
    .map_err(|error| format!("mod-invariant helper composition did not replay: {error:?}"))?;

    let mut mod_prepared = helpers.kernel().clone();
    let mod_invariant_source = find_name(&mod_prepared, MOD_INVARIANT_GENERIC)?;
    let mod_invariant_arguments = MOD_INVARIANT_ARGUMENTS
        .iter()
        .map(|name| find_name(&mod_prepared, name))
        .collect::<Result<Vec<_>, _>>()?;
    let nat = find_name(&mod_prepared, "Nat")?;
    let dvd_mod_iff = mod_prepared.name_str(nat, "dvd_mod_iff");
    let mod_specialized = specialize_checked_theorem(
        &mod_prepared,
        mod_invariant_source,
        &mod_invariant_arguments,
        dvd_mod_iff,
    )
    .map_err(|error| format!("Nat.dvd_mod_iff specialization declined: {error:?}"))?;
    verify_checked_theorem_specialization(
        &mod_prepared,
        mod_specialized.kernel(),
        mod_invariant_source,
        &mod_invariant_arguments,
        dvd_mod_iff,
        mod_specialized.receipt(),
    )
    .map_err(|error| format!("Nat.dvd_mod_iff specialization did not replay: {error:?}"))?;

    let bridge = compose_checked_theorem_slice(
        gcd_bridge.kernel(),
        mod_specialized.kernel(),
        &[MOD_LT_SUCC_GENERIC, GCD_SUCC_GENERIC],
    )
    .map_err(|error| format!("gcd bridge composition declined: {error:?}"))?;
    verify_checked_theorem_composition(
        gcd_bridge.kernel(),
        mod_specialized.kernel(),
        bridge.kernel(),
        bridge.receipt(),
    )
    .map_err(|error| format!("gcd bridge composition did not replay: {error:?}"))?;
    require_empty_added_footprints(
        bridge
            .receipt()
            .added_theorems
            .iter()
            .map(|row| (row.name.as_str(), row.axiom_footprint.as_slice())),
    )?;

    let mut bridge_prepared = bridge.kernel().clone();
    let mod_lt_succ_source = find_name(&bridge_prepared, MOD_LT_SUCC_GENERIC)?;
    let mod_lt = find_name(&bridge_prepared, "Nat.mod_lt")?;
    let mod_lt_succ_target = nested_name(
        &mut bridge_prepared,
        &["Axeyum", "Autogenesis", "ModLtSucc"],
    );
    let mod_lt_succ = specialize_checked_theorem(
        &bridge_prepared,
        mod_lt_succ_source,
        &[mod_lt],
        mod_lt_succ_target,
    )
    .map_err(|error| format!("successor-mod bound specialization declined: {error:?}"))?;
    verify_checked_theorem_specialization(
        &bridge_prepared,
        mod_lt_succ.kernel(),
        mod_lt_succ_source,
        &[mod_lt],
        mod_lt_succ_target,
        mod_lt_succ.receipt(),
    )
    .map_err(|error| format!("successor-mod bound specialization did not replay: {error:?}"))?;

    let mut gcd_prepared = mod_lt_succ.kernel().clone();
    let gcd_succ_source = find_name(&gcd_prepared, GCD_SUCC_GENERIC)?;
    let mod_lt_succ_argument = find_name(&gcd_prepared, MOD_LT_SUCC_TARGET)?;
    let gcd_succ_target = {
        let nat = find_name(&gcd_prepared, "Nat")?;
        gcd_prepared.name_str(nat, "gcd_succ")
    };
    let gcd_succ = specialize_checked_theorem(
        &gcd_prepared,
        gcd_succ_source,
        &[mod_lt_succ_argument],
        gcd_succ_target,
    )
    .map_err(|error| format!("Nat.gcd_succ specialization declined: {error:?}"))?;
    verify_checked_theorem_specialization(
        &gcd_prepared,
        gcd_succ.kernel(),
        gcd_succ_source,
        &[mod_lt_succ_argument],
        gcd_succ_target,
        gcd_succ.receipt(),
    )
    .map_err(|error| format!("Nat.gcd_succ specialization did not replay: {error:?}"))?;
    let gcd_succ_compatibility =
        checked_reused_declaration_compatibility(&native, gcd_succ.kernel(), GCD_SUCC_TARGET)
            .map_err(|error| format!("native Nat.gcd_succ compatibility failed: {error:?}"))?;

    let frontier = retry_dvd_gcd(&native, gcd_succ.kernel())?;
    let output = json!({
        "schema_version": 1,
        "kind": "axeyum-nat-gcd-succ-specialization",
        "lean_version": gcd_bridge.report().lean_version,
        "bridge_composition": {
            "roots": [MOD_LT_SUCC_GENERIC, GCD_SUCC_GENERIC],
            "source_closure": bridge.receipt().source_closure.len(),
            "reused": bridge.receipt().reused_declarations.len(),
            "added_theorems": bridge.receipt().added_theorems.len(),
            "added_definitions": bridge.receipt().added_definitions.len(),
            "added_singleton_inductives": bridge.receipt().added_singleton_inductives.len(),
            "receipt_sha256": bridge.receipt().receipt_sha256,
        },
        "mod_lt_succ_specialization": specialization_json(mod_lt_succ.receipt()),
        "gcd_succ_specialization": {
            "result": specialization_json(gcd_succ.receipt()),
            "native_type_compatibility": gcd_succ_compatibility.compatibility.as_str(),
            "native_type_shape_sha256": gcd_succ_compatibility.source_type_shape_sha256,
            "target_type_shape_sha256": gcd_succ_compatibility.target_type_shape_sha256,
        },
        "dvd_gcd_frontier": frontier,
        "proof_search_invocations": 0,
        "ledger_writes": 0,
    });
    println!(
        "{}",
        serde_json::to_string_pretty(&output).map_err(|error| error.to_string())?
    );
    Ok(())
}

fn retry_dvd_gcd(source: &Kernel, target: &Kernel) -> Result<Value, String> {
    match compose_checked_theorem_slice_with_target_leaves(
        source,
        target,
        &["Nat.dvd_gcd"],
        &DVD_GCD_LEAVES,
    ) {
        Ok(completed) => {
            verify_checked_theorem_composition_with_target_leaves(
                source,
                target,
                completed.kernel(),
                completed.receipt(),
            )
            .map_err(|error| format!("Nat.dvd_gcd composition did not replay: {error:?}"))?;
            require_empty_added_footprints(
                completed
                    .receipt()
                    .added_theorems
                    .iter()
                    .map(|row| (row.name.as_str(), row.axiom_footprint.as_slice())),
            )?;
            Ok(json!({
                "outcome": "composed",
                "target_theorem_leaves": DVD_GCD_LEAVES,
                "source_closure": completed.receipt().source_closure.len(),
                "added_theorems": completed.receipt().added_theorems.len(),
                "added_definitions": completed.receipt().added_definitions.len(),
                "receipt_sha256": completed.receipt().receipt_sha256,
            }))
        }
        Err(CheckedTheoremCompositionError::AdmissionRejected { name, error }) => Ok(json!({
            "outcome": "declined",
            "target_theorem_leaves": DVD_GCD_LEAVES,
            "first_rejected": name,
            "error": error,
        })),
        Err(error) => Err(format!(
            "Nat.dvd_gcd composition declined unexpectedly: {error:?}"
        )),
    }
}

fn specialization_json(receipt: &axeyum_lean_import::CheckedTheoremSpecializationReceipt) -> Value {
    json!({
        "source": receipt.source_theorem,
        "arguments": receipt.arguments.iter().map(|row| &row.name).collect::<Vec<_>>(),
        "target": receipt.target_theorem,
        "target_sha256": receipt.target_theorem_sha256,
        "axiom_footprint": receipt.axiom_footprint,
        "receipt_sha256": receipt.receipt_sha256,
    })
}

fn import(path: &PathBuf, label: &str) -> Result<axeyum_lean_import::CompletedImport, String> {
    let bytes = fs::read(path).map_err(|error| format!("{label} read failed: {error}"))?;
    import_ndjson(Cursor::new(bytes), ImportLimits::default())
        .map_err(|error| format!("{label} import failed: {error:?}"))
}

fn required_path(
    arguments: &mut impl Iterator<Item = std::ffi::OsString>,
    label: &str,
) -> Result<PathBuf, String> {
    arguments
        .next()
        .map(PathBuf::from)
        .ok_or_else(|| format!("missing required {label} argument"))
}

fn nested_name(kernel: &mut Kernel, components: &[&str]) -> NameId {
    components.iter().fold(kernel.anon(), |prefix, component| {
        kernel.name_str(prefix, *component)
    })
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
