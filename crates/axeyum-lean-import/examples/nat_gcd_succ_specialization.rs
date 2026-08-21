//! Reconstruct an axiom-free official `Nat.gcd_succ`, compose the complete
//! Fibonacci support surface, and optionally admit the exact frozen
//! `Nat.fib_coprime_fib_succ` target using an isolated recurrence export.

#[path = "support/fib_coprime.rs"]
mod fib_coprime;
#[path = "support/fib_gcd_shift.rs"]
mod fib_gcd_shift;

use std::fs;
use std::io::Cursor;
use std::path::PathBuf;

use axeyum_lean_import::{
    CHECKED_DEPENDENCY_THEOREM_RECEIPT_VERSION, CheckedDependencyTheoremAuthority,
    CheckedTheoremAuthority, CheckedTheoremCompositionError, CheckedTheoremDependency,
    ImportLimits, canonical_declaration_sha256, canonical_expression_sha256,
    checked_reused_declaration_compatibility, compose_checked_theorem_slice,
    compose_checked_theorem_slice_with_target_leaves, import_ndjson,
    issue_checked_dependency_theorem_receipt, specialize_checked_theorem,
    verify_checked_dependency_theorem_receipt, verify_checked_theorem_composition,
    verify_checked_theorem_composition_with_target_leaves, verify_checked_theorem_specialization,
};
use axeyum_lean_kernel::{Declaration, Kernel, NameId, build_nat_prelude};
use serde_json::{Value, json};
use sha2::{Digest, Sha256};

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
const BALANCED_BEZOUT_GENERIC: &str = "Axeyum.Autogenesis.officialGcdBalancedBezoutCleanV1";
const BALANCED_BEZOUT_GENERIC_SHA256: &str =
    "feb1c3e41dd2f745261002b3876ddab750db5777226956ddbb07d805b4abc9ec";
const BALANCED_BEZOUT_TARGET: &str = "Axeyum.Autogenesis.officialGcdBalancedBezoutClosedV1";
const GCD_ZERO_LEFT_SHA256: &str =
    "f81aee8a1d8528ddf8b7be6007efbee190f2208cdef3dcfda9fa03a1f200175d";
const GCD_SUCC_SHA256: &str = "e41996f98e01e15b88e11773bb42db825bf271888ece2d002c193627a8392727";
const FIB_RECURRENCE: &str = "Axeyum.Autogenesis.fibAddTwo";
const FIB_COPRIME_TARGET: &str = "Nat.fib_coprime_fib_succ";
const TARGET_STATEMENT: &str = "Axeyum.Autogenesis.Coverage.r082";
const TARGET_GOAL_SHA256: &str = "a053d8f483f2cc1e79c53924baf5f79e4897ce992ca77722168cee20a6f5150f";
const TARGET_STREAM_SHA256: &str =
    "6afa79d79481403d3e3273ea3eea26b4d1194762f9bd623ec019f8e821323cfd";
const TARGET_FACT: &str = "F:ml430-nat-fib-coprime-fib-succ-162fc738";
const GCD_SHIFT_STREAM_SHA256: &str =
    "fc1117679c743009e8548a25d1f73f71f6cd42555ea77b3efce07844673670b2";
const CANDIDATE_OBSERVATION_SHA256: &str =
    "a1d92b2090392ac90e22419e6e4f6572beff1cbbd27f83d72c7dfcd566ca860a";
const CANDIDATE_PROOF_SHA256: &str =
    "baa3313f7b40ad1c73ae29de08deb9f0368e9fcf06fd318fea9c73822c7d6827";
const CANDIDATE_THEOREM_SHA256: &str =
    "7fd9a1e811b93f8021ded1e34de5a816a0e9b23940e15cfcd5cbe81309daede9";
const RECEIPT_AUTHORITY_MANIFEST_SHA256: &str =
    "b9eb358d0928be257084150998f4f57c87cbbe01040f2c43ac1a306810093b6b";
const DVD_GCD_LEAVES: [&str; 3] = ["Nat.dvd_mod_iff", "Nat.mod_lt", "Nat.gcd_succ"];
const REQUIRED_SUPPORT_ROOTS: [&str; 7] = [
    "Nat.add_comm",
    "Nat.dvd_add_iff_right",
    "Nat.dvd_gcd",
    "Nat.eq_one_of_dvd_one",
    "Nat.gcd_dvd_left",
    "Nat.gcd_dvd_right",
    "Nat.gcd_zero_left",
];

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
    let (
        all_support,
        exact_target_path,
        authority_audit,
        receipt_candidate_path,
        gcd_shift_support,
        gcd_shift_second_support,
        balanced_bezout_path,
    ) = match arguments.next() {
        None => (false, None, false, None, false, false, None),
        Some(flag) if flag == "--all-support" => (true, None, false, None, false, false, None),
        Some(flag) if flag == "--exact-target" => (
            true,
            Some(required_path(&mut arguments, "fib-recurrence.ndjson")?),
            false,
            None,
            false,
            false,
            None,
        ),
        Some(flag) if flag == "--exact-authority" => (
            true,
            Some(required_path(&mut arguments, "fib-recurrence.ndjson")?),
            true,
            None,
            false,
            false,
            None,
        ),
        Some(flag) if flag == "--issue-receipt" => (
            true,
            Some(required_path(&mut arguments, "fib-recurrence.ndjson")?),
            false,
            Some(required_path(&mut arguments, "candidate-observation.json")?),
            false,
            false,
            None,
        ),
        Some(flag) if flag == "--gcd-fib-add-self-support" => (
            true,
            Some(required_path(&mut arguments, "fib-recurrence.ndjson")?),
            false,
            None,
            true,
            false,
            None,
        ),
        Some(flag) if flag == "--gcd-fib-add-self-second-support" => (
            true,
            Some(required_path(&mut arguments, "fib-recurrence.ndjson")?),
            false,
            None,
            true,
            true,
            None,
        ),
        Some(flag) if flag == "--closed-balanced-bezout" => (
            true,
            None,
            false,
            None,
            false,
            false,
            Some(required_path(
                &mut arguments,
                "official-gcd-balanced-bezout-clean.ndjson",
            )?),
        ),
        Some(_) => return Err("unexpected trailing argument".to_owned()),
    };
    if arguments.next().is_some() {
        return Err("unexpected trailing argument".to_owned());
    }
    if receipt_candidate_path.is_some()
        && hex_sha256(
            &fs::read(&target_path)
                .map_err(|error| format!("receipt target stream read failed: {error}"))?,
        ) != TARGET_STREAM_SHA256
    {
        return Err("receipt target stream identity changed".to_owned());
    }
    if gcd_shift_support
        && hex_sha256(
            &fs::read(&target_path)
                .map_err(|error| format!("gcd-shift target stream read failed: {error}"))?,
        ) != GCD_SHIFT_STREAM_SHA256
    {
        return Err("gcd-shift target stream identity changed".to_owned());
    }

    let mod_invariant = import(&mod_invariant_path, "mod-invariant")?;
    let target = import(&target_path, "target")?;
    let gcd_bridge = import(&gcd_bridge_path, "gcd-bridge")?;
    let exact_target = exact_target_path
        .as_ref()
        .map(|path| import(path, "fib-recurrence"))
        .transpose()?;
    let balanced_bezout = balanced_bezout_path
        .as_ref()
        .map(|path| import(path, "official-gcd-balanced-bezout-clean"))
        .transpose()?;
    if !mod_invariant.report().axioms.is_empty()
        || !target.report().axioms.is_empty()
        || !gcd_bridge.report().axioms.is_empty()
        || exact_target
            .as_ref()
            .is_some_and(|imported| !imported.report().axioms.is_empty())
        || balanced_bezout
            .as_ref()
            .is_some_and(|imported| !imported.report().axioms.is_empty())
    {
        return Err("every selected input must be proof-isolated".to_owned());
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
    let native_prelude = build_nat_prelude(&mut native)
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

    let support_roots: &[&str] = if all_support {
        &REQUIRED_SUPPORT_ROOTS
    } else {
        &["Nat.dvd_gcd"]
    };
    if gcd_shift_support {
        let completed = compose_checked_theorem_slice_with_target_leaves(
            &native,
            gcd_succ.kernel(),
            support_roots,
            &DVD_GCD_LEAVES,
        )
        .map_err(|error| format!("gcd-shift support composition declined: {error:?}"))?;
        verify_checked_theorem_composition_with_target_leaves(
            &native,
            gcd_succ.kernel(),
            completed.kernel(),
            completed.receipt(),
        )
        .map_err(|error| format!("gcd-shift support composition did not replay: {error:?}"))?;
        require_empty_added_footprints(
            completed
                .receipt()
                .added_theorems
                .iter()
                .map(|row| (row.name.as_str(), row.axiom_footprint.as_slice())),
        )?;
        let recurrence = exact_target
            .as_ref()
            .ok_or("gcd-shift support requires the recurrence source")?;
        let native_with_recurrence =
            compose_checked_theorem_slice(recurrence.kernel(), &native, &[FIB_RECURRENCE])
                .map_err(|error| {
                    format!("native gcd-shift recurrence composition declined: {error:?}")
                })?;
        verify_checked_theorem_composition(
            recurrence.kernel(),
            &native,
            native_with_recurrence.kernel(),
            native_with_recurrence.receipt(),
        )
        .map_err(|error| {
            format!("native gcd-shift recurrence composition did not replay: {error:?}")
        })?;
        let addition = fib_gcd_shift::reconstruct_addition_twice(
            native_with_recurrence.kernel(),
            &native_prelude,
            FIB_RECURRENCE,
        )?;
        let target_with_recurrence = compose_checked_theorem_slice(
            recurrence.kernel(),
            completed.kernel(),
            &[FIB_RECURRENCE],
        )
        .map_err(|error| format!("target gcd-shift recurrence composition declined: {error:?}"))?;
        verify_checked_theorem_composition(
            recurrence.kernel(),
            completed.kernel(),
            target_with_recurrence.kernel(),
            target_with_recurrence.receipt(),
        )
        .map_err(|error| {
            format!("target gcd-shift recurrence composition did not replay: {error:?}")
        })?;
        let target_with_addition = compose_checked_theorem_slice(
            &addition.kernel,
            target_with_recurrence.kernel(),
            &[fib_gcd_shift::ADDITION_TARGET],
        )
        .map_err(|error| format!("gcd-shift addition composition declined: {error:?}"))?;
        verify_checked_theorem_composition(
            &addition.kernel,
            target_with_recurrence.kernel(),
            target_with_addition.kernel(),
            target_with_addition.receipt(),
        )
        .map_err(|error| format!("gcd-shift addition composition did not replay: {error:?}"))?;
        if gcd_shift_second_support {
            let cancellation =
                fib_gcd_shift::reconstruct_cancellation_twice(&addition.kernel, &native_prelude)?;
            let target_with_cancellation = match compose_checked_theorem_slice(
                &cancellation.kernel,
                target_with_addition.kernel(),
                &[fib_gcd_shift::CANCELLATION_TARGET],
            ) {
                Ok(completed) => completed,
                Err(error) => {
                    let rendered = format!("{error:?}");
                    if !rendered.contains("AdmissionRejected")
                        || !rendered.contains("Nat.div_mod_exec")
                        || !rendered.contains("TypeMismatch")
                    {
                        return Err(format!(
                            "gcd-shift cancellation composition changed: {rendered}"
                        ));
                    }
                    println!(
                        "{}",
                        serde_json::to_string_pretty(&json!({
                            "schema_version": 1,
                            "kind": "axeyum-nat-gcd-fib-add-self-support-control",
                            "state": "second-support-reconstructed-target-composition-declined",
                            "target_stream_sha256": GCD_SHIFT_STREAM_SHA256,
                            "support_composition_receipt_sha256": completed.receipt().receipt_sha256,
                            "native_recurrence_composition_receipt_sha256": native_with_recurrence.receipt().receipt_sha256,
                            "target_recurrence_composition_receipt_sha256": target_with_recurrence.receipt().receipt_sha256,
                            "addition_composition_receipt_sha256": target_with_addition.receipt().receipt_sha256,
                            "supports": [addition.evidence, cancellation.evidence],
                            "support_theorems_reconstructed": 2,
                            "fresh_kernel_submissions_cumulative": 4,
                            "kernel_checks_this_invocation": 4,
                            "retained_support_replay_submissions": 2,
                            "new_support_kernel_submissions": 2,
                            "exact_source_target_submissions": 0,
                            "proof_search_invocations": 0,
                            "executor_invocations": 0,
                            "failure": {
                                "operation": "compose second native support into exact r091 kernel",
                                "first_rejected": "Nat.div_mod_exec",
                                "class": "incompatible-target-definition",
                                "native_transport_authorized": false,
                                "partial_kernel_published": false,
                            },
                            "evaluation_credit": 0,
                            "ledger_writes": 0,
                        }))
                        .map_err(|error| error.to_string())?
                    );
                    return Ok(());
                }
            };
            verify_checked_theorem_composition(
                &cancellation.kernel,
                target_with_addition.kernel(),
                target_with_cancellation.kernel(),
                target_with_cancellation.receipt(),
            )
            .map_err(|error| {
                format!("gcd-shift cancellation composition did not replay: {error:?}")
            })?;
            println!(
                "{}",
                serde_json::to_string_pretty(&json!({
                    "schema_version": 1,
                    "kind": "axeyum-nat-gcd-fib-add-self-support-control",
                    "state": "both-supports-reconstructed-no-target-or-ledger-credit",
                    "target_stream_sha256": GCD_SHIFT_STREAM_SHA256,
                    "support_composition_receipt_sha256": completed.receipt().receipt_sha256,
                    "native_recurrence_composition_receipt_sha256": native_with_recurrence.receipt().receipt_sha256,
                    "target_recurrence_composition_receipt_sha256": target_with_recurrence.receipt().receipt_sha256,
                    "addition_composition_receipt_sha256": target_with_addition.receipt().receipt_sha256,
                    "cancellation_composition_receipt_sha256": target_with_cancellation.receipt().receipt_sha256,
                    "supports": [addition.evidence, cancellation.evidence],
                    "support_theorems_reconstructed": 2,
                    "fresh_kernel_submissions_cumulative": 4,
                    "kernel_checks_this_invocation": 4,
                    "retained_support_replay_submissions": 2,
                    "new_support_kernel_submissions": 2,
                    "exact_source_target_submissions": 0,
                    "proof_search_invocations": 0,
                    "executor_invocations": 0,
                    "evaluation_credit": 0,
                    "ledger_writes": 0,
                }))
                .map_err(|error| error.to_string())?
            );
            return Ok(());
        }
        println!(
            "{}",
            serde_json::to_string_pretty(&json!({
                "schema_version": 1,
                "kind": "axeyum-nat-gcd-fib-add-self-support-control",
                "state": "first-support-reconstructed-no-target-or-ledger-credit",
                "target_stream_sha256": GCD_SHIFT_STREAM_SHA256,
                "support_composition_receipt_sha256": completed.receipt().receipt_sha256,
                "native_recurrence_composition_receipt_sha256": native_with_recurrence.receipt().receipt_sha256,
                "target_recurrence_composition_receipt_sha256": target_with_recurrence.receipt().receipt_sha256,
                "addition_composition_receipt_sha256": target_with_addition.receipt().receipt_sha256,
                "supports": [addition.evidence],
                "support_theorems_reconstructed": 1,
                "kernel_submissions": 2,
                "exact_source_target_submissions": 0,
                "proof_search_invocations": 0,
                "executor_invocations": 0,
                "evaluation_credit": 0,
                "ledger_writes": 0,
            }))
            .map_err(|error| error.to_string())?
        );
        return Ok(());
    }
    if let Some(balanced_bezout) = balanced_bezout.as_ref() {
        let completed = compose_checked_theorem_slice_with_target_leaves(
            &native,
            gcd_succ.kernel(),
            &REQUIRED_SUPPORT_ROOTS,
            &DVD_GCD_LEAVES,
        )
        .map_err(|error| format!("balanced-Bezout support composition declined: {error:?}"))?;
        verify_checked_theorem_composition_with_target_leaves(
            &native,
            gcd_succ.kernel(),
            completed.kernel(),
            completed.receipt(),
        )
        .map_err(|error| {
            format!("balanced-Bezout support composition did not replay: {error:?}")
        })?;
        require_empty_added_footprints(
            completed
                .receipt()
                .added_theorems
                .iter()
                .map(|row| (row.name.as_str(), row.axiom_footprint.as_slice())),
        )?;
        return close_balanced_bezout(balanced_bezout.kernel(), completed.kernel());
    }
    let frontier = retry_native_support(
        &native,
        gcd_succ.kernel(),
        support_roots,
        exact_target
            .as_ref()
            .map(axeyum_lean_import::CompletedImport::kernel),
        authority_audit,
        receipt_candidate_path.as_ref(),
    )?;
    let kind = if receipt_candidate_path.is_some() {
        "axeyum-exact-fibonacci-dependency-theorem-receipt"
    } else {
        "axeyum-nat-gcd-succ-specialization"
    };
    let output = json!({
        "schema_version": 1,
        "kind": kind,
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

#[allow(clippy::too_many_lines)]
fn close_balanced_bezout(source: &Kernel, target: &Kernel) -> Result<(), String> {
    let composed = compose_checked_theorem_slice(source, target, &[BALANCED_BEZOUT_GENERIC])
        .map_err(|error| format!("generic balanced-Bezout composition declined: {error:?}"))?;
    verify_checked_theorem_composition(source, target, composed.kernel(), composed.receipt())
        .map_err(|error| {
            format!("generic balanced-Bezout composition did not replay: {error:?}")
        })?;
    require_empty_added_footprints(
        composed
            .receipt()
            .added_theorems
            .iter()
            .map(|row| (row.name.as_str(), row.axiom_footprint.as_slice())),
    )?;

    let mut prepared = composed.kernel().clone();
    let generic = find_name(&prepared, BALANCED_BEZOUT_GENERIC)?;
    require_declaration_identity(
        &prepared,
        generic,
        BALANCED_BEZOUT_GENERIC,
        BALANCED_BEZOUT_GENERIC_SHA256,
    )?;
    let gcd_zero_left = find_name(&prepared, "Nat.gcd_zero_left")?;
    require_declaration_identity(
        &prepared,
        gcd_zero_left,
        "Nat.gcd_zero_left",
        GCD_ZERO_LEFT_SHA256,
    )?;
    let gcd_succ = find_name(&prepared, GCD_SUCC_TARGET)?;
    require_declaration_identity(&prepared, gcd_succ, GCD_SUCC_TARGET, GCD_SUCC_SHA256)?;
    let target_name = nested_name(
        &mut prepared,
        &["Axeyum", "Autogenesis", "officialGcdBalancedBezoutClosedV1"],
    );
    let specialized =
        specialize_checked_theorem(&prepared, generic, &[gcd_zero_left, gcd_succ], target_name)
            .map_err(|error| {
                format!("closed balanced-Bezout specialization declined: {error:?}")
            })?;
    verify_checked_theorem_specialization(
        &prepared,
        specialized.kernel(),
        generic,
        &[gcd_zero_left, gcd_succ],
        target_name,
        specialized.receipt(),
    )
    .map_err(|error| format!("closed balanced-Bezout specialization did not replay: {error:?}"))?;

    let footprint = specialized
        .kernel()
        .axiom_footprint(target_name)
        .into_iter()
        .map(|name| specialized.kernel().display_name(name).to_string())
        .collect::<Vec<_>>();
    if !footprint.is_empty() {
        return Err(format!(
            "closed balanced-Bezout theorem reaches assumptions: {footprint:?}"
        ));
    }
    let mut dependencies = specialized
        .kernel()
        .theorem_dependencies(target_name)
        .into_iter()
        .map(|name| specialized.kernel().display_name(name).to_string())
        .collect::<Vec<_>>();
    dependencies.sort();
    let expected_dependencies = [
        BALANCED_BEZOUT_GENERIC.to_owned(),
        GCD_SUCC_TARGET.to_owned(),
        "Nat.gcd_zero_left".to_owned(),
    ];
    if dependencies != expected_dependencies {
        return Err(format!(
            "closed balanced-Bezout dependencies changed: {dependencies:?}"
        ));
    }
    let declaration_sha256 = canonical_declaration_sha256(specialized.kernel(), target_name)?;
    println!(
        "{}",
        serde_json::to_string_pretty(&json!({
            "schema_version": 1,
            "kind": "axeyum-official-gcd-balanced-bezout-closed-specialization",
            "state": "closed-gcd-balanced-bezout-reconstructed-empty-footprint",
            "generic_composition_receipt_sha256": composed.receipt().receipt_sha256,
            "specialization": {
                "source": BALANCED_BEZOUT_GENERIC,
                "source_declaration_sha256": BALANCED_BEZOUT_GENERIC_SHA256,
                "arguments": [
                    {"name": "Nat.gcd_zero_left", "declaration_sha256": GCD_ZERO_LEFT_SHA256},
                    {"name": GCD_SUCC_TARGET, "declaration_sha256": GCD_SUCC_SHA256},
                ],
                "target": BALANCED_BEZOUT_TARGET,
                "target_declaration_sha256": declaration_sha256,
                "receipt_sha256": specialized.receipt().receipt_sha256,
                "axiom_footprint": footprint,
                "direct_theorem_dependencies": dependencies,
            },
            "rendered_material": {"proof_terms": 0, "theorem_types": 0, "theorem_values": 0},
            "proof_search_invocations": 0,
            "executor_invocations": 0,
            "fact_status_changes": 0,
            "evaluation_credit": 0,
            "ledger_writes": 0,
        }))
        .map_err(|error| error.to_string())?
    );
    Ok(())
}

fn require_declaration_identity(
    kernel: &Kernel,
    name: NameId,
    label: &str,
    expected: &str,
) -> Result<(), String> {
    let actual = canonical_declaration_sha256(kernel, name)?;
    if actual != expected {
        return Err(format!(
            "{label} declaration identity changed: expected {expected}, found {actual}"
        ));
    }
    Ok(())
}

fn retry_native_support(
    source: &Kernel,
    target: &Kernel,
    roots: &[&str],
    exact_source: Option<&Kernel>,
    authority_audit: bool,
    receipt_candidate_path: Option<&PathBuf>,
) -> Result<Value, String> {
    match compose_checked_theorem_slice_with_target_leaves(source, target, roots, &DVD_GCD_LEAVES) {
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
            let mut value = json!({
                "outcome": "composed",
                "target_theorem_leaves": DVD_GCD_LEAVES,
                "source_closure": completed.receipt().source_closure.len(),
                "added_theorems": completed.receipt().added_theorems.len(),
                "added_definitions": completed.receipt().added_definitions.len(),
                "receipt_sha256": completed.receipt().receipt_sha256,
            });
            if let Some(exact_source) = exact_source {
                value["exact_target"] = if let Some(candidate_path) = receipt_candidate_path {
                    issue_exact_target_receipt(
                        source,
                        target,
                        roots,
                        exact_source,
                        completed.kernel(),
                        completed.receipt().receipt_sha256.as_str(),
                        candidate_path,
                    )?
                } else {
                    compose_exact_target(exact_source, completed.kernel(), authority_audit)?
                };
            }
            Ok(with_optional_roots(value, roots))
        }
        Err(CheckedTheoremCompositionError::AdmissionRejected { name, error }) => {
            Ok(with_optional_roots(
                json!({
                    "outcome": "declined",
                    "target_theorem_leaves": DVD_GCD_LEAVES,
                    "first_rejected": name,
                    "error": error,
                }),
                roots,
            ))
        }
        Err(error) => Err(format!(
            "Nat.dvd_gcd composition declined unexpectedly: {error:?}"
        )),
    }
}

struct ExactTargetAdmission {
    kernel: Kernel,
    theorem: NameId,
    dependency_ids: Vec<NameId>,
    dependencies: Vec<String>,
    footprint: Vec<String>,
    target_goal_sha256: String,
    proof_sha256: String,
    declaration_sha256: String,
    source_closure: usize,
    added_theorems: usize,
    added_definitions: usize,
    added_singleton_inductives: usize,
    recurrence_composition_receipt_sha256: String,
}

fn compose_exact_target(
    source: &Kernel,
    target: &Kernel,
    authority_audit: bool,
) -> Result<Value, String> {
    let first = reconstruct_exact_target(source, target)?;
    let replay = reconstruct_exact_target(source, target)?;
    require_same_exact_target(&first, &replay)?;
    let mut result = exact_target_json(&first, 2);
    if authority_audit {
        result["receipt_authority_audit"] =
            receipt_authority_audit(&first.kernel, &first.dependency_ids)?;
    }
    Ok(result)
}

fn reconstruct_exact_target(
    source: &Kernel,
    target: &Kernel,
) -> Result<ExactTargetAdmission, String> {
    let completed = compose_checked_theorem_slice(source, target, &[FIB_RECURRENCE])
        .map_err(|error| format!("Fibonacci recurrence composition declined: {error:?}"))?;
    verify_checked_theorem_composition(source, target, completed.kernel(), completed.receipt())
        .map_err(|error| format!("Fibonacci recurrence composition did not replay: {error:?}"))?;
    require_empty_added_footprints(
        completed
            .receipt()
            .added_theorems
            .iter()
            .map(|row| (row.name.as_str(), row.axiom_footprint.as_slice())),
    )?;

    let mut checked = completed.kernel().clone();
    let statement = find_name(&checked, TARGET_STATEMENT)?;
    let target_goal = match checked.environment().get(statement) {
        Some(Declaration::Definition { value, .. }) => *value,
        _ => return Err("r082 target statement is not a definition".to_owned()),
    };
    let target_goal_sha256 = canonical_expression_sha256(&checked, target_goal)?;
    if target_goal_sha256 != TARGET_GOAL_SHA256 {
        return Err(format!(
            "r082 target goal identity changed: {target_goal_sha256}"
        ));
    }
    let target_name = {
        let nat = find_name(&checked, "Nat")?;
        checked.name_str(nat, "fib_coprime_fib_succ")
    };
    let (theorem, _, proof) =
        fib_coprime::admit(&mut checked, target_name, target_goal, FIB_RECURRENCE)?;
    let footprint = checked
        .axiom_footprint(theorem)
        .into_iter()
        .map(|name| checked.display_name(name).to_string())
        .collect::<Vec<_>>();
    if !footprint.is_empty() {
        return Err(format!(
            "exact Fibonacci theorem reaches assumptions: {footprint:?}"
        ));
    }
    let dependency_ids = checked.theorem_dependencies(theorem);
    let dependencies = dependency_ids
        .iter()
        .map(|&name| checked.display_name(name).to_string())
        .collect::<Vec<_>>();
    let expected_dependencies = [
        FIB_RECURRENCE,
        "Nat.add_comm",
        "Nat.dvd_add_iff_right",
        "Nat.dvd_gcd",
        "Nat.eq_one_of_dvd_one",
        "Nat.gcd_dvd_left",
        "Nat.gcd_dvd_right",
        "Nat.gcd_zero_left",
    ];
    if dependencies != expected_dependencies.map(str::to_owned) {
        return Err(format!(
            "exact Fibonacci theorem dependencies changed: {dependencies:?}"
        ));
    }
    let proof_sha256 = canonical_expression_sha256(&checked, proof)?;
    let declaration_sha256 = canonical_declaration_sha256(&checked, theorem)?;
    Ok(ExactTargetAdmission {
        kernel: checked,
        theorem,
        dependency_ids,
        dependencies,
        footprint,
        target_goal_sha256,
        proof_sha256,
        declaration_sha256,
        source_closure: completed.receipt().source_closure.len(),
        added_theorems: completed.receipt().added_theorems.len(),
        added_definitions: completed.receipt().added_definitions.len(),
        added_singleton_inductives: completed.receipt().added_singleton_inductives.len(),
        recurrence_composition_receipt_sha256: completed.receipt().receipt_sha256.clone(),
    })
}

fn require_same_exact_target(
    first: &ExactTargetAdmission,
    replay: &ExactTargetAdmission,
) -> Result<(), String> {
    if first.target_goal_sha256 != replay.target_goal_sha256
        || first.proof_sha256 != replay.proof_sha256
        || first.declaration_sha256 != replay.declaration_sha256
        || first.footprint != replay.footprint
        || first.dependencies != replay.dependencies
        || first.recurrence_composition_receipt_sha256
            != replay.recurrence_composition_receipt_sha256
    {
        return Err("exact Fibonacci theorem reconstruction changed".to_owned());
    }
    Ok(())
}

fn exact_target_json(admission: &ExactTargetAdmission, fresh_reconstructions: usize) -> Value {
    json!({
        "recurrence_root": FIB_RECURRENCE,
        "source_closure": admission.source_closure,
        "added_theorems": admission.added_theorems,
        "added_definitions": admission.added_definitions,
        "added_singleton_inductives": admission.added_singleton_inductives,
        "recurrence_composition_receipt_sha256": admission.recurrence_composition_receipt_sha256,
        "target": FIB_COPRIME_TARGET,
        "target_goal_sha256": admission.target_goal_sha256,
        "proof_sha256": admission.proof_sha256,
        "target_declaration_sha256": admission.declaration_sha256,
        "target_axiom_footprint": admission.footprint,
        "direct_theorem_dependencies": admission.dependencies,
        "fresh_reconstructions": fresh_reconstructions,
    })
}

#[allow(clippy::too_many_arguments, clippy::too_many_lines)]
fn issue_exact_target_receipt(
    support_source: &Kernel,
    support_target: &Kernel,
    support_roots: &[&str],
    recurrence_source: &Kernel,
    first_support: &Kernel,
    first_support_receipt_sha256: &str,
    candidate_path: &PathBuf,
) -> Result<Value, String> {
    let candidate_bytes = fs::read(candidate_path)
        .map_err(|error| format!("candidate observation read failed: {error}"))?;
    if hex_sha256(&candidate_bytes) != CANDIDATE_OBSERVATION_SHA256 {
        return Err("candidate observation identity changed".to_owned());
    }
    let candidate: Value = serde_json::from_slice(&candidate_bytes)
        .map_err(|error| format!("candidate observation JSON failed: {error}"))?;
    require_sealed_candidate(&candidate)?;

    let mut first = reconstruct_exact_target(recurrence_source, first_support)?;
    let replay_support = compose_checked_theorem_slice_with_target_leaves(
        support_source,
        support_target,
        support_roots,
        &DVD_GCD_LEAVES,
    )
    .map_err(|error| format!("replay support composition declined: {error:?}"))?;
    verify_checked_theorem_composition_with_target_leaves(
        support_source,
        support_target,
        replay_support.kernel(),
        replay_support.receipt(),
    )
    .map_err(|error| format!("replay support composition changed: {error:?}"))?;
    require_empty_added_footprints(
        replay_support
            .receipt()
            .added_theorems
            .iter()
            .map(|row| (row.name.as_str(), row.axiom_footprint.as_slice())),
    )?;
    if replay_support.receipt().receipt_sha256 != first_support_receipt_sha256 {
        return Err("fresh support composition receipt changed".to_owned());
    }
    let mut replay = reconstruct_exact_target(recurrence_source, replay_support.kernel())?;
    require_same_exact_target(&first, &replay)?;

    let authority = CheckedDependencyTheoremAuthority {
        theorem: CheckedTheoremAuthority {
            policy_version: "nat-fib-coprime-official-receipt-v1".to_owned(),
            source_artifact_sha256: TARGET_STREAM_SHA256.to_owned(),
            target_definition: TARGET_STATEMENT.to_owned(),
            fact_id: TARGET_FACT.to_owned(),
            goal_sha256: TARGET_GOAL_SHA256.to_owned(),
            candidate_observation_sha256: CANDIDATE_OBSERVATION_SHA256.to_owned(),
            expected_proof_sha256: CANDIDATE_PROOF_SHA256.to_owned(),
            expected_theorem_content_sha256: CANDIDATE_THEOREM_SHA256.to_owned(),
            operation: "official-fibonacci-coprimality-induction-v1".to_owned(),
            max_plan_templates: 1,
            max_kernel_submissions: 2,
            max_executor_invocations: 1,
            max_retries: 0,
        },
        expected_direct_theorem_dependencies: receipt_dependencies(),
    };
    let receipt =
        issue_checked_dependency_theorem_receipt(&mut first.kernel, first.theorem, &authority)
            .map_err(|error| error.to_string())?;
    verify_checked_dependency_theorem_receipt(
        &receipt,
        &mut replay.kernel,
        replay.theorem,
        &authority,
    )
    .map_err(|error| error.to_string())?;
    let replayed =
        issue_checked_dependency_theorem_receipt(&mut replay.kernel, replay.theorem, &authority)
            .map_err(|error| error.to_string())?;
    if receipt != replayed
        || receipt.schema_version != CHECKED_DEPENDENCY_THEOREM_RECEIPT_VERSION
        || !receipt.has_valid_digest()
    {
        return Err("fresh exact theorem receipt replay changed".to_owned());
    }
    let receipt_json: Value = serde_json::from_str(
        &receipt
            .to_pretty_json()
            .map_err(|error| error.to_string())?,
    )
    .map_err(|error| error.to_string())?;
    let mut output = exact_target_json(&first, 2);
    output["candidate_observation_sha256"] = json!(CANDIDATE_OBSERVATION_SHA256);
    output["receipt_authority_manifest_sha256"] = json!(RECEIPT_AUTHORITY_MANIFEST_SHA256);
    output["semantic_theorem_receipt"] = receipt_json;
    output["assurance"] = json!({
        "fresh_full_reconstructions": 2,
        "target_theorem_submissions": 2,
        "receipt_reissued_exactly": true,
        "axiom_footprint": [],
        "direct_theorem_dependencies": receipt.direct_theorem_dependencies.iter().map(|row| json!({
            "name": row.name,
            "content_sha256": row.content_sha256,
        })).collect::<Vec<_>>(),
        "proof_search_invocations": 0,
    });
    output["authority"] = json!({
        "held_out_inspected": false,
        "semantic_theorem_receipts_issued": 1,
        "fact_status_changes": 0,
        "evaluation_credit": 0,
        "ledger_writes": 0,
    });
    Ok(output)
}

fn require_sealed_candidate(candidate: &Value) -> Result<(), String> {
    let exact = candidate
        .pointer("/dvd_gcd_frontier/exact_target")
        .ok_or("candidate exact target is missing")?;
    if candidate.get("kind").and_then(Value::as_str) != Some("axeyum-nat-gcd-succ-specialization")
        || exact.get("target").and_then(Value::as_str) != Some(FIB_COPRIME_TARGET)
        || exact.get("target_goal_sha256").and_then(Value::as_str) != Some(TARGET_GOAL_SHA256)
        || exact.get("proof_sha256").and_then(Value::as_str) != Some(CANDIDATE_PROOF_SHA256)
        || exact
            .get("target_declaration_sha256")
            .and_then(Value::as_str)
            != Some(CANDIDATE_THEOREM_SHA256)
        || exact.get("target_axiom_footprint") != Some(&json!([]))
        || candidate
            .get("proof_search_invocations")
            .and_then(Value::as_u64)
            != Some(0)
        || candidate.get("ledger_writes").and_then(Value::as_u64) != Some(0)
    {
        return Err("sealed candidate authority changed".to_owned());
    }
    Ok(())
}

fn receipt_dependencies() -> Vec<CheckedTheoremDependency> {
    [
        (
            FIB_RECURRENCE,
            "982c676b0656664e807c5e195bbdbd43376d78dec029bb3c409df661de39edb4",
        ),
        (
            "Nat.add_comm",
            "c05e6d0986251392c9b1bc9fcc2bd5d66de22c856b9669cdd993e9993d94f4f9",
        ),
        (
            "Nat.dvd_add_iff_right",
            "4bc8146aabb20e59aa1b0a19f80588ac80656320031f12b61f96da3f94802cf0",
        ),
        (
            "Nat.dvd_gcd",
            "325197e87bf46cc929ad03177c49e73de7054b446ec22f132c605af4d3c35e94",
        ),
        (
            "Nat.eq_one_of_dvd_one",
            "bc5301b4f9dbd08785db127ca6512283d2125321be596b362129d339c80ffa37",
        ),
        (
            "Nat.gcd_dvd_left",
            "7fa32fac2240feebdb94d6259f2bbab2dbb83059227286303efd7c306e5ad399",
        ),
        (
            "Nat.gcd_dvd_right",
            "d3214bf5b657f399baa82c9e2817996b64ae26d688308dfa0641a6ed376fdef4",
        ),
        (
            "Nat.gcd_zero_left",
            "f81aee8a1d8528ddf8b7be6007efbee190f2208cdef3dcfda9fa03a1f200175d",
        ),
    ]
    .into_iter()
    .map(|(name, content_sha256)| CheckedTheoremDependency {
        name: name.to_owned(),
        content_sha256: content_sha256.to_owned(),
    })
    .collect()
}

fn receipt_authority_audit(kernel: &Kernel, dependencies: &[NameId]) -> Result<Value, String> {
    let mut identities = dependencies
        .iter()
        .map(|&name| {
            Ok((
                kernel.display_name(name).to_string(),
                canonical_declaration_sha256(kernel, name)?,
            ))
        })
        .collect::<Result<Vec<(String, String)>, String>>()?;
    identities.sort_by(|left, right| left.0.cmp(&right.0));
    Ok(json!({
        "direct_theorem_dependencies": identities.iter().map(|(name, content_sha256)| json!({
            "name": name,
            "content_sha256": content_sha256,
        })).collect::<Vec<_>>(),
        "semantic_theorem_receipts_issued": 0,
        "fact_status_changes": 0,
        "evaluation_credit": 0,
        "ledger_writes": 0,
    }))
}

fn with_optional_roots(mut value: Value, roots: &[&str]) -> Value {
    if roots != ["Nat.dvd_gcd"] {
        value["roots"] = json!(roots);
    }
    value
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

fn hex_sha256(bytes: &[u8]) -> String {
    let digest = Sha256::digest(bytes);
    let mut output = String::with_capacity(64);
    for byte in digest {
        use std::fmt::Write;
        write!(output, "{byte:02x}").expect("writing to String cannot fail");
    }
    output
}
