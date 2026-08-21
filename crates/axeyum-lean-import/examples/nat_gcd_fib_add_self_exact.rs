//! Reconstruct exact `Nat.gcd_fib_add_self` from four sealed proof capsules.

#[path = "support/fib_coprime.rs"]
mod fib_coprime;

use std::fmt::Write as _;
use std::fs;
use std::io::Cursor;
use std::path::{Path, PathBuf};

use axeyum_lean_import::{
    ImportLimits, ReusedTypeCompatibility, canonical_declaration_sha256,
    canonical_expression_sha256, canonical_kernel_type_shape_sha256,
    checked_reused_declaration_compatibility, compose_checked_theorem_slice,
    compose_checked_theorem_slice_with_target_leaves, import_ndjson, specialize_checked_theorem,
    verify_checked_theorem_composition, verify_checked_theorem_composition_with_target_leaves,
    verify_checked_theorem_specialization,
};
use axeyum_lean_kernel::{
    BinderInfo, Declaration, ExprId, Kernel, Lean4ExportMetadata, LevelId, NameId,
};
use serde_json::{Value, json};
use sha2::{Digest, Sha256};

const R091_SHA256: &str = "fc1117679c743009e8548a25d1f73f71f6cd42555ea77b3efce07844673670b2";
const GOAL_DEFINITION: &str = "Axeyum.Autogenesis.Coverage.r091";
const GOAL_SHA256: &str = "297c9f4af4d63eff354223f9548ab1d4dd3d7e52aa701e88802d58b7929a1451";
const TARGET_NATIVE_GOAL_SHA256: &str =
    "0ac365e0654218862f44cc19391e699b85e495ab1b9608fc3eca79585c0e0475";
const TARGET: &str = "Nat.gcd_fib_add_self";
const GCD_GREATEST_TARGET: &str = "Nat.gcd_greatest";
const FIB_GCD_TARGET: &str = "Nat.fib_gcd";
const FIB_GCD_ITERATION: &str = "Axeyum.Autogenesis.fibGcdQuotientIterationV1";
const GCD_GREATEST_CAPSULE: &str =
    "c233478948b4d4aedc01c839ef9013c3feb2ddb0009d8b57699d7efb755375e6";
const GCD_FIB_SHIFT_CAPSULE: &str =
    "279dc4db5daa6dc2f532f9876052500a7e278c54264b32ccbc9d4256907dfc24";
const CLEAN_ANTISYMM: &str = "Axeyum.Autogenesis.dvdAntisymmOfficialV1";
const CLEAN_ANTISYMM_CAPSULE: &str =
    "bc147e08e6425ce8c31f3a10ccd5e9a7f7774ef0265b45784700588cb4bbcb25";
const CANCELLATION: &str = "Axeyum.Autogenesis.officialCoprimeFactorDivisibilityCancellationV1";
const CANCELLATION_BOOTSTRAP: &str = "Nat.mod_lt";
const CANCELLATION_CAPSULE: &str =
    "6f9a3983ba4b0e7b2c872615d796ceb5414d3bd2cf51843ecb496b3ba83a52b0";
const ADDITION: &str = "Axeyum.Autogenesis.NatFibSuccessorAddition";
const ADDITION_CAPSULE: &str = "f46e3dd4053c930984b3232ff98320021daa2fcdb3451e84bfbf011945a18621";
const COPRIME: &str = "Nat.fib_coprime_fib_succ";
const COPRIME_DIRECT_PREMISES: [&str; 8] = [
    "Axeyum.Autogenesis.fibAddTwo",
    "Nat.add_comm",
    "Nat.dvd_add_iff_right",
    "Nat.dvd_gcd",
    "Nat.eq_one_of_dvd_one",
    "Nat.gcd_dvd_left",
    "Nat.gcd_dvd_right",
    "Nat.gcd_zero_left",
];
const COPRIME_SUPPORT_CANDIDATES: [&str; 17] = [
    "Nat.dvd_add",
    "Axeyum.Autogenesis.dvdAddCancelAllNatClosedV1",
    "Nat.dvd_add_right_cancel_of_pos",
    "Iff",
    "Iff.intro",
    "Nat.not_succ_le_zero",
    "Nat.le_refl",
    "False",
    "False.rec",
    "Nat.mul_zero",
    "Nat.dvd_mod_iff",
    "Nat.mod_lt",
    "Axeyum.Autogenesis.nat_gcd_succ",
    "Axeyum.Autogenesis.officialNatGcdSuccClosedV1",
    "Axeyum.Autogenesis.nat_gcd_zero_left",
    "Nat.lt_wellFounded",
    "WellFounded.fix",
];
const GCD_SUPPORT_CANDIDATES: [&str; 14] = [
    "Nat.gcd.induction",
    "And",
    "And.intro",
    "And.left",
    "And.right",
    "Axeyum.Autogenesis.modQuotientWitnessV4",
    "Axeyum.Autogenesis.dvdAddCancelAllNatClosedV1",
    TARGET_DVD_ADD,
    "Nat.dvd_mul_right_of_dvd",
    "Nat.dvd_refl",
    "Nat.mul_zero",
    GCD_ZERO_LEFT_GENERIC,
    COPRIME_GCD_SUCC_LEAF,
    "Nat.mod_lt",
];
const COPRIME_GCD_SUCC_LEAF: &str = "Axeyum.Autogenesis.nat_gcd_succ";
const COPRIME_GCD_SUCC_LEAF_SHA256: &str =
    "1a9cf6e4ef4dc54a298214571515e7682a6265d9db7008b7cf1f8b3c38d11f16";
const GCD_ZERO_LEFT_GENERIC: &str = "Axeyum.Autogenesis.nat_gcd_zero_left";
const GCD_ZERO_LEFT_GENERIC_SHA256: &str =
    "e4f6c7e3971f5751bd1e889e9bfc28b7035d9f47204f7aafa5efc06b97cf3555";
const GCD_ZERO_LEFT_PUBLIC: &str = "Nat.gcd_zero_left";
const TARGET_DVD_ADD: &str = "Axeyum.Autogenesis.dvdAddOfficialV1";
const TARGET_EQ_ONE_OF_DVD_ONE: &str = "Axeyum.Autogenesis.eqOneOfDvdOneOfficialV1";
const TARGET_DVD_REFL: &str = "Axeyum.Autogenesis.dvdReflOfficialV1";
const TARGET_DVD_MUL_RIGHT: &str = "Axeyum.Autogenesis.dvdMulRightOfficialV1";
const GCD_DIVISIBILITY_GENERIC: &str = "Axeyum.Autogenesis.gcdDivisibilityFamilyGenericV1";
const GCD_DIVISIBILITY_GENERIC_CAPSULE: &str =
    "69971cb5f19607b454ba716966aebc4b1e3e3e3675fdc1f8534c5475b15ee5b2";
const GCD_DIVISIBILITY_CLOSED: &str = "Axeyum.Autogenesis.gcdDivisibilityFamilyClosedV1";
const TARGET_GCD_DVD_LEFT: &str = "Axeyum.Autogenesis.gcdDvdLeftOfficialV1";
const TARGET_GCD_DVD_RIGHT: &str = "Axeyum.Autogenesis.gcdDvdRightOfficialV1";
const TARGET_DVD_GCD: &str = "Axeyum.Autogenesis.dvdGcdOfficialV1";
const TARGET_FIB_COPRIME: &str = "Axeyum.Autogenesis.fibCoprimeFibSuccOfficialV1";
const COPRIME_CAPSULE: &str = "9106a3442d75a5fdaf51e35436e6fdbea78714d743e666bec27ffd9641160b11";
const CLEAN_GCD_COMM: &str = "Axeyum.Autogenesis.gcdCommCleanV1";
const OFFICIAL_EQ_ZERO: &str = "Axeyum.Autogenesis.eqZeroOfZeroDvdOfficialV1";
const OFFICIAL_ONE_LE_RIGHT_OF_MUL: &str = "Axeyum.Autogenesis.oneLeRightOfMulOfficialV1";
const OFFICIAL_MUL_LE_MUL_LEFT: &str = "Axeyum.Autogenesis.mulLeMulLeftOfficialV1";
const OFFICIAL_LE_OF_DVD: &str = "Axeyum.Autogenesis.leOfDvdOfficialV1";
const OFFICIAL_LE_ANTISYMM: &str = "Axeyum.Autogenesis.leAntisymmOfficialV1";
const OFFICIAL_ANTISYMM: &str = "Axeyum.Autogenesis.dvdAntisymmOfficialV1";
const USAGE: &str = "usage: nat_gcd_fib_add_self_exact <r091> <clean-order> <cancellation> <addition> <coprimality>";

fn main() {
    if let Err(error) = run() {
        eprintln!("nat-gcd-fib-add-self-exact: {error}");
        std::process::exit(1);
    }
}

#[allow(clippy::too_many_lines)]
fn run() -> Result<(), String> {
    let mut args = std::env::args_os().skip(1);
    if args.next().as_deref() == Some(std::ffi::OsStr::new("--official-clean-order-capsule")) {
        return run_official_clean_order_capsule(args);
    }
    let mut args = std::env::args_os().skip(1);
    if args.next().as_deref() == Some(std::ffi::OsStr::new("--coprime-carrier-audit")) {
        return run_coprime_carrier_audit(args);
    }
    let mut args = std::env::args_os().skip(1);
    if args.next().as_deref() == Some(std::ffi::OsStr::new("--target-native-coprime-audit")) {
        return run_target_native_coprime_audit(args);
    }
    let mut args = std::env::args_os().skip(1);
    if args.next().as_deref()
        == Some(std::ffi::OsStr::new(
            "--target-native-simple-support-capsule",
        ))
    {
        return run_target_native_simple_support_capsule(args);
    }
    let mut args = std::env::args_os().skip(1);
    if args.next().as_deref() == Some(std::ffi::OsStr::new("--target-native-gcd-surface-audit")) {
        return run_target_native_gcd_surface_audit(args);
    }
    let mut args = std::env::args_os().skip(1);
    if args.next().as_deref() == Some(std::ffi::OsStr::new("--target-native-dvd-utility-capsule")) {
        return run_target_native_dvd_utility_capsule(args);
    }
    let mut args = std::env::args_os().skip(1);
    if args.next().as_deref()
        == Some(std::ffi::OsStr::new(
            "--target-native-gcd-divisibility-capsule",
        ))
    {
        return run_target_native_gcd_divisibility_capsule(args);
    }
    let mut args = std::env::args_os().skip(1);
    if args.next().as_deref() == Some(std::ffi::OsStr::new("--target-native-gcd-parameter-audit")) {
        return run_target_native_gcd_parameter_audit(args);
    }
    let mut args = std::env::args_os().skip(1);
    if args.next().as_deref() == Some(std::ffi::OsStr::new("--target-native-fib-coprime-capsule")) {
        return run_target_native_fib_coprime_capsule(args);
    }
    let mut args = std::env::args_os().skip(1);
    if args.next().as_deref() == Some(std::ffi::OsStr::new("--target-native-exact-capsule")) {
        return run_target_native_exact_capsule(args);
    }
    let mut args = std::env::args_os().skip(1);
    if args.next().as_deref() == Some(std::ffi::OsStr::new("--target-native-gcd-greatest")) {
        return run_target_native_gcd_greatest(args);
    }
    let mut args = std::env::args_os().skip(1);
    if args.next().as_deref() == Some(std::ffi::OsStr::new("--target-native-fib-gcd")) {
        return run_target_native_fib_gcd(args);
    }
    let mut args = std::env::args_os().skip(1);
    if args.next().as_deref()
        == Some(std::ffi::OsStr::new(
            "--target-native-fib-gcd-helper-type-diagnostic",
        ))
    {
        return run_fib_gcd_helper_type_diagnostic(args);
    }
    let mut args = std::env::args_os().skip(1);
    if args.next().as_deref()
        == Some(std::ffi::OsStr::new(
            "--target-native-fib-gcd-target-type-diagnostic",
        ))
    {
        return run_fib_gcd_target_type_diagnostic(args);
    }
    let mut args = std::env::args_os().skip(1);
    if args.next().as_deref()
        == Some(std::ffi::OsStr::new(
            "--target-native-fib-gcd-induction-argument-diagnostic",
        ))
    {
        return run_fib_gcd_induction_argument_diagnostic(args);
    }
    let mut args = std::env::args_os().skip(1);
    if args.next().as_deref()
        == Some(std::ffi::OsStr::new(
            "--target-native-fib-gcd-step-branch-diagnostic",
        ))
    {
        return run_fib_gcd_step_branch_diagnostic(args);
    }
    let mut args = std::env::args_os().skip(1);
    if args.next().as_deref()
        == Some(std::ffi::OsStr::new(
            "--target-native-fib-gcd-witness-elim-diagnostic",
        ))
    {
        return run_fib_gcd_witness_elim_diagnostic(args);
    }
    let mut args = std::env::args_os().skip(1);
    if args.next().as_deref()
        == Some(std::ffi::OsStr::new(
            "--target-native-fib-gcd-exists-rec-prefix-diagnostic",
        ))
    {
        return run_fib_gcd_exists_rec_prefix_diagnostic(args);
    }
    let mut args = std::env::args_os().skip(1);
    if args.next().as_deref() == Some(std::ffi::OsStr::new("--target-native-goal-audit")) {
        return run_target_native_goal_audit(args);
    }
    let mut args = std::env::args_os().skip(1);
    let r091_path = path(&mut args)?;
    let capsules = [
        (CLEAN_ANTISYMM, path(&mut args)?, CLEAN_ANTISYMM_CAPSULE),
        (CANCELLATION, path(&mut args)?, CANCELLATION_CAPSULE),
        (ADDITION, path(&mut args)?, ADDITION_CAPSULE),
        (COPRIME, path(&mut args)?, COPRIME_CAPSULE),
    ];
    if args.next().is_some() {
        return Err(USAGE.to_owned());
    }
    let imported = import_bound(&r091_path, R091_SHA256, "r091")?;
    if !imported.report().axioms.is_empty() {
        return Err("r091 is not proof-isolated".to_owned());
    }
    let mut kernel = imported.kernel().clone();
    let mut receipts = Vec::new();
    for (root, source_path, expected_sha256) in capsules {
        let source = import_bound(&source_path, expected_sha256, root)?;
        if !source.report().axioms.is_empty() {
            return Err(format!("{root} capsule is not proof-isolated"));
        }
        let completed = if root == COPRIME {
            let existing_zero_left = find_name(&kernel, GCD_ZERO_LEFT_GENERIC)?;
            let existing_zero_left_hash =
                canonical_declaration_sha256(&kernel, existing_zero_left)?;
            if existing_zero_left_hash != GCD_ZERO_LEFT_GENERIC_SHA256 {
                return Err(format!(
                    "existing {GCD_ZERO_LEFT_GENERIC} identity changed: {existing_zero_left_hash}"
                ));
            }
            let public_zero_left = declare_public_gcd_zero_left(&mut kernel)?;
            require_empty(&kernel, public_zero_left, GCD_ZERO_LEFT_PUBLIC)?;
            let public_compatibility = checked_reused_declaration_compatibility(
                source.kernel(),
                &kernel,
                GCD_ZERO_LEFT_PUBLIC,
            )
            .map_err(|error| {
                format!("public gcd zero-left type compatibility declined: {error:?}")
            })?;
            if public_compatibility.compatibility
                != ReusedTypeCompatibility::TranslatedDefinitionalEquality
            {
                return Err(
                    "public gcd zero-left did not require checked translated definitional reuse"
                        .to_owned(),
                );
            }
            let source_leaf = find_name(source.kernel(), COPRIME_GCD_SUCC_LEAF)?;
            let target_leaf = find_name(&kernel, COPRIME_GCD_SUCC_LEAF)?;
            let source_hash = canonical_declaration_sha256(source.kernel(), source_leaf)?;
            let target_hash = canonical_declaration_sha256(&kernel, target_leaf)?;
            if source_hash != COPRIME_GCD_SUCC_LEAF_SHA256 || target_hash != source_hash {
                return Err(format!(
                    "{COPRIME_GCD_SUCC_LEAF} exact target leaf changed: source={source_hash}, target={target_hash}"
                ));
            }
            let completed = compose_checked_theorem_slice_with_target_leaves(
                source.kernel(),
                &kernel,
                &[root],
                &[COPRIME_GCD_SUCC_LEAF, GCD_ZERO_LEFT_PUBLIC],
            )
            .map_err(|error| format!("{root} target-leaf composition declined: {error:?}"))?;
            verify_checked_theorem_composition_with_target_leaves(
                source.kernel(),
                &kernel,
                completed.kernel(),
                completed.receipt(),
            )
            .map_err(|error| format!("{root} target-leaf composition did not replay: {error:?}"))?;
            completed
        } else {
            let completed = compose_checked_theorem_slice(source.kernel(), &kernel, &[root])
                .map_err(|error| format!("{root} composition declined: {error:?}"))?;
            verify_checked_theorem_composition(
                source.kernel(),
                &kernel,
                completed.kernel(),
                completed.receipt(),
            )
            .map_err(|error| format!("{root} composition did not replay: {error:?}"))?;
            completed
        };
        if completed
            .receipt()
            .added_theorems
            .iter()
            .any(|row| !row.axiom_footprint.is_empty())
        {
            return Err(format!(
                "{root} composition added an assumption-bearing theorem"
            ));
        }
        receipts.push(json!({
            "root": root,
            "receipt_sha256": completed.receipt().receipt_sha256,
            "source_closure": completed.receipt().source_closure.len(),
            "added_theorems": completed.receipt().added_theorems.len(),
            "added_definitions": completed.receipt().added_definitions.len(),
            "added_singleton_inductives": completed.receipt().added_singleton_inductives.len(),
        }));
        kernel = completed.kernel().clone();
    }
    let goal_name = find_name(&kernel, GOAL_DEFINITION)?;
    let goal = match kernel.environment().get(goal_name) {
        Some(Declaration::Definition { value, .. }) => *value,
        _ => return Err("r091 goal carrier is not a definition".to_owned()),
    };
    let goal_sha256 = canonical_expression_sha256(&kernel, goal)?;
    if goal_sha256 != GOAL_SHA256 {
        return Err(format!("r091 goal identity changed: {goal_sha256}"));
    }
    let comm = declare_clean_gcd_comm(&mut kernel, false)?;
    require_empty(&kernel, comm, CLEAN_GCD_COMM)?;
    let theorem = declare_target(&mut kernel, goal, false)?;
    require_empty(&kernel, theorem, TARGET)?;
    let proof = match kernel.environment().get(theorem) {
        Some(Declaration::Theorem { value, .. }) => *value,
        _ => return Err("exact target is not a theorem".to_owned()),
    };
    let transitive = transitive_dependencies(&kernel, theorem);
    for root in [CLEAN_ANTISYMM, CANCELLATION, ADDITION, COPRIME] {
        if !transitive.iter().any(|name| name == root) {
            return Err(format!(
                "exact target is independent of required root {root}"
            ));
        }
    }
    println!(
        "{}",
        serde_json::to_string_pretty(&json!({
            "schema_version": 1,
            "kind": "axeyum-autogenesis-nat-gcd-fib-add-self-exact-candidate",
            "state": "exact-target-reconstructed-empty-footprint",
            "target_stream_sha256": R091_SHA256,
            "capsule_compositions": receipts,
            "local_gcd_comm": evidence(&kernel, comm)?,
            "target": {
                "name": TARGET,
                "target_goal_sha256": goal_sha256,
                "proof_sha256": canonical_expression_sha256(&kernel, proof)?,
                "declaration_sha256": canonical_declaration_sha256(&kernel, theorem)?,
                "axiom_footprint": [],
                "direct_theorem_dependencies": names(&kernel, &kernel.theorem_dependencies(theorem)),
                "transitive_theorem_dependencies": transitive,
            },
            "execution": {"capsule_compositions": 4, "local_gcd_comm_submissions": 1, "exact_target_submissions": 1, "retries": 0},
            "rendered_material": {"proof_terms": 0, "theorem_types": 0, "theorem_values": 0},
            "fact_status_changes": 0,
            "evaluation_credit": 0,
            "ledger_writes": 0,
        }))
        .map_err(|error| error.to_string())?
    );
    Ok(())
}

fn run_target_native_dvd_utility_capsule(
    mut args: impl Iterator<Item = std::ffi::OsString>,
) -> Result<(), String> {
    let r091_path = path(&mut args)?;
    let clean_path = path(&mut args)?;
    let cancellation_path = path(&mut args)?;
    let addition_path = path(&mut args)?;
    let simple_path = path(&mut args)?;
    let output_path = path(&mut args)?;
    if args.next().is_some() || output_path.exists() {
        return Err("usage: nat_gcd_fib_add_self_exact --target-native-dvd-utility-capsule <r091> <official-clean-order> <cancellation> <addition> <simple-support> <output>".to_owned());
    }
    let r091 = import_bound(&r091_path, R091_SHA256, "r091")?;
    let clean = import_bound(&clean_path, CLEAN_ANTISYMM_CAPSULE, CLEAN_ANTISYMM)?;
    let cancellation = import_bound(&cancellation_path, CANCELLATION_CAPSULE, CANCELLATION)?;
    let addition = import_bound(&addition_path, ADDITION_CAPSULE, ADDITION)?;
    let simple = import_bound(
        &simple_path,
        "ce0db76dc93690e1e345627ce555e9f53b532a396643581fe554a7bcdce18322",
        "simple-support",
    )?;
    let mut kernel = r091.kernel().clone();
    let mut setup = Vec::new();
    for (roots, source) in [
        (&[CLEAN_ANTISYMM][..], clean.kernel()),
        (&[CANCELLATION][..], cancellation.kernel()),
        (&[ADDITION][..], addition.kernel()),
        (
            &[TARGET_DVD_ADD, TARGET_EQ_ONE_OF_DVD_ONE][..],
            simple.kernel(),
        ),
    ] {
        let completed = compose_checked_theorem_slice(source, &kernel, roots)
            .map_err(|error| format!("dvd utility setup composition declined: {error:?}"))?;
        verify_checked_theorem_composition(
            source,
            &kernel,
            completed.kernel(),
            completed.receipt(),
        )
        .map_err(|error| format!("dvd utility setup did not replay: {error:?}"))?;
        setup.push(json!({"roots": roots, "receipt_sha256": completed.receipt().receipt_sha256}));
        kernel = completed.kernel().clone();
    }
    let refl = declare_target_native_dvd_refl(&mut kernel)?;
    require_empty(&kernel, refl, TARGET_DVD_REFL)?;
    let mul = declare_target_native_dvd_mul_right(&mut kernel)?;
    require_empty(&kernel, mul, TARGET_DVD_MUL_RIGHT)?;
    let expected = [evidence(&kernel, refl)?, evidence(&kernel, mul)?];
    let bytes = kernel
        .render_lean4export_ndjson_roots(&Lean4ExportMetadata::axeyum("4.30.0"), &[refl, mul])
        .map_err(|error| format!("dvd utility capsule export failed: {error}"))?;
    for pass in 1..=2 {
        let replay = import_ndjson(Cursor::new(bytes.as_bytes()), ImportLimits::default())
            .map_err(|error| format!("dvd utility capsule import {pass} failed: {error:?}"))?;
        for (name, expected_row) in [
            (TARGET_DVD_REFL, &expected[0]),
            (TARGET_DVD_MUL_RIGHT, &expected[1]),
        ] {
            let theorem = find_name(replay.kernel(), name)?;
            if evidence(replay.kernel(), theorem)? != *expected_row {
                return Err(format!("dvd utility import {pass} changed {name}"));
            }
        }
    }
    fs::write(&output_path, &bytes)
        .map_err(|error| format!("dvd utility capsule write failed: {error}"))?;
    println!("{}", serde_json::to_string_pretty(&json!({
        "schema_version":1,"kind":"axeyum-autogenesis-target-native-dvd-utility-capsule","state":"two-dvd-utilities-reconstructed-empty-footprint-roundtrip-checked","setup_compositions":setup,"supports":expected,"capsule":{"bytes":bytes.len(),"sha256":hex_sha256(bytes.as_bytes()),"fresh_imports":2},"execution":{"support_submissions":2,"exports":1,"fresh_imports":2,"retries":0},"rendered_material":{"proof_terms":0,"theorem_types":0,"theorem_values":0},"exact_target_submissions":0,"fact_status_changes":0,"evaluation_credit":0,"ledger_writes":0
    })).map_err(|error| error.to_string())?);
    Ok(())
}

#[allow(clippy::too_many_lines)]
fn run_target_native_gcd_divisibility_capsule(
    mut args: impl Iterator<Item = std::ffi::OsString>,
) -> Result<(), String> {
    let r091_path = path(&mut args)?;
    let clean_path = path(&mut args)?;
    let cancellation_path = path(&mut args)?;
    let addition_path = path(&mut args)?;
    let simple_path = path(&mut args)?;
    let dvd_path = path(&mut args)?;
    let generic_path = path(&mut args)?;
    let output_path = path(&mut args)?;
    if args.next().is_some() || output_path.exists() {
        return Err("usage: nat_gcd_fib_add_self_exact --target-native-gcd-divisibility-capsule <r091> <official-clean-order> <cancellation> <addition> <simple-support> <dvd-utilities> <generic-family> <output>".to_owned());
    }
    let inputs = [
        (clean_path, CLEAN_ANTISYMM_CAPSULE, vec![CLEAN_ANTISYMM]),
        (cancellation_path, CANCELLATION_CAPSULE, vec![CANCELLATION]),
        (addition_path, ADDITION_CAPSULE, vec![ADDITION]),
        (
            simple_path,
            "ce0db76dc93690e1e345627ce555e9f53b532a396643581fe554a7bcdce18322",
            vec![TARGET_DVD_ADD, TARGET_EQ_ONE_OF_DVD_ONE],
        ),
        (
            dvd_path,
            "51f5e30677457cb0e6f39799fe062c11d115b1120c04dd23e17dbed596ff3cf3",
            vec![TARGET_DVD_REFL, TARGET_DVD_MUL_RIGHT],
        ),
        (
            generic_path,
            GCD_DIVISIBILITY_GENERIC_CAPSULE,
            vec![GCD_DIVISIBILITY_GENERIC],
        ),
    ];
    let r091 = import_bound(&r091_path, R091_SHA256, "r091")?;
    let mut kernel = r091.kernel().clone();
    let mut setup = Vec::new();
    for (source_path, expected_sha256, roots) in inputs {
        let source = import_bound(&source_path, expected_sha256, roots[0])?;
        let completed = compose_checked_theorem_slice(source.kernel(), &kernel, &roots)
            .map_err(|error| format!("GCD divisibility setup composition declined: {error:?}"))?;
        verify_checked_theorem_composition(
            source.kernel(),
            &kernel,
            completed.kernel(),
            completed.receipt(),
        )
        .map_err(|error| format!("GCD divisibility setup did not replay: {error:?}"))?;
        setup.push(json!({"roots":roots,"receipt_sha256":completed.receipt().receipt_sha256}));
        kernel = completed.kernel().clone();
    }

    let generic = find_name(&kernel, GCD_DIVISIBILITY_GENERIC)?;
    let arguments = [
        find_name(&kernel, GCD_ZERO_LEFT_GENERIC)?,
        find_name(&kernel, "Axeyum.Autogenesis.officialNatGcdSuccClosedV1")?,
        find_name(&kernel, "Axeyum.Autogenesis.modQuotientWitnessV4")?,
        find_name(&kernel, TARGET_DVD_REFL)?,
        find_name(&kernel, TARGET_DVD_MUL_RIGHT)?,
        find_name(&kernel, TARGET_DVD_ADD)?,
        find_name(&kernel, "Axeyum.Autogenesis.dvdAddCancelAllNatClosedV1")?,
    ];
    let closed_name = nested_name(
        &mut kernel,
        &["Axeyum", "Autogenesis", "gcdDivisibilityFamilyClosedV1"],
    );
    let closed = specialize_checked_theorem(&kernel, generic, &arguments, closed_name)
        .map_err(|error| format!("GCD divisibility specialization declined: {error:?}"))?;
    verify_checked_theorem_specialization(
        &kernel,
        closed.kernel(),
        generic,
        &arguments,
        closed_name,
        closed.receipt(),
    )
    .map_err(|error| format!("GCD divisibility specialization did not replay: {error:?}"))?;
    kernel = closed.kernel().clone();
    require_empty(&kernel, closed_name, GCD_DIVISIBILITY_CLOSED)?;

    let left = declare_target_native_gcd_dvd_projection(&mut kernel, true)?;
    require_empty(&kernel, left, TARGET_GCD_DVD_LEFT)?;
    let right = declare_target_native_gcd_dvd_projection(&mut kernel, false)?;
    require_empty(&kernel, right, TARGET_GCD_DVD_RIGHT)?;
    let greatest = declare_target_native_dvd_gcd_projection(&mut kernel)?;
    require_empty(&kernel, greatest, TARGET_DVD_GCD)?;
    let expected = [
        evidence(&kernel, left)?,
        evidence(&kernel, right)?,
        evidence(&kernel, greatest)?,
    ];
    let bytes = kernel
        .render_lean4export_ndjson_roots(
            &Lean4ExportMetadata::axeyum("4.30.0"),
            &[left, right, greatest],
        )
        .map_err(|error| format!("GCD divisibility capsule export failed: {error}"))?;
    for pass in 1..=2 {
        let replay = import_ndjson(Cursor::new(bytes.as_bytes()), ImportLimits::default())
            .map_err(|error| format!("GCD divisibility capsule import {pass} failed: {error:?}"))?;
        for (name, expected_row) in [
            (TARGET_GCD_DVD_LEFT, &expected[0]),
            (TARGET_GCD_DVD_RIGHT, &expected[1]),
            (TARGET_DVD_GCD, &expected[2]),
        ] {
            let theorem = find_name(replay.kernel(), name)?;
            if evidence(replay.kernel(), theorem)? != *expected_row {
                return Err(format!("GCD divisibility import {pass} changed {name}"));
            }
        }
    }
    fs::write(&output_path, &bytes)
        .map_err(|error| format!("GCD divisibility capsule write failed: {error}"))?;
    println!(
        "{}",
        serde_json::to_string_pretty(&json!({
            "schema_version":1,
            "kind":"axeyum-autogenesis-target-native-gcd-divisibility-capsule",
            "state":"three-gcd-divisibility-theorems-reconstructed-empty-footprint-roundtrip-checked",
            "setup_compositions":setup,
            "closed_family":evidence(&kernel, closed_name)?,
            "supports":expected,
            "capsule":{"bytes":bytes.len(),"sha256":hex_sha256(bytes.as_bytes()),"fresh_imports":2},
            "execution":{"closed_theorem_submissions":3,"exports":1,"fresh_imports":2,"retries":0},
            "rendered_material":{"proof_terms":0,"theorem_types":0,"theorem_values":0},
            "exact_target_submissions":0,
            "fact_status_changes":0,
            "evaluation_credit":0,
            "ledger_writes":0
        }))
        .map_err(|error| error.to_string())?
    );
    Ok(())
}

#[allow(clippy::too_many_lines)]
fn run_target_native_gcd_parameter_audit(
    mut args: impl Iterator<Item = std::ffi::OsString>,
) -> Result<(), String> {
    let r091_path = path(&mut args)?;
    let inputs = [
        (
            path(&mut args)?,
            CLEAN_ANTISYMM_CAPSULE,
            vec![CLEAN_ANTISYMM],
        ),
        (path(&mut args)?, CANCELLATION_CAPSULE, vec![CANCELLATION]),
        (path(&mut args)?, ADDITION_CAPSULE, vec![ADDITION]),
        (
            path(&mut args)?,
            "ce0db76dc93690e1e345627ce555e9f53b532a396643581fe554a7bcdce18322",
            vec![TARGET_DVD_ADD, TARGET_EQ_ONE_OF_DVD_ONE],
        ),
        (
            path(&mut args)?,
            "51f5e30677457cb0e6f39799fe062c11d115b1120c04dd23e17dbed596ff3cf3",
            vec![TARGET_DVD_REFL, TARGET_DVD_MUL_RIGHT],
        ),
        (
            path(&mut args)?,
            GCD_DIVISIBILITY_GENERIC_CAPSULE,
            vec![GCD_DIVISIBILITY_GENERIC],
        ),
    ];
    if args.next().is_some() {
        return Err("usage: nat_gcd_fib_add_self_exact --target-native-gcd-parameter-audit <r091> <official-clean-order> <cancellation> <addition> <simple-support> <dvd-utilities> <generic-family>".to_owned());
    }
    let r091 = import_bound(&r091_path, R091_SHA256, "r091")?;
    let mut kernel = r091.kernel().clone();
    for (source_path, expected_sha256, roots) in inputs {
        let source = import_bound(&source_path, expected_sha256, roots[0])?;
        let completed = compose_checked_theorem_slice(source.kernel(), &kernel, &roots)
            .map_err(|error| format!("GCD parameter audit composition declined: {error:?}"))?;
        verify_checked_theorem_composition(
            source.kernel(),
            &kernel,
            completed.kernel(),
            completed.receipt(),
        )
        .map_err(|error| format!("GCD parameter audit composition did not replay: {error:?}"))?;
        kernel = completed.kernel().clone();
    }
    let generic = find_name(&kernel, GCD_DIVISIBILITY_GENERIC)?;
    let argument_names = [
        GCD_ZERO_LEFT_GENERIC,
        "Axeyum.Autogenesis.officialNatGcdSuccClosedV1",
        "Axeyum.Autogenesis.modQuotientWitnessV4",
        TARGET_DVD_REFL,
        TARGET_DVD_MUL_RIGHT,
        TARGET_DVD_ADD,
        "Axeyum.Autogenesis.dvdAddCancelAllNatClosedV1",
    ];
    let mut proof = kernel.const_(generic, vec![]);
    let mut rows = Vec::new();
    let mut first_incompatible = None;
    for (position, expected_name) in argument_names.iter().enumerate() {
        let argument = find_name(&kernel, expected_name)?;
        let argument_constant = kernel.const_(argument, vec![]);
        let argument_type = kernel
            .infer(argument_constant)
            .map_err(|error| format!("cannot infer {expected_name} type: {error:?}"))?;
        let candidate = kernel.app(proof, argument_constant);
        let inferred = kernel.infer(candidate);
        let compatible = inferred.is_ok();
        let error = inferred.err().map(|value| format!("{value:?}"));
        rows.push(json!({
            "position":position,
            "name":expected_name,
            "declaration_sha256":canonical_declaration_sha256(&kernel,argument)?,
            "kernel_type_shape_sha256":canonical_kernel_type_shape_sha256(&kernel,argument_type)?,
            "application_typechecks":compatible,
            "error":error,
        }));
        if !compatible {
            first_incompatible = Some(position);
            break;
        }
        proof = candidate;
    }
    println!(
        "{}",
        serde_json::to_string_pretty(&json!({
            "schema_version":1,
            "kind":"axeyum-autogenesis-target-native-gcd-parameter-audit",
            "state":"generic-parameters-checked-without-rendering",
            "generic":{"name":GCD_DIVISIBILITY_GENERIC,"declaration_sha256":canonical_declaration_sha256(&kernel,generic)?},
            "parameters":rows,
            "first_incompatible_position":first_incompatible,
            "execution":{"complete_audits":1,"kernel_submissions":0,"exports":0,"retries":0},
            "rendered_material":{"proof_terms":0,"theorem_types":0,"theorem_values":0},
            "exact_target_submissions":0,
            "fact_status_changes":0,
            "evaluation_credit":0,
            "ledger_writes":0
        }))
        .map_err(|error| error.to_string())?
    );
    Ok(())
}

#[allow(clippy::too_many_lines)]
fn run_target_native_fib_coprime_capsule(
    mut args: impl Iterator<Item = std::ffi::OsString>,
) -> Result<(), String> {
    let r091_path = path(&mut args)?;
    let inputs = [
        (
            path(&mut args)?,
            CLEAN_ANTISYMM_CAPSULE,
            vec![CLEAN_ANTISYMM],
        ),
        (path(&mut args)?, CANCELLATION_CAPSULE, vec![CANCELLATION]),
        (path(&mut args)?, ADDITION_CAPSULE, vec![ADDITION]),
        (
            path(&mut args)?,
            "ce0db76dc93690e1e345627ce555e9f53b532a396643581fe554a7bcdce18322",
            vec![TARGET_DVD_ADD, TARGET_EQ_ONE_OF_DVD_ONE],
        ),
        (
            path(&mut args)?,
            "51f5e30677457cb0e6f39799fe062c11d115b1120c04dd23e17dbed596ff3cf3",
            vec![TARGET_DVD_REFL, TARGET_DVD_MUL_RIGHT],
        ),
        (
            path(&mut args)?,
            "9ecf0b10d1390f880040790fb1845a11d7987b94c0d3a71acf4ad8dca0c5a304",
            vec![TARGET_GCD_DVD_LEFT, TARGET_GCD_DVD_RIGHT, TARGET_DVD_GCD],
        ),
    ];
    let output_path = path(&mut args)?;
    if args.next().is_some() || output_path.exists() {
        return Err("usage: nat_gcd_fib_add_self_exact --target-native-fib-coprime-capsule <r091> <official-clean-order> <cancellation> <addition> <simple-support> <dvd-utilities> <gcd-divisibility> <output>".to_owned());
    }
    let r091 = import_bound(&r091_path, R091_SHA256, "r091")?;
    let mut kernel = r091.kernel().clone();
    let mut setup = Vec::new();
    for (source_path, expected_sha256, roots) in inputs {
        let source = import_bound(&source_path, expected_sha256, roots[0])?;
        let completed = compose_checked_theorem_slice(source.kernel(), &kernel, &roots)
            .map_err(|error| format!("target-native coprime setup declined: {error:?}"))?;
        verify_checked_theorem_composition(
            source.kernel(),
            &kernel,
            completed.kernel(),
            completed.receipt(),
        )
        .map_err(|error| format!("target-native coprime setup did not replay: {error:?}"))?;
        setup.push(json!({"roots":roots,"receipt_sha256":completed.receipt().receipt_sha256}));
        kernel = completed.kernel().clone();
    }
    let target = nested_name(
        &mut kernel,
        &["Axeyum", "Autogenesis", "fibCoprimeFibSuccOfficialV1"],
    );
    let goal = target_native_fib_coprime_goal(&mut kernel)?;
    let (theorem, _, _) = fib_coprime::admit_target_native(
        &mut kernel,
        target,
        goal,
        "Axeyum.Autogenesis.fibAddTwo",
    )?;
    require_empty(&kernel, theorem, TARGET_FIB_COPRIME)?;
    let expected = evidence(&kernel, theorem)?;
    let forbidden = [
        "Iff",
        "Iff.rec",
        "Nat.dvd_add_iff_right",
        "Nat.dvd_gcd",
        "Nat.eq_one_of_dvd_one",
        "Nat.gcd_dvd_left",
        "Nat.gcd_dvd_right",
        "Nat.gcd_zero_left",
        "propext",
        "Quot.sound",
    ];
    let transitive = transitive_dependencies(&kernel, theorem);
    if let Some(name) = forbidden
        .iter()
        .find(|name| transitive.iter().any(|item| item == **name))
    {
        return Err(format!(
            "target-native coprime reaches forbidden dependency {name}"
        ));
    }
    let bytes = kernel
        .render_lean4export_ndjson_roots(&Lean4ExportMetadata::axeyum("4.30.0"), &[theorem])
        .map_err(|error| format!("target-native coprime capsule export failed: {error}"))?;
    for pass in 1..=2 {
        let replay = import_ndjson(Cursor::new(bytes.as_bytes()), ImportLimits::default())
            .map_err(|error| format!("target-native coprime import {pass} failed: {error:?}"))?;
        let replayed = find_name(replay.kernel(), TARGET_FIB_COPRIME)?;
        if evidence(replay.kernel(), replayed)? != expected {
            return Err(format!(
                "target-native coprime import {pass} changed theorem"
            ));
        }
    }
    fs::write(&output_path, &bytes)
        .map_err(|error| format!("target-native coprime capsule write failed: {error}"))?;
    println!(
        "{}",
        serde_json::to_string_pretty(&json!({
            "schema_version":1,
            "kind":"axeyum-autogenesis-target-native-fib-coprime-capsule",
            "state":"target-native-fibonacci-coprimality-reconstructed-empty-footprint-roundtrip-checked",
            "setup_compositions":setup,
            "theorem":expected,
            "transitive_theorem_dependencies":transitive,
            "capsule":{"bytes":bytes.len(),"sha256":hex_sha256(bytes.as_bytes()),"fresh_imports":2},
            "execution":{"coprime_submissions":1,"exports":1,"fresh_imports":2,"retries":0},
            "rendered_material":{"proof_terms":0,"theorem_types":0,"theorem_values":0},
            "exact_target_submissions":0,
            "fact_status_changes":0,
            "evaluation_credit":0,
            "ledger_writes":0
        }))
        .map_err(|error| error.to_string())?
    );
    Ok(())
}

fn target_native_fib_coprime_goal(kernel: &mut Kernel) -> Result<ExprId, String> {
    let mut d = Dev::new(kernel)?;
    let nat = d.nat_ty();
    let value_fv = d.fresh();
    let value = d.kernel.fvar(value_fv);
    let successor = d.succ(value);
    let left = d.fib(value);
    let right = d.fib(successor);
    let gcd = d.gcd(left, right);
    let one = d.num(1);
    let conclusion = d.eq(gcd, one);
    Ok(d.pi(value_fv, nat, conclusion))
}

#[allow(clippy::too_many_lines)]
fn run_target_native_exact_capsule(
    mut args: impl Iterator<Item = std::ffi::OsString>,
) -> Result<(), String> {
    let r091_path = path(&mut args)?;
    let inputs = [
        (
            path(&mut args)?,
            CLEAN_ANTISYMM_CAPSULE,
            vec![CLEAN_ANTISYMM],
        ),
        (path(&mut args)?, CANCELLATION_CAPSULE, vec![CANCELLATION]),
        (path(&mut args)?, ADDITION_CAPSULE, vec![ADDITION]),
        (
            path(&mut args)?,
            "9ecf0b10d1390f880040790fb1845a11d7987b94c0d3a71acf4ad8dca0c5a304",
            vec![TARGET_GCD_DVD_LEFT, TARGET_GCD_DVD_RIGHT, TARGET_DVD_GCD],
        ),
        (
            path(&mut args)?,
            "e7933242c5caeb90a17bb7141656fe12a1c78780a83e82958c9ddd38ccd85d3f",
            vec![TARGET_FIB_COPRIME],
        ),
    ];
    let output_path = path(&mut args)?;
    if args.next().is_some() || output_path.exists() {
        return Err("usage: nat_gcd_fib_add_self_exact --target-native-exact-capsule <r091> <official-clean-order> <cancellation> <addition> <gcd-divisibility> <target-native-coprimality> <output>".to_owned());
    }
    let r091 = import_bound(&r091_path, R091_SHA256, "r091")?;
    let mut kernel = r091.kernel().clone();
    let mut setup = Vec::new();
    for (source_path, expected_sha256, roots) in inputs {
        let source = import_bound(&source_path, expected_sha256, roots[0])?;
        let completed = compose_checked_theorem_slice(source.kernel(), &kernel, &roots)
            .map_err(|error| format!("target-native exact setup declined: {error:?}"))?;
        verify_checked_theorem_composition(
            source.kernel(),
            &kernel,
            completed.kernel(),
            completed.receipt(),
        )
        .map_err(|error| format!("target-native exact setup did not replay: {error:?}"))?;
        setup.push(json!({"roots":roots,"receipt_sha256":completed.receipt().receipt_sha256}));
        kernel = completed.kernel().clone();
    }
    let goal_name = find_name(&kernel, GOAL_DEFINITION)?;
    let goal = match kernel.environment().get(goal_name) {
        Some(Declaration::Definition { value, .. }) => *value,
        _ => return Err("r091 goal carrier is not a definition".to_owned()),
    };
    let goal_sha256 = canonical_expression_sha256(&kernel, goal)?;
    if goal_sha256 != TARGET_NATIVE_GOAL_SHA256 {
        return Err(format!("r091 goal identity changed: {goal_sha256}"));
    }
    let constructed_goal = {
        let mut d = Dev::new(&mut kernel)?;
        let nat = d.nat_ty();
        let m_fv = d.fresh();
        let m = d.kernel.fvar(m_fv);
        let n_fv = d.fresh();
        let n = d.kernel.fvar(n_fv);
        let body = statement(&mut d, m, n);
        let body = d.pi(n_fv, nat, body);
        d.pi(m_fv, nat, body)
    };
    if !kernel.def_eq(goal, constructed_goal) {
        return Err(
            "r091 goal is not definitionally equal to the exact constructed statement".to_owned(),
        );
    }
    let comm = declare_clean_gcd_comm(&mut kernel, true)?;
    require_empty(&kernel, comm, CLEAN_GCD_COMM)?;
    let theorem = declare_target(&mut kernel, goal, true)?;
    require_empty(&kernel, theorem, TARGET)?;
    let transitive = transitive_dependencies(&kernel, theorem);
    let required = [
        CLEAN_ANTISYMM,
        CANCELLATION,
        ADDITION,
        TARGET_GCD_DVD_LEFT,
        TARGET_GCD_DVD_RIGHT,
        TARGET_DVD_GCD,
        TARGET_DVD_MUL_RIGHT,
        TARGET_DVD_ADD,
        "Axeyum.Autogenesis.dvdAddCancelAllNatClosedV1",
        TARGET_FIB_COPRIME,
    ];
    if let Some(name) = required
        .iter()
        .find(|name| !transitive.iter().any(|item| item == **name))
    {
        return Err(format!(
            "target-native exact proof is independent of {name}"
        ));
    }
    let forbidden = [
        "Iff",
        "Iff.rec",
        "Nat.dvd_add_iff_right",
        "Nat.dvd_gcd",
        "Nat.gcd_dvd_left",
        "Nat.gcd_dvd_right",
        "Nat.dvd_mul_right_of_dvd",
        "Nat.dvd_add",
        "propext",
        "Quot.sound",
    ];
    if let Some(name) = forbidden
        .iter()
        .find(|name| transitive.iter().any(|item| item == **name))
    {
        return Err(format!(
            "target-native exact proof reaches forbidden dependency {name}"
        ));
    }
    let expected = evidence(&kernel, theorem)?;
    let bytes = kernel
        .render_lean4export_ndjson_roots(&Lean4ExportMetadata::axeyum("4.30.0"), &[theorem])
        .map_err(|error| format!("target-native exact capsule export failed: {error}"))?;
    for pass in 1..=2 {
        let replay = import_ndjson(Cursor::new(bytes.as_bytes()), ImportLimits::default())
            .map_err(|error| format!("target-native exact import {pass} failed: {error:?}"))?;
        let replayed = find_name(replay.kernel(), TARGET)?;
        if evidence(replay.kernel(), replayed)? != expected {
            return Err(format!("target-native exact import {pass} changed theorem"));
        }
    }
    fs::write(&output_path, &bytes)
        .map_err(|error| format!("target-native exact capsule write failed: {error}"))?;
    println!(
        "{}",
        serde_json::to_string_pretty(&json!({
            "schema_version":1,
            "kind":"axeyum-autogenesis-target-native-nat-gcd-fib-add-self-capsule",
            "state":"exact-target-reconstructed-empty-footprint-roundtrip-checked",
            "target_goal_sha256":goal_sha256,
            "setup_compositions":setup,
            "local_gcd_comm":evidence(&kernel,comm)?,
            "target":expected,
            "transitive_theorem_dependencies":transitive,
            "capsule":{"bytes":bytes.len(),"sha256":hex_sha256(bytes.as_bytes()),"fresh_imports":2},
            "execution":{"local_gcd_comm_submissions":1,"exact_target_submissions":1,"exports":1,"fresh_imports":2,"retries":0},
            "rendered_material":{"proof_terms":0,"theorem_types":0,"theorem_values":0},
            "fact_status_changes":0,
            "evaluation_credit":0,
            "ledger_writes":0
        }))
        .map_err(|error| error.to_string())?
    );
    Ok(())
}

fn run_target_native_gcd_greatest(
    mut args: impl Iterator<Item = std::ffi::OsString>,
) -> Result<(), String> {
    let gcd_input_path = path(&mut args)?;
    let antisymm_input_path = path(&mut args)?;
    let output_path = path(&mut args)?;
    if args.next().is_some() || output_path.exists() {
        return Err(
            "usage: nat_gcd_fib_add_self_exact --target-native-gcd-greatest \
             <gcd-divisibility> <clean-antisymmetry> <output>"
                .to_owned(),
        );
    }
    let gcd_source = import_bound(
        &gcd_input_path,
        "9ecf0b10d1390f880040790fb1845a11d7987b94c0d3a71acf4ad8dca0c5a304",
        "target-native GCD divisibility",
    )?;
    let antisymm_source = import_bound(
        &antisymm_input_path,
        CLEAN_ANTISYMM_CAPSULE,
        "clean divisibility antisymmetry",
    )?;
    let composed = compose_checked_theorem_slice(
        antisymm_source.kernel(),
        gcd_source.kernel(),
        &[CLEAN_ANTISYMM],
    )
    .map_err(|error| format!("Nat.gcd_greatest setup composition declined: {error:?}"))?;
    verify_checked_theorem_composition(
        antisymm_source.kernel(),
        gcd_source.kernel(),
        composed.kernel(),
        composed.receipt(),
    )
    .map_err(|error| format!("Nat.gcd_greatest setup composition did not replay: {error:?}"))?;
    let composition_receipt = composed.receipt().receipt_sha256.clone();
    let mut kernel = composed.kernel().clone();
    let theorem = declare_target_native_gcd_greatest(&mut kernel)?;
    require_empty(&kernel, theorem, GCD_GREATEST_TARGET)?;
    let expected = evidence(&kernel, theorem)?;
    let expected_dependencies = [
        CLEAN_ANTISYMM,
        TARGET_DVD_GCD,
        TARGET_GCD_DVD_LEFT,
        TARGET_GCD_DVD_RIGHT,
    ];
    if expected["direct_theorem_dependencies"] != json!(expected_dependencies) {
        return Err(format!(
            "Nat.gcd_greatest direct dependency set changed: {}",
            expected["direct_theorem_dependencies"]
        ));
    }
    let goal = theorem_type(&kernel, theorem)?;
    let goal_sha256 = canonical_expression_sha256(&kernel, goal)?;
    let bytes = kernel
        .render_lean4export_ndjson_roots(&Lean4ExportMetadata::axeyum("4.30.0"), &[theorem])
        .map_err(|error| format!("Nat.gcd_greatest capsule export failed: {error}"))?;
    for pass in 1..=2 {
        let replay = import_ndjson(Cursor::new(bytes.as_bytes()), ImportLimits::default())
            .map_err(|error| format!("Nat.gcd_greatest import {pass} failed: {error:?}"))?;
        let replayed = find_name(replay.kernel(), GCD_GREATEST_TARGET)?;
        if evidence(replay.kernel(), replayed)? != expected {
            return Err(format!("Nat.gcd_greatest import {pass} changed theorem"));
        }
    }
    fs::write(&output_path, &bytes)
        .map_err(|error| format!("Nat.gcd_greatest capsule write failed: {error}"))?;
    println!(
        "{}",
        serde_json::to_string_pretty(&json!({
            "schema_version":1,
            "kind":"axeyum-autogenesis-target-native-nat-gcd-greatest-capsule",
            "state":"exact-target-reconstructed-empty-footprint-roundtrip-checked",
            "composition_receipt_sha256":composition_receipt,
            "target_goal_sha256":goal_sha256,
            "target":expected,
            "capsule":{"bytes":bytes.len(),"sha256":hex_sha256(bytes.as_bytes()),"fresh_imports":2},
            "execution":{"exact_target_submissions":1,"exports":1,"fresh_imports":2,"retries":0},
            "rendered_material":{"proof_terms":0,"theorem_types":0,"theorem_values":0},
            "search_invocations":0,
            "fact_status_changes":0,
            "evaluation_credit":0,
            "ledger_writes":0
        }))
        .map_err(|error| error.to_string())?
    );
    Ok(())
}

fn declare_target_native_gcd_greatest(kernel: &mut Kernel) -> Result<NameId, String> {
    let target = nested_name(kernel, &["Nat", "gcd_greatest"]);
    if optional_name(kernel, GCD_GREATEST_TARGET)?.is_some() {
        return Err("Nat.gcd_greatest unexpectedly already exists".to_owned());
    }
    let mut d = GcdDev::new(kernel)?;
    let antisymm = d.exact(CLEAN_ANTISYMM)?;
    let dvd_gcd = d.exact(TARGET_DVD_GCD)?;
    let gcd_left = d.exact(TARGET_GCD_DVD_LEFT)?;
    let gcd_right = d.exact(TARGET_GCD_DVD_RIGHT)?;
    let nat = d.nat_ty();
    let a_fv = d.fresh();
    let a = d.kernel.fvar(a_fv);
    let b_fv = d.fresh();
    let b = d.kernel.fvar(b_fv);
    let divisor_fv = d.fresh();
    let divisor = d.kernel.fvar(divisor_fv);
    let divisor_left_ty = d.dvd(divisor, a);
    let divisor_left_fv = d.fresh();
    let divisor_left = d.kernel.fvar(divisor_left_fv);
    let divisor_right_ty = d.dvd(divisor, b);
    let divisor_right_fv = d.fresh();
    let divisor_right = d.kernel.fvar(divisor_right_fv);
    let candidate_fv = d.fresh();
    let candidate = d.kernel.fvar(candidate_fv);
    let candidate_left = d.dvd(candidate, a);
    let candidate_right = d.dvd(candidate, b);
    let candidate_divisor = d.dvd(candidate, divisor);
    let greatest_body = d.arrow(candidate_right, candidate_divisor);
    let greatest_body = d.arrow(candidate_left, greatest_body);
    let greatest_ty = d.pi(candidate_fv, nat, greatest_body);
    let greatest_fv = d.fresh();
    let greatest = d.kernel.fvar(greatest_fv);
    let gcd = d.gcd(a, b);
    let divisor_gcd = d.lemma(dvd_gcd, &[divisor, a, b, divisor_left, divisor_right]);
    let gcd_left_proof = d.lemma(gcd_left, &[a, b]);
    let gcd_right_proof = d.lemma(gcd_right, &[a, b]);
    let gcd_divisor = d.apply(greatest, &[gcd, gcd_left_proof, gcd_right_proof]);
    let conclusion = d.eq(divisor, gcd);
    let proof = d.lemma(antisymm, &[divisor, gcd, divisor_gcd, gcd_divisor]);
    let proof = d.lam(greatest_fv, greatest_ty, proof);
    let proof = d.lam(divisor_right_fv, divisor_right_ty, proof);
    let proof = d.lam(divisor_left_fv, divisor_left_ty, proof);
    let proof = d.lam_info(divisor_fv, nat, proof, BinderInfo::Implicit);
    let proof = d.lam_info(b_fv, nat, proof, BinderInfo::Implicit);
    let proof = d.lam_info(a_fv, nat, proof, BinderInfo::Implicit);
    let ty = d.arrow(greatest_ty, conclusion);
    let ty = d.arrow(divisor_right_ty, ty);
    let ty = d.arrow(divisor_left_ty, ty);
    let ty = d.pi_info(divisor_fv, nat, ty, BinderInfo::Implicit);
    let ty = d.pi_info(b_fv, nat, ty, BinderInfo::Implicit);
    let ty = d.pi_info(a_fv, nat, ty, BinderInfo::Implicit);
    d.kernel
        .add_declaration(Declaration::Theorem {
            name: target,
            uparams: vec![],
            ty,
            value: proof,
        })
        .map_err(|error| format!("target-native Nat.gcd_greatest rejected: {error:?}"))?;
    Ok(target)
}

fn run_target_native_fib_gcd(
    mut args: impl Iterator<Item = std::ffi::OsString>,
) -> Result<(), String> {
    let greatest_path = path(&mut args)?;
    let shift_path = path(&mut args)?;
    let output_path = path(&mut args)?;
    if args.next().is_some() || output_path.exists() {
        return Err("usage: nat_gcd_fib_add_self_exact --target-native-fib-gcd \
             <gcd-greatest> <gcd-fib-add-self> <output>"
            .to_owned());
    }
    let greatest = import_bound(&greatest_path, GCD_GREATEST_CAPSULE, "gcd-greatest")?;
    let shift = import_bound(&shift_path, GCD_FIB_SHIFT_CAPSULE, "gcd-fib-add-self")?;
    let composed = compose_checked_theorem_slice(shift.kernel(), greatest.kernel(), &[TARGET])
        .map_err(|error| format!("Nat.fib_gcd setup composition declined: {error:?}"))?;
    verify_checked_theorem_composition(
        shift.kernel(),
        greatest.kernel(),
        composed.kernel(),
        composed.receipt(),
    )
    .map_err(|error| format!("Nat.fib_gcd setup composition did not replay: {error:?}"))?;
    let composition_receipt = composed.receipt().receipt_sha256.clone();
    let mut kernel = composed.kernel().clone();
    let helper = declare_fib_gcd_quotient_iteration(&mut kernel)?;
    require_empty(&kernel, helper, FIB_GCD_ITERATION)?;
    let theorem = declare_fib_gcd(&mut kernel)?;
    require_empty(&kernel, theorem, FIB_GCD_TARGET)?;
    let helper_evidence = evidence(&kernel, helper)?;
    let target_evidence = evidence(&kernel, theorem)?;
    let target_goal = theorem_type(&kernel, theorem)?;
    let target_goal_sha256 = canonical_expression_sha256(&kernel, target_goal)?;
    let bytes = kernel
        .render_lean4export_ndjson_roots(&Lean4ExportMetadata::axeyum("4.30.0"), &[theorem])
        .map_err(|error| format!("Nat.fib_gcd capsule export failed: {error}"))?;
    for pass in 1..=2 {
        let replay = import_ndjson(Cursor::new(bytes.as_bytes()), ImportLimits::default())
            .map_err(|error| format!("Nat.fib_gcd import {pass} failed: {error:?}"))?;
        let replayed = find_name(replay.kernel(), FIB_GCD_TARGET)?;
        if evidence(replay.kernel(), replayed)? != target_evidence {
            return Err(format!("Nat.fib_gcd import {pass} changed theorem"));
        }
    }
    fs::write(&output_path, &bytes)
        .map_err(|error| format!("Nat.fib_gcd capsule write failed: {error}"))?;
    println!(
        "{}",
        serde_json::to_string_pretty(&json!({
            "schema_version":1,
            "kind":"axeyum-autogenesis-target-native-nat-fib-gcd-capsule",
            "state":"exact-helper-and-target-reconstructed-empty-footprint-roundtrip-checked",
            "composition_receipt_sha256":composition_receipt,
            "target_goal_sha256":target_goal_sha256,
            "helper":helper_evidence,
            "target":target_evidence,
            "capsule":{"bytes":bytes.len(),"sha256":hex_sha256(bytes.as_bytes()),"fresh_imports":2},
            "execution":{"helper_theorem_submissions":1,"target_theorem_submissions":1,"exports":1,"fresh_imports":2,"retries":0},
            "rendered_material":{"proof_terms":0,"theorem_types":0,"theorem_values":0},
            "search_invocations":0,
            "fact_status_changes":0,
            "evaluation_credit":0,
            "ledger_writes":0
        }))
        .map_err(|error| error.to_string())?
    );
    Ok(())
}

fn run_fib_gcd_helper_type_diagnostic(
    mut args: impl Iterator<Item = std::ffi::OsString>,
) -> Result<(), String> {
    let greatest_path = path(&mut args)?;
    let shift_path = path(&mut args)?;
    if args.next().is_some() {
        return Err("usage: nat_gcd_fib_add_self_exact \
             --target-native-fib-gcd-helper-type-diagnostic \
             <gcd-greatest> <gcd-fib-add-self>"
            .to_owned());
    }
    let greatest = import_bound(&greatest_path, GCD_GREATEST_CAPSULE, "gcd-greatest")?;
    let shift = import_bound(&shift_path, GCD_FIB_SHIFT_CAPSULE, "gcd-fib-add-self")?;
    let composed = compose_checked_theorem_slice(shift.kernel(), greatest.kernel(), &[TARGET])
        .map_err(|error| format!("helper diagnostic composition declined: {error:?}"))?;
    verify_checked_theorem_composition(
        shift.kernel(),
        greatest.kernel(),
        composed.kernel(),
        composed.receipt(),
    )
    .map_err(|error| format!("helper diagnostic composition did not replay: {error:?}"))?;
    let mut kernel = composed.kernel().clone();
    let (_name, expected, proof) = build_fib_gcd_quotient_iteration(&mut kernel)?;
    let inferred = kernel
        .infer(proof)
        .map_err(|error| format!("helper proof inference failed: {error:?}"))?;
    let definitionally_equal = kernel.def_eq(expected, inferred);
    println!(
        "{}",
        serde_json::to_string_pretty(&json!({
            "schema_version":1,
            "kind":"axeyum-autogenesis-nat-fib-gcd-helper-type-diagnostic-v1",
            "state":"expected-and-inferred-helper-types-compared-without-submission",
            "expected":{"type":kernel.render_lean(expected),"sha256":canonical_expression_sha256(&kernel,expected)?},
            "inferred":{"type":kernel.render_lean(inferred),"sha256":canonical_expression_sha256(&kernel,inferred)?},
            "definitionally_equal":definitionally_equal,
            "execution":{"complete_diagnostics":1,"proof_inferences":1,"helper_theorem_submissions":0,"target_theorem_submissions":0,"proof_values_rendered":0,"retries":0,"ledger_writes":0}
        }))
        .map_err(|error| error.to_string())?
    );
    Ok(())
}

fn run_fib_gcd_target_type_diagnostic(
    mut args: impl Iterator<Item = std::ffi::OsString>,
) -> Result<(), String> {
    let greatest_path = path(&mut args)?;
    let shift_path = path(&mut args)?;
    if args.next().is_some() {
        return Err("usage: nat_gcd_fib_add_self_exact \
             --target-native-fib-gcd-target-type-diagnostic \
             <gcd-greatest> <gcd-fib-add-self>"
            .to_owned());
    }
    let greatest = import_bound(&greatest_path, GCD_GREATEST_CAPSULE, "gcd-greatest")?;
    let shift = import_bound(&shift_path, GCD_FIB_SHIFT_CAPSULE, "gcd-fib-add-self")?;
    let composed = compose_checked_theorem_slice(shift.kernel(), greatest.kernel(), &[TARGET])
        .map_err(|error| format!("target diagnostic composition declined: {error:?}"))?;
    verify_checked_theorem_composition(
        shift.kernel(),
        greatest.kernel(),
        composed.kernel(),
        composed.receipt(),
    )
    .map_err(|error| format!("target diagnostic composition did not replay: {error:?}"))?;
    let mut kernel = composed.kernel().clone();
    declare_fib_gcd_quotient_iteration(&mut kernel)?;
    let (_name, expected, proof) = build_fib_gcd(&mut kernel)?;
    let inferred = kernel
        .infer(proof)
        .map_err(|error| format!("target proof inference failed: {error:?}"))?;
    let definitionally_equal = kernel.def_eq(expected, inferred);
    println!(
        "{}",
        serde_json::to_string_pretty(&json!({
            "schema_version":1,
            "kind":"axeyum-autogenesis-nat-fib-gcd-target-type-diagnostic-v1",
            "state":"expected-and-inferred-target-types-compared-without-target-submission",
            "expected":{"type":kernel.render_lean(expected),"sha256":canonical_expression_sha256(&kernel,expected)?},
            "inferred":{"type":kernel.render_lean(inferred),"sha256":canonical_expression_sha256(&kernel,inferred)?},
            "definitionally_equal":definitionally_equal,
            "execution":{"complete_diagnostics":1,"helper_theorem_submissions":1,"target_proof_inferences":1,"target_theorem_submissions":0,"proof_values_rendered":0,"capsule_writes":0,"retries":0,"ledger_writes":0}
        }))
        .map_err(|error| error.to_string())?
    );
    Ok(())
}

fn run_fib_gcd_induction_argument_diagnostic(
    mut args: impl Iterator<Item = std::ffi::OsString>,
) -> Result<(), String> {
    let greatest_path = path(&mut args)?;
    let shift_path = path(&mut args)?;
    if args.next().is_some() {
        return Err("usage: nat_gcd_fib_add_self_exact \
             --target-native-fib-gcd-induction-argument-diagnostic \
             <gcd-greatest> <gcd-fib-add-self>"
            .to_owned());
    }
    let greatest = import_bound(&greatest_path, GCD_GREATEST_CAPSULE, "gcd-greatest")?;
    let shift = import_bound(&shift_path, GCD_FIB_SHIFT_CAPSULE, "gcd-fib-add-self")?;
    let composed = compose_checked_theorem_slice(shift.kernel(), greatest.kernel(), &[TARGET])
        .map_err(|error| format!("induction diagnostic composition declined: {error:?}"))?;
    verify_checked_theorem_composition(
        shift.kernel(),
        greatest.kernel(),
        composed.kernel(),
        composed.receipt(),
    )
    .map_err(|error| format!("induction diagnostic composition did not replay: {error:?}"))?;
    let mut kernel = composed.kernel().clone();
    declare_fib_gcd_quotient_iteration(&mut kernel)?;
    let mut d = Dev::new(&mut kernel)?;
    let quotient = d.exact("Axeyum.Autogenesis.modQuotientWitnessV4")?;
    let helper = d.exact(FIB_GCD_ITERATION)?;
    let gcd_comm = d.exact(CLEAN_GCD_COMM)?;
    let nat = d.nat_ty();
    let base_n_fv = d.fresh();
    let base_n = d.kernel.fvar(base_n_fv);
    let fib_base_n = d.fib(base_n);
    let base = d.refl(fib_base_n);
    let base = d.lam(base_n_fv, nat, base);
    let base_type = d
        .kernel
        .infer(base)
        .map_err(|error| format!("base proof inference failed: {error:?}"))?;
    let step = fib_gcd_step(&mut d, quotient, helper, gcd_comm)?;
    let step_type = d
        .kernel
        .infer(step)
        .map_err(|error| format!("step proof inference failed: {error:?}"))?;
    println!(
        "{}",
        serde_json::to_string_pretty(&json!({
            "schema_version":1,
            "kind":"axeyum-autogenesis-nat-fib-gcd-induction-argument-diagnostic-v1",
            "state":"base-and-step-types-inferred-without-target-construction",
            "base":{"type":d.kernel.render_lean(base_type),"sha256":canonical_expression_sha256(d.kernel,base_type)?},
            "step":{"type":d.kernel.render_lean(step_type),"sha256":canonical_expression_sha256(d.kernel,step_type)?},
            "execution":{"complete_diagnostics":1,"helper_theorem_submissions":1,"base_proof_inferences":1,"step_proof_inferences":1,"target_proof_inferences":0,"target_theorem_submissions":0,"proof_values_rendered":0,"capsule_writes":0,"retries":0,"ledger_writes":0}
        }))
        .map_err(|error| error.to_string())?
    );
    Ok(())
}

fn run_fib_gcd_step_branch_diagnostic(
    mut args: impl Iterator<Item = std::ffi::OsString>,
) -> Result<(), String> {
    let greatest_path = path(&mut args)?;
    let shift_path = path(&mut args)?;
    if args.next().is_some() {
        return Err("usage: nat_gcd_fib_add_self_exact \
             --target-native-fib-gcd-step-branch-diagnostic \
             <gcd-greatest> <gcd-fib-add-self>"
            .to_owned());
    }
    let greatest = import_bound(&greatest_path, GCD_GREATEST_CAPSULE, "gcd-greatest")?;
    let shift = import_bound(&shift_path, GCD_FIB_SHIFT_CAPSULE, "gcd-fib-add-self")?;
    let composed = compose_checked_theorem_slice(shift.kernel(), greatest.kernel(), &[TARGET])
        .map_err(|error| format!("step-branch diagnostic composition declined: {error:?}"))?;
    verify_checked_theorem_composition(
        shift.kernel(),
        greatest.kernel(),
        composed.kernel(),
        composed.receipt(),
    )
    .map_err(|error| format!("step-branch diagnostic composition did not replay: {error:?}"))?;
    let mut kernel = composed.kernel().clone();
    declare_fib_gcd_quotient_iteration(&mut kernel)?;
    let mut d = Dev::new(&mut kernel)?;
    let quotient = d.exact("Axeyum.Autogenesis.modQuotientWitnessV4")?;
    let helper = d.exact(FIB_GCD_ITERATION)?;
    let gcd_comm = d.exact(CLEAN_GCD_COMM)?;
    let nat = d.nat_ty();
    let n_fv = d.fresh();
    let n = d.kernel.fvar(n_fv);
    let zero_branch = fib_gcd_step_zero_branch(&mut d, n);
    let closed_zero = d.lam(n_fv, nat, zero_branch);
    let zero_type = d
        .kernel
        .infer(closed_zero)
        .map_err(|error| format!("zero step branch inference failed: {error:?}"))?;
    let predecessor_fv = d.fresh();
    let predecessor = d.kernel.fvar(predecessor_fv);
    let successor_branch =
        fib_gcd_step_successor_branch(&mut d, n, predecessor, quotient, helper, gcd_comm);
    let closed_successor = d.lam(predecessor_fv, nat, successor_branch);
    let closed_successor = d.lam(n_fv, nat, closed_successor);
    let successor_type = d
        .kernel
        .infer(closed_successor)
        .map_err(|error| format!("successor step branch inference failed: {error:?}"))?;
    println!(
        "{}",
        serde_json::to_string_pretty(&json!({
            "schema_version":1,
            "kind":"axeyum-autogenesis-nat-fib-gcd-step-branch-diagnostic-v1",
            "state":"zero-and-successor-step-branch-types-inferred",
            "zero":{"type":d.kernel.render_lean(zero_type),"sha256":canonical_expression_sha256(d.kernel,zero_type)?},
            "successor":{"type":d.kernel.render_lean(successor_type),"sha256":canonical_expression_sha256(d.kernel,successor_type)?},
            "execution":{"complete_diagnostics":1,"helper_theorem_submissions":1,"zero_branch_inferences":1,"successor_branch_inferences":1,"step_proof_inferences":0,"target_theorem_submissions":0,"proof_values_rendered":0,"capsule_writes":0,"retries":0,"ledger_writes":0}
        }))
        .map_err(|error| error.to_string())?
    );
    Ok(())
}

#[allow(clippy::too_many_lines)]
fn run_fib_gcd_witness_elim_diagnostic(
    mut args: impl Iterator<Item = std::ffi::OsString>,
) -> Result<(), String> {
    let greatest_path = path(&mut args)?;
    let shift_path = path(&mut args)?;
    if args.next().is_some() {
        return Err("usage: nat_gcd_fib_add_self_exact \
             --target-native-fib-gcd-witness-elim-diagnostic \
             <gcd-greatest> <gcd-fib-add-self>"
            .to_owned());
    }
    let greatest = import_bound(&greatest_path, GCD_GREATEST_CAPSULE, "gcd-greatest")?;
    let shift = import_bound(&shift_path, GCD_FIB_SHIFT_CAPSULE, "gcd-fib-add-self")?;
    let composed = compose_checked_theorem_slice(shift.kernel(), greatest.kernel(), &[TARGET])
        .map_err(|error| format!("witness diagnostic composition declined: {error:?}"))?;
    verify_checked_theorem_composition(
        shift.kernel(),
        greatest.kernel(),
        composed.kernel(),
        composed.receipt(),
    )
    .map_err(|error| format!("witness diagnostic composition did not replay: {error:?}"))?;
    let mut kernel = composed.kernel().clone();
    declare_fib_gcd_quotient_iteration(&mut kernel)?;
    let mut d = Dev::new(&mut kernel)?;
    let quotient = d.exact("Axeyum.Autogenesis.modQuotientWitnessV4")?;
    let helper = d.exact(FIB_GCD_ITERATION)?;
    let gcd_comm = d.exact(CLEAN_GCD_COMM)?;
    let nat = d.nat_ty();
    let n_fv = d.fresh();
    let n = d.kernel.fvar(n_fv);
    let predecessor_fv = d.fresh();
    let predecessor = d.kernel.fvar(predecessor_fv);
    let m = d.succ(predecessor);
    let hm_ty = {
        let zero = d.zero();
        let one = d.succ(zero);
        d.le(one, m)
    };
    let remainder = d.modulo(n, m)?;
    let ih_ty = fib_gcd_statement(&mut d, remainder, m);
    let hm_fv = d.fresh();
    let hm = d.kernel.fvar(hm_fv);
    let ih_fv = d.fresh();
    let ih = d.kernel.fvar(ih_fv);
    let witness = d.lemma(quotient, &[m, n, hm]);
    let parts = build_fib_gcd_witness_elim(&mut d, m, n, remainder, ih, witness, helper, gcd_comm);
    let close_outer = |d: &mut Dev<'_>, value: ExprId, with_hm: bool, with_ih: bool| {
        let value = if with_ih {
            d.lam(ih_fv, ih_ty, value)
        } else {
            value
        };
        let value = if with_hm {
            d.lam(hm_fv, hm_ty, value)
        } else {
            value
        };
        let value = d.lam(predecessor_fv, nat, value);
        d.lam(n_fv, nat, value)
    };
    let left = close_outer(&mut d, parts.left_to_mr, false, true);
    let left_ty = d
        .kernel
        .infer(left)
        .map_err(|error| format!("ih-gcd-comm stage inference failed: {error:?}"))?;
    let mr_to_sum = d.lam(parts.q_fv, nat, parts.mr_to_sum);
    let mr_to_sum = close_outer(&mut d, mr_to_sum, false, false);
    let mr_to_sum_ty = d
        .kernel
        .infer(mr_to_sum)
        .map_err(|error| format!("quotient-iteration stage inference failed: {error:?}"))?;
    let sum_to_n = d.lam(parts.equation_fv, parts.equation_ty, parts.sum_to_n);
    let sum_to_n = d.lam(parts.q_fv, nat, sum_to_n);
    let sum_to_n = close_outer(&mut d, sum_to_n, false, false);
    let sum_to_n_ty = d
        .kernel
        .infer(sum_to_n)
        .map_err(|error| format!("quotient-congruence stage inference failed: {error:?}"))?;
    let body = d.lam(parts.equation_fv, parts.equation_ty, parts.body);
    let body = d.lam(parts.q_fv, nat, body);
    let body = close_outer(&mut d, body, false, true);
    let body_ty = d
        .kernel
        .infer(body)
        .map_err(|error| format!("combined-chain stage inference failed: {error:?}"))?;
    let minor = close_outer(&mut d, parts.minor, false, true);
    let minor_ty = d
        .kernel
        .infer(minor)
        .map_err(|error| format!("exists-minor stage inference failed: {error:?}"))?;
    let result = close_outer(&mut d, parts.result, true, true);
    let result_ty = d
        .kernel
        .infer(result)
        .map_err(|error| format!("exists-rec stage inference failed: {error:?}"))?;
    let stages = [
        ("ih_gcd_comm", left_ty),
        ("quotient_iteration", mr_to_sum_ty),
        ("quotient_congruence", sum_to_n_ty),
        ("combined_chain", body_ty),
        ("exists_minor", minor_ty),
        ("exists_rec", result_ty),
    ]
    .into_iter()
    .map(|(name, ty)| {
        Ok(json!({
            "name":name,
            "type":d.kernel.render_lean(ty),
            "sha256":canonical_expression_sha256(d.kernel,ty)?
        }))
    })
    .collect::<Result<Vec<_>, String>>()?;
    println!(
        "{}",
        serde_json::to_string_pretty(&json!({
            "schema_version":1,
            "kind":"axeyum-autogenesis-nat-fib-gcd-witness-elim-diagnostic-v1",
            "state":"all-six-closed-witness-elimination-stages-inferred",
            "stages":stages,
            "execution":{"complete_diagnostics":1,"helper_theorem_submissions":1,"ordered_stage_inferences":6,"target_theorem_submissions":0,"proof_values_rendered":0,"capsule_writes":0,"retries":0,"ledger_writes":0}
        }))
        .map_err(|error| error.to_string())?
    );
    Ok(())
}

#[allow(clippy::too_many_lines)]
fn run_fib_gcd_exists_rec_prefix_diagnostic(
    mut args: impl Iterator<Item = std::ffi::OsString>,
) -> Result<(), String> {
    let greatest_path = path(&mut args)?;
    let shift_path = path(&mut args)?;
    if args.next().is_some() {
        return Err("usage: nat_gcd_fib_add_self_exact \
             --target-native-fib-gcd-exists-rec-prefix-diagnostic \
             <gcd-greatest> <gcd-fib-add-self>"
            .to_owned());
    }
    let greatest = import_bound(&greatest_path, GCD_GREATEST_CAPSULE, "gcd-greatest")?;
    let shift = import_bound(&shift_path, GCD_FIB_SHIFT_CAPSULE, "gcd-fib-add-self")?;
    let composed = compose_checked_theorem_slice(shift.kernel(), greatest.kernel(), &[TARGET])
        .map_err(|error| format!("Exists.rec diagnostic composition declined: {error:?}"))?;
    verify_checked_theorem_composition(
        shift.kernel(),
        greatest.kernel(),
        composed.kernel(),
        composed.receipt(),
    )
    .map_err(|error| format!("Exists.rec diagnostic composition did not replay: {error:?}"))?;
    let mut kernel = composed.kernel().clone();
    declare_fib_gcd_quotient_iteration(&mut kernel)?;
    let mut d = Dev::new(&mut kernel)?;
    let quotient = d.exact("Axeyum.Autogenesis.modQuotientWitnessV4")?;
    let helper = d.exact(FIB_GCD_ITERATION)?;
    let gcd_comm = d.exact(CLEAN_GCD_COMM)?;
    let nat = d.nat_ty();
    let n_fv = d.fresh();
    let n = d.kernel.fvar(n_fv);
    let predecessor_fv = d.fresh();
    let predecessor = d.kernel.fvar(predecessor_fv);
    let m = d.succ(predecessor);
    let hm_ty = {
        let zero = d.zero();
        let one = d.succ(zero);
        d.le(one, m)
    };
    let remainder = d.modulo(n, m)?;
    let ih_ty = fib_gcd_statement(&mut d, remainder, m);
    let hm_fv = d.fresh();
    let hm = d.kernel.fvar(hm_fv);
    let ih_fv = d.fresh();
    let ih = d.kernel.fvar(ih_fv);
    let witness = d.lemma(quotient, &[m, n, hm]);
    let parts = build_fib_gcd_witness_elim(&mut d, m, n, remainder, ih, witness, helper, gcd_comm);
    let close = |d: &mut Dev<'_>, value: ExprId, with_hm: bool, with_ih: bool| {
        let value = if with_ih {
            d.lam(ih_fv, ih_ty, value)
        } else {
            value
        };
        let value = if with_hm {
            d.lam(hm_fv, hm_ty, value)
        } else {
            value
        };
        let value = d.lam(predecessor_fv, nat, value);
        d.lam(n_fv, nat, value)
    };
    let prefix_nat = d.apply(parts.rec, &[parts.nat]);
    let nat_type = d
        .kernel
        .infer(prefix_nat)
        .map_err(|error| format!("Exists.rec Nat prefix inference failed: {error:?}"))?;
    let prefix_predicate = d.apply(prefix_nat, &[parts.predicate]);
    let closed_predicate = close(&mut d, prefix_predicate, false, false);
    let predicate_type = d
        .kernel
        .infer(closed_predicate)
        .map_err(|error| format!("Exists.rec predicate prefix inference failed: {error:?}"))?;
    let prefix_motive = d.apply(prefix_predicate, &[parts.motive]);
    let closed_motive = close(&mut d, prefix_motive, false, false);
    let motive_type = d
        .kernel
        .infer(closed_motive)
        .map_err(|error| format!("Exists.rec motive prefix inference failed: {error:?}"))?;
    let prefix_minor = d.apply(prefix_motive, &[parts.minor]);
    let closed_minor = close(&mut d, prefix_minor, false, true);
    let minor_type = d
        .kernel
        .infer(closed_minor)
        .map_err(|error| format!("Exists.rec minor prefix inference failed: {error:?}"))?;
    let prefix_witness = d.apply(prefix_minor, &[parts.witness]);
    let closed_witness = close(&mut d, prefix_witness, true, true);
    let witness_type = d
        .kernel
        .infer(closed_witness)
        .map_err(|error| format!("Exists.rec witness prefix inference failed: {error:?}"))?;
    let prefixes = [
        ("Nat", nat_type),
        ("predicate", predicate_type),
        ("motive", motive_type),
        ("minor", minor_type),
        ("witness", witness_type),
    ]
    .into_iter()
    .map(|(name, ty)| {
        Ok(json!({"name":name,"type":d.kernel.render_lean(ty),"sha256":canonical_expression_sha256(d.kernel,ty)?}))
    })
    .collect::<Result<Vec<_>, String>>()?;
    println!(
        "{}",
        serde_json::to_string_pretty(&json!({
            "schema_version":1,
            "kind":"axeyum-autogenesis-nat-fib-gcd-exists-rec-prefix-diagnostic-v1",
            "state":"all-five-exists-rec-prefixes-inferred",
            "prefixes":prefixes,
            "execution":{"complete_diagnostics":1,"helper_theorem_submissions":1,"prefix_inferences":5,"target_theorem_submissions":0,"proof_values_rendered":0,"capsule_writes":0,"retries":0,"ledger_writes":0}
        }))
        .map_err(|error| error.to_string())?
    );
    Ok(())
}

fn fib_gcd_iteration_statement(d: &mut Dev<'_>, m: ExprId, r: ExprId, q: ExprId) -> ExprId {
    let fib_m = d.fib(m);
    let product = d.mul(m, q);
    let index = d.add(product, r);
    let fib_index = d.fib(index);
    let fib_r = d.fib(r);
    let left = d.gcd(fib_m, fib_index);
    let right = d.gcd(fib_m, fib_r);
    d.eq(left, right)
}

#[allow(clippy::too_many_lines)]
fn declare_fib_gcd_quotient_iteration(kernel: &mut Kernel) -> Result<NameId, String> {
    if optional_name(kernel, FIB_GCD_ITERATION)?.is_some() {
        return Err("Fibonacci quotient-iteration helper unexpectedly exists".to_owned());
    }
    let (target, ty, proof) = build_fib_gcd_quotient_iteration(kernel)?;
    kernel
        .add_declaration(Declaration::Theorem {
            name: target,
            uparams: vec![],
            ty,
            value: proof,
        })
        .map_err(|error| format!("Fibonacci quotient iteration rejected: {error:?}"))?;
    Ok(target)
}

#[allow(clippy::too_many_lines)]
fn build_fib_gcd_quotient_iteration(
    kernel: &mut Kernel,
) -> Result<(NameId, ExprId, ExprId), String> {
    let target = nested_name(
        kernel,
        &["Axeyum", "Autogenesis", "fibGcdQuotientIterationV1"],
    );
    let mut d = Dev::new(kernel)?;
    let add_zero = d.exact("Nat.zero_add")?;
    let add_assoc = d.exact("Nat.add_assoc")?;
    let add_comm = d.exact("Nat.add_comm")?;
    let mul_succ = d.exact("Nat.mul_succ")?;
    let shift = d.exact(TARGET)?;
    let nat = d.nat_ty();
    let m_fv = d.fresh();
    let m = d.kernel.fvar(m_fv);
    let r_fv = d.fresh();
    let r = d.kernel.fvar(r_fv);
    let q_fv = d.fresh();
    let q = d.kernel.fvar(q_fv);
    let proof = d.induct(
        &|d, candidate| fib_gcd_iteration_statement(d, m, r, candidate),
        &|d| {
            let zero = d.zero();
            let source = d.add(zero, r);
            let equality = d.lemma(add_zero, &[r]);
            d.congr(source, r, equality, &|d, index| {
                let fib_m = d.fib(m);
                let fib_index = d.fib(index);
                d.gcd(fib_m, fib_index)
            })
        },
        &|d, predecessor, ih| {
            let successor = d.succ(predecessor);
            let product = d.mul(m, predecessor);
            let source_product = d.mul(m, successor);
            let source = d.add(source_product, r);
            let product_plus_m = d.add(product, m);
            let first_target = d.add(product_plus_m, r);
            let mul_step = d.lemma(mul_succ, &[m, predecessor]);
            let first = d.congr(source_product, product_plus_m, mul_step, &|d, value| {
                d.add(value, r)
            });
            let m_plus_r = d.add(m, r);
            let middle_one = d.add(product, m_plus_r);
            let second = d.lemma(add_assoc, &[product, m, r]);
            let r_plus_m = d.add(r, m);
            let swapped = d.lemma(add_comm, &[m, r]);
            let third = d.congr(m_plus_r, r_plus_m, swapped, &|d, value| {
                d.add(product, value)
            });
            let product_plus_r = d.add(product, r);
            let target = d.add(product_plus_r, m);
            let associated = d.lemma(add_assoc, &[product, r, m]);
            let product_plus_r_plus_m = d.add(product, r_plus_m);
            let fourth = d.symm(target, product_plus_r_plus_m, associated);
            let first_two = d.trans(source, first_target, middle_one, first, second);
            let first_three = d.trans(source, middle_one, product_plus_r_plus_m, first_two, third);
            let index_equality =
                d.trans(source, product_plus_r_plus_m, target, first_three, fourth);
            let normalized = d.congr(source, target, index_equality, &|d, index| {
                let fib_m = d.fib(m);
                let fib_index = d.fib(index);
                d.gcd(fib_m, fib_index)
            });
            let shifted = d.add(product, r);
            let shift_proof = d.lemma(shift, &[m, shifted]);
            let source_gcd = {
                let fib_m = d.fib(m);
                let fib_source = d.fib(source);
                d.gcd(fib_m, fib_source)
            };
            let target_gcd = {
                let fib_m = d.fib(m);
                let fib_target = d.fib(target);
                d.gcd(fib_m, fib_target)
            };
            let shifted_gcd = {
                let fib_m = d.fib(m);
                let fib_shifted = d.fib(shifted);
                d.gcd(fib_m, fib_shifted)
            };
            let through_shift =
                d.trans(source_gcd, target_gcd, shifted_gcd, normalized, shift_proof);
            let final_gcd = {
                let fib_m = d.fib(m);
                let fib_r = d.fib(r);
                d.gcd(fib_m, fib_r)
            };
            d.trans(source_gcd, shifted_gcd, final_gcd, through_shift, ih)
        },
        q,
    );
    let proof = d.lam(q_fv, nat, proof);
    let proof = d.lam(r_fv, nat, proof);
    let proof = d.lam(m_fv, nat, proof);
    let ty = fib_gcd_iteration_statement(&mut d, m, r, q);
    let ty = d.pi(q_fv, nat, ty);
    let ty = d.pi(r_fv, nat, ty);
    let ty = d.pi(m_fv, nat, ty);
    Ok((target, ty, proof))
}

fn fib_gcd_statement(d: &mut Dev<'_>, m: ExprId, n: ExprId) -> ExprId {
    let gcd_indices = d.gcd(m, n);
    let left = d.fib(gcd_indices);
    let fib_m = d.fib(m);
    let fib_n = d.fib(n);
    let right = d.gcd(fib_m, fib_n);
    d.eq(left, right)
}

fn declare_fib_gcd(kernel: &mut Kernel) -> Result<NameId, String> {
    if optional_name(kernel, FIB_GCD_TARGET)?.is_some() {
        return Err("Nat.fib_gcd unexpectedly already exists".to_owned());
    }
    let (target, ty, proof) = build_fib_gcd(kernel)?;
    kernel
        .add_declaration(Declaration::Theorem {
            name: target,
            uparams: vec![],
            ty,
            value: proof,
        })
        .map_err(|error| format!("exact Nat.fib_gcd rejected: {error:?}"))?;
    Ok(target)
}

fn build_fib_gcd(kernel: &mut Kernel) -> Result<(NameId, ExprId, ExprId), String> {
    let target = nested_name(kernel, &["Nat", "fib_gcd"]);
    let mut d = Dev::new(kernel)?;
    let gcd_induction = d.exact("Nat.gcd.induction")?;
    let quotient = d.exact("Axeyum.Autogenesis.modQuotientWitnessV4")?;
    let helper = d.exact(FIB_GCD_ITERATION)?;
    let gcd_comm = d.exact(CLEAN_GCD_COMM)?;
    let nat = d.nat_ty();
    let m_fv = d.fresh();
    let m = d.kernel.fvar(m_fv);
    let n_fv = d.fresh();
    let n = d.kernel.fvar(n_fv);
    let motive = d.two_lambdas(nat, nat, &|d, left, right| {
        fib_gcd_statement(d, left, right)
    });
    let base_n_fv = d.fresh();
    let base_n = d.kernel.fvar(base_n_fv);
    let fib_base_n = d.fib(base_n);
    let base = d.refl(fib_base_n);
    let base = d.lam(base_n_fv, nat, base);
    let step = fib_gcd_step(&mut d, quotient, helper, gcd_comm)?;
    let induction = d.kernel.const_(gcd_induction, vec![]);
    let proof = d.apply(induction, &[motive, m, n, base, step]);
    let proof = d.lam(n_fv, nat, proof);
    let proof = d.lam(m_fv, nat, proof);
    let ty = fib_gcd_statement(&mut d, m, n);
    let ty = d.pi(n_fv, nat, ty);
    let ty = d.pi(m_fv, nat, ty);
    Ok((target, ty, proof))
}

fn fib_gcd_step(
    d: &mut Dev<'_>,
    quotient: NameId,
    helper: NameId,
    gcd_comm: NameId,
) -> Result<ExprId, String> {
    let nat = d.nat_ty();
    let m_fv = d.fresh();
    let m = d.kernel.fvar(m_fv);
    let n_fv = d.fresh();
    let n = d.kernel.fvar(n_fv);
    let hm_ty = {
        let zero = d.zero();
        let one = d.succ(zero);
        d.le(one, m)
    };
    let remainder = d.modulo(n, m)?;
    let ih_ty = fib_gcd_statement(d, remainder, m);
    let hm_fv = d.fresh();
    let hm = d.kernel.fvar(hm_fv);
    let ih_fv = d.fresh();
    let ih = d.kernel.fvar(ih_fv);
    let body = fib_gcd_step_by_cases(d, m, n, quotient, helper, gcd_comm);
    let body = d.apply(body, &[hm, ih]);
    let body = d.lam(ih_fv, ih_ty, body);
    let body = d.lam(hm_fv, hm_ty, body);
    let body = d.lam(n_fv, nat, body);
    Ok(d.lam(m_fv, nat, body))
}

fn fib_gcd_step_by_cases(
    d: &mut Dev<'_>,
    m: ExprId,
    n: ExprId,
    quotient: NameId,
    helper: NameId,
    gcd_comm: NameId,
) -> ExprId {
    let branch_motive = |d: &mut Dev<'_>, candidate: ExprId| -> ExprId {
        let hm_ty = {
            let zero = d.zero();
            let one = d.succ(zero);
            d.le(one, candidate)
        };
        let remainder = d.modulo(n, candidate).expect("Nat.mod must exist");
        let ih_ty = fib_gcd_statement(d, remainder, candidate);
        let result = fib_gcd_statement(d, candidate, n);
        let after_ih = d.arrow(ih_ty, result);
        d.arrow(hm_ty, after_ih)
    };
    d.induct(
        &branch_motive,
        &|d| fib_gcd_step_zero_branch(d, n),
        &|d, predecessor, _case_ih| {
            fib_gcd_step_successor_branch(d, n, predecessor, quotient, helper, gcd_comm)
        },
        m,
    )
}

fn fib_gcd_step_zero_branch(d: &mut Dev<'_>, n: ExprId) -> ExprId {
    let zero = d.zero();
    let hm_ty = {
        let one = d.succ(zero);
        d.le(one, zero)
    };
    let remainder = d.modulo(n, zero).expect("Nat.mod must exist");
    let ih_ty = fib_gcd_statement(d, remainder, zero);
    let hm_fv = d.fresh();
    let ih_fv = d.fresh();
    let fib_n = d.fib(n);
    let proof = d.refl(fib_n);
    let proof = d.lam(ih_fv, ih_ty, proof);
    d.lam(hm_fv, hm_ty, proof)
}

fn fib_gcd_step_successor_branch(
    d: &mut Dev<'_>,
    n: ExprId,
    predecessor: ExprId,
    quotient: NameId,
    helper: NameId,
    gcd_comm: NameId,
) -> ExprId {
    let sm = d.succ(predecessor);
    let hm_ty = {
        let zero = d.zero();
        let one = d.succ(zero);
        d.le(one, sm)
    };
    let remainder = d.modulo(n, sm).expect("Nat.mod must exist");
    let ih_ty = fib_gcd_statement(d, remainder, sm);
    let hm_fv = d.fresh();
    let hm = d.kernel.fvar(hm_fv);
    let ih_fv = d.fresh();
    let ih = d.kernel.fvar(ih_fv);
    let witness = d.lemma(quotient, &[sm, n, hm]);
    let result = fib_gcd_witness_elim(d, sm, n, remainder, ih, witness, helper, gcd_comm);
    let result = d.lam(ih_fv, ih_ty, result);
    d.lam(hm_fv, hm_ty, result)
}

#[allow(clippy::too_many_arguments)]
fn fib_gcd_witness_elim(
    d: &mut Dev<'_>,
    m: ExprId,
    n: ExprId,
    remainder: ExprId,
    ih: ExprId,
    witness: ExprId,
    helper: NameId,
    gcd_comm: NameId,
) -> ExprId {
    build_fib_gcd_witness_elim(d, m, n, remainder, ih, witness, helper, gcd_comm).result
}

struct FibGcdWitnessElimParts {
    nat: ExprId,
    rec: ExprId,
    predicate: ExprId,
    motive: ExprId,
    witness: ExprId,
    q_fv: u64,
    equation_fv: u64,
    equation_ty: ExprId,
    left_to_mr: ExprId,
    mr_to_sum: ExprId,
    sum_to_n: ExprId,
    body: ExprId,
    minor: ExprId,
    result: ExprId,
}

#[allow(clippy::too_many_arguments)]
fn build_fib_gcd_witness_elim(
    d: &mut Dev<'_>,
    m: ExprId,
    n: ExprId,
    remainder: ExprId,
    ih: ExprId,
    witness: ExprId,
    helper: NameId,
    gcd_comm: NameId,
) -> FibGcdWitnessElimParts {
    let nat = d.nat_ty();
    let result_ty = fib_gcd_statement(d, m, n);
    let predicate = {
        let q_fv = d.fresh();
        let q = d.kernel.fvar(q_fv);
        let product = d.mul(m, q);
        let sum = d.add(product, remainder);
        let equation = d.eq(sum, n);
        d.lam(q_fv, nat, equation)
    };
    let one = d.one_level();
    let exists = find_name(d.kernel, "Exists").expect("Exists must exist");
    let exists_head = d.kernel.const_(exists, vec![one]);
    let witness_ty = d.apply(exists_head, &[nat, predicate]);
    let proof_fv = d.fresh();
    let motive = d.lam(proof_fv, witness_ty, result_ty);
    let q_fv = d.fresh();
    let q = d.kernel.fvar(q_fv);
    let product = d.mul(m, q);
    let sum = d.add(product, remainder);
    let equation_ty = d.eq(sum, n);
    let equation_fv = d.fresh();
    let equation = d.kernel.fvar(equation_fv);
    let fib_r = d.fib(remainder);
    let fib_m = d.fib(m);
    let gcd_r_m = d.gcd(fib_r, fib_m);
    let gcd_m_r = d.gcd(fib_m, fib_r);
    let comm = d.lemma(gcd_comm, &[fib_r, fib_m]);
    let gcd_indices = d.gcd(remainder, m);
    let left = d.fib(gcd_indices);
    let left_to_mr = d.trans(left, gcd_r_m, gcd_m_r, ih, comm);
    let helper_proof = d.lemma(helper, &[m, remainder, q]);
    let fib_sum = d.fib(sum);
    let gcd_m_sum = d.gcd(fib_m, fib_sum);
    let mr_to_sum = d.symm(gcd_m_sum, gcd_m_r, helper_proof);
    let sum_to_n = d.congr(sum, n, equation, &|d, index| {
        let fib_m = d.fib(m);
        let fib_index = d.fib(index);
        d.gcd(fib_m, fib_index)
    });
    let fib_n = d.fib(n);
    let gcd_m_n = d.gcd(fib_m, fib_n);
    let mr_to_n = d.trans(gcd_m_r, gcd_m_sum, gcd_m_n, mr_to_sum, sum_to_n);
    let body = d.trans(left, gcd_m_r, gcd_m_n, left_to_mr, mr_to_n);
    let minor = d.lam(equation_fv, equation_ty, body);
    let minor = d.lam(q_fv, nat, minor);
    let rec = d.kernel.const_(d.exists_rec, vec![one]);
    let result = d.apply(rec, &[nat, predicate, motive, minor, witness]);
    FibGcdWitnessElimParts {
        nat,
        rec,
        predicate,
        motive,
        witness,
        q_fv,
        equation_fv,
        equation_ty,
        left_to_mr,
        mr_to_sum,
        sum_to_n,
        body,
        minor,
        result,
    }
}

#[allow(clippy::too_many_lines)]
fn run_target_native_goal_audit(
    mut args: impl Iterator<Item = std::ffi::OsString>,
) -> Result<(), String> {
    let r091_path = path(&mut args)?;
    let inputs = [
        (
            path(&mut args)?,
            CLEAN_ANTISYMM_CAPSULE,
            vec![CLEAN_ANTISYMM],
        ),
        (path(&mut args)?, CANCELLATION_CAPSULE, vec![CANCELLATION]),
        (path(&mut args)?, ADDITION_CAPSULE, vec![ADDITION]),
        (
            path(&mut args)?,
            "9ecf0b10d1390f880040790fb1845a11d7987b94c0d3a71acf4ad8dca0c5a304",
            vec![TARGET_GCD_DVD_LEFT, TARGET_GCD_DVD_RIGHT, TARGET_DVD_GCD],
        ),
        (
            path(&mut args)?,
            "e7933242c5caeb90a17bb7141656fe12a1c78780a83e82958c9ddd38ccd85d3f",
            vec![TARGET_FIB_COPRIME],
        ),
    ];
    if args.next().is_some() {
        return Err("usage: nat_gcd_fib_add_self_exact --target-native-goal-audit <r091> <official-clean-order> <cancellation> <addition> <gcd-divisibility> <target-native-coprimality>".to_owned());
    }
    let r091 = import_bound(&r091_path, R091_SHA256, "r091")?;
    let mut kernel = r091.kernel().clone();
    for (source_path, expected_sha256, roots) in inputs {
        let source = import_bound(&source_path, expected_sha256, roots[0])?;
        let completed = compose_checked_theorem_slice(source.kernel(), &kernel, &roots)
            .map_err(|error| format!("target-native goal audit setup declined: {error:?}"))?;
        verify_checked_theorem_composition(
            source.kernel(),
            &kernel,
            completed.kernel(),
            completed.receipt(),
        )
        .map_err(|error| format!("target-native goal audit setup did not replay: {error:?}"))?;
        kernel = completed.kernel().clone();
    }
    let goal_name = find_name(&kernel, GOAL_DEFINITION)?;
    let carrier = match kernel.environment().get(goal_name) {
        Some(Declaration::Definition { value, .. }) => *value,
        _ => return Err("r091 goal carrier is not a definition".to_owned()),
    };
    let constructed = {
        let mut d = Dev::new(&mut kernel)?;
        let nat = d.nat_ty();
        let m_fv = d.fresh();
        let m = d.kernel.fvar(m_fv);
        let n_fv = d.fresh();
        let n = d.kernel.fvar(n_fv);
        let body = statement(&mut d, m, n);
        let body = d.pi(n_fv, nat, body);
        d.pi(m_fv, nat, body)
    };
    let carrier_sha256 = canonical_expression_sha256(&kernel, carrier)?;
    let constructed_sha256 = canonical_expression_sha256(&kernel, constructed)?;
    let carrier_shape = canonical_kernel_type_shape_sha256(&kernel, carrier)?;
    let constructed_shape = canonical_kernel_type_shape_sha256(&kernel, constructed)?;
    let definitionally_equal = kernel.def_eq(carrier, constructed);
    println!(
        "{}",
        serde_json::to_string_pretty(&json!({
            "schema_version":1,
            "kind":"axeyum-autogenesis-target-native-exact-goal-audit",
            "state":"carrier-compared-to-independently-constructed-statement",
            "carrier":{"name":GOAL_DEFINITION,"canonical_expression_sha256":carrier_sha256,"kernel_type_shape_sha256":carrier_shape},
            "constructed":{"canonical_expression_sha256":constructed_sha256,"kernel_type_shape_sha256":constructed_shape},
            "definitionally_equal":definitionally_equal,
            "execution":{"complete_audits":1,"kernel_submissions":0,"exports":0,"retries":0},
            "rendered_material":{"proof_terms":0,"theorem_types":0,"theorem_values":0},
            "exact_target_submissions":0,
            "fact_status_changes":0,
            "evaluation_credit":0,
            "ledger_writes":0
        }))
        .map_err(|error| error.to_string())?
    );
    Ok(())
}

fn run_target_native_gcd_surface_audit(
    mut args: impl Iterator<Item = std::ffi::OsString>,
) -> Result<(), String> {
    let r091_path = path(&mut args)?;
    let clean_path = path(&mut args)?;
    let cancellation_path = path(&mut args)?;
    let addition_path = path(&mut args)?;
    let simple_path = path(&mut args)?;
    if args.next().is_some() {
        return Err("usage: nat_gcd_fib_add_self_exact --target-native-gcd-surface-audit <r091> <official-clean-order> <cancellation> <addition> <simple-support>".to_owned());
    }
    let r091 = import_bound(&r091_path, R091_SHA256, "r091")?;
    let clean = import_bound(&clean_path, CLEAN_ANTISYMM_CAPSULE, CLEAN_ANTISYMM)?;
    let cancellation = import_bound(&cancellation_path, CANCELLATION_CAPSULE, CANCELLATION)?;
    let addition = import_bound(&addition_path, ADDITION_CAPSULE, ADDITION)?;
    let simple = import_bound(
        &simple_path,
        "ce0db76dc93690e1e345627ce555e9f53b532a396643581fe554a7bcdce18322",
        "simple-support",
    )?;
    let mut target = r091.kernel().clone();
    let mut setup = Vec::new();
    for (roots, source) in [
        (&[CLEAN_ANTISYMM][..], clean.kernel()),
        (&[CANCELLATION][..], cancellation.kernel()),
        (&[ADDITION][..], addition.kernel()),
        (
            &[TARGET_DVD_ADD, TARGET_EQ_ONE_OF_DVD_ONE][..],
            simple.kernel(),
        ),
    ] {
        let completed = compose_checked_theorem_slice(source, &target, roots)
            .map_err(|error| format!("GCD audit setup composition declined: {error:?}"))?;
        verify_checked_theorem_composition(
            source,
            &target,
            completed.kernel(),
            completed.receipt(),
        )
        .map_err(|error| format!("GCD audit setup composition did not replay: {error:?}"))?;
        setup.push(json!({"roots": roots, "receipt_sha256": completed.receipt().receipt_sha256}));
        target = completed.kernel().clone();
    }
    let candidates = GCD_SUPPORT_CANDIDATES
        .iter()
        .map(|&candidate| {
            let row = optional_name(&target, candidate)?
                .map(|name| {
                    let declaration = target.environment().get(name)
                        .ok_or_else(|| format!("candidate disappeared: {candidate}"))?;
                    let footprint = if matches!(declaration, Declaration::Theorem { .. }) {
                        names(&target, &target.axiom_footprint(name))
                    } else { Vec::new() };
                    Ok::<_, String>(json!({"kind": declaration_kind(declaration), "declaration_sha256": canonical_declaration_sha256(&target, name)?, "axiom_footprint": footprint}))
                }).transpose()?;
            Ok::<_, String>(json!({"name": candidate, "target": row}))
        })
        .collect::<Result<Vec<_>, _>>()?;
    println!("{}", serde_json::to_string_pretty(&json!({
        "schema_version": 1,
        "kind": "axeyum-autogenesis-target-native-gcd-divisibility-surface-audit",
        "setup_compositions": setup,
        "candidates": candidates,
        "execution": {"reads_per_input": 1, "complete_audits": 1, "kernel_submissions": 0, "exports": 0, "retries": 0},
        "rendered_material": {"proof_terms": 0, "theorem_types": 0, "theorem_values": 0},
        "exact_target_submissions": 0,
        "fact_status_changes": 0,
        "evaluation_credit": 0,
        "ledger_writes": 0,
    })).map_err(|error| error.to_string())?);
    Ok(())
}

fn run_target_native_simple_support_capsule(
    mut args: impl Iterator<Item = std::ffi::OsString>,
) -> Result<(), String> {
    let r091_path = path(&mut args)?;
    let clean_path = path(&mut args)?;
    let cancellation_path = path(&mut args)?;
    let addition_path = path(&mut args)?;
    let output_path = path(&mut args)?;
    if args.next().is_some() || output_path.exists() {
        return Err("usage: nat_gcd_fib_add_self_exact --target-native-simple-support-capsule <r091> <official-clean-order> <cancellation> <addition> <output>".to_owned());
    }
    let r091 = import_bound(&r091_path, R091_SHA256, "r091")?;
    let clean = import_bound(&clean_path, CLEAN_ANTISYMM_CAPSULE, CLEAN_ANTISYMM)?;
    let cancellation = import_bound(&cancellation_path, CANCELLATION_CAPSULE, CANCELLATION)?;
    let addition = import_bound(&addition_path, ADDITION_CAPSULE, ADDITION)?;
    let mut kernel = r091.kernel().clone();
    let mut setup_receipts = Vec::new();
    for (root, source) in [
        (CLEAN_ANTISYMM, clean.kernel()),
        (CANCELLATION, cancellation.kernel()),
        (ADDITION, addition.kernel()),
    ] {
        let completed = compose_checked_theorem_slice(source, &kernel, &[root])
            .map_err(|error| format!("{root} support setup composition declined: {error:?}"))?;
        verify_checked_theorem_composition(
            source,
            &kernel,
            completed.kernel(),
            completed.receipt(),
        )
        .map_err(|error| format!("{root} support setup composition did not replay: {error:?}"))?;
        setup_receipts
            .push(json!({"root": root, "receipt_sha256": completed.receipt().receipt_sha256}));
        kernel = completed.kernel().clone();
    }
    let dvd_add = declare_target_native_dvd_add(&mut kernel)?;
    require_empty(&kernel, dvd_add, TARGET_DVD_ADD)?;
    let eq_one = declare_target_native_eq_one_of_dvd_one(&mut kernel)?;
    require_empty(&kernel, eq_one, TARGET_EQ_ONE_OF_DVD_ONE)?;
    let expected = [evidence(&kernel, dvd_add)?, evidence(&kernel, eq_one)?];
    let bytes = kernel
        .render_lean4export_ndjson_roots(&Lean4ExportMetadata::axeyum("4.30.0"), &[dvd_add, eq_one])
        .map_err(|error| format!("simple support capsule export failed: {error}"))?;
    for pass in 1..=2 {
        let replay = import_ndjson(Cursor::new(bytes.as_bytes()), ImportLimits::default())
            .map_err(|error| format!("simple support capsule import {pass} failed: {error:?}"))?;
        for (name, evidence_expected) in [
            (TARGET_DVD_ADD, &expected[0]),
            (TARGET_EQ_ONE_OF_DVD_ONE, &expected[1]),
        ] {
            let theorem = find_name(replay.kernel(), name)?;
            if evidence(replay.kernel(), theorem)? != *evidence_expected {
                return Err(format!(
                    "simple support capsule import {pass} changed {name}"
                ));
            }
        }
    }
    fs::write(&output_path, &bytes)
        .map_err(|error| format!("simple support capsule write failed: {error}"))?;
    println!(
        "{}",
        serde_json::to_string_pretty(&json!({
            "schema_version": 1,
            "kind": "axeyum-autogenesis-target-native-simple-coprime-support-capsule",
            "state": "two-simple-supports-reconstructed-empty-footprint-roundtrip-checked",
            "setup_compositions": setup_receipts,
            "supports": expected,
            "capsule": {"bytes": bytes.len(), "sha256": hex_sha256(bytes.as_bytes()), "fresh_imports": 2},
            "execution": {"support_submissions": 2, "exports": 1, "fresh_imports": 2, "retries": 0},
            "rendered_material": {"proof_terms": 0, "theorem_types": 0, "theorem_values": 0},
            "exact_coprime_submissions": 0,
            "exact_target_submissions": 0,
            "fact_status_changes": 0,
            "evaluation_credit": 0,
            "ledger_writes": 0,
        }))
        .map_err(|error| error.to_string())?
    );
    Ok(())
}

#[allow(clippy::too_many_lines)]
fn run_target_native_coprime_audit(
    mut args: impl Iterator<Item = std::ffi::OsString>,
) -> Result<(), String> {
    let r091_path = path(&mut args)?;
    let clean_path = path(&mut args)?;
    let cancellation_path = path(&mut args)?;
    let addition_path = path(&mut args)?;
    let coprime_path = path(&mut args)?;
    if args.next().is_some() {
        return Err("usage: nat_gcd_fib_add_self_exact --target-native-coprime-audit <r091> <official-clean-order> <cancellation> <addition> <coprimality>".to_owned());
    }
    let r091 = import_bound(&r091_path, R091_SHA256, "r091")?;
    let clean = import_bound(&clean_path, CLEAN_ANTISYMM_CAPSULE, CLEAN_ANTISYMM)?;
    let cancellation = import_bound(&cancellation_path, CANCELLATION_CAPSULE, CANCELLATION)?;
    let addition = import_bound(&addition_path, ADDITION_CAPSULE, ADDITION)?;
    let coprime = import_bound(&coprime_path, COPRIME_CAPSULE, COPRIME)?;
    let mut target = r091.kernel().clone();
    let mut setup = Vec::new();
    for (root, source) in [
        (CLEAN_ANTISYMM, clean.kernel()),
        (CANCELLATION, cancellation.kernel()),
        (ADDITION, addition.kernel()),
    ] {
        let completed = compose_checked_theorem_slice(source, &target, &[root])
            .map_err(|error| format!("{root} audit setup composition declined: {error:?}"))?;
        verify_checked_theorem_composition(
            source,
            &target,
            completed.kernel(),
            completed.receipt(),
        )
        .map_err(|error| format!("{root} audit setup composition did not replay: {error:?}"))?;
        setup.push(json!({"root": root, "receipt_sha256": completed.receipt().receipt_sha256}));
        target = completed.kernel().clone();
    }
    let source = coprime.kernel();
    let rows = COPRIME_DIRECT_PREMISES
        .iter()
        .map(|&premise| {
            let source_name = find_name(source, premise)?;
            if !matches!(source.environment().get(source_name), Some(Declaration::Theorem { .. })) {
                return Err(format!("source direct premise is not a theorem: {premise}"));
            }
            let source_shape =
                canonical_kernel_type_shape_sha256(source, theorem_type(source, source_name)?)?;
            let source_hash = canonical_declaration_sha256(source, source_name)?;
            let target_same_name = optional_name(&target, premise)?
                .map(|target_name| {
                    let compatibility = checked_reused_declaration_compatibility(source, &target, premise)
                        .map(|receipt| receipt.compatibility.as_str().to_owned())
                        .map_err(|error| format!("declined:{error:?}"));
                    Ok::<_, String>(json!({
                        "declaration_sha256": canonical_declaration_sha256(&target, target_name)?,
                        "type_shape_sha256": canonical_kernel_type_shape_sha256(&target, theorem_type(&target, target_name)?)?,
                        "axiom_footprint": names(&target, &target.axiom_footprint(target_name)),
                        "compatibility": compatibility.unwrap_or_else(|error| error),
                    }))
                })
                .transpose()?;
            let mut equivalents = target
                .environment()
                .iter()
                .filter_map(|(&candidate, declaration)| {
                    matches!(declaration, Declaration::Theorem { .. }).then_some(candidate)
                })
                .filter_map(|candidate| {
                    let ty = theorem_type(&target, candidate).ok()?;
                    let shape = canonical_kernel_type_shape_sha256(&target, ty).ok()?;
                    (shape == source_shape && target.axiom_footprint(candidate).is_empty())
                        .then_some(candidate)
                })
                .map(|candidate| {
                    Ok::<_, String>(json!({
                        "name": target.display_name(candidate).to_string(),
                        "declaration_sha256": canonical_declaration_sha256(&target, candidate)?,
                    }))
                })
                .collect::<Result<Vec<_>, _>>()?;
            equivalents.sort_by_key(|row| row["name"].as_str().unwrap_or_default().to_owned());
            Ok::<_, String>(json!({
                "source_name": premise,
                "source_declaration_sha256": source_hash,
                "source_type_shape_sha256": source_shape,
                "source_axiom_footprint": names(source, &source.axiom_footprint(source_name)),
                "target_same_name": target_same_name,
                "target_native_exact_type_shape_equivalents": equivalents,
            }))
        })
        .collect::<Result<Vec<_>, _>>()?;
    let candidates = COPRIME_SUPPORT_CANDIDATES
        .iter()
        .map(|&candidate| {
            let row = optional_name(&target, candidate)?
                .map(|name| {
                    let declaration = target
                        .environment()
                        .get(name)
                        .ok_or_else(|| format!("candidate disappeared: {candidate}"))?;
                    let footprint = if matches!(declaration, Declaration::Theorem { .. }) {
                        names(&target, &target.axiom_footprint(name))
                    } else {
                        Vec::new()
                    };
                    Ok::<_, String>(json!({
                        "kind": declaration_kind(declaration),
                        "declaration_sha256": canonical_declaration_sha256(&target, name)?,
                        "axiom_footprint": footprint,
                    }))
                })
                .transpose()?;
            Ok::<_, String>(json!({"name": candidate, "target": row}))
        })
        .collect::<Result<Vec<_>, _>>()?;
    println!(
        "{}",
        serde_json::to_string_pretty(&json!({
            "schema_version": 1,
            "kind": "axeyum-autogenesis-target-native-fibonacci-coprime-premise-audit",
            "source_target": COPRIME,
            "setup_compositions": setup,
            "direct_premises": rows,
            "support_candidates": candidates,
            "execution": {"reads_per_input": 1, "complete_audits": 1, "kernel_submissions": 0, "exports": 0, "retries": 0},
            "rendered_material": {"proof_terms": 0, "theorem_types": 0, "theorem_values": 0},
            "exact_target_submissions": 0,
            "fact_status_changes": 0,
            "evaluation_credit": 0,
            "ledger_writes": 0,
        }))
        .map_err(|error| error.to_string())?
    );
    Ok(())
}

#[allow(clippy::too_many_lines)]
fn run_coprime_carrier_audit(
    mut args: impl Iterator<Item = std::ffi::OsString>,
) -> Result<(), String> {
    let r091_path = path(&mut args)?;
    let clean_path = path(&mut args)?;
    let cancellation_path = path(&mut args)?;
    let addition_path = path(&mut args)?;
    let coprime_path = path(&mut args)?;
    let blocked_text = args
        .next()
        .ok_or_else(|| "missing blocked dependency".to_owned())?
        .into_string()
        .map_err(|_| "blocked dependency is not valid UTF-8".to_owned())?;
    if args.next().is_some() {
        return Err("usage: nat_gcd_fib_add_self_exact --coprime-carrier-audit <r091> <official-clean-order> <cancellation> <addition> <coprimality> <blocked-dependency>".to_owned());
    }
    let r091 = import_bound(&r091_path, R091_SHA256, "r091")?;
    let clean = import_bound(&clean_path, CLEAN_ANTISYMM_CAPSULE, CLEAN_ANTISYMM)?;
    let cancellation = import_bound(&cancellation_path, CANCELLATION_CAPSULE, CANCELLATION)?;
    let addition = import_bound(&addition_path, ADDITION_CAPSULE, ADDITION)?;
    let coprime = import_bound(&coprime_path, COPRIME_CAPSULE, COPRIME)?;
    let sources = [
        (CLEAN_ANTISYMM, clean.kernel()),
        (CANCELLATION, cancellation.kernel()),
        (ADDITION, addition.kernel()),
    ];
    let mut target = r091.kernel().clone();
    let mut receipts = Vec::new();
    for (root, source) in sources {
        let completed = compose_checked_theorem_slice(source, &target, &[root])
            .map_err(|error| format!("{root} audit setup composition declined: {error:?}"))?;
        verify_checked_theorem_composition(
            source,
            &target,
            completed.kernel(),
            completed.receipt(),
        )
        .map_err(|error| format!("{root} audit setup composition did not replay: {error:?}"))?;
        receipts.push(json!({
            "root": root,
            "receipt_sha256": completed.receipt().receipt_sha256,
        }));
        target = completed.kernel().clone();
    }
    let source = coprime.kernel();
    let root = find_name(source, COPRIME)?;
    let blocked = find_name(source, &blocked_text)?;
    let root_closure = source.declaration_dependency_closure(root);
    if !root_closure.contains(&blocked) {
        return Err(format!("{blocked_text} disappeared from {COPRIME} closure"));
    }
    let mut carriers = root_closure
        .iter()
        .copied()
        .filter_map(|candidate| {
            let closure = source.declaration_dependency_closure(candidate);
            (candidate == blocked || closure.contains(&blocked))
                .then_some((candidate, closure.len()))
        })
        .collect::<Vec<_>>();
    carriers.sort_by_key(|(name, closure_size)| {
        (*closure_size, source.display_name(*name).to_string())
    });
    let rows = carriers
        .into_iter()
        .map(|(name, closure_size)| {
            let rendered = source.display_name(name).to_string();
            let declaration = source
                .environment()
                .get(name)
                .ok_or_else(|| format!("source carrier disappeared: {rendered}"))?;
            let source_hash = canonical_declaration_sha256(source, name)?;
            let target_row = optional_name(&target, &rendered)?
                .map(|target_name| {
                    let target_hash = canonical_declaration_sha256(&target, target_name)?;
                    let compatibility = if target_hash == source_hash {
                        "exact-declaration".to_owned()
                    } else {
                        checked_reused_declaration_compatibility(source, &target, &rendered)
                            .map_or_else(
                                |error| format!("declined:{error:?}"),
                                |receipt| receipt.compatibility.as_str().to_owned(),
                            )
                    };
                    Ok::<_, String>(json!({"declaration_sha256": target_hash, "compatibility": compatibility}))
                })
                .transpose()?;
            let origins = sources
                .iter()
                .filter_map(|(root, kernel)| {
                    optional_name(kernel, &rendered)
                        .transpose()
                        .map(|result| result.map(|origin| (*root, kernel, origin)))
                })
                .collect::<Result<Vec<_>, _>>()?
                .into_iter()
                .map(|(root, kernel, origin)| {
                    Ok::<_, String>(json!({"root": root, "declaration_sha256": canonical_declaration_sha256(kernel, origin)?}))
                })
                .collect::<Result<Vec<_>, _>>()?;
            let footprint = if matches!(declaration, Declaration::Theorem { .. }) {
                names(source, &source.axiom_footprint(name))
            } else {
                Vec::new()
            };
            Ok::<_, String>(json!({
                "name": rendered,
                "kind": declaration_kind(declaration),
                "source_declaration_sha256": source_hash,
                "source_closure_size": closure_size,
                "source_axiom_footprint": footprint,
                "target": target_row,
                "introducing_capsules": origins,
            }))
        })
        .collect::<Result<Vec<_>, _>>()?;
    println!(
        "{}",
        serde_json::to_string_pretty(&json!({
            "schema_version": 1,
            "kind": "axeyum-autogenesis-nat-gcd-fib-add-self-coprime-carrier-audit",
            "source_root": COPRIME,
            "blocked_dependency": blocked_text,
            "setup_compositions": receipts,
            "root_closure_size": root_closure.len(),
            "carrier_count": rows.len(),
            "carriers_nearest_first": rows,
            "execution": {"reads_per_input": 1, "complete_audits": 1, "kernel_submissions": 0, "exports": 0, "retries": 0},
            "rendered_material": {"proof_terms": 0, "theorem_types": 0, "theorem_values": 0},
            "exact_target_submissions": 0,
            "fact_status_changes": 0,
            "evaluation_credit": 0,
            "ledger_writes": 0,
        }))
        .map_err(|error| error.to_string())?
    );
    Ok(())
}

#[allow(clippy::too_many_lines)]
fn run_official_clean_order_capsule(
    mut args: impl Iterator<Item = std::ffi::OsString>,
) -> Result<(), String> {
    let r091_path = path(&mut args)?;
    let cancellation_path = path(&mut args)?;
    let output_path = path(&mut args)?;
    if args.next().is_some() || output_path.exists() {
        return Err("usage: nat_gcd_fib_add_self_exact --official-clean-order-capsule <r091> <official-cancellation> <output>".to_owned());
    }
    let imported = import_bound(&r091_path, R091_SHA256, "r091")?;
    if !imported.report().axioms.is_empty() {
        return Err("r091 is not proof-isolated".to_owned());
    }
    let mut kernel = imported.kernel().clone();
    let cancellation = import_bound(&cancellation_path, CANCELLATION_CAPSULE, CANCELLATION)?;
    let mod_lt_reuse = checked_reused_declaration_compatibility(
        cancellation.kernel(),
        &kernel,
        CANCELLATION_BOOTSTRAP,
    )
    .map_err(|error| format!("Nat.mod_lt checked reuse declined: {error:?}"))?;
    if mod_lt_reuse.source_declaration_sha256 != mod_lt_reuse.target_declaration_sha256
        || mod_lt_reuse.compatibility != ReusedTypeCompatibility::KernelTypeShape
    {
        return Err("Nat.mod_lt checked reuse identity or type shape changed".to_owned());
    }
    let target_mod_lt = find_name(&kernel, CANCELLATION_BOOTSTRAP)?;
    require_empty(&kernel, target_mod_lt, CANCELLATION_BOOTSTRAP)?;
    let compatible = compose_checked_theorem_slice_with_target_leaves(
        cancellation.kernel(),
        &kernel,
        &[CANCELLATION],
        &[CANCELLATION_BOOTSTRAP],
    )
    .map_err(|error| format!("official cancellation compatibility declined: {error:?}"))?;
    verify_checked_theorem_composition_with_target_leaves(
        cancellation.kernel(),
        &kernel,
        compatible.kernel(),
        compatible.receipt(),
    )
    .map_err(|error| format!("official cancellation compatibility did not replay: {error:?}"))?;
    if compatible
        .receipt()
        .added_theorems
        .iter()
        .any(|row| !row.axiom_footprint.is_empty())
    {
        return Err("official cancellation compatibility added assumptions".to_owned());
    }
    let compatibility_receipt = compatible.receipt().receipt_sha256.clone();
    kernel = compatible.kernel().clone();
    let eq_zero = declare_official_eq_zero(&mut kernel)?;
    require_empty(&kernel, eq_zero, OFFICIAL_EQ_ZERO)?;
    let one_le_right = declare_official_one_le_right_of_mul(&mut kernel)?;
    require_empty(&kernel, one_le_right, OFFICIAL_ONE_LE_RIGHT_OF_MUL)?;
    let mul_le_left = declare_official_mul_le_mul_left(&mut kernel)?;
    require_empty(&kernel, mul_le_left, OFFICIAL_MUL_LE_MUL_LEFT)?;
    let le_of_dvd = declare_official_le_of_dvd(&mut kernel)?;
    require_empty(&kernel, le_of_dvd, OFFICIAL_LE_OF_DVD)?;
    let le_antisymm = declare_official_le_antisymm(&mut kernel)?;
    require_empty(&kernel, le_antisymm, OFFICIAL_LE_ANTISYMM)?;
    let antisymm = declare_official_antisymm(&mut kernel)?;
    require_empty(&kernel, antisymm, OFFICIAL_ANTISYMM)?;

    let root = find_name(&kernel, OFFICIAL_ANTISYMM)?;
    let expected = evidence(&kernel, root)?;
    let bytes = kernel
        .render_lean4export_ndjson_roots(&Lean4ExportMetadata::axeyum("4.30.0"), &[root])
        .map_err(|error| format!("official clean-order capsule export failed: {error}"))?;
    for pass in 1..=2 {
        let replay = import_ndjson(Cursor::new(bytes.as_bytes()), ImportLimits::default())
            .map_err(|error| {
                format!("official clean-order capsule import {pass} failed: {error:?}")
            })?;
        let replay_root = find_name(replay.kernel(), OFFICIAL_ANTISYMM)?;
        if evidence(replay.kernel(), replay_root)? != expected {
            return Err(format!(
                "official clean-order capsule import {pass} changed evidence"
            ));
        }
    }
    fs::write(&output_path, &bytes)
        .map_err(|error| format!("official clean-order capsule write failed: {error}"))?;
    println!(
        "{}",
        serde_json::to_string_pretty(&json!({
            "schema_version": 1,
            "kind": "axeyum-autogenesis-official-r091-clean-dvd-antisymm-capsule",
            "state": "official-clean-order-compatible-with-cancellation-and-roundtrip-checked",
            "supports": [
                evidence(&kernel, eq_zero)?,
                evidence(&kernel, one_le_right)?,
                evidence(&kernel, mul_le_left)?,
                evidence(&kernel, le_of_dvd)?,
                evidence(&kernel, le_antisymm)?,
                expected
            ],
            "official_cancellation_compatibility": {
                "bootstrap_root": CANCELLATION_BOOTSTRAP,
                "source_declaration_sha256": mod_lt_reuse.source_declaration_sha256,
                "target_declaration_sha256": mod_lt_reuse.target_declaration_sha256,
                "compatibility": mod_lt_reuse.compatibility.as_str(),
                "root": CANCELLATION,
                "receipt_sha256": compatibility_receipt,
                "replayed": true,
            },
            "portable_capsule": {
                "root": OFFICIAL_ANTISYMM,
                "bytes": bytes.len(),
                "sha256": hex_sha256(bytes.as_bytes()),
                "fresh_imports": 2,
                "theorem": evidence(&kernel, root)?,
                "rendered_material": {"proof_terms": 0, "theorem_types": 0, "theorem_values": 0},
            },
            "exact_target_submissions": 0,
            "target_credit": 0,
            "fact_status_changes": 0,
            "evaluation_credit": 0,
            "ledger_writes": 0,
        }))
        .map_err(|error| error.to_string())?
    );
    Ok(())
}

struct Dev<'a> {
    kernel: &'a mut Kernel,
    anon: NameId,
    nat: NameId,
    zero: NameId,
    succ: NameId,
    rec: NameId,
    add: NameId,
    mul: NameId,
    gcd: NameId,
    dvd: NameId,
    le: NameId,
    fib: NameId,
    eq: NameId,
    eq_refl: NameId,
    eq_rec: NameId,
    exists_rec: NameId,
    next_fvar: u64,
}

struct GcdDev<'a> {
    kernel: &'a mut Kernel,
    anon: NameId,
    nat: NameId,
    gcd: NameId,
    dvd: NameId,
    eq: NameId,
    next_fvar: u64,
}

impl<'a> GcdDev<'a> {
    fn new(kernel: &'a mut Kernel) -> Result<Self, String> {
        Ok(Self {
            anon: kernel.anon(),
            nat: find_name(kernel, "Nat")?,
            gcd: find_name(kernel, "Nat.gcd")?,
            dvd: find_name(kernel, "Nat.dvd")?,
            eq: find_name(kernel, "Eq")?,
            kernel,
            next_fvar: 20_000,
        })
    }
    fn exact(&self, expected: &str) -> Result<NameId, String> {
        find_name(self.kernel, expected)
    }
    fn fresh(&mut self) -> u64 {
        self.next_fvar += 1;
        self.next_fvar
    }
    fn apply(&mut self, head: ExprId, args: &[ExprId]) -> ExprId {
        args.iter()
            .fold(head, |term, &argument| self.kernel.app(term, argument))
    }
    fn lemma(&mut self, name: NameId, args: &[ExprId]) -> ExprId {
        let head = self.kernel.const_(name, vec![]);
        self.apply(head, args)
    }
    fn nat_ty(&mut self) -> ExprId {
        self.kernel.const_(self.nat, vec![])
    }
    fn gcd(&mut self, left: ExprId, right: ExprId) -> ExprId {
        self.lemma(self.gcd, &[left, right])
    }
    fn dvd(&mut self, divisor: ExprId, value: ExprId) -> ExprId {
        self.lemma(self.dvd, &[divisor, value])
    }
    fn eq(&mut self, left: ExprId, right: ExprId) -> ExprId {
        let zero = self.kernel.level_zero();
        let one = self.kernel.level_succ(zero);
        let head = self.kernel.const_(self.eq, vec![one]);
        let nat = self.nat_ty();
        self.apply(head, &[nat, left, right])
    }
    fn arrow(&mut self, domain: ExprId, codomain: ExprId) -> ExprId {
        self.kernel
            .pi(self.anon, domain, codomain, BinderInfo::Default)
    }
    fn lam(&mut self, fv: u64, ty: ExprId, body: ExprId) -> ExprId {
        self.lam_info(fv, ty, body, BinderInfo::Default)
    }
    fn lam_info(&mut self, fv: u64, ty: ExprId, body: ExprId, binder_info: BinderInfo) -> ExprId {
        let body = self.kernel.abstract_fvars(body, &[fv]);
        self.kernel.lam(self.anon, ty, body, binder_info)
    }
    fn pi(&mut self, fv: u64, ty: ExprId, body: ExprId) -> ExprId {
        self.pi_info(fv, ty, body, BinderInfo::Default)
    }
    fn pi_info(&mut self, fv: u64, ty: ExprId, body: ExprId, binder_info: BinderInfo) -> ExprId {
        let body = self.kernel.abstract_fvars(body, &[fv]);
        self.kernel.pi(self.anon, ty, body, binder_info)
    }
}

impl<'a> Dev<'a> {
    fn new(kernel: &'a mut Kernel) -> Result<Self, String> {
        Ok(Self {
            anon: kernel.anon(),
            nat: find_name(kernel, "Nat")?,
            zero: find_name(kernel, "Nat.zero")?,
            succ: find_name(kernel, "Nat.succ")?,
            rec: find_name(kernel, "Nat.rec")?,
            add: find_name(kernel, "Nat.add")?,
            mul: find_name(kernel, "Nat.mul")?,
            gcd: find_name(kernel, "Nat.gcd")?,
            dvd: find_name(kernel, "Nat.dvd")?,
            le: find_name(kernel, "Nat.le")?,
            fib: find_name(kernel, "Nat.fib")?,
            eq: find_name(kernel, "Eq")?,
            eq_refl: find_name(kernel, "Eq.refl")?,
            eq_rec: find_name(kernel, "Eq.rec")?,
            exists_rec: find_name(kernel, "Exists.rec")?,
            kernel,
            next_fvar: 10_000,
        })
    }
    fn exact(&self, expected: &str) -> Result<NameId, String> {
        find_name(self.kernel, expected)
    }
    fn fresh(&mut self) -> u64 {
        self.next_fvar += 1;
        self.next_fvar
    }
    fn apply(&mut self, head: ExprId, args: &[ExprId]) -> ExprId {
        args.iter()
            .fold(head, |term, &arg| self.kernel.app(term, arg))
    }
    fn lemma(&mut self, name: NameId, args: &[ExprId]) -> ExprId {
        let head = self.kernel.const_(name, vec![]);
        self.apply(head, args)
    }
    fn nat_ty(&mut self) -> ExprId {
        self.kernel.const_(self.nat, vec![])
    }
    fn zero(&mut self) -> ExprId {
        self.kernel.const_(self.zero, vec![])
    }
    fn succ(&mut self, value: ExprId) -> ExprId {
        let head = self.kernel.const_(self.succ, vec![]);
        self.kernel.app(head, value)
    }
    fn num(&mut self, value: u32) -> ExprId {
        let mut result = self.zero();
        for _ in 0..value {
            result = self.succ(result);
        }
        result
    }
    fn add(&mut self, left: ExprId, right: ExprId) -> ExprId {
        self.lemma(self.add, &[left, right])
    }
    fn mul(&mut self, left: ExprId, right: ExprId) -> ExprId {
        self.lemma(self.mul, &[left, right])
    }
    fn modulo(&mut self, left: ExprId, right: ExprId) -> Result<ExprId, String> {
        let modulo = find_name(self.kernel, "Nat.mod")?;
        Ok(self.lemma(modulo, &[left, right]))
    }
    fn gcd(&mut self, left: ExprId, right: ExprId) -> ExprId {
        self.lemma(self.gcd, &[left, right])
    }
    fn dvd(&mut self, divisor: ExprId, value: ExprId) -> ExprId {
        self.lemma(self.dvd, &[divisor, value])
    }
    fn le(&mut self, left: ExprId, right: ExprId) -> ExprId {
        self.lemma(self.le, &[left, right])
    }
    fn fib(&mut self, value: ExprId) -> ExprId {
        self.lemma(self.fib, &[value])
    }
    fn one_level(&mut self) -> LevelId {
        let zero = self.kernel.level_zero();
        self.kernel.level_succ(zero)
    }
    fn eq(&mut self, left: ExprId, right: ExprId) -> ExprId {
        let one = self.one_level();
        let head = self.kernel.const_(self.eq, vec![one]);
        let nat = self.nat_ty();
        self.apply(head, &[nat, left, right])
    }
    fn refl(&mut self, value: ExprId) -> ExprId {
        let one = self.one_level();
        let head = self.kernel.const_(self.eq_refl, vec![one]);
        let nat = self.nat_ty();
        self.apply(head, &[nat, value])
    }
    fn congr_succ(&mut self, left: ExprId, right: ExprId, equality: ExprId) -> ExprId {
        let successor_left = self.succ(left);
        let motive = self.eq_motive(left, &|d, value| {
            let successor = d.succ(value);
            d.eq(successor_left, successor)
        });
        let base = self.refl(successor_left);
        self.transport(left, motive, base, right, equality)
    }
    fn congr(
        &mut self,
        left: ExprId,
        right: ExprId,
        equality: ExprId,
        context: &dyn Fn(&mut Self, ExprId) -> ExprId,
    ) -> ExprId {
        let context_left = context(self, left);
        let motive = self.eq_motive(left, &|d, value| {
            let context_value = context(d, value);
            d.eq(context_left, context_value)
        });
        let base = self.refl(context_left);
        self.transport(left, motive, base, right, equality)
    }
    fn false_elim(&mut self, goal: ExprId, contradiction: ExprId) -> ExprId {
        let false_name = find_name(self.kernel, "False").expect("False must exist");
        let false_rec = find_name(self.kernel, "False.rec").expect("False.rec must exist");
        let zero = self.kernel.level_zero();
        let rec = self.kernel.const_(false_rec, vec![zero]);
        let false_ty = self.kernel.const_(false_name, vec![]);
        let motive = self
            .kernel
            .lam(self.anon, false_ty, goal, BinderInfo::Default);
        self.apply(rec, &[motive, contradiction])
    }
    fn lam(&mut self, fv: u64, ty: ExprId, body: ExprId) -> ExprId {
        self.lam_info(fv, ty, body, BinderInfo::Default)
    }
    fn lam_info(&mut self, fv: u64, ty: ExprId, body: ExprId, binder_info: BinderInfo) -> ExprId {
        let body = self.kernel.abstract_fvars(body, &[fv]);
        self.kernel.lam(self.anon, ty, body, binder_info)
    }
    fn pi(&mut self, fv: u64, ty: ExprId, body: ExprId) -> ExprId {
        self.pi_info(fv, ty, body, BinderInfo::Default)
    }
    fn pi_info(&mut self, fv: u64, ty: ExprId, body: ExprId, binder_info: BinderInfo) -> ExprId {
        let body = self.kernel.abstract_fvars(body, &[fv]);
        self.kernel.pi(self.anon, ty, body, binder_info)
    }
    fn arrow(&mut self, domain: ExprId, codomain: ExprId) -> ExprId {
        self.kernel
            .pi(self.anon, domain, codomain, BinderInfo::Default)
    }
    fn and(&mut self, left: ExprId, right: ExprId) -> ExprId {
        let and = find_name(self.kernel, "And").expect("And must exist");
        self.lemma(and, &[left, right])
    }
    fn and_left(&mut self, left: ExprId, right: ExprId, proof: ExprId) -> ExprId {
        let pair = self.and(left, right);
        let pair_fv = self.fresh();
        let motive = self.lam(pair_fv, pair, left);
        let left_fv = self.fresh();
        let left_proof = self.kernel.fvar(left_fv);
        let right_fv = self.fresh();
        let minor = self.lam(right_fv, right, left_proof);
        let minor = self.lam(left_fv, left, minor);
        let zero = self.kernel.level_zero();
        let and_rec = find_name(self.kernel, "And.rec").expect("And.rec must exist");
        let rec = self.kernel.const_(and_rec, vec![zero]);
        self.apply(rec, &[left, right, motive, minor, proof])
    }
    fn and_right(&mut self, left: ExprId, right: ExprId, proof: ExprId) -> ExprId {
        let pair = self.and(left, right);
        let pair_fv = self.fresh();
        let motive = self.lam(pair_fv, pair, right);
        let left_fv = self.fresh();
        let right_fv = self.fresh();
        let right_proof = self.kernel.fvar(right_fv);
        let minor = self.lam(right_fv, right, right_proof);
        let minor = self.lam(left_fv, left, minor);
        let zero = self.kernel.level_zero();
        let and_rec = find_name(self.kernel, "And.rec").expect("And.rec must exist");
        let rec = self.kernel.const_(and_rec, vec![zero]);
        self.apply(rec, &[left, right, motive, minor, proof])
    }
    fn eq_motive(&mut self, source: ExprId, body: &dyn Fn(&mut Self, ExprId) -> ExprId) -> ExprId {
        let value_fv = self.fresh();
        let value = self.kernel.fvar(value_fv);
        let conclusion = body(self, value);
        let equality = self.eq(source, value);
        let inner = self
            .kernel
            .lam(self.anon, equality, conclusion, BinderInfo::Default);
        let nat = self.nat_ty();
        self.lam(value_fv, nat, inner)
    }
    fn transport(
        &mut self,
        source: ExprId,
        motive: ExprId,
        source_proof: ExprId,
        target: ExprId,
        equality: ExprId,
    ) -> ExprId {
        let zero = self.kernel.level_zero();
        let one = self.one_level();
        let rec = self.kernel.const_(self.eq_rec, vec![zero, one]);
        let nat = self.nat_ty();
        self.apply(rec, &[nat, source, motive, source_proof, target, equality])
    }
    fn symm(&mut self, left: ExprId, right: ExprId, proof: ExprId) -> ExprId {
        let motive = self.eq_motive(left, &|d, value| d.eq(value, left));
        let base = self.refl(left);
        self.transport(left, motive, base, right, proof)
    }
    fn trans(
        &mut self,
        left: ExprId,
        middle: ExprId,
        right: ExprId,
        first: ExprId,
        second: ExprId,
    ) -> ExprId {
        let motive = self.eq_motive(middle, &|d, value| d.eq(left, value));
        self.transport(middle, motive, first, right, second)
    }
    fn dvd_predicate(&mut self, divisor: ExprId, value: ExprId) -> ExprId {
        let witness_fv = self.fresh();
        let witness = self.kernel.fvar(witness_fv);
        let product = self.mul(divisor, witness);
        let body = self.eq(value, product);
        let nat = self.nat_ty();
        self.lam(witness_fv, nat, body)
    }
    fn transport_dvd(
        &mut self,
        divisor: ExprId,
        source: ExprId,
        target: ExprId,
        proof: ExprId,
        equality: ExprId,
    ) -> ExprId {
        let motive = self.eq_motive(source, &|d, value| d.dvd(divisor, value));
        self.transport(source, motive, proof, target, equality)
    }
    fn iff_reverse(&mut self, left: ExprId, right: ExprId, proof: ExprId) -> ExprId {
        let iff = find_name(self.kernel, "Iff").expect("Iff is required by iff_reverse");
        let iff_rec =
            find_name(self.kernel, "Iff.rec").expect("Iff.rec is required by iff_reverse");
        let iff_ty = self.lemma(iff, &[left, right]);
        let target = self.arrow(right, left);
        let proof_fv = self.fresh();
        let motive = self.lam(proof_fv, iff_ty, target);
        let forward_ty = self.arrow(left, right);
        let forward_fv = self.fresh();
        let reverse_fv = self.fresh();
        let reverse = self.kernel.fvar(reverse_fv);
        let minor = self.lam(reverse_fv, target, reverse);
        let minor = self.lam(forward_fv, forward_ty, minor);
        let zero = self.kernel.level_zero();
        let rec = self.kernel.const_(iff_rec, vec![zero]);
        self.apply(rec, &[left, right, motive, minor, proof])
    }
    fn induct(
        &mut self,
        motive: &dyn Fn(&mut Self, ExprId) -> ExprId,
        base: &dyn Fn(&mut Self) -> ExprId,
        step: &dyn Fn(&mut Self, ExprId, ExprId) -> ExprId,
        target: ExprId,
    ) -> ExprId {
        let nat = self.nat_ty();
        let value_fv = self.fresh();
        let value = self.kernel.fvar(value_fv);
        let motive_body = motive(self, value);
        let motive_term = self.lam(value_fv, nat, motive_body);
        let base_term = base(self);
        let pred_fv = self.fresh();
        let pred = self.kernel.fvar(pred_fv);
        let ih_fv = self.fresh();
        let ih = self.kernel.fvar(ih_fv);
        let ih_ty = motive(self, pred);
        let step_body = step(self, pred, ih);
        let step_term = self.lam(ih_fv, ih_ty, step_body);
        let step_term = self.lam(pred_fv, nat, step_term);
        let zero = self.kernel.level_zero();
        let rec = self.kernel.const_(self.rec, vec![zero]);
        self.apply(rec, &[motive_term, base_term, step_term, target])
    }
    fn two_lambdas(
        &mut self,
        first_ty: ExprId,
        second_ty: ExprId,
        body: &dyn Fn(&mut Self, ExprId, ExprId) -> ExprId,
    ) -> ExprId {
        let first_fv = self.fresh();
        let first = self.kernel.fvar(first_fv);
        let second_fv = self.fresh();
        let second = self.kernel.fvar(second_fv);
        let result = body(self, first, second);
        let result = self.lam(second_fv, second_ty, result);
        self.lam(first_fv, first_ty, result)
    }
}

fn declare_official_eq_zero(kernel: &mut Kernel) -> Result<NameId, String> {
    let target = nested_name(
        kernel,
        &["Axeyum", "Autogenesis", "eqZeroOfZeroDvdOfficialV1"],
    );
    let mut d = Dev::new(kernel)?;
    let zero_mul = d.exact("Nat.zero_mul")?;
    let nat = d.nat_ty();
    let n_fv = d.fresh();
    let n = d.kernel.fvar(n_fv);
    let zero = d.zero();
    let hypothesis_ty = d.dvd(zero, n);
    let hypothesis_fv = d.fresh();
    let hypothesis = d.kernel.fvar(hypothesis_fv);
    let goal = d.eq(n, zero);
    let predicate = d.dvd_predicate(zero, n);
    let motive = d
        .kernel
        .lam(d.anon, hypothesis_ty, goal, BinderInfo::Default);
    let witness_fv = d.fresh();
    let witness = d.kernel.fvar(witness_fv);
    let product = d.mul(zero, witness);
    let equation_ty = d.eq(n, product);
    let equation_fv = d.fresh();
    let equation = d.kernel.fvar(equation_fv);
    let collapse = d.lemma(zero_mul, &[witness]);
    let proof = d.trans(n, product, zero, equation, collapse);
    let minor = d.lam(equation_fv, equation_ty, proof);
    let minor = d.lam(witness_fv, nat, minor);
    let one = d.one_level();
    let rec = d.kernel.const_(d.exists_rec, vec![one]);
    let proof = d.apply(rec, &[nat, predicate, motive, minor, hypothesis]);
    let proof = d.lam(hypothesis_fv, hypothesis_ty, proof);
    let proof = d.lam(n_fv, nat, proof);
    let ty = d.arrow(hypothesis_ty, goal);
    let ty = d.pi(n_fv, nat, ty);
    d.kernel
        .add_declaration(Declaration::Theorem {
            name: target,
            uparams: vec![],
            ty,
            value: proof,
        })
        .map_err(|error| format!("official zero-divisibility equality rejected: {error:?}"))?;
    Ok(target)
}

#[allow(clippy::too_many_lines)]
fn declare_official_one_le_right_of_mul(kernel: &mut Kernel) -> Result<NameId, String> {
    let target = nested_name(
        kernel,
        &["Axeyum", "Autogenesis", "oneLeRightOfMulOfficialV1"],
    );
    let mut d = Dev::new(kernel)?;
    let mul_zero = d.exact("Nat.mul_zero")?;
    let not_succ_le_zero = d.exact("Nat.not_succ_le_zero")?;
    let zero_le = d.exact("Nat.zero_le")?;
    let le_succ = d.exact("Nat.le_succ_succ")?;
    let false_name = d.exact("False")?;
    let false_rec = d.exact("False.rec")?;
    let nat = d.nat_ty();
    let scale_fv = d.fresh();
    let scale = d.kernel.fvar(scale_fv);
    let factor_fv = d.fresh();
    let factor = d.kernel.fvar(factor_fv);
    let statement = |d: &mut Dev<'_>, value| {
        let zero = d.zero();
        let one = d.succ(zero);
        let product = d.mul(scale, value);
        let hypothesis = d.le(one, product);
        let conclusion = d.le(one, value);
        d.arrow(hypothesis, conclusion)
    };
    let proof = d.induct(
        &statement,
        &|d| {
            let zero = d.zero();
            let one = d.succ(zero);
            let product = d.mul(scale, zero);
            let hypothesis_ty = d.le(one, product);
            let goal = d.le(one, zero);
            let hypothesis_fv = d.fresh();
            let hypothesis = d.kernel.fvar(hypothesis_fv);
            let collapse = d.lemma(mul_zero, &[scale]);
            let motive = d.eq_motive(product, &|d, value| {
                let zero = d.zero();
                let one = d.succ(zero);
                d.le(one, value)
            });
            let bounded = d.transport(product, motive, hypothesis, zero, collapse);
            let contradiction = d.lemma(not_succ_le_zero, &[zero, bounded]);
            let level = d.kernel.level_zero();
            let rec = d.kernel.const_(false_rec, vec![level]);
            let false_ty = d.kernel.const_(false_name, vec![]);
            let motive = d.kernel.lam(d.anon, false_ty, goal, BinderInfo::Default);
            let body = d.apply(rec, &[motive, contradiction]);
            d.lam(hypothesis_fv, hypothesis_ty, body)
        },
        &|d, predecessor, _ih| {
            let zero = d.zero();
            let one = d.succ(zero);
            let successor = d.succ(predecessor);
            let product = d.mul(scale, successor);
            let hypothesis_ty = d.le(one, product);
            let hypothesis_fv = d.fresh();
            let base = d.lemma(zero_le, &[predecessor]);
            let body = d.lemma(le_succ, &[zero, predecessor, base]);
            d.lam(hypothesis_fv, hypothesis_ty, body)
        },
        factor,
    );
    let ty = statement(&mut d, factor);
    let proof = d.lam(factor_fv, nat, proof);
    let proof = d.lam(scale_fv, nat, proof);
    let ty = d.pi(factor_fv, nat, ty);
    let ty = d.pi(scale_fv, nat, ty);
    d.kernel
        .add_declaration(Declaration::Theorem {
            name: target,
            uparams: vec![],
            ty,
            value: proof,
        })
        .map_err(|error| format!("official positive-product factor rejected: {error:?}"))?;
    Ok(target)
}

fn mul_le_statement(d: &mut Dev<'_>, scale: ExprId, left: ExprId, right: ExprId) -> ExprId {
    let premise = d.le(left, right);
    let scaled_left = d.mul(scale, left);
    let scaled_right = d.mul(scale, right);
    let conclusion = d.le(scaled_left, scaled_right);
    d.arrow(premise, conclusion)
}

#[allow(clippy::too_many_lines)]
fn declare_official_mul_le_mul_left(kernel: &mut Kernel) -> Result<NameId, String> {
    let target = nested_name(kernel, &["Axeyum", "Autogenesis", "mulLeMulLeftOfficialV1"]);
    let mut d = Dev::new(kernel)?;
    let le_rec = d.exact("Nat.le.rec")?;
    let le_refl = d.exact("Nat.le_refl")?;
    let le_add_right = d.exact("Nat.le_add_right")?;
    let le_trans = d.exact("Nat.le_trans")?;
    let nat = d.nat_ty();
    let scale_fv = d.fresh();
    let scale = d.kernel.fvar(scale_fv);
    let left_fv = d.fresh();
    let left = d.kernel.fvar(left_fv);
    let right_fv = d.fresh();
    let right = d.kernel.fvar(right_fv);
    let premise = d.le(left, right);
    let premise_fv = d.fresh();
    let premise_proof = d.kernel.fvar(premise_fv);

    let candidate_fv = d.fresh();
    let candidate = d.kernel.fvar(candidate_fv);
    let bound_ty = d.le(left, candidate);
    let bound_fv = d.fresh();
    let scaled_left = d.mul(scale, left);
    let scaled_candidate = d.mul(scale, candidate);
    let motive_body = d.le(scaled_left, scaled_candidate);
    let motive_body = d.lam(bound_fv, bound_ty, motive_body);
    let motive = d.lam(candidate_fv, nat, motive_body);

    let base_product = d.mul(scale, left);
    let base = d.lemma(le_refl, &[base_product]);

    let step_value_fv = d.fresh();
    let step_value = d.kernel.fvar(step_value_fv);
    let step_bound_ty = d.le(left, step_value);
    let step_bound_fv = d.fresh();
    let step_ih_ty = {
        let lhs = d.mul(scale, left);
        let rhs = d.mul(scale, step_value);
        d.le(lhs, rhs)
    };
    let step_ih_fv = d.fresh();
    let step_ih = d.kernel.fvar(step_ih_fv);
    let scaled_step = d.mul(scale, step_value);
    let scaled_successor = {
        let successor = d.succ(step_value);
        d.mul(scale, successor)
    };
    let append_scale = d.lemma(le_add_right, &[scaled_step, scale]);
    let step_body = d.lemma(
        le_trans,
        &[
            scaled_left,
            scaled_step,
            scaled_successor,
            step_ih,
            append_scale,
        ],
    );
    let step = d.lam(step_ih_fv, step_ih_ty, step_body);
    let step = d.lam(step_bound_fv, step_bound_ty, step);
    let step = d.lam(step_value_fv, nat, step);

    let rec = d.kernel.const_(le_rec, vec![]);
    let proof = d.apply(rec, &[left, motive, base, step, right, premise_proof]);
    let ty = mul_le_statement(&mut d, scale, left, right);
    let proof = d.lam(premise_fv, premise, proof);
    let proof = d.lam(right_fv, nat, proof);
    let proof = d.lam(left_fv, nat, proof);
    let proof = d.lam(scale_fv, nat, proof);
    let ty = d.pi(right_fv, nat, ty);
    let ty = d.pi(left_fv, nat, ty);
    let ty = d.pi(scale_fv, nat, ty);
    d.kernel
        .add_declaration(Declaration::Theorem {
            name: target,
            uparams: vec![],
            ty,
            value: proof,
        })
        .map_err(|error| format!("official multiplicative monotonicity rejected: {error:?}"))?;
    Ok(target)
}

#[allow(clippy::too_many_lines)]
fn declare_official_le_of_dvd(kernel: &mut Kernel) -> Result<NameId, String> {
    let target = nested_name(kernel, &["Axeyum", "Autogenesis", "leOfDvdOfficialV1"]);
    let mut d = Dev::new(kernel)?;
    let one_le_right = d.exact(OFFICIAL_ONE_LE_RIGHT_OF_MUL)?;
    let mul_le_left = d.exact(OFFICIAL_MUL_LE_MUL_LEFT)?;
    let mul_one = d.exact("Nat.mul_one")?;
    let nat = d.nat_ty();
    let a_fv = d.fresh();
    let a = d.kernel.fvar(a_fv);
    let n_fv = d.fresh();
    let n = d.kernel.fvar(n_fv);
    let one = d.num(1);
    let positive_ty = d.le(one, n);
    let divides_ty = d.dvd(a, n);
    let conclusion = d.le(a, n);
    let positive_fv = d.fresh();
    let positive = d.kernel.fvar(positive_fv);
    let divides_fv = d.fresh();
    let divides = d.kernel.fvar(divides_fv);
    let predicate = d.dvd_predicate(a, n);
    let motive = d
        .kernel
        .lam(d.anon, divides_ty, conclusion, BinderInfo::Default);
    let witness_fv = d.fresh();
    let witness = d.kernel.fvar(witness_fv);
    let product = d.mul(a, witness);
    let equation_ty = d.eq(n, product);
    let equation_fv = d.fresh();
    let equation = d.kernel.fvar(equation_fv);
    let product_positive = {
        let motive = d.eq_motive(n, &|d, value| {
            let one = d.num(1);
            d.le(one, value)
        });
        d.transport(n, motive, positive, product, equation)
    };
    let witness_positive = d.lemma(one_le_right, &[a, witness, product_positive]);
    let scaled = d.lemma(mul_le_left, &[a, one, witness, witness_positive]);
    let a_one = d.mul(a, one);
    let collapse = d.lemma(mul_one, &[a]);
    let bounded_product = {
        let motive = d.eq_motive(a_one, &|d, value| d.le(value, product));
        d.transport(a_one, motive, scaled, a, collapse)
    };
    let reverse_equation = d.symm(n, product, equation);
    let body = {
        let motive = d.eq_motive(product, &|d, value| d.le(a, value));
        d.transport(product, motive, bounded_product, n, reverse_equation)
    };
    let minor = d.lam(equation_fv, equation_ty, body);
    let minor = d.lam(witness_fv, nat, minor);
    let one_level = d.one_level();
    let rec = d.kernel.const_(d.exists_rec, vec![one_level]);
    let proof = d.apply(rec, &[nat, predicate, motive, minor, divides]);
    let proof = d.lam(divides_fv, divides_ty, proof);
    let proof = d.lam(positive_fv, positive_ty, proof);
    let proof = d.lam(n_fv, nat, proof);
    let proof = d.lam(a_fv, nat, proof);
    let ty = d.arrow(divides_ty, conclusion);
    let ty = d.arrow(positive_ty, ty);
    let ty = d.pi(n_fv, nat, ty);
    let ty = d.pi(a_fv, nat, ty);
    d.kernel
        .add_declaration(Declaration::Theorem {
            name: target,
            uparams: vec![],
            ty,
            value: proof,
        })
        .map_err(|error| format!("official divisor bound rejected: {error:?}"))?;
    Ok(target)
}

fn le_antisymm_statement(d: &mut Dev<'_>, left: ExprId, right: ExprId) -> ExprId {
    let forward = d.le(left, right);
    let reverse = d.le(right, left);
    let equality = d.eq(left, right);
    let rest = d.arrow(reverse, equality);
    d.arrow(forward, rest)
}

#[allow(clippy::too_many_lines)]
fn declare_official_le_antisymm(kernel: &mut Kernel) -> Result<NameId, String> {
    let target = nested_name(kernel, &["Axeyum", "Autogenesis", "leAntisymmOfficialV1"]);
    let mut d = Dev::new(kernel)?;
    let not_succ_le_zero = d.exact("Nat.not_succ_le_zero")?;
    let le_of_succ = d.exact("Nat.le_of_succ_le_succ")?;
    let nat = d.nat_ty();
    let left_fv = d.fresh();
    let left = d.kernel.fvar(left_fv);
    let right_fv = d.fresh();
    let right = d.kernel.fvar(right_fv);

    let proof = d.induct(
        &|d, candidate_left| {
            let candidate_right_fv = d.fresh();
            let candidate_right = d.kernel.fvar(candidate_right_fv);
            let statement = le_antisymm_statement(d, candidate_left, candidate_right);
            let nat = d.nat_ty();
            d.pi(candidate_right_fv, nat, statement)
        },
        &|d| {
            let zero = d.zero();
            let candidate_right_fv = d.fresh();
            let candidate_right = d.kernel.fvar(candidate_right_fv);
            let body = d.induct(
                &|d, value| le_antisymm_statement(d, zero, value),
                &|d| {
                    let zero = d.zero();
                    let forward_ty = d.le(zero, zero);
                    let reverse_ty = d.le(zero, zero);
                    d.two_lambdas(forward_ty, reverse_ty, &|d, _forward, _reverse| {
                        d.refl(zero)
                    })
                },
                &|d, predecessor, _ih| {
                    let zero = d.zero();
                    let successor = d.succ(predecessor);
                    let forward_ty = d.le(zero, successor);
                    let reverse_ty = d.le(successor, zero);
                    d.two_lambdas(forward_ty, reverse_ty, &|d, _forward, reverse| {
                        let contradiction = d.lemma(not_succ_le_zero, &[predecessor, reverse]);
                        let goal = d.eq(zero, successor);
                        d.false_elim(goal, contradiction)
                    })
                },
                candidate_right,
            );
            let nat = d.nat_ty();
            d.lam(candidate_right_fv, nat, body)
        },
        &|d, left_pred, outer_ih| {
            let left_succ = d.succ(left_pred);
            let candidate_right_fv = d.fresh();
            let candidate_right = d.kernel.fvar(candidate_right_fv);
            let body = d.induct(
                &|d, value| le_antisymm_statement(d, left_succ, value),
                &|d| {
                    let zero = d.zero();
                    let forward_ty = d.le(left_succ, zero);
                    let reverse_ty = d.le(zero, left_succ);
                    d.two_lambdas(forward_ty, reverse_ty, &|d, forward, _reverse| {
                        let contradiction = d.lemma(not_succ_le_zero, &[left_pred, forward]);
                        let goal = d.eq(left_succ, zero);
                        d.false_elim(goal, contradiction)
                    })
                },
                &|d, right_pred, _inner_ih| {
                    let right_succ = d.succ(right_pred);
                    let forward_ty = d.le(left_succ, right_succ);
                    let reverse_ty = d.le(right_succ, left_succ);
                    d.two_lambdas(forward_ty, reverse_ty, &|d, forward, reverse| {
                        let pred_forward = d.lemma(le_of_succ, &[left_pred, right_pred, forward]);
                        let pred_reverse = d.lemma(le_of_succ, &[right_pred, left_pred, reverse]);
                        let ih_at_right = d.apply(outer_ih, &[right_pred]);
                        let pred_equality = d.apply(ih_at_right, &[pred_forward, pred_reverse]);
                        d.congr_succ(left_pred, right_pred, pred_equality)
                    })
                },
                candidate_right,
            );
            let nat = d.nat_ty();
            d.lam(candidate_right_fv, nat, body)
        },
        left,
    );
    let ty = le_antisymm_statement(&mut d, left, right);
    let proof = d.apply(proof, &[right]);
    let proof = d.lam(right_fv, nat, proof);
    let proof = d.lam(left_fv, nat, proof);
    let ty = d.pi(right_fv, nat, ty);
    let ty = d.pi(left_fv, nat, ty);
    d.kernel
        .add_declaration(Declaration::Theorem {
            name: target,
            uparams: vec![],
            ty,
            value: proof,
        })
        .map_err(|error| format!("official order antisymmetry rejected: {error:?}"))?;
    Ok(target)
}

fn antisymm_statement(d: &mut Dev<'_>, a: ExprId, b: ExprId) -> ExprId {
    let forward = d.dvd(a, b);
    let reverse = d.dvd(b, a);
    let equality = d.eq(a, b);
    let rest = d.arrow(reverse, equality);
    d.arrow(forward, rest)
}

#[allow(clippy::too_many_lines)]
fn declare_official_antisymm(kernel: &mut Kernel) -> Result<NameId, String> {
    let target = nested_name(kernel, &["Axeyum", "Autogenesis", "dvdAntisymmOfficialV1"]);
    let mut d = Dev::new(kernel)?;
    let eq_zero = d.exact(OFFICIAL_EQ_ZERO)?;
    let clean_le = d.exact(OFFICIAL_LE_OF_DVD)?;
    let le_antisymm = d.exact(OFFICIAL_LE_ANTISYMM)?;
    let zero_le = d.exact("Nat.zero_le")?;
    let le_succ = d.exact("Nat.le_succ_succ")?;
    let nat = d.nat_ty();
    let a_fv = d.fresh();
    let a = d.kernel.fvar(a_fv);
    let b_fv = d.fresh();
    let b = d.kernel.fvar(b_fv);
    let proof = d.induct(
        &|d, candidate_b| antisymm_statement(d, a, candidate_b),
        &|d| {
            let zero = d.zero();
            let forward_ty = d.dvd(a, zero);
            let reverse_ty = d.dvd(zero, a);
            d.two_lambdas(forward_ty, reverse_ty, &|d, _forward, reverse| {
                d.lemma(eq_zero, &[a, reverse])
            })
        },
        &|d, b_pred, _ih| {
            let b_succ = d.succ(b_pred);
            d.induct(
                &|d, candidate_a| antisymm_statement(d, candidate_a, b_succ),
                &|d| {
                    let zero = d.zero();
                    let forward_ty = d.dvd(zero, b_succ);
                    let reverse_ty = d.dvd(b_succ, zero);
                    d.two_lambdas(forward_ty, reverse_ty, &|d, forward, _reverse| {
                        let collapse = d.lemma(eq_zero, &[b_succ, forward]);
                        d.symm(b_succ, zero, collapse)
                    })
                },
                &|d, a_pred, _a_ih| {
                    let a_succ = d.succ(a_pred);
                    let forward_ty = d.dvd(a_succ, b_succ);
                    let reverse_ty = d.dvd(b_succ, a_succ);
                    d.two_lambdas(forward_ty, reverse_ty, &|d, forward, reverse| {
                        let zero = d.zero();
                        let zero_b = d.lemma(zero_le, &[b_pred]);
                        let b_positive = d.lemma(le_succ, &[zero, b_pred, zero_b]);
                        let zero_a = d.lemma(zero_le, &[a_pred]);
                        let a_positive = d.lemma(le_succ, &[zero, a_pred, zero_a]);
                        let a_le_b = d.lemma(clean_le, &[a_succ, b_succ, b_positive, forward]);
                        let b_le_a = d.lemma(clean_le, &[b_succ, a_succ, a_positive, reverse]);
                        d.lemma(le_antisymm, &[a_succ, b_succ, a_le_b, b_le_a])
                    })
                },
                a,
            )
        },
        b,
    );
    let ty = antisymm_statement(&mut d, a, b);
    let proof = d.lam(b_fv, nat, proof);
    let proof = d.lam(a_fv, nat, proof);
    let ty = d.pi(b_fv, nat, ty);
    let ty = d.pi(a_fv, nat, ty);
    d.kernel
        .add_declaration(Declaration::Theorem {
            name: target,
            uparams: vec![],
            ty,
            value: proof,
        })
        .map_err(|error| format!("official divisibility antisymmetry rejected: {error:?}"))?;
    Ok(target)
}

#[allow(clippy::similar_names)]
fn declare_target_native_dvd_refl(kernel: &mut Kernel) -> Result<NameId, String> {
    let target = nested_name(kernel, &["Axeyum", "Autogenesis", "dvdReflOfficialV1"]);
    let mut d = Dev::new(kernel)?;
    let mul_one = d.exact("Nat.mul_one")?;
    let exists_intro = d.exact("Exists.intro")?;
    let nat = d.nat_ty();
    let value_fv = d.fresh();
    let value = d.kernel.fvar(value_fv);
    let one_value = d.num(1);
    let product = d.mul(value, one_value);
    let collapse = d.lemma(mul_one, &[value]);
    let equation = d.symm(product, value, collapse);
    let predicate = d.dvd_predicate(value, value);
    let level = d.one_level();
    let intro = d.kernel.const_(exists_intro, vec![level]);
    let proof = d.apply(intro, &[nat, predicate, one_value, equation]);
    let ty = d.dvd(value, value);
    let proof = d.lam(value_fv, nat, proof);
    let ty = d.pi(value_fv, nat, ty);
    d.kernel
        .add_declaration(Declaration::Theorem {
            name: target,
            uparams: vec![],
            ty,
            value: proof,
        })
        .map_err(|error| format!("target-native dvd reflexivity rejected: {error:?}"))?;
    Ok(target)
}

fn declare_target_native_dvd_mul_right(kernel: &mut Kernel) -> Result<NameId, String> {
    let target = nested_name(kernel, &["Axeyum", "Autogenesis", "dvdMulRightOfficialV1"]);
    let mut d = Dev::new(kernel)?;
    let mul_assoc = d.exact("Axeyum.Autogenesis.balancedBezoutMulAssocLeafV1")?;
    let exists_intro = d.exact("Exists.intro")?;
    let nat = d.nat_ty();
    let divisor_fv = d.fresh();
    let divisor = d.kernel.fvar(divisor_fv);
    let value_fv = d.fresh();
    let value = d.kernel.fvar(value_fv);
    let factor_fv = d.fresh();
    let factor = d.kernel.fvar(factor_fv);
    let premise_ty = d.dvd(divisor, value);
    let premise_fv = d.fresh();
    let premise = d.kernel.fvar(premise_fv);
    let result_value = d.mul(value, factor);
    let conclusion = d.dvd(divisor, result_value);
    let predicate = d.dvd_predicate(divisor, value);
    let motive = d
        .kernel
        .lam(d.anon, premise_ty, conclusion, BinderInfo::Default);
    let witness_fv = d.fresh();
    let witness = d.kernel.fvar(witness_fv);
    let divisor_witness = d.mul(divisor, witness);
    let equation_ty = d.eq(value, divisor_witness);
    let equation_fv = d.fresh();
    let equation = d.kernel.fvar(equation_fv);
    let first = d.congr(value, divisor_witness, equation, &|d, x| d.mul(x, factor));
    let associated = d.lemma(mul_assoc, &[divisor, witness, factor]);
    let result_witness = d.mul(witness, factor);
    let product = d.mul(divisor, result_witness);
    let replaced = d.mul(divisor_witness, factor);
    let full_equation = d.trans(result_value, replaced, product, first, associated);
    let result_predicate = d.dvd_predicate(divisor, result_value);
    let level = d.one_level();
    let intro = d.kernel.const_(exists_intro, vec![level]);
    let body = d.apply(
        intro,
        &[nat, result_predicate, result_witness, full_equation],
    );
    let minor = d.lam(equation_fv, equation_ty, body);
    let minor = d.lam(witness_fv, nat, minor);
    let rec = d.kernel.const_(d.exists_rec, vec![level]);
    let proof = d.apply(rec, &[nat, predicate, motive, minor, premise]);
    let proof = d.lam(premise_fv, premise_ty, proof);
    let proof = d.lam(factor_fv, nat, proof);
    let proof = d.lam(value_fv, nat, proof);
    let proof = d.lam(divisor_fv, nat, proof);
    let ty = d.arrow(premise_ty, conclusion);
    let ty = d.pi(factor_fv, nat, ty);
    let ty = d.pi(value_fv, nat, ty);
    let ty = d.pi(divisor_fv, nat, ty);
    d.kernel
        .add_declaration(Declaration::Theorem {
            name: target,
            uparams: vec![],
            ty,
            value: proof,
        })
        .map_err(|error| format!("target-native dvd multiplication rejected: {error:?}"))?;
    Ok(target)
}

fn gcd_divides_pair_type(d: &mut Dev<'_>) -> ExprId {
    let nat = d.nat_ty();
    let left_fv = d.fresh();
    let left = d.kernel.fvar(left_fv);
    let right_fv = d.fresh();
    let right = d.kernel.fvar(right_fv);
    let gcd = d.gcd(left, right);
    let divides_left = d.dvd(gcd, left);
    let divides_right = d.dvd(gcd, right);
    let pair = d.and(divides_left, divides_right);
    let pair = d.pi(right_fv, nat, pair);
    d.pi(left_fv, nat, pair)
}

fn divides_gcd_type(d: &mut Dev<'_>) -> ExprId {
    let nat = d.nat_ty();
    let divisor_fv = d.fresh();
    let divisor = d.kernel.fvar(divisor_fv);
    let left_fv = d.fresh();
    let left = d.kernel.fvar(left_fv);
    let right_fv = d.fresh();
    let right = d.kernel.fvar(right_fv);
    let divides_left = d.dvd(divisor, left);
    let divides_right = d.dvd(divisor, right);
    let gcd = d.gcd(left, right);
    let conclusion = d.dvd(divisor, gcd);
    let ty = d.arrow(divides_right, conclusion);
    let ty = d.arrow(divides_left, ty);
    let ty = d.pi(right_fv, nat, ty);
    let ty = d.pi(left_fv, nat, ty);
    d.pi(divisor_fv, nat, ty)
}

fn declare_target_native_gcd_dvd_projection(
    kernel: &mut Kernel,
    project_left: bool,
) -> Result<NameId, String> {
    let target_name = if project_left {
        "gcdDvdLeftOfficialV1"
    } else {
        "gcdDvdRightOfficialV1"
    };
    let target = nested_name(kernel, &["Axeyum", "Autogenesis", target_name]);
    let mut d = Dev::new(kernel)?;
    let family_name = d.exact(GCD_DIVISIBILITY_CLOSED)?;
    let family = d.kernel.const_(family_name, vec![]);
    let pair_family_ty = gcd_divides_pair_type(&mut d);
    let greatest_family_ty = divides_gcd_type(&mut d);
    let pair_family = d.and_left(pair_family_ty, greatest_family_ty, family);
    let nat = d.nat_ty();
    let left_fv = d.fresh();
    let left = d.kernel.fvar(left_fv);
    let right_fv = d.fresh();
    let right = d.kernel.fvar(right_fv);
    let pair = d.apply(pair_family, &[left, right]);
    let gcd = d.gcd(left, right);
    let divides_left = d.dvd(gcd, left);
    let divides_right = d.dvd(gcd, right);
    let body = if project_left {
        d.and_left(divides_left, divides_right, pair)
    } else {
        d.and_right(divides_left, divides_right, pair)
    };
    let proof = d.lam(right_fv, nat, body);
    let proof = d.lam(left_fv, nat, proof);
    let conclusion = if project_left {
        divides_left
    } else {
        divides_right
    };
    let ty = d.pi(right_fv, nat, conclusion);
    let ty = d.pi(left_fv, nat, ty);
    d.kernel
        .add_declaration(Declaration::Theorem {
            name: target,
            uparams: vec![],
            ty,
            value: proof,
        })
        .map_err(|error| format!("target-native {target_name} rejected: {error:?}"))?;
    Ok(target)
}

fn declare_target_native_dvd_gcd_projection(kernel: &mut Kernel) -> Result<NameId, String> {
    let target = nested_name(kernel, &["Axeyum", "Autogenesis", "dvdGcdOfficialV1"]);
    let mut d = Dev::new(kernel)?;
    let family_name = d.exact(GCD_DIVISIBILITY_CLOSED)?;
    let family = d.kernel.const_(family_name, vec![]);
    let pair_family_ty = gcd_divides_pair_type(&mut d);
    let greatest_family_ty = divides_gcd_type(&mut d);
    let proof = d.and_right(pair_family_ty, greatest_family_ty, family);
    d.kernel
        .add_declaration(Declaration::Theorem {
            name: target,
            uparams: vec![],
            ty: greatest_family_ty,
            value: proof,
        })
        .map_err(|error| format!("target-native dvdGcdOfficialV1 rejected: {error:?}"))?;
    Ok(target)
}

fn declare_target_native_dvd_add(kernel: &mut Kernel) -> Result<NameId, String> {
    let target = nested_name(kernel, &["Axeyum", "Autogenesis", "dvdAddOfficialV1"]);
    let mut d = Dev::new(kernel)?;
    let mul_add = d.exact("Nat.mul_add")?;
    let exists_intro = d.exact("Exists.intro")?;
    let nat = d.nat_ty();
    let divisor_fv = d.fresh();
    let divisor = d.kernel.fvar(divisor_fv);
    let left_fv = d.fresh();
    let left = d.kernel.fvar(left_fv);
    let right_fv = d.fresh();
    let right = d.kernel.fvar(right_fv);
    let divides_left_ty = d.dvd(divisor, left);
    let divides_left_fv = d.fresh();
    let divides_left = d.kernel.fvar(divides_left_fv);
    let divides_right_ty = d.dvd(divisor, right);
    let divides_right_fv = d.fresh();
    let divides_right = d.kernel.fvar(divides_right_fv);
    let sum = d.add(left, right);
    let conclusion = d.dvd(divisor, sum);
    let left_predicate = d.dvd_predicate(divisor, left);
    let remaining = d.arrow(divides_right_ty, conclusion);
    let left_motive = d
        .kernel
        .lam(d.anon, divides_left_ty, remaining, BinderInfo::Default);
    let left_witness_fv = d.fresh();
    let left_witness = d.kernel.fvar(left_witness_fv);
    let divisor_left = d.mul(divisor, left_witness);
    let left_equation_ty = d.eq(left, divisor_left);
    let left_equation_fv = d.fresh();
    let left_equation = d.kernel.fvar(left_equation_fv);
    let right_predicate = d.dvd_predicate(divisor, right);
    let right_motive = d
        .kernel
        .lam(d.anon, divides_right_ty, conclusion, BinderInfo::Default);
    let right_witness_fv = d.fresh();
    let right_witness = d.kernel.fvar(right_witness_fv);
    let divisor_right = d.mul(divisor, right_witness);
    let right_equation_ty = d.eq(right, divisor_right);
    let right_equation_fv = d.fresh();
    let right_equation = d.kernel.fvar(right_equation_fv);
    let first = d.congr(left, divisor_left, left_equation, &|d, value| {
        d.add(value, right)
    });
    let second = d.congr(right, divisor_right, right_equation, &|d, value| {
        d.add(divisor_left, value)
    });
    let distributed = d.lemma(mul_add, &[divisor, left_witness, right_witness]);
    let witness = d.add(left_witness, right_witness);
    let product = d.mul(divisor, witness);
    let divisor_sum = d.add(divisor_left, divisor_right);
    let undistribute = d.symm(product, divisor_sum, distributed);
    let left_replaced = d.add(divisor_left, right);
    let left_to_both = d.trans(sum, left_replaced, divisor_sum, first, second);
    let equation = d.trans(sum, divisor_sum, product, left_to_both, undistribute);
    let sum_predicate = d.dvd_predicate(divisor, sum);
    let one = d.one_level();
    let intro = d.kernel.const_(exists_intro, vec![one]);
    let inner_body = d.apply(intro, &[nat, sum_predicate, witness, equation]);
    let inner_minor = d.lam(right_equation_fv, right_equation_ty, inner_body);
    let inner_minor = d.lam(right_witness_fv, nat, inner_minor);
    let rec = d.kernel.const_(d.exists_rec, vec![one]);
    let inner = d.apply(
        rec,
        &[
            nat,
            right_predicate,
            right_motive,
            inner_minor,
            divides_right,
        ],
    );
    let inner = d.lam(divides_right_fv, divides_right_ty, inner);
    let outer_minor = d.lam(left_equation_fv, left_equation_ty, inner);
    let outer_minor = d.lam(left_witness_fv, nat, outer_minor);
    let rec = d.kernel.const_(d.exists_rec, vec![one]);
    let proof = d.apply(
        rec,
        &[nat, left_predicate, left_motive, outer_minor, divides_left],
    );
    let proof = d.lam(divides_left_fv, divides_left_ty, proof);
    let proof = d.lam(right_fv, nat, proof);
    let proof = d.lam(left_fv, nat, proof);
    let proof = d.lam(divisor_fv, nat, proof);
    let ty = d.arrow(divides_right_ty, conclusion);
    let ty = d.arrow(divides_left_ty, ty);
    let ty = d.pi(right_fv, nat, ty);
    let ty = d.pi(left_fv, nat, ty);
    let ty = d.pi(divisor_fv, nat, ty);
    d.kernel
        .add_declaration(Declaration::Theorem {
            name: target,
            uparams: vec![],
            ty,
            value: proof,
        })
        .map_err(|error| format!("target-native dvd_add rejected: {error:?}"))?;
    Ok(target)
}

fn declare_target_native_eq_one_of_dvd_one(kernel: &mut Kernel) -> Result<NameId, String> {
    let target = nested_name(
        kernel,
        &["Axeyum", "Autogenesis", "eqOneOfDvdOneOfficialV1"],
    );
    let mut d = Dev::new(kernel)?;
    let antisymm = d.exact(OFFICIAL_ANTISYMM)?;
    let one_mul = d.exact("Nat.one_mul")?;
    let exists_intro = d.exact("Exists.intro")?;
    let nat = d.nat_ty();
    let divisor_fv = d.fresh();
    let divisor = d.kernel.fvar(divisor_fv);
    let one_value = d.num(1);
    let divides_ty = d.dvd(divisor, one_value);
    let divides_fv = d.fresh();
    let divides = d.kernel.fvar(divides_fv);
    let one_times = d.mul(one_value, divisor);
    let collapse = d.lemma(one_mul, &[divisor]);
    let witness_equation = d.symm(one_times, divisor, collapse);
    let predicate = d.dvd_predicate(one_value, divisor);
    let level = d.one_level();
    let intro = d.kernel.const_(exists_intro, vec![level]);
    let one_divides = d.apply(intro, &[nat, predicate, divisor, witness_equation]);
    let proof = d.lemma(antisymm, &[divisor, one_value, divides, one_divides]);
    let conclusion = d.eq(divisor, one_value);
    let proof = d.lam(divides_fv, divides_ty, proof);
    let proof = d.lam(divisor_fv, nat, proof);
    let ty = d.arrow(divides_ty, conclusion);
    let ty = d.pi(divisor_fv, nat, ty);
    d.kernel
        .add_declaration(Declaration::Theorem {
            name: target,
            uparams: vec![],
            ty,
            value: proof,
        })
        .map_err(|error| format!("target-native eq_one_of_dvd_one rejected: {error:?}"))?;
    Ok(target)
}

fn declare_public_gcd_zero_left(kernel: &mut Kernel) -> Result<NameId, String> {
    if optional_name(kernel, GCD_ZERO_LEFT_PUBLIC)?.is_some() {
        return Err(format!(
            "{GCD_ZERO_LEFT_PUBLIC} already exists before target-owned alias"
        ));
    }
    let generic = find_name(kernel, GCD_ZERO_LEFT_GENERIC)?;
    let ty = match kernel.environment().get(generic) {
        Some(Declaration::Theorem { ty, .. }) => *ty,
        _ => return Err(format!("{GCD_ZERO_LEFT_GENERIC} is not a theorem")),
    };
    let value = kernel.const_(generic, vec![]);
    let target = {
        let nat = find_name(kernel, "Nat")?;
        kernel.name_str(nat, "gcd_zero_left")
    };
    kernel
        .add_declaration(Declaration::Theorem {
            name: target,
            uparams: vec![],
            ty,
            value,
        })
        .map_err(|error| format!("public gcd zero-left alias rejected: {error:?}"))?;
    Ok(target)
}

fn declare_clean_gcd_comm(kernel: &mut Kernel, target_native: bool) -> Result<NameId, String> {
    let target = nested_name(kernel, &["Axeyum", "Autogenesis", "gcdCommCleanV1"]);
    let mut d = Dev::new(kernel)?;
    let antisymm = d.exact(CLEAN_ANTISYMM)?;
    let gcd_left = d.exact(if target_native {
        TARGET_GCD_DVD_LEFT
    } else {
        "Nat.gcd_dvd_left"
    })?;
    let gcd_right = d.exact(if target_native {
        TARGET_GCD_DVD_RIGHT
    } else {
        "Nat.gcd_dvd_right"
    })?;
    let dvd_gcd = d.exact(if target_native {
        TARGET_DVD_GCD
    } else {
        "Nat.dvd_gcd"
    })?;
    let nat = d.nat_ty();
    let a_fv = d.fresh();
    let a = d.kernel.fvar(a_fv);
    let b_fv = d.fresh();
    let b = d.kernel.fvar(b_fv);
    let ab = d.gcd(a, b);
    let ba = d.gcd(b, a);
    let ab_to_b = d.lemma(gcd_right, &[a, b]);
    let ab_to_a = d.lemma(gcd_left, &[a, b]);
    let forward = d.lemma(dvd_gcd, &[ab, b, a, ab_to_b, ab_to_a]);
    let ba_to_a = d.lemma(gcd_right, &[b, a]);
    let ba_to_b = d.lemma(gcd_left, &[b, a]);
    let reverse = d.lemma(dvd_gcd, &[ba, a, b, ba_to_a, ba_to_b]);
    let proof = d.lemma(antisymm, &[ab, ba, forward, reverse]);
    let ty = d.eq(ab, ba);
    let proof = d.lam(b_fv, nat, proof);
    let proof = d.lam(a_fv, nat, proof);
    let ty = d.pi(b_fv, nat, ty);
    let ty = d.pi(a_fv, nat, ty);
    d.kernel
        .add_declaration(Declaration::Theorem {
            name: target,
            uparams: vec![],
            ty,
            value: proof,
        })
        .map_err(|error| format!("clean gcd commutativity rejected: {error:?}"))?;
    Ok(target)
}

enum AdditiveCancellation {
    Direct(NameId),
    Iff(NameId),
}

fn declare_target(
    kernel: &mut Kernel,
    goal: ExprId,
    target_native: bool,
) -> Result<NameId, String> {
    let target = nested_name(kernel, &["Nat", "gcd_fib_add_self"]);
    let mut d = Dev::new(kernel)?;
    let addition = d.exact(ADDITION)?;
    let coprime = d.exact(if target_native {
        TARGET_FIB_COPRIME
    } else {
        COPRIME
    })?;
    let cancellation = d.exact(CANCELLATION)?;
    let antisymm = d.exact(CLEAN_ANTISYMM)?;
    let gcd_comm = d.exact(CLEAN_GCD_COMM)?;
    let gcd_left = d.exact(if target_native {
        TARGET_GCD_DVD_LEFT
    } else {
        "Nat.gcd_dvd_left"
    })?;
    let gcd_right = d.exact(if target_native {
        TARGET_GCD_DVD_RIGHT
    } else {
        "Nat.gcd_dvd_right"
    })?;
    let dvd_gcd = d.exact(if target_native {
        TARGET_DVD_GCD
    } else {
        "Nat.dvd_gcd"
    })?;
    let dvd_mul = d.exact(if target_native {
        TARGET_DVD_MUL_RIGHT
    } else {
        "Nat.dvd_mul_right_of_dvd"
    })?;
    let dvd_add = d.exact(if target_native {
        TARGET_DVD_ADD
    } else {
        "Nat.dvd_add"
    })?;
    let additive_cancellation = if target_native {
        AdditiveCancellation::Direct(d.exact("Axeyum.Autogenesis.dvdAddCancelAllNatClosedV1")?)
    } else {
        AdditiveCancellation::Iff(d.exact("Nat.dvd_add_iff_right")?)
    };
    let mul_comm = d.exact("Nat.mul_comm")?;
    let nat = d.nat_ty();
    let m_fv = d.fresh();
    let m = d.kernel.fvar(m_fv);
    let n_fv = d.fresh();
    let n = d.kernel.fvar(n_fv);
    let proof = d.induct(
        &|d, candidate| statement(d, candidate, n),
        &|d| {
            let zero = d.zero();
            let fib_zero = d.fib(zero);
            let fib_n = d.fib(n);
            let common = d.gcd(fib_zero, fib_n);
            d.refl(common)
        },
        &|d, k, _ih| {
            prove_successor(
                d,
                k,
                n,
                addition,
                coprime,
                cancellation,
                antisymm,
                gcd_comm,
                gcd_left,
                gcd_right,
                dvd_gcd,
                dvd_mul,
                dvd_add,
                &additive_cancellation,
                mul_comm,
            )
        },
        m,
    );
    let proof = d.lam(n_fv, nat, proof);
    let proof = d.lam(m_fv, nat, proof);
    d.kernel
        .add_declaration(Declaration::Theorem {
            name: target,
            uparams: vec![],
            ty: goal,
            value: proof,
        })
        .map_err(|error| format!("exact Fibonacci GCD-shift rejected: {error:?}"))?;
    Ok(target)
}

fn statement(d: &mut Dev<'_>, m: ExprId, n: ExprId) -> ExprId {
    let fib_m = d.fib(m);
    let n_plus_m = d.add(n, m);
    let fib_shift = d.fib(n_plus_m);
    let fib_n = d.fib(n);
    let left = d.gcd(fib_m, fib_shift);
    let right = d.gcd(fib_m, fib_n);
    d.eq(left, right)
}

#[allow(
    clippy::many_single_char_names,
    clippy::similar_names,
    clippy::too_many_arguments
)]
fn prove_successor(
    d: &mut Dev<'_>,
    k: ExprId,
    n: ExprId,
    addition: NameId,
    coprime: NameId,
    cancellation: NameId,
    antisymm: NameId,
    gcd_comm: NameId,
    gcd_left: NameId,
    gcd_right: NameId,
    dvd_gcd: NameId,
    dvd_mul: NameId,
    dvd_add: NameId,
    additive_cancellation: &AdditiveCancellation,
    mul_comm: NameId,
) -> ExprId {
    let sk = d.succ(k);
    let sn = d.succ(n);
    let a = d.fib(sk);
    let b = d.fib(n);
    let f = d.fib(k);
    let x = d.fib(sn);
    let shifted = d.add(n, sk);
    let c = d.fib(shifted);
    let ax = d.mul(a, x);
    let fb = d.mul(f, b);
    let sum = d.add(ax, fb);
    let left = d.gcd(a, c);
    let right = d.gcd(a, b);
    let c_eq_sum = d.lemma(addition, &[n, k]);

    let right_a = d.lemma(gcd_left, &[a, b]);
    let right_b = d.lemma(gcd_right, &[a, b]);
    let right_ax = d.lemma(dvd_mul, &[right, a, x, right_a]);
    let bf = d.mul(b, f);
    let right_bf = d.lemma(dvd_mul, &[right, b, f, right_b]);
    let bf_eq_fb = d.lemma(mul_comm, &[b, f]);
    let right_fb = d.transport_dvd(right, bf, fb, right_bf, bf_eq_fb);
    let right_sum = d.lemma(dvd_add, &[right, ax, fb, right_ax, right_fb]);
    let sum_eq_c = d.symm(c, sum, c_eq_sum);
    let right_c = d.transport_dvd(right, sum, c, right_sum, sum_eq_c);
    let right_left = d.lemma(dvd_gcd, &[right, a, c, right_a, right_c]);

    let left_a = d.lemma(gcd_left, &[a, c]);
    let left_c = d.lemma(gcd_right, &[a, c]);
    let left_sum = d.transport_dvd(left, c, sum, left_c, c_eq_sum);
    let left_ax = d.lemma(dvd_mul, &[left, a, x, left_a]);
    let left_fb = match additive_cancellation {
        AdditiveCancellation::Direct(cancel) => {
            d.lemma(*cancel, &[left, ax, fb, left_ax, left_sum])
        }
        AdditiveCancellation::Iff(dvd_add_iff) => {
            let left_fb_ty = d.dvd(left, fb);
            let left_sum_ty = d.dvd(left, sum);
            let iff = d.lemma(*dvd_add_iff, &[left, ax, fb, left_ax]);
            let reverse = d.iff_reverse(left_fb_ty, left_sum_ty, iff);
            d.apply(reverse, &[left_sum])
        }
    };

    let coprime_f_a = d.lemma(coprime, &[k]);
    let f_a = d.gcd(f, a);
    let a_f = d.gcd(a, f);
    let comm = d.lemma(gcd_comm, &[f, a]);
    let zero = d.zero();
    let one = d.succ(zero);
    let motive = d.eq_motive(f_a, &|d, value| d.eq(value, one));
    let coprime_a_f = d.transport(f_a, motive, coprime_f_a, a_f, comm);
    let left_b = d.lemma(cancellation, &[a, f, b, left, coprime_a_f, left_a, left_fb]);
    let left_right = d.lemma(dvd_gcd, &[left, a, b, left_a, left_b]);
    d.lemma(antisymm, &[left, right, left_right, right_left])
}

fn path(args: &mut impl Iterator<Item = std::ffi::OsString>) -> Result<PathBuf, String> {
    args.next()
        .map(PathBuf::from)
        .ok_or_else(|| USAGE.to_owned())
}
fn import_bound(
    path: &Path,
    expected: &str,
    label: &str,
) -> Result<axeyum_lean_import::CompletedImport, String> {
    let bytes = fs::read(path).map_err(|error| format!("{label} read failed: {error}"))?;
    let actual = hex_sha256(&bytes);
    if actual != expected {
        return Err(format!(
            "{label} identity changed: expected {expected}, got {actual}"
        ));
    }
    import_ndjson(Cursor::new(bytes), ImportLimits::default())
        .map_err(|error| format!("{label} import failed: {error:?}"))
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
    Ok(
        json!({"name": kernel.display_name(theorem).to_string(), "declaration_sha256": canonical_declaration_sha256(kernel, theorem)?, "axiom_footprint": names(kernel, &kernel.axiom_footprint(theorem)), "direct_theorem_dependencies": names(kernel, &kernel.theorem_dependencies(theorem))}),
    )
}
fn transitive_dependencies(kernel: &Kernel, theorem: NameId) -> Vec<String> {
    let mut seen = std::collections::BTreeSet::new();
    let mut pending = vec![theorem];
    while let Some(current) = pending.pop() {
        for dependency in kernel.theorem_dependencies(current) {
            if seen.insert(kernel.display_name(dependency).to_string()) {
                pending.push(dependency);
            }
        }
    }
    seen.into_iter().collect()
}
fn find_name(kernel: &Kernel, expected: &str) -> Result<NameId, String> {
    optional_name(kernel, expected)?.ok_or_else(|| format!("declaration is absent: {expected}"))
}
fn optional_name(kernel: &Kernel, expected: &str) -> Result<Option<NameId>, String> {
    let found = kernel
        .environment()
        .iter()
        .filter_map(|(&name, _)| {
            (kernel.display_name(name).to_string() == expected).then_some(name)
        })
        .collect::<Vec<_>>();
    match found.as_slice() {
        [name] => Ok(Some(*name)),
        [] => Ok(None),
        _ => Err(format!("declaration is ambiguous: {expected}")),
    }
}
fn declaration_kind(declaration: &Declaration) -> &'static str {
    match declaration {
        Declaration::Axiom { .. } => "axiom",
        Declaration::Definition { .. } => "definition",
        Declaration::Theorem { .. } => "theorem",
        Declaration::Opaque { .. } => "opaque",
        Declaration::Quotient { .. } => "quotient",
        Declaration::Inductive { .. } => "inductive",
        Declaration::Constructor { .. } => "constructor",
        Declaration::Recursor { .. } => "recursor",
    }
}
fn theorem_type(kernel: &Kernel, name: NameId) -> Result<ExprId, String> {
    match kernel.environment().get(name) {
        Some(Declaration::Theorem { ty, .. }) => Ok(*ty),
        _ => Err(format!(
            "declaration is not a theorem: {}",
            kernel.display_name(name)
        )),
    }
}
fn nested_name(kernel: &mut Kernel, parts: &[&str]) -> NameId {
    parts
        .iter()
        .fold(kernel.anon(), |prefix, part| kernel.name_str(prefix, *part))
}
fn names(kernel: &Kernel, values: &[NameId]) -> Vec<String> {
    values
        .iter()
        .map(|&name| kernel.display_name(name).to_string())
        .collect()
}
fn hex_sha256(bytes: &[u8]) -> String {
    let mut out = String::with_capacity(64);
    for byte in Sha256::digest(bytes) {
        write!(&mut out, "{byte:02x}").expect("String writes cannot fail");
    }
    out
}
