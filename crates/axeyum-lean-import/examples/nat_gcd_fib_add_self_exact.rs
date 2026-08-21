//! Reconstruct exact `Nat.gcd_fib_add_self` from four sealed proof capsules.

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
const TARGET: &str = "Nat.gcd_fib_add_self";
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
    let comm = declare_clean_gcd_comm(&mut kernel)?;
    require_empty(&kernel, comm, CLEAN_GCD_COMM)?;
    let theorem = declare_target(&mut kernel, goal)?;
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
        find_name(&kernel, COPRIME_GCD_SUCC_LEAF)?,
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
        COPRIME_GCD_SUCC_LEAF,
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
        let body = self.kernel.abstract_fvars(body, &[fv]);
        self.kernel.lam(self.anon, ty, body, BinderInfo::Default)
    }
    fn pi(&mut self, fv: u64, ty: ExprId, body: ExprId) -> ExprId {
        let body = self.kernel.abstract_fvars(body, &[fv]);
        self.kernel.pi(self.anon, ty, body, BinderInfo::Default)
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

fn declare_clean_gcd_comm(kernel: &mut Kernel) -> Result<NameId, String> {
    let target = nested_name(kernel, &["Axeyum", "Autogenesis", "gcdCommCleanV1"]);
    let mut d = Dev::new(kernel)?;
    let antisymm = d.exact(CLEAN_ANTISYMM)?;
    let gcd_left = d.exact("Nat.gcd_dvd_left")?;
    let gcd_right = d.exact("Nat.gcd_dvd_right")?;
    let dvd_gcd = d.exact("Nat.dvd_gcd")?;
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

fn declare_target(kernel: &mut Kernel, goal: ExprId) -> Result<NameId, String> {
    let target = nested_name(kernel, &["Nat", "gcd_fib_add_self"]);
    let mut d = Dev::new(kernel)?;
    let addition = d.exact(ADDITION)?;
    let coprime = d.exact(COPRIME)?;
    let cancellation = d.exact(CANCELLATION)?;
    let antisymm = d.exact(CLEAN_ANTISYMM)?;
    let gcd_comm = d.exact(CLEAN_GCD_COMM)?;
    let gcd_left = d.exact("Nat.gcd_dvd_left")?;
    let gcd_right = d.exact("Nat.gcd_dvd_right")?;
    let dvd_gcd = d.exact("Nat.dvd_gcd")?;
    let dvd_mul = d.exact("Nat.dvd_mul_right_of_dvd")?;
    let dvd_add = d.exact("Nat.dvd_add")?;
    let dvd_add_iff = d.exact("Nat.dvd_add_iff_right")?;
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
                dvd_add_iff,
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
    dvd_add_iff: NameId,
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
    let left_fb_ty = d.dvd(left, fb);
    let left_sum_ty = d.dvd(left, sum);
    let iff = d.lemma(dvd_add_iff, &[left, ax, fb, left_ax]);
    let reverse = d.iff_reverse(left_fb_ty, left_sum_ty, iff);
    let left_fb = d.apply(reverse, &[left_sum]);

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
