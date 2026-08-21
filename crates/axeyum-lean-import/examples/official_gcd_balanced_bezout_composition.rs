// Close the generic official-gcd balanced-Bezout theorem without crossing
// the measured native/official `WellFounded` representation boundary.

use std::fmt::Write as _;
use std::fs;
use std::io::Cursor;
use std::path::{Path, PathBuf};

use axeyum_lean_import::{
    ImportLimits, ReusedTypeCompatibility, canonical_declaration_sha256,
    checked_reused_declaration_compatibility, compose_checked_theorem_slice, import_ndjson,
    specialize_checked_theorem, verify_checked_theorem_composition,
    verify_checked_theorem_specialization,
};
use axeyum_lean_kernel::{Declaration, Kernel, NameId, build_nat_prelude};
use serde_json::{Value, json};
use sha2::{Digest, Sha256};

const TARGET_STREAM_SHA256: &str =
    "6afa79d79481403d3e3273ea3eea26b4d1194762f9bd623ec019f8e821323cfd";
const MOD_ADAPTER_STREAM_SHA256: &str =
    "6e99d4ae83b3916f8ee36c541bac18fc91b9f922252ca0af1cf658578b4e20db";
const ZERO_LEFT_STREAM_SHA256: &str =
    "824399899916c72329f201c0ea8c1b0fe25315ea013c4f392586668f67f606a0";
const SUCCESSOR_STREAM_SHA256: &str =
    "2af40b2c7d89a0959bbe3018da60841ea1dc933ae2f40112ae84d95feab6044c";
const GENERIC_STREAM_SHA256: &str =
    "c106a1e03a329535042f17f6a9d3cf408361e4b4691b5ea6bac4d1a71186bb56";
const CLEAN_MUL_STREAM_SHA256: &str =
    "d157386bf359aa25d9f48ca361010a211598fb4d563384a608886d21044d63bc";
const RESIDUAL_STREAM_SHA256: &str =
    "477f006772dd6e5a968f09ebec2c05778044b3727b20129e117730dd3927716f";
const ALL_NAT_ADAPTER_STREAM_SHA256: &str =
    "9f710f7b64afffe7c021cadfd7ec1dae34bbab1d059d8335628bb4d7c2547558";

const MOD_LT_ADAPTER: &str = "Axeyum.Autogenesis.modLtSucc";
const MOD_LT_ADAPTER_SHA256: &str =
    "c7b73f3e5b22dd1f05c631e10f033377d5d62a2747a80691f238c7feba3808fa";
const ZERO_LEFT: &str = "Axeyum.Autogenesis.nat_gcd_zero_left";
const ZERO_LEFT_SHA256: &str = "e4f6c7e3971f5751bd1e889e9bfc28b7035d9f47204f7aafa5efc06b97cf3555";
const SUCCESSOR: &str = "Axeyum.Autogenesis.nat_gcd_succ";
const SUCCESSOR_SHA256: &str = "1a9cf6e4ef4dc54a298214571515e7682a6265d9db7008b7cf1f8b3c38d11f16";
const GENERIC: &str = "Axeyum.Autogenesis.officialGcdBalancedBezoutCleanV1";
const GENERIC_SHA256: &str = "feb1c3e41dd2f745261002b3876ddab750db5777226956ddbb07d805b4abc9ec";

const MOD_LT_CLOSED: &str = "Axeyum.Autogenesis.officialModLtSuccV1";
const SUCCESSOR_CLOSED: &str = "Axeyum.Autogenesis.officialNatGcdSuccClosedV1";
const BALANCED_BEZOUT_CLOSED: &str =
    "Axeyum.Autogenesis.officialGcdBalancedBezoutClosedOfficialKernelV1";
const MUL_ASSOC_LEAF: &str = "Axeyum.Autogenesis.balancedBezoutMulAssocLeafV1";
const RIGHT_DISTRIB_LEAF: &str = "Axeyum.Autogenesis.balancedBezoutRightDistribLeafV1";
const RESIDUAL_CANCELLATION: &str =
    "Axeyum.Autogenesis.coprimeFactorDivisibilityCancellationResidualV2";
const ALL_NAT_ADAPTER: &str = "Axeyum.Autogenesis.dvdAddCancelAllNatAdapterV1";
const POSITIVE_CANCELLATION: &str = "Nat.dvd_add_right_cancel_of_pos";
const ALL_NAT_CLOSED: &str = "Axeyum.Autogenesis.dvdAddCancelAllNatClosedV1";
const OFFICIAL_CANCELLATION: &str =
    "Axeyum.Autogenesis.officialCoprimeFactorDivisibilityCancellationV1";

const USAGE: &str = "usage: official_coprime_factor_cancellation_composition <target-base> <mod-lt-adapter> <zero-left> <successor> <generic-balanced-bezout> <clean-mul-leaves> <residual-cancellation> <all-nat-adapter>";

fn main() {
    if let Err(error) = run() {
        eprintln!("official-gcd-balanced-bezout-composition: {error}");
        std::process::exit(1);
    }
}

#[allow(clippy::too_many_lines)]
fn run() -> Result<(), String> {
    let mut arguments = std::env::args_os().skip(1);
    let target_path = required_path(&mut arguments)?;
    let adapter_path = required_path(&mut arguments)?;
    let zero_left_path = required_path(&mut arguments)?;
    let successor_path = required_path(&mut arguments)?;
    let generic_path = required_path(&mut arguments)?;
    let clean_mul_path = required_path(&mut arguments)?;
    let residual_path = required_path(&mut arguments)?;
    let all_nat_adapter_path = required_path(&mut arguments)?;
    if arguments.next().is_some() {
        return Err(USAGE.to_owned());
    }

    let target = import_bound(&target_path, "target-base", TARGET_STREAM_SHA256)?;
    let adapter = import_bound(&adapter_path, "mod-lt-adapter", MOD_ADAPTER_STREAM_SHA256)?;
    let zero_left = import_bound(&zero_left_path, "zero-left", ZERO_LEFT_STREAM_SHA256)?;
    let successor = import_bound(&successor_path, "successor", SUCCESSOR_STREAM_SHA256)?;
    let generic = import_bound(
        &generic_path,
        "generic-balanced-bezout",
        GENERIC_STREAM_SHA256,
    )?;
    let clean_mul = import_bound(&clean_mul_path, "clean-mul-leaves", CLEAN_MUL_STREAM_SHA256)?;
    let residual = import_bound(
        &residual_path,
        "residual-cancellation",
        RESIDUAL_STREAM_SHA256,
    )?;
    let all_nat_adapter = import_bound(
        &all_nat_adapter_path,
        "all-nat-adapter",
        ALL_NAT_ADAPTER_STREAM_SHA256,
    )?;
    for (label, imported) in [
        ("target-base", &target),
        ("mod-lt-adapter", &adapter),
        ("zero-left", &zero_left),
        ("successor", &successor),
        ("generic-balanced-bezout", &generic),
        ("clean-mul-leaves", &clean_mul),
        ("residual-cancellation", &residual),
        ("all-nat-adapter", &all_nat_adapter),
    ] {
        if !imported.report().axioms.is_empty() {
            return Err(format!("{label} stream is not proof-isolated"));
        }
    }

    require_identity(zero_left.kernel(), ZERO_LEFT, ZERO_LEFT_SHA256)?;
    require_identity(successor.kernel(), SUCCESSOR, SUCCESSOR_SHA256)?;
    require_identity(adapter.kernel(), MOD_LT_ADAPTER, MOD_LT_ADAPTER_SHA256)?;
    require_identity(generic.kernel(), GENERIC, GENERIC_SHA256)?;
    require_identity(
        clean_mul.kernel(),
        MUL_ASSOC_LEAF,
        "3e1ef3dc51f2702b9b457e5621457542c07757b30a57cede7db9e5b7273f7c00",
    )?;
    require_identity(
        clean_mul.kernel(),
        RIGHT_DISTRIB_LEAF,
        "7d41f955bf36b0825b925ec0d1d31b0df7551c0b413b0ed6cca4fcef1d833f05",
    )?;
    require_identity(
        residual.kernel(),
        RESIDUAL_CANCELLATION,
        "ce4e5a785f115f8c6f858d63df218db2470dca1ba436b2faa0dee6d1fc2c18ef",
    )?;
    require_identity(
        all_nat_adapter.kernel(),
        ALL_NAT_ADAPTER,
        "2ab68f18df024f92a1f344e2f323737b7d69293175d6511b99af797be22280e4",
    )?;

    let mod_lt_reuse =
        checked_reused_declaration_compatibility(target.kernel(), generic.kernel(), "Nat.mod_lt")
            .map_err(|error| format!("Nat.mod_lt checked reuse declined: {error:?}"))?;
    if mod_lt_reuse.source_declaration_sha256 != mod_lt_reuse.target_declaration_sha256 {
        return Err(format!(
            "Nat.mod_lt declaration identity differs across pinned kernels: source {}, target {}",
            mod_lt_reuse.source_declaration_sha256, mod_lt_reuse.target_declaration_sha256,
        ));
    }
    if mod_lt_reuse.compatibility != ReusedTypeCompatibility::KernelTypeShape {
        return Err(format!(
            "Nat.mod_lt reuse is not exact kernel-type-shape compatibility: {}",
            mod_lt_reuse.compatibility.as_str(),
        ));
    }
    let with_adapter = compose_root(
        adapter.kernel(),
        generic.kernel(),
        MOD_LT_ADAPTER,
        "mod-lt-adapter",
    )?;
    let with_zero = compose_root(
        zero_left.kernel(),
        with_adapter.kernel(),
        ZERO_LEFT,
        "zero-left",
    )?;
    let with_successor = compose_root(
        successor.kernel(),
        with_zero.kernel(),
        SUCCESSOR,
        "successor",
    )?;

    let mut mod_prepared = with_successor.kernel().clone();
    let mod_adapter_name = find_name(&mod_prepared, MOD_LT_ADAPTER)?;
    let nat_mod_lt = find_name(&mod_prepared, "Nat.mod_lt")?;
    let mod_closed_name = nested_name(
        &mut mod_prepared,
        &["Axeyum", "Autogenesis", "officialModLtSuccV1"],
    );
    let mod_closed = specialize_checked_theorem(
        &mod_prepared,
        mod_adapter_name,
        &[nat_mod_lt],
        mod_closed_name,
    )
    .map_err(|error| format!("modulo-bound specialization declined: {error:?}"))?;
    verify_checked_theorem_specialization(
        &mod_prepared,
        mod_closed.kernel(),
        mod_adapter_name,
        &[nat_mod_lt],
        mod_closed_name,
        mod_closed.receipt(),
    )
    .map_err(|error| format!("modulo-bound specialization did not replay: {error:?}"))?;
    let mod_evidence = theorem_evidence(mod_closed.kernel(), mod_closed_name)?;
    require_empty_footprint(&mod_evidence, MOD_LT_CLOSED)?;
    require_dependencies(
        &mod_evidence,
        &[MOD_LT_ADAPTER.to_owned(), "Nat.mod_lt".to_owned()],
        MOD_LT_CLOSED,
    )?;

    let mut successor_prepared = mod_closed.kernel().clone();
    let successor_name = find_name(&successor_prepared, SUCCESSOR)?;
    let mod_argument = find_name(&successor_prepared, MOD_LT_CLOSED)?;
    let successor_closed_name = nested_name(
        &mut successor_prepared,
        &["Axeyum", "Autogenesis", "officialNatGcdSuccClosedV1"],
    );
    let successor_closed = specialize_checked_theorem(
        &successor_prepared,
        successor_name,
        &[mod_argument],
        successor_closed_name,
    )
    .map_err(|error| format!("successor specialization declined: {error:?}"))?;
    verify_checked_theorem_specialization(
        &successor_prepared,
        successor_closed.kernel(),
        successor_name,
        &[mod_argument],
        successor_closed_name,
        successor_closed.receipt(),
    )
    .map_err(|error| format!("successor specialization did not replay: {error:?}"))?;
    let successor_evidence = theorem_evidence(successor_closed.kernel(), successor_closed_name)?;
    require_empty_footprint(&successor_evidence, SUCCESSOR_CLOSED)?;
    require_dependencies(
        &successor_evidence,
        &[SUCCESSOR.to_owned(), MOD_LT_CLOSED.to_owned()],
        SUCCESSOR_CLOSED,
    )?;

    let mut closed_prepared = successor_closed.kernel().clone();
    let generic_name = find_name(&closed_prepared, GENERIC)?;
    let zero_argument = find_name(&closed_prepared, ZERO_LEFT)?;
    let successor_argument = find_name(&closed_prepared, SUCCESSOR_CLOSED)?;
    let closed_name = nested_name(
        &mut closed_prepared,
        &[
            "Axeyum",
            "Autogenesis",
            "officialGcdBalancedBezoutClosedOfficialKernelV1",
        ],
    );
    let closed = specialize_checked_theorem(
        &closed_prepared,
        generic_name,
        &[zero_argument, successor_argument],
        closed_name,
    )
    .map_err(|error| format!("balanced-Bezout specialization declined: {error:?}"))?;
    verify_checked_theorem_specialization(
        &closed_prepared,
        closed.kernel(),
        generic_name,
        &[zero_argument, successor_argument],
        closed_name,
        closed.receipt(),
    )
    .map_err(|error| format!("balanced-Bezout specialization did not replay: {error:?}"))?;
    let closed_evidence = theorem_evidence(closed.kernel(), closed_name)?;
    require_empty_footprint(&closed_evidence, BALANCED_BEZOUT_CLOSED)?;
    require_dependencies(
        &closed_evidence,
        &[
            ZERO_LEFT.to_owned(),
            GENERIC.to_owned(),
            SUCCESSOR_CLOSED.to_owned(),
        ],
        BALANCED_BEZOUT_CLOSED,
    )?;

    let mul_assoc_reuse = checked_reused_declaration_compatibility(
        clean_mul.kernel(),
        closed.kernel(),
        MUL_ASSOC_LEAF,
    )
    .map_err(|error| format!("multiplication-associativity checked reuse declined: {error:?}"))?;
    require_exact_kernel_type_shape_reuse(&mul_assoc_reuse, MUL_ASSOC_LEAF)?;
    let right_distrib_reuse = checked_reused_declaration_compatibility(
        clean_mul.kernel(),
        closed.kernel(),
        RIGHT_DISTRIB_LEAF,
    )
    .map_err(|error| format!("right-distributivity checked reuse declined: {error:?}"))?;
    require_exact_kernel_type_shape_reuse(&right_distrib_reuse, RIGHT_DISTRIB_LEAF)?;
    let with_residual = compose_root(
        residual.kernel(),
        closed.kernel(),
        RESIDUAL_CANCELLATION,
        "residual-cancellation",
    )?;
    let with_all_nat_adapter = compose_root(
        all_nat_adapter.kernel(),
        with_residual.kernel(),
        ALL_NAT_ADAPTER,
        "all-nat-adapter",
    )?;
    let mut native = Kernel::new();
    let native_prelude = build_nat_prelude(&mut native)
        .map_err(|error| format!("native Nat prelude build failed: {error:?}"))?;
    if native
        .display_name(native_prelude.dvd_add_right_cancel_of_pos)
        .to_string()
        != POSITIVE_CANCELLATION
    {
        return Err("native positive-cancellation identity changed".to_owned());
    }
    if !native
        .axiom_footprint(native_prelude.dvd_add_right_cancel_of_pos)
        .is_empty()
    {
        return Err("native positive cancellation reaches assumptions".to_owned());
    }
    let with_positive = compose_root(
        &native,
        with_all_nat_adapter.kernel(),
        POSITIVE_CANCELLATION,
        "native-positive-cancellation",
    )?;

    let mut all_nat_prepared = with_positive.kernel().clone();
    let adapter_name = find_name(&all_nat_prepared, ALL_NAT_ADAPTER)?;
    let positive_name = find_name(&all_nat_prepared, POSITIVE_CANCELLATION)?;
    let all_nat_closed_name = nested_name(
        &mut all_nat_prepared,
        &["Axeyum", "Autogenesis", "dvdAddCancelAllNatClosedV1"],
    );
    let all_nat_closed = specialize_checked_theorem(
        &all_nat_prepared,
        adapter_name,
        &[positive_name],
        all_nat_closed_name,
    )
    .map_err(|error| format!("all-Nat cancellation specialization declined: {error:?}"))?;
    verify_checked_theorem_specialization(
        &all_nat_prepared,
        all_nat_closed.kernel(),
        adapter_name,
        &[positive_name],
        all_nat_closed_name,
        all_nat_closed.receipt(),
    )
    .map_err(|error| format!("all-Nat cancellation specialization did not replay: {error:?}"))?;
    let all_nat_evidence = theorem_evidence(all_nat_closed.kernel(), all_nat_closed_name)?;
    require_empty_footprint(&all_nat_evidence, ALL_NAT_CLOSED)?;
    require_dependencies(
        &all_nat_evidence,
        &[ALL_NAT_ADAPTER.to_owned(), POSITIVE_CANCELLATION.to_owned()],
        ALL_NAT_CLOSED,
    )?;

    let mut cancellation_prepared = all_nat_closed.kernel().clone();
    let residual_name = find_name(&cancellation_prepared, RESIDUAL_CANCELLATION)?;
    let cancellation_arguments = [
        find_name(&cancellation_prepared, BALANCED_BEZOUT_CLOSED)?,
        find_name(&cancellation_prepared, MUL_ASSOC_LEAF)?,
        find_name(&cancellation_prepared, RIGHT_DISTRIB_LEAF)?,
        find_name(&cancellation_prepared, ALL_NAT_CLOSED)?,
    ];
    let official_cancellation_name = nested_name(
        &mut cancellation_prepared,
        &[
            "Axeyum",
            "Autogenesis",
            "officialCoprimeFactorDivisibilityCancellationV1",
        ],
    );
    let official_cancellation = specialize_checked_theorem(
        &cancellation_prepared,
        residual_name,
        &cancellation_arguments,
        official_cancellation_name,
    )
    .map_err(|error| format!("official cancellation specialization declined: {error:?}"))?;
    verify_checked_theorem_specialization(
        &cancellation_prepared,
        official_cancellation.kernel(),
        residual_name,
        &cancellation_arguments,
        official_cancellation_name,
        official_cancellation.receipt(),
    )
    .map_err(|error| format!("official cancellation specialization did not replay: {error:?}"))?;
    let official_cancellation_evidence =
        theorem_evidence(official_cancellation.kernel(), official_cancellation_name)?;
    require_empty_footprint(&official_cancellation_evidence, OFFICIAL_CANCELLATION)?;
    require_dependencies(
        &official_cancellation_evidence,
        &[
            MUL_ASSOC_LEAF.to_owned(),
            RIGHT_DISTRIB_LEAF.to_owned(),
            RESIDUAL_CANCELLATION.to_owned(),
            ALL_NAT_CLOSED.to_owned(),
            BALANCED_BEZOUT_CLOSED.to_owned(),
        ],
        OFFICIAL_CANCELLATION,
    )?;

    let output = json!({
        "schema_version": 1,
        "kind": "axeyum-official-coprime-factor-cancellation-exact-reuse-composition",
        "state": "official-coprime-factor-cancellation-reconstructed-empty-footprint",
        "input_streams": {
            "target_base_sha256": TARGET_STREAM_SHA256,
            "mod_lt_adapter_sha256": MOD_ADAPTER_STREAM_SHA256,
            "zero_left_sha256": ZERO_LEFT_STREAM_SHA256,
            "successor_sha256": SUCCESSOR_STREAM_SHA256,
            "generic_balanced_bezout_sha256": GENERIC_STREAM_SHA256,
            "clean_mul_leaves_sha256": CLEAN_MUL_STREAM_SHA256,
            "residual_cancellation_sha256": RESIDUAL_STREAM_SHA256,
            "all_nat_adapter_sha256": ALL_NAT_ADAPTER_STREAM_SHA256,
        },
        "reused_declarations": {
            "Nat.mod_lt": {
                "source_declaration_sha256": mod_lt_reuse.source_declaration_sha256,
                "target_declaration_sha256": mod_lt_reuse.target_declaration_sha256,
                "source_type_shape_sha256": mod_lt_reuse.source_type_shape_sha256,
                "target_type_shape_sha256": mod_lt_reuse.target_type_shape_sha256,
                "compatibility": mod_lt_reuse.compatibility.as_str(),
            },
            MUL_ASSOC_LEAF: {
                "source_declaration_sha256": mul_assoc_reuse.source_declaration_sha256,
                "target_declaration_sha256": mul_assoc_reuse.target_declaration_sha256,
                "source_type_shape_sha256": mul_assoc_reuse.source_type_shape_sha256,
                "target_type_shape_sha256": mul_assoc_reuse.target_type_shape_sha256,
                "compatibility": mul_assoc_reuse.compatibility.as_str(),
            },
            RIGHT_DISTRIB_LEAF: {
                "source_declaration_sha256": right_distrib_reuse.source_declaration_sha256,
                "target_declaration_sha256": right_distrib_reuse.target_declaration_sha256,
                "source_type_shape_sha256": right_distrib_reuse.source_type_shape_sha256,
                "target_type_shape_sha256": right_distrib_reuse.target_type_shape_sha256,
                "compatibility": right_distrib_reuse.compatibility.as_str(),
            },
        },
        "compositions": {
            "mod_lt_adapter_receipt_sha256": with_adapter.receipt().receipt_sha256,
            "zero_left_receipt_sha256": with_zero.receipt().receipt_sha256,
            "successor_receipt_sha256": with_successor.receipt().receipt_sha256,
            "residual_cancellation_receipt_sha256": with_residual.receipt().receipt_sha256,
            "all_nat_adapter_receipt_sha256": with_all_nat_adapter.receipt().receipt_sha256,
            "native_positive_cancellation_receipt_sha256": with_positive.receipt().receipt_sha256,
        },
        "composition_base": "generic-balanced-bezout-kernel",
        "generic_composition_operations": 0,
        "specializations": {
            "mod_lt_succ": {
                "receipt_sha256": mod_closed.receipt().receipt_sha256,
                "evidence": mod_evidence,
            },
            "gcd_succ": {
                "receipt_sha256": successor_closed.receipt().receipt_sha256,
                "evidence": successor_evidence,
            },
            "balanced_bezout": {
                "receipt_sha256": closed.receipt().receipt_sha256,
                "evidence": closed_evidence,
            },
            "all_nat_cancellation": {
                "receipt_sha256": all_nat_closed.receipt().receipt_sha256,
                "evidence": all_nat_evidence,
            },
            "official_coprime_factor_cancellation": {
                "receipt_sha256": official_cancellation.receipt().receipt_sha256,
                "evidence": official_cancellation_evidence,
            },
        },
        "accepted_argument_identities": {
            "zero_left": ZERO_LEFT_SHA256,
            "successor_generic": SUCCESSOR_SHA256,
            "generic_balanced_bezout": GENERIC_SHA256,
        },
        "rendered_material": {"proof_terms": 0, "theorem_types": 0, "theorem_values": 0},
        "proof_search_invocations": 0,
        "executor_invocations": 0,
        "exact_fibonacci_target_submissions": 0,
        "fact_status_changes": 0,
        "evaluation_credit": 0,
        "ledger_writes": 0,
    });
    println!(
        "{}",
        serde_json::to_string_pretty(&output).map_err(|error| error.to_string())?
    );
    Ok(())
}

fn required_path(
    arguments: &mut impl Iterator<Item = std::ffi::OsString>,
) -> Result<PathBuf, String> {
    arguments
        .next()
        .map(PathBuf::from)
        .ok_or_else(|| USAGE.to_owned())
}

fn import_bound(
    path: &Path,
    label: &str,
    expected_sha256: &str,
) -> Result<axeyum_lean_import::CompletedImport, String> {
    let bytes = fs::read(path).map_err(|error| format!("{label} stream read failed: {error}"))?;
    let actual_sha256 = hex_sha256(&bytes);
    if actual_sha256 != expected_sha256 {
        return Err(format!(
            "{label} stream identity changed: expected {expected_sha256}, got {actual_sha256}"
        ));
    }
    import_ndjson(Cursor::new(bytes), ImportLimits::default())
        .map_err(|error| format!("{label} stream import failed: {error:?}"))
}

fn compose_root(
    source: &Kernel,
    target: &Kernel,
    root: &str,
    label: &str,
) -> Result<axeyum_lean_import::CompletedTheoremComposition, String> {
    let composed = compose_checked_theorem_slice(source, target, &[root])
        .map_err(|error| format!("{label} composition declined: {error:?}"))?;
    verify_checked_theorem_composition(source, target, composed.kernel(), composed.receipt())
        .map_err(|error| format!("{label} composition did not replay: {error:?}"))?;
    for theorem in &composed.receipt().added_theorems {
        if !theorem.axiom_footprint.is_empty() {
            return Err(format!(
                "{label} composition added assumption-bearing theorem {}: {:?}",
                theorem.name, theorem.axiom_footprint
            ));
        }
    }
    Ok(composed)
}

fn theorem_evidence(kernel: &Kernel, name: NameId) -> Result<Value, String> {
    if !matches!(
        kernel.environment().get(name),
        Some(Declaration::Theorem { .. })
    ) {
        return Err(format!("{} is not a theorem", kernel.display_name(name)));
    }
    let mut footprint = kernel
        .axiom_footprint(name)
        .into_iter()
        .map(|dependency| kernel.display_name(dependency).to_string())
        .collect::<Vec<_>>();
    footprint.sort();
    let mut dependencies = kernel
        .theorem_dependencies(name)
        .into_iter()
        .map(|dependency| kernel.display_name(dependency).to_string())
        .collect::<Vec<_>>();
    dependencies.sort();
    Ok(json!({
        "name": kernel.display_name(name).to_string(),
        "declaration_sha256": canonical_declaration_sha256(kernel, name)?,
        "axiom_footprint": footprint,
        "direct_theorem_dependencies": dependencies,
    }))
}

fn require_empty_footprint(evidence: &Value, label: &str) -> Result<(), String> {
    if evidence["axiom_footprint"] != json!([]) {
        return Err(format!("{label} reaches assumptions"));
    }
    Ok(())
}

fn require_dependencies(evidence: &Value, expected: &[String], label: &str) -> Result<(), String> {
    if evidence["direct_theorem_dependencies"] != json!(expected) {
        return Err(format!(
            "{label} direct dependencies changed: {}",
            evidence["direct_theorem_dependencies"]
        ));
    }
    Ok(())
}

fn require_identity(kernel: &Kernel, name: &str, expected_sha256: &str) -> Result<(), String> {
    let id = find_name(kernel, name)?;
    let actual_sha256 = canonical_declaration_sha256(kernel, id)?;
    if actual_sha256 != expected_sha256 {
        return Err(format!(
            "{name} identity changed: expected {expected_sha256}, got {actual_sha256}"
        ));
    }
    Ok(())
}

fn require_exact_kernel_type_shape_reuse(
    receipt: &axeyum_lean_import::ReusedDeclarationReceipt,
    name: &str,
) -> Result<(), String> {
    if receipt.source_declaration_sha256 != receipt.target_declaration_sha256 {
        return Err(format!(
            "{name} declaration identity differs across pinned kernels: source {}, target {}",
            receipt.source_declaration_sha256, receipt.target_declaration_sha256,
        ));
    }
    if receipt.compatibility != ReusedTypeCompatibility::KernelTypeShape {
        return Err(format!(
            "{name} reuse is not exact kernel-type-shape compatibility: {}",
            receipt.compatibility.as_str(),
        ));
    }
    Ok(())
}

fn find_name(kernel: &Kernel, expected: &str) -> Result<NameId, String> {
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

fn nested_name(kernel: &mut Kernel, parts: &[&str]) -> NameId {
    parts
        .iter()
        .fold(kernel.anon(), |prefix, part| kernel.name_str(prefix, *part))
}

fn hex_sha256(bytes: &[u8]) -> String {
    let mut digest = String::with_capacity(64);
    for byte in Sha256::digest(bytes) {
        write!(&mut digest, "{byte:02x}").expect("writing a digest into a String cannot fail");
    }
    digest
}
