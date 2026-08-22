//! Construct exact `Int.gcd_fib` from two sealed roots and a tiny `Int.gcd`.

use std::fmt::Write as _;
use std::fs;
use std::io::Cursor;
use std::path::{Path, PathBuf};

use axeyum_lean_import::{
    ImportLimits, canonical_declaration_sha256, compose_checked_theorem_slice, import_ndjson,
    verify_checked_theorem_composition,
};
use axeyum_lean_kernel::{
    BinderInfo, Declaration, ExprId, Kernel, Lean4ExportMetadata, NameId, ReducibilityHint,
};
use serde_json::{Value, json};
use sha2::{Digest, Sha256};

const HASHES: [&str; 2] = [
    "1ec10d475fb3c77fea3353036e2a09f70abf88f03402a2912407c71b26e3b7e4",
    "8ac3c35874540a10e5fa393c65f3ad313a6cf6a06303cec68fec3ec45d0f04cd",
];
const BRIDGE: &str = "Axeyum.Autogenesis.intFibNatAbsV1";
const FIB_GCD: &str = "Nat.fib_gcd";
const INT_GCD: &str = "Int.gcd";
const INT_GCD_DEF: &str = "Int.gcd_def";
const TARGET: &str = "Int.gcd_fib";
const USAGE: &str = "usage: int_gcd_fib_exact <int-fib-natabs> <nat-fib-gcd> <output>";

fn main() {
    if let Err(error) = run() {
        eprintln!("int-gcd-fib-exact: {error}");
        std::process::exit(1);
    }
}

/// Construct the inverse presentation theorem `Int.fib_gcd` from this
/// driver's sealed `Int.gcd_fib` capsule. Kept here so both directions share
/// the exact kernel-level equality constructors instead of duplicating them.
pub(crate) fn run_int_fib_gcd_exact() -> Result<(), String> {
    const INPUT_SHA256: &str = "b1ce136473ead161243e7cdc053f3a8e0dab81a8e253c364171e839f22fd86f6";
    const INPUT_ROOT_SHA256: &str =
        "44660dc7f15cda1b469f99e349f4b874afca9dbca24bcfc5c847ca226ccc357f";
    const NATCAST_SHA256: &str = "73b8742709bbb1b91780f41ff4a475b5b3f0b1c2981999c868b53fc38334bea3";
    const USAGE_FIB_GCD: &str = "usage: int_fib_gcd_exact <int-gcd-fib> <output>";

    let mut arguments = std::env::args_os().skip(1);
    let input = arguments
        .next()
        .map(PathBuf::from)
        .ok_or_else(|| USAGE_FIB_GCD.to_owned())?;
    let output = arguments
        .next()
        .map(PathBuf::from)
        .ok_or_else(|| USAGE_FIB_GCD.to_owned())?;
    if arguments.next().is_some() || output.exists() {
        return Err(USAGE_FIB_GCD.to_owned());
    }

    let imported = import_bound(&input, INPUT_SHA256, "integer gcd Fibonacci capsule")?;
    if !imported.report().axioms.is_empty() {
        return Err("the input stream reaches assumptions".to_owned());
    }
    require_bound_root(imported.kernel(), "Int.gcd_fib", INPUT_ROOT_SHA256)?;
    require_bound_root(imported.kernel(), "Int.fib_natCast", NATCAST_SHA256)?;

    let mut kernel = imported.kernel().clone();
    add_int_fib_gcd(&mut kernel)?;
    let target = find_name(&kernel, "Int.fib_gcd")?;
    require_empty(&kernel, target, "Int.fib_gcd")?;
    let target_evidence = evidence(&kernel, target)?;
    let expected_dependencies = ["Eq.symm", "Eq.trans", "Int.fib_natCast", "Int.gcd_fib"];
    if names(&kernel, &kernel.theorem_dependencies(target)) != sorted(&expected_dependencies) {
        return Err(format!(
            "exact target dependency set changed: {:?}",
            names(&kernel, &kernel.theorem_dependencies(target))
        ));
    }

    let bytes = kernel
        .render_lean4export_ndjson_roots(&Lean4ExportMetadata::axeyum("4.30.0"), &[target])
        .map_err(|error| format!("target export failed: {error}"))?;
    for pass in 1..=2 {
        let fresh = import_ndjson(Cursor::new(bytes.as_bytes()), ImportLimits::default())
            .map_err(|error| format!("fresh target import {pass} failed: {error:?}"))?;
        let fresh_target = find_name(fresh.kernel(), "Int.fib_gcd")?;
        if evidence(fresh.kernel(), fresh_target)? != target_evidence {
            return Err(format!("fresh target import {pass} changed evidence"));
        }
    }
    fs::write(&output, &bytes).map_err(|error| format!("target write failed: {error}"))?;

    println!(
        "{}",
        serde_json::to_string_pretty(&json!({
            "schema_version": 1,
            "kind": "axeyum-int-fib-gcd-exact",
            "state": "exact-target-constructed-exported-and-twice-reimported-empty-footprint",
            "input_sha256": INPUT_SHA256,
            "target": target_evidence,
            "capsule": {"path": output, "bytes": bytes.len(), "sha256": hex_sha256(bytes.as_bytes()), "fresh_imports": 2},
            "execution": {"complete_invocations": 1, "input_stream_reads": 1, "target_theorem_submissions": 1, "target_exports": 1, "fresh_target_imports": 2, "retries": 0, "ledger_writes": 0},
            "rendered_material": {"proof_terms": 0, "theorem_types": 0, "theorem_values": 0}
        }))
        .map_err(|error| error.to_string())?
    );
    Ok(())
}

#[allow(clippy::too_many_lines)]
fn run() -> Result<(), String> {
    let mut arguments = std::env::args_os().skip(1);
    let paths = (0..3)
        .map(|_| path(&mut arguments))
        .collect::<Result<Vec<_>, _>>()?;
    if arguments.next().is_some() || paths[2].exists() {
        return Err(USAGE.to_owned());
    }
    let bridge_import = import_bound(&paths[0], HASHES[0], "integer Fibonacci natAbs bridge")?;
    let fib_gcd_import = import_bound(&paths[1], HASHES[1], "natural Fibonacci gcd")?;
    if !bridge_import.report().axioms.is_empty() || !fib_gcd_import.report().axioms.is_empty() {
        return Err("an input stream reaches assumptions".to_owned());
    }
    require_bound_root(
        bridge_import.kernel(),
        BRIDGE,
        "deee672b0430d982d1df383c933b520de37ffcaba4dcb23d5231c29926493e83",
    )?;
    require_bound_root(
        fib_gcd_import.kernel(),
        FIB_GCD,
        "2b5f52996fdc275c859364de7b99bf32ab4ba01e24fc14e10cf65bbd5724ea8d",
    )?;

    let mut kernel = bridge_import.kernel().clone();
    let completed = compose_checked_theorem_slice(fib_gcd_import.kernel(), &kernel, &[FIB_GCD])
        .map_err(|error| format!("Nat.fib_gcd composition declined: {error:?}"))?;
    verify_checked_theorem_composition(
        fib_gcd_import.kernel(),
        &kernel,
        completed.kernel(),
        completed.receipt(),
    )
    .map_err(|error| format!("Nat.fib_gcd composition replay failed: {error:?}"))?;
    let composition_receipt = completed.receipt().receipt_sha256.clone();
    kernel = completed.kernel().clone();

    add_int_gcd(&mut kernel)?;
    add_int_gcd_def(&mut kernel)?;
    let gcd_def = find_name(&kernel, INT_GCD_DEF)?;
    require_empty(&kernel, gcd_def, INT_GCD_DEF)?;
    add_int_gcd_fib(&mut kernel)?;

    let target = find_name(&kernel, TARGET)?;
    require_empty(&kernel, target, TARGET)?;
    let target_evidence = evidence(&kernel, target)?;
    let expected_dependencies = [BRIDGE, "Eq.symm", "Eq.trans", INT_GCD_DEF, FIB_GCD];
    if names(&kernel, &kernel.theorem_dependencies(target)) != sorted(&expected_dependencies) {
        return Err(format!(
            "exact target dependency set changed: {:?}",
            names(&kernel, &kernel.theorem_dependencies(target))
        ));
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
    fs::write(&paths[2], &bytes).map_err(|error| format!("target write failed: {error}"))?;

    println!(
        "{}",
        serde_json::to_string_pretty(&json!({
            "schema_version": 1,
            "kind": "axeyum-int-gcd-fib-exact",
            "state": "exact-target-constructed-exported-and-twice-reimported-empty-footprint",
            "input_sha256": HASHES,
            "composition_receipt_sha256": composition_receipt,
            "int_gcd": declaration_evidence(&kernel, find_name(&kernel, INT_GCD)?)?,
            "int_gcd_def": evidence(&kernel, gcd_def)?,
            "target": target_evidence,
            "capsule": {"path": paths[2], "bytes": bytes.len(), "sha256": hex_sha256(bytes.as_bytes()), "fresh_imports": 2},
            "execution": {"complete_invocations": 1, "input_stream_reads": 2, "composition_operations": 1, "composition_replays": 1, "definition_submissions": 1, "support_theorem_submissions": 1, "target_theorem_submissions": 1, "target_exports": 1, "fresh_target_imports": 2, "retries": 0, "ledger_writes": 0},
            "rendered_material": {"proof_terms": 0, "theorem_types": 0, "theorem_values": 0}
        }))
        .map_err(|error| error.to_string())?
    );
    Ok(())
}

fn add_int_gcd(kernel: &mut Kernel) -> Result<(), String> {
    let name = nested_name(kernel, &["Int", "gcd"]);
    if kernel.environment().get(name).is_some() {
        return Err("Int.gcd exists before target-owned construction".to_owned());
    }
    let int_ty = const0(kernel, "Int")?;
    let nat_ty = const0(kernel, "Nat")?;
    let nat_abs = find_name(kernel, "Int.natAbs")?;
    let nat_gcd = find_name(kernel, "Nat.gcd")?;
    let m_id = u64::MAX - 120_001;
    let n_id = u64::MAX - 120_002;
    let m = kernel.fvar(m_id);
    let n = kernel.fvar(n_id);
    let abs_m = app_const(kernel, nat_abs, &[], &[m]);
    let abs_n = app_const(kernel, nat_abs, &[], &[n]);
    let body = app_const(kernel, nat_gcd, &[], &[abs_m, abs_n]);
    let ty = close_pi2(kernel, m_id, n_id, "m", "n", int_ty, int_ty, nat_ty);
    let value = close_lam2(kernel, m_id, n_id, "m", "n", int_ty, int_ty, body);
    kernel
        .add_declaration(Declaration::Definition {
            name,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(1),
        })
        .map_err(|error| format!("Int.gcd definition rejected: {error:?}"))
}

fn add_int_fib_gcd(kernel: &mut Kernel) -> Result<(), String> {
    let name = nested_name(kernel, &["Int", "fib_gcd"]);
    if kernel.environment().get(name).is_some() {
        return Err("Int.fib_gcd exists before target submission".to_owned());
    }
    let int_ty = const0(kernel, "Int")?;
    let nat_ty = const0(kernel, "Nat")?;
    let zero = kernel.level_zero();
    let carrier_level = kernel.level_succ(zero);
    let int_fib = find_name(kernel, "Int.fib")?;
    let int_gcd = find_name(kernel, "Int.gcd")?;
    let nat_fib = find_name(kernel, "Nat.fib")?;
    let int_of_nat = find_name(kernel, "Int.ofNat")?;
    let fib_natcast = find_name(kernel, "Int.fib_natCast")?;
    let gcd_fib = find_name(kernel, "Int.gcd_fib")?;
    let eq_symm = find_name(kernel, "Eq.symm")?;
    let eq_trans = find_name(kernel, "Eq.trans")?;

    let m_id = u64::MAX - 122_001;
    let n_id = u64::MAX - 122_002;
    let m = kernel.fvar(m_id);
    let n = kernel.fvar(n_id);
    let fib_m = app_const(kernel, int_fib, &[], &[m]);
    let fib_n = app_const(kernel, int_fib, &[], &[n]);
    let gcd_mn = app_const(kernel, int_gcd, &[], &[m, n]);
    let gcd_fibs = app_const(kernel, int_gcd, &[], &[fib_m, fib_n]);
    let nat_fib_gcd = app_const(kernel, nat_fib, &[], &[gcd_mn]);
    let cast_gcd = app_const(kernel, int_of_nat, &[], &[gcd_mn]);
    let cast_nat_fib_gcd = app_const(kernel, int_of_nat, &[], &[nat_fib_gcd]);
    let cast_gcd_fibs = app_const(kernel, int_of_nat, &[], &[gcd_fibs]);
    let lhs = app_const(kernel, int_fib, &[], &[cast_gcd]);

    let p0 = app_const(kernel, fib_natcast, &[], &[gcd_mn]);
    let p0_type = equality(kernel, int_ty, lhs, cast_nat_fib_gcd)?;
    require_closed_type(
        kernel,
        p0,
        p0_type,
        m_id,
        n_id,
        int_ty,
        "p0 Int.fib_natCast",
    )?;

    let gcd_fib_forward = app_const(kernel, gcd_fib, &[], &[m, n]);
    let gcd_fib_reverse = app_const(
        kernel,
        eq_symm,
        &[carrier_level],
        &[nat_ty, gcd_fibs, nat_fib_gcd, gcd_fib_forward],
    );
    let cast_function = kernel.const_(int_of_nat, vec![]);
    let p1 = eq_rec_congr(
        kernel,
        nat_ty,
        int_ty,
        cast_function,
        nat_fib_gcd,
        gcd_fibs,
        gcd_fib_reverse,
        122_101,
    )?;
    let p1_type = equality(kernel, int_ty, cast_nat_fib_gcd, cast_gcd_fibs)?;
    require_closed_type(
        kernel,
        p1,
        p1_type,
        m_id,
        n_id,
        int_ty,
        "p1 casted symmetric Int.gcd_fib",
    )?;

    let proof = app_const(
        kernel,
        eq_trans,
        &[carrier_level],
        &[int_ty, lhs, cast_nat_fib_gcd, cast_gcd_fibs, p0, p1],
    );
    let proposition = equality(kernel, int_ty, lhs, cast_gcd_fibs)?;
    require_closed_type(
        kernel,
        proof,
        proposition,
        m_id,
        n_id,
        int_ty,
        "completed Int.fib_gcd equality",
    )?;
    let ty = close_pi2(kernel, m_id, n_id, "m", "n", int_ty, int_ty, proposition);
    let value = close_lam2(kernel, m_id, n_id, "m", "n", int_ty, int_ty, proof);
    kernel
        .add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty,
            value,
        })
        .map_err(|error| format!("Int.fib_gcd rejected: {error:?}"))
}

fn add_int_gcd_def(kernel: &mut Kernel) -> Result<(), String> {
    let name = nested_name(kernel, &["Int", "gcd_def"]);
    if kernel.environment().get(name).is_some() {
        return Err("Int.gcd_def exists before support construction".to_owned());
    }
    let int_ty = const0(kernel, "Int")?;
    let nat_ty = const0(kernel, "Nat")?;
    let int_gcd = find_name(kernel, INT_GCD)?;
    let nat_abs = find_name(kernel, "Int.natAbs")?;
    let nat_gcd = find_name(kernel, "Nat.gcd")?;
    let m_id = u64::MAX - 120_101;
    let n_id = u64::MAX - 120_102;
    let m = kernel.fvar(m_id);
    let n = kernel.fvar(n_id);
    let left = app_const(kernel, int_gcd, &[], &[m, n]);
    let abs_m = app_const(kernel, nat_abs, &[], &[m]);
    let abs_n = app_const(kernel, nat_abs, &[], &[n]);
    let right = app_const(kernel, nat_gcd, &[], &[abs_m, abs_n]);
    let proposition = equality(kernel, nat_ty, left, right)?;
    let proof = eq_refl(kernel, nat_ty, right)?;
    let ty = close_pi2(kernel, m_id, n_id, "m", "n", int_ty, int_ty, proposition);
    let value = close_lam2(kernel, m_id, n_id, "m", "n", int_ty, int_ty, proof);
    kernel
        .add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty,
            value,
        })
        .map_err(|error| format!("Int.gcd_def rejected: {error:?}"))
}

#[allow(clippy::too_many_lines)]
fn add_int_gcd_fib(kernel: &mut Kernel) -> Result<(), String> {
    let name = nested_name(kernel, &["Int", "gcd_fib"]);
    if kernel.environment().get(name).is_some() {
        return Err("Int.gcd_fib exists before target submission".to_owned());
    }
    let int_ty = const0(kernel, "Int")?;
    let nat_ty = const0(kernel, "Nat")?;
    let zero_level = kernel.level_zero();
    let nat_level = kernel.level_succ(zero_level);
    let int_fib = find_name(kernel, "Int.fib")?;
    let nat_fib = find_name(kernel, "Nat.fib")?;
    let int_gcd = find_name(kernel, INT_GCD)?;
    let nat_gcd = find_name(kernel, "Nat.gcd")?;
    let nat_abs = find_name(kernel, "Int.natAbs")?;
    let gcd_def = find_name(kernel, INT_GCD_DEF)?;
    let bridge = find_name(kernel, BRIDGE)?;
    let fib_gcd = find_name(kernel, FIB_GCD)?;
    let eq_symm = find_name(kernel, "Eq.symm")?;
    let eq_trans = find_name(kernel, "Eq.trans")?;

    let m_id = u64::MAX - 120_201;
    let n_id = u64::MAX - 120_202;
    let m = kernel.fvar(m_id);
    let n = kernel.fvar(n_id);
    let fib_m = app_const(kernel, int_fib, &[], &[m]);
    let fib_n = app_const(kernel, int_fib, &[], &[n]);
    let abs_m = app_const(kernel, nat_abs, &[], &[m]);
    let abs_n = app_const(kernel, nat_abs, &[], &[n]);
    let abs_fib_m = app_const(kernel, nat_abs, &[], &[fib_m]);
    let abs_fib_n = app_const(kernel, nat_abs, &[], &[fib_n]);
    let nat_fib_abs_m = app_const(kernel, nat_fib, &[], &[abs_m]);
    let nat_fib_abs_n = app_const(kernel, nat_fib, &[], &[abs_n]);
    let lhs = app_const(kernel, int_gcd, &[], &[fib_m, fib_n]);
    let gcd_abs_fib = app_const(kernel, nat_gcd, &[], &[abs_fib_m, abs_fib_n]);
    let gcd_first = app_const(kernel, nat_gcd, &[], &[nat_fib_abs_m, abs_fib_n]);
    let gcd_both = app_const(kernel, nat_gcd, &[], &[nat_fib_abs_m, nat_fib_abs_n]);
    let gcd_abs = app_const(kernel, nat_gcd, &[], &[abs_m, abs_n]);
    let fib_gcd_abs = app_const(kernel, nat_fib, &[], &[gcd_abs]);
    let gcd_mn = app_const(kernel, int_gcd, &[], &[m, n]);
    let rhs = app_const(kernel, nat_fib, &[], &[gcd_mn]);

    let p0 = app_const(kernel, gcd_def, &[], &[fib_m, fib_n]);
    let p0_type = equality(kernel, nat_ty, lhs, gcd_abs_fib)?;
    require_closed_type(kernel, p0, p0_type, m_id, n_id, int_ty, "p0 Int.gcd_def")?;
    let bridge_m = app_const(kernel, bridge, &[], &[m]);
    let first_argument = kernel.bvar(0);
    let first_fn_body = app_const(kernel, nat_gcd, &[], &[first_argument, abs_fib_n]);
    let first_binder = kernel.anon();
    let first_fn = kernel.lam(first_binder, nat_ty, first_fn_body, BinderInfo::Default);
    let p1 = eq_rec_congr(
        kernel,
        nat_ty,
        nat_ty,
        first_fn,
        abs_fib_m,
        nat_fib_abs_m,
        bridge_m,
        121_001,
    )?;
    let p1_type = equality(kernel, nat_ty, gcd_abs_fib, gcd_first)?;
    require_closed_type(
        kernel,
        p1,
        p1_type,
        m_id,
        n_id,
        int_ty,
        "p1 first natAbs transport",
    )?;
    let bridge_n = app_const(kernel, bridge, &[], &[n]);
    let second_argument = kernel.bvar(0);
    let second_fn_body = app_const(kernel, nat_gcd, &[], &[nat_fib_abs_m, second_argument]);
    let second_binder = kernel.anon();
    let second_fn = kernel.lam(second_binder, nat_ty, second_fn_body, BinderInfo::Default);
    let p2 = eq_rec_congr(
        kernel,
        nat_ty,
        nat_ty,
        second_fn,
        abs_fib_n,
        nat_fib_abs_n,
        bridge_n,
        121_101,
    )?;
    let p2_type = equality(kernel, nat_ty, gcd_first, gcd_both)?;
    require_closed_type(
        kernel,
        p2,
        p2_type,
        m_id,
        n_id,
        int_ty,
        "p2 second natAbs transport",
    )?;
    let fib_gcd_forward = app_const(kernel, fib_gcd, &[], &[abs_m, abs_n]);
    let p3 = app_const(
        kernel,
        eq_symm,
        &[nat_level],
        &[nat_ty, fib_gcd_abs, gcd_both, fib_gcd_forward],
    );
    let p3_type = equality(kernel, nat_ty, gcd_both, fib_gcd_abs)?;
    require_closed_type(
        kernel,
        p3,
        p3_type,
        m_id,
        n_id,
        int_ty,
        "p3 symmetric Nat.fib_gcd",
    )?;
    let gcd_def_mn = app_const(kernel, gcd_def, &[], &[m, n]);
    let gcd_def_reverse = app_const(
        kernel,
        eq_symm,
        &[nat_level],
        &[nat_ty, gcd_mn, gcd_abs, gcd_def_mn],
    );
    let nat_fib_const = kernel.const_(nat_fib, vec![]);
    let p4 = eq_rec_congr(
        kernel,
        nat_ty,
        nat_ty,
        nat_fib_const,
        gcd_abs,
        gcd_mn,
        gcd_def_reverse,
        121_201,
    )?;
    let p4_type = equality(kernel, nat_ty, fib_gcd_abs, rhs)?;
    require_closed_type(
        kernel,
        p4,
        p4_type,
        m_id,
        n_id,
        int_ty,
        "p4 final Int.gcd_def transport",
    )?;
    let proof = eq_trans_chain(
        kernel,
        nat_ty,
        eq_trans,
        &[
            (lhs, gcd_abs_fib, p0),
            (gcd_abs_fib, gcd_first, p1),
            (gcd_first, gcd_both, p2),
            (gcd_both, fib_gcd_abs, p3),
            (fib_gcd_abs, rhs, p4),
        ],
        nat_level,
    );
    let proposition = equality(kernel, nat_ty, lhs, rhs)?;
    require_closed_type(
        kernel,
        proof,
        proposition,
        m_id,
        n_id,
        int_ty,
        "completed equality chain",
    )?;
    let ty = close_pi2(kernel, m_id, n_id, "m", "n", int_ty, int_ty, proposition);
    let value = close_lam2(kernel, m_id, n_id, "m", "n", int_ty, int_ty, proof);
    kernel
        .add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty,
            value,
        })
        .map_err(|error| format!("Int.gcd_fib rejected: {error:?}"))
}

#[allow(clippy::too_many_arguments)]
fn require_closed_type(
    kernel: &mut Kernel,
    proof: ExprId,
    expected: ExprId,
    first: u64,
    second: u64,
    binder_ty: ExprId,
    label: &str,
) -> Result<(), String> {
    let closed_proof = close_lam2(kernel, first, second, "m", "n", binder_ty, binder_ty, proof);
    let closed_expected = close_pi2(
        kernel, first, second, "m", "n", binder_ty, binder_ty, expected,
    );
    let inferred = kernel
        .infer(closed_proof)
        .map_err(|error| format!("{label} inference failed: {error:?}"))?;
    if kernel.def_eq(inferred, closed_expected) {
        Ok(())
    } else {
        Err(format!("{label} inferred a non-convertible type"))
    }
}

#[allow(clippy::too_many_arguments)]
fn eq_rec_congr(
    kernel: &mut Kernel,
    domain: ExprId,
    codomain: ExprId,
    function: ExprId,
    left: ExprId,
    right: ExprId,
    proof: ExprId,
    id_suffix: u64,
) -> Result<ExprId, String> {
    let right_id = u64::MAX - id_suffix;
    let equality_id = u64::MAX - id_suffix - 1;
    let variable = kernel.fvar(right_id);
    let function_left = kernel.app(function, left);
    let function_variable = kernel.app(function, variable);
    let result = equality(kernel, codomain, function_left, function_variable)?;
    let premise = equality(kernel, domain, left, variable)?;
    let motive = close_lam(kernel, equality_id, "h", premise, result);
    let motive = close_lam(kernel, right_id, "b", domain, motive);
    let reflexivity = eq_refl(kernel, codomain, function_left)?;
    let zero = kernel.level_zero();
    let carrier_level = kernel.level_succ(zero);
    let motive_level = kernel.level_zero();
    let rec = find_name(kernel, "Eq.rec")?;
    Ok(app_const(
        kernel,
        rec,
        &[motive_level, carrier_level],
        &[domain, left, motive, reflexivity, right, proof],
    ))
}

fn eq_trans_chain(
    kernel: &mut Kernel,
    ty: ExprId,
    trans: NameId,
    steps: &[(ExprId, ExprId, ExprId)],
    level: axeyum_lean_kernel::LevelId,
) -> ExprId {
    let mut proof = steps[0].2;
    let start = steps[0].0;
    let mut middle = steps[0].1;
    for &(left, right, next) in &steps[1..] {
        debug_assert_eq!(left, middle);
        proof = app_const(
            kernel,
            trans,
            &[level],
            &[ty, start, middle, right, proof, next],
        );
        middle = right;
    }
    proof
}

fn equality(
    kernel: &mut Kernel,
    ty: ExprId,
    left: ExprId,
    right: ExprId,
) -> Result<ExprId, String> {
    let eq = find_name(kernel, "Eq")?;
    let zero = kernel.level_zero();
    let level = kernel.level_succ(zero);
    Ok(app_const(kernel, eq, &[level], &[ty, left, right]))
}

fn eq_refl(kernel: &mut Kernel, ty: ExprId, value: ExprId) -> Result<ExprId, String> {
    let refl = find_name(kernel, "Eq.refl")?;
    let zero = kernel.level_zero();
    let level = kernel.level_succ(zero);
    Ok(app_const(kernel, refl, &[level], &[ty, value]))
}

fn close_lam(kernel: &mut Kernel, id: u64, name: &str, domain: ExprId, body: ExprId) -> ExprId {
    let body = kernel.abstract_fvars(body, &[id]);
    let binder = nested_name(kernel, &[name]);
    kernel.lam(binder, domain, body, BinderInfo::Default)
}

#[allow(clippy::too_many_arguments)]
fn close_pi2(
    kernel: &mut Kernel,
    first: u64,
    second: u64,
    first_name: &str,
    second_name: &str,
    first_ty: ExprId,
    second_ty: ExprId,
    body: ExprId,
) -> ExprId {
    let body = kernel.abstract_fvars(body, &[second]);
    let second_binder = nested_name(kernel, &[second_name]);
    let body = kernel.pi(second_binder, second_ty, body, BinderInfo::Default);
    let body = kernel.abstract_fvars(body, &[first]);
    let first_binder = nested_name(kernel, &[first_name]);
    kernel.pi(first_binder, first_ty, body, BinderInfo::Default)
}

#[allow(clippy::too_many_arguments)]
fn close_lam2(
    kernel: &mut Kernel,
    first: u64,
    second: u64,
    first_name: &str,
    second_name: &str,
    first_ty: ExprId,
    second_ty: ExprId,
    body: ExprId,
) -> ExprId {
    let body = kernel.abstract_fvars(body, &[second]);
    let second_binder = nested_name(kernel, &[second_name]);
    let body = kernel.lam(second_binder, second_ty, body, BinderInfo::Default);
    let body = kernel.abstract_fvars(body, &[first]);
    let first_binder = nested_name(kernel, &[first_name]);
    kernel.lam(first_binder, first_ty, body, BinderInfo::Default)
}

fn app_const(
    kernel: &mut Kernel,
    name: NameId,
    levels: &[axeyum_lean_kernel::LevelId],
    arguments: &[ExprId],
) -> ExprId {
    let mut expression = kernel.const_(name, levels.to_vec());
    for &argument in arguments {
        expression = kernel.app(expression, argument);
    }
    expression
}

fn const0(kernel: &mut Kernel, rendered: &str) -> Result<ExprId, String> {
    Ok(kernel.const_(find_name(kernel, rendered)?, vec![]))
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

fn declaration_evidence(kernel: &Kernel, name: NameId) -> Result<Value, String> {
    Ok(json!({
        "name": kernel.display_name(name).to_string(),
        "declaration_sha256": canonical_declaration_sha256(kernel, name)?,
        "axiom_footprint": names(kernel, &kernel.axiom_footprint(name)),
    }))
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
