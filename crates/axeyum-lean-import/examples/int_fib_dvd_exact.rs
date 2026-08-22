//! Construct exact, empty-footprint `Int.fib_dvd` from sealed capsules.

use std::fmt::Write as _;
use std::fs;
use std::io::Cursor;
use std::path::{Path, PathBuf};

use axeyum_lean_import::{
    ImportLimits, canonical_declaration_sha256, compose_checked_theorem_slice, import_ndjson,
    verify_checked_theorem_composition,
};
use axeyum_lean_kernel::{
    BinderInfo, Declaration, ExprId, ExprNode, Kernel, Lean4ExportMetadata, NameId,
};
use serde_json::{Value, json};
use sha2::{Digest, Sha256};

const INPUT_SHA256: [&str; 4] = [
    "1ec10d475fb3c77fea3353036e2a09f70abf88f03402a2912407c71b26e3b7e4",
    "52acbd5a51f2163ab5b712483c582adb916ab198567c2b0b6c3678f7316d86d7",
    "09ebd925b3af67009b1806fd157a25b195e046124065778ec6eaf754f5ecfc04",
    "66faaafc0b7a34267d22427cd968fe3649e31cae3dcf9b87c56ab3db83004bc6",
];
const BRIDGE: &str = "Axeyum.Autogenesis.intFibNatAbsV1";
const NAT_FIB_DVD: &str = "Nat.fib_dvd";
const NAT_ABS_MUL: &str = "Axeyum.Autogenesis.intNatAbsMulDirectV1";
const FORWARD: &str = "Axeyum.Autogenesis.intNatAbsDvdForwardResidualV1";
const REVERSE: &str = "Axeyum.Autogenesis.intDvdOfNatAbsDvdDirectV1";
const TARGET: &str = "Int.fib_dvd";
const USAGE: &str = "usage: int_fib_dvd_exact <int-fib-natabs> <nat-fib-dvd> <natabs-mul> <witness-transports> <output>";

fn main() {
    if let Err(error) = run() {
        eprintln!("int-fib-dvd-exact: {error}");
        std::process::exit(1);
    }
}

#[allow(clippy::too_many_lines)]
fn run() -> Result<(), String> {
    let mut arguments = std::env::args_os().skip(1);
    let paths = (0..5)
        .map(|_| path(&mut arguments))
        .collect::<Result<Vec<_>, _>>()?;
    if arguments.next().is_some() || paths[4].exists() {
        return Err(USAGE.to_owned());
    }

    let imports = paths[..4]
        .iter()
        .zip(INPUT_SHA256)
        .map(|(path, hash)| import_bound(path, hash))
        .collect::<Result<Vec<_>, _>>()?;
    if imports.iter().any(|imported| !imported.report().axioms.is_empty()) {
        return Err("an input stream reaches assumptions".to_owned());
    }
    require_bound_root(
        imports[0].kernel(),
        BRIDGE,
        "deee672b0430d982d1df383c933b520de37ffcaba4dcb23d5231c29926493e83",
    )?;
    require_bound_root(
        imports[1].kernel(),
        NAT_FIB_DVD,
        "eef50a6cf5d2d19c80ed894f11d14bbe3521b86982a960e381fff8076be55237",
    )?;
    require_bound_root(
        imports[2].kernel(),
        NAT_ABS_MUL,
        "ebfbf0442e5e7d93a2a38e70e51b364100455633f44832878ed34ec37de01bb3",
    )?;
    require_bound_root(
        imports[3].kernel(),
        FORWARD,
        "d542789b57420405457285516702575360ce7f9a4c8ba45d2e78319f27d74e26",
    )?;
    require_bound_root(
        imports[3].kernel(),
        REVERSE,
        "9da5f612a874815dd7aaed32791eb6636da801a1054884937ad0ff477c8ba319",
    )?;

    let mut kernel = imports[0].kernel().clone();
    let mut receipts = Vec::with_capacity(3);
    compose(
        imports[1].kernel(),
        &mut kernel,
        &[NAT_FIB_DVD],
        &mut receipts,
    )?;
    compose(
        imports[2].kernel(),
        &mut kernel,
        &[NAT_ABS_MUL],
        &mut receipts,
    )?;
    compose(
        imports[3].kernel(),
        &mut kernel,
        &[FORWARD, REVERSE],
        &mut receipts,
    )?;

    add_int_fib_dvd(&mut kernel)?;
    let target = find_name(&kernel, TARGET)?;
    require_empty(&kernel, target, TARGET)?;
    let target_evidence = evidence(&kernel, target)?;
    let expected_dependencies = [
        REVERSE,
        BRIDGE,
        FORWARD,
        NAT_ABS_MUL,
        "Eq.symm",
        NAT_FIB_DVD,
    ];
    let actual_dependencies = names(&kernel, &kernel.theorem_dependencies(target));
    if actual_dependencies != sorted(&expected_dependencies) {
        return Err(format!(
            "exact target dependency set changed: {actual_dependencies:?}"
        ));
    }

    let bytes = kernel
        .render_lean4export_ndjson_roots(&Lean4ExportMetadata::axeyum("4.30.0"), &[target])
        .map_err(|error| format!("target export failed: {error}"))?;
    for pass in 1..=2 {
        let imported = import_ndjson(Cursor::new(bytes.as_bytes()), ImportLimits::default())
            .map_err(|error| format!("fresh target import {pass} failed: {error:?}"))?;
        let fresh_target = find_name(imported.kernel(), TARGET)?;
        if evidence(imported.kernel(), fresh_target)? != target_evidence {
            return Err(format!("fresh target import {pass} changed evidence"));
        }
    }
    fs::write(&paths[4], &bytes).map_err(|error| format!("target write failed: {error}"))?;

    println!(
        "{}",
        serde_json::to_string_pretty(&json!({
            "schema_version": 1,
            "kind": "axeyum-int-fib-dvd-exact",
            "state": "exact-target-constructed-exported-and-twice-reimported-empty-footprint",
            "input_sha256": INPUT_SHA256,
            "composition_receipt_sha256": receipts,
            "target": target_evidence,
            "capsule": {"path": paths[4], "bytes": bytes.len(), "sha256": hex_sha256(bytes.as_bytes()), "fresh_imports": 2},
            "execution": {"complete_invocations": 1, "input_stream_reads": 4, "composition_operations": 3, "composition_replays": 3, "target_theorem_submissions": 1, "target_exports": 1, "fresh_target_imports": 2, "retries": 0, "ledger_writes": 0},
            "rendered_material": {"proof_terms": 0, "theorem_types": 0, "theorem_values": 0}
        }))
        .map_err(|error| error.to_string())?
    );
    Ok(())
}

#[allow(clippy::too_many_lines)]
fn add_int_fib_dvd(kernel: &mut Kernel) -> Result<(), String> {
    let name = nested_name(kernel, &["Int", "fib_dvd"]);
    if kernel.environment().get(name).is_some() {
        return Err("Int.fib_dvd exists before target submission".to_owned());
    }
    let int_ty = const0(kernel, "Int")?;
    let nat_ty = const0(kernel, "Nat")?;
    let int_fib = find_name(kernel, "Int.fib")?;
    let nat_fib = find_name(kernel, "Nat.fib")?;
    let nat_abs = find_name(kernel, "Int.natAbs")?;
    let bridge = find_name(kernel, BRIDGE)?;
    let nat_fib_dvd = find_name(kernel, NAT_FIB_DVD)?;
    let nat_abs_mul = find_name(kernel, NAT_ABS_MUL)?;
    let forward = find_name(kernel, FORWARD)?;
    let reverse = find_name(kernel, REVERSE)?;
    let eq_symm = find_name(kernel, "Eq.symm")?;

    let m_id = u64::MAX - 140_001;
    let n_id = u64::MAX - 140_002;
    let h_id = u64::MAX - 140_003;
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

    let forward_mn = app_const(kernel, forward, &[], &[nat_abs_mul, m, n]);
    let hypothesis_ty = function_domain(kernel, forward_mn, "forward hypothesis")?;
    let hypothesis = kernel.fvar(h_id);
    let abs_indices_dvd = kernel.app(forward_mn, hypothesis);
    let nat_fibs_dvd = app_const(
        kernel,
        nat_fib_dvd,
        &[],
        &[abs_m, abs_n, abs_indices_dvd],
    );

    let zero = kernel.level_zero();
    let nat_level = kernel.level_succ(zero);
    let bridge_m = app_const(kernel, bridge, &[], &[m]);
    let bridge_n = app_const(kernel, bridge, &[], &[n]);
    let bridge_m_reverse = app_const(
        kernel,
        eq_symm,
        &[nat_level],
        &[nat_ty, abs_fib_m, nat_fib_abs_m, bridge_m],
    );
    let bridge_n_reverse = app_const(
        kernel,
        eq_symm,
        &[nat_level],
        &[nat_ty, abs_fib_n, nat_fib_abs_n, bridge_n],
    );

    let second_id = u64::MAX - 140_101;
    let second = kernel.fvar(second_id);
    let second_prop = nat_dvd(kernel, nat_ty, nat_fib_abs_m, second)?;
    let second_motive = close_lam(kernel, second_id, "b", nat_ty, second_prop);
    let first_transport = eq_rec_transport(
        kernel,
        nat_ty,
        nat_fib_abs_n,
        abs_fib_n,
        second_motive,
        nat_fibs_dvd,
        bridge_n_reverse,
    )?;

    let first_id = u64::MAX - 140_201;
    let first = kernel.fvar(first_id);
    let first_prop = nat_dvd(kernel, nat_ty, first, abs_fib_n)?;
    let first_motive = close_lam(kernel, first_id, "a", nat_ty, first_prop);
    let both_transport = eq_rec_transport(
        kernel,
        nat_ty,
        nat_fib_abs_m,
        abs_fib_m,
        first_motive,
        first_transport,
        bridge_m_reverse,
    )?;

    let proof = app_const(kernel, reverse, &[], &[fib_m, fib_n, both_transport]);
    let proposition = kernel
        .infer(proof)
        .map_err(|error| format!("completed target proof inference failed: {error:?}"))?;
    let hypothesis_binder = nested_name(kernel, &["h"]);
    let proposition_with_h = kernel.pi(
        hypothesis_binder,
        hypothesis_ty,
        proposition,
        BinderInfo::Default,
    );
    let proof_with_h = close_lam(kernel, h_id, "h", hypothesis_ty, proof);
    let ty = close_pi2(
        kernel,
        m_id,
        n_id,
        "m",
        "n",
        int_ty,
        int_ty,
        proposition_with_h,
    );
    let value = close_lam2(
        kernel,
        m_id,
        n_id,
        "m",
        "n",
        int_ty,
        int_ty,
        proof_with_h,
    );
    kernel
        .add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty,
            value,
        })
        .map_err(|error| format!("Int.fib_dvd rejected: {error:?}"))
}

fn nat_dvd(
    kernel: &mut Kernel,
    nat_ty: ExprId,
    left: ExprId,
    right: ExprId,
) -> Result<ExprId, String> {
    let dvd = find_name(kernel, "Dvd.dvd")?;
    let instance = find_name(kernel, "Nat.instDvd")?;
    let zero = kernel.level_zero();
    Ok(app_const(
        kernel,
        dvd,
        &[zero],
        &[nat_ty, kernel.const_(instance, vec![]), left, right],
    ))
}

fn function_domain(kernel: &mut Kernel, function: ExprId, label: &str) -> Result<ExprId, String> {
    let inferred = kernel
        .infer(function)
        .map_err(|error| format!("{label} inference failed: {error:?}"))?;
    let reduced = kernel.whnf(inferred);
    match kernel.expr_node(reduced) {
        ExprNode::Pi(_, domain, _, _) => Ok(*domain),
        _ => Err(format!("{label} is not a function")),
    }
}

fn eq_rec_transport(
    kernel: &mut Kernel,
    domain: ExprId,
    left: ExprId,
    right: ExprId,
    motive: ExprId,
    value: ExprId,
    equality: ExprId,
) -> Result<ExprId, String> {
    let rec = find_name(kernel, "Eq.rec")?;
    let zero = kernel.level_zero();
    let domain_level = kernel.level_succ(zero);
    Ok(app_const(
        kernel,
        rec,
        &[zero, domain_level],
        &[domain, left, motive, value, right, equality],
    ))
}

fn compose(
    source: &Kernel,
    target: &mut Kernel,
    roots: &[&str],
    receipts: &mut Vec<String>,
) -> Result<(), String> {
    let completed = compose_checked_theorem_slice(source, target, roots)
        .map_err(|error| format!("composition declined for {roots:?}: {error:?}"))?;
    verify_checked_theorem_composition(source, target, completed.kernel(), completed.receipt())
        .map_err(|error| format!("composition replay failed for {roots:?}: {error:?}"))?;
    receipts.push(completed.receipt().receipt_sha256.clone());
    *target = completed.kernel().clone();
    Ok(())
}

fn import_bound(
    path: &Path,
    expected_sha256: &str,
) -> Result<axeyum_lean_import::CompletedImport, String> {
    let bytes = fs::read(path).map_err(|error| format!("input read failed: {error}"))?;
    let actual = hex_sha256(&bytes);
    if actual != expected_sha256 {
        return Err(format!("input hash changed: expected {expected_sha256}, got {actual}"));
    }
    import_ndjson(Cursor::new(bytes), ImportLimits::default())
        .map_err(|error| format!("input import failed: {error:?}"))
}

fn require_bound_root(kernel: &Kernel, name: &str, expected: &str) -> Result<(), String> {
    let root = find_name(kernel, name)?;
    let actual = canonical_declaration_sha256(kernel, root)
        .map_err(|error| format!("{name} declaration hash failed: {error}"))?;
    if actual == expected {
        Ok(())
    } else {
        Err(format!("{name} declaration changed: expected {expected}, got {actual}"))
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
    Ok(json!({
        "name": kernel.display_name(theorem).to_string(),
        "declaration_sha256": canonical_declaration_sha256(kernel, theorem)
            .map_err(|error| format!("declaration hash failed: {error}"))?,
        "axiom_footprint": names(kernel, &kernel.axiom_footprint(theorem)),
        "direct_theorem_dependencies": names(kernel, &kernel.theorem_dependencies(theorem)),
    }))
}

fn find_name(kernel: &Kernel, expected: &str) -> Result<NameId, String> {
    kernel
        .environment()
        .iter()
        .map(|(&name, _)| name)
        .find(|&name| kernel.display_name(name).to_string() == expected)
        .ok_or_else(|| format!("declaration absent: {expected}"))
}

fn nested_name(kernel: &mut Kernel, parts: &[&str]) -> NameId {
    let mut name = kernel.anon();
    for part in parts {
        name = kernel.str_name(name, (*part).to_owned());
    }
    name
}

fn const0(kernel: &mut Kernel, rendered: &str) -> Result<ExprId, String> {
    let name = find_name(kernel, rendered)?;
    Ok(kernel.const_(name, vec![]))
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

fn path(arguments: &mut impl Iterator<Item = std::ffi::OsString>) -> Result<PathBuf, String> {
    arguments
        .next()
        .map(PathBuf::from)
        .ok_or_else(|| USAGE.to_owned())
}

fn names(kernel: &Kernel, ids: &[NameId]) -> Vec<String> {
    let mut rendered = ids
        .iter()
        .map(|&name| kernel.display_name(name).to_string())
        .collect::<Vec<_>>();
    rendered.sort();
    rendered
}

fn sorted(values: &[&str]) -> Vec<String> {
    let mut values = values
        .iter()
        .map(|value| (*value).to_owned())
        .collect::<Vec<_>>();
    values.sort();
    values
}

fn hex_sha256(bytes: &[u8]) -> String {
    let digest = Sha256::digest(bytes);
    let mut encoded = String::with_capacity(64);
    for byte in digest {
        let _ = write!(encoded, "{byte:02x}");
    }
    encoded
}
