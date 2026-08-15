//! Capability gate: official Lean structural recursion (`brecOn`/`below`) is
//! admissible by our kernel.
//!
//! THE MEASUREMENT THIS GUARDS. Lean compiles a structurally recursive function
//! to `Nat.brecOn`, `Nat.brecOn` to a **projection out of a recursor
//! application**, and proves its defining equations by `rfl`. On a variable
//! argument that projection cannot reduce on either side, so admitting
//! `Nat.add_succ` is exactly the question "does `def_eq` have `Proj`/`Proj`
//! congruence". Before it did, a census of forty official `Init`/`Std` streams
//! (`scripts/lean-import-census.sh`) reported **10 distinct root blockers over 18
//! declining streams**, `Nat.add_comm` among them — the most-cited theorem in
//! our own fact ledger, which we prove ourselves and could not check Lean's proof
//! of. After it: **one** root blocker, over three streams.
//!
//! WHAT THIS IS NOT. It is not a fact. `Nat.add_comm` is already ours
//! (`F:nat-add-comm`, `proof_route: kernel-lean`), so importing it establishes no
//! new proposition; the stream is pinned in `artifacts/lean-imports/MANIFEST.json`
//! with `"fact": null` for that reason. What it establishes is that the kernel
//! still reduces the shape, which is a capability and regresses silently.
//!
//! The import runs through the ordinary fail-closed [`import_ndjson`]: every one
//! of the 52 declarations passes `Kernel::add_declaration`, or nothing is
//! published and this test fails.

use std::path::{Path, PathBuf};

use axeyum_lean_import::{ImportLimits, import_ndjson};
use axeyum_lean_kernel::Declaration;
use sha2::{Digest, Sha256};

/// Pinned bytes of the official export. Re-exported byte-identically on
/// 2026-08-15 from lean4export `a3e35a58` under Lean 4.30.0, with both
/// `lean4export Init -- Nat.add_comm` and `lean4export Init Std -- Nat.add_comm`.
const FIXTURE: &str = "nat-add-comm.ndjson";
const SHA256: &str = "cf186612f5719a3775bbd94480a417dadbe0d427659fddf13e03f6854ace11d4";

/// Declarations the trusted gate must admit from this stream.
const ADMITTED: usize = 52;

/// The declarations in this stream that exist *only* because Lean compiles
/// structural recursion through `brecOn`. Each is a real declaration our kernel
/// type-checks, and each was un-admittable before `Proj`/`Proj` congruence.
const BRECON_MACHINERY: &[&str] = &[
    "Nat.below",
    "Nat.brecOn",
    "Nat.brecOn.go",
    "Nat.add._f",
    "Nat.add.match_1",
    "Nat.zero_add._f",
    "Nat.succ_add._f",
    "Nat.add_comm._f",
];

/// Theorems in this stream whose proofs go *through* the `brecOn` encoding —
/// each is proved by induction whose `._f` body is a `brecOn` application, and
/// each declined before `Proj`/`Proj` congruence. `Nat.add_succ` itself is not in
/// this closure (Lean's `add_comm` does not cite it); the `Nat.add_succ` stream is
/// censused separately by `scripts/lean-import-census.sh`.
const RFL_EQUATIONS: &[&str] = &["Nat.zero_add", "Nat.succ_add", "Nat.add_comm"];

fn hex(bytes: &[u8]) -> String {
    use std::fmt::Write as _;
    let mut out = String::with_capacity(bytes.len() * 2);
    for b in bytes {
        let _ = write!(out, "{b:02x}");
    }
    out
}

fn fixture_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../artifacts/lean-imports")
        .canonicalize()
        .expect("artifacts/lean-imports must exist")
        .join(FIXTURE)
}

#[test]
fn official_brecon_structural_recursion_is_admissible() {
    let path = fixture_path();
    let bytes = std::fs::read(&path).unwrap_or_else(|e| panic!("{}: {e}", path.display()));
    assert_eq!(
        hex(&Sha256::digest(&bytes)),
        SHA256,
        "{FIXTURE} bytes changed; re-export and re-pin deliberately"
    );

    let completed = import_ndjson(bytes.as_slice(), ImportLimits::default())
        .unwrap_or_else(|e| panic!("{FIXTURE}: import failed: {e}"));
    let (kernel, report) = completed.into_parts();

    let names: Vec<String> = kernel
        .environment()
        .iter()
        .map(|(_, d)| kernel.display_name(d.name()).to_string())
        .collect();

    let mut missing: Vec<&str> = Vec::new();
    for wanted in BRECON_MACHINERY.iter().chain(RFL_EQUATIONS.iter()) {
        if !names.iter().any(|n| n == wanted) {
            missing.push(wanted);
        }
    }
    assert!(
        missing.is_empty(),
        "{FIXTURE}: the import published without {missing:?}; the stream or the exporter changed"
    );

    // `Nat.add_comm` itself: the strand's headline blocker.
    let target = kernel
        .environment()
        .iter()
        .map(|(_, d)| d.name())
        .find(|&n| kernel.display_name(n).to_string() == "Nat.add_comm")
        .expect("Nat.add_comm must be admitted");
    let declaration = kernel
        .environment()
        .get(target)
        .expect("just found by name");
    let ty = match declaration {
        Declaration::Theorem { ty, .. } => *ty,
        other => panic!("Nat.add_comm is {other:?}, not a theorem"),
    };
    let rendered = kernel.render_lean(ty);
    // `render_lean` rewrites a root `Nat` to `AxNat` so an emitted module does
    // not shadow Lean's builtin `Nat`. That guard is backwards for an imported
    // stream (see `imported_fact_evidence.rs`), and it is pinned verbatim here
    // because it is what the kernel actually derives.
    assert_eq!(
        rendered,
        "((n : AxNat) -> ((m : AxNat) -> Eq.{1} AxNat (HAdd.hAdd.{0, 0, 0} AxNat AxNat AxNat (instHAdd.{0} AxNat instAddNat) n m) (HAdd.hAdd.{0, 0, 0} AxNat AxNat AxNat (instHAdd.{0} AxNat instAddNat) m n)))",
        "the admitted type of Nat.add_comm moved"
    );

    let footprint: Vec<String> = kernel
        .axiom_footprint(target)
        .into_iter()
        .map(|n| kernel.display_name(n).to_string())
        .collect();
    assert!(
        footprint.is_empty(),
        "Lean's own proof of Nat.add_comm should rest on no axioms, got {footprint:?}"
    );

    assert_eq!(
        report.admitted_declarations, ADMITTED,
        "admitted-declaration count moved"
    );

    // The suite prints a count so an inert build (this repository's signature
    // defect: a green gate that examined nothing) is distinguishable from a pass.
    println!(
        "AXEYUM-BRECON-IMPORT|fixture={FIXTURE}|lean={}|admitted={}|brecon_decls={}|rfl_equations={}",
        report.lean_version,
        report.admitted_declarations,
        BRECON_MACHINERY.len(),
        RFL_EQUATIONS.len(),
    );
}
