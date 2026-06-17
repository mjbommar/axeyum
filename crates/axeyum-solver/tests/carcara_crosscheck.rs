//! Third-party cross-check of axeyum's emitted Alethe proofs by **Carcara**
//! (the Rust Alethe proof checker), per plan task T3.3.5.
//!
//! This closes the "trust our own checker" gap: an `unsat` proof axeyum emits
//! is serialized to the textual Alethe format (`write_alethe`) alongside the
//! matching SMT-LIB problem (`write_script`), then handed to an *independent*
//! checker that shares none of our code. Carcara accepting the proof is
//! stronger evidence than `check_alethe` (ours) accepting it.
//!
//! Carcara lives in the gitignored `references/` tree and is not present in CI,
//! so each test **skips** (prints a note, passes) when the binary is absent.
//! Build it with `cargo build --release -p carcara-cli` inside
//! `references/carcara`, or point `AXEYUM_CARCARA_BIN` at a `carcara` binary.

use std::path::{Path, PathBuf};
use std::process::Command;

use axeyum_cnf::write_alethe;
use axeyum_ir::{Sort, TermArena, TermId};
use axeyum_smtlib::write_script;
use axeyum_solver::prove_qf_uf_unsat_alethe;

/// Resolves the Carcara binary: `AXEYUM_CARCARA_BIN` if set, otherwise the
/// conventional reference build path. Returns `None` (→ skip) if unavailable.
fn carcara_bin() -> Option<PathBuf> {
    if let Ok(p) = std::env::var("AXEYUM_CARCARA_BIN") {
        let path = PathBuf::from(p);
        return path.is_file().then_some(path);
    }
    // crates/axeyum-solver → workspace root → references/carcara/...
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../references/carcara/target/release/carcara");
    path.is_file().then_some(path)
}

/// Emits `proof` + the matching `.smt2` to a temp dir and runs `carcara check`.
/// Returns Carcara's combined stdout/stderr; panics on a non-zero (invalid) exit.
fn carcara_accepts(
    bin: &Path,
    tag: &str,
    arena: &TermArena,
    assertions: &[TermId],
    proof: &[axeyum_cnf::AletheCommand],
) -> String {
    let dir = std::env::temp_dir().join(format!("axeyum_carcara_{tag}"));
    std::fs::create_dir_all(&dir).expect("create temp dir");
    let smt2 = dir.join("problem.smt2");
    let alethe = dir.join("proof.alethe");
    std::fs::write(&smt2, write_script(arena, assertions)).expect("write smt2");
    std::fs::write(&alethe, write_alethe(proof)).expect("write alethe");

    let out = Command::new(bin)
        .arg("check")
        .arg(&alethe)
        .arg(&smt2)
        .output()
        .expect("run carcara");
    let combined = format!(
        "{}{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
    assert!(
        out.status.success() && combined.contains("valid") && !combined.contains("holey"),
        "carcara rejected the {tag} proof:\n{combined}"
    );
    combined
}

fn var(arena: &mut TermArena, name: &str) -> TermId {
    let s = arena.declare(name, Sort::BitVec(8)).expect("declare");
    arena.var(s)
}

#[test]
fn euf_transitivity_proof_is_accepted_by_carcara() {
    let Some(bin) = carcara_bin() else {
        eprintln!("[skip] carcara binary not found; build references/carcara to enable");
        return;
    };
    // a = b, b = c, a != c — unsat by transitivity.
    let mut arena = TermArena::new();
    let a = var(&mut arena, "a");
    let b = var(&mut arena, "b");
    let c = var(&mut arena, "c");
    let ab = arena.eq(a, b).unwrap();
    let bc = arena.eq(b, c).unwrap();
    let ac = arena.eq(a, c).unwrap();
    let nac = arena.not(ac).unwrap();
    let assertions = vec![ab, bc, nac];

    let proof = prove_qf_uf_unsat_alethe(&arena, &assertions).expect("emit EUF proof");
    let report = carcara_accepts(&bin, "euf_trans", &arena, &assertions, &proof);
    assert!(report.contains("valid"), "expected 'valid', got:\n{report}");
}

#[test]
fn euf_congruence_proof_is_accepted_by_carcara() {
    let Some(bin) = carcara_bin() else {
        eprintln!("[skip] carcara binary not found; build references/carcara to enable");
        return;
    };
    // f(a) != f(b) with a = b — unsat by congruence.
    let mut arena = TermArena::new();
    let a = var(&mut arena, "a");
    let b = var(&mut arena, "b");
    let f = arena
        .declare_fun("f", &[Sort::BitVec(8)], Sort::BitVec(8))
        .expect("declare_fun");
    let fa = arena.apply(f, &[a]).unwrap();
    let fb = arena.apply(f, &[b]).unwrap();
    let ab = arena.eq(a, b).unwrap();
    let fafb = arena.eq(fa, fb).unwrap();
    let nfafb = arena.not(fafb).unwrap();
    let assertions = vec![ab, nfafb];

    let proof = prove_qf_uf_unsat_alethe(&arena, &assertions).expect("emit EUF proof");
    let report = carcara_accepts(&bin, "euf_cong", &arena, &assertions, &proof);
    assert!(report.contains("valid"), "expected 'valid', got:\n{report}");
}
