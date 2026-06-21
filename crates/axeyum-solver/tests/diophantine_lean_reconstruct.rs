//! Integration tests for integer-infeasibility (Diophantine) Lean reconstruction
//! (ADR-0042): the canonical `x + y = 0 ∧ x − y = 1 ⇒ 2x = 1` integer-infeasible
//! system reconstructs to a kernel-checked Lean `False`, while an
//! integer-FEASIBLE system is declined (never fabricated).

use std::path::PathBuf;
use std::process::Command;

use axeyum_ir::TermArena;
use axeyum_solver::{
    ProofFragment, prove_unsat_to_lean_module, reconstruct_diophantine_proof, scan_proof_fragment,
};

/// `x + y = 0 ∧ x − y = 1` over `Int`: rational-feasible (`x = ½`) yet
/// integer-infeasible (`2x = 1`). It reconstructs to a kernel-checked Lean `False`
/// through the Diophantine fragment, with the exported module naming the
/// `axeyum_refutation` theorem.
#[test]
fn two_x_eq_one_reconstructs_to_false() {
    let mut arena = TermArena::new();
    let x = arena.int_var("x").unwrap();
    let y = arena.int_var("y").unwrap();
    let xpy = arena.int_add(x, y).unwrap();
    let zero = arena.int_const(0);
    let e1 = arena.eq(xpy, zero).unwrap();
    let xmy = arena.int_sub(x, y).unwrap();
    let one = arena.int_const(1);
    let e2 = arena.eq(xmy, one).unwrap();

    // The low-level reconstruction yields a kernel-checked `False` proof term.
    let proof = reconstruct_diophantine_proof(&arena, &[e1, e2]);
    assert!(
        proof.is_ok(),
        "x+y=0 ∧ x−y=1 should reconstruct to False, got {:?}",
        proof.err()
    );

    // The unified entry routes it through the Diophantine fragment and renders a
    // self-contained Lean module that names the exported refutation.
    let (fragment, source) = prove_unsat_to_lean_module(&mut arena, &[e1, e2])
        .expect("Diophantine system should prove unsat to a Lean module");
    assert_eq!(fragment, ProofFragment::Diophantine);
    assert!(
        source.contains("axeyum_refutation"),
        "rendered module should name the axeyum_refutation theorem"
    );
    assert_eq!(
        scan_proof_fragment(&arena, &[e1, e2]),
        ProofFragment::Diophantine
    );
}

/// An integer-FEASIBLE system `x + y = 2 ∧ x − y = 0` (sat at `x = y = 1`) has no
/// Diophantine refutation and must be declined — never fabricated.
#[test]
fn feasible_system_is_declined() {
    let mut arena = TermArena::new();
    let x = arena.int_var("x").unwrap();
    let y = arena.int_var("y").unwrap();
    let xpy = arena.int_add(x, y).unwrap();
    let two = arena.int_const(2);
    let e1 = arena.eq(xpy, two).unwrap();
    let xmy = arena.int_sub(x, y).unwrap();
    let zero = arena.int_const(0);
    let e2 = arena.eq(xmy, zero).unwrap();

    assert!(
        reconstruct_diophantine_proof(&arena, &[e1, e2]).is_err(),
        "a feasible integer system must not produce a Diophantine refutation"
    );
    // It is not classified as the Diophantine fragment either.
    assert_ne!(
        scan_proof_fragment(&arena, &[e1, e2]),
        ProofFragment::Diophantine,
        "feasible system should not route to the Diophantine fragment"
    );
}

/// A cancelling system whose Diophantine refutation has the **degenerate `g = 0`
/// row**: `x + y = 0 ∧ y + z = 0 ∧ x − z = 1`. The integer combination
/// `−E₁ + E₂ + E₃` cancels every variable, leaving `0 = 1` (`combined = []`,
/// `constant = 1`). This reconstructs to a kernel-checked `False` through the
/// Diophantine fragment via the sign-based `Not (Eq Z zero 1)` close — no
/// discreteness needed.
#[test]
fn cancelling_system_zero_eq_const_reconstructs_to_false() {
    let mut arena = TermArena::new();
    let x = arena.int_var("x").unwrap();
    let y = arena.int_var("y").unwrap();
    let z = arena.int_var("z").unwrap();
    let xpy = arena.int_add(x, y).unwrap();
    let zero = arena.int_const(0);
    let e1 = arena.eq(xpy, zero).unwrap();
    let ypz = arena.int_add(y, z).unwrap();
    let e2 = arena.eq(ypz, zero).unwrap();
    let xmz = arena.int_sub(x, z).unwrap();
    let one = arena.int_const(1);
    let e3 = arena.eq(xmz, one).unwrap();

    // Low-level reconstruction yields a kernel-checked `False` proof term.
    let proof = reconstruct_diophantine_proof(&arena, &[e1, e2, e3]);
    assert!(
        proof.is_ok(),
        "cancelling 0 = 1 system should reconstruct to False, got {:?}",
        proof.err()
    );

    // The unified entry routes it through the Diophantine fragment and renders a
    // self-contained Lean module naming the exported refutation.
    let (fragment, source) = prove_unsat_to_lean_module(&mut arena, &[e1, e2, e3])
        .expect("cancelling system should prove unsat to a Lean module");
    assert_eq!(fragment, ProofFragment::Diophantine);
    assert!(
        source.contains("axeyum_refutation"),
        "rendered module should name the axeyum_refutation theorem"
    );
    assert_eq!(
        scan_proof_fragment(&arena, &[e1, e2, e3]),
        ProofFragment::Diophantine
    );
}

/// A 2-equality cancelling system `x = 1 ∧ x = 2` whose combination `−E₁ + E₂`
/// cancels `x`, leaving the degenerate `0 = 1` row (`combined = []`, `constant = 1`).
/// Like the 3-equality case, it reconstructs to a kernel-checked `False`.
#[test]
fn x_eq_one_and_x_eq_two_zero_eq_const_reconstructs_to_false() {
    let mut arena = TermArena::new();
    let x = arena.int_var("x").unwrap();
    let one = arena.int_const(1);
    let two = arena.int_const(2);
    let e1 = arena.eq(x, one).unwrap();
    let e2 = arena.eq(x, two).unwrap();

    let proof = reconstruct_diophantine_proof(&arena, &[e1, e2]);
    assert!(
        proof.is_ok(),
        "x=1 ∧ x=2 (0 = 1 row) should reconstruct to False, got {:?}",
        proof.err()
    );
    let (fragment, source) = prove_unsat_to_lean_module(&mut arena, &[e1, e2])
        .expect("x=1 ∧ x=2 should prove unsat to a Lean module");
    assert_eq!(fragment, ProofFragment::Diophantine);
    assert!(source.contains("axeyum_refutation"));
}

/// Locate a `lean` binary (env override or `PATH`/elan); `None` ⇒ skip.
fn lean_bin() -> Option<PathBuf> {
    if let Ok(p) = std::env::var("AXEYUM_LEAN_BIN") {
        let pb = PathBuf::from(p);
        if pb.exists() {
            return Some(pb);
        }
    }
    let elan = dirs_home().join(".elan/bin/lean");
    if elan.exists() {
        return Some(elan);
    }
    which_lean()
}

fn dirs_home() -> PathBuf {
    std::env::var("HOME").map(PathBuf::from).unwrap_or_default()
}

fn which_lean() -> Option<PathBuf> {
    let out = Command::new("which").arg("lean").output().ok()?;
    if !out.status.success() {
        return None;
    }
    let path = String::from_utf8_lossy(&out.stdout).trim().to_owned();
    if path.is_empty() {
        None
    } else {
        Some(PathBuf::from(path))
    }
}

/// **Real-Lean crosscheck**: the rendered Diophantine module must be accepted by a
/// genuine `lean` binary (skips gracefully if none is installed), and `#print
/// axioms axeyum_refutation` must not depend on `sorryAx`. This is the end-to-end
/// kernel-checked integer-proof payoff of ADR-0042.
#[test]
fn diophantine_module_checks_in_real_lean() {
    let mut arena = TermArena::new();
    let x = arena.int_var("x").unwrap();
    let y = arena.int_var("y").unwrap();
    let xpy = arena.int_add(x, y).unwrap();
    let zero = arena.int_const(0);
    let e1 = arena.eq(xpy, zero).unwrap();
    let xmy = arena.int_sub(x, y).unwrap();
    let one = arena.int_const(1);
    let e2 = arena.eq(xmy, one).unwrap();
    let (frag, source) = prove_unsat_to_lean_module(&mut arena, &[e1, e2])
        .expect("Diophantine system reconstructs to a Lean module");
    assert_eq!(frag, ProofFragment::Diophantine);

    let Some(bin) = lean_bin() else {
        eprintln!("[skip] diophantine: lean binary not found; set AXEYUM_LEAN_BIN to enable");
        return;
    };
    let dir = std::env::temp_dir().join("axeyum_lean_diophantine");
    std::fs::create_dir_all(&dir).expect("create temp dir");
    let file = dir.join("diophantine.lean");
    std::fs::write(&file, &source).expect("write lean module");
    let out = Command::new(&bin).arg(&file).output().expect("run lean");
    let stdout = String::from_utf8_lossy(&out.stdout);
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(
        out.status.success(),
        "lean REJECTED the diophantine module\n=== stdout ===\n{stdout}\n=== stderr ===\n{stderr}\n=== source ===\n{source}"
    );
    assert!(
        !stdout.contains("sorryAx"),
        "diophantine proof depends on sorryAx:\n{stdout}"
    );
    assert!(
        stdout.contains("axeyum_refutation"),
        "missing #print axioms output:\n{stdout}"
    );
    eprintln!(
        "[lean ok] diophantine: {}",
        stdout.trim().replace('\n', " | ")
    );
}
