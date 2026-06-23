//! Integration tests for integer-INEQUALITY (interval) infeasibility Lean
//! reconstruction (ADR-0042, the integer-cut payoff): the canonical
//! `3*x ≥ 1 ∧ 3*x ≤ 2` (Int) system — infeasible because no multiple of 3 lies in
//! `[1, 2]`, equivalently `0 < x < 1`, refuted by `no_int_between` — reconstructs to
//! a kernel-checked Lean `False`, while an integer-FEASIBLE inequality system is
//! declined (never fabricated).

use std::path::PathBuf;
use std::process::Command;

use axeyum_ir::TermArena;
use axeyum_solver::{
    ProofFragment, prove_unsat_to_lean_module, reconstruct_int_inequality_proof,
    scan_proof_fragment,
};

/// `3*x ≥ 1 ∧ 3*x ≤ 2` over `Int`: LP-feasible (`x ∈ [⅓, ⅔]`) yet integer-infeasible
/// (no multiple of 3 in `[1, 2]`). It reconstructs to a kernel-checked Lean `False`
/// through the `IntInequality` fragment, with the exported module naming the
/// `axeyum_refutation` theorem.
#[test]
fn three_x_in_one_two_reconstructs_to_false() {
    let mut arena = TermArena::new();
    let x = arena.int_var("x").unwrap();
    let three = arena.int_const(3);
    let three_x = arena.int_mul(three, x).unwrap();
    let one = arena.int_const(1);
    let two = arena.int_const(2);
    let e1 = arena.int_ge(three_x, one).unwrap(); // 3x ≥ 1
    let e2 = arena.int_le(three_x, two).unwrap(); // 3x ≤ 2

    // The low-level reconstruction yields a kernel-checked `False` proof term.
    let proof = reconstruct_int_inequality_proof(&arena, &[e1, e2]);
    assert!(
        proof.is_ok(),
        "3x≥1 ∧ 3x≤2 should reconstruct to False, got {:?}",
        proof.err()
    );

    // The unified entry routes it through the IntInequality fragment and renders a
    // self-contained Lean module that names the exported refutation.
    let (fragment, source) = prove_unsat_to_lean_module(&mut arena, &[e1, e2])
        .expect("integer-interval system should prove unsat to a Lean module");
    assert_eq!(fragment, ProofFragment::IntInequality);
    assert!(
        source.contains("axeyum_refutation"),
        "rendered module should name the axeyum_refutation theorem"
    );
    assert_eq!(
        scan_proof_fragment(&arena, &[e1, e2]),
        ProofFragment::IntInequality
    );
}

/// The same instance with a strict bound and the variable on the right
/// (`1 ≤ 3*x ∧ 3*x < 3`): strict `< 3` rewrites to `≤ 2`, so it matches the same
/// `1 ≤ 3x ≤ 2` interval. Confirms the comparison-normalization (strict↔non-strict,
/// orientation) of the shape detector.
#[test]
fn strict_and_oriented_bounds_reconstruct() {
    let mut arena = TermArena::new();
    let x = arena.int_var("x").unwrap();
    let three = arena.int_const(3);
    let three_x = arena.int_mul(three, x).unwrap();
    let one = arena.int_const(1);
    let three_c = arena.int_const(3);
    let e1 = arena.int_le(one, three_x).unwrap(); // 1 ≤ 3x  (lower, var on right)
    let e2 = arena.int_lt(three_x, three_c).unwrap(); // 3x < 3 ⇒ 3x ≤ 2

    let proof = reconstruct_int_inequality_proof(&arena, &[e1, e2]);
    assert!(
        proof.is_ok(),
        "1≤3x ∧ 3x<3 should reconstruct to False, got {:?}",
        proof.err()
    );
    let (fragment, _src) = prove_unsat_to_lean_module(&mut arena, &[e1, e2])
        .expect("strict/oriented interval should prove unsat");
    assert_eq!(fragment, ProofFragment::IntInequality);
}

/// A shifted interval `3*x ≥ 4 ∧ 3*x ≤ 5` (no multiple of 3 in `[4, 5]`, infeasible;
/// the reduction offset is `m = 1`, so `1 < x < 2`). Exercises the general `m ≠ 0`
/// additive-shift path.
#[test]
fn shifted_interval_reconstructs_to_false() {
    let mut arena = TermArena::new();
    let x = arena.int_var("x").unwrap();
    let three = arena.int_const(3);
    let three_x = arena.int_mul(three, x).unwrap();
    let four = arena.int_const(4);
    let five = arena.int_const(5);
    let e1 = arena.int_ge(three_x, four).unwrap(); // 3x ≥ 4
    let e2 = arena.int_le(three_x, five).unwrap(); // 3x ≤ 5

    let proof = reconstruct_int_inequality_proof(&arena, &[e1, e2]);
    assert!(
        proof.is_ok(),
        "3x≥4 ∧ 3x≤5 (m=1) should reconstruct to False, got {:?}",
        proof.err()
    );
    let (fragment, _src) = prove_unsat_to_lean_module(&mut arena, &[e1, e2])
        .expect("shifted interval should prove unsat");
    assert_eq!(fragment, ProofFragment::IntInequality);
}

/// An integer-FEASIBLE inequality system `2*x ≥ 1 ∧ 2*x ≤ 3` (sat at `x = 1`, since
/// `2·1 = 2 ∈ [1, 3]`) has no integer-cut refutation and must be declined — never
/// fabricated, and not classified as the `IntInequality` fragment.
#[test]
fn feasible_interval_is_declined() {
    let mut arena = TermArena::new();
    let x = arena.int_var("x").unwrap();
    let two = arena.int_const(2);
    let two_x = arena.int_mul(two, x).unwrap();
    let one = arena.int_const(1);
    let three = arena.int_const(3);
    let e1 = arena.int_ge(two_x, one).unwrap(); // 2x ≥ 1
    let e2 = arena.int_le(two_x, three).unwrap(); // 2x ≤ 3  (x=1 ⇒ 2 ∈ [1,3])

    assert!(
        reconstruct_int_inequality_proof(&arena, &[e1, e2]).is_err(),
        "a feasible integer interval must not produce a refutation"
    );
    assert_ne!(
        scan_proof_fragment(&arena, &[e1, e2]),
        ProofFragment::IntInequality,
        "feasible interval should not route to the IntInequality fragment"
    );
}

/// `3*x ≥ 2 ∧ 2*x ≤ 1` over `Int`: **different** multipliers (lower `k=3`, upper
/// `k=2`). The lower integer cut forces `x ≥ 1` (`3x ≥ 2 ⇒ x > 0`, `m_lo = 0`) and the
/// upper forces `x ≤ 0` (`2x ≤ 1 ⇒ x < 1`, `m_hi = 0`), leaving the empty window
/// `(0, 1)`. The equal-multiplier detector does not cover distinct `k`, so this routes
/// to the new different-multiplier reconstructor through the `IntInequality` fragment.
#[test]
fn diff_mult_interval_reconstructs_to_false() {
    let mut arena = TermArena::new();
    let x = arena.int_var("x").unwrap();
    let three = arena.int_const(3);
    let two = arena.int_const(2);
    let three_x = arena.int_mul(three, x).unwrap();
    let two_x = arena.int_mul(two, x).unwrap();
    let lo = arena.int_const(2);
    let hi = arena.int_const(1);
    let e1 = arena.int_ge(three_x, lo).unwrap(); // 3x ≥ 2  ⇒ x ≥ 1
    let e2 = arena.int_le(two_x, hi).unwrap(); // 2x ≤ 1  ⇒ x ≤ 0

    let proof = reconstruct_int_inequality_proof(&arena, &[e1, e2]);
    assert!(
        proof.is_ok(),
        "3x≥2 ∧ 2x≤1 (different multipliers) should reconstruct to False, got {:?}",
        proof.err()
    );
    let (fragment, source) = prove_unsat_to_lean_module(&mut arena, &[e1, e2])
        .expect("different-multiplier interval should prove unsat to a Lean module");
    assert_eq!(fragment, ProofFragment::IntInequality);
    assert!(source.contains("axeyum_refutation"));
    assert_eq!(
        scan_proof_fragment(&arena, &[e1, e2]),
        ProofFragment::IntInequality
    );
}

/// A different-multiplier interval with a **non-zero shared offset** `m_lo = m_hi = 1`:
/// `5 ≤ 3*x ∧ 2*x ≤ 3` gives `m_lo = ⌊4/3⌋ = 1` (so `3x ≥ 5 ⇒ x > 1`) and
/// `m_hi = ⌊3/2⌋ = 1` (so `2x ≤ 3 ⇒ x < 2`), the empty open window `(1, 2)`. Exercises
/// the `m ≠ 0` additive shift on the different-multiplier path with both offsets equal.
#[test]
fn diff_mult_shifted_interval_reconstructs() {
    let mut arena = TermArena::new();
    let x = arena.int_var("x").unwrap();
    let three = arena.int_const(3);
    let two = arena.int_const(2);
    let three_x = arena.int_mul(three, x).unwrap();
    let two_x = arena.int_mul(two, x).unwrap();
    let lo = arena.int_const(5);
    let hi = arena.int_const(3);
    let e1 = arena.int_ge(three_x, lo).unwrap(); // 3x ≥ 5 ⇒ x > 1
    let e2 = arena.int_le(two_x, hi).unwrap(); // 2x ≤ 3 ⇒ x < 2

    let proof = reconstruct_int_inequality_proof(&arena, &[e1, e2]);
    assert!(
        proof.is_ok(),
        "5≤3x ∧ 2x≤3 should reconstruct to False, got {:?}",
        proof.err()
    );
    let (fragment, _src) = prove_unsat_to_lean_module(&mut arena, &[e1, e2])
        .expect("shifted different-multiplier interval should prove unsat");
    assert_eq!(fragment, ProofFragment::IntInequality);
}

/// A different-multiplier interval where the offsets **differ** (`m_hi < m_lo`):
/// `7 ≤ 4*x ∧ 3*x ≤ 5` ⇒ `x ≥ 2` (from `4x ≥ 7`, `m_lo = ⌊6/4⌋ = 1`, `x > 1`) and
/// `x ≤ 1` (from `3x ≤ 5`, `m_hi = ⌊5/3⌋ = 1`)… here both are 1. Use `9 ≤ 4*x ∧ 3*x ≤ 5`:
/// `m_lo = ⌊8/4⌋ = 2` (`x > 2`), `m_hi = ⌊5/3⌋ = 1` (`x < 2`), so `m_hi (1) < m_lo (2)`
/// — exercising the upper-bound weakening branch (`lt x 2 ⇒ lt x 3`).
#[test]
fn diff_mult_unequal_offsets_reconstructs() {
    let mut arena = TermArena::new();
    let x = arena.int_var("x").unwrap();
    let four = arena.int_const(4);
    let three = arena.int_const(3);
    let four_x = arena.int_mul(four, x).unwrap();
    let three_x = arena.int_mul(three, x).unwrap();
    let lo = arena.int_const(9);
    let hi = arena.int_const(5);
    let e1 = arena.int_ge(four_x, lo).unwrap(); // 4x ≥ 9 ⇒ x > 2 (m_lo = 2)
    let e2 = arena.int_le(three_x, hi).unwrap(); // 3x ≤ 5 ⇒ x < 2 (m_hi = 1)

    let proof = reconstruct_int_inequality_proof(&arena, &[e1, e2]);
    assert!(
        proof.is_ok(),
        "9≤4x ∧ 3x≤5 (unequal offsets) should reconstruct to False, got {:?}",
        proof.err()
    );
    let (fragment, _src) = prove_unsat_to_lean_module(&mut arena, &[e1, e2])
        .expect("unequal-offset different-multiplier interval should prove unsat");
    assert_eq!(fragment, ProofFragment::IntInequality);
}

/// An integer-FEASIBLE different-multiplier interval `3*x ≥ 2 ∧ 2*x ≤ 5` ⇒ `x ≥ 1`
/// and `x ≤ 2`, satisfiable at `x = 1` or `x = 2`. It has no integer-cut refutation and
/// must be declined — never fabricated, and not routed to `IntInequality`.
#[test]
fn diff_mult_feasible_interval_is_declined() {
    let mut arena = TermArena::new();
    let x = arena.int_var("x").unwrap();
    let three = arena.int_const(3);
    let two = arena.int_const(2);
    let three_x = arena.int_mul(three, x).unwrap();
    let two_x = arena.int_mul(two, x).unwrap();
    let lo = arena.int_const(2);
    let hi = arena.int_const(5);
    let e1 = arena.int_ge(three_x, lo).unwrap(); // 3x ≥ 2 ⇒ x ≥ 1
    let e2 = arena.int_le(two_x, hi).unwrap(); // 2x ≤ 5 ⇒ x ≤ 2 (x=1,2 feasible)

    assert!(
        reconstruct_int_inequality_proof(&arena, &[e1, e2]).is_err(),
        "a feasible different-multiplier interval must not produce a refutation"
    );
    assert_ne!(
        scan_proof_fragment(&arena, &[e1, e2]),
        ProofFragment::IntInequality,
        "feasible different-multiplier interval should not route to IntInequality"
    );
}

/// **Real-Lean crosscheck** of the different-multiplier reconstruction: the rendered
/// `9 ≤ 4*x ∧ 3*x ≤ 5` module (unequal offsets, exercises the weakening branch) must be
/// accepted by a genuine `lean` binary with no `sorryAx` dependency (skips if no Lean).
#[test]
fn diff_mult_module_checks_in_real_lean() {
    let mut arena = TermArena::new();
    let x = arena.int_var("x").unwrap();
    let four = arena.int_const(4);
    let three = arena.int_const(3);
    let four_x = arena.int_mul(four, x).unwrap();
    let three_x = arena.int_mul(three, x).unwrap();
    let lo = arena.int_const(9);
    let hi = arena.int_const(5);
    let e1 = arena.int_ge(four_x, lo).unwrap();
    let e2 = arena.int_le(three_x, hi).unwrap();
    let (frag, source) = prove_unsat_to_lean_module(&mut arena, &[e1, e2])
        .expect("different-multiplier interval reconstructs to a Lean module");
    assert_eq!(frag, ProofFragment::IntInequality);

    let Some(bin) = lean_bin() else {
        eprintln!("[skip] diff_mult: lean binary not found; set AXEYUM_LEAN_BIN to enable");
        return;
    };
    let dir = std::env::temp_dir().join("axeyum_lean_diff_mult");
    std::fs::create_dir_all(&dir).expect("create temp dir");
    let file = dir.join("diff_mult.lean");
    std::fs::write(&file, &source).expect("write lean module");
    let out = Command::new(&bin).arg(&file).output().expect("run lean");
    let stdout = String::from_utf8_lossy(&out.stdout);
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(
        out.status.success(),
        "lean REJECTED the diff_mult module\n=== stdout ===\n{stdout}\n=== stderr ===\n{stderr}\n=== source ===\n{source}"
    );
    assert!(
        !stdout.contains("sorryAx"),
        "diff_mult proof depends on sorryAx:\n{stdout}"
    );
    assert!(
        stdout.contains("axeyum_refutation"),
        "missing #print axioms output:\n{stdout}"
    );
    eprintln!(
        "[lean ok] diff_mult: {}",
        stdout.trim().replace('\n', " | ")
    );
}

/// `2*x = 4 ∧ x ≥ 3` over `Int`: an **equality combined with a unit-multiplier bound**.
/// The equality pins `x = 2`, which violates `x ≥ 3`, so the conjunction is already
/// real-infeasible — yet the Diophantine path declines (the equality `2x = 4` alone is
/// feasible, `2 | 4`) and the interval detectors require two inequalities. This routes to
/// the new equality-and-bound reconstructor through the `IntInequality` fragment.
#[test]
fn eq_bound_lower_reconstructs_to_false() {
    let mut arena = TermArena::new();
    let x = arena.int_var("x").unwrap();
    let two = arena.int_const(2);
    let two_x = arena.int_mul(two, x).unwrap();
    let four = arena.int_const(4);
    let three = arena.int_const(3);
    let e1 = arena.eq(two_x, four).unwrap(); // 2x = 4 ⇒ x = 2
    let e2 = arena.int_ge(x, three).unwrap(); // x ≥ 3

    let proof = reconstruct_int_inequality_proof(&arena, &[e1, e2]);
    assert!(
        proof.is_ok(),
        "2x=4 ∧ x≥3 should reconstruct to False, got {:?}",
        proof.err()
    );
    let (fragment, source) = prove_unsat_to_lean_module(&mut arena, &[e1, e2])
        .expect("equality-and-bound system should prove unsat to a Lean module");
    assert_eq!(fragment, ProofFragment::IntInequality);
    assert!(source.contains("axeyum_refutation"));
    assert_eq!(
        scan_proof_fragment(&arena, &[e1, e2]),
        ProofFragment::IntInequality
    );
}

/// `x ≤ 1 ∧ 3*x = 6` over `Int` (bound first, equality second; upper-bound branch). The
/// equality pins `x = 2`, violating `x ≤ 1`. Exercises both assertion orders and the
/// upper-bound close. `3 | 6` keeps the equality alone feasible, so Diophantine declines.
#[test]
fn eq_bound_upper_reconstructs_to_false() {
    let mut arena = TermArena::new();
    let x = arena.int_var("x").unwrap();
    let three = arena.int_const(3);
    let three_x = arena.int_mul(three, x).unwrap();
    let six = arena.int_const(6);
    let one = arena.int_const(1);
    let e1 = arena.int_le(x, one).unwrap(); // x ≤ 1
    let e2 = arena.eq(three_x, six).unwrap(); // 3x = 6 ⇒ x = 2

    let proof = reconstruct_int_inequality_proof(&arena, &[e1, e2]);
    assert!(
        proof.is_ok(),
        "x≤1 ∧ 3x=6 should reconstruct to False, got {:?}",
        proof.err()
    );
    let (fragment, _src) = prove_unsat_to_lean_module(&mut arena, &[e1, e2])
        .expect("upper-bound equality-and-bound system should prove unsat");
    assert_eq!(fragment, ProofFragment::IntInequality);
}

/// A **feasible** equality-and-bound system `2*x = 4 ∧ x ≥ 1` (`x = 2` satisfies both).
/// It has no refutation and must be declined — never fabricated, and not routed to the
/// `IntInequality` fragment.
#[test]
fn eq_bound_feasible_is_declined() {
    let mut arena = TermArena::new();
    let x = arena.int_var("x").unwrap();
    let two = arena.int_const(2);
    let two_x = arena.int_mul(two, x).unwrap();
    let four = arena.int_const(4);
    let one = arena.int_const(1);
    let e1 = arena.eq(two_x, four).unwrap(); // 2x = 4 ⇒ x = 2
    let e2 = arena.int_ge(x, one).unwrap(); // x ≥ 1 (x = 2 feasible)

    assert!(
        reconstruct_int_inequality_proof(&arena, &[e1, e2]).is_err(),
        "a feasible equality-and-bound system must not produce a refutation"
    );
    assert_ne!(
        scan_proof_fragment(&arena, &[e1, e2]),
        ProofFragment::IntInequality,
        "feasible equality-and-bound system should not route to IntInequality"
    );
}

/// **Real-Lean crosscheck** of the equality-and-bound reconstruction: the rendered
/// `2*x = 4 ∧ x ≥ 3` module must be accepted by a genuine `lean` binary with no `sorryAx`
/// dependency (skips if no Lean), with the axiom audit naming only the prelude axioms and
/// the two verbatim hypotheses.
#[test]
fn eq_bound_module_checks_in_real_lean() {
    let mut arena = TermArena::new();
    let x = arena.int_var("x").unwrap();
    let two = arena.int_const(2);
    let two_x = arena.int_mul(two, x).unwrap();
    let four = arena.int_const(4);
    let three = arena.int_const(3);
    let e1 = arena.eq(two_x, four).unwrap();
    let e2 = arena.int_ge(x, three).unwrap();
    let (frag, source) = prove_unsat_to_lean_module(&mut arena, &[e1, e2])
        .expect("equality-and-bound reconstructs to a Lean module");
    assert_eq!(frag, ProofFragment::IntInequality);

    let Some(bin) = lean_bin() else {
        eprintln!("[skip] eq_bound: lean binary not found; set AXEYUM_LEAN_BIN to enable");
        return;
    };
    let dir = std::env::temp_dir().join("axeyum_lean_int_eq_bound");
    std::fs::create_dir_all(&dir).expect("create temp dir");
    let file = dir.join("int_eq_bound.lean");
    std::fs::write(&file, &source).expect("write lean module");
    let out = Command::new(&bin).arg(&file).output().expect("run lean");
    let stdout = String::from_utf8_lossy(&out.stdout);
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(
        out.status.success(),
        "lean REJECTED the eq_bound module\n=== stdout ===\n{stdout}\n=== stderr ===\n{stderr}\n=== source ===\n{source}"
    );
    assert!(
        !stdout.contains("sorryAx"),
        "eq_bound proof depends on sorryAx:\n{stdout}"
    );
    assert!(
        stdout.contains("axeyum_refutation"),
        "missing #print axioms output:\n{stdout}"
    );
    eprintln!("[lean ok] eq_bound: {}", stdout.trim().replace('\n', " | "));
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

/// **Real-Lean crosscheck**: the rendered integer-interval module must be accepted by
/// a genuine `lean` binary (skips gracefully if none is installed), and
/// `#print axioms axeyum_refutation` must not depend on `sorryAx`. This is the
/// end-to-end kernel-checked integer-inequality payoff of ADR-0042.
#[test]
fn int_inequality_module_checks_in_real_lean() {
    let mut arena = TermArena::new();
    let x = arena.int_var("x").unwrap();
    let three = arena.int_const(3);
    let three_x = arena.int_mul(three, x).unwrap();
    let one = arena.int_const(1);
    let two = arena.int_const(2);
    let e1 = arena.int_ge(three_x, one).unwrap();
    let e2 = arena.int_le(three_x, two).unwrap();
    let (frag, source) = prove_unsat_to_lean_module(&mut arena, &[e1, e2])
        .expect("integer-interval system reconstructs to a Lean module");
    assert_eq!(frag, ProofFragment::IntInequality);

    let Some(bin) = lean_bin() else {
        eprintln!("[skip] int_inequality: lean binary not found; set AXEYUM_LEAN_BIN to enable");
        return;
    };
    let dir = std::env::temp_dir().join("axeyum_lean_int_inequality");
    std::fs::create_dir_all(&dir).expect("create temp dir");
    let file = dir.join("int_inequality.lean");
    std::fs::write(&file, &source).expect("write lean module");
    let out = Command::new(&bin).arg(&file).output().expect("run lean");
    let stdout = String::from_utf8_lossy(&out.stdout);
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(
        out.status.success(),
        "lean REJECTED the int_inequality module\n=== stdout ===\n{stdout}\n=== stderr ===\n{stderr}\n=== source ===\n{source}"
    );
    assert!(
        !stdout.contains("sorryAx"),
        "int_inequality proof depends on sorryAx:\n{stdout}"
    );
    assert!(
        stdout.contains("axeyum_refutation"),
        "missing #print axioms output:\n{stdout}"
    );
    eprintln!(
        "[lean ok] int_inequality: {}",
        stdout.trim().replace('\n', " | ")
    );
}
