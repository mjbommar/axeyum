//! Cross-checks for the **is-tester** datatype certificate emitted by
//! [`prove_qf_dt_unsat_alethe_via_simplification`] (gap-analysis Gap 14, the
//! is-tester twin of the certified `select`-over-`construct` fold).
//!
//! Each `is_C(K(args))` redex is abstracted to a fresh `BitVec(1)` truth-bit `w`
//! (the redex substituted by the predicate `(= w #b1)`), the **test-fold**
//! premise — `(= (is_C (K args)) #b1)` when `K == C`, else the disequality
//! `(not (= (is_C (K args)) #b1))` — is asserted as a trusted premise, and the
//! truth fact over `(= w #b1)` is derived by `eq_transitive` (true) or
//! `cong`+`equiv1` (false), then resolved into the bit-blast refutation. Carcara
//! (no datatype rule) treats the reserved `!dttest_n_c` / `!dtcon_m_K` heads as
//! uninterpreted functions and takes the test-fold as a premise; it then checks
//! every *structural* step. Honest residual: the is-tester fold stays a premise;
//! the COLLAPSE reasoning is Carcara-/kernel-checked. The field-unification axioms
//! (distinctness, injectivity, acyclicity) stay trusted and are out of scope.
//!
//! Carcara lives in the gitignored `references/` tree (absent in CI), so each
//! real-checker test **skips** (prints a note, passes) when the binary is absent.
//!
//! **Lean reconstruction is deferred** for the is-tester collapse: the fragment
//! dispatch does not yet route datatype is-tester proofs to a datatype
//! reconstructor (it would fall through to the `QF_UFBV` reconstructor, which
//! rejects them). The Carcara route below fully certifies the COLLAPSE reasoning;
//! the kernel-checked Lean twin is follow-up work.

use std::path::{Path, PathBuf};
use std::process::Command;

use axeyum_cnf::{AletheCommand, write_alethe};
use axeyum_ir::{ConstructorId, Sort, TermArena, TermId};
use axeyum_solver::prove_qf_dt_unsat_alethe_via_simplification;

/// Resolves the Carcara binary: `AXEYUM_CARCARA_BIN` if set, otherwise the
/// conventional reference build path. Returns `None` (→ skip) if unavailable.
fn carcara_bin() -> Option<PathBuf> {
    if let Ok(p) = std::env::var("AXEYUM_CARCARA_BIN") {
        let path = PathBuf::from(p);
        return path.is_file().then_some(path);
    }
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../references/carcara/target/release/carcara");
    path.is_file().then_some(path)
}

/// Runs `carcara check` over `smt2_text` + `proof`, returning the combined
/// stdout/stderr. Asserts a hole-free `valid` when `expect_valid`; otherwise
/// asserts a rejection (no clean `valid`).
fn carcara_check(
    bin: &Path,
    tag: &str,
    smt2_text: &str,
    proof: &[AletheCommand],
    expect_valid: bool,
) -> String {
    let dir = std::env::temp_dir().join(format!("axeyum_dttest_{tag}"));
    std::fs::create_dir_all(&dir).expect("create temp dir");
    let smt2 = dir.join("problem.smt2");
    let alethe = dir.join("proof.alethe");
    std::fs::write(&smt2, smt2_text).expect("write smt2");
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
    let accepted =
        out.status.success() && combined.contains("valid") && !combined.contains("holey");
    if expect_valid {
        assert!(accepted, "carcara rejected the {tag} proof:\n{combined}");
    } else {
        assert!(
            !accepted,
            "carcara ACCEPTED a tampered {tag} proof (expected rejection):\n{combined}"
        );
    }
    combined
}

/// A `BitVec(width)` variable named `name`.
fn bvw(arena: &mut TermArena, name: &str, width: u32) -> TermId {
    let s = arena.declare(name, Sort::BitVec(width)).unwrap();
    arena.var(s)
}

/// Builds a two-constructor `Color` datatype `Red(v : BitVec 2) | Green(w : BitVec 2)`.
fn color_datatype(arena: &mut TermArena) -> (ConstructorId, ConstructorId) {
    let color = arena.declare_datatype("Color");
    let red = arena.add_constructor(color, "Red", &[("v".into(), Sort::BitVec(2))]);
    let green = arena.add_constructor(color, "Green", &[("w".into(), Sort::BitVec(2))]);
    (red, green)
}

/// The `.smt2` declaring the reserved heads as plain uninterpreted functions over
/// an uninterpreted `Color` sort, then asserting `residual_asserts` (the textual
/// residual the proof's `assume`s reference). The two `!dttest`/`!dtcon` heads and
/// the truth-bit `!dt_t_0` plus the field var `a` are declared.
fn tester_smt2(residual_asserts: &str) -> String {
    format!(
        "\
(set-logic QF_UFBV)
(declare-sort Color 0)
(declare-const a (_ BitVec 2))
(declare-const !dt_t_0 (_ BitVec 1))
(declare-fun !dtcon_1_Green ((_ BitVec 2)) Color)
(declare-fun !dttest_1_Green (Color) (_ BitVec 1))
(declare-fun !dttest_1_Red (Color) (_ BitVec 1))
{residual_asserts}(check-sat)
"
    )
}

// =====================================================================
// (1) Same-constructor TRUE fold: ¬is_Green(Green(a)) is UNSAT.
// =====================================================================
#[test]
fn tester_true_fold_is_accepted_by_carcara() {
    let Some(bin) = carcara_bin() else {
        eprintln!("[skip] carcara binary not found; build references/carcara to enable");
        return;
    };
    let mut arena = TermArena::new();
    let (_red, green) = color_datatype(&mut arena);
    let a = bvw(&mut arena, "a", 2);
    let g = arena.construct(green, &[a]).unwrap();
    let is_green = arena.dt_test(green, g).unwrap();
    let not_is = arena.not(is_green).unwrap();
    let proof = prove_qf_dt_unsat_alethe_via_simplification(&mut arena, &[not_is])
        .expect("emit is-tester (true fold) proof");
    // Residual: ¬(= !dt_t_0 #b1) [the negated assertion]; the abstraction def and
    // the TRUE test-fold (= (is_Green (Green a)) #b1) are the proof's premises.
    let smt2 = tester_smt2(
        "(assert (not (= !dt_t_0 #b1)))
(assert (= !dt_t_0 (!dttest_1_Green (!dtcon_1_Green a))))
(assert (= (!dttest_1_Green (!dtcon_1_Green a)) #b1))
",
    );
    let report = carcara_check(&bin, "tester_true", &smt2, &proof, true);
    assert!(report.contains("valid"), "expected valid, got:\n{report}");
}

// =====================================================================
// (2) Different-constructor FALSE fold: is_Red(Green(a)) is UNSAT.
// =====================================================================
#[test]
fn tester_false_fold_is_accepted_by_carcara() {
    let Some(bin) = carcara_bin() else {
        eprintln!("[skip] carcara binary not found; build references/carcara to enable");
        return;
    };
    let mut arena = TermArena::new();
    let (red, green) = color_datatype(&mut arena);
    let a = bvw(&mut arena, "a", 2);
    let g = arena.construct(green, &[a]).unwrap();
    let is_red_green = arena.dt_test(red, g).unwrap();
    let proof = prove_qf_dt_unsat_alethe_via_simplification(&mut arena, &[is_red_green])
        .expect("emit is-tester (false fold) proof");
    // Residual: (= !dt_t_0 #b1) [the positive assertion]; the abstraction def and
    // the FALSE test-fold (not (= (is_Red (Green a)) #b1)) are the proof's premises.
    let smt2 = tester_smt2(
        "(assert (= !dt_t_0 #b1))
(assert (= !dt_t_0 (!dttest_1_Red (!dtcon_1_Green a))))
(assert (not (= (!dttest_1_Red (!dtcon_1_Green a)) #b1)))
",
    );
    let report = carcara_check(&bin, "tester_false", &smt2, &proof, true);
    assert!(report.contains("valid"), "expected valid, got:\n{report}");
}

// =====================================================================
// (3) Direct tester contradiction is_C(K) ∧ ¬is_C(K) collapses to (cl).
//     (Here is_Red(Green) ∧ ¬is_Red(Green): the SAME tester redex, two polarities;
//     both fold to #b0, so the residual is the unit conflict over (= w #b1).)
// =====================================================================
#[test]
fn tester_polarity_contradiction_is_accepted_by_carcara() {
    let Some(bin) = carcara_bin() else {
        eprintln!("[skip] carcara binary not found; build references/carcara to enable");
        return;
    };
    let mut arena = TermArena::new();
    let (red, green) = color_datatype(&mut arena);
    let a = bvw(&mut arena, "a", 2);
    let g = arena.construct(green, &[a]).unwrap();
    let is_red_green = arena.dt_test(red, g).unwrap();
    let not_is = arena.not(is_red_green).unwrap();
    // is_Red(Green) ∧ ¬is_Red(Green): trivially UNSAT, and the is-tester fold
    // (false) makes the single shared redex `(= w #b1)` appear with both polarities.
    let proof = prove_qf_dt_unsat_alethe_via_simplification(&mut arena, &[is_red_green, not_is])
        .expect("emit is-tester polarity-contradiction proof");
    let smt2 = tester_smt2(
        "(assert (= !dt_t_0 #b1))
(assert (not (= !dt_t_0 #b1)))
(assert (= !dt_t_0 (!dttest_1_Red (!dtcon_1_Green a))))
(assert (not (= (!dttest_1_Red (!dtcon_1_Green a)) #b1)))
",
    );
    carcara_check(&bin, "tester_polarity", &smt2, &proof, true);
}

// =====================================================================
// (4) TAMPER: flipping the TRUE test-fold to #b0 must be rejected by Carcara.
//     We re-emit the true-fold proof, then corrupt the test-fold premise so the
//     `eq_transitive` no longer derives `(= w #b1)`. Carcara must REJECT.
// =====================================================================
#[test]
fn tester_tampered_fold_is_rejected_by_carcara() {
    let Some(bin) = carcara_bin() else {
        eprintln!("[skip] carcara binary not found; build references/carcara to enable");
        return;
    };
    let mut arena = TermArena::new();
    let (_red, green) = color_datatype(&mut arena);
    let a = bvw(&mut arena, "a", 2);
    let g = arena.construct(green, &[a]).unwrap();
    let is_green = arena.dt_test(green, g).unwrap();
    let not_is = arena.not(is_green).unwrap();
    let mut proof = prove_qf_dt_unsat_alethe_via_simplification(&mut arena, &[not_is])
        .expect("emit is-tester (true fold) proof");
    // Tamper: rewrite the `eq_transitive` conclusion to claim `(= w #b1)` from a
    // BROKEN chain — drop one transitivity hypothesis literal so the rule no longer
    // licenses the conclusion. Carcara must reject the malformed `eq_transitive`.
    tamper_first_eq_transitive(&mut proof);
    let smt2 = tester_smt2(
        "(assert (not (= !dt_t_0 #b1)))
(assert (= !dt_t_0 (!dttest_1_Green (!dtcon_1_Green a))))
(assert (= (!dttest_1_Green (!dtcon_1_Green a)) #b1))
",
    );
    carcara_check(&bin, "tester_tamper", &smt2, &proof, false);
}

/// Corrupts the first `eq_transitive` step by deleting one of its negated
/// transitivity hypotheses, breaking the rule's premise chain (the conclusion is
/// then unjustified). Used by the tamper test to confirm Carcara catches it.
fn tamper_first_eq_transitive(proof: &mut [AletheCommand]) {
    for cmd in proof.iter_mut() {
        if let AletheCommand::Step { rule, clause, .. } = cmd
            && rule == "eq_transitive"
            && clause.len() >= 2
        {
            clause.remove(0);
            return;
        }
    }
    panic!("no eq_transitive step found to tamper");
}
