//! Cross-checks for the **constructor distinctness** datatype certificate emitted
//! by [`prove_qf_dt_distinct_alethe_carcara`] (gap-analysis Gap 14, narrowing the
//! `TrustId::DatatypeElim` hole by COMPOSING the certified is-tester collapse with
//! congruence).
//!
//! Given an asserted constructor equality `(= (C x…) (D y…))` with **distinct**
//! constructors `C != D`, the emitter refutes it by:
//!
//! 1. taking `(= (C x…) (D y…))` as the trusted premise `h`;
//! 2. `cong`-lifting `h` under the tester head `is_C` to
//!    `(= (is_C (C x…)) (is_C (D y…)))`;
//! 3. the two **trusted is-tester folds** `(= #b1 (is_C (C x…)))` (true, `C == C`)
//!    and `(= (is_C (D y…)) #b0)` (false, `C != D`);
//! 4. a single `eq_transitive` chaining `#b1 = is_C(C x…) = is_C(D y…) = #b0` to
//!    the contradiction `(= #b1 #b0)`, resolved against the three equalities;
//! 5. `evaluate` (`#b1 != #b0`) + `equiv1` + the `false` tautology + `resolution`
//!    closing to the empty clause `(cl)`.
//!
//! Carcara (no datatype rule) treats the reserved `!dttest_n_C` / `!dtcon_m_K`
//! heads as uninterpreted functions and takes the constructor equality and the two
//! is-tester folds as premises; it then checks every *structural* step (`cong`,
//! `eq_transitive`, `resolution`, `evaluate`, `equiv1`, `false`). **Honest
//! residual:** the constructor equality and the two is-tester folds stay trusted
//! premises; the DISTINCTNESS reasoning (a constructor equality between distinct
//! `C != D` forces `#b1 = #b0`, i.e. ⊥) is Carcara-checked. Constructor
//! **injectivity** and **acyclicity** stay trusted/deferred and are out of scope.
//!
//! Carcara lives in the gitignored `references/` tree (absent in CI), so each
//! real-checker test **skips** (prints a note, passes) when the binary is absent.
//!
//! **Lean reconstruction is deferred** for the distinctness collapse (it composes
//! the deferred is-tester reconstruction); the Carcara route below fully certifies
//! the COLLAPSE reasoning.

use std::path::{Path, PathBuf};
use std::process::Command;

use axeyum_cnf::{AletheCommand, write_alethe};
use axeyum_ir::{ConstructorId, Sort, TermArena, TermId};
use axeyum_solver::prove_qf_dt_distinct_alethe_carcara;

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
    let dir = std::env::temp_dir().join(format!("axeyum_dtdistinct_{tag}"));
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

/// Builds a two-constructor `Shape` datatype
/// `Circle(r : BitVec 3) | Box(s : BitVec 3)` on a distinct sort, exercising a
/// different sort / width than `Color`.
fn shape_datatype(arena: &mut TermArena) -> (ConstructorId, ConstructorId) {
    let shape = arena.declare_datatype("Shape");
    let circle = arena.add_constructor(shape, "Circle", &[("r".into(), Sort::BitVec(3))]);
    let boxc = arena.add_constructor(shape, "Box", &[("s".into(), Sort::BitVec(3))]);
    (circle, boxc)
}

/// The `.smt2` for the `Color` distinctness problem: declares the reserved heads as
/// plain uninterpreted functions over an uninterpreted `Color` sort, then asserts
/// `residual_asserts` (the textual premises the proof's `assume`s reference).
fn color_smt2(residual_asserts: &str) -> String {
    format!(
        "\
(set-logic QF_UFBV)
(declare-sort Color 0)
(declare-const a (_ BitVec 2))
(declare-const b (_ BitVec 2))
(declare-fun !dtcon_1_Red ((_ BitVec 2)) Color)
(declare-fun !dtcon_1_Green ((_ BitVec 2)) Color)
(declare-fun !dttest_1_Red (Color) (_ BitVec 1))
{residual_asserts}(check-sat)
"
    )
}

// =====================================================================
// (1) Distinct constructors `Red(a) = Green(b)` is UNSAT (refuted via the
//     is-tester collapse on `is_Red`).
// =====================================================================
#[test]
fn distinct_constructors_contradiction_is_accepted_by_carcara() {
    let Some(bin) = carcara_bin() else {
        eprintln!("[skip] carcara binary not found; build references/carcara to enable");
        return;
    };
    let mut arena = TermArena::new();
    let (red, green) = color_datatype(&mut arena);
    let a = bvw(&mut arena, "a", 2);
    let b = bvw(&mut arena, "b", 2);
    let red_a = arena.construct(red, &[a]).unwrap();
    let green_b = arena.construct(green, &[b]).unwrap();
    let eq = arena.eq(red_a, green_b).unwrap();
    let proof = prove_qf_dt_distinct_alethe_carcara(&arena, &[eq])
        .expect("emit distinctness (Red != Green) proof");
    // Premises: the constructor equality `h`, plus the two trusted is-tester folds
    // (`is_Red(Red a) = #b1`, `is_Red(Green b) = #b0`).
    let smt2 = color_smt2(
        "(assert (= (!dtcon_1_Red a) (!dtcon_1_Green b)))
(assert (= #b1 (!dttest_1_Red (!dtcon_1_Red a))))
(assert (= (!dttest_1_Red (!dtcon_1_Green b)) #b0))
",
    );
    let report = carcara_check(&bin, "distinct_color", &smt2, &proof, true);
    assert!(report.contains("valid"), "expected valid, got:\n{report}");
}

/// The `.smt2` for the `Shape` distinctness problem (`Circle` vs `Box`, both unary
/// over `BitVec 3`), exercising a distinct sort and width.
fn shape_smt2(residual_asserts: &str) -> String {
    format!(
        "\
(set-logic QF_UFBV)
(declare-sort Shape 0)
(declare-const c (_ BitVec 3))
(declare-const d (_ BitVec 3))
(declare-fun !dtcon_1_Circle ((_ BitVec 3)) Shape)
(declare-fun !dtcon_1_Box ((_ BitVec 3)) Shape)
(declare-fun !dttest_1_Circle (Shape) (_ BitVec 1))
{residual_asserts}(check-sat)
"
    )
}

// =====================================================================
// (2) A second distinct pair on a different sort/width: `Circle(c) = Box(d)`
//     is UNSAT. The tested constructor is `Circle`; `is_Circle(Circle c) = #b1`,
//     `is_Circle(Box d) = #b0`.
// =====================================================================
#[test]
fn distinct_constructors_other_sort_is_accepted_by_carcara() {
    let Some(bin) = carcara_bin() else {
        eprintln!("[skip] carcara binary not found; build references/carcara to enable");
        return;
    };
    let mut arena = TermArena::new();
    let (circle, boxc) = shape_datatype(&mut arena);
    let c = bvw(&mut arena, "c", 3);
    let d = bvw(&mut arena, "d", 3);
    let circle_c = arena.construct(circle, &[c]).unwrap();
    let box_d = arena.construct(boxc, &[d]).unwrap();
    let eq = arena.eq(circle_c, box_d).unwrap();
    let proof = prove_qf_dt_distinct_alethe_carcara(&arena, &[eq])
        .expect("emit distinctness (Circle != Box) proof");
    let smt2 = shape_smt2(
        "(assert (= (!dtcon_1_Circle c) (!dtcon_1_Box d)))
(assert (= #b1 (!dttest_1_Circle (!dtcon_1_Circle c))))
(assert (= (!dttest_1_Circle (!dtcon_1_Box d)) #b0))
",
    );
    let report = carcara_check(&bin, "distinct_shape", &smt2, &proof, true);
    assert!(report.contains("valid"), "expected valid, got:\n{report}");
}

// =====================================================================
// (3) TAMPER: corrupt the `eq_transitive` chain so it no longer derives
//     `(= #b1 #b0)`. Carcara must REJECT.
// =====================================================================
#[test]
fn distinct_tampered_chain_is_rejected_by_carcara() {
    let Some(bin) = carcara_bin() else {
        eprintln!("[skip] carcara binary not found; build references/carcara to enable");
        return;
    };
    let mut arena = TermArena::new();
    let (red, green) = color_datatype(&mut arena);
    let a = bvw(&mut arena, "a", 2);
    let b = bvw(&mut arena, "b", 2);
    let red_a = arena.construct(red, &[a]).unwrap();
    let green_b = arena.construct(green, &[b]).unwrap();
    let eq = arena.eq(red_a, green_b).unwrap();
    let mut proof =
        prove_qf_dt_distinct_alethe_carcara(&arena, &[eq]).expect("emit distinctness proof");
    // Tamper: delete one negated transitivity hypothesis from the `eq_transitive`
    // chain so the rule no longer licenses `(= #b1 #b0)`. Carcara must reject.
    tamper_first_eq_transitive(&mut proof);
    let smt2 = color_smt2(
        "(assert (= (!dtcon_1_Red a) (!dtcon_1_Green b)))
(assert (= #b1 (!dttest_1_Red (!dtcon_1_Red a))))
(assert (= (!dttest_1_Red (!dtcon_1_Green b)) #b0))
",
    );
    carcara_check(&bin, "distinct_tamper", &smt2, &proof, false);
}

/// Corrupts the first `eq_transitive` step by deleting one of its negated
/// transitivity hypotheses, breaking the rule's premise chain.
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

// =====================================================================
// (4) Same-constructor equality `Red(a) = Red(b)` is NOT distinctness — the
//     emitter must DECLINE (returns None), so we never claim a refutation that
//     would actually require injectivity (out of scope).
// =====================================================================
#[test]
fn same_constructor_equality_is_declined() {
    let mut arena = TermArena::new();
    let (red, _green) = color_datatype(&mut arena);
    let a = bvw(&mut arena, "a", 2);
    let b = bvw(&mut arena, "b", 2);
    let red_a = arena.construct(red, &[a]).unwrap();
    let red_b = arena.construct(red, &[b]).unwrap();
    let eq = arena.eq(red_a, red_b).unwrap();
    assert!(
        prove_qf_dt_distinct_alethe_carcara(&arena, &[eq]).is_none(),
        "same-constructor equality must be declined (injectivity is out of scope)"
    );
}
