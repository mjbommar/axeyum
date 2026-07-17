//! Cross-checks for the **constructor injectivity** datatype certificate emitted
//! by [`prove_qf_dt_injective_alethe_carcara`] (gap-analysis Gap 14, narrowing the
//! `TrustId::DatatypeElim` hole by COMPOSING the certified `select`-over-`construct`
//! fold with congruence).
//!
//! Given an asserted same-constructor equality `(= (C x…) (C y…))` plus a
//! conflicting field disequality `(not (= x_i y_i))`, the emitter refutes it by:
//!
//! 1. taking `(= (C x…) (C y…))` as the trusted premise `h`;
//! 2. `cong`-lifting `h` under the selector head `sel_i` to
//!    `(= (sel_i (C x…)) (sel_i (C y…)))`;
//! 3. the two **trusted `select` folds** `(= x_i (sel_i (C x…)))` and
//!    `(= (sel_i (C y…)) y_i)`;
//! 4. a single `eq_transitive` chaining `x_i = sel_i(C x…) = sel_i(C y…) = y_i` to
//!    `(= x_i y_i)`, resolved against the three equalities;
//! 5. `resolution` against the trusted disequality `(not (= x_i y_i))` closing to
//!    the empty clause `(cl)`.
//!
//! Carcara (no datatype rule) treats the reserved `!dtsel_n_i_C` / `!dtcon_n_C`
//! heads as uninterpreted functions and takes the constructor equality, the field
//! disequality, and the two `select` folds as premises; it then checks every
//! *structural* step (`cong`, `eq_transitive`, `resolution`). **Honest residual:**
//! those four stay trusted premises; the INJECTIVITY reasoning (a same-constructor
//! equality forces each field pair `(= x_i y_i)`, so a conflicting `x_i != y_i` is
//! ⊥) is Carcara-checked. Constructor **acyclicity** (needs induction) and the
//! distinct-constructor case stay trusted/deferred and are out of scope.
//!
//! Carcara lives in the gitignored `references/` tree (absent in CI), so each
//! real-checker test **skips** (prints a note, passes) when the binary is absent.
//!
//! **Lean reconstruction is deferred** for the injectivity collapse (it composes
//! the deferred `select`-fold reconstruction tail through `cong`); the Carcara
//! route below fully certifies the COLLAPSE reasoning.
#![cfg(feature = "full")]

use std::path::{Path, PathBuf};
use std::process::Command;

use axeyum_cnf::{AletheCommand, write_alethe};
use axeyum_ir::{ConstructorId, Sort, TermArena, TermId};
use axeyum_solver::prove_qf_dt_injective_alethe_carcara;

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
    let dir = std::env::temp_dir().join(format!("axeyum_dtinjective_{tag}"));
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

/// Builds a binary-constructor `Pair` datatype
/// `Pair(fst : BitVec 2, snd : BitVec 2)` — exercises a multi-field constructor.
fn pair_datatype(arena: &mut TermArena) -> ConstructorId {
    let pair = arena.declare_datatype("Pair");
    arena.add_constructor(
        pair,
        "Pair",
        &[
            ("fst".into(), Sort::BitVec(2)),
            ("snd".into(), Sort::BitVec(2)),
        ],
    )
}

/// Builds a unary-constructor `Cell` datatype `Cell(val : BitVec 3)` on a distinct
/// sort, exercising a single-field constructor / different width.
fn cell_datatype(arena: &mut TermArena) -> ConstructorId {
    let cell = arena.declare_datatype("Cell");
    arena.add_constructor(cell, "Cell", &[("val".into(), Sort::BitVec(3))])
}

/// The `.smt2` for the `Pair` injectivity problem: declares the reserved heads
/// (`!dtcon_2_Pair`, the two `!dtsel_2_i_Pair` selectors) as plain uninterpreted
/// functions over an uninterpreted `Pair` sort, then asserts `residual_asserts`
/// (the textual premises the proof's `assume`s reference).
fn pair_smt2(residual_asserts: &str) -> String {
    format!(
        "\
(set-logic QF_UFBV)
(declare-sort Pair 0)
(declare-const a (_ BitVec 2))
(declare-const b (_ BitVec 2))
(declare-const c (_ BitVec 2))
(declare-const d (_ BitVec 2))
(declare-fun !dtcon_2_Pair ((_ BitVec 2) (_ BitVec 2)) Pair)
(declare-fun !dtsel_2_0_Pair (Pair) (_ BitVec 2))
(declare-fun !dtsel_2_1_Pair (Pair) (_ BitVec 2))
{residual_asserts}(check-sat)
"
    )
}

// =====================================================================
// (1) Same constructor, field-0 mismatch: `Pair(a,b) = Pair(c,d)` ∧ `a != c`
//     is UNSAT (refuted via cong on sel_0 + the two select folds).
// =====================================================================
#[test]
fn injective_field_mismatch_contradiction_is_accepted_by_carcara() {
    let Some(bin) = carcara_bin() else {
        eprintln!("[skip] carcara binary not found; build references/carcara to enable");
        return;
    };
    let mut arena = TermArena::new();
    let pair = pair_datatype(&mut arena);
    let a = bvw(&mut arena, "a", 2);
    let b = bvw(&mut arena, "b", 2);
    let c = bvw(&mut arena, "c", 2);
    let d = bvw(&mut arena, "d", 2);
    let lhs = arena.construct(pair, &[a, b]).unwrap();
    let rhs = arena.construct(pair, &[c, d]).unwrap();
    let eq = arena.eq(lhs, rhs).unwrap();
    let a_eq_c = arena.eq(a, c).unwrap();
    let a_ne_c = arena.not(a_eq_c).unwrap();
    let proof = prove_qf_dt_injective_alethe_carcara(&arena, &[eq, a_ne_c])
        .expect("emit injectivity (field-0) proof");
    // Premises: the constructor equality `h`, the field disequality, and the two
    // trusted select folds (`a = sel_0(Pair a b)`, `sel_0(Pair c d) = c`).
    let smt2 = pair_smt2(
        "(assert (= (!dtcon_2_Pair a b) (!dtcon_2_Pair c d)))
(assert (not (= a c)))
(assert (= a (!dtsel_2_0_Pair (!dtcon_2_Pair a b))))
(assert (= (!dtsel_2_0_Pair (!dtcon_2_Pair c d)) c))
",
    );
    let report = carcara_check(&bin, "injective_pair0", &smt2, &proof, true);
    assert!(report.contains("valid"), "expected valid, got:\n{report}");
}

// =====================================================================
// (2) Same constructor, field-1 mismatch on the SAME Pair sort: `Pair(a,b) =
//     Pair(c,d)` ∧ `b != d` is UNSAT (refuted via cong on sel_1). Exercises a
//     non-zero field index / second selector.
// =====================================================================
#[test]
fn injective_second_field_mismatch_is_accepted_by_carcara() {
    let Some(bin) = carcara_bin() else {
        eprintln!("[skip] carcara binary not found; build references/carcara to enable");
        return;
    };
    let mut arena = TermArena::new();
    let pair = pair_datatype(&mut arena);
    let a = bvw(&mut arena, "a", 2);
    let b = bvw(&mut arena, "b", 2);
    let c = bvw(&mut arena, "c", 2);
    let d = bvw(&mut arena, "d", 2);
    let lhs = arena.construct(pair, &[a, b]).unwrap();
    let rhs = arena.construct(pair, &[c, d]).unwrap();
    let eq = arena.eq(lhs, rhs).unwrap();
    let b_eq_d = arena.eq(b, d).unwrap();
    let b_ne_d = arena.not(b_eq_d).unwrap();
    let proof = prove_qf_dt_injective_alethe_carcara(&arena, &[eq, b_ne_d])
        .expect("emit injectivity (field-1) proof");
    let smt2 = pair_smt2(
        "(assert (= (!dtcon_2_Pair a b) (!dtcon_2_Pair c d)))
(assert (not (= b d)))
(assert (= b (!dtsel_2_1_Pair (!dtcon_2_Pair a b))))
(assert (= (!dtsel_2_1_Pair (!dtcon_2_Pair c d)) d))
",
    );
    let report = carcara_check(&bin, "injective_pair1", &smt2, &proof, true);
    assert!(report.contains("valid"), "expected valid, got:\n{report}");
}

/// The `.smt2` for the unary `Cell` injectivity problem (single `BitVec 3` field),
/// exercising a different sort/width and a unary constructor.
fn cell_smt2(residual_asserts: &str) -> String {
    format!(
        "\
(set-logic QF_UFBV)
(declare-sort Cell 0)
(declare-const p (_ BitVec 3))
(declare-const q (_ BitVec 3))
(declare-fun !dtcon_1_Cell ((_ BitVec 3)) Cell)
(declare-fun !dtsel_1_0_Cell (Cell) (_ BitVec 3))
{residual_asserts}(check-sat)
"
    )
}

// =====================================================================
// (3) A unary constructor on a different sort/width: `Cell(p) = Cell(q)` ∧
//     `p != q` is UNSAT (cong on sel_0 of the single field).
// =====================================================================
#[test]
fn injective_unary_constructor_is_accepted_by_carcara() {
    let Some(bin) = carcara_bin() else {
        eprintln!("[skip] carcara binary not found; build references/carcara to enable");
        return;
    };
    let mut arena = TermArena::new();
    let cell = cell_datatype(&mut arena);
    let p = bvw(&mut arena, "p", 3);
    let q = bvw(&mut arena, "q", 3);
    let lhs = arena.construct(cell, &[p]).unwrap();
    let rhs = arena.construct(cell, &[q]).unwrap();
    let eq = arena.eq(lhs, rhs).unwrap();
    let p_eq_q = arena.eq(p, q).unwrap();
    let p_ne_q = arena.not(p_eq_q).unwrap();
    let proof = prove_qf_dt_injective_alethe_carcara(&arena, &[eq, p_ne_q])
        .expect("emit injectivity (unary Cell) proof");
    let smt2 = cell_smt2(
        "(assert (= (!dtcon_1_Cell p) (!dtcon_1_Cell q)))
(assert (not (= p q)))
(assert (= p (!dtsel_1_0_Cell (!dtcon_1_Cell p))))
(assert (= (!dtsel_1_0_Cell (!dtcon_1_Cell q)) q))
",
    );
    let report = carcara_check(&bin, "injective_cell", &smt2, &proof, true);
    assert!(report.contains("valid"), "expected valid, got:\n{report}");
}

// =====================================================================
// (4) TAMPER: corrupt the `eq_transitive` chain so it no longer derives
//     `(= a c)`. Carcara must REJECT.
// =====================================================================
#[test]
fn injective_tampered_chain_is_rejected_by_carcara() {
    let Some(bin) = carcara_bin() else {
        eprintln!("[skip] carcara binary not found; build references/carcara to enable");
        return;
    };
    let mut arena = TermArena::new();
    let pair = pair_datatype(&mut arena);
    let a = bvw(&mut arena, "a", 2);
    let b = bvw(&mut arena, "b", 2);
    let c = bvw(&mut arena, "c", 2);
    let d = bvw(&mut arena, "d", 2);
    let lhs = arena.construct(pair, &[a, b]).unwrap();
    let rhs = arena.construct(pair, &[c, d]).unwrap();
    let eq = arena.eq(lhs, rhs).unwrap();
    let a_eq_c = arena.eq(a, c).unwrap();
    let a_ne_c = arena.not(a_eq_c).unwrap();
    let mut proof = prove_qf_dt_injective_alethe_carcara(&arena, &[eq, a_ne_c])
        .expect("emit injectivity proof");
    // Tamper: delete one negated transitivity hypothesis from the `eq_transitive`
    // chain so the rule no longer licenses `(= a c)`. Carcara must reject.
    tamper_first_eq_transitive(&mut proof);
    let smt2 = pair_smt2(
        "(assert (= (!dtcon_2_Pair a b) (!dtcon_2_Pair c d)))
(assert (not (= a c)))
(assert (= a (!dtsel_2_0_Pair (!dtcon_2_Pair a b))))
(assert (= (!dtsel_2_0_Pair (!dtcon_2_Pair c d)) c))
",
    );
    carcara_check(&bin, "injective_tamper", &smt2, &proof, false);
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
// (5) DISTINCT-constructor equality `Red(a) = Green(b)` is NOT injectivity —
//     the emitter must DECLINE (returns None). That case is distinctness's job;
//     injectivity needs the SAME constructor.
// =====================================================================
#[test]
fn distinct_constructor_equality_is_declined() {
    let mut arena = TermArena::new();
    let color = arena.declare_datatype("Color");
    let red = arena.add_constructor(color, "Red", &[("v".into(), Sort::BitVec(2))]);
    let green = arena.add_constructor(color, "Green", &[("w".into(), Sort::BitVec(2))]);
    let a = bvw(&mut arena, "a", 2);
    let b = bvw(&mut arena, "b", 2);
    let red_a = arena.construct(red, &[a]).unwrap();
    let green_b = arena.construct(green, &[b]).unwrap();
    let eq = arena.eq(red_a, green_b).unwrap();
    let a_eq_b = arena.eq(a, b).unwrap();
    let a_ne_b = arena.not(a_eq_b).unwrap();
    assert!(
        prove_qf_dt_injective_alethe_carcara(&arena, &[eq, a_ne_b]).is_none(),
        "distinct-constructor equality must be declined (distinctness is the right tool)"
    );
}

// =====================================================================
// (6) A same-constructor equality with NO conflicting field disequality is
//     declined (there is nothing to refute — injectivity yields equalities, not ⊥,
//     without a clashing diseq).
// =====================================================================
#[test]
fn same_constructor_without_field_conflict_is_declined() {
    let mut arena = TermArena::new();
    let pair = pair_datatype(&mut arena);
    let a = bvw(&mut arena, "a", 2);
    let b = bvw(&mut arena, "b", 2);
    let c = bvw(&mut arena, "c", 2);
    let d = bvw(&mut arena, "d", 2);
    let lhs = arena.construct(pair, &[a, b]).unwrap();
    let rhs = arena.construct(pair, &[c, d]).unwrap();
    let eq = arena.eq(lhs, rhs).unwrap();
    assert!(
        prove_qf_dt_injective_alethe_carcara(&arena, &[eq]).is_none(),
        "no field disequality means nothing to refute — must decline"
    );
}
