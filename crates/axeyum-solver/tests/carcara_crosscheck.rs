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

use axeyum_cnf::{AletheClause, AletheCommand, AletheLit, AletheTerm, write_alethe};
use axeyum_ir::{Rational, Sort, TermArena, TermId};
use axeyum_smtlib::write_script;
use axeyum_solver::{bitblast_step, prove_lra_unsat_alethe, prove_qf_uf_unsat_alethe};

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

/// Writes the given `.smt2` text + `proof` to a temp dir and runs `carcara
/// check`. Returns Carcara's combined stdout/stderr; panics unless it reports a
/// hole-free `valid`.
fn carcara_accepts_smt2(
    bin: &Path,
    tag: &str,
    smt2_text: &str,
    proof: &[axeyum_cnf::AletheCommand],
) -> String {
    let dir = std::env::temp_dir().join(format!("axeyum_carcara_{tag}"));
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
    assert!(
        out.status.success() && combined.contains("valid") && !combined.contains("holey"),
        "carcara rejected the {tag} proof:\n{combined}"
    );
    combined
}

/// Writes `smt2_text` + `proof` to a temp dir and runs `carcara check`,
/// returning the combined stdout/stderr **without** asserting validity. Used to
/// inspect Carcara's diagnostics — e.g. to confirm a step *parses* even when the
/// proof as a whole is incomplete (does not conclude the empty clause).
fn carcara_output(
    bin: &Path,
    tag: &str,
    smt2_text: &str,
    proof: &[axeyum_cnf::AletheCommand],
) -> String {
    let dir = std::env::temp_dir().join(format!("axeyum_carcara_{tag}"));
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
    format!(
        "{}{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    )
}

/// Emits `proof` + the matching IR-derived `.smt2` to a temp dir and runs
/// `carcara check`.
fn carcara_accepts(
    bin: &Path,
    tag: &str,
    arena: &TermArena,
    assertions: &[TermId],
    proof: &[axeyum_cnf::AletheCommand],
) -> String {
    carcara_accepts_smt2(bin, tag, &write_script(arena, assertions), proof)
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

/// A real numeral term `n`.
fn real_int(arena: &mut TermArena, n: i128) -> TermId {
    arena.real_const(Rational::integer(n))
}

#[test]
fn lra_unit_coefficients_proof_is_accepted_by_carcara() {
    let Some(bin) = carcara_bin() else {
        eprintln!("[skip] carcara binary not found; build references/carcara to enable");
        return;
    };
    // x <= 0 ∧ x >= 1 — unsat with unit Farkas coefficients (1, 1).
    let mut arena = TermArena::new();
    let x = arena.real_var("x").unwrap();
    let zero = real_int(&mut arena, 0);
    let one = real_int(&mut arena, 1);
    let a1 = arena.real_le(x, zero).unwrap();
    let a2 = arena.real_ge(x, one).unwrap();
    let assertions = vec![a1, a2];

    let proof = prove_lra_unsat_alethe(&arena, &assertions).expect("emit LRA proof");
    let report = carcara_accepts(&bin, "lra_unit", &arena, &assertions, &proof);
    assert!(report.contains("valid"), "expected 'valid', got:\n{report}");
}

#[test]
fn lra_nonunit_coefficients_proof_is_accepted_by_carcara() {
    let Some(bin) = carcara_bin() else {
        eprintln!("[skip] carcara binary not found; build references/carcara to enable");
        return;
    };
    // 2x <= 1 ∧ x >= 1 — unsat with non-unit Farkas coefficients (1, 2):
    // 1·(2x ≤ 1) + 2·(x ≥ 1) ⟹ 1 ≥ 2, a contradiction.
    let mut arena = TermArena::new();
    let x = arena.real_var("x").unwrap();
    let two = real_int(&mut arena, 2);
    let one = real_int(&mut arena, 1);
    let two_x = arena.real_mul(two, x).unwrap();
    let a1 = arena.real_le(two_x, one).unwrap();
    let a2 = arena.real_ge(x, one).unwrap();
    let assertions = vec![a1, a2];

    let proof = prove_lra_unsat_alethe(&arena, &assertions).expect("emit LRA proof");
    let report = carcara_accepts(&bin, "lra_nonunit", &arena, &assertions, &proof);
    assert!(report.contains("valid"), "expected 'valid', got:\n{report}");
}

#[test]
fn lra_multivariable_proof_is_accepted_by_carcara() {
    let Some(bin) = carcara_bin() else {
        eprintln!("[skip] carcara binary not found; build references/carcara to enable");
        return;
    };
    // x + y <= 0 ∧ x >= 1 ∧ y >= 0 — unsat: (x + y) ≥ 1 > 0 contradicts the first.
    let mut arena = TermArena::new();
    let x = arena.real_var("x").unwrap();
    let y = arena.real_var("y").unwrap();
    let zero = real_int(&mut arena, 0);
    let one = real_int(&mut arena, 1);
    let x_plus_y = arena.real_add(x, y).unwrap();
    let a1 = arena.real_le(x_plus_y, zero).unwrap();
    let a2 = arena.real_ge(x, one).unwrap();
    let a3 = arena.real_ge(y, zero).unwrap();
    let assertions = vec![a1, a2, a3];

    let proof = prove_lra_unsat_alethe(&arena, &assertions).expect("emit LRA proof");
    let report = carcara_accepts(&bin, "lra_multivar", &arena, &assertions, &proof);
    assert!(report.contains("valid"), "expected 'valid', got:\n{report}");
}

#[test]
fn lra_equalities_proof_is_accepted_by_carcara() {
    let Some(bin) = carcara_bin() else {
        eprintln!("[skip] carcara binary not found; build references/carcara to enable");
        return;
    };
    // x = 1 ∧ x = 2 — pure equalities, unsat. Each `a = b` splits into two bounds,
    // so the emitted la_generic args are signed per-assertion coefficients (e.g.
    // `(1, (- 1))`): exactly the new case this proof emitter must cover.
    let mut arena = TermArena::new();
    let x = arena.real_var("x").unwrap();
    let one = real_int(&mut arena, 1);
    let two = real_int(&mut arena, 2);
    let a1 = arena.eq(x, one).unwrap();
    let a2 = arena.eq(x, two).unwrap();
    let assertions = vec![a1, a2];

    let proof = prove_lra_unsat_alethe(&arena, &assertions).expect("emit LRA proof");
    let report = carcara_accepts(&bin, "lra_equalities", &arena, &assertions, &proof);
    assert!(report.contains("valid"), "expected 'valid', got:\n{report}");
}

#[test]
fn lra_mixed_equality_inequality_proof_is_accepted_by_carcara() {
    let Some(bin) = carcara_bin() else {
        eprintln!("[skip] carcara binary not found; build references/carcara to enable");
        return;
    };
    // x = 1 ∧ x + y <= 0 ∧ y >= 1 — unsat: x = 1, y ≥ 1 ⇒ x + y ≥ 2 > 0. Mixes an
    // equality (two-atom split) with inequalities (single-atom) in one step.
    let mut arena = TermArena::new();
    let x = arena.real_var("x").unwrap();
    let y = arena.real_var("y").unwrap();
    let zero = real_int(&mut arena, 0);
    let one = real_int(&mut arena, 1);
    let x_plus_y = arena.real_add(x, y).unwrap();
    let a1 = arena.eq(x, one).unwrap();
    let a2 = arena.real_le(x_plus_y, zero).unwrap();
    let a3 = arena.real_ge(y, one).unwrap();
    let assertions = vec![a1, a2, a3];

    let proof = prove_lra_unsat_alethe(&arena, &assertions).expect("emit LRA proof");
    let report = carcara_accepts(&bin, "lra_mixed_eq", &arena, &assertions, &proof);
    assert!(report.contains("valid"), "expected 'valid', got:\n{report}");
}

#[test]
fn lra_coefficient_bearing_equality_proof_is_accepted_by_carcara() {
    let Some(bin) = carcara_bin() else {
        eprintln!("[skip] carcara binary not found; build references/carcara to enable");
        return;
    };
    // 2x = 1 ∧ x = 1 — unsat: the first forces x = 0.5, the second x = 1. The
    // refutation needs a non-unit coefficient on an equality split.
    let mut arena = TermArena::new();
    let x = arena.real_var("x").unwrap();
    let two = real_int(&mut arena, 2);
    let one = real_int(&mut arena, 1);
    let two_x = arena.real_mul(two, x).unwrap();
    let a1 = arena.eq(two_x, one).unwrap();
    let a2 = arena.eq(x, one).unwrap();
    let assertions = vec![a1, a2];

    let proof = prove_lra_unsat_alethe(&arena, &assertions).expect("emit LRA proof");
    let report = carcara_accepts(&bin, "lra_coeff_eq", &arena, &assertions, &proof);
    assert!(report.contains("valid"), "expected 'valid', got:\n{report}");
}

/// Renders a CNF formula as a propositional SMT-LIB problem whose assertions
/// match `lrat_to_alethe`'s `v{index}` atom naming and clause-literal order, so
/// Carcara can match the proof's `assume`d input clauses to the assertions.
fn cnf_to_smt2(formula: &axeyum_cnf::CnfFormula) -> String {
    use std::fmt::Write as _;
    let mut max_var = 0usize;
    for clause in formula.clauses() {
        for lit in clause.lits() {
            max_var = max_var.max(lit.var().index());
        }
    }
    let mut out = String::from("(set-logic QF_UF)\n");
    for v in 0..=max_var {
        let _ = writeln!(out, "(declare-const v{v} Bool)");
    }
    for clause in formula.clauses() {
        let lits: Vec<String> = clause
            .lits()
            .iter()
            .map(|lit| {
                let name = format!("v{}", lit.var().index());
                if lit.is_negated() {
                    format!("(not {name})")
                } else {
                    name
                }
            })
            .collect();
        let body = if lits.len() == 1 {
            lits[0].clone()
        } else {
            format!("(or {})", lits.join(" "))
        };
        let _ = writeln!(out, "(assert {body})");
    }
    out.push_str("(check-sat)\n");
    out
}

#[test]
fn resolution_refutation_proof_is_accepted_by_carcara() {
    use axeyum_cnf::{
        CnfClause, CnfFormula, CnfLit, CnfVar, ProofSolveOutcome, elaborate_drat_to_lrat,
        lrat_to_alethe, solve_with_drat_proof,
    };
    let Some(bin) = carcara_bin() else {
        eprintln!("[skip] carcara binary not found; build references/carcara to enable");
        return;
    };
    // (a∨b) ∧ (a∨¬b) ∧ (¬a∨b) ∧ (¬a∨¬b) — propositionally unsat. The clausal
    // refutation goes CDCL → DRAT → LRAT → Alethe resolution; Carcara checks the
    // resolution chain against the asserted input clauses end to end.
    let v = |i: usize| CnfVar::new(i).expect("var");
    let pos = |i: usize| CnfLit::positive(v(i));
    let neg = |i: usize| CnfLit::positive(v(i)).negated();
    let mut formula = CnfFormula::new(2);
    for clause in [
        vec![pos(0), pos(1)],
        vec![pos(0), neg(1)],
        vec![neg(0), pos(1)],
        vec![neg(0), neg(1)],
    ] {
        formula
            .add_clause(CnfClause::new(clause))
            .expect("add clause");
    }

    let ProofSolveOutcome::Unsat(drat) = solve_with_drat_proof(&formula) else {
        panic!("formula is unsatisfiable");
    };
    let lrat = elaborate_drat_to_lrat(&formula, &drat).expect("DRAT elaborates to LRAT");
    let proof = lrat_to_alethe(&formula, &lrat);
    let smt2 = cnf_to_smt2(&formula);
    let report = carcara_accepts_smt2(&bin, "resolution", &smt2, &proof);
    assert!(report.contains("valid"), "expected 'valid', got:\n{report}");
}

/// Builds the single `bitblast_*` step for `term` via [`bitblast_step`], writes
/// it alongside a matching `.smt2` that declares the operand symbols and asserts
/// a well-typed equality mentioning them, runs Carcara, and asserts the **step's
/// rule check passed**: no parser error, no `checking failed`, and the proof
/// reaches the only remaining (expected) failure — a lone step does not conclude
/// the empty clause. Returns Carcara's combined output for the caller to quote.
fn carcara_rule_accepts_bitblast(
    bin: &Path,
    tag: &str,
    arena: &TermArena,
    term: TermId,
    decls: &str,
    assertion: &str,
) -> String {
    use axeyum_solver::bitblast_step;
    let step = bitblast_step(arena, term, "s").expect("term is in the bitwise fragment");
    let smt2 = format!("(set-logic QF_BV)\n{decls}(assert {assertion})\n(check-sat)\n");
    let report = carcara_output(bin, tag, &smt2, std::slice::from_ref(&step));

    assert!(
        !report.contains("parser error"),
        "carcara could not parse the {tag} bitblast step:\n{report}"
    );
    assert!(
        !report.contains("checking failed"),
        "carcara rejected the {tag} bitblast step's rule:\n{report}"
    );
    assert!(
        report.contains("does not conclude empty clause"),
        "expected only the empty-clause-conclusion failure for {tag}, got:\n{report}"
    );
    report
}

fn bv_var(arena: &mut TermArena, name: &str, width: u32) -> TermId {
    let s = arena.declare(name, Sort::BitVec(width)).expect("declare");
    arena.var(s)
}

#[test]
fn bitblast_var_step_is_rule_accepted_by_carcara() {
    let Some(bin) = carcara_bin() else {
        eprintln!("[skip] carcara binary not found; build references/carcara to enable");
        return;
    };
    let mut arena = TermArena::new();
    let x = bv_var(&mut arena, "x", 3);
    carcara_rule_accepts_bitblast(
        &bin,
        "bitblast_var_step",
        &arena,
        x,
        "(declare-const x (_ BitVec 3))\n",
        "(= x x)",
    );
}

#[test]
fn bitblast_const_step_is_rule_accepted_by_carcara() {
    let Some(bin) = carcara_bin() else {
        eprintln!("[skip] carcara binary not found; build references/carcara to enable");
        return;
    };
    // width-4 value 0b1010 = 10: exercises both true and false bits.
    let mut arena = TermArena::new();
    let c = arena.bv_const(4, 10).expect("bv const");
    carcara_rule_accepts_bitblast(
        &bin,
        "bitblast_const_step",
        &arena,
        c,
        "(declare-const x (_ BitVec 4))\n",
        "(= #b1010 x)",
    );
}

#[test]
fn bitblast_not_step_is_rule_accepted_by_carcara() {
    let Some(bin) = carcara_bin() else {
        eprintln!("[skip] carcara binary not found; build references/carcara to enable");
        return;
    };
    let mut arena = TermArena::new();
    let a = bv_var(&mut arena, "a", 3);
    let t = arena.bv_not(a).expect("bvnot");
    carcara_rule_accepts_bitblast(
        &bin,
        "bitblast_not_step",
        &arena,
        t,
        "(declare-const a (_ BitVec 3))\n",
        "(= (bvnot a) (bvnot a))",
    );
}

#[test]
fn bitblast_and_step_is_rule_accepted_by_carcara() {
    let Some(bin) = carcara_bin() else {
        eprintln!("[skip] carcara binary not found; build references/carcara to enable");
        return;
    };
    // width 4 (>= 2) binary bvand.
    let mut arena = TermArena::new();
    let a = bv_var(&mut arena, "a", 4);
    let b = bv_var(&mut arena, "b", 4);
    let t = arena.bv_and(a, b).expect("bvand");
    carcara_rule_accepts_bitblast(
        &bin,
        "bitblast_and_step",
        &arena,
        t,
        "(declare-const a (_ BitVec 4))\n(declare-const b (_ BitVec 4))\n",
        "(= (bvand a b) (bvand a b))",
    );
}

#[test]
fn bitblast_or_step_is_rule_accepted_by_carcara() {
    let Some(bin) = carcara_bin() else {
        eprintln!("[skip] carcara binary not found; build references/carcara to enable");
        return;
    };
    let mut arena = TermArena::new();
    let a = bv_var(&mut arena, "a", 4);
    let b = bv_var(&mut arena, "b", 4);
    let t = arena.bv_or(a, b).expect("bvor");
    carcara_rule_accepts_bitblast(
        &bin,
        "bitblast_or_step",
        &arena,
        t,
        "(declare-const a (_ BitVec 4))\n(declare-const b (_ BitVec 4))\n",
        "(= (bvor a b) (bvor a b))",
    );
}

#[test]
fn bitblast_xor_step_is_rule_accepted_by_carcara() {
    let Some(bin) = carcara_bin() else {
        eprintln!("[skip] carcara binary not found; build references/carcara to enable");
        return;
    };
    // A nested xor `(bvxor (bvxor a b) c)` exercises the fold path: arg0 is itself
    // a bvxor, so its bit projects as ((_ @bit_of i) (bvxor a b)) — the n-ary nest.
    let mut arena = TermArena::new();
    let a = bv_var(&mut arena, "a", 2);
    let b = bv_var(&mut arena, "b", 2);
    let c = bv_var(&mut arena, "c", 2);
    let ab = arena.bv_xor(a, b).expect("bvxor");
    let abc = arena.bv_xor(ab, c).expect("bvxor");
    carcara_rule_accepts_bitblast(
        &bin,
        "bitblast_xor_step",
        &arena,
        abc,
        "(declare-const a (_ BitVec 2))\n(declare-const b (_ BitVec 2))\n(declare-const c (_ BitVec 2))\n",
        "(= (bvxor (bvxor a b) c) (bvxor (bvxor a b) c))",
    );
}

#[test]
fn bitblast_xnor_step_is_rule_accepted_by_carcara() {
    let Some(bin) = carcara_bin() else {
        eprintln!("[skip] carcara binary not found; build references/carcara to enable");
        return;
    };
    let mut arena = TermArena::new();
    let a = bv_var(&mut arena, "a", 4);
    let b = bv_var(&mut arena, "b", 4);
    let t = arena.bv_xnor(a, b).expect("bvxnor");
    carcara_rule_accepts_bitblast(
        &bin,
        "bitblast_xnor_step",
        &arena,
        t,
        "(declare-const a (_ BitVec 4))\n(declare-const b (_ BitVec 4))\n",
        "(= (bvxnor a b) (bvxnor a b))",
    );
}

#[test]
fn bitblast_add_step_is_rule_accepted_by_carcara() {
    let Some(bin) = carcara_bin() else {
        eprintln!("[skip] carcara binary not found; build references/carcara to enable");
        return;
    };
    // width 4 (>= 2) binary bvadd.
    let mut arena = TermArena::new();
    let a = bv_var(&mut arena, "a", 4);
    let b = bv_var(&mut arena, "b", 4);
    let t = arena.bv_add(a, b).expect("bvadd");
    carcara_rule_accepts_bitblast(
        &bin,
        "bitblast_add_step",
        &arena,
        t,
        "(declare-const a (_ BitVec 4))\n(declare-const b (_ BitVec 4))\n",
        "(= (bvadd a b) (bvadd a b))",
    );
}

#[test]
fn bitblast_add_nary_step_is_rule_accepted_by_carcara() {
    let Some(bin) = carcara_bin() else {
        eprintln!("[skip] carcara binary not found; build references/carcara to enable");
        return;
    };
    // A nested add `(bvadd (bvadd a b) c)` exercises the left-fold: arg0 is itself
    // a bvadd, so its bits come from the accumulator @bbterm of the first add.
    let mut arena = TermArena::new();
    let a = bv_var(&mut arena, "a", 3);
    let b = bv_var(&mut arena, "b", 3);
    let c = bv_var(&mut arena, "c", 3);
    let ab = arena.bv_add(a, b).expect("bvadd");
    let abc = arena.bv_add(ab, c).expect("bvadd");
    carcara_rule_accepts_bitblast(
        &bin,
        "bitblast_add_nary_step",
        &arena,
        abc,
        "(declare-const a (_ BitVec 3))\n(declare-const b (_ BitVec 3))\n(declare-const c (_ BitVec 3))\n",
        "(= (bvadd (bvadd a b) c) (bvadd (bvadd a b) c))",
    );
}

#[test]
fn bitblast_neg_step_is_rule_accepted_by_carcara() {
    let Some(bin) = carcara_bin() else {
        eprintln!("[skip] carcara binary not found; build references/carcara to enable");
        return;
    };
    let mut arena = TermArena::new();
    let a = bv_var(&mut arena, "a", 4);
    let t = arena.bv_neg(a).expect("bvneg");
    carcara_rule_accepts_bitblast(
        &bin,
        "bitblast_neg_step",
        &arena,
        t,
        "(declare-const a (_ BitVec 4))\n",
        "(= (bvneg a) (bvneg a))",
    );
}

#[test]
fn bitblast_ult_step_is_rule_accepted_by_carcara() {
    let Some(bin) = carcara_bin() else {
        eprintln!("[skip] carcara binary not found; build references/carcara to enable");
        return;
    };
    // Predicate op: assert the predicate itself as the well-typed Bool formula.
    let mut arena = TermArena::new();
    let a = bv_var(&mut arena, "a", 4);
    let b = bv_var(&mut arena, "b", 4);
    let t = arena.bv_ult(a, b).expect("bvult");
    carcara_rule_accepts_bitblast(
        &bin,
        "bitblast_ult_step",
        &arena,
        t,
        "(declare-const a (_ BitVec 4))\n(declare-const b (_ BitVec 4))\n",
        "(bvult a b)",
    );
}

#[test]
fn bitblast_slt_step_is_rule_accepted_by_carcara() {
    let Some(bin) = carcara_bin() else {
        eprintln!("[skip] carcara binary not found; build references/carcara to enable");
        return;
    };
    // Multi-bit: the general ladder with a separate sign step.
    let mut arena = TermArena::new();
    let a = bv_var(&mut arena, "a", 4);
    let b = bv_var(&mut arena, "b", 4);
    let t = arena.bv_slt(a, b).expect("bvslt");
    carcara_rule_accepts_bitblast(
        &bin,
        "bitblast_slt_step",
        &arena,
        t,
        "(declare-const a (_ BitVec 4))\n(declare-const b (_ BitVec 4))\n",
        "(bvslt a b)",
    );
}

#[test]
fn bitblast_slt_width1_step_is_rule_accepted_by_carcara() {
    let Some(bin) = carcara_bin() else {
        eprintln!("[skip] carcara binary not found; build references/carcara to enable");
        return;
    };
    // Carcara special-cases size == 1: result is (and x0 (not y0)).
    let mut arena = TermArena::new();
    let a = bv_var(&mut arena, "a", 1);
    let b = bv_var(&mut arena, "b", 1);
    let t = arena.bv_slt(a, b).expect("bvslt");
    carcara_rule_accepts_bitblast(
        &bin,
        "bitblast_slt_width1_step",
        &arena,
        t,
        "(declare-const a (_ BitVec 1))\n(declare-const b (_ BitVec 1))\n",
        "(bvslt a b)",
    );
}

#[test]
fn bitblast_equal_step_is_rule_accepted_by_carcara() {
    let Some(bin) = carcara_bin() else {
        eprintln!("[skip] carcara binary not found; build references/carcara to enable");
        return;
    };
    let mut arena = TermArena::new();
    let a = bv_var(&mut arena, "a", 4);
    let b = bv_var(&mut arena, "b", 4);
    let t = arena.eq(a, b).expect("eq");
    carcara_rule_accepts_bitblast(
        &bin,
        "bitblast_equal_step",
        &arena,
        t,
        "(declare-const a (_ BitVec 4))\n(declare-const b (_ BitVec 4))\n",
        "(= a b)",
    );
}

#[test]
fn bitblast_comp_step_is_rule_accepted_by_carcara() {
    let Some(bin) = carcara_bin() else {
        eprintln!("[skip] carcara binary not found; build references/carcara to enable");
        return;
    };
    // bvcomp yields a 1-bit BV; assert a well-typed BV equation mentioning it.
    let mut arena = TermArena::new();
    let a = bv_var(&mut arena, "a", 4);
    let b = bv_var(&mut arena, "b", 4);
    let t = arena.bv_comp(a, b).expect("bvcomp");
    carcara_rule_accepts_bitblast(
        &bin,
        "bitblast_comp_step",
        &arena,
        t,
        "(declare-const a (_ BitVec 4))\n(declare-const b (_ BitVec 4))\n",
        "(= (bvcomp a b) (bvcomp a b))",
    );
}

#[test]
fn bitblast_var_indexed_syntax_is_parseable_by_carcara() {
    use axeyum_cnf::{AletheCommand, AletheLit, AletheTerm};
    let Some(bin) = carcara_bin() else {
        eprintln!("[skip] carcara binary not found; build references/carcara to enable");
        return;
    };
    // The confirmed Carcara contract (T3.3.1): a `bitblast_var` step concludes
    // `(= x (@bbterm ((_ @bit_of 0) x) ((_ @bit_of 1) x)))`, where each bit uses the
    // indexed bit-extraction `(_ @bit_of i)`. Built entirely via the IR + write_alethe,
    // this proves the new `AletheTerm::Indexed` renders syntax Carcara *parses* and the
    // `bitblast_var` rule itself checks; only the missing empty-clause conclusion remains.
    let bit_of = |i: i128| AletheTerm::Indexed {
        op: "@bit_of".to_owned(),
        indices: vec![i],
        args: vec![AletheTerm::Const("x".to_owned())],
    };
    let bbterm = AletheTerm::App("@bbterm".to_owned(), vec![bit_of(0), bit_of(1)]);
    let conclusion = AletheLit {
        atom: AletheTerm::App(
            "=".to_owned(),
            vec![AletheTerm::Const("x".to_owned()), bbterm],
        ),
        negated: false,
    };
    let proof = vec![AletheCommand::Step {
        id: "s".to_owned(),
        clause: vec![conclusion],
        rule: "bitblast_var".to_owned(),
        premises: Vec::new(),
        args: Vec::new(),
    }];

    let smt2 = "(set-logic QF_BV)\n\
        (declare-const x (_ BitVec 2))\n\
        (assert (= x x))\n\
        (check-sat)\n";
    let report = carcara_output(&bin, "bitblast_var_indexed", smt2, &proof);

    // The emitted indexed-op syntax parses (no parser error) and the `bitblast_var`
    // rule checks; the only remaining failure is that a lone step is not a refutation.
    assert!(
        !report.contains("parser error"),
        "carcara could not parse the emitted indexed-op syntax:\n{report}"
    );
    assert!(
        report.contains("does not conclude empty clause"),
        "expected only the empty-clause-conclusion failure, got:\n{report}"
    );
}

#[test]
fn bitblast_mult_step_is_rule_accepted_by_carcara() {
    let Some(bin) = carcara_bin() else {
        eprintln!("[skip] carcara binary not found; build references/carcara to enable");
        return;
    };
    // width 4 (>= 2) binary bvmul: the full shift-add multiplier.
    let mut arena = TermArena::new();
    let a = bv_var(&mut arena, "a", 4);
    let b = bv_var(&mut arena, "b", 4);
    let t = arena.bv_mul(a, b).expect("bvmul");
    carcara_rule_accepts_bitblast(
        &bin,
        "bitblast_mult_step",
        &arena,
        t,
        "(declare-const a (_ BitVec 4))\n(declare-const b (_ BitVec 4))\n",
        "(= (bvmul a b) (bvmul a b))",
    );
}

#[test]
fn bitblast_mult_width1_step_is_rule_accepted_by_carcara() {
    let Some(bin) = carcara_bin() else {
        eprintln!("[skip] carcara binary not found; build references/carcara to enable");
        return;
    };
    // width 1: the `for j in 1..n` loop is empty, so the result is (@bbterm (and b0 a0)).
    let mut arena = TermArena::new();
    let a = bv_var(&mut arena, "a", 1);
    let b = bv_var(&mut arena, "b", 1);
    let t = arena.bv_mul(a, b).expect("bvmul");
    carcara_rule_accepts_bitblast(
        &bin,
        "bitblast_mult_width1_step",
        &arena,
        t,
        "(declare-const a (_ BitVec 1))\n(declare-const b (_ BitVec 1))\n",
        "(= (bvmul a b) (bvmul a b))",
    );
}

#[test]
fn bitblast_mult_nary_step_is_rule_accepted_by_carcara() {
    let Some(bin) = carcara_bin() else {
        eprintln!("[skip] carcara binary not found; build references/carcara to enable");
        return;
    };
    // A nested mul `(bvmul (bvmul a b) c)` exercises the left fold: arg0 is itself
    // a bvmul, so its bits come from the accumulator @bbterm of the first multiply.
    let mut arena = TermArena::new();
    let a = bv_var(&mut arena, "a", 3);
    let b = bv_var(&mut arena, "b", 3);
    let c = bv_var(&mut arena, "c", 3);
    let ab = arena.bv_mul(a, b).expect("bvmul");
    let abc = arena.bv_mul(ab, c).expect("bvmul");
    carcara_rule_accepts_bitblast(
        &bin,
        "bitblast_mult_nary_step",
        &arena,
        abc,
        "(declare-const a (_ BitVec 3))\n(declare-const b (_ BitVec 3))\n(declare-const c (_ BitVec 3))\n",
        "(= (bvmul (bvmul a b) c) (bvmul (bvmul a b) c))",
    );
}

#[test]
fn bitblast_extract_step_is_rule_accepted_by_carcara() {
    let Some(bin) = carcara_bin() else {
        eprintln!("[skip] carcara binary not found; build references/carcara to enable");
        return;
    };
    // ((_ extract 2 1) x) over width 4: a sub-range (bits 1..=2).
    let mut arena = TermArena::new();
    let x = bv_var(&mut arena, "x", 4);
    let t = arena.extract(2, 1, x).expect("extract");
    carcara_rule_accepts_bitblast(
        &bin,
        "bitblast_extract_step",
        &arena,
        t,
        "(declare-const x (_ BitVec 4))\n",
        "(= ((_ extract 2 1) x) ((_ extract 2 1) x))",
    );
}

#[test]
fn bitblast_concat_step_is_rule_accepted_by_carcara() {
    let Some(bin) = carcara_bin() else {
        eprintln!("[skip] carcara binary not found; build references/carcara to enable");
        return;
    };
    // (concat a b) with different operand widths: a high (width 2), b low (width 3).
    let mut arena = TermArena::new();
    let a = bv_var(&mut arena, "a", 2);
    let b = bv_var(&mut arena, "b", 3);
    let t = arena.concat(a, b).expect("concat");
    carcara_rule_accepts_bitblast(
        &bin,
        "bitblast_concat_step",
        &arena,
        t,
        "(declare-const a (_ BitVec 2))\n(declare-const b (_ BitVec 3))\n",
        "(= (concat a b) (concat a b))",
    );
}

#[test]
fn bitblast_sign_extend_step_is_rule_accepted_by_carcara() {
    let Some(bin) = carcara_bin() else {
        eprintln!("[skip] carcara binary not found; build references/carcara to enable");
        return;
    };
    // ((_ sign_extend 2) x) over width 3: i >= 1, so the sign bit is repeated.
    let mut arena = TermArena::new();
    let x = bv_var(&mut arena, "x", 3);
    let t = arena.sign_ext(2, x).expect("sign_extend");
    carcara_rule_accepts_bitblast(
        &bin,
        "bitblast_sign_extend_step",
        &arena,
        t,
        "(declare-const x (_ BitVec 3))\n",
        "(= ((_ sign_extend 2) x) ((_ sign_extend 2) x))",
    );
}

#[test]
fn bitblast_sign_extend_zero_step_is_rule_accepted_by_carcara() {
    let Some(bin) = carcara_bin() else {
        eprintln!("[skip] carcara binary not found; build references/carcara to enable");
        return;
    };
    // ((_ sign_extend 0) x): the i == 0 case degenerates to just x's bits.
    let mut arena = TermArena::new();
    let x = bv_var(&mut arena, "x", 3);
    let t = arena.sign_ext(0, x).expect("sign_extend");
    carcara_rule_accepts_bitblast(
        &bin,
        "bitblast_sign_extend_zero_step",
        &arena,
        t,
        "(declare-const x (_ BitVec 3))\n",
        "(= ((_ sign_extend 0) x) ((_ sign_extend 0) x))",
    );
}

// --- Full QF_BV `unsat` proof: bitblast steps + the bridge to a closing `(cl)` ---
//
// The bridge composition (hand-validated against the binary, then locked in here):
//   assume φ → `bitblast_<pred>` gives `(= φ B)` → `equiv1` + `resolution` derive
//   the Boolean form `B` → CNF-introduction (`and` with an `:args` conjunct index,
//   `equiv2`) breaks `B` into clauses → `resolution` closes to `(cl)`.

fn term_const(name: &str) -> AletheTerm {
    AletheTerm::Const(name.to_owned())
}

fn bit0(name: &str) -> AletheTerm {
    AletheTerm::Indexed {
        op: "@bit_of".to_owned(),
        indices: vec![0],
        args: vec![term_const(name)],
    }
}

fn pos(atom: AletheTerm) -> AletheLit {
    AletheLit {
        atom,
        negated: false,
    }
}

fn neg(atom: AletheTerm) -> AletheLit {
    AletheLit {
        atom,
        negated: true,
    }
}

fn step(
    id: &str,
    clause: AletheClause,
    rule: &str,
    premises: &[&str],
    args: Vec<AletheTerm>,
) -> AletheCommand {
    AletheCommand::Step {
        id: id.to_owned(),
        clause,
        rule: rule.to_owned(),
        premises: premises.iter().map(|s| (*s).to_owned()).collect(),
        args,
    }
}

#[test]
fn full_qf_bv_unsat_proof_is_accepted_by_carcara() {
    let Some(bin) = carcara_bin() else {
        eprintln!("[skip] carcara binary not found; build references/carcara to enable");
        return;
    };
    // (= a b) ∧ (bvult a b) over 1-bit a, b — unsat: a = b yet a < b.
    let mut arena = TermArena::new();
    let a = {
        let s = arena.declare("a", Sort::BitVec(1)).unwrap();
        arena.var(s)
    };
    let b = {
        let s = arena.declare("b", Sort::BitVec(1)).unwrap();
        arena.var(s)
    };
    let eq = arena.eq(a, b).unwrap();
    let ult = arena.bv_ult(a, b).unwrap();
    let assertions = vec![eq, ult];

    // Bitblast the two predicates with the production emitter.
    let s1 = bitblast_step(&arena, eq, "s1").expect("bitblast_equal");
    let s2 = bitblast_step(&arena, ult, "s2").expect("bitblast_ult");

    // Alethe atoms.
    let a_eq_b = AletheTerm::App("=".to_owned(), vec![term_const("a"), term_const("b")]);
    let a_ult_b = AletheTerm::App("bvult".to_owned(), vec![term_const("a"), term_const("b")]);
    let a0 = bit0("a");
    let b0 = bit0("b");
    let a0_eq_b0 = AletheTerm::App("=".to_owned(), vec![a0.clone(), b0.clone()]);
    let not_a0_and_b0 = AletheTerm::App(
        "and".to_owned(),
        vec![
            AletheTerm::App("not".to_owned(), vec![a0.clone()]),
            b0.clone(),
        ],
    );

    let proof = vec![
        AletheCommand::Assume {
            id: "h1".to_owned(),
            clause: vec![pos(a_eq_b.clone())],
        },
        AletheCommand::Assume {
            id: "h2".to_owned(),
            clause: vec![pos(a_ult_b.clone())],
        },
        s1,
        s2,
        // Derive the bitblasted Boolean form of each assertion.
        step(
            "e1",
            vec![neg(a_eq_b), pos(a0_eq_b0.clone())],
            "equiv1",
            &["s1"],
            vec![],
        ),
        step(
            "b1",
            vec![pos(a0_eq_b0)],
            "resolution",
            &["e1", "h1"],
            vec![],
        ),
        step(
            "e2",
            vec![neg(a_ult_b), pos(not_a0_and_b0.clone())],
            "equiv1",
            &["s2"],
            vec![],
        ),
        step(
            "b2",
            vec![pos(not_a0_and_b0)],
            "resolution",
            &["e2", "h2"],
            vec![],
        ),
        // CNF-introduction + resolution to the empty clause.
        step(
            "c1",
            vec![neg(a0.clone())],
            "and",
            &["b2"],
            vec![term_const("0")],
        ),
        step(
            "c2",
            vec![pos(b0.clone())],
            "and",
            &["b2"],
            vec![term_const("1")],
        ),
        step("c3", vec![pos(a0), neg(b0)], "equiv2", &["b1"], vec![]),
        step("c4", vec![], "resolution", &["c3", "c1", "c2"], vec![]),
    ];
    let report = carcara_accepts(&bin, "full_qfbv", &arena, &assertions, &proof);
    assert!(report.contains("valid"), "expected 'valid', got:\n{report}");
}
