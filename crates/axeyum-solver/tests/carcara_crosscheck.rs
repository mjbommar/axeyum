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
#![cfg(feature = "full")]

use std::path::{Path, PathBuf};
use std::process::Command;

use axeyum_cnf::{AletheClause, AletheCommand, AletheLit, AletheTerm, write_alethe};
use axeyum_ir::{Rational, Sort, TermArena, TermId};
use axeyum_smtlib::write_script;
use axeyum_solver::{
    bitblast_step, lra_interpolant_certified, prove_lra_unsat_alethe,
    prove_qf_abv_row_diff_alethe_carcara, prove_qf_abv_row_same_alethe_carcara,
    prove_qf_abv_select_congruence_alethe_carcara, prove_qf_abv_unsat_alethe_via_elimination,
    prove_qf_bv_unsat_alethe, prove_qf_bv_unsat_alethe_ext_compare,
    prove_qf_bv_unsat_alethe_route2, prove_qf_dt_unsat_alethe_via_simplification,
    prove_qf_uf_unsat_alethe, prove_qf_ufbv_unsat_alethe, qf_bv_interpolant_certified,
    qf_uf_interpolant_certified, uflra_interpolant_certified,
};

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

/// Renders a `.smt2` whose assertions are **fully inlined** (no shared-subterm
/// `define-fun` hoisting), so each assertion term renders verbatim and matches the
/// proof's `assume` term. The production [`write_script`] hoists a shared interior
/// node into a `define-fun` alias, which Carcara keeps opaque when matching an
/// `assume` against the original premises; the compound driver's `assume` renders
/// the full term, so the cross-check feeds Carcara the inlined form. (The emitted
/// proof itself is identical either way — only the problem text differs.)
fn inlined_smt2(arena: &TermArena, assertions: &[TermId]) -> String {
    // Collect the BV-symbol declarations by walking the assertion DAG, sorted by
    // name for a deterministic, declared-before-use script.
    use std::collections::BTreeMap;
    use std::fmt::Write as _;
    let mut decls: BTreeMap<String, axeyum_ir::Sort> = BTreeMap::new();
    let mut stack: Vec<TermId> = assertions.to_vec();
    let mut seen: std::collections::HashSet<TermId> = std::collections::HashSet::new();
    while let Some(t) = stack.pop() {
        if !seen.insert(t) {
            continue;
        }
        match arena.node(t) {
            axeyum_ir::TermNode::Symbol(s) => {
                let (name, sort) = arena.symbol(*s);
                decls.insert(name.to_owned(), sort);
            }
            axeyum_ir::TermNode::App { args, .. } => stack.extend(args.iter().copied()),
            _ => {}
        }
    }
    let mut out = String::from("(set-logic QF_BV)\n");
    for (name, sort) in &decls {
        let axeyum_ir::Sort::BitVec(w) = sort else {
            panic!("inlined_smt2 helper only declares bit-vector symbols");
        };
        let _ = writeln!(out, "(declare-const {name} (_ BitVec {w}))");
    }
    for &a in assertions {
        let _ = writeln!(out, "(assert {})", axeyum_ir::render(arena, a));
    }
    out.push_str("(check-sat)\n");
    out
}

/// Like [`carcara_accepts`] but uses the fully-inlined `.smt2` (see
/// [`inlined_smt2`]) so a compound `assume` term over a shared subterm matches the
/// problem premise structurally.
fn carcara_accepts_inlined(
    bin: &Path,
    tag: &str,
    arena: &TermArena,
    assertions: &[TermId],
    proof: &[axeyum_cnf::AletheCommand],
) -> String {
    carcara_accepts_smt2(bin, tag, &inlined_smt2(arena, assertions), proof)
}

fn var(arena: &mut TermArena, name: &str) -> TermId {
    let s = arena.declare(name, Sort::BitVec(8)).expect("declare");
    arena.var(s)
}

/// Renders an SMT-LIB sort for the inlined `QF_UFLRA` script writer.
fn render_smt_sort(sort: &axeyum_ir::Sort) -> String {
    match sort {
        axeyum_ir::Sort::Real => "Real".to_owned(),
        axeyum_ir::Sort::Int => "Int".to_owned(),
        axeyum_ir::Sort::Bool => "Bool".to_owned(),
        axeyum_ir::Sort::BitVec(w) => format!("(_ BitVec {w})"),
        other => panic!("inlined_uflra_smt2: unsupported sort {other:?}"),
    }
}

/// Renders a `QF_UFLRA` `.smt2` whose assertions are **fully inlined** (no
/// `define-fun` hoisting), declaring every real symbol and every uninterpreted
/// function reached from the assertions. The `(f args)` applications then render
/// verbatim, so an `assume` of an opaque application atom matches the problem
/// premise structurally (the production [`write_script`] hoists `(f c)` into a
/// `define-fun` alias Carcara keeps opaque, which would not match).
fn inlined_uflra_smt2(arena: &TermArena, assertions: &[TermId]) -> String {
    use std::collections::BTreeMap;
    use std::fmt::Write as _;
    let mut consts: BTreeMap<String, axeyum_ir::Sort> = BTreeMap::new();
    let mut funcs: BTreeMap<String, (Vec<axeyum_ir::Sort>, axeyum_ir::Sort)> = BTreeMap::new();
    let mut stack: Vec<TermId> = assertions.to_vec();
    let mut seen: std::collections::HashSet<TermId> = std::collections::HashSet::new();
    while let Some(t) = stack.pop() {
        if !seen.insert(t) {
            continue;
        }
        match arena.node(t) {
            axeyum_ir::TermNode::Symbol(s) => {
                let (name, sort) = arena.symbol(*s);
                consts.insert(name.to_owned(), sort);
            }
            axeyum_ir::TermNode::App { op, args } => {
                if let axeyum_ir::Op::Apply(func) = op {
                    let (name, params, result) = arena.function(*func);
                    funcs.insert(name.to_owned(), (params.to_vec(), result));
                }
                stack.extend(args.iter().copied());
            }
            _ => {}
        }
    }
    let mut out = String::from("(set-logic QF_UFLRA)\n");
    for (name, sort) in &consts {
        let _ = writeln!(out, "(declare-const {name} {})", render_smt_sort(sort));
    }
    for (name, (params, result)) in &funcs {
        let params: Vec<String> = params.iter().map(render_smt_sort).collect();
        let _ = writeln!(
            out,
            "(declare-fun {name} ({}) {})",
            params.join(" "),
            render_smt_sort(result)
        );
    }
    for &a in assertions {
        let _ = writeln!(out, "(assert {})", axeyum_ir::render(arena, a));
    }
    out.push_str("(check-sat)\n");
    out
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

// --- Full QF_BV proof with a COMPOUND term: `cong`+`trans` operand substitution ---
//
// Resolves the last bridge unknown: a predicate over a compound bit-vector term
// (here `(bvand a a)`) is reduced to a bit-level Boolean by bitblasting each
// operand bottom-up and substituting via `cong` (congruence of `=` over the two
// bitblast equalities) + `trans` + `bitblast_equal`, then Boolean-refuted to
// `(cl)`. `(not (= (bvand a a) a))` is unsat since `a & a = a`.

fn app(head: &str, args: Vec<AletheTerm>) -> AletheTerm {
    AletheTerm::App(head.to_owned(), args)
}

#[test]
#[allow(clippy::too_many_lines, clippy::similar_names)]
fn full_qf_bv_compound_term_proof_is_accepted_by_carcara() {
    let Some(bin) = carcara_bin() else {
        eprintln!("[skip] carcara binary not found; build references/carcara to enable");
        return;
    };
    let mut arena = TermArena::new();
    let a = {
        let s = arena.declare("a", Sort::BitVec(1)).unwrap();
        arena.var(s)
    };
    let bvand_aa = arena.bv_and(a, a).unwrap();
    let eq = arena.eq(bvand_aa, a).unwrap();
    let not_eq = arena.not(eq).unwrap();
    let assertions = vec![not_eq];

    // Bitblast steps from the production emitter.
    let bb_and = bitblast_step(&arena, bvand_aa, "bb_and").expect("bitblast_and");
    let bb_var = bitblast_step(&arena, a, "bb_var").expect("bitblast_var");

    // Alethe terms.
    let a0 = bit0("a");
    let and_a0 = app("and", vec![a0.clone(), a0.clone()]);
    let bbt_and = app("@bbterm", vec![and_a0.clone()]);
    let bbt_a0 = app("@bbterm", vec![a0.clone()]);
    let pred_orig = app(
        "=",
        vec![
            app("bvand", vec![term_const("a"), term_const("a")]),
            term_const("a"),
        ],
    );
    let pred_bb = app("=", vec![bbt_and, bbt_a0]);
    let pred_bit = app("=", vec![and_a0.clone(), a0.clone()]);

    let proof = vec![
        AletheCommand::Assume {
            id: "h".to_owned(),
            clause: vec![neg(pred_orig.clone())],
        },
        bb_and,
        bb_var,
        // Substitute the bitblasted operands into the predicate by congruence,
        // then chain to the bit-level equality through the @bbterm forms.
        step(
            "cong1",
            vec![pos(app("=", vec![pred_orig.clone(), pred_bb.clone()]))],
            "cong",
            &["bb_and", "bb_var"],
            vec![],
        ),
        step(
            "bb_eq",
            vec![pos(app("=", vec![pred_bb, pred_bit.clone()]))],
            "bitblast_equal",
            &[],
            vec![],
        ),
        step(
            "trans1",
            vec![pos(app("=", vec![pred_orig.clone(), pred_bit.clone()]))],
            "trans",
            &["cong1", "bb_eq"],
            vec![],
        ),
        // Move the assumption to the bit level, then Boolean-refute it.
        step(
            "e2",
            vec![pos(pred_orig), neg(pred_bit.clone())],
            "equiv2",
            &["trans1"],
            vec![],
        ),
        step(
            "nq",
            vec![neg(pred_bit)],
            "resolution",
            &["e2", "h"],
            vec![],
        ),
        step(
            "nq1",
            vec![pos(and_a0.clone()), pos(a0.clone())],
            "not_equiv1",
            &["nq"],
            vec![],
        ),
        step(
            "nq2",
            vec![neg(and_a0.clone()), neg(a0.clone())],
            "not_equiv2",
            &["nq"],
            vec![],
        ),
        step(
            "ap",
            vec![neg(and_a0.clone()), pos(a0.clone())],
            "and_pos",
            &[],
            vec![term_const("0")],
        ),
        step(
            "an",
            vec![pos(and_a0), neg(a0.clone()), neg(a0.clone())],
            "and_neg",
            &[],
            vec![],
        ),
        step(
            "r1",
            vec![pos(a0.clone())],
            "resolution",
            &["nq1", "ap"],
            vec![],
        ),
        step("r2", vec![neg(a0)], "resolution", &["nq2", "an"], vec![]),
        step("done", vec![], "resolution", &["r1", "r2"], vec![]),
    ];

    let report = carcara_accepts(&bin, "compound_qfbv", &arena, &assertions, &proof);
    assert!(report.contains("valid"), "expected 'valid', got:\n{report}");
}

// --- General QF_BV `unsat` Alethe driver: `prove_qf_bv_unsat_alethe` ---------
//
// The driver builds a complete refutation closing to `(cl)` for the
// variable/constant predicate fragment, validated end-to-end by the Carcara
// binary. Each test constructs an unsat instance in the IR, calls the driver, and
// asserts Carcara reports `valid`.

fn bvw(arena: &mut TermArena, name: &str, width: u32) -> TermId {
    let s = arena.declare(name, Sort::BitVec(width)).expect("declare");
    arena.var(s)
}

#[test]
fn driver_eq_and_ult_conflict_is_accepted_by_carcara() {
    let Some(bin) = carcara_bin() else {
        eprintln!("[skip] carcara binary not found; build references/carcara to enable");
        return;
    };
    // (= a b) ∧ (bvult a b) over 1-bit a, b — unsat: a = b yet a < b. This is the
    // committed template, now reproduced by the driver.
    let mut arena = TermArena::new();
    let a = bvw(&mut arena, "a", 1);
    let b = bvw(&mut arena, "b", 1);
    let eq = arena.eq(a, b).unwrap();
    let ult = arena.bv_ult(a, b).unwrap();
    let assertions = vec![eq, ult];

    let proof = prove_qf_bv_unsat_alethe(&arena, &assertions).expect("emit QF_BV proof");
    let report = carcara_accepts(&bin, "driver_eq_ult", &arena, &assertions, &proof);
    assert!(report.contains("valid"), "expected 'valid', got:\n{report}");
}

#[test]
fn driver_eq_and_neq_conflict_is_accepted_by_carcara() {
    let Some(bin) = carcara_bin() else {
        eprintln!("[skip] carcara binary not found; build references/carcara to enable");
        return;
    };
    // (= a b) ∧ (not (= a b)) over width-2 a, b — unsat with multi-bit equality
    // structure (the negated equality exercises the `not (and …)` refutation).
    let mut arena = TermArena::new();
    let a = bvw(&mut arena, "a", 2);
    let b = bvw(&mut arena, "b", 2);
    let eq = arena.eq(a, b).unwrap();
    let neq = arena.not(eq).unwrap();
    let assertions = vec![eq, neq];

    let proof = prove_qf_bv_unsat_alethe(&arena, &assertions).expect("emit QF_BV proof");
    let report = carcara_accepts(&bin, "driver_eq_neq", &arena, &assertions, &proof);
    assert!(report.contains("valid"), "expected 'valid', got:\n{report}");
}

#[test]
fn driver_ult_cycle_conflict_is_accepted_by_carcara() {
    let Some(bin) = carcara_bin() else {
        eprintln!("[skip] carcara binary not found; build references/carcara to enable");
        return;
    };
    // (bvult a b) ∧ (bvult b a) over width-2 a, b — unsat: < is antisymmetric.
    let mut arena = TermArena::new();
    let a = bvw(&mut arena, "a", 2);
    let b = bvw(&mut arena, "b", 2);
    let ab = arena.bv_ult(a, b).unwrap();
    let ba = arena.bv_ult(b, a).unwrap();
    let assertions = vec![ab, ba];

    let proof = prove_qf_bv_unsat_alethe(&arena, &assertions).expect("emit QF_BV proof");
    let report = carcara_accepts(&bin, "driver_ult_cycle", &arena, &assertions, &proof);
    assert!(report.contains("valid"), "expected 'valid', got:\n{report}");
}

#[test]
fn driver_slt_and_const_conflict_is_accepted_by_carcara() {
    let Some(bin) = carcara_bin() else {
        eprintln!("[skip] carcara binary not found; build references/carcara to enable");
        return;
    };
    // (bvslt a b) ∧ (= a b) over width-3 a, b — unsat: a = b yet a < b (signed).
    let mut arena = TermArena::new();
    let a = bvw(&mut arena, "a", 3);
    let b = bvw(&mut arena, "b", 3);
    let slt = arena.bv_slt(a, b).unwrap();
    let eq = arena.eq(a, b).unwrap();
    let assertions = vec![slt, eq];

    let proof = prove_qf_bv_unsat_alethe(&arena, &assertions).expect("emit QF_BV proof");
    let report = carcara_accepts(&bin, "driver_slt_eq", &arena, &assertions, &proof);
    assert!(report.contains("valid"), "expected 'valid', got:\n{report}");
}

#[test]
fn driver_returns_none_for_sat_instance() {
    // (bvult a b) alone over width-2 — satisfiable, so no refutation exists.
    let mut arena = TermArena::new();
    let a = bvw(&mut arena, "a", 2);
    let b = bvw(&mut arena, "b", 2);
    let ult = arena.bv_ult(a, b).unwrap();
    assert!(
        prove_qf_bv_unsat_alethe(&arena, &[ult]).is_none(),
        "a sat instance has no unsat proof"
    );
}

#[test]
fn driver_returns_none_for_shift_subterm_instance() {
    // (= (bvshl a b) a) ∧ (not (= (bvshl a b) a)) is unsat, but `bvshl` is a Carcara
    // hole (not bit-blastable), so the compound-term driver bails to None.
    let mut arena = TermArena::new();
    let a = bvw(&mut arena, "a", 2);
    let b = bvw(&mut arena, "b", 2);
    let shl = arena.bv_shl(a, b).unwrap();
    let eq = arena.eq(shl, a).unwrap();
    let neq = arena.not(eq).unwrap();
    assert!(
        prove_qf_bv_unsat_alethe(&arena, &[eq, neq]).is_none(),
        "a shift subterm is a Carcara hole, outside the bit-blastable fragment"
    );
}

#[test]
fn driver_returns_none_for_div_subterm_instance() {
    // (= (bvudiv a b) a) ∧ (not …) is unsat, but `bvudiv` is a Carcara hole → None.
    let mut arena = TermArena::new();
    let a = bvw(&mut arena, "a", 2);
    let b = bvw(&mut arena, "b", 2);
    let div = arena.bv_udiv(a, b).unwrap();
    let eq = arena.eq(div, a).unwrap();
    let neq = arena.not(eq).unwrap();
    assert!(
        prove_qf_bv_unsat_alethe(&arena, &[eq, neq]).is_none(),
        "a division subterm is a Carcara hole, outside the bit-blastable fragment"
    );
}

// --- Compound-term predicate fragment: cong/bitblast/trans reduction ---------
//
// The driver now reduces predicates over *compound* bit-vector terms by
// bit-blasting each operand bottom-up to its `@bbterm` form, substituting via
// `cong`, and `trans`-chaining to the bit-level Boolean — then Boolean-refuting to
// `(cl)`. Each test builds a genuinely-unsat instance (the SAT-BV path confirms it
// inside the driver), emits the proof, and asserts Carcara reports `valid`.

#[test]
fn driver_bitwise_compound_is_accepted_by_carcara() {
    let Some(bin) = carcara_bin() else {
        eprintln!("[skip] carcara binary not found; build references/carcara to enable");
        return;
    };
    // (= (bvand a b) c) ∧ (= a b) ∧ (not (= b c)) over width 2 — unsat:
    // a = b ⇒ (bvand a b) = b; the first then forces c = b, contradicting b ≠ c.
    let mut arena = TermArena::new();
    let a = bvw(&mut arena, "a", 2);
    let b = bvw(&mut arena, "b", 2);
    let c = bvw(&mut arena, "c", 2);
    let and = arena.bv_and(a, b).unwrap();
    let eq_and_c = arena.eq(and, c).unwrap();
    let eq_ab = arena.eq(a, b).unwrap();
    let bc = arena.eq(b, c).unwrap();
    let neq_bc = arena.not(bc).unwrap();
    let assertions = vec![eq_and_c, eq_ab, neq_bc];

    let proof = prove_qf_bv_unsat_alethe(&arena, &assertions).expect("emit QF_BV proof");
    let report =
        carcara_accepts_inlined(&bin, "driver_bitwise_compound", &arena, &assertions, &proof);
    assert!(report.contains("valid"), "expected 'valid', got:\n{report}");
}

#[test]
fn driver_bvand_idempotent_compound_is_accepted_by_carcara() {
    let Some(bin) = carcara_bin() else {
        eprintln!("[skip] carcara binary not found; build references/carcara to enable");
        return;
    };
    // (not (= (bvand a a) a)) over width 3 — unsat since a & a = a. The shared
    // operand `a` is bit-blasted once (DAG dedup) and both cong premises reference it.
    let mut arena = TermArena::new();
    let a = bvw(&mut arena, "a", 3);
    let and = arena.bv_and(a, a).unwrap();
    let eq = arena.eq(and, a).unwrap();
    let neq = arena.not(eq).unwrap();
    let assertions = vec![neq];

    let proof = prove_qf_bv_unsat_alethe(&arena, &assertions).expect("emit QF_BV proof");
    let report = carcara_accepts_inlined(&bin, "driver_bvand_idem", &arena, &assertions, &proof);
    assert!(report.contains("valid"), "expected 'valid', got:\n{report}");
}

#[test]
fn driver_arithmetic_compound_is_accepted_by_carcara() {
    let Some(bin) = carcara_bin() else {
        eprintln!("[skip] carcara binary not found; build references/carcara to enable");
        return;
    };
    // (= (bvadd a b) c) ∧ (= (bvadd a b) d) ∧ (not (= c d)) over width 3 — unsat:
    // c = (a+b) = d contradicts c ≠ d. The shared subterm `(bvadd a b)` is reduced once.
    let mut arena = TermArena::new();
    let a = bvw(&mut arena, "a", 3);
    let b = bvw(&mut arena, "b", 3);
    let c = bvw(&mut arena, "c", 3);
    let d = bvw(&mut arena, "d", 3);
    let sum = arena.bv_add(a, b).unwrap();
    let eq_c = arena.eq(sum, c).unwrap();
    let eq_d = arena.eq(sum, d).unwrap();
    let cd = arena.eq(c, d).unwrap();
    let neq_cd = arena.not(cd).unwrap();
    let assertions = vec![eq_c, eq_d, neq_cd];

    let proof = prove_qf_bv_unsat_alethe(&arena, &assertions).expect("emit QF_BV proof");
    let report =
        carcara_accepts_inlined(&bin, "driver_arith_compound", &arena, &assertions, &proof);
    assert!(report.contains("valid"), "expected 'valid', got:\n{report}");
}

#[test]
fn driver_nested_compound_is_accepted_by_carcara() {
    let Some(bin) = carcara_bin() else {
        eprintln!("[skip] carcara binary not found; build references/carcara to enable");
        return;
    };
    // (= (bvand (bvor a b) c) d) ∧ (= (bvor a b) c) ∧ (not (= c d)) over width 2 —
    // a genuinely NESTED compound: the inner `(bvor a b)` and the outer `(bvand … c)`
    // each reduce bottom-up. With (bvor a b) = c, the outer is (bvand c c) = c, so
    // d = c, contradicting c ≠ d.
    let mut arena = TermArena::new();
    let a = bvw(&mut arena, "a", 2);
    let b = bvw(&mut arena, "b", 2);
    let c = bvw(&mut arena, "c", 2);
    let d = bvw(&mut arena, "d", 2);
    let or = arena.bv_or(a, b).unwrap();
    let and = arena.bv_and(or, c).unwrap();
    let eq_and_d = arena.eq(and, d).unwrap();
    let eq_or_c = arena.eq(or, c).unwrap();
    let cd = arena.eq(c, d).unwrap();
    let neq_cd = arena.not(cd).unwrap();
    let assertions = vec![eq_and_d, eq_or_c, neq_cd];

    let proof = prove_qf_bv_unsat_alethe(&arena, &assertions).expect("emit QF_BV proof");
    let report =
        carcara_accepts_inlined(&bin, "driver_nested_compound", &arena, &assertions, &proof);
    assert!(report.contains("valid"), "expected 'valid', got:\n{report}");
}

#[test]
fn driver_compound_in_ult_predicate_is_accepted_by_carcara() {
    let Some(bin) = carcara_bin() else {
        eprintln!("[skip] carcara binary not found; build references/carcara to enable");
        return;
    };
    // (bvult (bvadd a b) c) ∧ (= (bvadd a b) c) over width 3 — unsat: (a+b) < c yet
    // (a+b) = c. A compound operand inside a `bvult` predicate (not just `=`).
    let mut arena = TermArena::new();
    let a = bvw(&mut arena, "a", 3);
    let b = bvw(&mut arena, "b", 3);
    let c = bvw(&mut arena, "c", 3);
    let sum = arena.bv_add(a, b).unwrap();
    let ult = arena.bv_ult(sum, c).unwrap();
    let eq = arena.eq(sum, c).unwrap();
    let assertions = vec![ult, eq];

    let proof = prove_qf_bv_unsat_alethe(&arena, &assertions).expect("emit QF_BV proof");
    let report = carcara_accepts_inlined(&bin, "driver_compound_ult", &arena, &assertions, &proof);
    assert!(report.contains("valid"), "expected 'valid', got:\n{report}");
}

// --- QF_UFBV Ackermann certificate: `prove_qf_ufbv_unsat_alethe` -------------
//
// The composed proof refutes the *reduced* problem — the rewritten originals
// (function applications abstracted to fresh `!fn_app_*` symbols) plus the
// abstraction's defining equations `(= !fn_app_i (f a_i))` — with every
// functional-consistency constraint **derived** by `eq_congruent` rather than
// assumed. The matching `.smt2` therefore declares the fresh symbols and asserts
// the rewritten originals together with the (conservative) abstraction
// definitions, so each proof `assume` matches an original problem premise.

#[test]
fn ufbv_unary_congruence_is_accepted_by_carcara() {
    let Some(bin) = carcara_bin() else {
        eprintln!("[skip] carcara binary not found; build references/carcara to enable");
        return;
    };
    // f(a) = #b00 ∧ a = b ∧ ¬(f(b) = #b00) — unsat by congruence over `f`.
    let mut arena = TermArena::new();
    let f = arena
        .declare_fun("f", &[Sort::BitVec(2)], Sort::BitVec(2))
        .unwrap();
    let a = bvw(&mut arena, "a", 2);
    let b = bvw(&mut arena, "b", 2);
    let fa = arena.apply(f, &[a]).unwrap();
    let fb = arena.apply(f, &[b]).unwrap();
    let c00 = arena.bv_const(2, 0).unwrap();
    let e1 = arena.eq(fa, c00).unwrap();
    let e2 = arena.eq(a, b).unwrap();
    let e3 = {
        let e = arena.eq(fb, c00).unwrap();
        arena.not(e).unwrap()
    };

    let proof = prove_qf_ufbv_unsat_alethe(&mut arena, &[e1, e2, e3]).expect("emit QF_UFBV proof");
    let smt2 = "\
(set-logic QF_UFBV)
(declare-fun f ((_ BitVec 2)) (_ BitVec 2))
(declare-const a (_ BitVec 2))
(declare-const b (_ BitVec 2))
(declare-const !fn_app_0 (_ BitVec 2))
(declare-const !fn_app_1 (_ BitVec 2))
(assert (= !fn_app_0 #b00))
(assert (= a b))
(assert (not (= !fn_app_1 #b00)))
(assert (= !fn_app_0 (f a)))
(assert (= (f b) !fn_app_1))
(check-sat)
";
    let report = carcara_accepts_smt2(&bin, "ufbv_unary", smt2, &proof);
    assert!(report.contains("valid"), "expected 'valid', got:\n{report}");
}

#[test]
#[allow(clippy::many_single_char_names)]
fn ufbv_binary_congruence_is_accepted_by_carcara() {
    let Some(bin) = carcara_bin() else {
        eprintln!("[skip] carcara binary not found; build references/carcara to enable");
        return;
    };
    // g(a, b) = #b00 ∧ a = c ∧ b = d ∧ ¬(g(c, d) = #b00) — two-argument congruence.
    let mut arena = TermArena::new();
    let g = arena
        .declare_fun("g", &[Sort::BitVec(2), Sort::BitVec(2)], Sort::BitVec(2))
        .unwrap();
    let a = bvw(&mut arena, "a", 2);
    let b = bvw(&mut arena, "b", 2);
    let c = bvw(&mut arena, "c", 2);
    let d = bvw(&mut arena, "d", 2);
    let gab = arena.apply(g, &[a, b]).unwrap();
    let gcd = arena.apply(g, &[c, d]).unwrap();
    let c00 = arena.bv_const(2, 0).unwrap();
    let e1 = arena.eq(gab, c00).unwrap();
    let e2 = arena.eq(a, c).unwrap();
    let e3 = arena.eq(b, d).unwrap();
    let e4 = {
        let e = arena.eq(gcd, c00).unwrap();
        arena.not(e).unwrap()
    };

    let proof =
        prove_qf_ufbv_unsat_alethe(&mut arena, &[e1, e2, e3, e4]).expect("emit QF_UFBV proof");
    let smt2 = "\
(set-logic QF_UFBV)
(declare-fun g ((_ BitVec 2) (_ BitVec 2)) (_ BitVec 2))
(declare-const a (_ BitVec 2))
(declare-const b (_ BitVec 2))
(declare-const c (_ BitVec 2))
(declare-const d (_ BitVec 2))
(declare-const !fn_app_0 (_ BitVec 2))
(declare-const !fn_app_1 (_ BitVec 2))
(assert (= !fn_app_0 #b00))
(assert (= a c))
(assert (= b d))
(assert (not (= !fn_app_1 #b00)))
(assert (= !fn_app_0 (g a b)))
(assert (= (g c d) !fn_app_1))
(check-sat)
";
    let report = carcara_accepts_smt2(&bin, "ufbv_binary", smt2, &proof);
    assert!(report.contains("valid"), "expected 'valid', got:\n{report}");
}

#[test]
#[allow(clippy::many_single_char_names)]
fn ufbv_transitive_congruence_is_accepted_by_carcara() {
    let Some(bin) = carcara_bin() else {
        eprintln!("[skip] carcara binary not found; build references/carcara to enable");
        return;
    };
    // f(a) = #b00 ∧ a = b ∧ b = c ∧ ¬(f(c) = #b00). The argument equality a = c is
    // NOT directly asserted — only derivable by transitive closure a = b = c — so
    // the certificate proves it with an `eq_transitive` chain over the two asserted
    // edges. Carcara must accept that chain.
    let mut arena = TermArena::new();
    let f = arena
        .declare_fun("f", &[Sort::BitVec(2)], Sort::BitVec(2))
        .unwrap();
    let a = bvw(&mut arena, "a", 2);
    let b = bvw(&mut arena, "b", 2);
    let c = bvw(&mut arena, "c", 2);
    let fa = arena.apply(f, &[a]).unwrap();
    let fc = arena.apply(f, &[c]).unwrap();
    let c00 = arena.bv_const(2, 0).unwrap();
    let e1 = arena.eq(fa, c00).unwrap();
    let e2 = arena.eq(a, b).unwrap();
    let e3 = arena.eq(b, c).unwrap();
    let e4 = {
        let e = arena.eq(fc, c00).unwrap();
        arena.not(e).unwrap()
    };

    let proof =
        prove_qf_ufbv_unsat_alethe(&mut arena, &[e1, e2, e3, e4]).expect("emit QF_UFBV proof");
    let smt2 = "\
(set-logic QF_UFBV)
(declare-fun f ((_ BitVec 2)) (_ BitVec 2))
(declare-const a (_ BitVec 2))
(declare-const b (_ BitVec 2))
(declare-const c (_ BitVec 2))
(declare-const !fn_app_0 (_ BitVec 2))
(declare-const !fn_app_1 (_ BitVec 2))
(assert (= !fn_app_0 #b00))
(assert (= a b))
(assert (= b c))
(assert (not (= !fn_app_1 #b00)))
(assert (= !fn_app_0 (f a)))
(assert (= (f c) !fn_app_1))
(check-sat)
";
    let report = carcara_accepts_smt2(&bin, "ufbv_transitive", smt2, &proof);
    assert!(report.contains("valid"), "expected 'valid', got:\n{report}");
}

#[test]
#[allow(clippy::many_single_char_names)]
fn ufbv_nested_congruence_is_accepted_by_carcara() {
    let Some(bin) = carcara_bin() else {
        eprintln!("[skip] carcara binary not found; build references/carcara to enable");
        return;
    };
    // f(g(a)) = #b00 ∧ a = b ∧ ¬(f(g(b)) = #b00). The two f-applications' arguments
    // are g(a) and g(b) — equal NOT by a chain of asserted equalities but by
    // CONGRUENCE over g (from a = b). The asserted-edge BFS declines; the e-graph
    // congruence fallback derives the argument equality with eq_congruent over g.
    // The Ackermann reduction abstracts every application:
    //   g(a) → !fn_app_0, g(b) → !fn_app_2, f(!fn_app_0) → !fn_app_1,
    //   f(!fn_app_2) → !fn_app_3.
    // Carcara must accept the spliced eq_congruent/eq_transitive derivation.
    let mut arena = TermArena::new();
    let f = arena
        .declare_fun("f", &[Sort::BitVec(2)], Sort::BitVec(2))
        .unwrap();
    let g = arena
        .declare_fun("g", &[Sort::BitVec(2)], Sort::BitVec(2))
        .unwrap();
    let a = bvw(&mut arena, "a", 2);
    let b = bvw(&mut arena, "b", 2);
    let ga = arena.apply(g, &[a]).unwrap();
    let gb = arena.apply(g, &[b]).unwrap();
    let fga = arena.apply(f, &[ga]).unwrap();
    let fgb = arena.apply(f, &[gb]).unwrap();
    let c00 = arena.bv_const(2, 0).unwrap();
    let e1 = arena.eq(fga, c00).unwrap();
    let e2 = arena.eq(a, b).unwrap();
    let e3 = {
        let e = arena.eq(fgb, c00).unwrap();
        arena.not(e).unwrap()
    };

    let proof = prove_qf_ufbv_unsat_alethe(&mut arena, &[e1, e2, e3]).expect("emit QF_UFBV proof");
    let smt2 = "\
(set-logic QF_UFBV)
(declare-fun f ((_ BitVec 2)) (_ BitVec 2))
(declare-fun g ((_ BitVec 2)) (_ BitVec 2))
(declare-const a (_ BitVec 2))
(declare-const b (_ BitVec 2))
(declare-const !fn_app_0 (_ BitVec 2))
(declare-const !fn_app_1 (_ BitVec 2))
(declare-const !fn_app_2 (_ BitVec 2))
(declare-const !fn_app_3 (_ BitVec 2))
(assert (= !fn_app_1 #b00))
(assert (= a b))
(assert (not (= !fn_app_3 #b00)))
(assert (= !fn_app_0 (g a)))
(assert (= (g b) !fn_app_2))
(assert (= !fn_app_1 (f !fn_app_0)))
(assert (= (f !fn_app_2) !fn_app_3))
(check-sat)
";
    let report = carcara_accepts_smt2(&bin, "ufbv_nested", smt2, &proof);
    assert!(report.contains("valid"), "expected 'valid', got:\n{report}");
}

// --- QF_ABV array-elimination certificate: ----------------------------------
// `prove_qf_abv_unsat_alethe_via_elimination`
//
// The composed proof certifies the **read-consistency** (Ackermann-over-select)
// trust hole: an array variable `a` is the unary uninterpreted function
// `!sel_a := λ idx. select(a, idx)`, each abstracted select `select(a, idx)`
// becomes a fresh `!arr_sel_*` symbol with defining equation
// `(= !arr_sel_i (!sel_a idx_i))`, and the read-consistency constraint
// `(= idx_i idx_j) -> (= !arr_sel_i !arr_sel_j)` is **derived** by `eq_congruent`
// over `!sel_a` rather than assumed. The certificate uses **no array theory rule**
// (`!sel_a` is a plain uninterpreted function), so Carcara checks the proof in
// full — `eq_congruent`, `eq_transitive`, and every bit-blast step. The matching
// `.smt2` declares `!sel_a`, the fresh select symbols, and asserts the rewritten
// originals plus the (conservative) abstraction definitions, so each proof
// `assume` matches an original premise.

#[test]
#[allow(clippy::many_single_char_names)] // a, i, j, c, e: array, indices, const, expr
fn abv_select_consistency_is_accepted_by_carcara() {
    let Some(bin) = carcara_bin() else {
        eprintln!("[skip] carcara binary not found; build references/carcara to enable");
        return;
    };
    // select(a, i) = #b0…0 ∧ i = j ∧ ¬(select(a, j) = #b0…0) — unsat by
    // read-consistency over `select(a, ·)`.
    let mut arena = TermArena::new();
    let a = arena.array_var("a", 4, 8).unwrap();
    let i = bvw(&mut arena, "i", 4);
    let j = bvw(&mut arena, "j", 4);
    let c = arena.bv_const(8, 0).unwrap();
    let sa = arena.select(a, i).unwrap();
    let sb = arena.select(a, j).unwrap();
    let e1 = arena.eq(sa, c).unwrap();
    let e2 = arena.eq(i, j).unwrap();
    let e3 = {
        let e = arena.eq(sb, c).unwrap();
        arena.not(e).unwrap()
    };

    let proof = prove_qf_abv_unsat_alethe_via_elimination(&mut arena, &[e1, e2, e3])
        .expect("emit QF_ABV array-elimination proof");
    let smt2 = "\
(set-logic QF_AUFBV)
(declare-fun !sel_a ((_ BitVec 4)) (_ BitVec 8))
(declare-const i (_ BitVec 4))
(declare-const j (_ BitVec 4))
(declare-const !arr_sel_0 (_ BitVec 8))
(declare-const !arr_sel_1 (_ BitVec 8))
(assert (= !arr_sel_0 #b00000000))
(assert (= i j))
(assert (not (= !arr_sel_1 #b00000000)))
(assert (= !arr_sel_0 (!sel_a i)))
(assert (= (!sel_a j) !arr_sel_1))
(check-sat)
";
    let report = carcara_accepts_smt2(&bin, "abv_select_consistency", smt2, &proof);
    assert!(report.contains("valid"), "expected 'valid', got:\n{report}");
}

#[test]
#[allow(clippy::many_single_char_names)]
fn abv_select_consistency_transitive_is_accepted_by_carcara() {
    let Some(bin) = carcara_bin() else {
        eprintln!("[skip] carcara binary not found; build references/carcara to enable");
        return;
    };
    // select(a, i) = #b0…0 ∧ i = k ∧ k = j ∧ ¬(select(a, j) = #b0…0): the index
    // equality i = j holds only by transitive closure i = k = j, so the certificate
    // derives it with an `eq_transitive` chain. Carcara must accept that chain.
    let mut arena = TermArena::new();
    let a = arena.array_var("a", 4, 8).unwrap();
    let i = bvw(&mut arena, "i", 4);
    let k = bvw(&mut arena, "k", 4);
    let j = bvw(&mut arena, "j", 4);
    let c = arena.bv_const(8, 0).unwrap();
    let sa = arena.select(a, i).unwrap();
    let sb = arena.select(a, j).unwrap();
    let e1 = arena.eq(sa, c).unwrap();
    let e2 = arena.eq(i, k).unwrap();
    let e3 = arena.eq(k, j).unwrap();
    let e4 = {
        let e = arena.eq(sb, c).unwrap();
        arena.not(e).unwrap()
    };

    let proof = prove_qf_abv_unsat_alethe_via_elimination(&mut arena, &[e1, e2, e3, e4])
        .expect("emit QF_ABV array-elimination proof");
    let smt2 = "\
(set-logic QF_AUFBV)
(declare-fun !sel_a ((_ BitVec 4)) (_ BitVec 8))
(declare-const i (_ BitVec 4))
(declare-const k (_ BitVec 4))
(declare-const j (_ BitVec 4))
(declare-const !arr_sel_0 (_ BitVec 8))
(declare-const !arr_sel_1 (_ BitVec 8))
(assert (= !arr_sel_0 #b00000000))
(assert (= i k))
(assert (= k j))
(assert (not (= !arr_sel_1 #b00000000)))
(assert (= !arr_sel_0 (!sel_a i)))
(assert (= (!sel_a j) !arr_sel_1))
(check-sat)
";
    let report = carcara_accepts_smt2(&bin, "abv_select_consistency_transitive", smt2, &proof);
    assert!(report.contains("valid"), "expected 'valid', got:\n{report}");
}

// --- Datatype read-over-construct certificate: -------------------------------
// `prove_qf_dt_unsat_alethe_via_simplification`
//
// The composed proof certifies the **`select`-over-`construct`** fold (the
// read-over-construct fragment). For the redex `select_0(mk(a, b))`, a fresh
// abstraction `!dt_w_0` replaces it, the redex is rendered **structurally** as the
// selector application `(!dtsel_2_0_mk (!dtcon_2_mk a b))` over an uninterpreted
// datatype sort `Pair`, and the fold `(= !dt_w_0 a)` is **derived** by
// `eq_transitive` over the abstraction definition
// `(= !dt_w_0 (!dtsel_2_0_mk (!dtcon_2_mk a b)))` and the projection equation
// `(= (!dtsel_2_0_mk (!dtcon_2_mk a b)) a)`.
//
// Carcara has **no datatype rule**, so the two reserved heads are plain
// uninterpreted functions and the projection equation is asserted as a *premise*
// in the `.smt2` (exactly like the array-elim abstraction definitions); Carcara
// then checks every structural step of the proof (the abstraction-definition
// resolution, the `eq_transitive`, and the whole bit-blast tail). The projection
// equation's *truth* is what Carcara takes as a premise (internal-only); its *use*
// in the refutation is fully Carcara-checked. **The kernel reconstruction is the
// checker that discharges the projection by ι-reduction** (route A): there it is
// `Eq.refl` over a kernel inductive `Pair` with constructor `Pair.mk`, not an
// assumed axiom. The matching `.smt2` declares the `Pair` sort, the `mk`/`sel`
// functions, `!dt_w_0`, and `a`, and asserts the residual originals plus the
// abstraction definition and the projection equation, so each proof `assume`
// matches a premise.
#[test]
#[allow(clippy::many_single_char_names)] // a, b, p, c, e: fields, ctor app, const, expr
fn dt_select_over_construct_is_accepted_by_carcara() {
    let Some(bin) = carcara_bin() else {
        eprintln!("[skip] carcara binary not found; build references/carcara to enable");
        return;
    };
    // select_0(mk(a, b)) = #b00 ∧ ¬(a = #b00) — unsat by read-over-construct.
    let mut arena = TermArena::new();
    let pair = arena.declare_datatype("Pair");
    let mk = arena.add_constructor(
        pair,
        "mk",
        &[
            ("a".into(), axeyum_ir::Sort::BitVec(2)),
            ("b".into(), axeyum_ir::Sort::BitVec(2)),
        ],
    );
    let a = bvw(&mut arena, "a", 2);
    let b = bvw(&mut arena, "b", 2);
    let p = arena.construct(mk, &[a, b]).unwrap();
    let sel = arena.dt_select(mk, 0, p).unwrap();
    let c = arena.bv_const(2, 0).unwrap();
    let e1 = arena.eq(sel, c).unwrap();
    let e2 = {
        let e = arena.eq(a, c).unwrap();
        arena.not(e).unwrap()
    };

    let proof = prove_qf_dt_unsat_alethe_via_simplification(&mut arena, &[e1, e2])
        .expect("emit datatype read-over-construct proof");
    // The redex is rendered structurally as `(!dtsel_2_0_mk (!dtcon_2_mk a b))`,
    // with `Pair` an uninterpreted sort and the two reserved heads uninterpreted
    // functions for Carcara (which has no datatype rule).
    let smt2 = "\
(set-logic QF_UFBV)
(declare-sort Pair 0)
(declare-const a (_ BitVec 2))
(declare-const b (_ BitVec 2))
(declare-const !dt_w_0 (_ BitVec 2))
(declare-fun !dtcon_2_mk ((_ BitVec 2) (_ BitVec 2)) Pair)
(declare-fun !dtsel_2_0_mk (Pair) (_ BitVec 2))
(assert (= !dt_w_0 #b00))
(assert (not (= a #b00)))
(assert (= !dt_w_0 (!dtsel_2_0_mk (!dtcon_2_mk a b))))
(assert (= (!dtsel_2_0_mk (!dtcon_2_mk a b)) a))
(check-sat)
";
    let report = carcara_accepts_smt2(&bin, "dt_select_over_construct", smt2, &proof);
    assert!(report.contains("valid"), "expected 'valid', got:\n{report}");
}

// --- Route 2: certify the UN-LOWERED `bvsub` original (Task #15) -------------
//
// `prove_qf_bv_unsat_alethe_route2` keeps `(bvsub a b)` at the term level and bridges
// it to `(bvadd a (bvneg b))` with a Carcara-valid `bv_poly_simp` step, then bit-blasts
// the `bvadd`/`bvneg`. Carcara validates the whole refutation — INCLUDING the
// `bv_poly_simp` `bvsub`-rewrite step — over an `.smt2` whose assertions literally
// contain `bvsub`. This is the third-party trust anchor for the un-lowered cert.

#[test]
fn route2_bvsub_rewrite_proof_is_accepted_by_carcara() {
    let Some(bin) = carcara_bin() else {
        eprintln!("[skip] carcara binary not found; build references/carcara to enable");
        return;
    };
    // (= (bvsub a b) a) ∧ (bvult a b) over width-2 a, b — unsat: `a - b = a` forces
    // `b = 0`, then `a < b = a < 0` is impossible (unsigned). All-variable, exercising
    // the two's-complement subtract carry semantics. The original assertions contain
    // `bvsub` verbatim.
    let mut arena = TermArena::new();
    let a = bvw(&mut arena, "a", 2);
    let b = bvw(&mut arena, "b", 2);
    let sub = arena.bv_sub(a, b).unwrap();
    let eq = arena.eq(sub, a).unwrap();
    let ult = arena.bv_ult(a, b).unwrap();
    let assertions = vec![eq, ult];

    let proof =
        prove_qf_bv_unsat_alethe_route2(&mut arena, &assertions).expect("emit Route-2 proof");
    // The proof must contain the Carcara `bv_poly_simp` bvsub-rewrite step.
    assert!(
        proof.iter().any(|c| matches!(
            c,
            axeyum_cnf::AletheCommand::Step { rule, .. } if rule == "bv_poly_simp"
        )),
        "Route-2 proof must contain a bv_poly_simp step"
    );
    let report = carcara_accepts(&bin, "route2_bvsub", &arena, &assertions, &proof);
    assert!(report.contains("valid"), "expected 'valid', got:\n{report}");
}

// --- Extended comparisons: bvule/bvugt/bvuge/bvsle/bvsgt/bvsge ----------------
//
// Carcara bit-blasts only `bvult`/`bvslt`; it has no rule for the six extended
// comparisons, and (verified empirically) no stock rule — `comp_simplify`,
// `equiv_simplify`, `bv_poly_simp`, `refl`, `connective_def`, `rare_rewrite` without an
// external RARE file — rewrites one comparison to the other inside a proof. So
// `prove_qf_bv_unsat_alethe_ext_compare` normalizes each top-level extended comparison to
// its denotation-equal `bvult`/`bvslt` (possibly `not`-wrapped) form BEFORE emission, and
// returns the normalized assertions. The `.smt2` is rendered over those normalized
// assertions — the exact premises the proof's `assume`s match — and Carcara validates the
// whole core refutation. Each test builds a genuinely-unsat instance over a different
// extended comparison.

/// Emits a `prove_qf_bv_unsat_alethe_ext_compare` proof for `assertions`, renders the
/// `.smt2` over the *normalized* assertions it returns, and asserts Carcara reports
/// `valid` (and not `holey`).
fn assert_ext_compare_accepted(tag: &str, assertions: &[TermId], arena: &mut TermArena) {
    let Some(bin) = carcara_bin() else {
        eprintln!("[skip] carcara binary not found; build references/carcara to enable");
        return;
    };
    let (proof, normalized) =
        prove_qf_bv_unsat_alethe_ext_compare(arena, assertions).expect("emit ext-compare proof");
    let report = carcara_accepts(&bin, tag, arena, &normalized, &proof);
    assert!(report.contains("valid"), "expected 'valid', got:\n{report}");
    assert!(
        !report.contains("holey"),
        "proof must not be holey:\n{report}"
    );
}

#[test]
fn driver_bvugt_eq_conflict_is_accepted_by_carcara() {
    // (bvugt a b) ∧ (= a b) over width-2 — unsat: a > b yet a = b. `bvugt`→`(bvult b a)`.
    let mut arena = TermArena::new();
    let a = bvw(&mut arena, "a", 2);
    let b = bvw(&mut arena, "b", 2);
    let gt = arena.bv_ugt(a, b).unwrap();
    let eq = arena.eq(a, b).unwrap();
    assert_ext_compare_accepted("driver_bvugt", &[gt, eq], &mut arena);
}

#[test]
fn driver_bvule_ult_conflict_is_accepted_by_carcara() {
    // (bvule a b) ∧ (bvult b a) over width-2 — unsat: a ≤ b contradicts b < a.
    // `bvule`→`(not (bvult b a))`.
    let mut arena = TermArena::new();
    let a = bvw(&mut arena, "a", 2);
    let b = bvw(&mut arena, "b", 2);
    let le = arena.bv_ule(a, b).unwrap();
    let lt = arena.bv_ult(b, a).unwrap();
    assert_ext_compare_accepted("driver_bvule", &[le, lt], &mut arena);
}

#[test]
fn driver_bvuge_ult_conflict_is_accepted_by_carcara() {
    // (bvuge a b) ∧ (bvult a b) over width-2 — unsat: a ≥ b contradicts a < b.
    // `bvuge`→`(not (bvult a b))`.
    let mut arena = TermArena::new();
    let a = bvw(&mut arena, "a", 2);
    let b = bvw(&mut arena, "b", 2);
    let ge = arena.bv_uge(a, b).unwrap();
    let lt = arena.bv_ult(a, b).unwrap();
    assert_ext_compare_accepted("driver_bvuge", &[ge, lt], &mut arena);
}

#[test]
fn driver_bvsgt_eq_conflict_is_accepted_by_carcara() {
    // (bvsgt a b) ∧ (= a b) over width-3 — unsat: a >ₛ b yet a = b. `bvsgt`→`(bvslt b a)`.
    let mut arena = TermArena::new();
    let a = bvw(&mut arena, "a", 3);
    let b = bvw(&mut arena, "b", 3);
    let gt = arena.bv_sgt(a, b).unwrap();
    let eq = arena.eq(a, b).unwrap();
    assert_ext_compare_accepted("driver_bvsgt", &[gt, eq], &mut arena);
}

#[test]
fn driver_bvsle_slt_conflict_is_accepted_by_carcara() {
    // (bvsle a b) ∧ (bvslt b a) over width-3 — unsat: a ≤ₛ b contradicts b <ₛ a.
    // `bvsle`→`(not (bvslt b a))`.
    let mut arena = TermArena::new();
    let a = bvw(&mut arena, "a", 3);
    let b = bvw(&mut arena, "b", 3);
    let le = arena.bv_sle(a, b).unwrap();
    let lt = arena.bv_slt(b, a).unwrap();
    assert_ext_compare_accepted("driver_bvsle", &[le, lt], &mut arena);
}

#[test]
fn driver_bvsge_slt_conflict_is_accepted_by_carcara() {
    // (bvsge a b) ∧ (bvslt a b) over width-3 — unsat: a ≥ₛ b contradicts a <ₛ b.
    // `bvsge`→`(not (bvslt a b))`.
    let mut arena = TermArena::new();
    let a = bvw(&mut arena, "a", 3);
    let b = bvw(&mut arena, "b", 3);
    let ge = arena.bv_sge(a, b).unwrap();
    let lt = arena.bv_slt(a, b).unwrap();
    assert_ext_compare_accepted("driver_bvsge", &[ge, lt], &mut arena);
}

// --- QF_ABV select-congruence certificate: ---------------------------------
// `prove_qf_abv_select_congruence_alethe_carcara`
//
// Array equality is ordinary equality, so congruence alone proves
// `a = b => select(a, i) = select(b, i)`. The proof uses SMT-LIB's literal
// `select` head and only `eq_reflexive`, `eq_congruent`, equality symmetry, and
// resolution; no array axiom or reduction premise is needed.

fn select_congruence_conflict(arena: &mut TermArena) -> [TermId; 2] {
    let a = arena.array_var("a", 4, 8).unwrap();
    let b = arena.array_var("b", 4, 8).unwrap();
    let i = bvw(arena, "i", 4);
    let a_eq_b = arena.eq(a, b).unwrap();
    let read_a = arena.select(a, i).unwrap();
    let read_b = arena.select(b, i).unwrap();
    let reads_equal = arena.eq(read_a, read_b).unwrap();
    [a_eq_b, arena.not(reads_equal).unwrap()]
}

fn reversed_select_congruence_conflict(arena: &mut TermArena) -> [TermId; 2] {
    let a = arena.array_var("a", 4, 8).unwrap();
    let b = arena.array_var("b", 4, 8).unwrap();
    let i = bvw(arena, "i", 4);
    let a_eq_b = arena.eq(a, b).unwrap();
    let read_a = arena.select(a, i).unwrap();
    let read_b = arena.select(b, i).unwrap();
    let reads_equal = arena.eq(read_b, read_a).unwrap();
    [a_eq_b, arena.not(reads_equal).unwrap()]
}

const SELECT_CONGRUENCE_SMT2: &str = "\
(set-logic QF_ABV)
(declare-const a (Array (_ BitVec 4) (_ BitVec 8)))
(declare-const b (Array (_ BitVec 4) (_ BitVec 8)))
(declare-const i (_ BitVec 4))
(assert (= a b))
(assert (not (= (select a i) (select b i))))
(check-sat)
";

const REVERSED_SELECT_CONGRUENCE_SMT2: &str = "\
(set-logic QF_ABV)
(declare-const a (Array (_ BitVec 4) (_ BitVec 8)))
(declare-const b (Array (_ BitVec 4) (_ BitVec 8)))
(declare-const i (_ BitVec 4))
(assert (= a b))
(assert (not (= (select b i) (select a i))))
(check-sat)
";

#[test]
fn abv_select_congruence_is_accepted_by_carcara() {
    let Some(bin) = carcara_bin() else {
        eprintln!("[skip] carcara binary not found; build references/carcara to enable");
        return;
    };
    let mut arena = TermArena::new();
    let assertions = select_congruence_conflict(&mut arena);
    let proof = prove_qf_abv_select_congruence_alethe_carcara(&arena, &assertions)
        .expect("emit direct QF_ABV select-congruence certificate");
    let report = carcara_accepts_smt2(
        &bin,
        "abv_select_congruence",
        SELECT_CONGRUENCE_SMT2,
        &proof,
    );
    assert!(report.contains("valid"), "expected 'valid', got:\n{report}");
}

#[test]
fn reversed_abv_select_congruence_is_accepted_by_carcara() {
    let Some(bin) = carcara_bin() else {
        eprintln!("[skip] carcara binary not found; build references/carcara to enable");
        return;
    };
    let mut arena = TermArena::new();
    let assertions = reversed_select_congruence_conflict(&mut arena);
    let proof = prove_qf_abv_select_congruence_alethe_carcara(&arena, &assertions)
        .expect("emit reversed QF_ABV select-congruence certificate");
    let report = carcara_accepts_smt2(
        &bin,
        "abv_select_congruence_reversed",
        REVERSED_SELECT_CONGRUENCE_SMT2,
        &proof,
    );
    assert!(report.contains("valid"), "expected 'valid', got:\n{report}");
}

#[test]
fn abv_select_congruence_without_array_antecedent_is_rejected_by_carcara() {
    let Some(bin) = carcara_bin() else {
        eprintln!("[skip] carcara binary not found; build references/carcara to enable");
        return;
    };
    let mut arena = TermArena::new();
    let assertions = select_congruence_conflict(&mut arena);
    let mut proof = prove_qf_abv_select_congruence_alethe_carcara(&arena, &assertions)
        .expect("emit direct QF_ABV select-congruence certificate");
    let AletheCommand::Step { clause, rule, .. } = &mut proof[3] else {
        panic!("expected eq_congruent step at index 3");
    };
    assert_eq!(rule, "eq_congruent");
    clause.remove(0);

    let report = carcara_output(
        &bin,
        "abv_select_congruence_missing_array_antecedent",
        SELECT_CONGRUENCE_SMT2,
        &proof,
    );
    assert!(
        report.contains("invalid") || report.contains("ERROR"),
        "carcara must reject select congruence without the array antecedent, got:\n{report}"
    );
    assert!(
        !report.lines().any(|line| line.trim() == "valid"),
        "tampered proof must not be reported valid, got:\n{report}"
    );
}

// --- QF_ABV read-over-write-same certificate: -------------------------------
// `prove_qf_abv_row_same_alethe_carcara`
//
// The in-tree `prove_qf_abv_unsat_alethe` discharges a same-index read with the
// axeyum-internal premise-free `read_over_write_same` rule, which only the
// in-tree `check_alethe` accepts (Carcara has NO array theory rule). This
// certificate instead asserts the more primitive read-over-write *rewrite
// instance* `(= (select (store a i v) i) (ite (= i i) v (select a i)))` as a
// `QF_AUFBV` premise and derives the same-index collapse with rules Carcara
// checks in full — `eq_simplify` (`(= i i) → true`), `cong`, `ite_simplify`
// (`ite true v _ → v`), and `trans`. Carcara therefore checks the *collapse
// reasoning* externally; the rewrite instance itself remains an array fact in
// the problem. The matching `.smt2` declares the array `a`, index `i`, value
// `v`, and asserts the `rw` instance plus the refuted disequality.

/// Builds a read-over-write-same disequality `(not (= (select (store a i v) i) v))`
/// over `a : (Array (BitVec 4) (BitVec 8))`, returning the assertion id.
fn row_same_diseq(arena: &mut TermArena) -> TermId {
    let a = arena.array_var("a", 4, 8).unwrap();
    let i = bvw(arena, "i", 4);
    let v = bvw(arena, "v", 8);
    let stored = arena.store(a, i, v).unwrap();
    let sel = arena.select(stored, i).unwrap();
    let eq = arena.eq(sel, v).unwrap();
    arena.not(eq).unwrap()
}

#[test]
fn abv_row_same_collapse_is_accepted_by_carcara() {
    let Some(bin) = carcara_bin() else {
        eprintln!("[skip] carcara binary not found; build references/carcara to enable");
        return;
    };
    let mut arena = TermArena::new();
    let neq = row_same_diseq(&mut arena);
    let (proof, _rw) = prove_qf_abv_row_same_alethe_carcara(&arena, &[neq])
        .expect("emit QF_ABV read-over-write-same Carcara certificate");
    // The `rw` assume renders verbatim as the read-over-write rewrite instance,
    // asserted alongside the refuted disequality in the QF_AUFBV problem.
    let smt2 = "\
(set-logic QF_AUFBV)
(declare-const a (Array (_ BitVec 4) (_ BitVec 8)))
(declare-const i (_ BitVec 4))
(declare-const v (_ BitVec 8))
(assert (= (select (store a i v) i) (ite (= i i) v (select a i))))
(assert (not (= (select (store a i v) i) v)))
(check-sat)
";
    let report = carcara_accepts_smt2(&bin, "abv_row_same_collapse", smt2, &proof);
    assert!(report.contains("valid"), "expected 'valid', got:\n{report}");
}

#[test]
fn abv_row_same_tampered_collapse_is_rejected_by_carcara() {
    let Some(bin) = carcara_bin() else {
        eprintln!("[skip] carcara binary not found; build references/carcara to enable");
        return;
    };
    let mut arena = TermArena::new();
    let neq = row_same_diseq(&mut arena);
    let (mut proof, _rw) = prove_qf_abv_row_same_alethe_carcara(&arena, &[neq])
        .expect("emit QF_ABV read-over-write-same Carcara certificate");
    // Tamper the `ite_simplify` step (s3) to claim `ite true v (select a i) → (select a i)`
    // instead of `→ v`. The conclusion is no longer the genuine simplification, so a
    // sound checker MUST reject — no fabricated certificate slips through.
    let AletheCommand::Step { clause, .. } = &mut proof[4] else {
        panic!("expected step at index 4 (s3 ite_simplify)");
    };
    let AletheLit { atom, .. } = &mut clause[0];
    let AletheTerm::App(_, eq_args) = atom else {
        panic!("expected (= … …) atom in s3");
    };
    // RHS of s3 is `v`; swap it for the else-branch `(select a i)` (a wrong fold).
    let AletheTerm::App(_, ite_args) = &eq_args[0] else {
        panic!("expected (ite …) on the LHS of s3");
    };
    let bogus_rhs = ite_args[2].clone();
    eq_args[1] = bogus_rhs;
    let smt2 = "\
(set-logic QF_AUFBV)
(declare-const a (Array (_ BitVec 4) (_ BitVec 8)))
(declare-const i (_ BitVec 4))
(declare-const v (_ BitVec 8))
(assert (= (select (store a i v) i) (ite (= i i) v (select a i))))
(assert (not (= (select (store a i v) i) v)))
(check-sat)
";
    let report = carcara_output(&bin, "abv_row_same_tampered", smt2, &proof);
    assert!(
        report.contains("invalid") || report.contains("ERROR"),
        "carcara must reject the tampered ite_simplify step, got:\n{report}"
    );
    assert!(
        !report.lines().any(|l| l.trim() == "valid"),
        "tampered proof must not be reported valid, got:\n{report}"
    );
}

// `prove_qf_abv_row_diff_alethe_carcara`
//
// The diff-index (`i ≠ j`) counterpart of the same-index certificate above. The
// general select-of-store rewrite `select(store(a, i, e), j) → ite(i = j, e,
// select(a, j))` has two branches; the same-index test certifies `i = j ⇒ ite →
// e`, this one certifies `i ≠ j ⇒ ite → select(a, j)`. The `.smt2` asserts the
// read-over-write rewrite *instance* (the trusted residual) plus the refuted
// disequality `select(store(a, i, e), j) ≠ select(a, j)`; the proof folds the
// `ite` with `evaluate` (`(= i j) → false` for distinct constant indices), `cong`,
// `ite_simplify` (`ite false e _ → _`), and `trans` — all Carcara-checked. The
// indices are distinct *constants* (`#b0001`, `#b0010`) because `(= i j) → false`
// is only Carcara-derivable for concrete indices (no `*_simplify` folds a symbolic
// equality to `false`).

/// Builds a read-over-write-*diff* disequality
/// `(not (= (select (store a #b0001 e) #b0010) (select a #b0010)))` over
/// `a : (Array (BitVec 4) (BitVec 8))`, returning the assertion id.
fn row_diff_diseq(arena: &mut TermArena) -> TermId {
    let a = arena.array_var("a", 4, 8).unwrap();
    let i = arena.bv_const(4, 1).unwrap();
    let j = arena.bv_const(4, 2).unwrap();
    let e = bvw(arena, "e", 8);
    let stored = arena.store(a, i, e).unwrap();
    let sel_store = arena.select(stored, j).unwrap();
    let sel_a = arena.select(a, j).unwrap();
    let eq = arena.eq(sel_store, sel_a).unwrap();
    arena.not(eq).unwrap()
}

/// The `.smt2` problem matching [`row_diff_diseq`]: declares `a`, `e`, and asserts
/// the read-over-write rewrite instance plus the refuted diff disequality.
const ROW_DIFF_SMT2: &str = "\
(set-logic QF_AUFBV)
(declare-const a (Array (_ BitVec 4) (_ BitVec 8)))
(declare-const e (_ BitVec 8))
(assert (= (select (store a #b0001 e) #b0010) (ite (= #b0001 #b0010) e (select a #b0010))))
(assert (not (= (select (store a #b0001 e) #b0010) (select a #b0010))))
(check-sat)
";

#[test]
fn abv_row_diff_collapse_is_accepted_by_carcara() {
    let Some(bin) = carcara_bin() else {
        eprintln!("[skip] carcara binary not found; build references/carcara to enable");
        return;
    };
    let mut arena = TermArena::new();
    let neq = row_diff_diseq(&mut arena);
    let (proof, _rw) = prove_qf_abv_row_diff_alethe_carcara(&arena, &[neq])
        .expect("emit QF_ABV read-over-write-diff Carcara certificate");
    let report = carcara_accepts_smt2(&bin, "abv_row_diff_collapse", ROW_DIFF_SMT2, &proof);
    assert!(report.contains("valid"), "expected 'valid', got:\n{report}");
}

#[test]
fn abv_row_diff_tampered_collapse_is_rejected_by_carcara() {
    let Some(bin) = carcara_bin() else {
        eprintln!("[skip] carcara binary not found; build references/carcara to enable");
        return;
    };
    let mut arena = TermArena::new();
    let neq = row_diff_diseq(&mut arena);
    let (mut proof, _rw) = prove_qf_abv_row_diff_alethe_carcara(&arena, &[neq])
        .expect("emit QF_ABV read-over-write-diff Carcara certificate");
    // Tamper the `ite_simplify` step (s3) to claim `ite false e (select a j) → e`
    // (the then-branch) instead of `→ (select a j)` (the else-branch). The fold is
    // wrong, so a sound checker MUST reject — no fabricated certificate slips through.
    let AletheCommand::Step { clause, .. } = &mut proof[4] else {
        panic!("expected step at index 4 (s3 ite_simplify)");
    };
    let AletheLit { atom, .. } = &mut clause[0];
    let AletheTerm::App(_, eq_args) = atom else {
        panic!("expected (= … …) atom in s3");
    };
    // RHS of s3 is `(select a j)` (the else-branch); swap it for the then-branch `e`.
    let AletheTerm::App(_, ite_args) = &eq_args[0] else {
        panic!("expected (ite …) on the LHS of s3");
    };
    let bogus_rhs = ite_args[1].clone();
    eq_args[1] = bogus_rhs;
    let report = carcara_output(&bin, "abv_row_diff_tampered", ROW_DIFF_SMT2, &proof);
    assert!(
        report.contains("invalid") || report.contains("ERROR"),
        "carcara must reject the tampered ite_simplify step, got:\n{report}"
    );
    assert!(
        !report.lines().any(|l| l.trim() == "valid"),
        "tampered proof must not be reported valid, got:\n{report}"
    );
}

// --- Certified conjunctive QF_LRA Craig interpolant (lra_interpolant_certified) ---
//
// The interpolant `I` carries two Farkas certificates — `la_generic` refutations
// of `A ∧ ¬I` (Craig condition 1) and `I ∧ B` (condition 2). Each is handed to
// the REAL Carcara binary on the matching `.smt2` conjunction; Carcara accepting
// both (valid && !holey) is the external check that upgrades the interpolant from
// Validated to Checked.

#[test]
fn certified_lra_interpolant_both_farkas_certs_accepted_by_carcara() {
    let Some(bin) = carcara_bin() else {
        eprintln!("[skip] carcara binary not found; build references/carcara to enable");
        return;
    };
    // A: x ≤ 0 ; B: x ≥ 1.  Unsat; shared variable x. The interpolant is a single
    // inequality, so both `A ∧ ¬I` and `I ∧ B` are conjunctive (Farkas-refutable).
    let mut arena = TermArena::new();
    let x = arena.real_var("x").unwrap();
    let zero = real_int(&mut arena, 0);
    let one = real_int(&mut arena, 1);
    let a0 = arena.real_le(x, zero).unwrap();
    let b0 = arena.real_ge(x, one).unwrap();

    let cert = lra_interpolant_certified(&mut arena, &[a0], &[b0])
        .expect("decides")
        .expect("a certified interpolant exists");

    // Condition 1: Carcara accepts the A ∧ ¬I refutation.
    let report_a = carcara_accepts(
        &bin,
        "interp_a_not_i",
        &arena,
        &cert.a_and_not_i,
        &cert.a_refutation,
    );
    assert!(
        report_a.contains("valid"),
        "expected Carcara 'valid' on A ∧ ¬I, got:\n{report_a}"
    );
    // Condition 2: Carcara accepts the I ∧ B refutation.
    let report_b = carcara_accepts(
        &bin,
        "interp_i_b",
        &arena,
        &cert.i_and_b,
        &cert.b_refutation,
    );
    assert!(
        report_b.contains("valid"),
        "expected Carcara 'valid' on I ∧ B, got:\n{report_b}"
    );
}

#[test]
fn certified_lra_interpolant_rational_certs_accepted_by_carcara() {
    let Some(bin) = carcara_bin() else {
        eprintln!("[skip] carcara binary not found; build references/carcara to enable");
        return;
    };
    // A: 3x ≤ 1 ; B: 2x ≥ 3 — rational Farkas combination in the interpolant.
    let mut arena = TermArena::new();
    let x = arena.real_var("x").unwrap();
    let one = real_int(&mut arena, 1);
    let three = real_int(&mut arena, 3);
    let two = real_int(&mut arena, 2);
    let three_x = arena.real_mul(three, x).unwrap();
    let two_x = arena.real_mul(two, x).unwrap();
    let a0 = arena.real_le(three_x, one).unwrap();
    let b0 = arena.real_ge(two_x, three).unwrap();

    let cert = lra_interpolant_certified(&mut arena, &[a0], &[b0])
        .expect("decides")
        .expect("a certified interpolant exists");
    let report_a = carcara_accepts(
        &bin,
        "interp_rat_a",
        &arena,
        &cert.a_and_not_i,
        &cert.a_refutation,
    );
    assert!(report_a.contains("valid"), "A-side: {report_a}");
    let report_b = carcara_accepts(
        &bin,
        "interp_rat_b",
        &arena,
        &cert.i_and_b,
        &cert.b_refutation,
    );
    assert!(report_b.contains("valid"), "B-side: {report_b}");
}

/// TAMPER: corrupt the Farkas `:args` coefficient inside a certified interpolant's
/// refutation and confirm Carcara REJECTS it. This proves the external check has
/// teeth — a wrong certificate cannot pass (a bug surfaces as a rejection, never an
/// unsound accept).
#[test]
fn tampered_certified_lra_interpolant_cert_is_rejected_by_carcara() {
    use axeyum_cnf::{AletheCommand, AletheTerm};
    let Some(bin) = carcara_bin() else {
        eprintln!("[skip] carcara binary not found; build references/carcara to enable");
        return;
    };
    let mut arena = TermArena::new();
    let x = arena.real_var("x").unwrap();
    let zero = real_int(&mut arena, 0);
    let one = real_int(&mut arena, 1);
    let a0 = arena.real_le(x, zero).unwrap();
    let b0 = arena.real_ge(x, one).unwrap();
    let cert = lra_interpolant_certified(&mut arena, &[a0], &[b0])
        .expect("decides")
        .expect("a certified interpolant exists");

    // Tamper the A ∧ ¬I refutation: replace the la_generic Farkas `:args` with
    // bogus zero coefficients (which do NOT refute the conjunction), so Carcara's
    // own re-derivation from the coefficients fails.
    let mut tampered = cert.a_refutation.clone();
    let mut patched = false;
    for cmd in &mut tampered {
        if let AletheCommand::Step { rule, args, .. } = cmd
            && rule == "la_generic"
        {
            for a in args.iter_mut() {
                *a = AletheTerm::Const("0".to_owned());
            }
            patched = true;
        }
    }
    assert!(patched, "expected a la_generic step to tamper");

    let report = carcara_output(
        &bin,
        "interp_tampered",
        &write_script(&arena, &cert.a_and_not_i),
        &tampered,
    );
    assert!(
        !report.lines().any(|l| l.trim() == "valid"),
        "a tampered Farkas certificate must NOT be reported valid, got:\n{report}"
    );
    assert!(
        report.contains("invalid") || report.contains("ERROR") || report.contains("holey"),
        "Carcara must reject the tampered certificate, got:\n{report}"
    );
}

// --- Certified conjunctive QF_UF (EUF) Craig interpolant (qf_uf_interpolant_certified) ---
//
// The EUF interpolant `I` carries two congruence certificates — `eq_congruent` /
// `eq_transitive` / `resolution` refutations of `A ∧ ¬I` (Craig condition 1) and
// `I ∧ B` (condition 2). Each is handed to the REAL Carcara binary on the matching
// `.smt2` conjunction; Carcara accepting both (valid && !holey) is the external
// check that upgrades the EUF interpolant from Validated to Checked.

#[test]
fn certified_euf_interpolant_both_congruence_certs_accepted_by_carcara() {
    let Some(bin) = carcara_bin() else {
        eprintln!("[skip] carcara binary not found; build references/carcara to enable");
        return;
    };
    // A: a=b, b=c ; B: a≠c.  Unsat; shared terms a, c. I = (a=c), a positive
    // equality conjunction, so A ∧ ¬I and I ∧ B are each single-disequality
    // congruence conflicts (EUF-refutable).
    let mut arena = TermArena::new();
    let a = var(&mut arena, "a");
    let b = var(&mut arena, "b");
    let c = var(&mut arena, "c");
    let ab = arena.eq(a, b).unwrap();
    let bc = arena.eq(b, c).unwrap();
    let ac = arena.eq(a, c).unwrap();
    let nac = arena.not(ac).unwrap();

    let cert = qf_uf_interpolant_certified(&mut arena, &[ab, bc], &[nac])
        .expect("decides")
        .expect("a certified EUF interpolant exists");

    // Condition 1: Carcara accepts the A ∧ ¬I congruence refutation.
    let report_a = carcara_accepts(
        &bin,
        "euf_interp_a_not_i",
        &arena,
        &cert.a_and_not_i,
        &cert.a_refutation,
    );
    assert!(
        report_a.contains("valid"),
        "expected Carcara 'valid' on A ∧ ¬I, got:\n{report_a}"
    );
    // Condition 2: Carcara accepts the I ∧ B congruence refutation.
    let report_b = carcara_accepts(
        &bin,
        "euf_interp_i_b",
        &arena,
        &cert.i_and_b,
        &cert.b_refutation,
    );
    assert!(
        report_b.contains("valid"),
        "expected Carcara 'valid' on I ∧ B, got:\n{report_b}"
    );
}

#[test]
fn certified_euf_interpolant_congruence_certs_accepted_by_carcara() {
    let Some(bin) = carcara_bin() else {
        eprintln!("[skip] carcara binary not found; build references/carcara to enable");
        return;
    };
    // A: a=b ; B: f(a)≠f(b).  I = (f(a)=f(b)) over shared f(a), f(b). Both Craig
    // conjunctions are congruence conflicts.
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

    let cert = qf_uf_interpolant_certified(&mut arena, &[ab], &[nfafb])
        .expect("decides")
        .expect("a certified EUF interpolant exists");
    let report_a = carcara_accepts(
        &bin,
        "euf_interp_cong_a",
        &arena,
        &cert.a_and_not_i,
        &cert.a_refutation,
    );
    assert!(report_a.contains("valid"), "A-side: {report_a}");
    let report_b = carcara_accepts(
        &bin,
        "euf_interp_cong_b",
        &arena,
        &cert.i_and_b,
        &cert.b_refutation,
    );
    assert!(report_b.contains("valid"), "B-side: {report_b}");
}

/// TAMPER: corrupt a congruence step inside a certified EUF interpolant's refutation
/// and confirm Carcara REJECTS it. This proves the external check has teeth — a wrong
/// certificate cannot pass (a bug surfaces as a rejection, never an unsound accept).
#[test]
fn tampered_certified_euf_interpolant_cert_is_rejected_by_carcara() {
    let Some(bin) = carcara_bin() else {
        eprintln!("[skip] carcara binary not found; build references/carcara to enable");
        return;
    };
    let mut arena = TermArena::new();
    let a = var(&mut arena, "a");
    let b = var(&mut arena, "b");
    let c = var(&mut arena, "c");
    let ab = arena.eq(a, b).unwrap();
    let bc = arena.eq(b, c).unwrap();
    let ac = arena.eq(a, c).unwrap();
    let nac = arena.not(ac).unwrap();
    let cert = qf_uf_interpolant_certified(&mut arena, &[ab, bc], &[nac])
        .expect("decides")
        .expect("a certified EUF interpolant exists");

    // Tamper the A ∧ ¬I refutation: rewrite a derived (non-`assume`) step's clause
    // to a bogus reflexive equality `(= a a)` its premises do not entail, so Carcara
    // rejects the congruence chain.
    let mut tampered = cert.a_refutation.clone();
    let mut patched = false;
    for cmd in &mut tampered {
        if let AletheCommand::Step { clause, .. } = cmd
            && !clause.is_empty()
        {
            let bogus = AletheTerm::App(
                "=".to_owned(),
                vec![
                    AletheTerm::Const("a".to_owned()),
                    AletheTerm::Const("a".to_owned()),
                ],
            );
            *clause = vec![AletheLit {
                atom: bogus,
                negated: false,
            }];
            patched = true;
            break;
        }
    }
    assert!(patched, "expected a derivable step to tamper");

    let report = carcara_output(
        &bin,
        "euf_interp_tampered",
        &write_script(&arena, &cert.a_and_not_i),
        &tampered,
    );
    assert!(
        !report.lines().any(|l| l.trim() == "valid"),
        "a tampered EUF congruence certificate must NOT be reported valid, got:\n{report}"
    );
    assert!(
        report.contains("invalid") || report.contains("ERROR") || report.contains("holey"),
        "Carcara must reject the tampered EUF certificate, got:\n{report}"
    );
}

// --- Certified single-predicate QF_BV Craig interpolant (qf_bv_interpolant_certified) ---
//
// The interpolant `I` carries two bit-blast refutations — Alethe `bitblast_*` +
// `resolution` proofs of `A ∧ ¬I` (Craig condition 1) and `I ∧ B` (condition 2).
// Each is handed to the REAL Carcara binary on the matching `.smt2` conjunction;
// Carcara accepting both (valid && !holey) is the external check that upgrades the
// single-predicate QF_BV interpolant from Validated to Checked. A compound (tree)
// interpolant is out of the emitter's flat-predicate fragment and stays Validated.

/// Declares an 8-bit bit-vector symbol and returns its variable term.
fn bv8(arena: &mut TermArena, name: &str) -> TermId {
    let s = arena.declare(name, Sort::BitVec(8)).expect("declare");
    arena.var(s)
}

#[test]
fn certified_qf_bv_interpolant_both_bitblast_certs_accepted_by_carcara() {
    let Some(bin) = carcara_bin() else {
        eprintln!("[skip] carcara binary not found; build references/carcara to enable");
        return;
    };
    // A: x = y ; B: x ≠ y.  Unsat; shared terms x, y. The interpolant is the single
    // predicate I = (x = y), so both `A ∧ ¬I` (= x=y, x≠y) and `I ∧ B` (= x=y, x≠y)
    // are in the Carcara-checked flat-predicate bit-blast fragment.
    let mut arena = TermArena::new();
    let x = bv8(&mut arena, "x");
    let y = bv8(&mut arena, "y");
    let a0 = arena.eq(x, y).unwrap();
    let e = arena.eq(x, y).unwrap();
    let b0 = arena.not(e).unwrap();

    let cert = qf_bv_interpolant_certified(&mut arena, &[a0], &[b0])
        .expect("decides")
        .expect("a certified QF_BV interpolant exists");

    // Condition 1: Carcara accepts the A ∧ ¬I bit-blast refutation.
    let report_a = carcara_accepts(
        &bin,
        "bv_interp_a_not_i",
        &arena,
        &cert.a_and_not_i,
        &cert.a_refutation,
    );
    assert!(
        report_a.contains("valid"),
        "expected Carcara 'valid' on A ∧ ¬I, got:\n{report_a}"
    );
    // Condition 2: Carcara accepts the I ∧ B bit-blast refutation.
    let report_b = carcara_accepts(
        &bin,
        "bv_interp_i_b",
        &arena,
        &cert.i_and_b,
        &cert.b_refutation,
    );
    assert!(
        report_b.contains("valid"),
        "expected Carcara 'valid' on I ∧ B, got:\n{report_b}"
    );
}

/// A compound (Boolean-tree) interpolant — `A: x=0`, `B: x=1`, lifted to an `and` of
/// `extract`-predicates — is outside the Carcara-checked emitter's flat-predicate
/// fragment, so the certified path declines (`Ok(None)`) and stays `Validated`. (No
/// Carcara invocation: this is the honest emittable-only boundary.)
#[test]
fn compound_qf_bv_interpolant_declines_certification() {
    let mut arena = TermArena::new();
    let x = bv8(&mut arena, "x");
    let zero = arena.bv_const(8, 0).unwrap();
    let one = arena.bv_const(8, 1).unwrap();
    let a0 = arena.eq(x, zero).unwrap();
    let b0 = arena.eq(x, one).unwrap();
    assert!(
        qf_bv_interpolant_certified(&mut arena, &[a0], &[b0])
            .expect("decides")
            .is_none(),
        "a compound (tree) QF_BV interpolant must decline certification"
    );
}

/// TAMPER: corrupt a derived (non-`assume`) step's clause inside a certified `QF_BV`
/// interpolant's refutation and confirm Carcara REJECTS it. This proves the external
/// check has teeth — a wrong certificate cannot pass (a bug surfaces as a rejection,
/// never an unsound accept).
#[test]
fn tampered_certified_qf_bv_interpolant_cert_is_rejected_by_carcara() {
    let Some(bin) = carcara_bin() else {
        eprintln!("[skip] carcara binary not found; build references/carcara to enable");
        return;
    };
    let mut arena = TermArena::new();
    let x = bv8(&mut arena, "x");
    let y = bv8(&mut arena, "y");
    let a0 = arena.eq(x, y).unwrap();
    let e = arena.eq(x, y).unwrap();
    let b0 = arena.not(e).unwrap();
    let cert = qf_bv_interpolant_certified(&mut arena, &[a0], &[b0])
        .expect("decides")
        .expect("a certified QF_BV interpolant exists");

    // Tamper the A ∧ ¬I refutation: rewrite the LAST derived (non-`assume`) step's
    // clause to a bogus non-empty conclusion `(= x x)` its premises do not entail, so
    // Carcara's resolution chain to the empty clause breaks.
    let mut tampered = cert.a_refutation.clone();
    let mut patched = false;
    for cmd in tampered.iter_mut().rev() {
        if let AletheCommand::Step { clause, .. } = cmd {
            let bogus = AletheTerm::App(
                "=".to_owned(),
                vec![
                    AletheTerm::Const("x".to_owned()),
                    AletheTerm::Const("x".to_owned()),
                ],
            );
            *clause = vec![AletheLit {
                atom: bogus,
                negated: false,
            }];
            patched = true;
            break;
        }
    }
    assert!(patched, "expected a derivable step to tamper");

    let report = carcara_output(
        &bin,
        "bv_interp_tampered",
        &write_script(&arena, &cert.a_and_not_i),
        &tampered,
    );
    assert!(
        !report.lines().any(|l| l.trim() == "valid"),
        "a tampered QF_BV bit-blast certificate must NOT be reported valid, got:\n{report}"
    );
    assert!(
        report.contains("invalid") || report.contains("ERROR") || report.contains("holey"),
        "Carcara must reject the tampered QF_BV certificate, got:\n{report}"
    );
}

// --- Certified conjunctive QF_UFLRA Craig interpolant (uflra_interpolant_certified) ---
//
// The QF_UFLRA interpolant `I` carries two `la_generic` refutations — of `A ∧ ¬I`
// (Craig condition 1) and `I ∧ B` (condition 2) — each treating every
// uninterpreted-function application as an OPAQUE real (the certifiable interpolant
// is always congruence-free). Each is handed to the REAL Carcara binary on the
// matching INLINED `.smt2` conjunction (no `define-fun` hoisting, so `(f c)` renders
// verbatim); Carcara accepting both (valid && !holey) is the external check that
// upgrades the QF_UFLRA interpolant from Validated to Checked.

fn real_int_t(arena: &mut TermArena, v: i128) -> TermId {
    arena.real_const(Rational::integer(v))
}

#[test]
fn certified_uflra_interpolant_both_opaque_certs_accepted_by_carcara() {
    let Some(bin) = carcara_bin() else {
        eprintln!("[skip] carcara binary not found; build references/carcara to enable");
        return;
    };
    // A: f(c) >= 5 ; B: f(c) <= 3. Shared opaque f(c); no congruence needed.
    let mut arena = TermArena::new();
    let f = arena.declare_fun("f", &[Sort::Real], Sort::Real).unwrap();
    let c = arena.real_var("c").unwrap();
    let fc = arena.apply(f, &[c]).unwrap();
    let five = real_int_t(&mut arena, 5);
    let three = real_int_t(&mut arena, 3);
    let a0 = arena.real_ge(fc, five).unwrap();
    let b0 = arena.real_le(fc, three).unwrap();

    let cert = uflra_interpolant_certified(&mut arena, &[a0], &[b0])
        .expect("decides")
        .expect("a certified QF_UFLRA interpolant exists");

    // Condition 1: Carcara accepts the A ∧ ¬I refutation.
    let report_a = carcara_accepts_smt2(
        &bin,
        "uflra_interp_a_not_i",
        &inlined_uflra_smt2(&arena, &cert.a_and_not_i),
        &cert.a_refutation,
    );
    assert!(
        report_a.contains("valid"),
        "expected Carcara 'valid' on A ∧ ¬I, got:\n{report_a}"
    );
    // Condition 2: Carcara accepts the I ∧ B refutation.
    let report_b = carcara_accepts_smt2(
        &bin,
        "uflra_interp_i_b",
        &inlined_uflra_smt2(&arena, &cert.i_and_b),
        &cert.b_refutation,
    );
    assert!(
        report_b.contains("valid"),
        "expected Carcara 'valid' on I ∧ B, got:\n{report_b}"
    );
}

#[test]
fn certified_uflra_interpolant_app_plus_arithmetic_accepted_by_carcara() {
    let Some(bin) = carcara_bin() else {
        eprintln!("[skip] carcara binary not found; build references/carcara to enable");
        return;
    };
    // A: f(c) >= x ∧ x >= 5 ; B: f(c) <= 3. The interpolant is over the shared
    // opaque f(c); x is A-local.
    let mut arena = TermArena::new();
    let f = arena.declare_fun("f", &[Sort::Real], Sort::Real).unwrap();
    let c = arena.real_var("c").unwrap();
    let fc = arena.apply(f, &[c]).unwrap();
    let x = arena.real_var("x").unwrap();
    let five = real_int_t(&mut arena, 5);
    let three = real_int_t(&mut arena, 3);
    let a0 = arena.real_ge(fc, x).unwrap();
    let a1 = arena.real_ge(x, five).unwrap();
    let b0 = arena.real_le(fc, three).unwrap();

    let cert = uflra_interpolant_certified(&mut arena, &[a0, a1], &[b0])
        .expect("decides")
        .expect("a certified QF_UFLRA interpolant exists");
    let report_a = carcara_accepts_smt2(
        &bin,
        "uflra_interp_arith_a",
        &inlined_uflra_smt2(&arena, &cert.a_and_not_i),
        &cert.a_refutation,
    );
    assert!(report_a.contains("valid"), "A-side: {report_a}");
    let report_b = carcara_accepts_smt2(
        &bin,
        "uflra_interp_arith_b",
        &inlined_uflra_smt2(&arena, &cert.i_and_b),
        &cert.b_refutation,
    );
    assert!(report_b.contains("valid"), "B-side: {report_b}");
}

/// TAMPER: corrupt the `la_generic` Farkas `:args` inside a certified `QF_UFLRA`
/// interpolant's refutation and confirm Carcara REJECTS it. This proves the external
/// check has teeth — a wrong certificate cannot pass (a bug surfaces as a rejection,
/// never an unsound accept).
#[test]
fn tampered_certified_uflra_interpolant_cert_is_rejected_by_carcara() {
    let Some(bin) = carcara_bin() else {
        eprintln!("[skip] carcara binary not found; build references/carcara to enable");
        return;
    };
    let mut arena = TermArena::new();
    let f = arena.declare_fun("f", &[Sort::Real], Sort::Real).unwrap();
    let c = arena.real_var("c").unwrap();
    let fc = arena.apply(f, &[c]).unwrap();
    let five = real_int_t(&mut arena, 5);
    let three = real_int_t(&mut arena, 3);
    let a0 = arena.real_ge(fc, five).unwrap();
    let b0 = arena.real_le(fc, three).unwrap();
    let cert = uflra_interpolant_certified(&mut arena, &[a0], &[b0])
        .expect("decides")
        .expect("a certified QF_UFLRA interpolant exists");

    // Tamper the A ∧ ¬I refutation: replace the la_generic Farkas `:args` with bogus
    // zero coefficients (which do NOT refute the conjunction).
    let mut tampered = cert.a_refutation.clone();
    let mut patched = false;
    for cmd in &mut tampered {
        if let AletheCommand::Step { rule, args, .. } = cmd
            && rule == "la_generic"
        {
            for a in args.iter_mut() {
                *a = AletheTerm::Const("0".to_owned());
            }
            patched = true;
        }
    }
    assert!(patched, "expected a la_generic step to tamper");

    let report = carcara_output(
        &bin,
        "uflra_interp_tampered",
        &inlined_uflra_smt2(&arena, &cert.a_and_not_i),
        &tampered,
    );
    assert!(
        !report.lines().any(|l| l.trim() == "valid"),
        "a tampered Farkas certificate must NOT be reported valid, got:\n{report}"
    );
    assert!(
        report.contains("invalid") || report.contains("ERROR") || report.contains("holey"),
        "Carcara must reject the tampered certificate, got:\n{report}"
    );
}
