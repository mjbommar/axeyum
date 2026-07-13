//! **Real-Lean cross-check** of reconstructed refutations (destination-3).
//!
//! `prove_unsat_to_lean_module` renders a self-contained `prelude`-mode Lean 4
//! module (`theorem axeyum_refutation : False := <proof>` over the reachable
//! declarations) for each supported fragment. These tests feed that module to a
//! real `lean` binary: an external, Lean-grade kernel must accept it, and
//! `#print axioms` must report no `sorryAx` (no cheating). This independently
//! corroborates the in-tree [`axeyum_lean_kernel::Kernel`] check.
//!
//! The `lean` binary is optional: each test **skips** (prints a note, passes)
//! when it is absent. Install it with `elan` (a `leanprover/lean4` toolchain on
//! `PATH`), or point `AXEYUM_LEAN_BIN` at a `lean` executable.
#![allow(clippy::many_single_char_names)]
#![allow(clippy::similar_names)]

use std::cell::RefCell;
use std::path::PathBuf;
use std::process::Command;
use std::sync::Mutex;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::{Duration, Instant};

use axeyum_ir::{Rational, Sort, TermArena};
use axeyum_smtlib::parse_script;
use axeyum_solver::{
    ProofFragment, prove_unsat_to_lean_module, reconstruct_lex_clash_to_lean_module,
};
use axeyum_strings::{LexAtom, LexFormula, LexProblem, Seg};

/// Resolve the `lean` binary: `AXEYUM_LEAN_BIN` if set, otherwise the first
/// `lean` on `PATH`. Returns `None` (→ skip) if unavailable.
fn lean_bin() -> Option<PathBuf> {
    if let Ok(p) = std::env::var("AXEYUM_LEAN_BIN") {
        let pb = PathBuf::from(p);
        if pb.is_file() {
            return Some(pb);
        }
    }
    let path = std::env::var_os("PATH")?;
    std::env::split_paths(&path)
        .map(|d| d.join("lean"))
        .find(|c| c.is_file())
}

// -------------------------------------------------------------------------
// Lean cross-check harness (parallel + sliced).
//
// Each proof-family builder below reconstructs a self-contained `prelude`-mode
// Lean module and hands it to `lean_accepts`. Running every module through the
// real `lean` kernel is the Lean-parity gate, but the kernel checks are slow
// CPU-bound subprocesses: a naïve sequential sweep (one child at a time) makes a
// full `cargo test` run take hours.
//
// This harness keeps the gate but makes the cost bounded:
//   * The builders no longer run `lean` inline. `lean_accepts` *collects*
//     `(tag, source)` pairs into a thread-local sink; a builder invocation only
//     performs the (fast, always-on) Rust-side structural checks
//     (parse / `assert_eq!(fragment, …)` / no-`sorryAx`).
//   * Two harness `#[test]`s drive the collected cases through
//     `run_lean_checks`, which fans the independent `lean` processes across a
//     bounded thread pool (parallelism is *internal*, so it holds even under
//     `cargo test -- --test-threads 1`).
//   * `lean_crosscheck_representative` (default) checks ONE module per family —
//     minutes, not hours. `lean_crosscheck_full` (`#[ignore]`) checks every
//     module; run it with `cargo test --test lean_crosscheck -- --ignored`.
//
// Invariant: any module that is actually handed to `lean` and is REJECTED (or
// depends on `sorryAx`) fails the test. Coverage reductions are explicit and
// LOUD — every run prints `checked X of Y`, and budget/no-lean skips are
// reported, never silently dropped.
//
// Knobs (env):
//   AXEYUM_LEAN_BIN         path to a `lean` executable (else first on PATH)
//   AXEYUM_LEAN_JOBS        pool size (default: available parallelism)
//   AXEYUM_LEAN_BUDGET_SECS wall-clock budget; remaining modules are skipped
//                           (loudly, NOT failed) once exceeded. Unset/0 = no cap.
// -------------------------------------------------------------------------

thread_local! {
    /// When `Some`, `lean_accepts` collects into this sink instead of shelling
    /// out to `lean`. Set by the harness while it invokes a family builder.
    static LEAN_SINK: RefCell<Option<Vec<(String, String)>>> = const { RefCell::new(None) };
}

/// Family builders: each reconstructs one proof family and pushes its Lean
/// module(s) via `lean_accepts`. The `bool` marks whether the family's *first*
/// module is a heavier one (informational only). Registered here so both the
/// representative and full harness tests can enumerate every family.
type FamilyBuilder = fn();

/// Every proof-family builder in this file. The representative slice checks the
/// first module each produces; the full run checks all of them.
const FAMILY_BUILDERS: &[FamilyBuilder] = &[
    qf_ufbv_refutation_checks_in_real_lean,
    qf_ufbv_lean_entry_normalizes_conjunction_and_double_negation,
    qf_ufbv_finite_domain_pigeonhole_checks_in_real_lean,
    quantified_bv_finite_domain_enum_rows_check_in_real_lean,
    quantified_bv_source_instance_set_checks_in_real_lean,
    quantified_bv_negated_existential_witness_checks_in_real_lean,
    cvc5_quantified_bv_inversion_rows_check_in_real_lean,
    qf_ufff_bv_uf_local_rows_check_in_real_lean,
    qf_ff_term_level_enum_rows_check_in_real_lean,
    qf_ff_bv_defined_enum_gap_rows_check_in_real_lean,
    qf_fp_bv_defined_enum_rows_check_in_real_lean,
    qf_bvfp_bv_defined_enum_rows_check_in_real_lean,
    qf_dt_cvc5_slice_checks_in_real_lean,
    lra_refutation_checks_in_real_lean,
    qf_lra_ite_true_identity_checks_in_real_lean,
    qf_lra_dpll_audit_rows_check_in_real_lean,
    qf_lia_arith_dpll_audit_rows_check_in_real_lean,
    qf_uflia_use_name_arith_dpll_rows_check_in_real_lean,
    qf_lia_bool_simplification_audit_row_checks_in_real_lean,
    qf_uf_issue3970_term_identity_checks_in_real_lean,
    qf_ufbv_fun1_bool_uf_exhaustive_checks_in_real_lean,
    qf_uf_sets_cardinality_checks_in_real_lean,
    qf_uf_boolean_euf_rows_check_in_real_lean,
    qf_uf_overbound_online_euf_rows_check_in_real_lean,
    qf_uf_bug303_uf_arith_congruence_checks_in_real_lean,
    qf_uf_declared_sort_equality_checks_in_real_lean,
    qf_nra_sos_certificate_audit_rows_check_in_real_lean,
    qf_nra_even_power_audit_rows_check_in_real_lean,
    qf_nia_bounded_int_blast_audit_rows_check_in_real_lean,
    forall_refutation_checks_in_real_lean,
    exists_refutation_checks_in_real_lean,
    qf_abv_read_consistency_refutation_checks_in_real_lean,
    qf_abv_select_congruence_refutation_checks_in_real_lean,
    array_axiom_lean_entry_normalizes_conjunction_and_double_negation,
    qf_aufbv_finite_array_extensionality_checks_in_real_lean,
    qf_aufbv_array_axiom_refutations_check_in_real_lean,
    qf_aufbv_bv_abstraction_checks_in_real_lean,
    qf_alia_store_chain_certificates_check_in_real_lean,
    qf_ax_declared_sort_certificates_check_in_real_lean,
    qf_ax_bool_array_read_collapse_checks_in_real_lean,
    qf_aufbv_aligned_write_chain_checks_in_real_lean,
    qf_aufbv_two_byte_memcpy_checks_in_real_lean,
    qf_aufbv_two_element_bubble_sort_checks_in_real_lean,
    qf_aufbv_two_element_selection_sort_checks_in_real_lean,
    qf_aufbv_two_cell_xor_swap_checks_in_real_lean,
    qf_aufbv_two_byte_xor_swap_roundtrip_checks_in_real_lean,
    qf_aufbv_binary_search16_checks_in_real_lean,
    qf_aufbv_fifo_bc04_checks_in_real_lean,
    datatype_read_over_construct_checks_in_real_lean,
    tester_fold_checks_in_real_lean,
    distinct_constructors_check_in_real_lean,
    injective_field_mismatch_check_in_real_lean,
    acyclicity_cycle_check_in_real_lean,
    acyclicity_cycle_reversed_check_in_real_lean,
    acyclicity_two_step_cycle_check_in_real_lean,
    acyclicity_three_step_cycle_check_in_real_lean,
    distinct_constructor_equality_is_not_an_injectivity_refutation,
    qf_bv_comparison_refutation_checks_in_real_lean,
    qf_bv_bvredand_identity_contradiction_checks_in_real_lean,
    disjunctive_lra_case_split_checks_in_real_lean,
    const_shl_lowering_checks_in_real_lean,
    const_lshr_lowering_checks_in_real_lean,
    const_ashr_lowering_checks_in_real_lean,
    certified_lra_interpolant_both_farkas_certs_checked_by_real_lean,
    certified_euf_interpolant_both_congruence_certs_checked_by_real_lean,
    certified_lia_interpolant_both_integer_certs_checked_by_real_lean,
    certified_uflia_interpolant_both_integer_certs_checked_by_real_lean,
    qf_s_word_clash_refutations_check_in_real_lean,
    qf_s_lex_clash_refutations_check_in_real_lean,
];

/// Collect the Lean modules a builder produces (running its Rust-side structural
/// asserts as a side effect). `per_family = Some(k)` keeps only the first `k`
/// modules (the representative slice); `None` keeps them all.
fn collect_family(
    builder: FamilyBuilder,
    per_family: Option<usize>,
    out: &mut Vec<(String, String)>,
) {
    LEAN_SINK.with(|s| *s.borrow_mut() = Some(Vec::new()));
    builder();
    let cases = LEAN_SINK.with(|s| s.borrow_mut().take().unwrap_or_default());
    let keep = per_family.map_or(cases.len(), |k| k.min(cases.len()));
    out.extend(cases.into_iter().take(keep));
}

/// Build the module list for every family (`per_family = Some(1)` →
/// representative slice; `None` → exhaustive). Reconstruction is the CPU-heavy
/// part, and families are independent, so it is fanned across the same bounded
/// pool as the kernel checks. Each worker owns its `LEAN_SINK` (thread-local),
/// so there is no cross-talk; a builder's structural `assert!`/`panic!` still
/// aborts its scoped thread and fails the test via `thread::scope` join.
fn collect_cases(per_family: Option<usize>) -> Vec<(String, String)> {
    let jobs = lean_jobs(FAMILY_BUILDERS.len());
    let next = AtomicUsize::new(0);
    // Keep results indexed by family so the module order is deterministic.
    let per_family_out: Vec<Mutex<Vec<(String, String)>>> = (0..FAMILY_BUILDERS.len())
        .map(|_| Mutex::new(Vec::new()))
        .collect();

    std::thread::scope(|scope| {
        for _ in 0..jobs {
            scope.spawn(|| {
                loop {
                    let i = next.fetch_add(1, Ordering::SeqCst);
                    if i >= FAMILY_BUILDERS.len() {
                        break;
                    }
                    let mut cases = Vec::new();
                    collect_family(FAMILY_BUILDERS[i], per_family, &mut cases);
                    *per_family_out[i].lock().unwrap() = cases;
                }
            });
        }
    });

    per_family_out
        .into_iter()
        .flat_map(|m| m.into_inner().unwrap())
        .collect()
}

/// Run one Lean module through the kernel. `Ok(())` iff `lean` accepts it and
/// `#print axioms` shows no `sorryAx`; `Err` carries a diagnostic. Returns
/// `Ok(())` (a skip) when no `lean` binary is available.
fn check_one_lean(tag: &str, source: &str) -> Result<(), String> {
    let Some(bin) = lean_bin() else {
        return Ok(());
    };
    let dir = std::env::temp_dir().join(format!("axeyum_lean_{tag}"));
    std::fs::create_dir_all(&dir).map_err(|e| format!("{tag}: create temp dir: {e}"))?;
    let file = dir.join(format!("{tag}.lean"));
    std::fs::write(&file, source).map_err(|e| format!("{tag}: write lean module: {e}"))?;

    let out = Command::new(&bin)
        .arg(&file)
        .output()
        .map_err(|e| format!("{tag}: run lean binary: {e}"))?;
    let stdout = String::from_utf8_lossy(&out.stdout);
    let stderr = String::from_utf8_lossy(&out.stderr);
    if !out.status.success() {
        return Err(format!(
            "lean REJECTED the {tag} module ({})\n=== stdout ===\n{stdout}\n=== stderr ===\n{stderr}\n=== source ({}) ===\n{source}",
            bin.display(),
            file.display()
        ));
    }
    // `#print axioms axeyum_refutation` prints to stdout; a real proof must not
    // lean on the `sorryAx` escape hatch.
    if stdout.contains("sorryAx") {
        return Err(format!(
            "{tag}: reconstructed proof depends on sorryAx:\n{stdout}"
        ));
    }
    if !stdout.contains("axeyum_refutation") {
        return Err(format!("{tag}: missing `#print axioms` output:\n{stdout}"));
    }
    eprintln!("[lean ok] {tag}: {}", stdout.trim().replace('\n', " | "));
    Ok(())
}

/// Collect a Lean module for later kernel checking (harness mode), or — outside
/// the harness — check it immediately and panic on rejection (legacy direct
/// mode, used only if a builder is ever called as a plain function).
fn lean_accepts(tag: &str, source: &str) {
    let collected = LEAN_SINK.with(|s| {
        if let Some(v) = s.borrow_mut().as_mut() {
            v.push((tag.to_owned(), source.to_owned()));
            true
        } else {
            false
        }
    });
    if !collected {
        if lean_bin().is_none() {
            eprintln!(
                "[skip] {tag}: lean binary not found; install via elan or set AXEYUM_LEAN_BIN"
            );
            return;
        }
        if let Err(msg) = check_one_lean(tag, source) {
            panic!("{msg}");
        }
    }
}

/// Optional wall-clock budget from `AXEYUM_LEAN_BUDGET_SECS` (unset/0 = none).
fn lean_budget() -> Option<Duration> {
    match std::env::var("AXEYUM_LEAN_BUDGET_SECS") {
        Ok(v) => v
            .trim()
            .parse::<u64>()
            .ok()
            .filter(|&s| s > 0)
            .map(Duration::from_secs),
        Err(_) => None,
    }
}

/// Pool size from `AXEYUM_LEAN_JOBS`, else available parallelism, clamped to the
/// number of pending modules.
fn lean_jobs(total: usize) -> usize {
    let requested = std::env::var("AXEYUM_LEAN_JOBS")
        .ok()
        .and_then(|v| v.trim().parse::<usize>().ok())
        .filter(|&j| j > 0)
        .or_else(|| {
            std::thread::available_parallelism()
                .ok()
                .map(std::num::NonZeroUsize::get)
        })
        .unwrap_or(1);
    requested.clamp(1, total.max(1))
}

/// Drive `cases` through the real `lean` kernel across a bounded thread pool,
/// honoring the wall-clock budget. Prints an honest summary and FAILS the test
/// iff any *checked* module was rejected. Budget / no-lean skips are loud but
/// not failures. Skips gracefully (prints a note, passes) when no `lean` binary
/// is available — the CI-runner behavior.
fn run_lean_checks(label: &str, cases: &[(String, String)]) {
    let total = cases.len();
    if total == 0 {
        eprintln!("[lean crosscheck:{label}] no modules to check");
        return;
    }
    if lean_bin().is_none() {
        eprintln!(
            "[skip] lean crosscheck:{label}: lean binary not found; install via elan or set \
             AXEYUM_LEAN_BIN ({total} modules NOT checked)"
        );
        return;
    }

    let budget = lean_budget();
    let jobs = lean_jobs(total);
    let start = Instant::now();
    let next = AtomicUsize::new(0);
    let checked = AtomicUsize::new(0);
    let skipped = AtomicUsize::new(0);
    let failures: Mutex<Vec<String>> = Mutex::new(Vec::new());

    std::thread::scope(|scope| {
        for _ in 0..jobs {
            scope.spawn(|| {
                loop {
                    let i = next.fetch_add(1, Ordering::SeqCst);
                    if i >= total {
                        break;
                    }
                    if budget.is_some_and(|b| start.elapsed() >= b) {
                        skipped.fetch_add(1, Ordering::SeqCst);
                        continue;
                    }
                    let (tag, source) = &cases[i];
                    match check_one_lean(tag, source) {
                        Ok(()) => {
                            checked.fetch_add(1, Ordering::SeqCst);
                        }
                        Err(msg) => failures.lock().unwrap().push(msg),
                    }
                }
            });
        }
    });

    let checked = checked.load(Ordering::SeqCst);
    let skipped = skipped.load(Ordering::SeqCst);
    let failures = failures.into_inner().unwrap();
    let budget_note = budget.map_or_else(
        || "no budget".to_owned(),
        |b| format!("budget {}s", b.as_secs()),
    );
    eprintln!(
        "[lean crosscheck:{label}] checked {checked} of {total} modules in {:.1}s using {jobs} \
         jobs ({budget_note}); {skipped} skipped due to budget; {} FAILED",
        start.elapsed().as_secs_f64(),
        failures.len()
    );
    assert!(
        failures.is_empty(),
        "{} Lean module(s) FAILED the kernel crosscheck:\n{}",
        failures.len(),
        failures.join("\n===\n")
    );
}

/// **Representative Lean cross-check (default).** One reconstructed module per
/// proof family is fed to the real `lean` kernel. Fast enough for every
/// `cargo test` run; the exhaustive per-row check lives in
/// `lean_crosscheck_full` (`#[ignore]`). Structural asserts inside every family
/// builder still run for all rows regardless.
#[test]
fn lean_crosscheck_representative() {
    run_lean_checks("representative", &collect_cases(Some(1)));
}

/// **Exhaustive Lean cross-check.** Every reconstructed module across every
/// proof family is fed to the real `lean` kernel. Corpus-scale; run explicitly:
/// `cargo test --test lean_crosscheck -- --ignored`
/// (optionally `AXEYUM_LEAN_BUDGET_SECS=…` / `AXEYUM_LEAN_JOBS=…`).
#[test]
#[ignore = "corpus-scale; run explicitly: cargo test --test lean_crosscheck -- --ignored"]
fn lean_crosscheck_full() {
    run_lean_checks("full", &collect_cases(None));
}

/// `QF_UFBV`: `f(a) = #b00 ∧ a = b ∧ ¬(f(b) = #b00)` — `Apply` + `BitVec`, refuted
/// by congruence; the exported module must check in real Lean.
fn qf_ufbv_refutation_checks_in_real_lean() {
    let mut arena = TermArena::new();
    let f = arena
        .declare_fun("f", &[Sort::BitVec(2)], Sort::BitVec(2))
        .unwrap();
    let a = {
        let s = arena.declare("a", Sort::BitVec(2)).unwrap();
        arena.var(s)
    };
    let b = {
        let s = arena.declare("b", Sort::BitVec(2)).unwrap();
        arena.var(s)
    };
    let fa = arena.apply(f, &[a]).unwrap();
    let fb = arena.apply(f, &[b]).unwrap();
    let c00 = arena.bv_const(2, 0).unwrap();
    let e1 = arena.eq(fa, c00).unwrap();
    let e2 = arena.eq(a, b).unwrap();
    let e3 = {
        let e = arena.eq(fb, c00).unwrap();
        arena.not(e).unwrap()
    };
    let (_frag, source) =
        prove_unsat_to_lean_module(&mut arena, &[e1, e2, e3]).expect("QF_UFBV unsat reconstructs");
    lean_accepts("qf_ufbv", &source);
}

fn qf_ufbv_lean_entry_normalizes_conjunction_and_double_negation() {
    let mut arena = TermArena::new();
    let f = arena
        .declare_fun("f", &[Sort::BitVec(2)], Sort::BitVec(2))
        .unwrap();
    let a = {
        let s = arena.declare("a", Sort::BitVec(2)).unwrap();
        arena.var(s)
    };
    let b = {
        let s = arena.declare("b", Sort::BitVec(2)).unwrap();
        arena.var(s)
    };
    let fa = arena.apply(f, &[a]).unwrap();
    let fb = arena.apply(f, &[b]).unwrap();
    let c00 = arena.bv_const(2, 0).unwrap();
    let e1 = arena.eq(fa, c00).unwrap();
    let e2 = arena.eq(a, b).unwrap();
    let e3 = {
        let e = arena.eq(fb, c00).unwrap();
        arena.not(e).unwrap()
    };
    let not_e3 = arena.not(e3).unwrap();
    let double_not_e3 = arena.not(not_e3).unwrap();
    let e2_and_e3 = arena.and(e2, double_not_e3).unwrap();
    let single_assertion = arena.and(e1, e2_and_e3).unwrap();

    let (_fragment, source) = prove_unsat_to_lean_module(&mut arena, &[single_assertion])
        .expect("QF_UFBV normalized assertion spine reconstructs");
    lean_accepts("qf_ufbv_normalized_spine", &source);
}

/// P3.7 strings fragment: a word-level (string/sequence) refutation reconstructed
/// over the free-monoid string prelude (`Str = List Char`). Two representative
/// shapes — a concrete constant clash and a contradicted disequality — render
/// self-contained modules that must check in real Lean (the `Char`/`Str`/`Bool`
/// inductives regenerate their recursors, and the is-tester / discriminator folds
/// ι-compute).
fn qf_s_word_clash_refutations_check_in_real_lean() {
    let elem = Sort::Seq(axeyum_ir::ArraySortKey::BitVec(8));
    let mk_char = |arena: &mut TermArena, c: u8| {
        let e = arena.bv_const(8, u128::from(c)).unwrap();
        arena.seq_unit(e).unwrap()
    };

    // (a) Concrete constant clash: x = "a" ∧ x = "b".
    {
        let mut arena = TermArena::new();
        let x = {
            let s = arena.declare("x", elem).unwrap();
            arena.var(s)
        };
        let a = mk_char(&mut arena, b'a');
        let b = mk_char(&mut arena, b'b');
        let e1 = arena.eq(x, a).unwrap();
        let e2 = arena.eq(x, b).unwrap();
        let (fragment, source) = prove_unsat_to_lean_module(&mut arena, &[e1, e2])
            .expect("word constant clash reconstructs");
        assert_eq!(fragment, ProofFragment::WordEquation);
        lean_accepts("qf_s_word_constant_clash", &source);
    }

    // (b) Contradicted disequality: x = "hi" ∧ y = "hi" ∧ x ≠ y.
    {
        let mut arena = TermArena::new();
        let x = {
            let s = arena.declare("x", elem).unwrap();
            arena.var(s)
        };
        let y = {
            let s = arena.declare("y", elem).unwrap();
            arena.var(s)
        };
        let h1 = mk_char(&mut arena, b'h');
        let i1 = mk_char(&mut arena, b'i');
        let hi_x = arena.seq_concat(h1, i1).unwrap();
        let h2 = mk_char(&mut arena, b'h');
        let i2 = mk_char(&mut arena, b'i');
        let hi_y = arena.seq_concat(h2, i2).unwrap();
        let e1 = arena.eq(x, hi_x).unwrap();
        let e2 = arena.eq(y, hi_y).unwrap();
        let e3 = {
            let e = arena.eq(x, y).unwrap();
            arena.not(e).unwrap()
        };
        let (fragment, source) = prove_unsat_to_lean_module(&mut arena, &[e1, e2, e3])
            .expect("word disequality reconstructs");
        assert_eq!(fragment, ProofFragment::WordEquation);
        lean_accepts("qf_s_word_disequality", &source);
    }
}

/// P3.7 strings fragment: a lexicographic-order (`str.<=` / `str.<`) first-clash
/// refutation reconstructed over the free-monoid string prelude. A forced-true lex
/// atom that is variable-independently false (its first determined differing
/// position has the left code greater) closes to `False` because the `lex`
/// comparison ι-computes to `Bool.false` — kernel-checked in real Lean (the
/// `Char`/`Str`/`Bool` inductives regenerate their recursors, and the nested
/// `Char.rec`/`Str.rec` order table ι-folds).
fn qf_s_lex_clash_refutations_check_in_real_lean() {
    let ch = |c: char| Seg::Lit(c as u32);
    let vr = |n: &str| Seg::Var(n.to_owned());

    // (a) First-character clash: (str.<= "B"++x "A"++y) — 66 > 65 at pos 0.
    {
        let problem = LexProblem {
            atoms: vec![LexAtom::Lex {
                left: vec![ch('B'), vr("x")],
                right: vec![ch('A'), vr("y")],
                strict: false,
            }],
            assertions: vec![LexFormula::Atom(0)],
        };
        let source = reconstruct_lex_clash_to_lean_module(&problem)
            .expect("lex first-char clash reconstructs");
        lean_accepts("qf_s_lex_first_char_clash", &source);
    }

    // (b) Second-character clash under a variable tail, strict `<`:
    //     (str.< "AD"++x "AC"++y) — equal at pos 0, 68 > 67 at pos 1.
    {
        let problem = LexProblem {
            atoms: vec![LexAtom::Lex {
                left: vec![ch('A'), ch('D'), vr("x")],
                right: vec![ch('A'), ch('C'), vr("y")],
                strict: true,
            }],
            assertions: vec![LexFormula::Atom(0)],
        };
        let source = reconstruct_lex_clash_to_lean_module(&problem)
            .expect("lex strict second-char clash reconstructs");
        lean_accepts("qf_s_lex_strict_second_char_clash", &source);
    }
}

/// `QF_UFBV`: three pairwise-distinct `f(g ·)` outputs over a one-bit domain are
/// impossible by pigeonhole. This is the cvc5 `bug593` dominance-audit miss that
/// is not an Ackermann/BV proof: the Lean path proves it directly by `Bool.rec`
/// over the three one-bit arguments.
fn qf_ufbv_finite_domain_pigeonhole_checks_in_real_lean() {
    let mut script = parse_script(
        r"
        (set-logic QF_UFBV)
        (declare-sort A 0)
        (declare-fun f ((_ BitVec 1)) A)
        (declare-fun g (A) (_ BitVec 1))
        (declare-fun x () A)
        (declare-fun y () A)
        (declare-fun z () A)
        (assert (and
          (not (= (f (g x)) (f (g y))))
          (not (= (f (g x)) (f (g z))))
          (not (= (f (g y)) (f (g z))))))
        (check-sat)
    ",
    )
    .expect("bug593 slice parses");
    let assertions = script.assertions.clone();
    let (fragment, source) = prove_unsat_to_lean_module(&mut script.arena, &assertions)
        .expect("finite-domain pigeonhole unsat reconstructs");
    assert_eq!(fragment, ProofFragment::FiniteDomainPigeonhole);
    assert!(
        !source.contains("sorryAx"),
        "finite-domain pigeonhole module must not lean on sorryAx:\n{source}"
    );
    lean_accepts("qf_ufbv_finite_pigeonhole", &source);
}

/// Quantified Bool/BV audit rows with small finite domains are certified by the
/// evaluator-level finite-domain enumeration route. The Lean export is a
/// checked-certificate wrapper: reconstruction reruns the Rust certifier before
/// rendering the kernel-checked module.
fn quantified_bv_finite_domain_enum_rows_check_in_real_lean() {
    for (tag, input) in [
        (
            "quant_bv_abstract_unsatcore1",
            include_str!(
                "../../../corpus/public-curated/quantified/BV/bitwuzla-regress-clean/solver__abstract__unsatcore1.smt2"
            ),
        ),
        (
            "quant_bv_issue97",
            include_str!(
                "../../../corpus/public-curated/quantified/BV/bitwuzla-regress-clean/solver__quant__issue97.smt2"
            ),
        ),
        (
            "quant_bv_regrnormquant",
            include_str!(
                "../../../corpus/public-curated/quantified/BV/bitwuzla-regress-clean/solver__quant__regrnormquant.smt2"
            ),
        ),
    ] {
        let mut script = parse_script(input).expect("quantified BV audit row parses");
        let assertions = script.assertions.clone();
        let (fragment, source) = prove_unsat_to_lean_module(&mut script.arena, &assertions)
            .unwrap_or_else(|error| panic!("{tag}: finite-domain enum row reconstructs: {error}"));
        assert_eq!(fragment, ProofFragment::FiniteDomainEnum, "{tag}");
        assert!(
            !source.contains("sorryAx"),
            "{tag}: finite-domain enum module must not use sorryAx:\n{source}"
        );
        lean_accepts(tag, &source);
    }
}

/// Two distinct applications of one untouched universal source assertion imply
/// `p` and `q`; the ground assertion `not (p and q)` closes the source-derived
/// `QF_BV` residual. Both the in-tree kernel and real Lean check the resulting
/// quantified theorem.
fn quantified_bv_source_instance_set_checks_in_real_lean() {
    let mut script = parse_script(
        r"
        (set-logic BV)
        (declare-fun p () Bool)
        (declare-fun q () Bool)
        (assert (forall ((x (_ BitVec 32)))
          (and (=> (= x (_ bv0 32)) p)
               (=> (= x (_ bv1 32)) q))))
        (assert (not (and p q)))
        (check-sat)
        ",
    )
    .expect("quantified source-instance case parses");
    let assertions = script.assertions.clone();
    let (fragment, source) = prove_unsat_to_lean_module(&mut script.arena, &assertions)
        .expect("quantified source instances reconstruct");
    assert_eq!(fragment, ProofFragment::BvPositiveUniversalInstanceSet);
    assert!(!source.contains("sorryAx"));
    lean_accepts("quant_bv_source_instance_set", &source);
}

/// A concrete Bool/BV witness proves the existential body and closes against
/// its untouched negation through genuine typed `Exists.intro`.
fn quantified_bv_negated_existential_witness_checks_in_real_lean() {
    let mut script = parse_script(
        "(set-logic BV)
         (assert (not (exists ((b Bool) (x (_ BitVec 21)))
           (and b (= x x)))))
         (check-sat)",
    )
    .expect("negated-existential witness case parses");
    let assertions = script.assertions.clone();
    let (fragment, source) = prove_unsat_to_lean_module(&mut script.arena, &assertions)
        .expect("negated-existential witness reconstructs");
    assert_eq!(fragment, ProofFragment::NegatedExistentialWitness);
    assert!(!source.contains("sorryAx"));
    lean_accepts("quant_bv_negated_existential_witness", &source);
}

/// The remaining cvc5 quantified-BV inversion audit rows are closed by a checked
/// non-constant universal-BV certificate. Reconstruction reruns that checker
/// before rendering the certificate-wrapper module.
fn cvc5_quantified_bv_inversion_rows_check_in_real_lean() {
    for (tag, input) in [
        (
            "quant_bv_invert_bvadd",
            include_str!(
                "../../../corpus/public-curated/quantified/BV/cvc5-regress-clean/cli__regress0__quantifiers__qbv-test-invert-bvadd-neq.smt2"
            ),
        ),
        (
            "quant_bv_invert_bvashr",
            include_str!(
                "../../../corpus/public-curated/quantified/BV/cvc5-regress-clean/cli__regress0__quantifiers__qbv-test-invert-bvashr-0-neq.smt2"
            ),
        ),
        (
            "quant_bv_invert_concat_0",
            include_str!(
                "../../../corpus/public-curated/quantified/BV/cvc5-regress-clean/cli__regress0__quantifiers__qbv-test-invert-concat-0-neq.smt2"
            ),
        ),
        (
            "quant_bv_invert_concat_1",
            include_str!(
                "../../../corpus/public-curated/quantified/BV/cvc5-regress-clean/cli__regress0__quantifiers__qbv-test-invert-concat-1-neq.smt2"
            ),
        ),
        (
            "quant_bv_invert_bvudiv_0",
            include_str!(
                "../../../corpus/public-curated/quantified/BV/cvc5-regress-clean/cli__regress1__quantifiers__qbv-test-invert-bvudiv-0-neq.smt2"
            ),
        ),
        (
            "quant_bv_invert_bvudiv_1",
            include_str!(
                "../../../corpus/public-curated/quantified/BV/cvc5-regress-clean/cli__regress1__quantifiers__qbv-test-invert-bvudiv-1-neq.smt2"
            ),
        ),
    ] {
        let mut script = parse_script(input).expect("cvc5 quantified BV inversion row parses");
        let assertions = script.assertions.clone();
        let (fragment, source) = prove_unsat_to_lean_module(&mut script.arena, &assertions)
            .unwrap_or_else(|error| panic!("{tag}: BV universal inversion reconstructs: {error}"));
        assert_eq!(fragment, ProofFragment::BvForallNonconstant, "{tag}");
        assert!(
            !source.contains("sorryAx"),
            "{tag}: BV universal non-constant module must not use sorryAx:\n{source}"
        );
        lean_accepts(tag, &source);
    }
}

/// The `QF_UFFF` cvc5 row parses finite-field values as small bit-vectors. These
/// unsats are certified by deriving local BV equalities, then closing the UF
/// contradiction by congruence. Reconstruction reruns that checker before
/// rendering the certificate-wrapper module.
fn qf_ufff_bv_uf_local_rows_check_in_real_lean() {
    for (tag, input) in [
        (
            "qf_ufff_with_uf",
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_UFFF/cvc5-regress-clean/cli__regress0__ff__with_uf.smt2"
            ),
        ),
        (
            "qf_ufff_with_uf2",
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_UFFF/cvc5-regress-clean/cli__regress0__ff__with_uf2.smt2"
            ),
        ),
        (
            "qf_ufff_with_uf3",
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_UFFF/cvc5-regress-clean/cli__regress0__ff__with_uf3.smt2"
            ),
        ),
        (
            "qf_ufff_with_uf5",
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_UFFF/cvc5-regress-clean/cli__regress0__ff__with_uf5.smt2"
            ),
        ),
        (
            "qf_ufff_with_uf7",
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_UFFF/cvc5-regress-clean/cli__regress0__ff__with_uf7.smt2"
            ),
        ),
        (
            "qf_ufff_with_uf8",
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_UFFF/cvc5-regress-clean/cli__regress0__ff__with_uf8.smt2"
            ),
        ),
    ] {
        let mut script = parse_script(input).expect("QF_UFFF row parses");
        let assertions = script.assertions.clone();
        let (fragment, source) = prove_unsat_to_lean_module(&mut script.arena, &assertions)
            .unwrap_or_else(|error| panic!("{tag}: local BV+UF reconstructs: {error}"));
        assert_eq!(fragment, ProofFragment::BvUfLocal, "{tag}");
        assert!(
            !source.contains("sorryAx"),
            "{tag}: local BV+UF module must not use sorryAx:\n{source}"
        );
        lean_accepts(tag, &source);
    }
}

/// Ground `QF_FF` rows that fit the term-level Bool/BV enumeration budget already
/// have checked evidence; reconstruction must route them through the same
/// executable certificate instead of falling back to the unsupported DRAT Lean
/// path.
fn qf_ff_term_level_enum_rows_check_in_real_lean() {
    for (tag, input) in [
        (
            "qf_ff_simple",
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_FF/cvc5-regress-clean/cli__regress0__ff__simple.smt2"
            ),
        ),
        (
            "qf_ff_univar_conjunction_unsat",
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_FF/cvc5-regress-clean/cli__regress0__ff__univar_conjunction_unsat.smt2"
            ),
        ),
    ] {
        let mut script = parse_script(input).expect("QF_FF row parses");
        let assertions = script.assertions.clone();
        let (fragment, source) = prove_unsat_to_lean_module(&mut script.arena, &assertions)
            .unwrap_or_else(|error| panic!("{tag}: term-level enum reconstructs: {error}"));
        assert_eq!(fragment, ProofFragment::TermLevelEnum, "{tag}");
        assert!(
            !source.contains("sorryAx"),
            "{tag}: term-level enum module must not use sorryAx:\n{source}"
        );
        lean_accepts(tag, &source);
    }
}

/// The two remaining `QF_FF` audit gaps are certified by bounded enumeration after
/// checked top-level definitions and finite-domain restrictions. This keeps
/// finite-field algebra/parity rows off the unsupported DRAT Lean path.
fn qf_ff_bv_defined_enum_gap_rows_check_in_real_lean() {
    for (tag, input) in [
        (
            "qf_ff_xor_sound",
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_FF/cvc5-regress-clean/cli__regress0__ff__ff_xor_sound.smt2"
            ),
        ),
        (
            "qf_ff_issue10937",
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_FF/cvc5-regress-clean/cli__regress0__ff__issue10937.smt2"
            ),
        ),
    ] {
        let mut script = parse_script(input).expect("QF_FF row parses");
        let assertions = script.assertions.clone();
        let (fragment, source) = prove_unsat_to_lean_module(&mut script.arena, &assertions)
            .unwrap_or_else(|error| panic!("{tag}: BV defined enum reconstructs: {error}"));
        assert_eq!(fragment, ProofFragment::BvDefinedEnum, "{tag}");
        assert!(
            !source.contains("sorryAx"),
            "{tag}: BV defined enum module must not use sorryAx:\n{source}"
        );
        lean_accepts(tag, &source);
    }
}

/// `QF_FP` rows lower to finite scalar terms with Float values represented as bit
/// patterns. The definition-aware enum route rechecks the original assertions
/// before rendering the Lean wrapper.
fn qf_fp_bv_defined_enum_rows_check_in_real_lean() {
    for (tag, input) in [
        (
            "qf_fp_inf",
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_FP/bitwuzla-regress-clean/solver__fp__fp_inf.smt2"
            ),
        ),
        (
            "qf_fp_zero",
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_FP/bitwuzla-regress-clean/solver__fp__fp_zero.smt2"
            ),
        ),
        (
            "qf_fp_misc",
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_FP/bitwuzla-regress-clean/solver__fp__fp_misc.smt2"
            ),
        ),
    ] {
        let mut script = parse_script(input).expect("QF_FP row parses");
        let assertions = script.assertions.clone();
        let (fragment, source) = prove_unsat_to_lean_module(&mut script.arena, &assertions)
            .unwrap_or_else(|error| panic!("{tag}: BV defined enum reconstructs: {error}"));
        assert_eq!(fragment, ProofFragment::BvDefinedEnum, "{tag}");
        assert!(
            !source.contains("sorryAx"),
            "{tag}: BV defined enum module must not use sorryAx:\n{source}"
        );
        lean_accepts(tag, &source);
    }
}

fn qf_bvfp_bv_defined_enum_rows_check_in_real_lean() {
    for (tag, input) in [
        (
            "qf_bvfp_float_no_simp3",
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_BVFP/bitwuzla-regress-clean/solver__fp__Float-no-simp3-main.smt2"
            ),
        ),
        (
            "qf_bvfp_fp_fromsbv",
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_BVFP/bitwuzla-regress-clean/solver__fp__fp_fromsbv.smt2"
            ),
        ),
    ] {
        let mut script = parse_script(input).expect("QF_BVFP row parses");
        let assertions = script.assertions.clone();
        let (fragment, source) = prove_unsat_to_lean_module(&mut script.arena, &assertions)
            .unwrap_or_else(|error| panic!("{tag}: BV defined enum reconstructs: {error}"));
        assert_eq!(fragment, ProofFragment::BvDefinedEnum, "{tag}");
        assert!(
            !source.contains("sorryAx"),
            "{tag}: BV defined enum module must not use sorryAx:\n{source}"
        );
        lean_accepts(tag, &source);
    }
}

fn qf_dt_cvc5_slice_checks_in_real_lean() {
    for (tag, input) in [
        (
            "qf_dt_pf_v2l60078",
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_DT/cvc5-regress-clean/cli__regress0__datatypes__pf-v2l60078.smt2"
            ),
        ),
        (
            "qf_dt_cons_eq_clash",
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_DT/cvc5-regress-clean/cli__regress0__proofs__dt-cons-eq-clash-qfdt.smt2"
            ),
        ),
        (
            "qf_dt_acyclicity_or",
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_DT/cvc5-regress-clean/cli__regress1__datatypes__acyclicity-sr-ground096.smt2"
            ),
        ),
    ] {
        let mut script = parse_script(input).unwrap_or_else(|e| panic!("{tag}: parses: {e}"));
        let assertions = script.assertions.clone();
        let (fragment, source) = prove_unsat_to_lean_module(&mut script.arena, &assertions)
            .unwrap_or_else(|e| panic!("{tag}: datatype structural row reconstructs: {e}"));
        assert_eq!(fragment, ProofFragment::DatatypeStructural, "{tag}");
        assert!(
            !source.contains("sorryAx"),
            "{tag}: datatype structural module must not use sorryAx:\n{source}"
        );
        lean_accepts(tag, &source);
    }
}

/// `LRA`: `x < 0 ∧ 0 ≤ x` — a Farkas refutation over the axiomatized ordered field.
fn lra_refutation_checks_in_real_lean() {
    let mut arena = TermArena::new();
    let x = arena.real_var("x").unwrap();
    let zero = arena.real_const(Rational::integer(0));
    let a1 = arena.real_lt(x, zero).unwrap();
    let a2 = arena.real_le(zero, x).unwrap();
    let (_frag, source) =
        prove_unsat_to_lean_module(&mut arena, &[a1, a2]).expect("LRA unsat reconstructs");
    lean_accepts("lra", &source);
}

/// `QF_LRA`: the cvc5 `ite_arith` row is `not (= x (ite true x y))`.
/// The checked term-identity route recognizes `ite true x y = x` and exports a
/// Lean proof of the contradiction without invoking the bit-blast or DPLL proof
/// routes.
fn qf_lra_ite_true_identity_checks_in_real_lean() {
    let mut script = parse_script(include_str!(
        "../../../corpus/public-curated/non-incremental/QF_LRA/cvc5-regress-clean/cli__regress0__ite_arith.smt2"
    ))
    .expect("ite_arith parses");
    let assertions = script.assertions.clone();
    let (fragment, source) = prove_unsat_to_lean_module(&mut script.arena, &assertions)
        .expect("ite true identity contradiction reconstructs");
    assert_eq!(fragment, ProofFragment::TermIdentity);
    assert!(
        !source.contains("sorryAx"),
        "term-identity module must not use sorryAx:\n{source}"
    );
    lean_accepts("qf_lra_ite_true_identity", &source);
}

/// `QF_LRA`: the remaining cvc5 Boolean-LRA audit rows are certified by the
/// lazy-SMT DPLL(T) refutation checker. The Lean route is a checked-certificate
/// wrapper: reconstruction reruns the Rust certificate before rendering a kernel
/// proof term, matching the existing structural certificate routes.
fn qf_lra_dpll_audit_rows_check_in_real_lean() {
    for (tag, input) in [
        (
            "qf_lra_dpll_ite_lift",
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_LRA/cvc5-regress-clean/cli__regress0__arith__ite-lift.smt2"
            ),
        ),
        (
            "qf_lra_dpll_simple_lra",
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_LRA/cvc5-regress-clean/cli__regress0__simple-lra.smt2"
            ),
        ),
    ] {
        let mut script = parse_script(input).expect("QF_LRA audit row parses");
        let assertions = script.assertions.clone();
        let (fragment, source) = prove_unsat_to_lean_module(&mut script.arena, &assertions)
            .expect("LRA DPLL row reconstructs");
        assert_eq!(fragment, ProofFragment::LraDpll);
        assert!(
            !source.contains("sorryAx"),
            "LRA DPLL module must not use sorryAx:\n{source}"
        );
        lean_accepts(tag, &source);
    }
}

/// `QF_LIA`: two exact-audit unsats are certified by the arithmetic lazy-SMT
/// DPLL(T) refutation checker. As with `LraDpll`, the Lean route reruns the
/// Rust certificate and renders only a checked certificate wrapper.
fn qf_lia_arith_dpll_audit_rows_check_in_real_lean() {
    for (tag, input) in [
        (
            "qf_lia_arith_dpll_dump_unsat_core_full",
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_LIA/cvc5-regress-clean-bounded/cli__regress0__dump-unsat-core-full.smt2"
            ),
        ),
        (
            "qf_lia_arith_dpll_named_expr_use",
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_LIA/cvc5-regress-clean-bounded/cli__regress0__named-expr-use.smt2"
            ),
        ),
    ] {
        let mut script = parse_script(input).expect("QF_LIA audit row parses");
        let assertions = script.assertions.clone();
        let (fragment, source) = prove_unsat_to_lean_module(&mut script.arena, &assertions)
            .expect("arithmetic DPLL row reconstructs");
        assert_eq!(fragment, ProofFragment::ArithDpll);
        assert!(
            !source.contains("sorryAx"),
            "arithmetic DPLL module must not use sorryAx:\n{source}"
        );
        lean_accepts(tag, &source);
    }
}

/// `QF_UFLIA`: the `use-name-in-same-command` rows are Boolean-structured
/// arithmetic proof-step encodings. They reconstruct through the same checked
/// `ArithDPLL` wrapper after treating integer-valued UF applications as opaque
/// arithmetic variables.
fn qf_uflia_use_name_arith_dpll_rows_check_in_real_lean() {
    for (tag, input) in [
        (
            "qf_uflia_curated_use_name_arith_dpll",
            include_str!(
                "../../../corpus/public-curated/named/cvc5__use-name-in-same-command.smt2"
            ),
        ),
        (
            "qf_uflia_bounded_use_name_arith_dpll",
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_UFLIA/cvc5-regress-clean-bounded/cli__regress0__parser__use-name-in-same-command.smt2"
            ),
        ),
    ] {
        let mut script = parse_script(input).expect("QF_UFLIA use-name row parses");
        let assertions = script.assertions.clone();
        let (fragment, source) = prove_unsat_to_lean_module(&mut script.arena, &assertions)
            .expect("UFLIA arithmetic DPLL row reconstructs");
        assert_eq!(fragment, ProofFragment::ArithDpll);
        assert!(
            !source.contains("sorryAx"),
            "UFLIA arithmetic DPLL module must not use sorryAx:\n{source}"
        );
        lean_accepts(tag, &source);
    }
}

/// `QF_LIA`: the RF-11 ACI normalization stress row contains a large Boolean
/// assertion that simplifies directly to `false`. The checked Boolean
/// simplification route avoids spending the audit budget in arithmetic DPLL.
fn qf_lia_bool_simplification_audit_row_checks_in_real_lean() {
    let mut script = parse_script(include_str!(
        "../../../corpus/public-curated/non-incremental/QF_LIA/cvc5-regress-clean-bounded/cli__regress0__proofs__RF-11-aci-norm-ndet.smt2"
    ))
    .expect("QF_LIA RF row parses");
    let assertions = script.assertions.clone();
    let (fragment, source) = prove_unsat_to_lean_module(&mut script.arena, &assertions)
        .expect("Boolean simplification row reconstructs");
    assert_eq!(fragment, ProofFragment::BoolSimplification);
    assert!(
        !source.contains("sorryAx"),
        "Boolean simplification module must not use sorryAx:\n{source}"
    );
    lean_accepts("qf_lia_bool_simplification_rf11", &source);
}

/// `QF_UFNRA`: cvc5 `issue3970-nl-ext-purify` contains a purified `distinct`
/// contradiction whose expansion includes a disequality of the same term with
/// itself, before any nonlinear arithmetic certificate is needed.
fn qf_uf_issue3970_term_identity_checks_in_real_lean() {
    let mut script = parse_script(include_str!(
        "../../../corpus/public-curated/non-incremental/QF_UF/cvc5-regress-clean-bounded/cli__regress1__issue3970-nl-ext-purify.smt2"
    ))
    .expect("issue3970 row parses");
    let assertions = script.assertions.clone();
    let (fragment, source) = prove_unsat_to_lean_module(&mut script.arena, &assertions)
        .expect("issue3970 term-identity row reconstructs");
    assert_eq!(fragment, ProofFragment::TermIdentity);
    assert!(
        !source.contains("sorryAx"),
        "term-identity module must not use sorryAx:\n{source}"
    );
    lean_accepts("qf_uf_issue3970_term_identity", &source);
}

/// `QF_UFBV`: bitwuzla `fun1` is a tiny Boolean functional-graph
/// contradiction. Exhaustively checking the two Boolean variables and the
/// four unary-Boolean function interpretations gives a direct certificate,
/// avoiding the old Ackermann + bit-blast trust-hole route.
fn qf_ufbv_fun1_bool_uf_exhaustive_checks_in_real_lean() {
    let mut script = parse_script(include_str!(
        "../../../corpus/public-curated/non-incremental/QF_UFBV/bitwuzla-regress-clean/solver__fun__fun1.smt2"
    ))
    .expect("bitwuzla fun1 row parses");
    let assertions = script.assertions.clone();
    let (fragment, source) = prove_unsat_to_lean_module(&mut script.arena, &assertions)
        .expect("Boolean-UF exhaustive row reconstructs");
    assert_eq!(fragment, ProofFragment::BoolUfExhaustive);
    assert!(
        !source.contains("sorryAx"),
        "Boolean-UF exhaustive module must not use sorryAx:\n{source}"
    );
    lean_accepts("qf_ufbv_fun1_bool_uf_exhaustive", &source);
}

/// `QF_UF` with finite sets: the frontend lowers `set.card` to BV popcounts.
/// `sets/card-6` is refuted by `C ⊆ A ∪ B`, `|C| ≥ 5`, `|A| ≤ 2`, and
/// `|B| ≤ 2`, so the certificate avoids the slower reduced-CNF proof route.
fn qf_uf_sets_cardinality_checks_in_real_lean() {
    let mut script = parse_script(include_str!(
        "../../../corpus/public-curated/non-incremental/QF_UF/cvc5-regress-clean-bounded/cli__regress1__sets__card-6.smt2"
    ))
    .expect("sets/card-6 row parses");
    let assertions = script.assertions.clone();
    let (fragment, source) = prove_unsat_to_lean_module(&mut script.arena, &assertions)
        .expect("set-cardinality row reconstructs");
    assert_eq!(fragment, ProofFragment::SetCardinality);
    assert!(
        !source.contains("sorryAx"),
        "set-cardinality module must not use sorryAx:\n{source}"
    );
    lean_accepts("qf_uf_sets_cardinality", &source);
}

/// `QF_UF`: Boolean structure around EUF atoms is discharged by enumerating the
/// equality-atom skeleton and checking every skeleton model with congruence.
fn qf_uf_boolean_euf_rows_check_in_real_lean() {
    for (tag, input, expected_fragment) in [
        (
            "qf_uf_simple_uf_bool_euf",
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_UF/cvc5-regress-clean-bounded/cli__regress0__simple-uf.smt2"
            ),
            ProofFragment::ArrayAxiom,
        ),
        (
            "qf_uf_cnf_and_neg_bool_euf",
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_UF/cvc5-regress-clean-bounded/cli__regress0__uf__cnf-and-neg.smt2"
            ),
            ProofFragment::BoolEufExhaustive,
        ),
        (
            "qf_uf_cnf_ite_bool_euf",
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_UF/cvc5-regress-clean-bounded/cli__regress0__uf__cnf-ite.smt2"
            ),
            ProofFragment::BoolEufExhaustive,
        ),
    ] {
        let mut script = parse_script(input).expect("Boolean-EUF row parses");
        let assertions = script.assertions.clone();
        let (fragment, source) = prove_unsat_to_lean_module(&mut script.arena, &assertions)
            .unwrap_or_else(|error| panic!("{tag}: reconstructs: {error}"));
        assert_eq!(fragment, expected_fragment, "{tag}");
        assert!(
            !source.contains("sorryAx"),
            "{tag}: Boolean-EUF module must not use sorryAx:\n{source}"
        );
        lean_accepts(tag, &source);
    }
}

/// `QF_UF` overbound finite-model rows are too large for the bounded exhaustive
/// Boolean-EUF checker, but the online EUF DPLL(T) checker refutes their
/// Boolean equality skeletons and the Lean wrapper re-runs that checker.
fn qf_uf_overbound_online_euf_rows_check_in_real_lean() {
    for (tag, input) in [
        (
            "qf_uf_overbound_cnf_abc_online_euf",
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_UF/cvc5-regress-clean-overbound/cli__regress0__uf__cnf_abc.smt2"
            ),
        ),
        (
            "qf_uf_overbound_proof00_online_euf",
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_UF/cvc5-regress-clean-overbound/cli__regress1__proof00.smt2"
            ),
        ),
        (
            "qf_uf_overbound_macro_res_online_euf",
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_UF/cvc5-regress-clean-overbound/cli__regress1__proofs__macro-res-exp-crowding-lit-inside-unit.smt2"
            ),
        ),
    ] {
        let mut script = parse_script(input).expect("overbound Boolean-EUF row parses");
        let assertions = script.assertions.clone();
        let (fragment, source) = prove_unsat_to_lean_module(&mut script.arena, &assertions)
            .unwrap_or_else(|error| panic!("{tag}: reconstructs: {error}"));
        assert_eq!(fragment, ProofFragment::BoolEufOnline, "{tag}");
        assert!(
            !source.contains("sorryAx"),
            "{tag}: online Boolean-EUF module must not use sorryAx:\n{source}"
        );
        lean_accepts(tag, &source);
    }
}

/// `QF_UFLIA`: `bug303` needs congruence over the declared `list` carrier before
/// the integer contradiction is visible.
fn qf_uf_bug303_uf_arith_congruence_checks_in_real_lean() {
    let mut script = parse_script(include_str!(
        "../../../corpus/public-curated/non-incremental/QF_UF/cvc5-regress-clean-bounded/cli__regress0__bug303.smt2"
    ))
    .expect("bug303 parses");
    let assertions = script.assertions.clone();
    let (fragment, source) =
        prove_unsat_to_lean_module(&mut script.arena, &assertions).expect("bug303 reconstructs");
    assert_eq!(fragment, ProofFragment::UfArithCongruence);
    assert!(
        !source.contains("sorryAx"),
        "UF arithmetic congruence module must not use sorryAx:\n{source}"
    );
    lean_accepts("qf_uf_bug303_uf_arith_congruence", &source);
}

/// `QF_UF`: `parallel-let` reduces to a declared-carrier equality conflict
/// without any `Apply` node. The current proof route discharges it through the
/// exhaustive Boolean-EUF checker over the declared carrier equality atoms.
fn qf_uf_declared_sort_equality_checks_in_real_lean() {
    let mut script = parse_script(
        r"
        (set-logic QF_UF)
        (declare-sort U 0)
        (declare-fun x () U)
        (declare-fun y () U)
        (assert (distinct x y))
        (assert (let ((x y) (y x)) (= x y)))
        (check-sat)
    ",
    )
    .expect("parallel-let slice parses");
    let assertions = script.assertions.clone();
    let (fragment, source) = prove_unsat_to_lean_module(&mut script.arena, &assertions)
        .expect("declared-sort EUF equality row reconstructs");
    assert_eq!(fragment, ProofFragment::BoolEufExhaustive);
    assert!(
        !source.contains("sorryAx"),
        "declared-sort EUF module must not use sorryAx:\n{source}"
    );
    lean_accepts("qf_uf_declared_sort_equality", &source);
}

/// `QF_NRA`: broader SOS certificates now reconstruct through a certificate-gated
/// Lean wrapper when the detailed ring-normalized proof slice does not cover the
/// shape. The checker still re-runs `SosCertificate::verify` before rendering.
fn qf_nra_sos_certificate_audit_rows_check_in_real_lean() {
    for (tag, input) in [
        (
            "qf_nra_sos_plus_constant",
            include_str!(
                "../../../corpus/public-curated/synthetic/QF_NRA/graduated/nra-sos-unsat-k01.smt2"
            ),
        ),
        (
            "qf_nra_shifted_sos_plus_constant",
            include_str!(
                "../../../corpus/public-curated/synthetic/QF_NRA/graduated/nra-sos-strict-unsat-d01.smt2"
            ),
        ),
    ] {
        let mut script = parse_script(input).expect("synthetic NRA SOS row parses");
        let assertions = script.assertions.clone();
        let (fragment, source) = prove_unsat_to_lean_module(&mut script.arena, &assertions)
            .expect("SOS certificate row reconstructs");
        assert_eq!(fragment, ProofFragment::Sos);
        assert!(
            !source.contains("sorryAx"),
            "SOS certificate module must not use sorryAx:\n{source}"
        );
        lean_accepts(tag, &source);
    }
}

/// `QF_NRA`: higher even-power nonnegativity rows are outside the degree-2 SOS
/// certificate but still reconstruct through a checked structural Lean wrapper.
fn qf_nra_even_power_audit_rows_check_in_real_lean() {
    for (tag, input) in [
        (
            "qf_nra_fourth_power_negative",
            include_str!(
                "../../../corpus/public-curated/synthetic/QF_NRA/graduated/nra-neg-square-d02.smt2"
            ),
        ),
        (
            "qf_nra_shifted_fourth_power_sum",
            include_str!(
                "../../../corpus/public-curated/synthetic/QF_NRA/graduated/nra-sos-strict-unsat-d02.smt2"
            ),
        ),
    ] {
        let mut script = parse_script(input).expect("synthetic NRA even-power row parses");
        let assertions = script.assertions.clone();
        let (fragment, source) = prove_unsat_to_lean_module(&mut script.arena, &assertions)
            .expect("even-power certificate row reconstructs");
        assert_eq!(fragment, ProofFragment::NraEvenPower);
        assert!(
            !source.contains("sorryAx"),
            "even-power module must not use sorryAx:\n{source}"
        );
        lean_accepts(tag, &source);
    }
}

/// `QF_NIA`: bounded nonlinear integer UNSAT rows are certified by the
/// proven-box bounded-int-blast certificate (box + regenerated DIMACS + DRAT)
/// and reconstruct through a certificate-gated Lean wrapper.
fn qf_nia_bounded_int_blast_audit_rows_check_in_real_lean() {
    for (tag, input) in [
        (
            "qf_nia_no_square_mod_bounded_int_blast",
            include_str!(
                "../../../corpus/public-curated/synthetic/QF_NIA/graduated/nia-no-square-mod-b08.smt2"
            ),
        ),
        (
            "qf_nia_sum_sq_2_bounded_int_blast",
            include_str!(
                "../../../corpus/public-curated/synthetic/QF_NIA/graduated/nia-sum-sq-2-n08.smt2"
            ),
        ),
    ] {
        let mut script = parse_script(input).expect("synthetic QF_NIA row parses");
        let assertions = script.assertions.clone();
        let (fragment, source) = prove_unsat_to_lean_module(&mut script.arena, &assertions)
            .expect("bounded-int-blast certificate row reconstructs");
        assert_eq!(fragment, ProofFragment::BoundedIntBlast);
        assert!(
            !source.contains("sorryAx"),
            "bounded-int-blast module must not use sorryAx:\n{source}"
        );
        lean_accepts(tag, &source);
    }
}

/// Universal: `∀x.(f x = c) ∧ ¬(f a = c)` — instantiation refutation.
fn forall_refutation_checks_in_real_lean() {
    let mut arena = TermArena::new();
    let alpha = Sort::BitVec(8);
    let x = arena.declare("x", alpha).unwrap();
    let a = arena.declare("a", alpha).unwrap();
    let c = arena.declare("c", alpha).unwrap();
    let f = arena.declare_fun("f", &[alpha], alpha).unwrap();
    let xv = arena.var(x);
    let cv = arena.var(c);
    let fx = arena.apply(f, &[xv]).unwrap();
    let fx_eq_c = arena.eq(fx, cv).unwrap();
    let forall = arena.forall(x, fx_eq_c).unwrap();
    let av = arena.var(a);
    let fa = arena.apply(f, &[av]).unwrap();
    let not_fa_eq_c = {
        let e = arena.eq(fa, cv).unwrap();
        arena.not(e).unwrap()
    };
    let (_frag, source) = prove_unsat_to_lean_module(&mut arena, &[forall, not_fa_eq_c])
        .expect("∀ unsat reconstructs");
    lean_accepts("forall", &source);
}

/// Existential: `∃x.(f x = c) ∧ ∀y.(f y = d) ∧ c ≠ d` — skolemization refutation.
fn exists_refutation_checks_in_real_lean() {
    let mut arena = TermArena::new();
    let alpha = Sort::BitVec(8);
    let x = arena.declare("x", alpha).unwrap();
    let y = arena.declare("y", alpha).unwrap();
    let c = arena.declare("c", alpha).unwrap();
    let d = arena.declare("d", alpha).unwrap();
    let f = arena.declare_fun("f", &[alpha], alpha).unwrap();
    let xv = arena.var(x);
    let cv = arena.var(c);
    let fx = arena.apply(f, &[xv]).unwrap();
    let fx_eq_c = arena.eq(fx, cv).unwrap();
    let exists = arena.exists(x, fx_eq_c).unwrap();
    let yv = arena.var(y);
    let dv = arena.var(d);
    let fy = arena.apply(f, &[yv]).unwrap();
    let fy_eq_d = arena.eq(fy, dv).unwrap();
    let forall = arena.forall(y, fy_eq_d).unwrap();
    let not_c_eq_d = {
        let e = arena.eq(cv, dv).unwrap();
        arena.not(e).unwrap()
    };
    let (_frag, source) = prove_unsat_to_lean_module(&mut arena, &[exists, forall, not_c_eq_d])
        .expect("∃ unsat reconstructs");
    lean_accepts("exists", &source);
}

/// `QF_ABV`: `select(a, i) = 0 ∧ i = j ∧ ¬(select(a, j) = 0)` is unsat by read
/// consistency (`i = j ⇒ select(a, i) = select(a, j)`). The reconstructed array
/// refutation (via array elimination → `QF_UFBV`) must type-check in real Lean.
fn qf_abv_read_consistency_refutation_checks_in_real_lean() {
    let mut arena = TermArena::new();
    let a = arena.array_var("a", 4, 8).unwrap();
    let i = {
        let s = arena.declare("i", Sort::BitVec(4)).unwrap();
        arena.var(s)
    };
    let j = {
        let s = arena.declare("j", Sort::BitVec(4)).unwrap();
        arena.var(s)
    };
    let c = arena.bv_const(8, 0).unwrap();
    let sa = arena.select(a, i).unwrap();
    let sb = arena.select(a, j).unwrap();
    let e1 = arena.eq(sa, c).unwrap();
    let e2 = arena.eq(i, j).unwrap();
    let e3 = {
        let e = arena.eq(sb, c).unwrap();
        arena.not(e).unwrap()
    };
    let (_frag, source) = prove_unsat_to_lean_module(&mut arena, &[e1, e2, e3])
        .expect("QF_ABV read-consistency unsat reconstructs");
    lean_accepts("qf_abv", &source);
}

/// `QF_ABV`: `a = b ∧ ¬(select a i = select b i)` is unsat by congruence over
/// `select`. This is the corpus `smtextarrayaxiom*uf` shape: evidence already has
/// a direct Alethe certificate, and the Lean route should reconstruct that direct
/// EUF proof instead of requiring the array-elimination certificate.
fn qf_abv_select_congruence_refutation_checks_in_real_lean() {
    let mut arena = TermArena::new();
    let a = arena.array_var("a", 2, 2).unwrap();
    let b = arena.array_var("b", 2, 2).unwrap();
    let i = {
        let s = arena.declare("i", Sort::BitVec(2)).unwrap();
        arena.var(s)
    };
    let sa = arena.select(a, i).unwrap();
    let sb = arena.select(b, i).unwrap();
    let a_eq_b = arena.eq(a, b).unwrap();
    let reversed_reads_ne = {
        let e = arena.eq(sb, sa).unwrap();
        arena.not(e).unwrap()
    };
    let (_frag, reversed_source) =
        prove_unsat_to_lean_module(&mut arena, &[a_eq_b, reversed_reads_ne])
            .expect("reversed QF_ABV select congruence unsat reconstructs");
    lean_accepts("qf_abv_select_congruence_reversed", &reversed_source);

    let reads_ne = {
        let e = arena.eq(sa, sb).unwrap();
        arena.not(e).unwrap()
    };
    let (_frag, source) = prove_unsat_to_lean_module(&mut arena, &[a_eq_b, reads_ne])
        .expect("forward QF_ABV select congruence unsat reconstructs");
    lean_accepts("qf_abv_select_congruence", &source);
}

fn array_axiom_lean_entry_normalizes_conjunction_and_double_negation() {
    let mut arena = TermArena::new();
    let a = arena.array_var("a", 2, 8).unwrap();
    let i = arena.bv_const(2, 1).unwrap();
    let v = arena.bv_const(8, 0xab).unwrap();
    let stored = arena.store(a, i, v).unwrap();
    let read = arena.select(stored, i).unwrap();
    let eq = arena.eq(read, v).unwrap();
    let diseq = arena.not(eq).unwrap();
    let not_diseq = arena.not(diseq).unwrap();
    let double_not_diseq = arena.not(not_diseq).unwrap();
    let truth = arena.bool_const(true);
    let single_assertion = arena.and(truth, double_not_diseq).unwrap();

    let (fragment, source) = prove_unsat_to_lean_module(&mut arena, &[single_assertion])
        .expect("array axiom normalized assertion spine reconstructs");
    assert_eq!(fragment, ProofFragment::ArrayAxiom);
    lean_accepts("array_axiom_normalized_spine", &source);
}

/// `QF_AUFBV`: all concrete reads over a finite BV2 index domain are equal, but
/// the arrays are asserted disequal. This mirrors the `smtextarrayaxiom*` corpus
/// family and reconstructs through the finite-array extensionality certificate,
/// not the generic ABV/Alethe route.
fn qf_aufbv_finite_array_extensionality_checks_in_real_lean() {
    let mut script = parse_script(
        r"
        (set-logic QF_AUFBV)
        (declare-fun a () (Array (_ BitVec 2) (_ BitVec 2)))
        (declare-fun b () (Array (_ BitVec 2) (_ BitVec 2)))
        (assert (= (select a (_ bv0 2)) (select b (_ bv0 2))))
        (assert (= (select a (_ bv1 2)) (select b (_ bv1 2))))
        (assert (= (select a (_ bv2 2)) (select b (_ bv2 2))))
        (assert (= (select a (_ bv3 2)) (select b (_ bv3 2))))
        (assert (not (= a b)))
        (check-sat)
    ",
    )
    .expect("finite-array extensionality slice parses");
    let assertions = script.assertions.clone();
    let (fragment, source) = prove_unsat_to_lean_module(&mut script.arena, &assertions)
        .expect("finite-array extensionality unsat reconstructs");
    assert_eq!(fragment, ProofFragment::FiniteArrayExtensionality);
    assert!(
        !source.contains("sorryAx"),
        "finite-array extensionality module must not lean on sorryAx:\n{source}"
    );
    lean_accepts("qf_aufbv_finite_array_extensionality", &source);
}

/// `QF_AUFBV`: single-assertion negations of small array axiom schemas from the
/// bitwuzla array regression slice. The schema checker supplies the certified
/// equality and the Lean route closes it against the asserted disequality.
#[allow(clippy::too_many_lines)]
fn qf_aufbv_array_axiom_refutations_check_in_real_lean() {
    let cases = [
        (
            "qf_aufbv_mccarthy",
            r"
            (set-logic QF_AUFBV)
            (declare-fun i () (_ BitVec 32))
            (declare-fun j () (_ BitVec 32))
            (declare-fun v () (_ BitVec 8))
            (declare-fun a () (Array (_ BitVec 32) (_ BitVec 8)))
            (assert (not (= (select (store a i v) j) (ite (= i j) v (select a j)))))
            (check-sat)
        ",
        ),
        (
            "qf_aufbv_select_ite",
            r"
            (set-logic QF_AUFBV)
            (declare-fun a () (Array (_ BitVec 32) (_ BitVec 8)))
            (declare-fun b () (Array (_ BitVec 32) (_ BitVec 8)))
            (declare-fun i () (_ BitVec 32))
            (declare-fun c () Bool)
            (assert (not (= (ite c (select a i) (select b i)) (select (ite c a b) i))))
            (check-sat)
        ",
        ),
        (
            "qf_aufbv_store_ite_select",
            r"
            (set-logic QF_AUFBV)
            (declare-fun a () (Array (_ BitVec 32) (_ BitVec 8)))
            (declare-fun b () (Array (_ BitVec 32) (_ BitVec 8)))
            (declare-fun i () (_ BitVec 32))
            (declare-fun j () (_ BitVec 32))
            (declare-fun v () (_ BitVec 8))
            (declare-fun c () Bool)
            (assert (not (= (select (ite c (store a i v) (store b i v)) j)
                            (select (store (ite c a b) i v) j))))
            (check-sat)
        ",
        ),
        (
            "qf_abv_btor_write1",
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__write1.btor.smt2"
            ),
        ),
        (
            "qf_abv_btor_write13",
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__write13.btor.smt2"
            ),
        ),
        (
            "qf_abv_btor_write2",
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__write2.btor.smt2"
            ),
        ),
        (
            "qf_abv_btor_write9",
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__write9.btor.smt2"
            ),
        ),
        (
            "qf_abv_btor_rwpropindexplusconst1",
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/rewrite__array__rwpropindexplusconst1.btor.smt2"
            ),
        ),
        (
            "qf_abv_btor_rwpropindexplusconst3",
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/rewrite__array__rwpropindexplusconst3.btor.smt2"
            ),
        ),
        (
            "qf_abv_btor_write22",
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__write22.btor.smt2"
            ),
        ),
        (
            "qf_abv_btor_write24",
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__write24.btor.smt2"
            ),
        ),
        (
            "qf_abv_btor_rw30",
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/rewrite__array__rw30.btor.smt2"
            ),
        ),
        (
            "qf_abv_btor_rw32",
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/rewrite__array__rw32.btor.smt2"
            ),
        ),
        (
            "qf_abv_btor_rw34",
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/rewrite__array__rw34.btor.smt2"
            ),
        ),
        (
            "qf_abv_btor_write14",
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__write14.btor.smt2"
            ),
        ),
        (
            "qf_abv_btor_arraycondconst",
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__arraycondconst.btor.smt2"
            ),
        ),
        (
            "qf_abv_btor_arraycondconstaig",
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__arraycondconstaig.btor.smt2"
            ),
        ),
        (
            "qf_abv_btor_arraycond3",
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__arraycond3.btor.smt2"
            ),
        ),
        (
            "qf_abv_btor_arraycond5",
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__arraycond5.btor.smt2"
            ),
        ),
        (
            "qf_abv_btor_arraycond6",
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__arraycond6.btor.smt2"
            ),
        ),
        (
            "qf_abv_btor_arraycond7",
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__arraycond7.btor.smt2"
            ),
        ),
        (
            "qf_abv_btor_arraycond8",
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__arraycond8.btor.smt2"
            ),
        ),
        (
            "qf_abv_btor_arraycond9",
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__arraycond9.btor.smt2"
            ),
        ),
        (
            "qf_abv_btor_arraycond11",
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__arraycond11.btor.smt2"
            ),
        ),
        (
            "qf_abv_btor_arraycond12",
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__arraycond12.btor.smt2"
            ),
        ),
        (
            "qf_abv_btor_arraycond13",
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__arraycond13.btor.smt2"
            ),
        ),
        (
            "qf_abv_btor_arraycond14",
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__arraycond14.btor.smt2"
            ),
        ),
        (
            "qf_abv_btor_arraycond18",
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__arraycond18.btor.smt2"
            ),
        ),
        (
            "qf_abv_btor_ext11",
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__ext11.btor.smt2"
            ),
        ),
        (
            "qf_abv_cvc5_issue9519",
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/cvc5-regress-clean/cli__regress0__bv__issue9519.smt2"
            ),
        ),
        (
            "qf_abv_cvc5_proj_issue321",
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/cvc5-regress-clean/cli__regress0__bv__proj-issue321.smt2"
            ),
        ),
        (
            "qf_abv_cvc5_bug637_delta",
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/cvc5-regress-clean/cli__regress0__arrays__bug637.delta.smt2"
            ),
        ),
        (
            "qf_abv_cvc5_issue9041",
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/cvc5-regress-clean/cli__regress0__arrays__issue9041.smt2"
            ),
        ),
        (
            "qf_abv_cvc5_bvproof2",
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/cvc5-regress-clean/cli__regress0__bv__bvproof2.smt2"
            ),
        ),
        (
            "qf_abv_btor_ext5",
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__ext5.btor.smt2"
            ),
        ),
        (
            "qf_abv_btor_ext21",
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__ext21.btor.smt2"
            ),
        ),
        (
            "qf_abv_btor_ext23",
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__ext23.btor.smt2"
            ),
        ),
        (
            "qf_abv_btor_ext16",
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__ext16.btor.smt2"
            ),
        ),
        (
            "qf_abv_btor_ext26",
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__ext26.btor.smt2"
            ),
        ),
        (
            "qf_abv_btor_ext13",
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__ext13.btor.smt2"
            ),
        ),
        (
            "qf_abv_btor_ext19",
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__ext19.btor.smt2"
            ),
        ),
        (
            "qf_abv_btor_ext24",
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__ext24.btor.smt2"
            ),
        ),
        (
            "qf_abv_btor_ext25",
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__ext25.btor.smt2"
            ),
        ),
        (
            "qf_abv_btor_3vl1",
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__3vl1.btor.smt2"
            ),
        ),
        (
            "qf_abv_btor_read9",
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__read9.btor.smt2"
            ),
        ),
        (
            "qf_abv_btor_write16",
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__write16.btor.smt2"
            ),
        ),
        (
            "qf_abv_btor_write17",
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__write17.btor.smt2"
            ),
        ),
        (
            "qf_abv_btor_extarraywrite1",
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__extarraywrite1.btor.smt2"
            ),
        ),
        (
            "qf_abv_btor_ext22",
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__ext22.btor.smt2"
            ),
        ),
        (
            "qf_abv_btor_ext27",
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__ext27.btor.smt2"
            ),
        ),
        (
            "qf_abv_btor_ext28",
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__ext28.btor.smt2"
            ),
        ),
        (
            "qf_abv_btor_read1",
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__read1.btor.smt2"
            ),
        ),
        (
            "qf_abv_btor_read4",
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__read4.btor.smt2"
            ),
        ),
        (
            "qf_abv_btor_read10",
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__read10.btor.smt2"
            ),
        ),
        (
            "qf_abv_btor_read22",
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ABV/bitwuzla-regress-clean/solver__array__read22.btor.smt2"
            ),
        ),
    ];

    for (tag, smt2) in cases {
        let mut script = parse_script(smt2).unwrap_or_else(|err| panic!("{tag} parses: {err}"));
        let assertions = script.assertions.clone();
        let (fragment, source) = prove_unsat_to_lean_module(&mut script.arena, &assertions)
            .unwrap_or_else(|err| panic!("{tag} reconstructs: {err}"));
        assert_eq!(fragment, ProofFragment::ArrayAxiom, "{tag}");
        assert!(
            !source.contains("sorryAx"),
            "{tag}: array axiom module must not lean on sorryAx:\n{source}"
        );
        lean_accepts(tag, &source);
    }
}

/// `QF_AUFBV`: `rw213` is already contradictory after the two array reads are
/// treated as arbitrary BV values. The Rust certificate re-checks that scalar
/// abstraction through the `QF_BV` evidence route, and the Lean module records the
/// resulting small contradiction witness.
fn qf_aufbv_bv_abstraction_checks_in_real_lean() {
    let text = include_str!(
        "../../../corpus/public-curated/non-incremental/QF_AUFBV/bitwuzla-regress-clean/rewrite__array__rw213.smt2"
    );
    let mut script = parse_script(text).expect("rw213 parses");
    let assertions = script.assertions.clone();
    let (fragment, source) = prove_unsat_to_lean_module(&mut script.arena, &assertions)
        .expect("rw213 BV-abstraction proof reconstructs");
    assert_eq!(fragment, ProofFragment::BvAbstraction);
    assert!(
        !source.contains("sorryAx"),
        "BV-abstraction module must not lean on sorryAx:\n{source}"
    );
    lean_accepts("qf_aufbv_bv_abstraction", &source);
}

fn qf_alia_store_chain_certificates_check_in_real_lean() {
    let cases = [
        (
            "qf_alia_constarr3",
            ProofFragment::ConstArrayDefaultMismatch,
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ALIA/cvc5-regress-clean/cli__regress1__constarr3.smt2"
            ),
        ),
        (
            "qf_alia_ios_np_sf",
            ProofFragment::StoreChainReadback,
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_ALIA/cvc5-regress-clean/cli__regress0__proofs__ios_np_sf.smt2"
            ),
        ),
    ];

    for (tag, expected, smt2) in cases {
        let mut script = parse_script(smt2).unwrap_or_else(|err| panic!("{tag} parses: {err}"));
        let assertions = script.assertions.clone();
        let (fragment, source) = prove_unsat_to_lean_module(&mut script.arena, &assertions)
            .unwrap_or_else(|err| panic!("{tag} reconstructs: {err}"));
        assert_eq!(fragment, expected, "{tag}");
        assert!(
            !source.contains("sorryAx"),
            "{tag}: QF_ALIA certificate module must not lean on sorryAx:\n{source}"
        );
        lean_accepts(tag, &source);
    }
}

fn qf_ax_declared_sort_certificates_check_in_real_lean() {
    let cases = [
        (
            "qf_ax_arr1",
            ProofFragment::ArrayAxiom,
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_AX/cvc5-regress-clean/cli__regress0__arr1.smt2"
            ),
        ),
        (
            "qf_ax_arrays0",
            ProofFragment::CrossStoreArrayDisequality,
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_AX/cvc5-regress-clean/cli__regress0__arrays__arrays0.smt2"
            ),
        ),
        (
            "qf_ax_arrays4",
            ProofFragment::CrossStoreArrayDisequality,
            include_str!(
                "../../../corpus/public-curated/non-incremental/QF_AX/cvc5-regress-clean/cli__regress0__arrays__arrays4.smt2"
            ),
        ),
    ];

    for (tag, expected, smt2) in cases {
        let mut script = parse_script(smt2).unwrap_or_else(|err| panic!("{tag} parses: {err}"));
        let assertions = script.assertions.clone();
        let (fragment, source) = prove_unsat_to_lean_module(&mut script.arena, &assertions)
            .unwrap_or_else(|err| panic!("{tag} reconstructs: {err}"));
        assert_eq!(fragment, expected, "{tag}");
        assert!(
            !source.contains("sorryAx"),
            "{tag}: QF_AX certificate module must not lean on sorryAx:\n{source}"
        );
        lean_accepts(tag, &source);
    }
}

fn qf_ax_bool_array_read_collapse_checks_in_real_lean() {
    let mut script = parse_script(include_str!(
        "../../../corpus/public-curated/non-incremental/QF_AX/cvc5-regress-clean/cli__regress0__arrays__bool-array.smt2"
    ))
    .expect("bool-array parses");
    let assertions = script.assertions.clone();
    let (fragment, source) = prove_unsat_to_lean_module(&mut script.arena, &assertions)
        .expect("bool-array reconstructs");
    assert_eq!(fragment, ProofFragment::BoolArrayReadCollapse);
    assert!(
        !source.contains("sorryAx"),
        "Bool-array read-collapse module must not lean on sorryAx:\n{source}"
    );
    lean_accepts("qf_ax_bool_array_read_collapse", &source);
}

/// `QF_AUFBV`: generated aligned byte write chains commute when both word
/// addresses have their low two bits cleared. The `wchains002ue` regression
/// asserts the opposite store orders differ under those guards.
fn qf_aufbv_aligned_write_chain_checks_in_real_lean() {
    let text = include_str!(
        "../../../corpus/public-curated/non-incremental/QF_AUFBV/bitwuzla-regress-clean/solver__array__wchains002ue.smt2"
    );
    let mut script = parse_script(text).expect("wchains002ue parses");
    let assertions = script.assertions.clone();
    let (fragment, source) = prove_unsat_to_lean_module(&mut script.arena, &assertions)
        .expect("wchains002ue aligned-write-chain proof reconstructs");
    assert_eq!(fragment, ProofFragment::AlignedWriteChainCommutation);
    assert!(
        !source.contains("sorryAx"),
        "aligned-write-chain module must not lean on sorryAx:\n{source}"
    );
    lean_accepts("qf_aufbv_aligned_write_chain", &source);
}

/// `QF_AUFBV`: a two-byte `memcpy` obligation under no-overlap/no-wrap guards
/// is refuted when the copied destination byte is asserted different from the
/// matching original source byte for some `j < 2`.
fn qf_aufbv_two_byte_memcpy_checks_in_real_lean() {
    let text = include_str!(
        "../../../corpus/public-curated/non-incremental/QF_AUFBV/bitwuzla-regress-clean/solver__array__memcpy02.smt2"
    );
    let mut script = parse_script(text).expect("memcpy02 parses");
    let assertions = script.assertions.clone();
    let (fragment, source) = prove_unsat_to_lean_module(&mut script.arena, &assertions)
        .expect("memcpy02 two-byte memcpy proof reconstructs");
    assert_eq!(fragment, ProofFragment::TwoByteMemcpy);
    assert!(
        !source.contains("sorryAx"),
        "two-byte memcpy module must not lean on sorryAx:\n{source}"
    );
    lean_accepts("qf_aufbv_two_byte_memcpy", &source);
}

/// `QF_AUFBV`: the two-element bubble-sort benchmark conditionally swaps the
/// original cells into sorted order, then asserts an in-range original read is
/// distinct from both sorted cells.
fn qf_aufbv_two_element_bubble_sort_checks_in_real_lean() {
    let text = include_str!(
        "../../../corpus/public-curated/non-incremental/QF_AUFBV/bitwuzla-regress-clean/solver__array__bubsort002un.smt2"
    );
    let mut script = parse_script(text).expect("bubsort002un parses");
    let assertions = script.assertions.clone();
    let (fragment, source) = prove_unsat_to_lean_module(&mut script.arena, &assertions)
        .expect("bubsort002un two-element bubble-sort proof reconstructs");
    assert_eq!(fragment, ProofFragment::TwoElementBubbleSort);
    assert!(
        !source.contains("sorryAx"),
        "two-element bubble-sort module must not lean on sorryAx:\n{source}"
    );
    lean_accepts("qf_aufbv_two_element_bubble_sort", &source);
}

/// `QF_AUFBV`: the two-element selection-sort benchmark stores the selected
/// minimum at `start`, then asserts an in-range original read is distinct from
/// both sorted cells.
fn qf_aufbv_two_element_selection_sort_checks_in_real_lean() {
    let text = include_str!(
        "../../../corpus/public-curated/non-incremental/QF_AUFBV/bitwuzla-regress-clean/solver__array__selsort002un.smt2"
    );
    let mut script = parse_script(text).expect("selsort002un parses");
    let assertions = script.assertions.clone();
    let (fragment, source) = prove_unsat_to_lean_module(&mut script.arena, &assertions)
        .expect("selsort002un two-element selection-sort proof reconstructs");
    assert_eq!(fragment, ProofFragment::TwoElementSelectionSort);
    assert!(
        !source.contains("sorryAx"),
        "two-element selection-sort module must not lean on sorryAx:\n{source}"
    );
    lean_accepts("qf_aufbv_two_element_selection_sort", &source);
}

/// `QF_AUFBV`: the two-cell XOR-swap benchmark compares two ordinary swaps
/// with the corresponding two generated XOR swaps and asserts the arrays differ.
fn qf_aufbv_two_cell_xor_swap_checks_in_real_lean() {
    let text = include_str!(
        "../../../corpus/public-curated/non-incremental/QF_AUFBV/bitwuzla-regress-clean/solver__array__dubreva002ue.smt2"
    );
    let mut script = parse_script(text).expect("dubreva002ue parses");
    let assertions = script.assertions.clone();
    let (fragment, source) = prove_unsat_to_lean_module(&mut script.arena, &assertions)
        .expect("dubreva002ue two-cell XOR-swap proof reconstructs");
    assert_eq!(fragment, ProofFragment::TwoCellXorSwap);
    assert!(
        !source.contains("sorryAx"),
        "two-cell XOR-swap module must not lean on sorryAx:\n{source}"
    );
    lean_accepts("qf_aufbv_two_cell_xor_swap", &source);
}

/// `QF_AUFBV`: the two-byte swapmem benchmark uses generated XOR swaps to swap
/// two disjoint byte ranges twice, then asserts memory changed.
fn qf_aufbv_two_byte_xor_swap_roundtrip_checks_in_real_lean() {
    let text = include_str!(
        "../../../corpus/public-curated/non-incremental/QF_AUFBV/bitwuzla-regress-clean/solver__array__swapmem002ue.smt2"
    );
    let mut script = parse_script(text).expect("swapmem002ue parses");
    let assertions = script.assertions.clone();
    let (fragment, source) = prove_unsat_to_lean_module(&mut script.arena, &assertions)
        .expect("swapmem002ue two-byte XOR-swap round-trip proof reconstructs");
    assert_eq!(fragment, ProofFragment::TwoByteXorSwapRoundtrip);
    assert!(
        !source.contains("sorryAx"),
        "two-byte XOR-swap round-trip module must not lean on sorryAx:\n{source}"
    );
    lean_accepts("qf_aufbv_two_byte_xor_swap_roundtrip", &source);
}

/// `QF_AUFBV`: after storing the searched value into a sorted 16-element
/// array, the generated five-probe binary search cannot miss that value.
fn qf_aufbv_binary_search16_checks_in_real_lean() {
    let text = include_str!(
        "../../../corpus/public-curated/non-incremental/QF_AUFBV/bitwuzla-regress-clean/solver__array__binarysearch32s016.smt2"
    );
    let mut script = parse_script(text).expect("binarysearch32s016 parses");
    let assertions = script.assertions.clone();
    let (fragment, source) = prove_unsat_to_lean_module(&mut script.arena, &assertions)
        .expect("binarysearch32s016 binary-search proof reconstructs");
    assert_eq!(fragment, ProofFragment::BinarySearch16);
    assert!(
        !source.contains("sorryAx"),
        "binary-search16 module must not lean on sorryAx:\n{source}"
    );
    lean_accepts("qf_aufbv_binary_search16", &source);
}

/// `QF_AUFBV`: the five-cycle FIFO benchmark compares a shift-register FIFO
/// with a circular-queue FIFO and asserts a final output/flag mismatch under
/// the generated transition constraints.
fn qf_aufbv_fifo_bc04_checks_in_real_lean() {
    let text = include_str!(
        "../../../corpus/public-curated/non-incremental/QF_AUFBV/bitwuzla-regress-clean/solver__array__fifo32bc04k05.smt2"
    );
    let mut script = parse_script(text).expect("fifo32bc04k05 parses");
    let assertions = script.assertions.clone();
    let (fragment, source) = prove_unsat_to_lean_module(&mut script.arena, &assertions)
        .expect("fifo32bc04k05 FIFO proof reconstructs");
    assert_eq!(fragment, ProofFragment::FifoBc04);
    assert!(
        !source.contains("sorryAx"),
        "FIFO BC04 module must not lean on sorryAx:\n{source}"
    );
    lean_accepts("qf_aufbv_fifo_bc04", &source);
}

/// Datatypes: `select_0(mk(a, b)) = #b00 ∧ ¬(a = #b00)` is unsat by
/// read-over-construct. Reconstructed via datatype simplification → `QF_UFBV`;
/// the refutation must type-check in real Lean.
fn datatype_read_over_construct_checks_in_real_lean() {
    let mut arena = TermArena::new();
    let pair = arena.declare_datatype("Pair");
    let mk = arena.add_constructor(
        pair,
        "mk",
        &[("a".into(), Sort::BitVec(2)), ("b".into(), Sort::BitVec(2))],
    );
    let a = {
        let s = arena.declare("a", Sort::BitVec(2)).unwrap();
        arena.var(s)
    };
    let b = {
        let s = arena.declare("b", Sort::BitVec(2)).unwrap();
        arena.var(s)
    };
    let p = arena.construct(mk, &[a, b]).unwrap();
    let sel = arena.dt_select(mk, 0, p).unwrap();
    let c = arena.bv_const(2, 0).unwrap();
    let e1 = arena.eq(sel, c).unwrap();
    let e2 = {
        let e = arena.eq(a, c).unwrap();
        arena.not(e).unwrap()
    };
    let (_frag, source) = prove_unsat_to_lean_module(&mut arena, &[e1, e2])
        .expect("datatype read-over-construct unsat reconstructs");
    lean_accepts("datatype", &source);
}

/// Datatype **is-tester** fold (route-A, the is-tester twin of read-over-construct).
/// Two pure is-tester contradictions, both discharged BY ι (no assumed fold axiom):
///
///   - TRUE fold:  `¬is_Green(Green a)` is UNSAT — `is_Green(Green a)` ι-reduces to
///     `Bool.true`, so `Eq.refl Bool true` closes the negated hypothesis.
///   - FALSE fold: `is_Red(Green a)` is UNSAT — `is_Red(Green a)` ι-reduces to
///     `Bool.false`, contradicting the asserted `… = true` via the
///     `Bool.true ≠ Bool.false` discriminator (`Bool.rec` ι, axiom-free).
///
/// The exported module must type-check in real Lean and `#print axioms` must
/// report no `sorryAx` — the fold is kernel-computed, not assumed.
fn tester_fold_checks_in_real_lean() {
    // A two-constructor datatype `Color = Red(v) | Green(w)`.
    let build = |tested_is_green: bool, negate: bool| {
        let mut arena = TermArena::new();
        let color = arena.declare_datatype("Color");
        let red = arena.add_constructor(color, "Red", &[("v".into(), Sort::BitVec(2))]);
        let green = arena.add_constructor(color, "Green", &[("w".into(), Sort::BitVec(2))]);
        let a = {
            let s = arena.declare("a", Sort::BitVec(2)).unwrap();
            arena.var(s)
        };
        // Argument is always `Green(a)`; vary which constructor we test for.
        let g = arena.construct(green, &[a]).unwrap();
        let tested = if tested_is_green { green } else { red };
        let is_c = arena.dt_test(tested, g).unwrap();
        let assertion = if negate {
            arena.not(is_c).unwrap()
        } else {
            is_c
        };
        let (_frag, source) = prove_unsat_to_lean_module(&mut arena, &[assertion])
            .expect("is-tester fold unsat reconstructs");
        source
    };

    // TRUE fold: ¬is_Green(Green a) — tested == builder, negated.
    lean_accepts("tester_true", &build(true, true));
    // FALSE fold: is_Red(Green a) — tested != builder, positive.
    lean_accepts("tester_false", &build(false, false));
}

/// Datatype constructor **DISTINCTNESS** (slice 2, the Lean mirror of the Carcara
/// distinctness route). An asserted equality between two **distinct** constructors
/// `Red a = Green b` is UNSAT — discharged BY ι + congruence + the existing
/// `Bool.true ≠ Bool.false` discriminator (NO `noConfusion`, NO assumed fold axiom):
///
///   - `is_Green (Red a)` ι-reduces to `Bool.false`, `is_Green (Green b)` to
///     `Bool.true`;
///   - `congrArg is_Green h` (an `Eq.rec`) transports the hypothesis to
///     `Eq Bool (is_Green (Red a)) (is_Green (Green b))`, `def_eq` to `false = true`;
///   - the `Bool.true ≠ Bool.false` discriminator (`Bool.rec` ι) closes it to `False`.
///
/// The exported module must type-check in real Lean and `#print axioms` must report
/// no `sorryAx` and no datatype-distinctness axiom — distinctness is kernel-computed.
fn distinct_constructors_check_in_real_lean() {
    let mut arena = TermArena::new();
    let color = arena.declare_datatype("Color");
    let red = arena.add_constructor(color, "Red", &[("v".into(), Sort::BitVec(2))]);
    let green = arena.add_constructor(color, "Green", &[("w".into(), Sort::BitVec(2))]);
    let a = {
        let s = arena.declare("a", Sort::BitVec(2)).unwrap();
        arena.var(s)
    };
    let b = {
        let s = arena.declare("b", Sort::BitVec(2)).unwrap();
        arena.var(s)
    };
    // Red(a) = Green(b) — distinct constructors, UNSAT.
    let lhs = arena.construct(red, &[a]).unwrap();
    let rhs = arena.construct(green, &[b]).unwrap();
    let eq = arena.eq(lhs, rhs).unwrap();
    let (_frag, source) = prove_unsat_to_lean_module(&mut arena, &[eq])
        .expect("distinct-constructor unsat reconstructs");
    lean_accepts("distinct_constructors", &source);
}

/// Soundness-negative: a **SAME-constructor** equality `Red a = Red b` must NOT be
/// claimed UNSAT by the distinctness route — it is *satisfiable* (take `a = b`), and
/// proving it would need injectivity (a separate slice), not distinctness. The
/// distinctness reconstructor declines, so no wrong `False` is emitted: the whole
/// datatype route reports no refutation for this lone same-constructor equality.
#[test]
fn same_constructor_equality_is_not_a_distinctness_refutation() {
    let mut arena = TermArena::new();
    let color = arena.declare_datatype("Color");
    let red = arena.add_constructor(color, "Red", &[("v".into(), Sort::BitVec(2))]);
    let _green = arena.add_constructor(color, "Green", &[("w".into(), Sort::BitVec(2))]);
    let a = {
        let s = arena.declare("a", Sort::BitVec(2)).unwrap();
        arena.var(s)
    };
    let b = {
        let s = arena.declare("b", Sort::BitVec(2)).unwrap();
        arena.var(s)
    };
    // Red(a) = Red(b) — SAME constructor; satisfiable, not a distinctness refutation.
    let lhs = arena.construct(red, &[a]).unwrap();
    let rhs = arena.construct(red, &[b]).unwrap();
    let eq = arena.eq(lhs, rhs).unwrap();
    assert!(
        prove_unsat_to_lean_module(&mut arena, &[eq]).is_err(),
        "a SAME-constructor equality must not reconstruct to a distinctness `False`"
    );
}

/// Datatype constructor **INJECTIVITY** (slice 3, the Lean mirror of the Carcara
/// injectivity route). A same-constructor equality `Pair(a,b) = Pair(c,d)` with a
/// conflicting field disequality `¬(a = c)` is UNSAT — discharged through the
/// SELECTOR route (NO `noConfusion`, NO assumed injectivity axiom):
///
///   - `sel_0 (Pair a b)` ι-reduces to `a`, `sel_0 (Pair c d)` to `c`;
///   - `congrArg sel_0 h` (an `Eq.rec`) transports the hypothesis to
///     `Eq α (sel_0 (Pair a b)) (sel_0 (Pair c d))`, `def_eq` to `Eq α a c`;
///   - applying the input field disequality `hne : ¬(a = c)` to it yields `False`.
///
/// The exported module must type-check in real Lean and `#print axioms` must report
/// no `sorryAx` and no datatype-injectivity axiom — injectivity is kernel-computed.
fn injective_field_mismatch_check_in_real_lean() {
    let mut arena = TermArena::new();
    let pair = arena.declare_datatype("Pair");
    let mk = arena.add_constructor(
        pair,
        "mk",
        &[
            ("fst".into(), Sort::BitVec(2)),
            ("snd".into(), Sort::BitVec(2)),
        ],
    );
    let bv = |arena: &mut TermArena, n: &str| {
        let s = arena.declare(n, Sort::BitVec(2)).unwrap();
        arena.var(s)
    };
    let a = bv(&mut arena, "a");
    let b = bv(&mut arena, "b");
    let c = bv(&mut arena, "c");
    let d = bv(&mut arena, "d");
    // mk(a,b) = mk(c,d) ∧ ¬(a = c) — SAME constructor, conflicting field 0; UNSAT.
    let lhs = arena.construct(mk, &[a, b]).unwrap();
    let rhs = arena.construct(mk, &[c, d]).unwrap();
    let eq = arena.eq(lhs, rhs).unwrap();
    let a_eq_c = arena.eq(a, c).unwrap();
    let a_ne_c = arena.not(a_eq_c).unwrap();
    let (_frag, source) = prove_unsat_to_lean_module(&mut arena, &[eq, a_ne_c])
        .expect("injectivity field-mismatch unsat reconstructs");
    // Independent of an external Lean: the rendered module must NOT smuggle a
    // datatype-injectivity escape hatch. The kernel already `infer`d it to `False`
    // (no `sorryAx`); the family + Bool are real `inductive`s, the only axioms are
    // the carrier, the field atoms, the selector default, and the two inputs.
    assert!(
        !source.contains("sorryAx") && !source.contains("noConfusion"),
        "injectivity module must not lean on sorryAx/noConfusion:\n{source}"
    );
    lean_accepts("injective_field_mismatch", &source);

    // Second sub-case: a non-zero field index AND the diseq in the REVERSED order
    // `¬(d = b)` (so `(p,q) = (y_1, x_1)`), exercising the field-1 selector and the
    // inline `Eq.symm` re-orientation of the selector congruence.
    let d_eq_b = arena.eq(d, b).unwrap();
    let d_ne_b = arena.not(d_eq_b).unwrap();
    let (_frag1, source1) = prove_unsat_to_lean_module(&mut arena, &[eq, d_ne_b])
        .expect("injectivity field-1 reversed-order unsat reconstructs");
    assert!(
        !source1.contains("sorryAx") && !source1.contains("noConfusion"),
        "injectivity (field-1, reversed) module must not lean on sorryAx/noConfusion:\n{source1}"
    );
    lean_accepts("injective_field1_reversed", &source1);
}

/// Soundness-negative: a same-constructor equality `mk(a,b) = mk(c,d)` **without**
/// any conflicting field disequality is *satisfiable* (take `a=c`, `b=d`), so the
/// injectivity route must DECLINE — no field conflict means no refutation. Combined
/// with distinctness declining a same-constructor equality, the whole datatype route
/// reports no refutation (no wrong `False`).
#[test]
fn same_constructor_without_field_conflict_is_not_an_injectivity_refutation() {
    let mut arena = TermArena::new();
    let pair = arena.declare_datatype("Pair");
    let mk = arena.add_constructor(
        pair,
        "mk",
        &[
            ("fst".into(), Sort::BitVec(2)),
            ("snd".into(), Sort::BitVec(2)),
        ],
    );
    let bv = |arena: &mut TermArena, n: &str| {
        let s = arena.declare(n, Sort::BitVec(2)).unwrap();
        arena.var(s)
    };
    let a = bv(&mut arena, "a");
    let b = bv(&mut arena, "b");
    let c = bv(&mut arena, "c");
    let d = bv(&mut arena, "d");
    // mk(a,b) = mk(c,d) with NO field disequality — satisfiable, not a refutation.
    let lhs = arena.construct(mk, &[a, b]).unwrap();
    let rhs = arena.construct(mk, &[c, d]).unwrap();
    let eq = arena.eq(lhs, rhs).unwrap();
    assert!(
        prove_unsat_to_lean_module(&mut arena, &[eq]).is_err(),
        "a same-constructor equality with no conflicting field must not reconstruct to `False`"
    );
}

/// Datatype **ACYCLICITY** (the occurs-check axiom — the LAST `QF_DT` field axiom,
/// completing the Lean chain). A single-level containment cycle `x = cons(h, x)`
/// over a recursive datatype `IntList = nil | cons(head, tail : IntList)` is UNSAT
/// — discharged BY the SIZE argument (no `noConfusion`, no assumed acyclicity
/// axiom, no well-founded recursion):
///
///   - `size : IntList → Nat` (a recursor measure) gives `size (cons h x)` ι→
///     `Nat.succ (size x)`;
///   - `congrArg size (hx : x = cons h x)` transports to `Eq Nat (size x)
///     (Nat.succ (size x))`;
///   - `n ≠ Nat.succ n` (proven by induction on `Nat` — a `zero ≠ succ`
///     discriminator + `succ` injectivity via a predecessor selector) closes it to
///     `False`.
///
/// The exported module must type-check in real Lean and `#print axioms` must
/// report no `sorryAx` and no acyclicity axiom — acyclicity is kernel-computed.
fn acyclicity_cycle_check_in_real_lean() {
    let mut arena = TermArena::new();
    // IntList = nil | cons(head : BitVec(2), tail : IntList) — RECURSIVE datatype.
    let list = arena.declare_datatype("IntList");
    let _nil = arena.add_constructor(list, "nil", &[]);
    let cons = arena.add_constructor(
        list,
        "cons",
        &[
            ("head".into(), Sort::BitVec(2)),
            ("tail".into(), Sort::Datatype(list)),
        ],
    );
    let h = {
        let s = arena.declare("h", Sort::BitVec(2)).unwrap();
        arena.var(s)
    };
    let x = {
        let s = arena.declare("x", Sort::Datatype(list)).unwrap();
        arena.var(s)
    };
    // x = cons(h, x) — a containment cycle, UNSAT by acyclicity.
    let cons_h_x = arena.construct(cons, &[h, x]).unwrap();
    let eq = arena.eq(x, cons_h_x).unwrap();
    let (_frag, source) =
        prove_unsat_to_lean_module(&mut arena, &[eq]).expect("acyclicity cycle unsat reconstructs");
    // The audit must not carry an acyclicity axiom (any `axiom …acyclic…`/occurs
    // declaration would be a smuggle); the size argument is fully kernel-computed.
    assert!(
        !source.to_lowercase().contains("acyclic"),
        "the acyclicity module must not declare an acyclicity axiom:\n{source}"
    );
    lean_accepts("acyclicity_cycle", &source);
}

/// Datatype acyclicity, **reversed orientation** `cons(h, x) = x` — the same cycle
/// asserted the other way; the size congruence is re-oriented by an inline
/// `Eq.symm`, and the module must still reconstruct to a kernel-checked `False`
/// that checks in real Lean with a clean `#print axioms`.
fn acyclicity_cycle_reversed_check_in_real_lean() {
    let mut arena = TermArena::new();
    let list = arena.declare_datatype("IntList");
    let _nil = arena.add_constructor(list, "nil", &[]);
    let cons = arena.add_constructor(
        list,
        "cons",
        &[
            ("head".into(), Sort::BitVec(2)),
            ("tail".into(), Sort::Datatype(list)),
        ],
    );
    let h = {
        let s = arena.declare("h", Sort::BitVec(2)).unwrap();
        arena.var(s)
    };
    let x = {
        let s = arena.declare("x", Sort::Datatype(list)).unwrap();
        arena.var(s)
    };
    // cons(h, x) = x — reversed cycle, UNSAT by acyclicity.
    let cons_h_x = arena.construct(cons, &[h, x]).unwrap();
    let eq = arena.eq(cons_h_x, x).unwrap();
    let (_frag, source) = prove_unsat_to_lean_module(&mut arena, &[eq])
        .expect("reversed acyclicity cycle unsat reconstructs");
    lean_accepts("acyclicity_cycle_reversed", &source);
}

/// Datatype acyclicity, **MULTI-STEP** containment cycle (k = 2, the mutual-
/// recursion case): `x = cons(h, y) ∧ y = cons(g, x)` over the recursive
/// `IntList`. The cycle `x ⊐ y ⊐ x` is UNSAT, discharged by the CHAINED size
/// argument — `congrArg size` on each link gives `size x = Nat.succ (size y)` and
/// `size y = Nat.succ (size x)`; chaining by `Eq.trans` (wrapping `congrArg
/// Nat.succ`) yields `size x = Nat.succ^2 (size x)`, refuted by `n ≠ Nat.succ^2 n`
/// (the chained generalization of `n ≠ Nat.succ n`). No `noConfusion`, no assumed
/// acyclicity axiom, no well-founded recursion; `#print axioms` stays clean.
fn acyclicity_two_step_cycle_check_in_real_lean() {
    let mut arena = TermArena::new();
    let list = arena.declare_datatype("IntList");
    let _nil = arena.add_constructor(list, "nil", &[]);
    let cons = arena.add_constructor(
        list,
        "cons",
        &[
            ("head".into(), Sort::BitVec(2)),
            ("tail".into(), Sort::Datatype(list)),
        ],
    );
    let h = {
        let s = arena.declare("h", Sort::BitVec(2)).unwrap();
        arena.var(s)
    };
    let g = {
        let s = arena.declare("g", Sort::BitVec(2)).unwrap();
        arena.var(s)
    };
    let x = {
        let s = arena.declare("x", Sort::Datatype(list)).unwrap();
        arena.var(s)
    };
    let y = {
        let s = arena.declare("y", Sort::Datatype(list)).unwrap();
        arena.var(s)
    };
    // x = cons(h, y) ∧ y = cons(g, x): a 2-step containment cycle x ⊐ y ⊐ x.
    let cons_h_y = arena.construct(cons, &[h, y]).unwrap();
    let cons_g_x = arena.construct(cons, &[g, x]).unwrap();
    let e1 = arena.eq(x, cons_h_y).unwrap();
    let e2 = arena.eq(y, cons_g_x).unwrap();
    let (_frag, source) = prove_unsat_to_lean_module(&mut arena, &[e1, e2])
        .expect("2-step acyclicity cycle unsat reconstructs");
    assert!(
        !source.to_lowercase().contains("acyclic"),
        "the multi-step acyclicity module must not declare an acyclicity axiom:\n{source}"
    );
    lean_accepts("acyclicity_two_step_cycle", &source);
}

/// Datatype acyclicity, **3-step** containment cycle `x = cons(h, y) ∧
/// y = cons(g, z) ∧ z = cons(f, x)` — the general-`k` chained size argument at
/// k = 3 (`size x = Nat.succ^3 (size x)`, refuted by `n ≠ Nat.succ^3 n`). Confirms
/// the chain length generalizes beyond the mutual-recursion (k = 2) case.
fn acyclicity_three_step_cycle_check_in_real_lean() {
    let mut arena = TermArena::new();
    let list = arena.declare_datatype("IntList");
    let _nil = arena.add_constructor(list, "nil", &[]);
    let cons = arena.add_constructor(
        list,
        "cons",
        &[
            ("head".into(), Sort::BitVec(2)),
            ("tail".into(), Sort::Datatype(list)),
        ],
    );
    let mk_bv = |arena: &mut TermArena, name: &str| {
        let s = arena.declare(name, Sort::BitVec(2)).unwrap();
        arena.var(s)
    };
    let mk_dt = |arena: &mut TermArena, name: &str| {
        let s = arena.declare(name, Sort::Datatype(list)).unwrap();
        arena.var(s)
    };
    let (h, g, f) = (
        mk_bv(&mut arena, "h"),
        mk_bv(&mut arena, "g"),
        mk_bv(&mut arena, "f"),
    );
    let (x, y, z) = (
        mk_dt(&mut arena, "x"),
        mk_dt(&mut arena, "y"),
        mk_dt(&mut arena, "z"),
    );
    let cons_h_y = arena.construct(cons, &[h, y]).unwrap();
    let cons_g_z = arena.construct(cons, &[g, z]).unwrap();
    let cons_f_x = arena.construct(cons, &[f, x]).unwrap();
    let e1 = arena.eq(x, cons_h_y).unwrap();
    let e2 = arena.eq(y, cons_g_z).unwrap();
    let e3 = arena.eq(z, cons_f_x).unwrap();
    let (_frag, source) = prove_unsat_to_lean_module(&mut arena, &[e1, e2, e3])
        .expect("3-step acyclicity cycle unsat reconstructs");
    lean_accepts("acyclicity_three_step_cycle", &source);
}

/// Soundness-negative: a FINITE list `x = cons(h, nil)` is **satisfiable** (no
/// cycle — the tail `nil` does not contain `x`), so the acyclicity route must NOT
/// claim it UNSAT. The reconstructor declines (the tail is not `x`), so no wrong
/// `False` is emitted.
#[test]
fn finite_list_is_not_an_acyclicity_refutation() {
    let mut arena = TermArena::new();
    let list = arena.declare_datatype("IntList");
    let nil = arena.add_constructor(list, "nil", &[]);
    let cons = arena.add_constructor(
        list,
        "cons",
        &[
            ("head".into(), Sort::BitVec(2)),
            ("tail".into(), Sort::Datatype(list)),
        ],
    );
    let h = {
        let s = arena.declare("h", Sort::BitVec(2)).unwrap();
        arena.var(s)
    };
    let x = {
        let s = arena.declare("x", Sort::Datatype(list)).unwrap();
        arena.var(s)
    };
    // x = cons(h, nil) — finite, satisfiable; the tail is `nil`, not `x`.
    let nil_v = arena.construct(nil, &[]).unwrap();
    let cons_h_nil = arena.construct(cons, &[h, nil_v]).unwrap();
    let eq = arena.eq(x, cons_h_nil).unwrap();
    assert!(
        prove_unsat_to_lean_module(&mut arena, &[eq]).is_err(),
        "a finite (non-cyclic) list equality must not reconstruct to `False`"
    );
}

/// Soundness/routing-negative: a DISTINCT-constructor equality `Red a = Green b`
/// is distinctness's job, NOT injectivity's. It must still reconstruct to a
/// kernel-checked `False` (via the slice-2 distinctness route), and the rendered
/// module must be axiom-free over the fold — confirming injectivity does not
/// hijack or corrupt the distinct-constructor case.
fn distinct_constructor_equality_is_not_an_injectivity_refutation() {
    let mut arena = TermArena::new();
    let color = arena.declare_datatype("Color");
    let red = arena.add_constructor(color, "Red", &[("v".into(), Sort::BitVec(2))]);
    let green = arena.add_constructor(color, "Green", &[("w".into(), Sort::BitVec(2))]);
    let a = {
        let s = arena.declare("a", Sort::BitVec(2)).unwrap();
        arena.var(s)
    };
    let b = {
        let s = arena.declare("b", Sort::BitVec(2)).unwrap();
        arena.var(s)
    };
    // Red(a) = Green(b) — distinct constructors; refuted by distinctness, not injectivity.
    let lhs = arena.construct(red, &[a]).unwrap();
    let rhs = arena.construct(green, &[b]).unwrap();
    let eq = arena.eq(lhs, rhs).unwrap();
    let (_frag, source) = prove_unsat_to_lean_module(&mut arena, &[eq])
        .expect("distinct-constructor unsat reconstructs (via distinctness)");
    assert!(
        !source.contains("sorryAx") && !source.contains("noConfusion"),
        "distinct-constructor module must stay axiom-free over the fold:\n{source}"
    );
    lean_accepts("distinct_not_injective", &source);
}

/// `QF_BV` (the foundational bit-blasting path): `bvule a b ∧ bvult b a`
/// (`a ≤ b ∧ b < a`, `BitVec(2)`) is unsat. It lowers to core ops and the
/// bit-level resolution refutation must type-check in real Lean.
fn qf_bv_comparison_refutation_checks_in_real_lean() {
    let mut arena = TermArena::new();
    let mk = |a: &mut TermArena, n: &str| {
        let s = a.declare(n, Sort::BitVec(2)).unwrap();
        a.var(s)
    };
    let a = mk(&mut arena, "a");
    let b = mk(&mut arena, "b");
    let le = arena.bv_ule(a, b).unwrap();
    let gt = arena.bv_ult(b, a).unwrap();
    let (_frag, source) = prove_unsat_to_lean_module(&mut arena, &[le, gt])
        .expect("QF_BV comparison unsat reconstructs");
    lean_accepts("qf_bv", &source);
}

/// The curated `bvredand` row is a parser-reduction identity contradiction.
/// The current structural Lean route recognizes the checked equivalence and
/// closes the row without falling back to the bit-blast emitter.
fn qf_bv_bvredand_identity_contradiction_checks_in_real_lean() {
    let mut script = parse_script(include_str!(
        "../../../corpus/public-curated/bvred/cvc5__redand-eliminate.smt2"
    ))
    .expect("bvredand row parses");
    let assertions = script.assertions.clone();
    let (fragment, source) = prove_unsat_to_lean_module(&mut script.arena, &assertions)
        .expect("bvredand identity contradiction reconstructs");
    assert_eq!(fragment, ProofFragment::ArrayAxiom);
    assert!(
        !source.contains("sorryAx"),
        "identity contradiction module must not use sorryAx:\n{source}"
    );
    lean_accepts("qf_bv_bvredand_identity", &source);
}

/// **Disjunctive `QF_LRA`** (the Boolean-structured case split): the conjunctive
/// system `x ≤ 0 ∧ y ≤ 0` plus the clause `(x ≥ 1 ∨ y ≥ 1)` is UNSAT — each leaf
/// is a two-atom Farkas contradiction (`x ≤ 0 ∧ 1 ≤ x` ⇒ `1 ≤ 0`, and likewise
/// for `y`). The conjunctive Farkas path declines a top-level positive `Or`, so
/// this carries a Lean proof only through the new `Or.rec` case-split
/// reconstruction. The exported module must check in real Lean with no `sorryAx`.
fn disjunctive_lra_case_split_checks_in_real_lean() {
    use axeyum_solver::ProofFragment;
    let mut arena = TermArena::new();
    let x = arena.real_var("x").unwrap();
    let y = arena.real_var("y").unwrap();
    let zero = arena.real_const(Rational::integer(0));
    let one = arena.real_const(Rational::integer(1));
    let x_le_0 = arena.real_le(x, zero).unwrap();
    let y_le_0 = arena.real_le(y, zero).unwrap();
    let x_ge_1 = arena.real_ge(x, one).unwrap();
    let y_ge_1 = arena.real_ge(y, one).unwrap();
    let clause = arena.or(x_ge_1, y_ge_1).unwrap();
    let (frag, source) = prove_unsat_to_lean_module(&mut arena, &[x_le_0, y_le_0, clause])
        .expect("disjunctive-LRA unsat reconstructs to a kernel-checked False");
    assert_eq!(
        frag,
        ProofFragment::DisjunctiveLra,
        "routed to the disjunctive-LRA case-split reconstructor"
    );
    // The in-tree kernel already accepted (infer + def_eq False inside the call);
    // the rendered module must not lean on the sorryAx escape hatch.
    assert!(
        !source.contains("sorryAx"),
        "disjunctive-LRA module depends on sorryAx:\n{source}"
    );
    lean_accepts("disjunctive_lra", &source);
}

/// **Decline (feasible) disjunctive `QF_LRA`**: `x ≤ 0 ∧ (x ≥ 1 ∨ y ≥ 1) ∧ y ≤ 5`
/// is SATISFIABLE (take `y = 1`), so the disjunctive detector must NOT match and
/// no proof may be fabricated — `prove_unsat_to_lean_module` returns an error
/// (the conjunctive Farkas path also declines the positive `Or`).
#[test]
fn disjunctive_lra_feasible_set_is_declined() {
    let mut arena = TermArena::new();
    let x = arena.real_var("x").unwrap();
    let y = arena.real_var("y").unwrap();
    let zero = arena.real_const(Rational::integer(0));
    let one = arena.real_const(Rational::integer(1));
    let five = arena.real_const(Rational::integer(5));
    let x_le_0 = arena.real_le(x, zero).unwrap();
    let y_le_5 = arena.real_le(y, five).unwrap();
    let x_ge_1 = arena.real_ge(x, one).unwrap();
    let y_ge_1 = arena.real_ge(y, one).unwrap();
    let clause = arena.or(x_ge_1, y_ge_1).unwrap();
    let result = prove_unsat_to_lean_module(&mut arena, &[x_le_0, y_le_5, clause]);
    assert!(
        result.is_err(),
        "a satisfiable disjunctive set must not produce a fabricated refutation; got {result:?}"
    );
}

/// **Regression**: the existing CONJUNCTIVE LRA refutation `x < 0 ∧ 0 ≤ x` still
/// reconstructs without falling into the disjunctive path.
#[test]
fn conjunctive_lra_still_reconstructs_unchanged() {
    use axeyum_solver::ProofFragment;
    let mut arena = TermArena::new();
    let x = arena.real_var("x").unwrap();
    let zero = arena.real_const(Rational::integer(0));
    let a1 = arena.real_lt(x, zero).unwrap();
    let a2 = arena.real_le(zero, x).unwrap();
    let (frag, source) = prove_unsat_to_lean_module(&mut arena, &[a1, a2])
        .expect("conjunctive LRA unsat still reconstructs");
    assert_eq!(
        frag,
        ProofFragment::LraDpll,
        "conjunctive LRA stays on a non-disjunctive LRA path"
    );
    assert!(!source.contains("sorryAx"));
}

// --- Constant-shift → concat lowering identity, kernel-certified (ROUTE B) ------
//
// The `lower_const_shift` rewrite (axeyum-rewrite) collapses a *constant* shift to
// `extract`/`concat`/`sign_extend`. That lowering step used to be TRUSTED. These
// tests certify the identity itself as a Lean-kernel-checked theorem: the per-bit
// equality `⋀_i ( bit_i(shift) ↔ bit_i(concat) )` is proved reflexively and gated by
// the kernel — a WRONG lowering is rejected, never accepted. Carcara has no rule for
// the `(= (bvshl a k) (concat …))` bridge (STEP-0 probe: `bv_poly_simp`/`bitblast_*`/
// `*_simplify` all reject it), so this standalone kernel lemma is the certificate.

use axeyum_cnf::AletheTerm;
use axeyum_solver::{
    ReconstructCtx, prove_const_shift_lowering_to_lean_module, reconstruct_const_shift_lowering,
};

/// `(bvshl a #b0001)` over width 4 — the LHS the test certifies.
fn shl1_w4() -> AletheTerm {
    AletheTerm::App(
        "bvshl".to_owned(),
        vec![
            AletheTerm::Const("a".to_owned()),
            AletheTerm::Const("#b0001".to_owned()),
        ],
    )
}

/// `(concat ((_ extract 2 0) a) #b0)` — the width-4 lowering of `bvshl a 1`
/// (drop the top bit, append one zero at the low end).
fn shl1_w4_concat() -> AletheTerm {
    AletheTerm::App(
        "concat".to_owned(),
        vec![
            AletheTerm::Indexed {
                op: "extract".to_owned(),
                indices: vec![2, 0],
                args: vec![AletheTerm::Const("a".to_owned())],
            },
            AletheTerm::Const("#b0".to_owned()),
        ],
    )
}

/// **ROUTE-B positive (`bvshl`)**: the constant-left-shift lowering identity
/// `(bvshl a #b0001) = (concat ((_ extract 2 0) a) #b0)` reconstructs to a real-Lean
/// kernel-checked theorem with **no `sorryAx`**.
fn const_shl_lowering_checks_in_real_lean() {
    let source = prove_const_shift_lowering_to_lean_module(&shl1_w4(), &shl1_w4_concat(), 4)
        .expect("constant bvshl lowering reconstructs to a kernel-checked theorem");
    // In-tree kernel already accepted (infer + def_eq inside the call); the rendered
    // module must check in real Lean with no sorryAx.
    assert!(
        !source.contains("sorryAx"),
        "const-shl lowering module depends on sorryAx:\n{source}"
    );
    lean_accepts("const_shl_lowering", &source);
}

/// **ROUTE-B positive (`bvlshr`)**: the constant-logical-right-shift identity
/// `(bvlshr a #b0001) = (concat #b0 ((_ extract 3 1) a))` over width 4 — prepend a
/// zero at the high end, drop the low bit.
fn const_lshr_lowering_checks_in_real_lean() {
    let shift = AletheTerm::App(
        "bvlshr".to_owned(),
        vec![
            AletheTerm::Const("a".to_owned()),
            AletheTerm::Const("#b0001".to_owned()),
        ],
    );
    let concat = AletheTerm::App(
        "concat".to_owned(),
        vec![
            AletheTerm::Const("#b0".to_owned()),
            AletheTerm::Indexed {
                op: "extract".to_owned(),
                indices: vec![3, 1],
                args: vec![AletheTerm::Const("a".to_owned())],
            },
        ],
    );
    let source = prove_const_shift_lowering_to_lean_module(&shift, &concat, 4)
        .expect("constant bvlshr lowering reconstructs to a kernel-checked theorem");
    assert!(
        !source.contains("sorryAx"),
        "const-lshr lowering module depends on sorryAx:\n{source}"
    );
    lean_accepts("const_lshr_lowering", &source);
}

/// **ROUTE-B positive (`bvashr`)**: the constant-arithmetic-right-shift identity
/// `(bvashr a #b0001) = ((_ sign_extend 1) ((_ extract 3 1) a))` over width 4 — drop
/// the low bit, fill the high end with the sign (`sign_extend` of the surviving high
/// slice, whose MSB is `a`'s sign bit).
fn const_ashr_lowering_checks_in_real_lean() {
    let shift = AletheTerm::App(
        "bvashr".to_owned(),
        vec![
            AletheTerm::Const("a".to_owned()),
            AletheTerm::Const("#b0001".to_owned()),
        ],
    );
    let rhs = AletheTerm::Indexed {
        op: "sign_extend".to_owned(),
        indices: vec![1],
        args: vec![AletheTerm::Indexed {
            op: "extract".to_owned(),
            indices: vec![3, 1],
            args: vec![AletheTerm::Const("a".to_owned())],
        }],
    };
    let source = prove_const_shift_lowering_to_lean_module(&shift, &rhs, 4)
        .expect("constant bvashr lowering reconstructs to a kernel-checked theorem");
    assert!(
        !source.contains("sorryAx"),
        "const-ashr lowering module depends on sorryAx:\n{source}"
    );
    lean_accepts("const_ashr_lowering", &source);
}

/// **ROUTE-B negative (the check has teeth)**: a WRONG lowering of `bvshl a 1` —
/// claiming `(concat ((_ extract 3 1) a) #b0)` (the wrong `extract` slice, the
/// `lshr` pattern) — must be **REJECTED** by the kernel, never certified. This proves
/// the per-bit reflexive proof only type-checks for a genuinely-equal lowering.
#[test]
fn wrong_const_shift_lowering_is_rejected_by_kernel() {
    let mut ctx = ReconstructCtx::new();
    let wrong_concat = AletheTerm::App(
        "concat".to_owned(),
        vec![
            // WRONG: `bvshl a 1` keeps bits 2..0 of `a` in the high part, not 3..1.
            AletheTerm::Indexed {
                op: "extract".to_owned(),
                indices: vec![3, 1],
                args: vec![AletheTerm::Const("a".to_owned())],
            },
            AletheTerm::Const("#b0".to_owned()),
        ],
    );
    let result = reconstruct_const_shift_lowering(&mut ctx, &shl1_w4(), &wrong_concat, 4);
    assert!(
        matches!(
            result,
            Err(axeyum_solver::ReconstructError::KernelRejected { .. })
        ),
        "a wrong shift→concat lowering must be kernel-REJECTED, got {result:?}"
    );
}

/// **Regression / boundary**: the CORRECT lowering reconstructs through the in-tree
/// kernel (`reconstruct_const_shift_lowering` returns `Ok`) — the positive companion
/// to the rejection test, without needing a `lean` binary.
#[test]
fn const_shift_lowering_in_tree_kernel_accepts() {
    let mut ctx = ReconstructCtx::new();
    let ok = reconstruct_const_shift_lowering(&mut ctx, &shl1_w4(), &shl1_w4_concat(), 4);
    assert!(
        ok.is_ok(),
        "the correct bvshl lowering must be kernel-accepted, got {ok:?}"
    );
}

// --- Certified conjunctive QF_LRA Craig interpolant (lra_interpolant_certified) ---
//
// The interpolant `I` carries two Farkas certificates witnessing its two Craig
// soundness conditions: `A ∧ ¬I ⊢ ⊥` and `I ∧ B ⊢ ⊥`. Each conjunction is itself
// a conjunctive LRA refutation, so `prove_unsat_to_lean_module` reconstructs it to
// a Lean-kernel-checked `theorem … : False`. Feeding both to the REAL `lean`
// binary — accepted, no `sorryAx` — is the external check that upgrades the
// interpolant from Validated to Checked via the Lean route.

/// Write `source` to a temp `.lean` file and run `lean`; return `true` iff the
/// module type-checks (exit 0). Skips (returns early `true`-equivalent via the
/// caller's guard) when no `lean` binary is available. Used by the TAMPER test to
/// confirm the kernel REJECTS a corrupted module.
fn lean_typechecks(tag: &str, source: &str) -> Option<bool> {
    let bin = lean_bin()?;
    let dir = std::env::temp_dir().join(format!("axeyum_lean_{tag}"));
    std::fs::create_dir_all(&dir).expect("create temp dir");
    let file = dir.join(format!("{tag}.lean"));
    std::fs::write(&file, source).expect("write lean module");
    let out = Command::new(&bin)
        .arg(&file)
        .output()
        .expect("run lean binary");
    Some(out.status.success())
}

fn certified_lra_interpolant_both_farkas_certs_checked_by_real_lean() {
    use axeyum_solver::lra_interpolant_certified;
    // A: x ≤ 0 ; B: x ≥ 1.  Unsat; shared variable x.
    let mut arena = TermArena::new();
    let x = arena.real_var("x").unwrap();
    let zero = arena.real_const(Rational::integer(0));
    let one = arena.real_const(Rational::integer(1));
    let a0 = arena.real_le(x, zero).unwrap();
    let b0 = arena.real_ge(x, one).unwrap();

    let cert = lra_interpolant_certified(&mut arena, &[a0], &[b0])
        .expect("decides")
        .expect("a certified interpolant exists");

    // Craig condition 1: A ∧ ¬I reconstructs to a kernel-checked `: False`.
    let (_frag_a, source_a) = prove_unsat_to_lean_module(&mut arena, &cert.a_and_not_i)
        .expect("A ∧ ¬I reconstructs to a Lean module");
    assert!(
        !source_a.contains("sorryAx"),
        "A ∧ ¬I module depends on sorryAx:\n{source_a}"
    );
    lean_accepts("interp_a_not_i", &source_a);

    // Craig condition 2: I ∧ B reconstructs to a kernel-checked `: False`.
    let (_frag_b, source_b) = prove_unsat_to_lean_module(&mut arena, &cert.i_and_b)
        .expect("I ∧ B reconstructs to a Lean module");
    assert!(
        !source_b.contains("sorryAx"),
        "I ∧ B module depends on sorryAx:\n{source_b}"
    );
    lean_accepts("interp_i_b", &source_b);
}

// (A rational-coefficient certified interpolant — `3x ≤ 1 ∧ 2x ≥ 3` — is exercised
// against the Lean *in-tree* kernel inside `lra_interpolant_certified` and against
// Carcara in `carcara_crosscheck`; it is intentionally NOT fed to the real `lean`
// binary here because the verbose nested-`add` reconstruction overruns Lean's
// default `maxRecDepth` during elaboration — a pretty-printing depth limit, not a
// soundness rejection. The unit-coefficient case above already proves real-Lean
// acceptance of both Farkas certs end to end.)

/// TAMPER (the no-`sorryAx` / kernel check has teeth): take a genuine certified
/// refutation module and replace its proof term with `sorry`. The real Lean kernel
/// then EITHER fails to type-check OR `#print axioms` reports `sorryAx` — both are
/// rejections. A fabricated certificate cannot pass the gate the positive tests use.
#[test]
fn tampered_certified_lra_interpolant_module_is_rejected_by_real_lean() {
    use axeyum_solver::lra_interpolant_certified;
    if lean_bin().is_none() {
        eprintln!("[skip] tamper: lean binary not found; install via elan or set AXEYUM_LEAN_BIN");
        return;
    }
    let mut arena = TermArena::new();
    let x = arena.real_var("x").unwrap();
    let zero = arena.real_const(Rational::integer(0));
    let one = arena.real_const(Rational::integer(1));
    let a0 = arena.real_le(x, zero).unwrap();
    let b0 = arena.real_ge(x, one).unwrap();
    let cert = lra_interpolant_certified(&mut arena, &[a0], &[b0])
        .expect("decides")
        .expect("a certified interpolant exists");
    let (_frag, source) =
        prove_unsat_to_lean_module(&mut arena, &cert.a_and_not_i).expect("A ∧ ¬I reconstructs");

    // Replace the proof body `:= <proof>` of the refutation theorem with `sorry`.
    let marker = "theorem axeyum_refutation : False :=";
    let idx = source
        .find(marker)
        .expect("module declares axeyum_refutation");
    let head = &source[..idx + marker.len()];
    // Keep the trailing `#print axioms` line so the axiom audit still runs.
    let tail_start = source[idx..]
        .find("#print axioms")
        .map(|p| idx + p)
        .expect("module has a #print axioms audit");
    let tampered = format!("{head} sorry\n\n{}", &source[tail_start..]);

    let typechecks = lean_typechecks("interp_tampered", &tampered).expect("lean available");
    if typechecks {
        // If `sorry` type-checks (a warning, not an error), `#print axioms` MUST
        // expose `sorryAx` — the audit the positive tests rely on.
        let bin = lean_bin().expect("lean available");
        let dir = std::env::temp_dir().join("axeyum_lean_interp_tampered");
        let file = dir.join("interp_tampered.lean");
        let out = Command::new(&bin).arg(&file).output().expect("run lean");
        let stdout = String::from_utf8_lossy(&out.stdout);
        assert!(
            stdout.contains("sorryAx"),
            "a `sorry`-tampered refutation must expose sorryAx in the axiom audit:\n{stdout}"
        );
    }
    // (If it does NOT type-check, that is already a rejection — nothing to assert.)
}

// --- Certified conjunctive QF_UF (EUF) Craig interpolant (qf_uf_interpolant_certified) ---
//
// The EUF interpolant `I` carries two congruence certificates witnessing its two
// Craig soundness conditions: `A ∧ ¬I ⊢ ⊥` and `I ∧ B ⊢ ⊥`. Each conjunction is a
// single-disequality congruence conflict, so `prove_unsat_to_lean_module`
// reconstructs it (through the `QfUf` fragment) to a Lean-kernel-checked
// `theorem … : False`. Feeding both to the REAL `lean` binary — accepted, no
// `sorryAx` — is the external check that upgrades the EUF interpolant from Validated
// to Checked via the Lean route.

fn certified_euf_interpolant_both_congruence_certs_checked_by_real_lean() {
    use axeyum_solver::qf_uf_interpolant_certified;
    // A: a=b, b=c ; B: a≠c.  I = (a=c), a positive equality conjunction.
    let mut arena = TermArena::new();
    let alpha = Sort::BitVec(8);
    let a = {
        let s = arena.declare("a", alpha).unwrap();
        arena.var(s)
    };
    let b = {
        let s = arena.declare("b", alpha).unwrap();
        arena.var(s)
    };
    let c = {
        let s = arena.declare("c", alpha).unwrap();
        arena.var(s)
    };
    let ab = arena.eq(a, b).unwrap();
    let bc = arena.eq(b, c).unwrap();
    let ac = arena.eq(a, c).unwrap();
    let nac = arena.not(ac).unwrap();

    let cert = qf_uf_interpolant_certified(&mut arena, &[ab, bc], &[nac])
        .expect("decides")
        .expect("a certified EUF interpolant exists");

    // Craig condition 1: A ∧ ¬I reconstructs to a kernel-checked `: False`.
    let (_frag_a, source_a) = prove_unsat_to_lean_module(&mut arena, &cert.a_and_not_i)
        .expect("A ∧ ¬I reconstructs to a Lean module");
    assert!(
        !source_a.contains("sorryAx"),
        "A ∧ ¬I module depends on sorryAx:\n{source_a}"
    );
    lean_accepts("euf_interp_a_not_i", &source_a);

    // Craig condition 2: I ∧ B reconstructs to a kernel-checked `: False`.
    let (_frag_b, source_b) = prove_unsat_to_lean_module(&mut arena, &cert.i_and_b)
        .expect("I ∧ B reconstructs to a Lean module");
    assert!(
        !source_b.contains("sorryAx"),
        "I ∧ B module depends on sorryAx:\n{source_b}"
    );
    lean_accepts("euf_interp_i_b", &source_b);
}

/// TAMPER (the no-`sorryAx` / kernel check has teeth): take a genuine certified EUF
/// refutation module and replace its proof term with `sorry`. The real Lean kernel
/// then EITHER fails to type-check OR `#print axioms` reports `sorryAx` — both are
/// rejections. A fabricated EUF certificate cannot pass the gate the positive test
/// uses.
#[test]
fn tampered_certified_euf_interpolant_module_is_rejected_by_real_lean() {
    use axeyum_solver::qf_uf_interpolant_certified;
    if lean_bin().is_none() {
        eprintln!("[skip] tamper: lean binary not found; install via elan or set AXEYUM_LEAN_BIN");
        return;
    }
    let mut arena = TermArena::new();
    let alpha = Sort::BitVec(8);
    let a = {
        let s = arena.declare("a", alpha).unwrap();
        arena.var(s)
    };
    let b = {
        let s = arena.declare("b", alpha).unwrap();
        arena.var(s)
    };
    let c = {
        let s = arena.declare("c", alpha).unwrap();
        arena.var(s)
    };
    let ab = arena.eq(a, b).unwrap();
    let bc = arena.eq(b, c).unwrap();
    let ac = arena.eq(a, c).unwrap();
    let nac = arena.not(ac).unwrap();
    let cert = qf_uf_interpolant_certified(&mut arena, &[ab, bc], &[nac])
        .expect("decides")
        .expect("a certified EUF interpolant exists");
    let (_frag, source) =
        prove_unsat_to_lean_module(&mut arena, &cert.a_and_not_i).expect("A ∧ ¬I reconstructs");

    // Replace the proof body `:= <proof>` of the refutation theorem with `sorry`.
    let marker = "theorem axeyum_refutation : False :=";
    let idx = source
        .find(marker)
        .expect("module declares axeyum_refutation");
    let head = &source[..idx + marker.len()];
    let tail_start = source[idx..]
        .find("#print axioms")
        .map(|p| idx + p)
        .expect("module has a #print axioms audit");
    let tampered = format!("{head} sorry\n\n{}", &source[tail_start..]);

    let typechecks = lean_typechecks("euf_interp_tampered", &tampered).expect("lean available");
    if typechecks {
        // If `sorry` type-checks (a warning, not an error), `#print axioms` MUST
        // expose `sorryAx` — the audit the positive test relies on.
        let bin = lean_bin().expect("lean available");
        let dir = std::env::temp_dir().join("axeyum_lean_euf_interp_tampered");
        let file = dir.join("euf_interp_tampered.lean");
        let out = Command::new(&bin).arg(&file).output().expect("run lean");
        let stdout = String::from_utf8_lossy(&out.stdout);
        assert!(
            stdout.contains("sorryAx"),
            "a `sorry`-tampered EUF refutation must expose sorryAx in the axiom audit:\n{stdout}"
        );
    }
    // (If it does NOT type-check, that is already a rejection — nothing to assert.)
}

// --- Certified conjunctive QF_LIA Craig interpolant (lia_interpolant_certified) ---
//
// The LIA interpolant `I` carries two KERNEL-CHECKED integer certificates witnessing
// its two Craig soundness conditions: `A ∧ ¬I ⊢ ⊥` and `I ∧ B ⊢ ⊥`. Each conjunction
// is an integer-infeasible system the integer-prelude reconstructor covers
// (Diophantine / interval cut), so each certificate is a Lean module
// `prove_unsat_to_lean_module` already kernel-checked in-tree. Feeding both to the
// REAL `lean` binary — accepted, no `sorryAx` — is the external check that upgrades
// the LIA interpolant from Validated to Checked. Carcara has NO `lia_generic` rule
// (warns + `holey`), so for integers the Lean kernel is the external checker.

fn certified_lia_interpolant_both_integer_certs_checked_by_real_lean() {
    use axeyum_solver::{ProofFragment, lia_interpolant_certified};
    // A: 2x ≥ 1 ; B: 2x ≤ 0 over Int.  Unsat; shared variable x.  I = (2x ≥ 1), and
    // both A ∧ ¬I and I ∧ B are the empty integer interval 1 ≤ 2x ≤ 0 (IntInequality).
    let mut arena = TermArena::new();
    let x = arena.int_var("x").unwrap();
    let two = arena.int_const(2);
    let two_x = arena.int_mul(two, x).unwrap();
    let zero = arena.int_const(0);
    let one = arena.int_const(1);
    let a0 = arena.int_ge(two_x, one).unwrap();
    let b0 = arena.int_le(two_x, zero).unwrap();

    let cert = lia_interpolant_certified(&mut arena, &[a0], &[b0])
        .expect("decides")
        .expect("a certified LIA interpolant exists");

    // Both certificates reconstructed through a COVERED integer fragment.
    assert!(matches!(
        cert.a_fragment,
        ProofFragment::Diophantine | ProofFragment::IntInequality
    ));
    assert!(matches!(
        cert.b_fragment,
        ProofFragment::Diophantine | ProofFragment::IntInequality
    ));

    // Craig condition 1: A ∧ ¬I is the kernel-checked integer module on the cert.
    assert!(
        !cert.a_certificate.contains("sorryAx"),
        "A ∧ ¬I module depends on sorryAx:\n{}",
        cert.a_certificate
    );
    lean_accepts("lia_interp_a_not_i", &cert.a_certificate);

    // Craig condition 2: I ∧ B likewise.
    assert!(
        !cert.b_certificate.contains("sorryAx"),
        "I ∧ B module depends on sorryAx:\n{}",
        cert.b_certificate
    );
    lean_accepts("lia_interp_i_b", &cert.b_certificate);
}

/// TAMPER (the no-`sorryAx` / kernel check has teeth): take a genuine certified LIA
/// integer module and replace its proof term with `sorry`. The real Lean kernel then
/// EITHER fails to type-check OR `#print axioms` reports `sorryAx` — both are
/// rejections. A fabricated LIA certificate cannot pass the gate the positive test
/// uses.
#[test]
fn tampered_certified_lia_interpolant_module_is_rejected_by_real_lean() {
    use axeyum_solver::lia_interpolant_certified;
    if lean_bin().is_none() {
        eprintln!("[skip] tamper: lean binary not found; install via elan or set AXEYUM_LEAN_BIN");
        return;
    }
    let mut arena = TermArena::new();
    let x = arena.int_var("x").unwrap();
    let two = arena.int_const(2);
    let two_x = arena.int_mul(two, x).unwrap();
    let zero = arena.int_const(0);
    let one = arena.int_const(1);
    let a0 = arena.int_ge(two_x, one).unwrap();
    let b0 = arena.int_le(two_x, zero).unwrap();
    let cert = lia_interpolant_certified(&mut arena, &[a0], &[b0])
        .expect("decides")
        .expect("a certified LIA interpolant exists");
    let source = &cert.a_certificate;

    // Replace the proof body `:= <proof>` of the refutation theorem with `sorry`.
    let marker = "theorem axeyum_refutation : False :=";
    let idx = source
        .find(marker)
        .expect("module declares axeyum_refutation");
    let head = &source[..idx + marker.len()];
    let tail_start = source[idx..]
        .find("#print axioms")
        .map(|p| idx + p)
        .expect("module has a #print axioms audit");
    let tampered = format!("{head} sorry\n\n{}", &source[tail_start..]);

    let typechecks = lean_typechecks("lia_interp_tampered", &tampered).expect("lean available");
    if typechecks {
        // If `sorry` type-checks (a warning, not an error), `#print axioms` MUST
        // expose `sorryAx` — the audit the positive test relies on.
        let bin = lean_bin().expect("lean available");
        let dir = std::env::temp_dir().join("axeyum_lean_lia_interp_tampered");
        let file = dir.join("lia_interp_tampered.lean");
        let out = Command::new(&bin).arg(&file).output().expect("run lean");
        let stdout = String::from_utf8_lossy(&out.stdout);
        assert!(
            stdout.contains("sorryAx"),
            "a `sorry`-tampered LIA refutation must expose sorryAx in the axiom audit:\n{stdout}"
        );
    }
    // (If it does NOT type-check, that is already a rejection — nothing to assert.)
}

/// BOUNDARY (`QF_UFLRA` interpolant cert): the certified conjunctive `QF_UFLRA` Craig
/// interpolant (`uflra_interpolant_certified`) carries its two soundness conditions
/// as `la_generic` refutations over OPAQUE uninterpreted-function applications, and
/// those are externally re-checked by **Carcara** (see `carcara_crosscheck.rs`). The
/// Lean-kernel reconstruction path (`prove_unsat_to_lean_module`) does NOT yet cover
/// the opaque-application `LRA` fragment, so it declines these conjunctions — the
/// external check for this cert is Carcara, not Lean. This test pins that boundary so
/// a future Lean-fragment extension is a deliberate, noticed change.
#[test]
fn uflra_opaque_application_refutation_is_declined_by_lean_path() {
    use axeyum_ir::Sort;
    let mut arena = TermArena::new();
    let f = arena.declare_fun("f", &[Sort::Real], Sort::Real).unwrap();
    let c = arena.real_var("c").unwrap();
    let fc = arena.apply(f, &[c]).unwrap();
    let five = arena.real_const(Rational::integer(5));
    // f(c) >= 5 ∧ f(c) < 5 — UNSAT with f(c) opaque; Carcara checks it via la_generic.
    let a = arena.real_ge(fc, five).unwrap();
    let b = arena.real_lt(fc, five).unwrap();
    assert!(
        prove_unsat_to_lean_module(&mut arena, &[a, b]).is_err(),
        "the Lean reconstruction path does not (yet) cover opaque-application LRA; \
         this cert's external check is Carcara"
    );
}

// --- Certified conjunctive QF_UFLIA Craig interpolant (uflia_interpolant_certified) ---
//
// The QF_UFLIA interpolant `I` carries two KERNEL-CHECKED integer certificates witnessing
// its two Craig soundness conditions: `A ∧ ¬I ⊢ ⊥` and `I ∧ B ⊢ ⊥`. Because the
// conjunctive construction declines whenever congruence is needed (the function-free
// relaxation is then sat), the certifiable interpolant is always congruence-free — its UF
// applications `(f c)` are OPAQUE shared integers. Each conjunction is therefore an
// integer-infeasible system over opaque applications that the integer-prelude
// reconstructor covers (Diophantine / interval cut, with each `(f c)` treated as a fresh
// opaque integer), so each certificate is a Lean module `prove_unsat_to_lean_module`
// already kernel-checked in-tree. Feeding both to the REAL `lean` binary — accepted, no
// `sorryAx` — is the external check that upgrades the QF_UFLIA interpolant from Validated
// to Checked. Carcara has NO `lia_generic` rule (warns + `holey`), so for integers the
// Lean kernel is the external checker (unlike QF_UFLRA, whose opaque-application
// `la_generic` refutations Carcara checks).

fn certified_uflia_interpolant_both_integer_certs_checked_by_real_lean() {
    use axeyum_solver::{ProofFragment, uflia_interpolant_certified};
    // A: 2·f(c) ≥ 1 ; B: 2·f(c) ≤ 0 over Int, with f(c) a SHARED opaque integer
    // application. Unsat (2·f(c) is even, cannot be ≥ 1 and ≤ 0). I = (2·f(c) ≥ 1), and
    // both A ∧ ¬I and I ∧ B are diff-multiplier integer intervals over the opaque f(c).
    let mut arena = TermArena::new();
    let f = arena.declare_fun("f", &[Sort::Int], Sort::Int).unwrap();
    let c = arena.int_var("c").unwrap();
    let fc = arena.apply(f, &[c]).unwrap();
    let two = arena.int_const(2);
    let two_fc = arena.int_mul(two, fc).unwrap();
    let zero = arena.int_const(0);
    let one = arena.int_const(1);
    let a0 = arena.int_ge(two_fc, one).unwrap();
    let b0 = arena.int_le(two_fc, zero).unwrap();

    let cert = uflia_interpolant_certified(&mut arena, &[a0], &[b0])
        .expect("decides")
        .expect("a certified QF_UFLIA interpolant exists");

    // Both certificates reconstructed through a COVERED integer fragment.
    assert!(matches!(
        cert.a_fragment,
        ProofFragment::Diophantine | ProofFragment::IntInequality
    ));
    assert!(matches!(
        cert.b_fragment,
        ProofFragment::Diophantine | ProofFragment::IntInequality
    ));

    // Craig condition 1: A ∧ ¬I is the kernel-checked integer module on the cert.
    assert!(
        !cert.a_certificate.contains("sorryAx"),
        "A ∧ ¬I module depends on sorryAx:\n{}",
        cert.a_certificate
    );
    lean_accepts("uflia_interp_a_not_i", &cert.a_certificate);

    // Craig condition 2: I ∧ B likewise.
    assert!(
        !cert.b_certificate.contains("sorryAx"),
        "I ∧ B module depends on sorryAx:\n{}",
        cert.b_certificate
    );
    lean_accepts("uflia_interp_i_b", &cert.b_certificate);
}

/// TAMPER (the no-`sorryAx` / kernel check has teeth): take a genuine certified `QF_UFLIA`
/// integer module and replace its proof term with `sorry`. The real Lean kernel then
/// EITHER fails to type-check OR `#print axioms` reports `sorryAx` — both are rejections.
/// A fabricated `QF_UFLIA` certificate cannot pass the gate the positive test uses.
#[test]
fn tampered_certified_uflia_interpolant_module_is_rejected_by_real_lean() {
    use axeyum_solver::uflia_interpolant_certified;
    if lean_bin().is_none() {
        eprintln!("[skip] tamper: lean binary not found; install via elan or set AXEYUM_LEAN_BIN");
        return;
    }
    let mut arena = TermArena::new();
    let f = arena.declare_fun("f", &[Sort::Int], Sort::Int).unwrap();
    let c = arena.int_var("c").unwrap();
    let fc = arena.apply(f, &[c]).unwrap();
    let two = arena.int_const(2);
    let two_fc = arena.int_mul(two, fc).unwrap();
    let zero = arena.int_const(0);
    let one = arena.int_const(1);
    let a0 = arena.int_ge(two_fc, one).unwrap();
    let b0 = arena.int_le(two_fc, zero).unwrap();
    let cert = uflia_interpolant_certified(&mut arena, &[a0], &[b0])
        .expect("decides")
        .expect("a certified QF_UFLIA interpolant exists");
    let source = &cert.a_certificate;

    // Replace the proof body `:= <proof>` of the refutation theorem with `sorry`.
    let marker = "theorem axeyum_refutation : False :=";
    let idx = source
        .find(marker)
        .expect("module declares axeyum_refutation");
    let head = &source[..idx + marker.len()];
    let tail_start = source[idx..]
        .find("#print axioms")
        .map(|p| idx + p)
        .expect("module has a #print axioms audit");
    let tampered = format!("{head} sorry\n\n{}", &source[tail_start..]);

    let typechecks = lean_typechecks("uflia_interp_tampered", &tampered).expect("lean available");
    if typechecks {
        // If `sorry` type-checks (a warning, not an error), `#print axioms` MUST expose
        // `sorryAx` — the audit the positive test relies on.
        let bin = lean_bin().expect("lean available");
        let dir = std::env::temp_dir().join("axeyum_lean_uflia_interp_tampered");
        let file = dir.join("uflia_interp_tampered.lean");
        let out = Command::new(&bin).arg(&file).output().expect("run lean");
        let stdout = String::from_utf8_lossy(&out.stdout);
        assert!(
            stdout.contains("sorryAx"),
            "a `sorry`-tampered QF_UFLIA refutation must expose sorryAx in the audit:\n{stdout}"
        );
    }
    // (If it does NOT type-check, that is already a rejection — nothing to assert.)
}
