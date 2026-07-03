//! Second differential soundness oracle for the **word-equation route**, using
//! **cvc5** (alongside the Z3-oracle fuzz in `word_equation_differential_fuzz.rs`).
//!
//! 4th-review demand: Z3-only validation is weakest exactly on strings, and the
//! committed string corpora are cvc5 regressions — so a wrong verdict from the
//! word route that Z3 happens to share (or that only strings surface) needs a
//! *second, independent* string theory to catch it. cvc5 is that oracle.
//!
//! Unlike the Z3 fuzz this test does **not** require the `z3` crate feature: it
//! shells the cvc5 *binary* (see `common_cvc5`) and uses only the always-available
//! `solve_smtlib` front door, so it runs in the default build whenever cvc5 is
//! installed. When cvc5 is absent the whole test is an adjudication-neutral no-op
//! pass, keeping CI without cvc5 green.
//!
//! Two adjudicated fronts:
//!
//! 1. a fuzz of ≥600 generated word-equation `QF_S` scripts (the generator is a
//!    self-contained copy of the Z3 fuzz's, biased toward unsat-heavy shapes —
//!    small alphabet, long-forcing concats, loops); and
//! 2. a sample (and an `#[ignore]`d full sweep) of the three committed cvc5
//!    string-regression corpora (`QF_S` / `QF_SEQ` / `QF_SLIA`).
//!
//! The joint gate for both fronts is the same soundness contract:
//!
//! - axeyum `Sat` ∧ cvc5 `unsat` → **PANIC** (wrong sat).
//! - axeyum `Unsat` ∧ cvc5 `sat` → **PANIC** (wrong unsat — the worst bug).
//! - axeyum `Unknown` / decline → SKIP (incomplete is sound).
//! - cvc5 `unknown` / timeout / parse-error → SKIP (cvc5 cannot adjudicate).

use std::fmt::Write as _;
use std::path::{Path, PathBuf};
use std::time::Duration;

use axeyum_solver::{CheckResult, SolverConfig, solve_smtlib};

mod common_cvc5;
use common_cvc5::{Verdict, cvc5_bin, cvc5_decide};

/// Number of fuzz scripts generated and adjudicated (≥ 600 as required).
const INSTANCES: u64 = 600;

/// Per-instance wall-clock budget for both engines.
const TIMEOUT: Duration = Duration::from_secs(10);

// ---------------------------------------------------------------------------
// Generator — a self-contained copy of `word_equation_differential_fuzz.rs`'s
// generator (duplicated deliberately so this test never depends on, and never
// forces an edit to, that concurrently-maintained fuzz file). Kept in sync in
// spirit, not by import: both must exercise the same word fragment.
// ---------------------------------------------------------------------------

/// A deterministic linear-congruential PRNG (the MMIX multiplier/increment).
struct Lcg(u64);

impl Lcg {
    fn new(seed: u64) -> Self {
        Lcg(seed
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407))
    }

    fn next_u64(&mut self) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        self.0
    }

    fn below(&mut self, n: u64) -> usize {
        usize::try_from(self.next_u64() % n).expect("modulus fits usize")
    }
}

/// Tiny alphabet — a small alphabet makes literal clashes (unsats) frequent.
const ALPHABET: &[u8] = b"ab";

fn gen_short_literal(rng: &mut Lcg) -> String {
    let len = rng.below(4); // 0..=3
    let mut s = String::with_capacity(len);
    for _ in 0..len {
        s.push(char::from(ALPHABET[rng.below(ALPHABET.len() as u64)]));
    }
    s
}

fn gen_long_literal(rng: &mut Lcg) -> String {
    let mut s = String::with_capacity(8);
    for _ in 0..8 {
        s.push(char::from(ALPHABET[rng.below(ALPHABET.len() as u64)]));
    }
    s
}

fn gen_over_long_literal(rng: &mut Lcg) -> String {
    let len = 9 + rng.below(6); // 9..=14
    let mut s = String::with_capacity(len);
    for _ in 0..len {
        s.push(char::from(ALPHABET[rng.below(ALPHABET.len() as u64)]));
    }
    s
}

fn gen_str_expr(rng: &mut Lcg, num_vars: usize, depth: u32, over_long: bool) -> String {
    if depth == 0 {
        return leaf(rng, num_vars, over_long);
    }
    match rng.below(6) {
        0 | 1 => leaf(rng, num_vars, over_long),
        _ => {
            let l = if over_long && rng.below(2) == 0 {
                format!("\"{}\"", gen_over_long_literal(rng))
            } else if depth >= 2 && rng.below(4) == 0 {
                format!("\"{}\"", gen_long_literal(rng))
            } else {
                gen_str_expr(rng, num_vars, depth - 1, over_long)
            };
            let r = gen_str_expr(rng, num_vars, depth - 1, over_long);
            if over_long && rng.below(2) == 0 {
                let m = gen_str_expr(rng, num_vars, depth - 1, over_long);
                format!("(str.++ {l} {m} {r})")
            } else {
                format!("(str.++ {l} {r})")
            }
        }
    }
}

fn leaf(rng: &mut Lcg, num_vars: usize, over_long: bool) -> String {
    if num_vars > 0 && rng.below(2) == 0 {
        format!("s{}", rng.below(num_vars as u64))
    } else if over_long && rng.below(3) == 0 {
        format!("\"{}\"", gen_over_long_literal(rng))
    } else {
        format!("\"{}\"", gen_short_literal(rng))
    }
}

/// A full generated word-equation script as SMT-LIB 2 text.
struct Instance {
    text: String,
}

impl Instance {
    fn generate(rng: &mut Lcg) -> Instance {
        let mode = rng.below(3); // 0 = easy, 1 = hard, 2 = over_long (fallback)
        let hard = mode >= 1;
        let over_long = mode == 2;
        let num_vars = rng.below(3) + 2; // 2..=4
        let num_eqs = if hard {
            rng.below(3) + 2 // 2..=4
        } else {
            rng.below(2) + 1 // 1..=2
        };
        let num_diseqs = rng.below(3); // 0..=2
        let num_ext = rng.below(3); // 0..=2 extended-function atoms
        let depth = if hard { 2 } else { 1 };

        let mut text = String::new();
        text.push_str("(set-logic QF_S)\n");
        for i in 0..num_vars {
            let _ = writeln!(text, "(declare-const s{i} String)");
        }

        for _ in 0..num_eqs {
            if hard && rng.below(6) == 0 {
                let i = rng.below(num_vars as u64);
                let lit = gen_short_literal(rng);
                let _ = writeln!(text, "(assert (= s{i} (str.++ \"{lit}\" s{i})))");
            } else {
                let l = gen_str_expr(rng, num_vars, depth, over_long);
                let r = gen_str_expr(rng, num_vars, depth, over_long);
                let _ = writeln!(text, "(assert (= {l} {r}))");
            }
        }
        for _ in 0..num_diseqs {
            let l = gen_str_expr(rng, num_vars, 1, over_long);
            let r = gen_str_expr(rng, num_vars, 1, over_long);
            if rng.below(2) == 0 {
                let _ = writeln!(text, "(assert (not (= {l} {r})))");
            } else {
                let _ = writeln!(text, "(assert (distinct {l} {r}))");
            }
        }

        for _ in 0..num_ext {
            let op = match rng.below(3) {
                0 => "str.prefixof",
                1 => "str.suffixof",
                _ => "str.contains",
            };
            let a = gen_str_expr(rng, num_vars, depth, over_long);
            let b = gen_str_expr(rng, num_vars, depth, over_long);
            let atom = format!("({op} {a} {b})");
            if rng.below(4) == 0 {
                let _ = writeln!(text, "(assert (not {atom}))");
            } else {
                let _ = writeln!(text, "(assert {atom})");
            }
        }

        text.push_str("(check-sat)\n");
        Instance { text }
    }
}

// ---------------------------------------------------------------------------
// Adjudication
// ---------------------------------------------------------------------------

/// Decide a script with axeyum's SMT-LIB front door. A `Sat` has already been
/// replay-checked; any error / `Unknown` is a sound SKIP.
fn axeyum_decide(text: &str) -> Verdict {
    let config = SolverConfig::new().with_timeout(TIMEOUT);
    match solve_smtlib(text, &config) {
        Ok(outcome) => match outcome.result {
            CheckResult::Sat(_) => Verdict::Sat,
            CheckResult::Unsat => Verdict::Unsat,
            CheckResult::Unknown(_) => Verdict::Skip,
        },
        Err(_) => Verdict::Skip,
    }
}

/// The joint soundness gate: a hard cross (sat vs unsat) is a PANIC; anything
/// else where both engines decide is an agreement.
fn gate(context: &str, ax: Verdict, cvc5: Verdict, text: &str) {
    let cross = matches!(
        (ax, cvc5),
        (Verdict::Sat, Verdict::Unsat) | (Verdict::Unsat, Verdict::Sat)
    );
    assert!(
        !cross,
        "DISAGREEMENT ({context}): axeyum = {ax:?}, cvc5 = {cvc5:?}.\n\
         This is a {} soundness bug in the word/string route.\n\
         script:\n{text}",
        match (ax, cvc5) {
            (Verdict::Sat, Verdict::Unsat) => "WRONG-SAT",
            (Verdict::Unsat, Verdict::Sat) => "WRONG-UNSAT (worst case)",
            _ => "verdict",
        }
    );
}

// ---------------------------------------------------------------------------
// Front 1: generated word-equation fuzz
// ---------------------------------------------------------------------------

#[test]
fn word_equation_cvc5_crosscheck_disagree_zero() {
    let Some(bin) = cvc5_bin() else {
        eprintln!("[cvc5-word-fuzz] cvc5 unavailable; skipping (no adjudicator)");
        return;
    };

    let mut jointly_decided = 0u64;
    let mut agreements = 0u64;
    let mut axeyum_sat = 0u64;
    let mut axeyum_unsat = 0u64;
    let mut axeyum_skip = 0u64;
    let mut cvc5_skip = 0u64;

    for seed in 0..INSTANCES {
        if seed % 100 == 0 {
            eprintln!(
                "[cvc5-word-fuzz] seed {seed}/{INSTANCES} (joint={jointly_decided}, \
                 agree={agreements}, ax_sat={axeyum_sat}, ax_unsat={axeyum_unsat}, \
                 ax_skip={axeyum_skip}, cvc5_skip={cvc5_skip})"
            );
        }
        let mut rng = Lcg::new(seed);
        let inst = Instance::generate(&mut rng);

        let ax = axeyum_decide(&inst.text);
        match ax {
            Verdict::Sat => axeyum_sat += 1,
            Verdict::Unsat => axeyum_unsat += 1,
            Verdict::Skip => {
                axeyum_skip += 1;
                continue;
            }
        }

        let cvc5 = cvc5_decide(&bin, &inst.text, TIMEOUT);
        if cvc5 == Verdict::Skip {
            cvc5_skip += 1;
            continue;
        }

        jointly_decided += 1;
        gate(&format!("fuzz seed {seed}"), ax, cvc5, &inst.text);
        agreements += 1;
    }

    println!("=== word-equation cvc5 differential fuzz tally ===");
    println!("total scripts:        {INSTANCES}");
    println!("jointly decided:      {jointly_decided}");
    println!("agreements:           {agreements}");
    println!("axeyum Sat:           {axeyum_sat}");
    println!("axeyum Unsat:         {axeyum_unsat}");
    println!("axeyum skipped:       {axeyum_skip} (Unknown/decline)");
    println!("cvc5 skipped:         {cvc5_skip} (unknown/timeout/parse)");
    println!("DISAGREEMENTS:        0");

    assert!(
        jointly_decided > 50,
        "too few jointly-decided scripts ({jointly_decided}); the cvc5 \
         differential gate is not meaningfully exercised"
    );
    assert!(
        axeyum_sat > 0 && axeyum_unsat > 0,
        "expected both sat and unsat verdicts to be adjudicated (sat={axeyum_sat}, \
         unsat={axeyum_unsat})"
    );
}

// ---------------------------------------------------------------------------
// Front 2: committed cvc5 string-regression corpora
// ---------------------------------------------------------------------------

/// The three committed cvc5 string-regression corpus directories, relative to
/// the workspace root (this crate lives at `crates/axeyum-solver`).
fn corpus_dirs() -> Vec<PathBuf> {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(Path::parent)
        .expect("workspace root is two levels above the crate manifest")
        .to_path_buf();
    ["QF_S", "QF_SEQ", "QF_SLIA"]
        .iter()
        .map(|logic| {
            root.join("corpus/public-curated/non-incremental")
                .join(logic)
                .join("cvc5-regress-clean")
        })
        .collect()
}

/// Collect `.smt2` files from each present corpus dir, sorted within a dir, then
/// interleaved round-robin across dirs (deterministic). A `limit` of 0 means all.
fn corpus_files(limit: usize) -> Vec<PathBuf> {
    let mut per_dir: Vec<Vec<PathBuf>> = Vec::new();
    for dir in corpus_dirs() {
        let Ok(rd) = std::fs::read_dir(&dir) else {
            continue; // corpus absent (gitignored NAS symlink) → skip
        };
        let mut files: Vec<PathBuf> = rd
            .filter_map(|e| e.ok().map(|e| e.path()))
            .filter(|p| p.extension().is_some_and(|x| x == "smt2"))
            .collect();
        files.sort();
        per_dir.push(files);
    }
    let mut out = Vec::new();
    let mut idx = 0usize;
    loop {
        let mut advanced = false;
        for files in &per_dir {
            if let Some(p) = files.get(idx) {
                out.push(p.clone());
                advanced = true;
                if limit != 0 && out.len() >= limit {
                    return out;
                }
            }
        }
        if !advanced {
            break;
        }
        idx += 1;
    }
    out
}

/// Run the corpus files (up to `limit`, 0 = all) through axeyum vs cvc5.
fn run_corpus(limit: usize) {
    let Some(bin) = cvc5_bin() else {
        eprintln!("[cvc5-corpus] cvc5 unavailable; skipping (no adjudicator)");
        return;
    };
    let files = corpus_files(limit);
    if files.is_empty() {
        eprintln!("[cvc5-corpus] no corpus files found (gitignored?); skipping");
        return;
    }

    let mut jointly = 0u64;
    let mut agree = 0u64;
    let mut ax_skip = 0u64;
    let mut cvc5_skip = 0u64;
    for path in &files {
        let Ok(text) = std::fs::read_to_string(path) else {
            continue;
        };
        let ax = axeyum_decide(&text);
        if ax == Verdict::Skip {
            ax_skip += 1;
            continue;
        }
        let cvc5 = cvc5_decide(&bin, &text, TIMEOUT);
        if cvc5 == Verdict::Skip {
            cvc5_skip += 1;
            continue;
        }
        jointly += 1;
        gate(&format!("corpus {}", path.display()), ax, cvc5, &text);
        agree += 1;
    }

    println!(
        "=== cvc5 string-corpus crosscheck tally (files={}) ===",
        files.len()
    );
    println!("jointly decided:      {jointly}");
    println!("agreements:           {agree}");
    println!("axeyum skipped:       {ax_skip} (Unknown/decline)");
    println!("cvc5 skipped:         {cvc5_skip} (unknown/timeout/parse)");
    println!("DISAGREEMENTS:        0");
}

/// Default: a small round-robin sample across the three corpora — cheap enough
/// for every `cargo test` run while still exercising real cvc5 regressions.
#[test]
fn string_corpora_cvc5_crosscheck_sample() {
    run_corpus(30);
}

/// Full sweep of all three corpora — heavier; run explicitly with `--ignored`.
#[test]
#[ignore = "full string-corpus sweep; run explicitly (heavier)"]
fn string_corpora_cvc5_crosscheck_full() {
    run_corpus(0);
}
