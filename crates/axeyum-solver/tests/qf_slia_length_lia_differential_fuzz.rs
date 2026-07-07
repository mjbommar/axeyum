//! Adversarial differential soundness fuzzer for the **length↔LIA string route**
//! (P2.7 Phase A, `LenAbs` `sat` bridge —
//! [`length_lia_verdict`](axeyum_solver::length_lia_verdict) / the `solve_smtlib`
//! front door) against the Z3 **and** cvc5 oracles (Z3-only validation is weakest
//! exactly on strings, so cvc5 is the independent second string oracle).
//!
//! The route decides `str.len`-coupled `QF_SLIA` rows whose `sat` witness the bounded
//! packed encoder cannot represent (its length is capped at `STRING_MAX_LEN`): it
//! links `str.len` to the LIA solver over fresh per-variable length symbols, and adds
//! a **replay-checked `sat`** (each string an `'a'`-fill of its solved length, then a
//! `Seq`-level ground-evaluator replay). It never emits `unsat` (the ADR-0052
//! `StringGate` owns the length-abstraction refutation).
//!
//! Both directions are soundness-gated on the jointly-decided scripts:
//!
//! - axeyum `Sat` ∧ oracle `unsat` → **PANIC** (wrong sat — the length route's own
//!   risk: an `'a'`-fill witness that should not have replayed);
//! - axeyum `Unsat` ∧ oracle `sat` → **PANIC** (wrong unsat — the `StringGate`
//!   companion, gated here for completeness).
//!
//! The generator biases length constants **past the bounded length cap** (0..=40) so
//! the bounded encoder returns `unknown` and the length route fires, and keeps most
//! words content-free (variables / `str.++` of variables) so the `'a'`-fill replays
//! and `sat` is exercised. Literals — including `\u{…}` escapes and the `>0x7F`
//! byte-model boundary — are still drawn so the literal grammar is covered (the
//! `ba0d9149` wrong-verdict-class rule). Fixed-seed LCG ⇒ fully reproducible.

use std::fmt::Write as _;
use std::time::Duration;

use axeyum_solver::{CheckResult, SolverConfig, solve_smtlib};

mod common_cvc5;
use common_cvc5::{Verdict, cvc5_bin, cvc5_decide};

mod common_string_grammar;
use common_string_grammar::GrammarCoverage;

/// Number of scripts generated and adjudicated (≥ 600 as required).
const INSTANCES: u64 = 800;

/// Per-call oracle wall-clock budget.
const ORACLE_TIMEOUT: Duration = Duration::from_secs(3);

/// Path to the system Z3 binary (its full string theory adjudicates).
#[cfg(feature = "z3")]
const Z3_BIN: &str = "/usr/bin/z3";

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

/// One character of a generated literal — mostly a small ASCII letter, but ~1 in 5 an
/// SMT-LIB `\u{…}` escape including the `>0x7F` byte-model boundary `\u{ff}` (the
/// `ba0d9149` escape-decode coverage rule). Literals stay within `0..=0xff` (a `>0xFF`
/// literal is a sound parse-time SKIP that would not exercise the length route).
fn push_char(rng: &mut Lcg, s: &mut String) {
    if rng.below(5) == 0 {
        match rng.below(3) {
            0 => s.push_str("\\u{0a}"),
            1 => s.push_str("\\u{41}"),
            _ => s.push_str("\\u{ff}"),
        }
    } else {
        const LETTERS: &[u8] = b"ABCDEabcde";
        s.push(char::from(LETTERS[rng.below(LETTERS.len() as u64)]));
    }
}

/// A short literal (0..=3 characters, some possibly `\u{…}`-escaped).
fn gen_literal(rng: &mut Lcg) -> String {
    let len = rng.below(4);
    let mut s = String::new();
    for _ in 0..len {
        push_char(rng, &mut s);
    }
    s
}

/// A **word** s-expression whose `str.len` is taken: mostly a variable or `str.++` of
/// variables (content-free, so the `'a'`-fill replays and `sat` is exercised), with a
/// minority literal / mixed concat (content-bearing — a sound decline if it cannot
/// replay).
fn gen_word(rng: &mut Lcg, num_vars: usize) -> String {
    match rng.below(8) {
        0..=2 => format!("s{}", rng.below(num_vars as u64)),
        3 | 4 => format!(
            "(str.++ s{} s{})",
            rng.below(num_vars as u64),
            rng.below(num_vars as u64)
        ),
        5 => format!(
            "(str.++ s{} s{} s{})",
            rng.below(num_vars as u64),
            rng.below(num_vars as u64),
            rng.below(num_vars as u64)
        ),
        6 => format!("\"{}\"", gen_literal(rng)),
        _ => format!(
            "(str.++ s{} \"{}\")",
            rng.below(num_vars as u64),
            gen_literal(rng)
        ),
    }
}

/// A large-ish integer constant, biased **past the bounded length cap** so the bounded
/// encoder declines and the length route fires.
fn gen_const(rng: &mut Lcg) -> u64 {
    // 0..=40, weighted toward the over-cap band (>8).
    match rng.below(4) {
        0 => rng.below(9) as u64, // 0..=8 (in-cap; the bounded path may decide)
        _ => 9 + rng.below(32) as u64, // 9..=40 (over-cap; forces the length route)
    }
}

/// A linear-`Int` **length term**: `str.len` of a word, a sum of two, a declared `Int`
/// variable, a constant, or a length-plus-constant.
fn gen_len_term(rng: &mut Lcg, num_vars: usize, num_ints: usize) -> String {
    match rng.below(if num_ints > 0 { 6 } else { 5 }) {
        0 | 1 => format!("(str.len {})", gen_word(rng, num_vars)),
        2 => format!(
            "(+ (str.len {}) (str.len {}))",
            gen_word(rng, num_vars),
            gen_word(rng, num_vars)
        ),
        3 => format!(
            "(+ (str.len {}) {})",
            gen_word(rng, num_vars),
            gen_const(rng)
        ),
        4 => format!("{}", gen_const(rng)),
        _ => format!("n{}", rng.below(num_ints as u64)),
    }
}

/// A single length-comparison atom whose **left** side always carries a `str.len`
/// (guaranteeing the length fragment is recognized), over `=`/`<`/`<=`/`>`/`>=`.
fn gen_len_atom(rng: &mut Lcg, num_vars: usize, num_ints: usize) -> String {
    let op = ["=", "<", "<=", ">", ">="][rng.below(5)];
    let left = format!("(str.len {})", gen_word(rng, num_vars));
    let right = gen_len_term(rng, num_vars, num_ints);
    format!("({op} {left} {right})")
}

/// A single asserted formula — a bare / negated / `or` / `and` / `=>` combination of
/// length atoms (plus, when `Int` variables exist, an occasional `n = str.len w` link).
fn gen_assertion(rng: &mut Lcg, num_vars: usize, num_ints: usize) -> String {
    if num_ints > 0 && rng.below(5) == 0 {
        return format!(
            "(= n{} (str.len {}))",
            rng.below(num_ints as u64),
            gen_word(rng, num_vars)
        );
    }
    match rng.below(7) {
        0 | 1 => gen_len_atom(rng, num_vars, num_ints),
        2 => format!("(not {})", gen_len_atom(rng, num_vars, num_ints)),
        3 | 4 => format!(
            "(or {} {})",
            gen_len_atom(rng, num_vars, num_ints),
            gen_len_atom(rng, num_vars, num_ints)
        ),
        5 => format!(
            "(and {} {})",
            gen_len_atom(rng, num_vars, num_ints),
            gen_len_atom(rng, num_vars, num_ints)
        ),
        _ => format!(
            "(=> {} {})",
            gen_len_atom(rng, num_vars, num_ints),
            gen_len_atom(rng, num_vars, num_ints)
        ),
    }
}

/// A full generated `QF_SLIA` length-coupled script as SMT-LIB 2 text.
struct Instance {
    text: String,
}

impl Instance {
    fn generate(rng: &mut Lcg) -> Instance {
        let num_vars = 1 + rng.below(3); // 1..=3 string variables
        let num_ints = rng.below(3); // 0..=2 integer variables
        let mut text = String::new();
        text.push_str("(set-logic QF_SLIA)\n");
        for i in 0..num_vars {
            let _ = writeln!(text, "(declare-fun s{i} () String)");
        }
        for i in 0..num_ints {
            let _ = writeln!(text, "(declare-fun n{i} () Int)");
        }
        // The first assertion is always a bare length atom (so the length fragment is
        // recognized), then 1..=4 more free-form assertions.
        let _ = writeln!(text, "(assert {})", gen_len_atom(rng, num_vars, num_ints));
        let extra = 1 + rng.below(4);
        for _ in 0..extra {
            let _ = writeln!(text, "(assert {})", gen_assertion(rng, num_vars, num_ints));
        }
        text.push_str("(check-sat)\n");
        Instance { text }
    }
}

/// Decide a script with axeyum's SMT-LIB front door. Any error or `Unknown` is a
/// sound SKIP.
fn axeyum_decide(text: &str) -> Verdict {
    let config = SolverConfig::new().with_timeout(Duration::from_secs(3));
    match solve_smtlib(text, &config) {
        Ok(outcome) => match outcome.result {
            CheckResult::Sat(_) => Verdict::Sat,
            CheckResult::Unsat => Verdict::Unsat,
            CheckResult::Unknown(_) => Verdict::Skip,
        },
        Err(_) => Verdict::Skip,
    }
}

/// The shared adjudication loop, parameterized by the oracle. A jointly-decided
/// disagreement in either direction is a soundness bug and panics.
fn run_against(label: &str, oracle: impl Fn(&str) -> Verdict) -> (u64, u64, u64) {
    let mut jointly_decided = 0u64;
    let mut agreements = 0u64;
    let mut axeyum_sat = 0u64;
    let mut axeyum_unsat = 0u64;
    let mut axeyum_skip = 0u64;
    let mut oracle_skip = 0u64;

    for seed in 0..INSTANCES {
        if seed % 100 == 0 {
            eprintln!(
                "[{label}] seed {seed}/{INSTANCES} (joint={jointly_decided}, \
                 agree={agreements}, ax_sat={axeyum_sat}, ax_unsat={axeyum_unsat}, \
                 ax_skip={axeyum_skip}, oracle_skip={oracle_skip})"
            );
        }
        let mut rng = Lcg::new(seed.wrapping_mul(0x9E37_79B9_7F4A_7C15).wrapping_add(1));
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

        let orc = oracle(&inst.text);
        if orc == Verdict::Skip {
            oracle_skip += 1;
            continue;
        }
        jointly_decided += 1;

        if ax == orc {
            agreements += 1;
        } else {
            panic!(
                "DIFFERENTIAL DISAGREEMENT (seed {seed}): axeyum={ax:?} {label}={orc:?} — a {} \
                 soundness bug in the length↔LIA route.\n--- script ---\n{}",
                match (ax, orc) {
                    (Verdict::Sat, Verdict::Unsat) => "WRONG-SAT (worst case)",
                    (Verdict::Unsat, Verdict::Sat) => "WRONG-UNSAT",
                    _ => "verdict",
                },
                inst.text
            );
        }
    }

    eprintln!(
        "[{label}] done: {INSTANCES} generated, {jointly_decided} jointly decided, \
         {agreements} agree (ax_sat={axeyum_sat}, ax_unsat={axeyum_unsat}, \
         ax_skip={axeyum_skip}, oracle_skip={oracle_skip})"
    );
    assert_eq!(
        jointly_decided, agreements,
        "every jointly decided length-coupled script must agree with {label}"
    );
    assert!(
        jointly_decided >= 100,
        "too few joint decisions ({jointly_decided}) — the length fuzz is not exercising the route"
    );
    // The sweep must exercise the length route's `sat` path (its only output).
    assert!(
        axeyum_sat > 0,
        "the fuzz must exercise the length route's replay-checked sat path (sat={axeyum_sat})"
    );
    (jointly_decided, axeyum_sat, axeyum_unsat)
}

/// Z3 oracle front (behind the `z3` feature — the system binary carries the full
/// string theory; the z3 *crate* AST has no string sorts, so the text is shelled).
#[cfg(feature = "z3")]
#[test]
fn qf_slia_length_lia_differential_fuzz_z3_disagree_zero() {
    use std::io::Write as _;
    use std::process::{Command, Stdio};

    let z3_decide = |text: &str| -> Verdict {
        let Ok(mut child) = Command::new(Z3_BIN)
            .arg(format!("-T:{}", ORACLE_TIMEOUT.as_secs().max(1)))
            .arg("-in")
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::null())
            .spawn()
        else {
            return Verdict::Skip;
        };
        if let Some(stdin) = child.stdin.as_mut() {
            let _ = stdin.write_all(text.as_bytes());
        }
        drop(child.stdin.take());
        let Ok(output) = child.wait_with_output() else {
            return Verdict::Skip;
        };
        for line in String::from_utf8_lossy(&output.stdout).lines() {
            match line.trim() {
                "sat" => return Verdict::Sat,
                "unsat" => return Verdict::Unsat,
                _ => {}
            }
        }
        Verdict::Skip
    };
    if z3_decide("(set-logic QF_SLIA)\n(check-sat)\n") == Verdict::Skip
        && Command::new(Z3_BIN).arg("--version").output().is_err()
    {
        eprintln!("[length-fuzz-z3] {Z3_BIN} unavailable; skipping (no adjudicator)");
        return;
    }
    run_against("z3", z3_decide);
}

/// cvc5 oracle front (the second independent string differential oracle).
#[test]
fn qf_slia_length_lia_differential_fuzz_cvc5_disagree_zero() {
    let Some(bin) = cvc5_bin() else {
        eprintln!("[length-fuzz-cvc5] cvc5 unavailable; skipping (no adjudicator)");
        return;
    };
    run_against("cvc5", |text| cvc5_decide(&bin, text, ORACLE_TIMEOUT));
}

/// INVARIANT (structural, oracle-free): the generator provably emits the full literal
/// grammar — `\u{…}` escapes **and** the `>0x7F` byte-model boundary `\u{ff}` — over
/// the batch it feeds the differential fuzz (the `ba0d9149` wrong-verdict-class rule).
#[test]
fn generator_emits_full_literal_grammar() {
    let mut cov = GrammarCoverage::new();
    for seed in 0..INSTANCES {
        let mut rng = Lcg::new(seed.wrapping_mul(0x9E37_79B9_7F4A_7C15).wrapping_add(1));
        cov.observe(&Instance::generate(&mut rng).text);
    }
    cov.assert_escape_coverage(0.05, "qf_slia_length_lia");
    cov.assert_boundary_coverage(0.01, "qf_slia_length_lia");
}
