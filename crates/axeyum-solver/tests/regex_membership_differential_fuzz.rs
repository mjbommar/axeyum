//! Adversarial differential soundness fuzzer for the **regex-membership route**
//! (P2.7 T-C.5, ADR-0054) against the Z3 and cvc5 oracles.
//!
//! The membership route runs behind the bounded pre-check + the word routes and
//! moves the verdict in **both** directions: it adds `sat` (a witness replayed
//! through the reference matcher) and `unsat` (only behind a re-checked
//! derivative-emptiness certificate). Both directions are soundness-gated here
//! against a full external string theory:
//!
//! - a wrong `sat` — a model of an unsatisfiable membership system — faces the
//!   oracle's `unsat`;
//! - a wrong `unsat` (the worst case) — a claimed-empty language that is in fact
//!   inhabited — faces the oracle's `sat`.
//!
//! The generator emits random `QF_S` membership scripts over a tiny alphabet:
//! 1..=3 string variables, positive **and** negative `str.in_re` atoms carrying
//! depth-≤4 regexes (concat / union / intersection / complement / star / plus /
//! opt / native `re.loop` / `re.range` / `re.allchar` / `re.all` / `re.none`),
//! occasional length bounds and literal pins, and the odd variable–variable
//! equality (which the route declines — an adjudication-neutral SKIP). Two oracle
//! fronts adjudicate the same generator: the system **Z3** binary (behind the
//! `z3` feature) and the **cvc5** binary (always, when installed).
//!
//! Joint gate (both fronts): axeyum `Sat` ∧ oracle `unsat` → PANIC (wrong sat);
//! axeyum `Unsat` ∧ oracle `sat` → PANIC (wrong unsat); any `Unknown` / decline /
//! timeout on either side → SKIP. DISAGREE must be 0.
#![cfg(feature = "full")]

use std::fmt::Write as _;
use std::time::Duration;

use axeyum_solver::{CheckResult, SolverConfig, solve_smtlib};

mod common_cvc5;
use common_cvc5::{Verdict, cvc5_bin, cvc5_decide};

/// Scripts generated and adjudicated (≥ 600 as required).
const INSTANCES: u64 = 700;

/// Per-instance wall-clock budget for both engines.
const TIMEOUT: Duration = Duration::from_secs(10);

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

/// A short literal over the tiny alphabet `{a, b}` (0..=2 chars).
fn gen_literal(rng: &mut Lcg) -> String {
    let len = rng.below(3);
    let mut s = String::with_capacity(len);
    for _ in 0..len {
        s.push(if rng.below(2) == 0 { 'a' } else { 'b' });
    }
    s
}

/// A random `RegLan` s-expression with bounded structural `depth`.
fn gen_regex(rng: &mut Lcg, depth: u32) -> String {
    if depth == 0 {
        return match rng.below(6) {
            0 => format!("(str.to_re \"{}\")", gen_literal(rng)),
            1 => "re.allchar".to_owned(),
            2 => "(re.range \"a\" \"b\")".to_owned(),
            3 => "re.none".to_owned(),
            4 => "re.all".to_owned(),
            _ => "(str.to_re \"a\")".to_owned(),
        };
    }
    match rng.below(11) {
        0 => format!("(str.to_re \"{}\")", gen_literal(rng)),
        1 => format!(
            "(re.++ {} {})",
            gen_regex(rng, depth - 1),
            gen_regex(rng, depth - 1)
        ),
        2 => format!(
            "(re.union {} {})",
            gen_regex(rng, depth - 1),
            gen_regex(rng, depth - 1)
        ),
        3 => format!(
            "(re.inter {} {})",
            gen_regex(rng, depth - 1),
            gen_regex(rng, depth - 1)
        ),
        4 => format!("(re.comp {})", gen_regex(rng, depth - 1)),
        5 => format!("(re.* {})", gen_regex(rng, depth - 1)),
        6 => format!("(re.+ {})", gen_regex(rng, depth - 1)),
        7 => format!("(re.opt {})", gen_regex(rng, depth - 1)),
        8 => {
            let lo = rng.below(3);
            let hi = lo + rng.below(3);
            format!("((_ re.loop {lo} {hi}) {})", gen_regex(rng, depth - 1))
        }
        9 => "(re.range \"a\" \"b\")".to_owned(),
        _ => format!(
            "(re.diff {} {})",
            gen_regex(rng, depth - 1),
            gen_regex(rng, depth - 1)
        ),
    }
}

/// A generated membership `QF_S` script.
fn generate(rng: &mut Lcg) -> String {
    let num_vars = rng.below(3) + 1; // 1..=3
    let mut text = String::new();
    text.push_str("(set-logic QF_S)\n");
    for i in 0..num_vars {
        let _ = writeln!(text, "(declare-const v{i} String)");
    }
    // At least one membership atom overall (so the route claims the script).
    let mut saw_membership = false;
    for i in 0..num_vars {
        let n_pos = 1 + rng.below(2); // 1..=2 positive
        for _ in 0..n_pos {
            let _ = writeln!(text, "(assert (str.in_re v{i} {}))", gen_regex(rng, 3));
            saw_membership = true;
        }
        if rng.below(2) == 0 {
            let _ = writeln!(
                text,
                "(assert (not (str.in_re v{i} {})))",
                gen_regex(rng, 3)
            );
            saw_membership = true;
        }
        // Occasional length bound.
        match rng.below(4) {
            0 => {
                let _ = writeln!(text, "(assert (>= (str.len v{i}) {}))", rng.below(4));
            }
            1 => {
                let _ = writeln!(text, "(assert (<= (str.len v{i}) {}))", rng.below(5));
            }
            _ => {}
        }
        // Occasional literal pin.
        if rng.below(5) == 0 {
            let _ = writeln!(text, "(assert (= v{i} \"{}\"))", gen_literal(rng));
        }
    }
    // Occasional variable–variable equality (the route declines it → SKIP).
    if num_vars >= 2 && rng.below(6) == 0 {
        let _ = writeln!(text, "(assert (= v0 v1))");
    }
    if !saw_membership {
        let _ = writeln!(text, "(assert (str.in_re v0 (str.to_re \"a\")))");
    }
    text.push_str("(check-sat)\n");
    text
}

/// Decide a script with axeyum's SMT-LIB front door. Any error / `Unknown` is a
/// sound SKIP.
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

/// The shared adjudication loop, parameterized by the oracle. Returns
/// `(jointly_decided, axeyum_sat, axeyum_unsat)`.
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
                "[{label}] seed {seed}/{INSTANCES} (joint={jointly_decided}, agree={agreements}, \
                 ax_sat={axeyum_sat}, ax_unsat={axeyum_unsat}, ax_skip={axeyum_skip})"
            );
        }
        let mut rng = Lcg::new(seed);
        let text = generate(&mut rng);

        let ax = axeyum_decide(&text);
        match ax {
            Verdict::Sat => axeyum_sat += 1,
            Verdict::Unsat => axeyum_unsat += 1,
            Verdict::Skip => {
                axeyum_skip += 1;
                continue;
            }
        }

        let orc = oracle(&text);
        if orc == Verdict::Skip {
            oracle_skip += 1;
            continue;
        }
        jointly_decided += 1;
        if ax == orc {
            agreements += 1;
        } else {
            panic!(
                "DISAGREEMENT (seed {seed}): axeyum = {ax:?}, {label} = {orc:?}.\n\
                 This is a {} soundness bug in the regex-membership route.\n\
                 script:\n{text}",
                match (ax, orc) {
                    (Verdict::Sat, Verdict::Unsat) => "WRONG-SAT",
                    (Verdict::Unsat, Verdict::Sat) => "WRONG-UNSAT (worst case)",
                    _ => "verdict",
                }
            );
        }
    }

    println!("=== regex-membership differential vs {label} ===");
    println!("jointly decided: {jointly_decided}");
    println!("agreements:      {agreements}");
    println!("axeyum Sat:      {axeyum_sat}");
    println!("axeyum Unsat:    {axeyum_unsat}");
    println!("axeyum skipped:  {axeyum_skip}");
    println!("{label} skipped: {oracle_skip}");
    println!("DISAGREEMENTS:   0");

    (jointly_decided, axeyum_sat, axeyum_unsat)
}

/// Z3 oracle front (behind the `z3` feature — the system binary carries the full
/// string theory; the z3 *crate* AST has no string sorts, so we shell the text).
#[cfg(feature = "z3")]
#[test]
fn regex_membership_differential_fuzz_z3_disagree_zero() {
    use std::io::Write as _;
    use std::process::{Command, Stdio};

    const Z3_BIN: &str = "/usr/bin/z3";
    let z3_decide = |text: &str| -> Verdict {
        let Ok(mut child) = Command::new(Z3_BIN)
            .arg(format!("-T:{}", TIMEOUT.as_secs().max(1)))
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
    if z3_decide("(set-logic QF_S)\n(check-sat)\n") == Verdict::Skip
        && Command::new(Z3_BIN).arg("--version").output().is_err()
    {
        eprintln!("[regex-fuzz-z3] {Z3_BIN} unavailable; skipping (no adjudicator)");
        return;
    }
    let (joint, sat, unsat) = run_against("z3", z3_decide);
    assert!(joint > 50, "too few jointly-decided scripts ({joint})");
    assert!(
        sat > 0 && unsat > 0,
        "expected both verdict directions (sat={sat}, unsat={unsat})"
    );
}

/// cvc5 oracle front (always present when the binary is installed; no feature
/// gate — shells the cvc5 binary as the word-equation crosscheck does).
#[test]
fn regex_membership_differential_fuzz_cvc5_disagree_zero() {
    let Some(bin) = cvc5_bin() else {
        eprintln!("[regex-fuzz-cvc5] cvc5 unavailable; skipping (no adjudicator)");
        return;
    };
    let (joint, sat, unsat) = run_against("cvc5", |text| cvc5_decide(&bin, text, TIMEOUT));
    assert!(joint > 50, "too few jointly-decided scripts ({joint})");
    assert!(
        sat > 0 && unsat > 0,
        "expected both verdict directions (sat={sat}, unsat={unsat})"
    );
}
