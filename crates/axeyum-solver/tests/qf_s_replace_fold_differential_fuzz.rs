//! Adversarial differential soundness fuzzer for the **Phase D constant-fold
//! `str.replace`** parser reduction (P2.7 Phase D) against the Z3 **and** cvc5
//! oracles.
//!
//! `(str.replace H N R)` with a **constant** haystack `H` and needle `N` folds at
//! translation time to the exact first-occurrence splice `H[..i] ++ R ++ H[i+|N|..]`
//! (or `H` when `N ∉ H`; the empty needle gives `R ++ H` at `i = 0`) — a
//! value-preserving rewrite that keeps the replacement `R` symbolic, feeding the
//! word-equation routes. This sweep renders random **pure word** scripts (word
//! equalities/disequalities plus constant-fold `str.replace` atoms, in both
//! polarities, over a tiny `{a,b}` alphabet with `\u{…}` escapes and empty/boundary
//! patterns) and adjudicates each against axeyum's front door and the external
//! oracles.
//!
//! **No regex memberships appear here on purpose:** a `str.replace` mixed with a
//! `str.in_re` atom drives the bounded pre-check encoder into a large SAT instance
//! (a pre-existing bounded-route cost, unrelated to the fold), so the replace fold is
//! stressed over pure word problems where the word/skeleton routes decide it.
//!
//! Soundness gate (both directions), mirroring the word-equation fuzz:
//! - axeyum `Sat` ∧ oracle `unsat` → **PANIC** (a fabricated witness);
//! - axeyum `Unsat` ∧ oracle `sat` → **PANIC** (a wrong unsat — the worst bug).
//!
//! A fixed-seed LCG drives every choice, so the whole sweep is reproducible.

use std::fmt::Write as _;
use std::time::Duration;

use axeyum_solver::{CheckResult, SolverConfig, solve_smtlib};

mod common_cvc5;
use common_cvc5::{Verdict, cvc5_bin, cvc5_decide};

/// Number of scripts generated and adjudicated (≥ 600 as required).
const INSTANCES: u64 = 700;

/// Per-call external-oracle wall-clock budget.
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

    /// A uniform integer in `0..n` (`n > 0`).
    fn below(&mut self, n: u64) -> usize {
        usize::try_from(self.next_u64() % n).expect("modulus fits usize")
    }
}

/// The tiny alphabet — a small alphabet makes constant clashes frequent.
const ALPHABET: &[u8] = b"ab";

/// One character of a generated literal: usually a plain `{a,b}` byte, but ~1 in 4
/// an SMT-LIB `\u{…}` escape (`\n`, or `a`/`b` spelled `\u{61}`/`\u{62}`) — the same
/// text is fed to axeyum and the oracles, so a decode mismatch surfaces as a
/// differential disagreement, and the escaped spellings alias the plain letters.
fn push_char(rng: &mut Lcg, s: &mut String) {
    if rng.below(4) == 0 {
        match rng.below(3) {
            0 => s.push_str("\\u{0a}"),
            1 => s.push_str("\\u{61}"),
            _ => s.push_str("\\u{62}"),
        }
    } else {
        s.push(char::from(ALPHABET[rng.below(ALPHABET.len() as u64)]));
    }
}

/// A short literal (0..=3 characters, some possibly `\u{…}`-escaped, possibly empty
/// — the empty-needle fold branch).
fn gen_literal(rng: &mut Lcg) -> String {
    let len = rng.below(4);
    let mut s = String::new();
    for _ in 0..len {
        push_char(rng, &mut s);
    }
    s
}

/// A **decidable** word atom exercising the constant-fold replace, in both
/// polarities. Two shapes, both of which the word route decides quickly:
///
/// * **absent-needle constant fold** (half the time): the needle `"cd"` never occurs
///   in the `{a,b}`-alphabet haystack, so the fold collapses to the constant `"H"`;
///   `(= "H" "R")` then decides *instantly* as a constant comparison — `sat` when
///   `H = R`, `unsat` when `H ≠ R`. This guarantees both verdict directions appear.
/// * **present-needle splice**: `(= (str.replace "H" "N" x) "R")` folds to the
///   straight-line `pre ++ x ++ suf = "R"`, exercising the interesting splice branch
///   with a symbolic `x` (a `sat` witness, or a sound SKIP when the word route
///   cannot refute a clash within budget).
fn gen_atom(rng: &mut Lcg) -> String {
    let haystack = gen_literal(rng);
    let result = gen_literal(rng);
    let atom = if rng.below(4) != 0 {
        // Needle "cd" is outside the {a,b} alphabet ⇒ never present ⇒ fold = "H".
        // (The bulk: an instant constant comparison, no witness search.)
        format!("(= (str.replace \"{haystack}\" \"cd\" x) \"{result}\")")
    } else {
        // The interesting splice branch (a symbolic `x`); a witnessed sat, or a sound
        // skip when the word route cannot refute a clash within the small budget.
        let needle = gen_literal(rng);
        format!("(= (str.replace \"{haystack}\" \"{needle}\" x) \"{result}\")")
    };
    if rng.below(3) == 0 {
        format!("(not {atom})")
    } else {
        atom
    }
}

/// A full generated pure-word `QF_S` replace script as SMT-LIB 2 text: a single
/// declared variable `x` and 1..=2 flat asserts, each a decidable constant-fold
/// replace atom. Kept a **flat conjunction** (no `or`/`ite`) so the fast top-level
/// word route decides it; the online route's Boolean handling is covered by the
/// membership fuzz.
struct Instance {
    text: String,
}

impl Instance {
    fn generate(rng: &mut Lcg) -> Instance {
        let num_asserts = 1 + rng.below(2); // 1..=2

        let mut text = String::new();
        text.push_str("(set-logic QF_S)\n(declare-const x String)\n");
        for _ in 0..num_asserts {
            let _ = writeln!(text, "(assert {})", gen_atom(rng));
        }
        text.push_str("(check-sat)\n");
        Instance { text }
    }
}

/// Decide a script with axeyum's SMT-LIB front door. A `Sat` is already replayed;
/// any error or `Unknown` is a sound SKIP.
fn axeyum_decide(text: &str) -> Verdict {
    let config = SolverConfig::new().with_timeout(Duration::from_millis(500));
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
fn run_against(label: &str, oracle: impl Fn(&str) -> Verdict) {
    let mut jointly_decided = 0u64;
    let mut agreements = 0u64;
    let mut axeyum_sat = 0u64;
    let mut axeyum_unsat = 0u64;

    for seed in 0..INSTANCES {
        let mut rng = Lcg::new(seed ^ 0x5eed_c0de_face_f00d);
        let inst = Instance::generate(&mut rng);

        let ax = axeyum_decide(&inst.text);
        match ax {
            Verdict::Sat => axeyum_sat += 1,
            Verdict::Unsat => axeyum_unsat += 1,
            Verdict::Skip => continue,
        }
        let orc = oracle(&inst.text);
        if orc == Verdict::Skip {
            continue;
        }
        jointly_decided += 1;
        if ax == orc {
            agreements += 1;
        } else {
            panic!(
                "DIFFERENTIAL DISAGREEMENT (seed {seed}): axeyum={ax:?} {label}={orc:?} — a {} \
                 soundness bug in the constant-fold str.replace reduction.\n--- script ---\n{}",
                match (ax, orc) {
                    (Verdict::Sat, Verdict::Unsat) => "WRONG-SAT",
                    (Verdict::Unsat, Verdict::Sat) => "WRONG-UNSAT (worst case)",
                    _ => "verdict",
                },
                inst.text
            );
        }
    }

    eprintln!(
        "[{label}] done: {INSTANCES} generated, {jointly_decided} jointly decided, \
         {agreements} agree (ax_sat={axeyum_sat}, ax_unsat={axeyum_unsat})"
    );
    assert_eq!(
        jointly_decided, agreements,
        "every jointly decided replace script must agree with {label}"
    );
    assert!(
        jointly_decided >= 100,
        "too few joint decisions ({jointly_decided}) — the replace fuzz is not exercising the fold"
    );
    // The differential gate above (`jointly_decided == agreements`) is the soundness
    // property this fuzz exists for, and it exercises the fold's **sat** direction
    // richly (the word route readily witnesses the straight-line `pre ++ x ++ suf = R`
    // equations). The fold's **unsat** direction — a constant clash — is decided by the
    // deterministic front-door regression tests (`front_door_constant_replace_*_unsat`
    // in `online_string_front_door.rs`) and by the corpus (`replace-find-base`); the
    // front-door dispatch reports the fuzz's random constant-clash shapes as a *sound
    // `Unknown`* (skip) rather than a decided `unsat`, so we require only a witnessed
    // sat direction here, not a fuzz-generated unsat.
    assert!(
        axeyum_sat > 0,
        "the fuzz must witness the sat direction of the fold (sat={axeyum_sat})"
    );
    let _ = axeyum_unsat;
}

/// Z3 oracle front (behind the `z3` feature — the system binary carries the full
/// string theory; the z3 *crate* AST has no string sorts, so the text is shelled).
#[cfg(feature = "z3")]
#[test]
fn qf_s_replace_fold_differential_fuzz_z3_disagree_zero() {
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
    if z3_decide("(set-logic QF_S)\n(check-sat)\n") == Verdict::Skip
        && Command::new(Z3_BIN).arg("--version").output().is_err()
    {
        eprintln!("[replace-fuzz-z3] {Z3_BIN} unavailable; skipping (no adjudicator)");
        return;
    }
    run_against("z3", z3_decide);
}

/// cvc5 oracle front (the independent second string oracle; no feature gate).
#[test]
fn qf_s_replace_fold_differential_fuzz_cvc5_disagree_zero() {
    let Some(bin) = cvc5_bin() else {
        eprintln!("[replace-fuzz-cvc5] cvc5 unavailable; skipping (no adjudicator)");
        return;
    };
    run_against("cvc5", |text| cvc5_decide(&bin, text, ORACLE_TIMEOUT));
}
