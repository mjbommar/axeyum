//! Adversarial differential soundness fuzzer for the **lexicographic-order string
//! route** (P2.7 T-C.6, [`lex_order_verdict`](axeyum_solver::lex_order_verdict) /
//! the `solve_smtlib` front door) against the Z3 **and** cvc5 oracles (Z3-only
//! validation is weakest exactly on strings, so cvc5 is the independent second
//! string oracle).
//!
//! The route decides Boolean combinations of `str.<=` / `str.<` and word-equality
//! atoms over words (literals / variables / `str.++` of those) that the bounded
//! encoder downgraded to `unknown` (a coarse lex atom). It only ever *adds* a
//! re-checked `unsat`:
//!
//! - a variable-independent **constant fold** (some lex atoms decide at the first
//!   determined differing code point; folding them can drive an assertion to
//!   `false`), or
//! - a **transitivity + first-character clash** over the forced-true `≤` atoms
//!   (`s ≤* t` with `lead(s) > lead(t)` fixed by word equalities).
//!
//! Both the wrong-`unsat` and (via the bounded encoder's `sat`) the wrong-`sat`
//! direction are soundness-gated:
//!
//! - axeyum `Unsat` ∧ oracle `sat` → **PANIC** (wrong unsat — the worst case, an
//!   uncertified lex contradiction);
//! - axeyum `Sat` ∧ oracle `unsat` → **PANIC** (wrong sat — a bounded-encoder
//!   witness the lex route failed to override; caught here for completeness).
//!
//! Method mirrors `qf_s_online_membership_differential_fuzz.rs`: a fixed-seed LCG
//! (no clock, no OS entropy) drives every choice, so the whole sweep is
//! reproducible. Each script is rendered once as `QF_SLIA` SMT-LIB text and decided
//! two ways — the axeyum front door and the system oracle binary. The alphabet is a
//! tiny set of code points (letters plus `\u{…}` escapes and boundary/`>0xFF` code
//! points) so first-character clashes — hence certified unsats — are frequent. The
//! test passes iff disagreements == 0 over the jointly decided scripts.

use std::fmt::Write as _;
use std::time::Duration;

use axeyum_solver::{CheckResult, SolverConfig, solve_smtlib};

mod common_cvc5;
use common_cvc5::{Verdict, cvc5_bin, cvc5_decide};

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

    /// A uniform integer in `0..n` (`n > 0`).
    fn below(&mut self, n: u64) -> usize {
        usize::try_from(self.next_u64() % n).expect("modulus fits usize")
    }
}

/// One character of a generated literal. Usually a plain ASCII letter from a small
/// set (so first-character clashes are frequent), but ~1 in 5 an SMT-LIB `\u{…}`
/// escape — the boundary `\u{0a}` (newline), `\u{41}` (aliases `A`), and the
/// top-of-byte-model boundary `\u{ff}` — exercising the escape decoder in code-point
/// order. The literals stay within the `0..=0xff` bounded byte model (a `>0xFF`
/// literal is rejected at parse time by the ADR-0029 encoder — a sound but
/// route-bypassing SKIP — so it would not exercise the lex route). `\u{41}` aliases
/// `A`, so escaped and plain spellings intersect and clash.
fn push_char(rng: &mut Lcg, s: &mut String) {
    if rng.below(5) == 0 {
        match rng.below(3) {
            0 => s.push_str("\\u{0a}"), // newline (low boundary)
            1 => s.push_str("\\u{41}"), // 'A' (aliases plain letter)
            _ => s.push_str("\\u{ff}"), // top of the byte model
        }
    } else {
        // A small ASCII set A..E / a..e — adjacent code points ⇒ frequent clashes.
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

/// A non-empty short literal (1..=3 characters).
fn gen_nonempty_literal(rng: &mut Lcg) -> String {
    let len = 1 + rng.below(3);
    let mut s = String::new();
    for _ in 0..len {
        push_char(rng, &mut s);
    }
    s
}

/// A **word** s-expression: a string literal, a declared variable, or a `str.++` of
/// literals and variables (a constant-prefixed / -suffixed span). These are exactly
/// the operands the lex refuter's word model recognizes.
fn gen_word(rng: &mut Lcg, num_vars: usize) -> String {
    match rng.below(6) {
        0 => format!("\"{}\"", gen_literal(rng)),
        1 | 2 => format!("s{}", rng.below(num_vars as u64)),
        3 => format!(
            "(str.++ \"{}\" s{})",
            gen_nonempty_literal(rng),
            rng.below(num_vars as u64)
        ),
        4 => format!(
            "(str.++ s{} \"{}\")",
            rng.below(num_vars as u64),
            gen_nonempty_literal(rng)
        ),
        _ => format!("(str.++ \"{}\" \"{}\")", gen_literal(rng), gen_literal(rng)),
    }
}

/// A lexicographic-order atom `(str.<= A B)` or `(str.< A B)`.
fn gen_lex_atom(rng: &mut Lcg, num_vars: usize) -> String {
    let op = if rng.below(2) == 0 { "str.<=" } else { "str.<" };
    format!(
        "({op} {} {})",
        gen_word(rng, num_vars),
        gen_word(rng, num_vars)
    )
}

/// A word-equality atom `(= si WORD)` (biased to a single-variable left so it feeds
/// the refuter's substitution) or `(= A B)`.
fn gen_eq_atom(rng: &mut Lcg, num_vars: usize) -> String {
    if rng.below(4) == 0 {
        format!(
            "(= {} {})",
            gen_word(rng, num_vars),
            gen_word(rng, num_vars)
        )
    } else {
        format!(
            "(= s{} {})",
            rng.below(num_vars as u64),
            gen_word(rng, num_vars)
        )
    }
}

/// A single asserted formula — a bare / negated / `or` / `and` / `=>` combination of
/// lex-order and word-equality atoms (the Boolean shapes the refuter folds).
fn gen_assertion(rng: &mut Lcg, num_vars: usize) -> String {
    match rng.below(8) {
        0 => gen_lex_atom(rng, num_vars),
        1 => format!("(not {})", gen_lex_atom(rng, num_vars)),
        2 => gen_eq_atom(rng, num_vars),
        3 | 4 => format!(
            "(or {} {})",
            gen_lex_atom(rng, num_vars),
            gen_lex_atom(rng, num_vars)
        ),
        5 => format!(
            "(or (not {}) {} {})",
            gen_lex_atom(rng, num_vars),
            gen_lex_atom(rng, num_vars),
            gen_lex_atom(rng, num_vars)
        ),
        6 => format!(
            "(and {} {})",
            gen_eq_atom(rng, num_vars),
            gen_lex_atom(rng, num_vars)
        ),
        _ => format!(
            "(=> {} {})",
            gen_lex_atom(rng, num_vars),
            gen_lex_atom(rng, num_vars)
        ),
    }
}

/// A full generated `QF_SLIA` lex-order script as SMT-LIB 2 text.
struct Instance {
    text: String,
}

impl Instance {
    /// Generate a lex-order script: 2..=4 declared string variables, then either a
    /// **transitivity-chain template** (a `≤` chain `s0 ≤ s1 ≤ … ≤ sk` plus a couple
    /// of first-character-fixing equalities — the shape that drives Arm B's clash) or
    /// a **free-form** mix of 2..=6 Boolean assertions over lex/equality atoms.
    fn generate(rng: &mut Lcg) -> Instance {
        let num_vars = 2 + rng.below(3); // 2..=4
        let mut text = String::new();
        text.push_str("(set-logic QF_SLIA)\n");
        for i in 0..num_vars {
            let _ = writeln!(text, "(declare-const s{i} String)");
        }

        if rng.below(2) == 0 {
            // Transitivity-chain template: connect the variables in a `≤` chain, then
            // pin some first characters with equalities (frequently forcing a clash).
            let order = if rng.below(2) == 0 { "str.<=" } else { "str.<" };
            for i in 0..num_vars - 1 {
                let _ = writeln!(text, "(assert ({order} s{i} s{}))", i + 1);
            }
            // Pin the endpoints' leading characters — a high-first-char head on an
            // early var and a low constant on a late var makes the chain unsat.
            let hi = gen_nonempty_literal(rng);
            let lo = gen_literal(rng);
            let _ = writeln!(text, "(assert (= s0 (str.++ \"{hi}\" s{})))", num_vars - 1);
            let _ = writeln!(text, "(assert (= s{} \"{lo}\"))", num_vars - 1);
            // A little extra free-form noise.
            if rng.below(2) == 0 {
                let _ = writeln!(text, "(assert {})", gen_assertion(rng, num_vars));
            }
        } else {
            let num_asserts = 2 + rng.below(5); // 2..=6
            for _ in 0..num_asserts {
                let _ = writeln!(text, "(assert {})", gen_assertion(rng, num_vars));
            }
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
/// disagreement in either direction is a soundness bug and panics. Returns
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
                "[{label}] seed {seed}/{INSTANCES} (joint={jointly_decided}, \
                 agree={agreements}, ax_sat={axeyum_sat}, ax_unsat={axeyum_unsat}, \
                 ax_skip={axeyum_skip}, oracle_skip={oracle_skip})"
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

        let orc = oracle(&inst.text);
        if orc == Verdict::Skip {
            oracle_skip += 1;
            continue;
        }
        jointly_decided += 1;

        // THE SOUNDNESS GATE: a jointly-decided script must AGREE in both directions.
        if ax == orc {
            agreements += 1;
        } else {
            panic!(
                "DIFFERENTIAL DISAGREEMENT (seed {seed}): axeyum={ax:?} {label}={orc:?} — a {} \
                 soundness bug in the lexicographic-order route.\n--- script ---\n{}",
                match (ax, orc) {
                    (Verdict::Unsat, Verdict::Sat) => "WRONG-UNSAT (worst case)",
                    (Verdict::Sat, Verdict::Unsat) => "WRONG-SAT",
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
        "every jointly decided lex-order script must agree with {label}"
    );
    assert!(
        jointly_decided >= 100,
        "too few joint decisions ({jointly_decided}) — the lex fuzz is not exercising the route"
    );
    // The sweep must exercise the certified-unsat path (the lex route's only output)
    // and satisfiable scripts (the bounded encoder's `sat`, which the lex route must
    // not override).
    assert!(
        axeyum_unsat > 0 && axeyum_sat > 0,
        "the fuzz must exercise both certified-unsat and sat paths \
         (unsat={axeyum_unsat}, sat={axeyum_sat})"
    );
    (jointly_decided, axeyum_sat, axeyum_unsat)
}

/// Z3 oracle front (behind the `z3` feature — the system binary carries the full
/// string theory; the z3 *crate* AST has no string sorts, so the text is shelled).
#[cfg(feature = "z3")]
#[test]
fn qf_slia_lex_order_differential_fuzz_z3_disagree_zero() {
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
        eprintln!("[lex-fuzz-z3] {Z3_BIN} unavailable; skipping (no adjudicator)");
        return;
    }
    run_against("z3", z3_decide);
}

/// cvc5 oracle front (always present when the binary is installed; the second
/// string differential oracle).
#[test]
fn qf_slia_lex_order_differential_fuzz_cvc5_disagree_zero() {
    let Some(bin) = cvc5_bin() else {
        eprintln!("[lex-fuzz-cvc5] cvc5 unavailable; skipping (no adjudicator)");
        return;
    };
    run_against("cvc5", |text| cvc5_decide(&bin, text, ORACLE_TIMEOUT));
}
