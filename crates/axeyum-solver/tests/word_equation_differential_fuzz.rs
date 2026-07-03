//! Adversarial differential soundness fuzzer for the **word-equation route**
//! (ADR-0053, T-B.4b) against the Z3 oracle.
//!
//! The word route runs behind the ADR-0029 bounded pre-check + ADR-0052 gate and
//! may only ever *add* `sat` where they returned `unknown`. Its one soundness
//! risk is therefore a **wrong `sat`**: a model of an equation system that is in
//! fact unsatisfiable (a wrong `unsat` is impossible — the arrangement search has
//! no `unsat` variant, and every `sat` replays through the ground evaluator
//! inside `axeyum-strings` before it is returned). This harness stresses exactly
//! that: it generates hundreds of random pure word-equation scripts — the
//! fragment the parser's dual build recognizes (`str.++` / string literals /
//! string variables, `=` / `distinct` / a single `not (= …)`) — biased toward
//! shapes the bounded encoder cannot decide (long-forcing concatenations and
//! loops), and adjudicates the front door against Z3's full string theory.
//!
//! Method mirrors `string_differential_fuzz.rs` / `bv_differential_fuzz.rs`: a
//! fixed-seed LCG (no clock, no OS entropy) drives every choice, so the whole
//! sweep is reproducible from the seed. Each script is decided two ways:
//!
//! - axeyum: [`solve_smtlib`] on the text — parse, bounded pre-check, gate, then
//!   the word route; a `Sat` has already been replay-checked, an `Unknown` /
//!   parse-decline is an adjudication-neutral SKIP.
//! - Z3: the same text piped to the system Z3 binary (`/usr/bin/z3`, full `QF_S`),
//!   with a per-call wall-clock timeout.
//!
//! The joint gate:
//!
//! - axeyum `Sat` ∧ Z3 `unsat` → **PANIC** (wrong sat — the bug this closes).
//! - axeyum `Unsat` ∧ Z3 `sat` → **PANIC** (wrong unsat — the worst bug).
//! - axeyum `Unknown` / decline → SKIP (incomplete is sound).
//! - Z3 `unknown` / timeout / error → SKIP (Z3 cannot adjudicate).
//!
//! The test passes iff disagreements == 0 over the jointly-decided scripts.

#![cfg(feature = "z3")]

use std::fmt::Write as _;
use std::io::Write as _;
use std::process::{Command, Stdio};
use std::time::Duration;

use axeyum_solver::{CheckResult, SolverConfig, solve_smtlib};

/// Number of scripts generated and adjudicated (≥ 300 as required by T-B.4b).
const INSTANCES: u64 = 600;

/// Per-call Z3 wall-clock budget. Small word-equation scripts decide fast; this
/// only bounds the rare pathological shape.
const Z3_TIMEOUT: Duration = Duration::from_secs(3);

/// Path to the system Z3 binary (it carries the full string theory; the z3
/// *crate* AST has no string sorts, so we shell the text in — as
/// `string_differential_fuzz.rs` does).
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

/// The tiny alphabet of literal characters. A small alphabet makes literal
/// clashes (and hence unsats) frequent, so the wrong-sat gate is stressed.
const ALPHABET: &[u8] = b"ab";

/// A short literal (0..=3 chars) — plain printable ASCII, no escaping needed.
fn gen_short_literal(rng: &mut Lcg) -> String {
    let len = rng.below(4); // 0..=3
    let mut s = String::with_capacity(len);
    for _ in 0..len {
        s.push(char::from(ALPHABET[rng.below(ALPHABET.len() as u64)]));
    }
    s
}

/// A maximal 8-byte literal (= the bounded `max_len`), used to force a witness
/// past the bound so the word route — not the bounded encoder — decides.
fn gen_long_literal(rng: &mut Lcg) -> String {
    let mut s = String::with_capacity(8);
    for _ in 0..8 {
        s.push(char::from(ALPHABET[rng.below(ALPHABET.len() as u64)]));
    }
    s
}

/// A string-sorted expression: a variable, a literal, or a shallow `str.++`.
/// `depth`-bounded and `str.++` kept binary so the summed bounded-encoder width
/// stays representable (a chain that overflows the cap simply makes axeyum SKIP,
/// which is adjudication-neutral, but keeping it shallow yields more joint
/// decisions).
fn gen_str_expr(rng: &mut Lcg, num_vars: usize, depth: u32) -> String {
    if depth == 0 {
        return leaf(rng, num_vars);
    }
    match rng.below(6) {
        0 | 1 => leaf(rng, num_vars),
        // str.++ of two shallower expressions; at depth ≥ 2 (the "hard" path)
        // occasionally seed a maximal literal to force a past-the-bound witness.
        _ => {
            let l = if depth >= 2 && rng.below(4) == 0 {
                format!("\"{}\"", gen_long_literal(rng))
            } else {
                gen_str_expr(rng, num_vars, depth - 1)
            };
            let r = gen_str_expr(rng, num_vars, depth - 1);
            format!("(str.++ {l} {r})")
        }
    }
}

/// A leaf string expression: a declared variable or a short literal.
fn leaf(rng: &mut Lcg, num_vars: usize) -> String {
    if num_vars > 0 && rng.below(2) == 0 {
        format!("s{}", rng.below(num_vars as u64))
    } else {
        format!("\"{}\"", gen_short_literal(rng))
    }
}

/// A full generated word-equation script as SMT-LIB 2 text.
struct Instance {
    text: String,
}

impl Instance {
    /// Deterministically generate a pure word-equation `QF_S` script.
    ///
    /// A difficulty mix keeps the sweep both *decidable enough* (so many scripts
    /// are jointly adjudicated) and *hard enough* (so the word route actually
    /// decides some): `hard` scripts seed long literals and loops the bounded
    /// encoder cannot decide (routing to the word search); `easy` scripts stay
    /// entirely within the bounded `max_len` (so the bounded path decides them and
    /// the word route is a no-op). The soundness gate covers **both** — every
    /// axeyum `Sat`, from either path, is checked against Z3.
    ///
    /// - 2..=4 declared `String` variables `s0..`;
    /// - 1..=4 equalities and 0..=2 disequalities over `str.++`/literals/vars;
    /// - an occasional loop `si = lit ++ si` (an unsat shape the bounded gate
    ///   downgrades, exercising the word route's decline).
    fn generate(rng: &mut Lcg) -> Instance {
        let hard = rng.below(2) == 0;
        let num_vars = rng.below(3) + 2; // 2..=4
        let num_eqs = if hard {
            rng.below(3) + 2 // 2..=4
        } else {
            rng.below(2) + 1 // 1..=2
        };
        let num_diseqs = rng.below(3); // 0..=2
        let depth = if hard { 2 } else { 1 };

        let mut text = String::new();
        text.push_str("(set-logic QF_S)\n");
        for i in 0..num_vars {
            let _ = writeln!(text, "(declare-const s{i} String)");
        }

        for _ in 0..num_eqs {
            if hard && rng.below(6) == 0 {
                // A loop: si = <literal> ++ si.
                let i = rng.below(num_vars as u64);
                let lit = gen_short_literal(rng);
                let _ = writeln!(text, "(assert (= s{i} (str.++ \"{lit}\" s{i})))");
            } else {
                let l = gen_str_expr(rng, num_vars, depth);
                let r = gen_str_expr(rng, num_vars, depth);
                let _ = writeln!(text, "(assert (= {l} {r}))");
            }
        }
        for _ in 0..num_diseqs {
            let l = gen_str_expr(rng, num_vars, 1);
            let r = gen_str_expr(rng, num_vars, 1);
            // Alternate the two disequality spellings the dual build recognizes.
            if rng.below(2) == 0 {
                let _ = writeln!(text, "(assert (not (= {l} {r})))");
            } else {
                let _ = writeln!(text, "(assert (distinct {l} {r}))");
            }
        }

        text.push_str("(check-sat)\n");
        Instance { text }
    }
}

/// A coarse verdict label.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Verdict {
    Sat,
    Unsat,
    /// Unknown / unsupported / declined / timeout — adjudication-neutral.
    Skip,
}

/// Decide a script with axeyum's SMT-LIB front door (bounded pre-check + gate +
/// word route). Any error or `Unknown` is a sound SKIP.
fn axeyum_decide(text: &str) -> Verdict {
    let config = SolverConfig::new().with_timeout(Duration::from_secs(10));
    match solve_smtlib(text, &config) {
        Ok(outcome) => match outcome.result {
            // A `Sat` has already been replay-checked against the original
            // equalities/disequalities through the ground evaluator (the word
            // route's trust anchor), so it is never a silent wrong sat.
            CheckResult::Sat(_) => Verdict::Sat,
            CheckResult::Unsat => Verdict::Unsat,
            CheckResult::Unknown(_) => Verdict::Skip,
        },
        Err(_) => Verdict::Skip,
    }
}

/// Decide a script with the system Z3 binary, piping the text to `z3 -in`.
fn z3_decide(text: &str) -> Verdict {
    let Ok(mut child) = Command::new(Z3_BIN)
        .arg(format!("-T:{}", Z3_TIMEOUT.as_secs().max(1)))
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
    let stdout = String::from_utf8_lossy(&output.stdout);
    for line in stdout.lines() {
        match line.trim() {
            "sat" => return Verdict::Sat,
            "unsat" => return Verdict::Unsat,
            "unknown" => return Verdict::Skip,
            _ => {}
        }
    }
    Verdict::Skip
}

#[test]
fn word_equation_differential_fuzz_disagree_zero() {
    // Probe the Z3 binary once; if absent, the differential is impossible and the
    // test is a no-op pass (mirrors the other fuzzers' adjudication-neutral skip).
    if z3_decide("(set-logic QF_S)\n(check-sat)\n") == Verdict::Skip
        && Command::new(Z3_BIN).arg("--version").output().is_err()
    {
        eprintln!("[word-fuzz] {Z3_BIN} unavailable; skipping (no adjudicator)");
        return;
    }

    let mut total = 0u64;
    let mut jointly_decided = 0u64;
    let mut agreements = 0u64;
    let mut axeyum_sat = 0u64;
    let mut axeyum_skip = 0u64;
    let mut z3_skip = 0u64;

    for seed in 0..INSTANCES {
        total += 1;
        if seed % 100 == 0 {
            eprintln!(
                "[word-fuzz] seed {seed}/{INSTANCES} (joint={jointly_decided}, \
                 agree={agreements}, ax_sat={axeyum_sat}, ax_skip={axeyum_skip}, z3_skip={z3_skip})"
            );
        }
        let mut rng = Lcg::new(seed);
        let inst = Instance::generate(&mut rng);

        let ax = axeyum_decide(&inst.text);
        if ax == Verdict::Sat {
            axeyum_sat += 1;
        }
        if ax == Verdict::Skip {
            axeyum_skip += 1;
            continue;
        }

        let z3 = z3_decide(&inst.text);
        if z3 == Verdict::Skip {
            z3_skip += 1;
            continue;
        }

        jointly_decided += 1;

        // THE SOUNDNESS GATE: a jointly-decided script must AGREE. In particular
        // no axeyum `Sat` may face a Z3 `unsat` (the word route's wrong-sat risk).
        if ax == z3 {
            agreements += 1;
        } else {
            panic!(
                "DISAGREEMENT (seed {seed}): axeyum = {ax:?}, Z3 = {z3:?}.\n\
                 This is a {} soundness bug in the word-equation route.\n\
                 script:\n{}",
                match (ax, z3) {
                    (Verdict::Sat, Verdict::Unsat) => "WRONG-SAT",
                    (Verdict::Unsat, Verdict::Sat) => "WRONG-UNSAT (worst case)",
                    _ => "verdict",
                },
                inst.text
            );
        }
    }

    println!("=== word-equation differential fuzz tally ===");
    println!("total scripts:        {total}");
    println!("jointly decided:      {jointly_decided}");
    println!("agreements:           {agreements}");
    println!("axeyum Sat:           {axeyum_sat}");
    println!("axeyum skipped:       {axeyum_skip} (Unknown/decline)");
    println!("Z3 skipped:           {z3_skip} (unknown/timeout)");
    println!("DISAGREEMENTS:        0");

    assert!(
        jointly_decided > 50,
        "too few jointly-decided scripts ({jointly_decided}); the differential \
         gate is not meaningfully exercised"
    );
}
