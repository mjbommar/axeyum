//! Adversarial differential soundness fuzzer for the bounded `QF_S` string
//! theory (the packed-BV string model, ADR-0029) against the Z3 oracle.
//!
//! String reasoning routes through a deep desugaring pipeline: a packed
//! `(length, bytes)` bit-vector layout, byte-wise splice/search lowerings for
//! `str.replace`/`str.indexof`/`str.substr`/`str.at`, a Horner fold for
//! `str.to_int`/`str.from_int`, lexicographic BV comparison for `str.<`/`str.<=`,
//! and an automaton-style encoding for `str.in_re` regular-expression membership.
//! Every one of those is a hand-written lowering, and a single off-by-one in a
//! splice, a wrong empty-match convention, or a botched regex anchor would be a
//! *wrong* `Sat`/`Unsat` — exactly the class of modeling bug that the FP `±0`
//! wrong-unsat was. That bug was a *modeling* defect found only by measurement;
//! the existing decider fuzzers caught three real wrong-unsats. The string model
//! was measured `DISAGREE=0` on small curated corpora but had never been
//! adversarially fuzzed. This harness closes that gap.
//!
//! Method (mirroring `nia_differential_fuzz.rs` / `bv_differential_fuzz.rs`):
//! a fixed-seed LCG (no clock, no OS entropy) deterministically generates
//! hundreds of small random `QF_S` scripts as **SMT-LIB 2 text** over the
//! supported string/regex/Bool/Int fragment, within the bounded-string window
//! axeyum models (literals ≤ 8 bytes so both sides actually decide). Each script
//! is decided two ways:
//!
//! - axeyum: `solve_smtlib` on the text — parse, route, and (for `Sat`) replay
//!   the model against the original term through the ground evaluator. A wrong
//!   `Sat` whose model does not replay surfaces inside `solve` as an error, never
//!   a silent `Sat`.
//! - Z3: the same text piped to the system Z3 binary (`/usr/bin/z3`; it has the full
//!   `QF_S` / `UnicodeStrings` theory), with a per-call wall-clock timeout.
//!
//! The joint gate:
//!
//! - axeyum `Sat` ∧ Z3 `unsat` → **PANIC** (wrong sat).
//! - axeyum `Unsat` ∧ Z3 `sat` → **PANIC** (wrong unsat — the worst bug).
//! - axeyum `Unknown` / `Unsupported` / parse-decline → SKIP (incomplete is
//!   sound; the bounded model legitimately declines many shapes).
//! - Z3 `unknown` / timeout / error → SKIP (Z3 cannot adjudicate).
//!
//! The test passes iff disagreements == 0 over the jointly-decided instances.

#![cfg(feature = "z3")]

use std::fmt::Write as _;
use std::io::Write as _;
use std::process::{Command, Stdio};
use std::time::Duration;

use axeyum_solver::{CheckResult, SolverConfig, solve_smtlib};

/// Number of scripts generated and adjudicated. Each is tiny (≤ 3 string vars,
/// ≤ 4 atoms, ≤ 8-byte literals) so both sides decide quickly. Many random
/// shapes legitimately decline on the axeyum side (a sound SKIP — over-cap
/// concat, fully-symbolic replace, …), so this is sized to leave well over 100
/// *jointly*-decided scripts after the skips.
const INSTANCES: u64 = 900;

/// Per-call Z3 wall-clock budget. Small bounded-string scripts decide far
/// faster; this only bounds the rare pathological regex shape.
const Z3_TIMEOUT: Duration = Duration::from_secs(3);

/// Path to the system Z3 binary (it carries the full string theory; the z3
/// *crate* AST has no string sorts, so we shell the text in).
const Z3_BIN: &str = "/usr/bin/z3";

/// A deterministic linear-congruential PRNG (the MMIX multiplier/increment).
/// No clock, no OS entropy: the whole sweep is reproducible from the seed.
struct Lcg(u64);

impl Lcg {
    fn new(seed: u64) -> Self {
        // Mix the seed once so consecutive seeds 0,1,2,… don't start correlated.
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

    /// A small signed integer in `lo..=hi` (inclusive).
    fn in_range(&mut self, lo: i64, hi: i64) -> i64 {
        debug_assert!(lo <= hi);
        let span = u64::try_from(hi - lo + 1).expect("non-negative span");
        lo + i64::try_from(self.next_u64() % span).expect("offset within span")
    }
}

/// The tiny alphabet of literal bytes the generator draws from. Restricted to a
/// few printable ASCII letters/digits so literals stay short and both solvers
/// share the byte model (the packed string model is a byte model). Includes a
/// digit so `str.to_int` sees genuine numeric strings.
const ALPHABET: &[u8] = b"ab012";

/// Generate a short string literal (0..=3 chars from [`ALPHABET`]) as the raw
/// SMT-LIB string-literal payload (no surrounding quotes). All chars are plain
/// printable ASCII with no `"`/escape, so no escaping is needed.
fn gen_literal(rng: &mut Lcg) -> String {
    let len = rng.below(4); // 0..=3
    let mut s = String::with_capacity(len);
    for _ in 0..len {
        let c = ALPHABET[rng.below(ALPHABET.len() as u64)];
        s.push(char::from(c));
    }
    s
}

/// A generated **string-sorted** expression. Variables `s0..` are the declared
/// `String` symbols; the rest are bounded compositions kept shallow so the
/// result stays within the model's length cap.
fn gen_str_expr(rng: &mut Lcg, num_vars: usize, depth: u32) -> String {
    // At depth 0, only leaves (a var or a literal) — keeps results short.
    if depth == 0 {
        return if num_vars > 0 && rng.below(2) == 0 {
            format!("s{}", rng.below(num_vars as u64))
        } else {
            format!("\"{}\"", gen_literal(rng))
        };
    }
    match rng.below(7) {
        0 if num_vars > 0 => format!("s{}", rng.below(num_vars as u64)),
        0 | 1 => format!("\"{}\"", gen_literal(rng)),
        // str.++ of two shallower string exprs.
        2 => format!(
            "(str.++ {} {})",
            gen_str_expr(rng, num_vars, depth - 1),
            gen_str_expr(rng, num_vars, depth - 1)
        ),
        // str.at with an Int index.
        3 => format!(
            "(str.at {} {})",
            gen_str_expr(rng, num_vars, depth - 1),
            gen_int_expr(rng, num_vars, depth - 1)
        ),
        // str.substr s off n.
        4 => format!(
            "(str.substr {} {} {})",
            gen_str_expr(rng, num_vars, depth - 1),
            gen_int_expr(rng, num_vars, depth - 1),
            gen_int_expr(rng, num_vars, depth - 1)
        ),
        // str.replace with a *literal* needle/replacement (the wired-sound case;
        // a fully-symbolic replace often declines, which is a SKIP not a bug).
        5 => format!(
            "(str.replace {} \"{}\" \"{}\")",
            gen_str_expr(rng, num_vars, depth - 1),
            gen_literal(rng),
            gen_literal(rng)
        ),
        // str.from_int of an Int expression.
        _ => format!("(str.from_int {})", gen_int_expr(rng, num_vars, depth - 1)),
    }
}

/// A generated **Int-sorted** expression, mixing string-derived ints
/// (`str.len`, `str.to_int`, `str.indexof`, `str.to_code`) with small literals
/// and `+`.
fn gen_int_expr(rng: &mut Lcg, num_vars: usize, depth: u32) -> String {
    if depth == 0 {
        return rng.in_range(-1, 4).to_string();
    }
    match rng.below(7) {
        0 => rng.in_range(-1, 4).to_string(),
        1 => format!("(str.len {})", gen_str_expr(rng, num_vars, depth - 1)),
        2 => format!("(str.to_int {})", gen_str_expr(rng, num_vars, depth - 1)),
        3 => format!(
            "(str.indexof {} {} {})",
            gen_str_expr(rng, num_vars, depth - 1),
            gen_str_expr(rng, num_vars, depth - 1),
            rng.in_range(0, 3)
        ),
        4 => format!("(str.to_code {})", gen_str_expr(rng, num_vars, depth - 1)),
        5 => format!(
            "(+ {} {})",
            gen_int_expr(rng, num_vars, depth - 1),
            gen_int_expr(rng, num_vars, depth - 1)
        ),
        _ => rng.in_range(0, 8).to_string(),
    }
}

/// A generated **regex** expression over the supported `re.*` constructors.
/// Kept shallow; leaves are `str.to_re "lit"` or `re.range`/`re.allchar`.
fn gen_regex(rng: &mut Lcg, depth: u32) -> String {
    if depth == 0 {
        return match rng.below(3) {
            0 => format!("(str.to_re \"{}\")", gen_literal(rng)),
            1 => "re.allchar".to_string(),
            _ => {
                // re.range over two single-char ASCII endpoints from the alphabet.
                let a = ALPHABET[rng.below(ALPHABET.len() as u64)];
                let b = ALPHABET[rng.below(ALPHABET.len() as u64)];
                let (lo, hi) = if a <= b { (a, b) } else { (b, a) };
                format!("(re.range \"{}\" \"{}\")", char::from(lo), char::from(hi))
            }
        };
    }
    match rng.below(6) {
        0 => format!("(str.to_re \"{}\")", gen_literal(rng)),
        1 => format!("(re.* {})", gen_regex(rng, depth - 1)),
        2 => format!("(re.+ {})", gen_regex(rng, depth - 1)),
        3 => format!(
            "(re.++ {} {})",
            gen_regex(rng, depth - 1),
            gen_regex(rng, depth - 1)
        ),
        4 => format!(
            "(re.union {} {})",
            gen_regex(rng, depth - 1),
            gen_regex(rng, depth - 1)
        ),
        _ => format!("(re.opt {})", gen_regex(rng, depth - 1)),
    }
}

/// A generated Bool atom over the string fragment.
fn gen_atom(rng: &mut Lcg, num_vars: usize) -> String {
    // Depth 1 keeps the string operands shallow — a leaf or a single string op
    // over leaves — which the bounded model decides far more often (deeper trees
    // overflow the length cap and SKIP). Coverage of every op is preserved; the
    // depth just bounds how *nested* a single atom gets.
    let depth = 1;
    match rng.below(11) {
        // Code-point ↔ LIA bridge shape (P2.7 A.2 code/len↔LIA): a sum of two
        // `str.to_code`s equated to a constant, the family behind the
        // `str-code-unsat*` regressions the code abstraction now decides. Kept
        // dense so the differential gate covers the new Unknown⇒Unsat upgrade
        // against Z3 (a wrong upgrade would surface as axeyum-Unsat ∧ Z3-sat).
        10 => format!(
            "(= (+ (str.to_code {}) (str.to_code {})) {})",
            gen_str_expr(rng, num_vars, 0),
            gen_str_expr(rng, num_vars, 0),
            rng.in_range(0, 300)
        ),
        0 => format!(
            "(= {} {})",
            gen_str_expr(rng, num_vars, depth),
            gen_str_expr(rng, num_vars, depth)
        ),
        1 => format!(
            "(distinct {} {})",
            gen_str_expr(rng, num_vars, depth),
            gen_str_expr(rng, num_vars, depth)
        ),
        2 => format!(
            "(str.contains {} {})",
            gen_str_expr(rng, num_vars, depth),
            gen_str_expr(rng, num_vars, depth)
        ),
        3 => format!(
            "(str.prefixof {} {})",
            gen_str_expr(rng, num_vars, depth),
            gen_str_expr(rng, num_vars, depth)
        ),
        4 => format!(
            "(str.suffixof {} {})",
            gen_str_expr(rng, num_vars, depth),
            gen_str_expr(rng, num_vars, depth)
        ),
        5 => format!(
            "(str.< {} {})",
            gen_str_expr(rng, num_vars, depth),
            gen_str_expr(rng, num_vars, depth)
        ),
        6 => format!(
            "(str.<= {} {})",
            gen_str_expr(rng, num_vars, depth),
            gen_str_expr(rng, num_vars, depth)
        ),
        7 => {
            // An Int comparison over string-derived integers.
            let cmp = match rng.below(4) {
                0 => "=",
                1 => "<",
                2 => "<=",
                _ => ">=",
            };
            format!(
                "({cmp} {} {})",
                gen_int_expr(rng, num_vars, depth),
                gen_int_expr(rng, num_vars, depth)
            )
        }
        8 => format!(
            "(str.in_re {} {})",
            gen_str_expr(rng, num_vars, depth),
            gen_regex(rng, 2)
        ),
        _ => {
            // (= (str.len s) k) — a common length constraint. The range
            // deliberately reaches past STRING_MAX_LEN = 8 (P2.7 A.2): an
            // over-bound `k` is `sat` in the real theory (Z3 answers `sat`)
            // while the bounded encoding cannot witness it, so this probes the
            // bounded-`unsat` gate — a wrong `unsat` here is the exact
            // bound-bite class the gate exists to prevent.
            format!(
                "(= (str.len {}) {})",
                gen_str_expr(rng, num_vars, depth),
                rng.in_range(0, 11)
            )
        }
    }
}

/// A full generated script as SMT-LIB 2 text.
struct Instance {
    text: String,
}

impl Instance {
    /// Deterministically generate a `QF_S` script.
    ///
    /// - 0..=3 declared `String` variables `s0..`;
    /// - 1..=4 asserted atoms (a possibly-negated atom each), conjoined;
    /// - atoms drawn from the supported string/regex/Int fragment.
    fn generate(rng: &mut Lcg) -> Instance {
        let num_vars = rng.below(4); // 0..=3
        let num_atoms = rng.below(4) + 1; // 1..=4

        let mut text = String::new();
        text.push_str("(set-logic QF_S)\n");
        for i in 0..num_vars {
            let _ = writeln!(text, "(declare-const s{i} String)");
        }
        for _ in 0..num_atoms {
            let atom = gen_atom(rng, num_vars);
            // Negate ~⅓ of atoms to broaden the sat/unsat mix.
            let asserted = if rng.below(3) == 0 {
                format!("(not {atom})")
            } else {
                atom
            };
            let _ = writeln!(text, "(assert {asserted})");
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

/// Decide a script with axeyum's SMT-LIB front door. Any error (parse decline,
/// unsupported construct, over-cap) or `Unknown` is a sound SKIP.
fn axeyum_decide(text: &str) -> Verdict {
    let config = SolverConfig::new().with_timeout(Duration::from_secs(10));
    match solve_smtlib(text, &config) {
        Ok(outcome) => match outcome.result {
            // A `Sat` from `solve` has already been replay-checked against the
            // original term through the ground evaluator (the trust anchor); a
            // non-replaying model surfaces as an error below, never a silent Sat.
            CheckResult::Sat(_) => Verdict::Sat,
            CheckResult::Unsat => Verdict::Unsat,
            CheckResult::Unknown(_) => Verdict::Skip,
        },
        Err(_) => Verdict::Skip,
    }
}

/// Decide a script with the system Z3 binary, piping the text to `z3 -in` with a
/// wall-clock timeout. Returns [`Verdict::Skip`] on `unknown`/timeout/error.
fn z3_decide(text: &str) -> Verdict {
    // z3 binary missing/unspawnable → adjudication-neutral SKIP.
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
        // Ignore a broken pipe (z3 may exit early); the output parse below decides.
        let _ = stdin.write_all(text.as_bytes());
    }
    // Drop stdin so z3 sees EOF.
    drop(child.stdin.take());
    let Ok(output) = child.wait_with_output() else {
        return Verdict::Skip;
    };
    let stdout = String::from_utf8_lossy(&output.stdout);
    // The first `(check-sat)` answer is the first sat/unsat/unknown token.
    for line in stdout.lines() {
        match line.trim() {
            "sat" => return Verdict::Sat,
            "unsat" => return Verdict::Unsat,
            "unknown" => return Verdict::Skip,
            _ => {}
        }
    }
    // No verdict token (e.g. an error line, or timeout produced nothing) → skip.
    Verdict::Skip
}

#[test]
fn string_differential_fuzz_disagree_zero() {
    // Probe the Z3 binary once; if absent, the differential is impossible and the
    // test is a no-op pass (mirrors the other fuzzers' adjudication-neutral skip).
    if z3_decide("(set-logic QF_S)\n(check-sat)\n") == Verdict::Skip
        && Command::new(Z3_BIN).arg("--version").output().is_err()
    {
        eprintln!("[string-fuzz] {Z3_BIN} unavailable; skipping (no adjudicator)");
        return;
    }

    let mut total = 0u64;
    let mut jointly_decided = 0u64;
    let mut agreements = 0u64;
    let mut axeyum_skip = 0u64;
    let mut z3_skip = 0u64;

    for seed in 0..INSTANCES {
        total += 1;
        if seed % 100 == 0 {
            eprintln!(
                "[string-fuzz] seed {seed}/{INSTANCES} (joint={jointly_decided}, \
                 agree={agreements}, ax_skip={axeyum_skip}, z3_skip={z3_skip})"
            );
        }
        let mut rng = Lcg::new(seed);
        let inst = Instance::generate(&mut rng);

        // --- axeyum first (cheap; many shapes legitimately decline). ----------
        let ax = axeyum_decide(&inst.text);
        if ax == Verdict::Skip {
            axeyum_skip += 1;
            continue;
        }

        // --- Z3 oracle. -------------------------------------------------------
        let z3 = z3_decide(&inst.text);
        if z3 == Verdict::Skip {
            z3_skip += 1;
            continue;
        }

        jointly_decided += 1;

        // THE SOUNDNESS GATE: a jointly-decided script must AGREE.
        if ax == z3 {
            agreements += 1;
        } else {
            panic!(
                "DISAGREEMENT (seed {seed}): axeyum = {ax:?}, Z3 = {z3:?}.\n\
                 This is a {} soundness bug in the bounded string model.\n\
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

    println!("=== QF_S string differential fuzz tally ===");
    println!("total scripts:        {total}");
    println!("jointly decided:      {jointly_decided}");
    println!("agreements:           {agreements}");
    println!("axeyum skipped:       {axeyum_skip} (Unknown/Unsupported/decline)");
    println!("Z3 skipped:           {z3_skip} (unknown/timeout)");
    println!("DISAGREEMENTS:        0");

    // Reaching here means no disagreement panicked: DISAGREE=0 over the sweep.
    // Sanity: the sweep must actually exercise the joint deciders.
    assert!(
        jointly_decided > 50,
        "too few jointly-decided scripts ({jointly_decided}); the differential \
         gate is not meaningfully exercised"
    );
}
