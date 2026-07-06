//! Adversarial differential soundness fuzzer for the **online CDCL(T) string
//! route's regex-membership atoms** (P2.7 T-C.6,
//! [`check_qf_s_online_cdclt_with_memberships`](axeyum_solver::check_qf_s_online_cdclt_with_memberships))
//! against the Z3 **and** cvc5 oracles (Z3-only validation is weakest exactly on
//! strings, so cvc5 is provisioned as the independent second string oracle).
//!
//! The route decides Boolean-structured `str.in_re` problems — `or` / `not` over
//! membership atoms, mixed with word equalities — that the one-shot membership
//! side channel declines (its atoms sit under `or` / `not(and)` structure). This
//! sweep also covers the **Phase D** constant-pattern extended functions that lift
//! into the same membership machinery — `str.prefixof` / `str.suffixof` /
//! `str.contains` on a single variable (as `P·Σ*` / `Σ*·S` / `Σ*·C·Σ*`, sound in
//! both polarities). (The Phase D constant-fold `str.replace` word atom is fuzzed
//! separately in `qf_s_replace_fold_differential_fuzz.rs`: a `str.replace` mixed
//! with a regex membership drives the bounded pre-check encoder into a large SAT
//! instance, so the replace fold is exercised over pure word problems there.) It
//! moves the verdict in **both** directions:
//!
//! - `unsat` only through a certified theory conflict: a per-variable regex
//!   intersection (grouped by the equivalence classes word equalities induce)
//!   proven empty behind the re-checked derivative-emptiness certificate;
//! - `sat` only through a model whose per-class witnesses are replayed by the
//!   independent reference matcher and whose membership-atom truths are recomputed
//!   by that matcher on the model's string bindings, then replayed against the
//!   original assertions.
//!
//! Both directions are soundness-gated here against Z3's full string theory:
//!
//! - axeyum `Sat` ∧ Z3 `unsat` → **PANIC** (wrong sat — a fabricated witness);
//! - axeyum `Unsat` ∧ Z3 `sat` → **PANIC** (wrong unsat — an uncertified
//!   emptiness, the worst bug).
//!
//! Method mirrors `word_equation_differential_fuzz.rs`: a fixed-seed LCG (no
//! clock, no OS entropy) drives every choice, so the whole sweep is reproducible.
//! Each script is rendered once as `QF_S` SMT-LIB text and decided two ways — the
//! axeyum front door ([`solve_smtlib`], which routes membership through the online
//! CDCL(T) path once the bounded pre-check declines/downgrades) and the system Z3
//! binary. A tiny `{a,b}` alphabet plus unbounded `re.*`/`re.comp` shapes makes
//! empty intersections (hence certified unsats) frequent, stressing the
//! wrong-unsat gate. The test passes iff disagreements == 0 over the jointly
//! decided scripts.

use std::fmt::Write as _;
use std::time::Duration;

use axeyum_solver::{CheckResult, SolverConfig, solve_smtlib};

mod common_cvc5;
use common_cvc5::{Verdict, cvc5_bin, cvc5_decide};

/// Number of scripts generated and adjudicated (≥ 600 as required).
const INSTANCES: u64 = 700;

/// Per-call Z3 wall-clock budget.
const Z3_TIMEOUT: Duration = Duration::from_secs(3);

/// Path to the system Z3 binary (its full string theory adjudicates; the z3 crate
/// AST has no string sorts, so the text is shelled in).
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

/// The tiny alphabet — a small alphabet makes empty intersections frequent.
const ALPHABET: &[u8] = b"ab";

/// One character of a generated literal: usually a plain `{a,b}` byte, but ~1 in 4
/// an SMT-LIB `\u{…}` escape — for `\n` (`0a`), or `a`/`b` themselves spelled as
/// `\u{61}`/`\u{62}`. This exercises the escape decoder in **both** string-literal
/// and regex-literal positions (the same text is fed to axeyum and Z3, so a decode
/// mismatch surfaces as a differential disagreement). `\u{61}`/`\u{62}` alias the
/// plain letters, so escaped and plain spellings intersect and clash frequently.
fn push_char(rng: &mut Lcg, s: &mut String) {
    if rng.below(4) == 0 {
        match rng.below(3) {
            0 => s.push_str("\\u{0a}"), // newline
            1 => s.push_str("\\u{61}"), // 'a'
            _ => s.push_str("\\u{62}"), // 'b'
        }
    } else {
        s.push(char::from(ALPHABET[rng.below(ALPHABET.len() as u64)]));
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

/// A non-empty short literal (1..=3 characters, some possibly `\u{…}`-escaped), for
/// `str.to_re` (an empty `str.to_re ""` is `ε`; a non-empty one grows the language).
fn gen_nonempty_literal(rng: &mut Lcg) -> String {
    let len = 1 + rng.below(3);
    let mut s = String::new();
    for _ in 0..len {
        push_char(rng, &mut s);
    }
    s
}

/// A `RegLan` regex s-expression over the tiny alphabet, `depth`-bounded.
fn gen_regex(rng: &mut Lcg, depth: u32) -> String {
    if depth == 0 {
        return match rng.below(3) {
            0 => "re.allchar".to_owned(),
            1 => format!("(str.to_re \"{}\")", gen_nonempty_literal(rng)),
            _ => "(re.range \"a\" \"b\")".to_owned(),
        };
    }
    match rng.below(10) {
        0 | 1 => gen_regex(rng, 0),
        2 => format!(
            "(re.++ {} {})",
            gen_regex(rng, depth - 1),
            gen_regex(rng, depth - 1)
        ),
        3 => format!(
            "(re.union {} {})",
            gen_regex(rng, depth - 1),
            gen_regex(rng, depth - 1)
        ),
        4 => format!("(re.* {})", gen_regex(rng, depth - 1)),
        5 => format!("(re.+ {})", gen_regex(rng, depth - 1)),
        6 => format!("(re.opt {})", gen_regex(rng, depth - 1)),
        7 => format!("(re.comp {})", gen_regex(rng, depth - 1)),
        // A bounded loop `(_ re.loop lo hi)` — outside the bounded encoder, so a
        // membership over it takes the word-first parse fallback (the P0 path).
        8 => {
            let lo = rng.below(3);
            let hi = lo + rng.below(3);
            format!("((_ re.loop {lo} {hi}) {})", gen_regex(rng, depth - 1))
        }
        _ => format!(
            "(re.inter {} {})",
            gen_regex(rng, depth - 1),
            gen_regex(rng, depth - 1)
        ),
    }
}

/// A membership atom `(str.in_re sVAR R)` on a single declared variable, or its
/// negation `(not (str.in_re …))`. One time in four the membership is spelled as a
/// **constant-pattern extended-function** atom instead — `str.prefixof` /
/// `str.suffixof` / `str.contains` on a single variable — which the Phase D
/// translation lifts into an exact regex membership (`P·Σ*` / `Σ*·S` / `Σ*·C·Σ*`).
/// Both spellings are decided by the same online route, and both are adjudicated
/// against z3 **and** cvc5, so a faithfulness bug in the extended-function encoding
/// (either polarity) surfaces as a differential disagreement.
fn gen_membership(rng: &mut Lcg, num_vars: usize) -> String {
    let atom = if rng.below(4) == 0 {
        gen_ext_pred(rng, num_vars)
    } else {
        let v = rng.below(num_vars as u64);
        let re = gen_regex(rng, 2);
        format!("(str.in_re s{v} {re})")
    };
    if rng.below(3) == 0 {
        format!("(not {atom})")
    } else {
        atom
    }
}

/// A constant-pattern extended-function predicate on a single variable:
/// `(str.prefixof "lit" sVAR)`, `(str.suffixof "lit" sVAR)`, or
/// `(str.contains sVAR "lit")` — exactly the Phase D regex-membership fragment. The
/// pattern is a short (possibly `\u{…}`-escaped, possibly empty) literal, exercising
/// the boundary shapes (`ε`-prefix ⇒ Σ*, single-char infix, …).
fn gen_ext_pred(rng: &mut Lcg, num_vars: usize) -> String {
    let v = rng.below(num_vars as u64);
    let lit = gen_literal(rng);
    match rng.below(3) {
        0 => format!("(str.prefixof \"{lit}\" s{v})"),
        1 => format!("(str.suffixof \"{lit}\" s{v})"),
        _ => format!("(str.contains s{v} \"{lit}\")"),
    }
}

/// A word-equality atom over the declared variables: `(= si sj)` or `(= si "lit")`.
fn gen_word_atom(rng: &mut Lcg, num_vars: usize) -> String {
    let i = rng.below(num_vars as u64);
    if num_vars > 1 && rng.below(2) == 0 {
        let mut j = rng.below(num_vars as u64);
        if j == i {
            j = (j + 1) % num_vars;
        }
        format!("(= s{i} s{j})")
    } else {
        format!("(= s{i} \"{}\")", gen_literal(rng))
    }
}

/// A full generated `QF_S` membership script as SMT-LIB 2 text.
struct Instance {
    text: String,
}

impl Instance {
    /// Generate a Boolean-structured membership script: 1..=3 declared string
    /// variables and 2..=5 asserts, each one of a top-level membership, a negated
    /// membership, an `or` of memberships, a `(not (and …))` over a word/membership
    /// pair, or a bare word equality — exactly the disjunctive/negated shapes the
    /// one-shot route declines and the online route decides.
    fn generate(rng: &mut Lcg) -> Instance {
        let num_vars = 1 + rng.below(3); // 1..=3
        let num_asserts = 2 + rng.below(4); // 2..=5

        let mut text = String::new();
        text.push_str("(set-logic QF_S)\n");
        for i in 0..num_vars {
            let _ = writeln!(text, "(declare-const s{i} String)");
        }

        for _ in 0..num_asserts {
            let assertion = match rng.below(6) {
                // A bare (positive or negated) membership atom.
                0 => gen_membership(rng, num_vars),
                // A disjunction of two memberships — the `re-mod-eq` shape's core.
                1 | 2 => format!(
                    "(or {} {})",
                    gen_membership(rng, num_vars),
                    gen_membership(rng, num_vars)
                ),
                // `(not (and A B))` — the `re-neg-unfold` shape: a word/membership
                // pair whose conjunction is negated.
                3 => format!(
                    "(not (and {} {}))",
                    gen_word_atom(rng, num_vars),
                    gen_membership(rng, num_vars)
                ),
                // A word equality — merges membership classes (the `re-mod-eq`
                // cross-variable intersection).
                4 => gen_word_atom(rng, num_vars),
                // A conjunction mixing a word atom and a membership.
                _ => format!(
                    "(and {} {})",
                    gen_word_atom(rng, num_vars),
                    gen_membership(rng, num_vars)
                ),
            };
            let _ = writeln!(text, "(assert {assertion})");
        }

        text.push_str("(check-sat)\n");
        Instance { text }
    }
}

/// Decide a script with axeyum's SMT-LIB front door. A `Sat` is already
/// matcher-replayed; any error or `Unknown` is a sound SKIP.
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

/// The shared adjudication loop, parameterized by the oracle. Each generated
/// script is decided by axeyum's front door and by `oracle`; a jointly-decided
/// disagreement in **either** direction is a soundness bug and panics. Returns
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

        // THE SOUNDNESS GATE: a jointly-decided script must AGREE in both
        // directions — a wrong `sat` (vs oracle `unsat`) or a wrong `unsat` (vs
        // oracle `sat`) is a soundness bug.
        if ax == orc {
            agreements += 1;
        } else {
            panic!(
                "DIFFERENTIAL DISAGREEMENT (seed {seed}): axeyum={ax:?} {label}={orc:?} — a {} \
                 soundness bug in the online membership route.\n--- script ---\n{}",
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
         {agreements} agree (ax_sat={axeyum_sat}, ax_unsat={axeyum_unsat}, \
         ax_skip={axeyum_skip}, oracle_skip={oracle_skip})"
    );
    assert_eq!(
        jointly_decided, agreements,
        "every jointly decided membership script must agree with {label}"
    );
    // The sweep must actually exercise the route in both directions, not degenerate
    // to all-Skip: require a floor of joint decisions and at least one unsat (the
    // certified-conflict path) and one sat (the matcher-replay path).
    assert!(
        jointly_decided >= 100,
        "too few joint decisions ({jointly_decided}) — the membership fuzz is not exercising the route"
    );
    assert!(
        axeyum_unsat > 0 && axeyum_sat > 0,
        "the fuzz must exercise both the certified-unsat and matcher-replayed-sat paths \
         (unsat={axeyum_unsat}, sat={axeyum_sat})"
    );
    (jointly_decided, axeyum_sat, axeyum_unsat)
}

/// Z3 oracle front (behind the `z3` feature — the system binary carries the full
/// string theory; the z3 *crate* AST has no string sorts, so the text is shelled).
#[cfg(feature = "z3")]
#[test]
fn qf_s_online_membership_differential_fuzz_z3_disagree_zero() {
    use std::io::Write as _;
    use std::process::{Command, Stdio};

    let z3_decide = |text: &str| -> Verdict {
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
        eprintln!("[mem-fuzz-z3] {Z3_BIN} unavailable; skipping (no adjudicator)");
        return;
    }
    run_against("z3", z3_decide);
}

/// cvc5 oracle front (always present when the binary is installed; no feature
/// gate — shells the cvc5 binary, the second string differential oracle). Z3-only
/// validation is weakest exactly on strings, so cvc5 is the independent check.
#[test]
fn qf_s_online_membership_differential_fuzz_cvc5_disagree_zero() {
    let Some(bin) = cvc5_bin() else {
        eprintln!("[mem-fuzz-cvc5] cvc5 unavailable; skipping (no adjudicator)");
        return;
    };
    run_against("cvc5", |text| cvc5_decide(&bin, text, Z3_TIMEOUT));
}
