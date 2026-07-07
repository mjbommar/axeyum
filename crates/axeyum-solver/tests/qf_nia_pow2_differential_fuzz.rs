//! Adversarial differential soundness fuzzer for the `QF_NIA` `int.pow2` wiring
//! (P2.5 slice 6, task #41) against the Z3 oracle.
//!
//! `int.pow2` follows cvc5's TOTAL semantics verbatim: `pow2(x) = 2^x` for
//! `x ≥ 0` and the DEFINED value `pow2(x) = 0` for `x < 0`. Z3 has no native
//! `int.pow2`, so each generated instance is rendered TWICE over the SAME
//! variables/bounds/atoms: native `(int.pow2 v)` for axeyum, and — for Z3 — an
//! INDEPENDENT nested-`ite` encoding of the exact semantics
//! `(ite (< v 0) 0 (ite (= v 0) 1 (ite (= v 1) 2 … (ite (= v hi) 2^hi) 0)))`
//! over `v`'s proven `[lo, hi]` window (ground-truth `2^k`; shares no code with
//! axeyum's abstraction/axioms). Z3 decides that pure-LIA/ITE query exactly.
//!
//! Per the HARD RULE, the generator DELIBERATELY emits the degenerate exponent
//! arguments the semantics is most fragile on: every `pow2` variable's lower
//! bound can be negative (the underspecified-looking `x < 0` case, which cvc5
//! DEFINES to `0`) and its window always contains `0` (`pow2(0) = 1`, the branch
//! boundary). Without those seeds the gate is blind on exactly the axis where a
//! wrong verdict would hide.
//!
//! - axeyum `Sat` ∧ Z3 `unsat` → PANIC (wrong sat).
//! - axeyum `Unsat` ∧ Z3 `sat` → PANIC (wrong unsat — the worst bug).
//! - axeyum `Unknown` is ALLOWED (incomplete is sound) — counted, never failed.
//! - Z3 `unknown`/timeout/unavailable → the instance is skipped.
//!
//! The test passes iff disagreements == 0. axeyum `Sat` is additionally
//! replay-checked in `solve_smtlib` (against the ORIGINAL `pow2` term under the
//! ground evaluator), so a fabricated model can never be reported `Sat`.

#![cfg(feature = "z3")]

use std::fmt::Write as _;
use std::io::Write as _;
use std::process::{Command, Stdio};
use std::time::Duration;

use axeyum_solver::{CheckResult, SolverConfig, solve_smtlib};

const Z3_BIN: &str = "/usr/bin/z3";
const INSTANCES: u64 = 3000;
const ORACLE_TIMEOUT: Duration = Duration::from_secs(3);

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Verdict {
    Sat,
    Unsat,
    Skip,
}

/// A deterministic LCG (MMIX multiplier/increment). No clock/OS entropy.
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
    fn below(&mut self, n: u64) -> u64 {
        self.next_u64() % n
    }
    fn index(&mut self, n: usize) -> usize {
        usize::try_from(self.below(n as u64)).expect("index fits usize")
    }
    fn range(&mut self, lo: i64, hi: i64) -> i64 {
        let span = u64::try_from(hi - lo + 1).expect("nonnegative span");
        lo + i64::try_from(self.below(span)).expect("offset fits i64")
    }
}

/// The independent Z3 encoding of `(int.pow2 v)` for a variable `v` proven to lie
/// in `[lo, hi]`: exact ground-truth `2^k` case split, `0` for the (`lo`-covered)
/// negative branch. Chains over the whole non-negative window `0..=hi` so it is
/// correct regardless of `lo`.
fn pow2_ite(v: &str, hi: i64) -> String {
    // Innermost fallthrough (unreachable given the bounds) is 0.
    let mut expr = String::from("0");
    for k in (0..=hi.max(0)).rev() {
        let val: i64 = 1i64 << k;
        expr = format!("(ite (= {v} {k}) {val} {expr})");
    }
    format!("(ite (< {v} 0) 0 {expr})")
}

/// A generated instance: the two rendered scripts over the SAME vocabulary.
struct Instance {
    axeyum_text: String,
    z3_text: String,
}

impl Instance {
    fn generate(rng: &mut Lcg) -> Instance {
        let names = ["x", "y", "z"];
        let nvars = rng.index(3) + 1; // 1..=3 vars
        let mut decls = String::new();
        let mut bounds = String::new();
        // Per-variable window. Lower bound may be negative (the DEGENERATE
        // negative-exponent seed); the window always includes 0 (`pow2(0)=1`),
        // and `hi` is kept small so `2^hi` and the enumeration stay tiny.
        let mut his: Vec<i64> = Vec::with_capacity(nvars);
        for name in names.iter().take(nvars) {
            let lo = rng.range(-4, 0); // ≤ 0 ⇒ window always contains 0
            let width = [3i64, 5, 8, 12][rng.index(4)];
            let hi = lo + width;
            his.push(hi);
            let _ = writeln!(decls, "(declare-fun {name} () Int)");
            let _ = writeln!(bounds, "(assert (<= {lo} {name}))");
            let _ = writeln!(bounds, "(assert (<= {name} {hi}))");
        }

        let natoms = rng.index(4) + 2; // 2..=5 atoms
        let mut ax_atoms = String::new();
        let mut z3_atoms = String::new();
        for _ in 0..natoms {
            let ai = rng.index(nvars);
            let an = names[ai];
            let bn = names[rng.index(nvars)];
            let cmp = ["<", "<=", ">", ">=", "="][rng.index(5)];
            match rng.below(4) {
                0 | 1 => {
                    // pow2 atom: (cmp (int.pow2 a) rhs).
                    let rhs = rng.range(-2, (1i64 << his[ai].max(0)) + 2);
                    let _ = writeln!(ax_atoms, "(assert ({cmp} (int.pow2 {an}) {rhs}))");
                    let _ = writeln!(z3_atoms, "(assert ({cmp} {} {rhs}))", pow2_ite(an, his[ai]));
                }
                2 => {
                    // pow2-vs-pow2 atom (monotonicity axis).
                    let bi = rng.index(nvars);
                    let bn2 = names[bi];
                    let _ = writeln!(
                        ax_atoms,
                        "(assert ({cmp} (int.pow2 {an}) (int.pow2 {bn2})))"
                    );
                    let _ = writeln!(
                        z3_atoms,
                        "(assert ({cmp} {} {}))",
                        pow2_ite(an, his[ai]),
                        pow2_ite(bn2, his[bi])
                    );
                }
                _ => {
                    // linear/product atom (shared verbatim).
                    let rhs = rng.range(-8, 60);
                    let atom = if rng.below(2) == 0 {
                        format!("(assert ({cmp} (+ {an} {bn}) {rhs}))\n")
                    } else {
                        format!("(assert ({cmp} (* {an} {bn}) {rhs}))\n")
                    };
                    ax_atoms.push_str(&atom);
                    z3_atoms.push_str(&atom);
                }
            }
        }

        let axeyum_text = format!("(set-logic QF_NIA)\n{decls}{bounds}{ax_atoms}(check-sat)\n");
        let z3_text = format!("(set-logic ALL)\n{decls}{bounds}{z3_atoms}(check-sat)\n");
        Instance {
            axeyum_text,
            z3_text,
        }
    }
}

fn axeyum_decide(text: &str) -> Verdict {
    let cfg = SolverConfig {
        timeout: Some(Duration::from_secs(4)),
        ..SolverConfig::default()
    };
    match solve_smtlib(text, &cfg) {
        Ok(o) => match o.result {
            CheckResult::Sat(_) => Verdict::Sat,
            CheckResult::Unsat => Verdict::Unsat,
            CheckResult::Unknown(_) => Verdict::Skip,
        },
        Err(_) => Verdict::Skip,
    }
}

fn z3_decide(text: &str) -> Verdict {
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
}

#[test]
fn qf_nia_pow2_differential_fuzz_z3_disagree_zero() {
    if z3_decide("(set-logic ALL)\n(check-sat)\n") == Verdict::Skip
        && Command::new(Z3_BIN).arg("--version").output().is_err()
    {
        eprintln!("[pow2-fuzz-z3] {Z3_BIN} unavailable; skipping (no adjudicator)");
        return;
    }

    let mut jointly_decided = 0u64;
    let mut agreements = 0u64;
    let mut ax_sat = 0u64;
    let mut ax_unsat = 0u64;
    let mut disagreements: Vec<(u64, Verdict, Verdict, String)> = Vec::new();

    for seed in 0..INSTANCES {
        let mut rng = Lcg::new(seed);
        let inst = Instance::generate(&mut rng);
        let ax = axeyum_decide(&inst.axeyum_text);
        match ax {
            Verdict::Sat => ax_sat += 1,
            Verdict::Unsat => ax_unsat += 1,
            Verdict::Skip => {}
        }
        if ax == Verdict::Skip {
            continue;
        }
        let z3 = z3_decide(&inst.z3_text);
        if z3 == Verdict::Skip {
            continue;
        }
        jointly_decided += 1;
        if ax == z3 {
            agreements += 1;
        } else if disagreements.len() < 10 {
            disagreements.push((seed, ax, z3, inst.axeyum_text.clone()));
        }
    }

    if !disagreements.is_empty() {
        for (seed, ax, z3, text) in &disagreements {
            let kind = match (ax, z3) {
                (Verdict::Unsat, Verdict::Sat) => "WRONG-UNSAT (worst case)",
                (Verdict::Sat, Verdict::Unsat) => "WRONG-SAT",
                _ => "disagree",
            };
            eprintln!("[pow2-fuzz] seed {seed}: axeyum={ax:?} z3={z3:?} — {kind}\n{text}");
        }
        panic!(
            "pow2 differential fuzz found {} disagreement(s) vs Z3 — soundness bug",
            disagreements.len()
        );
    }

    eprintln!(
        "[pow2-fuzz] {jointly_decided} jointly decided, {agreements} agree \
         (ax_sat={ax_sat}, ax_unsat={ax_unsat})"
    );
    assert!(
        ax_sat > 0 && ax_unsat > 0,
        "fuzz must exercise both sat and unsat pow2 decisions (sat={ax_sat}, unsat={ax_unsat})"
    );
    assert!(
        jointly_decided > 100,
        "too few jointly-decided instances ({jointly_decided}); oracle likely misconfigured"
    );
}
