//! Adversarial differential soundness fuzzer for the `QF_NIA` `((_ iand k) a b)`
//! bounded bit-blast (P2.5 slice 5) against the Z3 oracle.
//!
//! `iand` is parsed as the exact desugaring
//! `((_ iand k) a b) = bv2nat(bvand(int2bv k a, int2bv k b))`. axeyum decides an
//! `iand`-bearing bounded integer conjunction through the finite-box exact
//! bit-blast (`prove_int_box` + the `bv2nat` structural interval + linear bound
//! propagation). This harness generates thousands of small random bounded
//! `iand`-bearing conjunctions and adjudicates each against Z3 solving the SAME
//! query with `iand` written in its **desugared** `int2bv`/`bvand`/`bv2nat` form
//! (an independent oracle: Z3's native bit-vector + integer theory decides the
//! definition directly, no shared code with axeyum's blast).
//!
//! - axeyum `Sat` ∧ Z3 `unsat` → **PANIC** (wrong sat).
//! - axeyum `Unsat` ∧ Z3 `sat` → **PANIC** (wrong unsat — the worst bug).
//! - axeyum `Unknown` is ALLOWED (incomplete is sound) — counted, never failed.
//! - Z3 `unknown`/timeout/unavailable → the instance is skipped.
//!
//! The test passes iff disagreements == 0. axeyum `Sat` is additionally
//! replay-checked inside `solve_smtlib`'s entry point, so a fabricated model can
//! never be reported as `Sat` regardless of the oracle.
#![cfg(feature = "full")]
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
    /// A uniform value in `[0, n)` (`n > 0`).
    fn below(&mut self, n: u64) -> u64 {
        self.next_u64() % n
    }
    /// A uniform `usize` index in `[0, n)`.
    fn index(&mut self, n: usize) -> usize {
        usize::try_from(self.below(n as u64)).expect("index fits usize")
    }
    /// A uniform value in the inclusive integer range `[lo, hi]` (`lo ≤ hi`).
    fn range(&mut self, lo: i64, hi: i64) -> i64 {
        let span = u64::try_from(hi - lo + 1).expect("nonnegative span");
        lo + i64::try_from(self.below(span)).expect("offset fits i64")
    }
}

/// A generated instance: the two rendered scripts (native `iand` for axeyum, the
/// desugared bit-vector form for Z3) over the SAME variables, bounds, and atoms.
struct Instance {
    axeyum_text: String,
    z3_text: String,
}

impl Instance {
    fn generate(rng: &mut Lcg) -> Instance {
        let names = ["x", "y", "z"];
        let nvars = rng.index(3) + 1; // 1..=3 vars
        let mut decls = String::new();
        // Per-variable bounds. Every variable is finitely bounded so the box path
        // is (usually) reachable; the small ranges keep Z3 instant.
        let mut bounds = String::new();
        for name in names.iter().take(nvars) {
            let lo = rng.range(-4, 2);
            let width = [4i64, 8, 12, 16, 24, 32][rng.index(6)];
            let hi = lo + width;
            let _ = writeln!(decls, "(declare-fun {name} () Int)");
            let _ = writeln!(bounds, "(assert (<= {lo} {name}))");
            let _ = writeln!(bounds, "(assert (< {name} {hi}))");
        }

        // A handful of atoms mixing iand, linear, and (small) product terms. Each
        // atom is rendered twice: native for axeyum, desugared for Z3.
        let natoms = rng.index(4) + 2; // 2..=5 atoms
        let mut ax_atoms = String::new();
        let mut z3_atoms = String::new();
        for _ in 0..natoms {
            let an = names[rng.index(nvars)];
            let bn = names[rng.index(nvars)];
            let cmp = ["<", "<=", ">", ">=", "="][rng.index(5)];
            match rng.below(3) {
                0 => {
                    // iand atom: (cmp ((_ iand k) a b) const)
                    let k = rng.range(2, 6);
                    let rhs = rng.range(-2, (1i64 << k) + 2);
                    let _ = writeln!(ax_atoms, "(assert ({cmp} ((_ iand {k}) {an} {bn}) {rhs}))");
                    let _ = writeln!(
                        z3_atoms,
                        "(assert ({cmp} (bv2nat (bvand ((_ int2bv {k}) {an}) ((_ int2bv {k}) {bn}))) {rhs}))"
                    );
                }
                1 => {
                    // linear atom: (cmp (+ a b) const)
                    let rhs = rng.range(-8, 40);
                    let atom = format!("(assert ({cmp} (+ {an} {bn}) {rhs}))\n");
                    ax_atoms.push_str(&atom);
                    z3_atoms.push_str(&atom);
                }
                _ => {
                    // product atom: (cmp (* a b) const)
                    let rhs = rng.range(-4, 60);
                    let atom = format!("(assert ({cmp} (* {an} {bn}) {rhs}))\n");
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
fn qf_nia_iand_differential_fuzz_z3_disagree_zero() {
    if z3_decide("(set-logic ALL)\n(check-sat)\n") == Verdict::Skip
        && Command::new(Z3_BIN).arg("--version").output().is_err()
    {
        eprintln!("[iand-fuzz-z3] {Z3_BIN} unavailable; skipping (no adjudicator)");
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
            eprintln!("[iand-fuzz] seed {seed}: axeyum={ax:?} z3={z3:?} — {kind}\n{text}");
        }
        panic!(
            "iand differential fuzz found {} disagreement(s) vs Z3 — soundness bug",
            disagreements.len()
        );
    }

    eprintln!(
        "[iand-fuzz] {jointly_decided} jointly decided, {agreements} agree \
         (ax_sat={ax_sat}, ax_unsat={ax_unsat})"
    );
    // The sweep must exercise BOTH verdict directions or it proves nothing.
    assert!(
        ax_sat > 0 && ax_unsat > 0,
        "fuzz must exercise both sat and unsat iand decisions (sat={ax_sat}, unsat={ax_unsat})"
    );
    assert!(
        jointly_decided > 100,
        "too few jointly-decided instances ({jointly_decided}); oracle likely misconfigured"
    );
}
