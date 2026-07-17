//! End-to-end integration gate for the **regex derivative-emptiness → kernel-checked
//! Lean `False`** wiring (P3.7, task #52).
//!
//! A real `QF_S` regex-membership `unsat` behind the re-checked derivative-emptiness
//! certificate now carries a kernel-checked Lean module end-to-end: the text front
//! door / one-shot membership route decides the `unsat`, and
//! [`membership_unsat_lean_module`] reconstructs that same certificate to a Lean
//! `False` the in-tree kernel has already `infer`-checked and `def_eq False`-compared
//! (the successful `Some(_)` *is* the kernel gate — a wrong reconstruction declines to
//! `None`, never a wrong `False`). Mirrors `diophantine_lean_reconstruct.rs`.
#![cfg(feature = "full")]

use std::path::PathBuf;
use std::process::Command;
use std::time::Duration;

use axeyum_smtlib::parse_script;
use axeyum_solver::{CheckResult, SolverConfig, membership_unsat_lean_module, membership_verdict};

fn cfg() -> SolverConfig {
    SolverConfig {
        timeout: Some(Duration::from_secs(10)),
        ..SolverConfig::default()
    }
}

/// `x ∈ (ab)+ ∧ x ∈ (ba)+`: two disjoint non-nullable languages, so the intersection
/// is empty (they never share a member and neither accepts ε). The one-shot
/// membership route decides `unsat` behind the derivative-emptiness certificate, and
/// that certificate reconstructs to a kernel-checked Lean `False`.
const DISJOINT_PLUS_UNSAT: &str = r#"(set-logic QF_S)
(declare-const x String)
(assert (str.in_re x (re.+ (str.to_re "ab"))))
(assert (str.in_re x (re.+ (str.to_re "ba"))))
(check-sat)"#;

#[test]
fn disjoint_plus_membership_unsat_reconstructs_to_kernel_checked_false() {
    let mut script = parse_script(DISJOINT_PLUS_UNSAT).expect("parse membership script");

    // (1) The route decides this `unsat` (behind the re-checked emptiness certificate).
    assert_eq!(
        membership_verdict(&mut script, &cfg()),
        Some(CheckResult::Unsat),
        "two disjoint non-nullable positive memberships are an empty-language unsat",
    );

    // (2) End-to-end: solve → unsat → kernel-checked Lean module. A successful
    // `Some(_)` means the reconstructor already `infer`-checked the `False` proof and
    // `def_eq False`-compared it inside the kernel.
    let module = membership_unsat_lean_module(&script, &cfg())
        .expect("regex-emptiness unsat carries a kernel-checked Lean module");
    assert!(
        module.contains("theorem"),
        "the reconstructed module renders a Lean theorem"
    );
    assert!(
        module.contains("axeyum_refutation"),
        "the module names the shared axeyum_refutation theorem"
    );
    // The whole module is self-contained (emits its own inductives + recursors).
    assert!(
        module.contains("inductive"),
        "the module is self-contained (emits its automaton inductives)"
    );
}

#[test]
fn satisfiable_membership_carries_no_lean_module() {
    // x ∈ (ab)* — satisfiable (ε, "ab", "abab", …), so there is NO emptiness
    // certificate; the reconstruction must decline to `None` (never a wrong `False`).
    let s = r#"(set-logic QF_S)
(declare-const x String)
(assert (str.in_re x (re.* (str.to_re "ab"))))
(check-sat)"#;
    let mut script = parse_script(s).expect("parse satisfiable membership");
    // The route does not decide this `unsat` (it is satisfiable).
    assert_ne!(
        membership_verdict(&mut script, &cfg()),
        Some(CheckResult::Unsat),
        "a satisfiable membership must not be reported unsat",
    );
    assert!(
        membership_unsat_lean_module(&script, &cfg()).is_none(),
        "a satisfiable membership has no derivative-emptiness certificate to reconstruct",
    );
}

#[test]
fn non_membership_script_carries_no_lean_module() {
    // A pure word problem (no `str.in_re`) has no membership side channel.
    let s = r#"(set-logic QF_S)
(declare-const x String)
(assert (= x "a"))
(assert (= x "b"))
(check-sat)"#;
    let script = parse_script(s).expect("parse word script");
    assert!(
        membership_unsat_lean_module(&script, &cfg()).is_none(),
        "a non-membership script has no regex-emptiness module",
    );
}

/// **Real-Lean crosscheck**: the rendered regex-emptiness module must be accepted by a
/// genuine `lean` binary (skips gracefully if none is installed), and `#print axioms
/// axeyum_refutation` must not depend on `sorryAx`. This is the end-to-end
/// kernel-checked-in-real-Lean payoff of the #52 wiring.
#[test]
fn regex_emptiness_module_checks_in_real_lean() {
    let mut script = parse_script(DISJOINT_PLUS_UNSAT).expect("parse membership script");
    assert_eq!(
        membership_verdict(&mut script, &cfg()),
        Some(CheckResult::Unsat)
    );
    let module = membership_unsat_lean_module(&script, &cfg())
        .expect("regex-emptiness unsat carries a kernel-checked Lean module");

    let Some(bin) = lean_bin() else {
        eprintln!("[skip] regex-emptiness: lean binary not found; set AXEYUM_LEAN_BIN to enable");
        return;
    };
    let dir = std::env::temp_dir().join("axeyum_lean_regex_emptiness");
    std::fs::create_dir_all(&dir).expect("create temp dir");
    let file = dir.join("regex_emptiness.lean");
    std::fs::write(&file, &module).expect("write lean module");
    let out = Command::new(&bin).arg(&file).output().expect("run lean");
    let stdout = String::from_utf8_lossy(&out.stdout);
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(
        out.status.success(),
        "lean REJECTED the regex-emptiness module\n=== stdout ===\n{stdout}\n=== stderr ===\n{stderr}\n=== source ===\n{module}"
    );
    assert!(
        !stdout.contains("sorryAx"),
        "regex-emptiness proof depends on sorryAx:\n{stdout}"
    );
    assert!(
        stdout.contains("axeyum_refutation"),
        "missing #print axioms output:\n{stdout}"
    );
    eprintln!(
        "[lean ok] regex-emptiness: {}",
        stdout.trim().replace('\n', " | ")
    );
}

/// Locate a `lean` binary (env override or `PATH`/elan); `None` ⇒ skip.
fn lean_bin() -> Option<PathBuf> {
    if let Ok(p) = std::env::var("AXEYUM_LEAN_BIN") {
        let pb = PathBuf::from(p);
        if pb.exists() {
            return Some(pb);
        }
    }
    let elan = dirs_home().join(".elan/bin/lean");
    if elan.exists() {
        return Some(elan);
    }
    which_lean()
}

fn dirs_home() -> PathBuf {
    std::env::var("HOME").map(PathBuf::from).unwrap_or_default()
}

fn which_lean() -> Option<PathBuf> {
    let out = Command::new("which").arg("lean").output().ok()?;
    if !out.status.success() {
        return None;
    }
    let path = String::from_utf8_lossy(&out.stdout).trim().to_owned();
    if path.is_empty() {
        None
    } else {
        Some(PathBuf::from(path))
    }
}
