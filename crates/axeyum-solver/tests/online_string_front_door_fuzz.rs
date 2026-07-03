//! Text-level differential soundness fuzzer for the **front-door** online CDCL(T)
//! string route (P1.5b) against the Z3 oracle.
//!
//! Where `qf_s_online_differential_fuzz.rs` feeds typed IR directly to
//! [`check_qf_s_online_cdclt`], this harness generates `QF_S` SMT-LIB **text** and
//! routes axeyum through the real front door
//! ([`solve_smtlib`](axeyum_solver::solve_smtlib)) — exercising the whole new
//! pipeline: the parser's Boolean word-skeleton build (`Script::word_skeleton`),
//! the bounded encoder + gate, the flat word route, and finally the online CDCL(T)
//! second chance. The *same* text goes to `/usr/bin/z3`, so a disagreement is a
//! genuine soundness bug anywhere along that pipeline.
//!
//! Joint gate (over the scripts both jointly decide):
//! - axeyum `Sat` ∧ Z3 `unsat` → PANIC (wrong sat).
//! - axeyum `Unsat` ∧ Z3 `sat` → PANIC (wrong unsat — the worst bug).
//! - either side `unknown`/timeout/error → SKIP (sound).
//!
//! Fixed-seed LCG (no clock, no OS entropy): the whole sweep is reproducible.

#![cfg(feature = "z3")]

use std::fmt::Write as _;
use std::io::Write as _;
use std::process::{Command, Stdio};
use std::time::Duration;

use axeyum_solver::{CheckResult, SolverConfig, solve_smtlib};

/// Random Boolean-structured word-problem scripts adjudicated.
const INSTANCES: u64 = 1500;
const AXEYUM_TIMEOUT: Duration = Duration::from_secs(2);
const Z3_TIMEOUT: Duration = Duration::from_secs(3);
const Z3_BIN: &str = "/usr/bin/z3";

/// Small alphabet so constant clashes (and unsats) are common.
const ALPHABET: &[u8] = b"ab";

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

enum Expr {
    Var(usize),
    Lit(String),
    Cat(Box<Expr>, Box<Expr>),
}

/// A Boolean-structured word formula: (possibly negated) equality atom, disjunction,
/// or conjunction — arbitrary Boolean structure over `Seq` equality atoms.
enum Form {
    Atom(Expr, Expr, bool),
    Or(Box<Form>, Box<Form>),
    And(Box<Form>, Box<Form>),
}

fn gen_literal(rng: &mut Lcg) -> String {
    let len = 1 + rng.below(3);
    let mut s = String::with_capacity(len);
    for _ in 0..len {
        s.push(char::from(ALPHABET[rng.below(ALPHABET.len() as u64)]));
    }
    s
}

fn gen_expr(rng: &mut Lcg, num_vars: usize, depth: u32) -> Expr {
    if depth == 0 || rng.below(2) == 0 {
        return if rng.below(2) == 0 {
            Expr::Var(rng.below(num_vars as u64))
        } else {
            Expr::Lit(gen_literal(rng))
        };
    }
    let l = gen_expr(rng, num_vars, depth - 1);
    let r = gen_expr(rng, num_vars, depth - 1);
    Expr::Cat(Box::new(l), Box::new(r))
}

fn gen_leaf(rng: &mut Lcg, num_vars: usize) -> Form {
    let a = gen_expr(rng, num_vars, 2);
    let b = gen_expr(rng, num_vars, 2);
    let positive = rng.below(3) != 0;
    Form::Atom(a, b, positive)
}

fn gen_form(rng: &mut Lcg, num_vars: usize) -> Form {
    let n = 1 + rng.below(3);
    let mut f = gen_leaf(rng, num_vars);
    for _ in 1..n {
        let leaf = gen_leaf(rng, num_vars);
        f = if rng.below(2) == 0 {
            Form::Or(Box::new(f), Box::new(leaf))
        } else {
            Form::And(Box::new(f), Box::new(leaf))
        };
    }
    f
}

struct Instance {
    num_vars: usize,
    asserts: Vec<Form>,
}

impl Instance {
    fn generate(rng: &mut Lcg) -> Instance {
        let num_vars = 2 + rng.below(3);
        let n = 2 + rng.below(3);
        let asserts = (0..n).map(|_| gen_form(rng, num_vars)).collect();
        Instance { num_vars, asserts }
    }

    fn expr_text(e: &Expr, out: &mut String) {
        match e {
            Expr::Var(i) => {
                let _ = write!(out, "x{i}");
            }
            Expr::Lit(s) => {
                let _ = write!(out, "\"{s}\"");
            }
            Expr::Cat(a, b) => {
                out.push_str("(str.++ ");
                Self::expr_text(a, out);
                out.push(' ');
                Self::expr_text(b, out);
                out.push(')');
            }
        }
    }

    fn form_text(f: &Form, out: &mut String) {
        match f {
            Form::Atom(a, b, positive) => {
                out.push_str(if *positive { "(= " } else { "(not (= " });
                Self::expr_text(a, out);
                out.push(' ');
                Self::expr_text(b, out);
                out.push_str(if *positive { ")" } else { "))" });
            }
            Form::Or(a, b) => {
                out.push_str("(or ");
                Self::form_text(a, out);
                out.push(' ');
                Self::form_text(b, out);
                out.push(')');
            }
            Form::And(a, b) => {
                out.push_str("(and ");
                Self::form_text(a, out);
                out.push(' ');
                Self::form_text(b, out);
                out.push(')');
            }
        }
    }

    fn to_text(&self) -> String {
        let mut text = String::from("(set-logic QF_S)\n");
        for i in 0..self.num_vars {
            let _ = writeln!(text, "(declare-const x{i} String)");
        }
        for f in &self.asserts {
            text.push_str("(assert ");
            Self::form_text(f, &mut text);
            text.push_str(")\n");
        }
        text.push_str("(check-sat)\n");
        text
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Verdict {
    Sat,
    Unsat,
    Skip,
}

fn axeyum_decide(text: &str) -> Verdict {
    let config = SolverConfig::default().with_timeout(AXEYUM_TIMEOUT);
    match solve_smtlib(text, &config) {
        Ok(outcome) => match outcome.result {
            CheckResult::Sat(_) => Verdict::Sat,
            CheckResult::Unsat => Verdict::Unsat,
            CheckResult::Unknown(_) => Verdict::Skip,
        },
        // A parse/backend error is not a verdict — skip (never adjudicate on it).
        Err(_) => Verdict::Skip,
    }
}

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
fn online_string_front_door_fuzz_disagree_zero() {
    if z3_decide("(set-logic QF_S)\n(check-sat)\n") == Verdict::Skip
        && Command::new(Z3_BIN).arg("--version").output().is_err()
    {
        eprintln!("[front-door-fuzz] {Z3_BIN} unavailable; skipping (no adjudicator)");
        return;
    }

    let mut jointly_decided = 0u64;
    let mut agreements = 0u64;
    let mut ax_sat = 0u64;
    let mut ax_unsat = 0u64;
    let mut ax_skip = 0u64;
    let mut z3_skip = 0u64;

    for seed in 0..INSTANCES {
        if seed % 200 == 0 {
            eprintln!(
                "[front-door-fuzz] seed {seed}/{INSTANCES} (joint={jointly_decided}, \
                 agree={agreements}, ax_sat={ax_sat}, ax_unsat={ax_unsat}, ax_skip={ax_skip})"
            );
        }
        let mut rng = Lcg::new(seed ^ 0x5eed_f00d);
        let inst = Instance::generate(&mut rng);
        let text = inst.to_text();

        let ax = axeyum_decide(&text);
        match ax {
            Verdict::Sat => ax_sat += 1,
            Verdict::Unsat => ax_unsat += 1,
            Verdict::Skip => {
                ax_skip += 1;
                continue;
            }
        }

        let z3 = z3_decide(&text);
        if z3 == Verdict::Skip {
            z3_skip += 1;
            continue;
        }

        jointly_decided += 1;
        if ax == z3 {
            agreements += 1;
        } else {
            panic!(
                "DISAGREEMENT (seed {seed}): axeyum = {ax:?}, Z3 = {z3:?}.\n\
                 This is a {} soundness bug at the online CDCL(T) string front door.\n\
                 script:\n{text}",
                match (ax, z3) {
                    (Verdict::Sat, Verdict::Unsat) => "WRONG-SAT",
                    (Verdict::Unsat, Verdict::Sat) => "WRONG-UNSAT (worst case)",
                    _ => "verdict",
                },
            );
        }
    }

    println!("=== QF_S online CDCL(T) front-door differential fuzz tally ===");
    println!("instances:        {INSTANCES}");
    println!("jointly decided:  {jointly_decided}");
    println!("agreements:       {agreements}");
    println!("axeyum Sat:       {ax_sat}");
    println!("axeyum Unsat:     {ax_unsat}");
    println!("axeyum skipped:   {ax_skip} (Unknown/Err)");
    println!("Z3 skipped:       {z3_skip} (unknown/timeout)");
    println!("DISAGREEMENTS:    0");

    assert!(
        jointly_decided > 50,
        "too few jointly-decided scripts ({jointly_decided}); the differential gate \
         is not exercising the front door"
    );
    assert_eq!(
        agreements, jointly_decided,
        "a disagreement escaped the gate"
    );
}
