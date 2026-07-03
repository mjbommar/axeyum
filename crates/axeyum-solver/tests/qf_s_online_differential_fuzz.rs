//! Adversarial differential soundness fuzzer for the **online CDCL(T) string
//! theory** (P1.5 slice b, [`check_qf_s_online_cdclt`]) against the Z3 oracle.
//!
//! The route decides Boolean-structured word problems (`or` / negation over `Seq`
//! equality atoms): it produces `unsat` only through certified theory conflicts
//! (or a propositional refutation of the skeleton) and `sat` only via a
//! [`solve_word_equations`](axeyum_strings::solve_word_equations) model that
//! replays against the original assertions. Both directions are soundness-gated
//! here:
//!
//! - a wrong `sat` — a model of an in-fact-unsatisfiable system — faces Z3
//!   `unsat`;
//! - a wrong `unsat` (the worst case) — an uncertified refutation — faces Z3
//!   `sat`.
//!
//! Unlike `word_equation_differential_fuzz.rs` (which shells generated *text* to
//! Z3 and re-parses the same text for axeyum), this harness generates a small
//! Boolean-over-word-equation **AST** and renders it two ways from one source: to
//! typed IR `Seq(BitVec 8)` terms fed directly to [`check_qf_s_online_cdclt`], and
//! to `QF_S` SMT-LIB text piped to `/usr/bin/z3`. ASCII-only literals over a tiny
//! alphabet make the two renderings denotationally identical and make constant
//! clashes (hence theory-driven unsats) frequent, stressing the wrong-unsat gate.
//!
//! A fixed-seed LCG drives every choice (no clock, no OS entropy), so the whole
//! sweep is reproducible from the seed. The joint gate:
//!
//! - axeyum `Sat` ∧ Z3 `unsat` → **PANIC** (wrong sat).
//! - axeyum `Unsat` ∧ Z3 `sat` → **PANIC** (wrong unsat — the worst bug).
//! - axeyum `Unknown` → SKIP (incomplete is sound).
//! - Z3 `unknown` / timeout / error → SKIP (Z3 cannot adjudicate).
//!
//! The test passes iff disagreements == 0 over the jointly-decided scripts.

#![cfg(feature = "z3")]

use std::fmt::Write as _;
use std::io::Write as _;
use std::process::{Command, Stdio};
use std::time::Duration;

use axeyum_ir::{ArraySortKey, Sort, TermArena, TermId};
use axeyum_solver::{CheckResult, SolverConfig, check_qf_s_online_cdclt};

/// Random Boolean-structured word problems adjudicated (≥ 1500 as required).
const INSTANCES: u64 = 1500;

/// Per-axeyum-query wall-clock budget: bounds both the CDCL deadline and the word
/// search / refuter budget, so a pathological instance degrades to `Unknown`
/// (Skip) rather than hang.
const AXEYUM_TIMEOUT: Duration = Duration::from_secs(2);

/// Per-call Z3 wall-clock budget.
const Z3_TIMEOUT: Duration = Duration::from_secs(3);

const Z3_BIN: &str = "/usr/bin/z3";

const ELEM: ArraySortKey = ArraySortKey::BitVec(8);

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

/// The tiny literal alphabet — small so constant clashes (and unsats) are common.
const ALPHABET: &[u8] = b"ab";

/// A string-sorted expression over the declared variables.
enum Expr {
    Var(usize),
    Lit(String),
    Cat(Box<Expr>, Box<Expr>),
}

/// A Boolean-structured word formula: a (possibly negated) equality atom, or a
/// disjunction of two formulas.
enum Form {
    /// `(= a b)` if `positive`, else `(not (= a b))`.
    Atom(Expr, Expr, bool),
    Or(Box<Form>, Box<Form>),
}

fn gen_literal(rng: &mut Lcg) -> String {
    let len = 1 + rng.below(3); // 1..=3
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
    // Bias positive (equalities drive the theory); some negations exercise diseqs.
    let positive = rng.below(3) != 0;
    Form::Atom(a, b, positive)
}

fn gen_form(rng: &mut Lcg, num_vars: usize) -> Form {
    // 1..=3 disjuncts.
    let disjuncts = 1 + rng.below(3);
    let mut f = gen_leaf(rng, num_vars);
    for _ in 1..disjuncts {
        f = Form::Or(Box::new(f), Box::new(gen_leaf(rng, num_vars)));
    }
    f
}

struct Instance {
    num_vars: usize,
    asserts: Vec<Form>,
}

impl Instance {
    fn generate(rng: &mut Lcg) -> Instance {
        let num_vars = 2 + rng.below(3); // 2..=4
        let n = 2 + rng.below(3); // 2..=4 assertions
        let asserts = (0..n).map(|_| gen_form(rng, num_vars)).collect();
        Instance { num_vars, asserts }
    }

    // ----- SMT-LIB text rendering (for Z3) -----

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
                if *positive {
                    out.push_str("(= ");
                } else {
                    out.push_str("(not (= ");
                }
                Self::expr_text(a, out);
                out.push(' ');
                Self::expr_text(b, out);
                if *positive {
                    out.push(')');
                } else {
                    out.push_str("))");
                }
            }
            Form::Or(a, b) => {
                out.push_str("(or ");
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

    // ----- typed IR rendering (for axeyum) -----

    fn lit_ir(arena: &mut TermArena, s: &str) -> TermId {
        let mut acc: Option<TermId> = None;
        for &byte in s.as_bytes().iter().rev() {
            let c = arena.bv_const(8, u128::from(byte)).expect("char const");
            let u = arena.seq_unit(c).expect("seq.unit");
            acc = Some(match acc {
                None => u,
                Some(rest) => arena.seq_concat(u, rest).expect("str.++"),
            });
        }
        acc.unwrap_or_else(|| arena.seq_empty(ELEM))
    }

    fn expr_ir(arena: &mut TermArena, vars: &[TermId], e: &Expr) -> TermId {
        match e {
            Expr::Var(i) => vars[*i],
            Expr::Lit(s) => Self::lit_ir(arena, s),
            Expr::Cat(a, b) => {
                let ta = Self::expr_ir(arena, vars, a);
                let tb = Self::expr_ir(arena, vars, b);
                arena.seq_concat(ta, tb).expect("str.++")
            }
        }
    }

    fn form_ir(arena: &mut TermArena, vars: &[TermId], f: &Form) -> TermId {
        match f {
            Form::Atom(a, b, positive) => {
                let ta = Self::expr_ir(arena, vars, a);
                let tb = Self::expr_ir(arena, vars, b);
                let e = arena.eq(ta, tb).expect("=");
                if *positive {
                    e
                } else {
                    arena.not(e).expect("not")
                }
            }
            Form::Or(a, b) => {
                let ta = Self::form_ir(arena, vars, a);
                let tb = Self::form_ir(arena, vars, b);
                arena.or(ta, tb).expect("or")
            }
        }
    }

    fn to_ir(&self) -> (TermArena, Vec<TermId>) {
        let mut arena = TermArena::new();
        let vars: Vec<TermId> = (0..self.num_vars)
            .map(|i| {
                let s = arena
                    .declare(&format!("x{i}"), Sort::Seq(ELEM))
                    .expect("declare seq var");
                arena.var(s)
            })
            .collect();
        let assertions: Vec<TermId> = self
            .asserts
            .iter()
            .map(|f| Self::form_ir(&mut arena, &vars, f))
            .collect();
        (arena, assertions)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Verdict {
    Sat,
    Unsat,
    Skip,
}

fn axeyum_decide(inst: &Instance) -> Verdict {
    let (mut arena, assertions) = inst.to_ir();
    let config = SolverConfig::default().with_timeout(AXEYUM_TIMEOUT);
    match check_qf_s_online_cdclt(&mut arena, &assertions, &config) {
        CheckResult::Sat(_) => Verdict::Sat,
        CheckResult::Unsat => Verdict::Unsat,
        CheckResult::Unknown(_) => Verdict::Skip,
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
fn qf_s_online_differential_fuzz_disagree_zero() {
    if z3_decide("(set-logic QF_S)\n(check-sat)\n") == Verdict::Skip
        && Command::new(Z3_BIN).arg("--version").output().is_err()
    {
        eprintln!("[qf_s-fuzz] {Z3_BIN} unavailable; skipping (no adjudicator)");
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
                "[qf_s-fuzz] seed {seed}/{INSTANCES} (joint={jointly_decided}, \
                 agree={agreements}, ax_sat={ax_sat}, ax_unsat={ax_unsat}, ax_skip={ax_skip})"
            );
        }
        let mut rng = Lcg::new(seed);
        let inst = Instance::generate(&mut rng);

        let ax = axeyum_decide(&inst);
        match ax {
            Verdict::Sat => ax_sat += 1,
            Verdict::Unsat => ax_unsat += 1,
            Verdict::Skip => {
                ax_skip += 1;
                continue;
            }
        }

        let z3 = z3_decide(&inst.to_text());
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
                 This is a {} soundness bug in the online CDCL(T) string theory.\n\
                 script:\n{}",
                match (ax, z3) {
                    (Verdict::Sat, Verdict::Unsat) => "WRONG-SAT",
                    (Verdict::Unsat, Verdict::Sat) => "WRONG-UNSAT (worst case)",
                    _ => "verdict",
                },
                inst.to_text()
            );
        }
    }

    println!("=== QF_S online CDCL(T) differential fuzz tally ===");
    println!("instances:        {INSTANCES}");
    println!("jointly decided:  {jointly_decided}");
    println!("agreements:       {agreements}");
    println!("axeyum Sat:       {ax_sat}");
    println!("axeyum Unsat:     {ax_unsat} (certified theory conflicts / propositional)");
    println!("axeyum skipped:   {ax_skip} (Unknown)");
    println!("Z3 skipped:       {z3_skip} (unknown/timeout)");
    println!("DISAGREEMENTS:    0");

    assert!(
        jointly_decided > 50,
        "too few jointly-decided scripts ({jointly_decided}); the differential \
         gate is not meaningfully exercised"
    );
    assert!(
        ax_sat > 0 && ax_unsat > 0,
        "both verdict directions must be exercised (sat={ax_sat}, unsat={ax_unsat})"
    );
}
