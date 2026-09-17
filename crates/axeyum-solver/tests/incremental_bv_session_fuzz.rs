//! Differential fuzz for the **incremental** `QF_BV` path (ADR-2145): random
//! `push` / `assert` / `check` / `check-sat-assuming` / `pop` sessions over one
//! retained [`IncrementalBvSolver`], every verdict compared against a fresh
//! one-shot solve of the live assertion set, every `sat` model replayed
//! against that set through the IR ground evaluator, and -- under
//! `--features z3` -- every verdict compared against a z3 `Solver` driven
//! through the SAME push/assert/check/pop stream.
//!
//! Why this exists: the warm engine has been the production route for
//! symbolic-execution drivers since ADR-0009, its SAT core was swapped under it
//! by ADR-1703, and its solve boundary is being changed again by ADR-2145 --
//! and until this file no gate compared its verdicts on a *sequence* against
//! anything. The one-shot fuzzes (`bv_differential_fuzz`) decide one formula
//! per instance; the retained solver's failure modes are all sequential: a
//! popped scope's implication surviving into the next check, a clause added
//! against a live assignment registered at the wrong level, a pending
//! propagation dropped at a backtrack. A session fuzz is the only shape that
//! can reach them.
//!
//! Both arms of `SolverConfig::warm_keep_trail` run in every test (the field
//! is set explicitly, not through the process-wide env lever), so the gate
//! covers the shipped schedule and the ADR-2145 schedule from one binary.
//!
//! Every generator draw goes through a `SplitMix64` finaliser (ADR-2141): no
//! raw LCG state is ever returned, so the low bits that select polarities and
//! scope operations are not a fixed function of the seed's parity.
//!
//! Knobs: `AXEYUM_INCR_SESSIONS` (default 150 per arm), `AXEYUM_INCR_SEED`
//! (default 0). A disagreement prints the whole session as SMT-LIB.
#![cfg(feature = "full")]

use std::fmt::Write as _;

use axeyum_ir::{Sort, SymbolId, TermArena, TermId, Value, eval};
use axeyum_solver::{
    CheckResult, DEFAULT_WARM_KEEP_TRAIL, IncrementalBvSolver, SolverConfig, solve,
};

const VAR_NAMES: [&str; 3] = ["x", "y", "z"];
const WIDTHS: [u32; 3] = [4, 8, 16];
const MAX_DEPTH: usize = 5;

/// `SplitMix64` -- a finalised generator, never the raw state (ADR-2141).
struct Mix(u64);

impl Mix {
    fn new(seed: u64) -> Self {
        Mix(seed.wrapping_mul(0x9e37_79b9_7f4a_7c15) ^ 0x2145_2145_2145_2145)
    }

    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^ (z >> 31)
    }

    fn below(&mut self, n: u64) -> usize {
        usize::try_from(self.next_u64() % n).expect("fits")
    }
}

/// A width-uniform bit-vector term as plain data: buildable into the IR, into
/// z3, and into SMT-LIB text from one description.
#[derive(Clone, Debug)]
enum Term {
    Var(usize),
    Const(u64),
    Bin(BinOp, Box<Term>, Box<Term>),
    Not(Box<Term>),
    Neg(Box<Term>),
}

#[derive(Clone, Copy, Debug)]
enum BinOp {
    Add,
    Sub,
    Mul,
    And,
    Or,
    Xor,
    Shl,
    Lshr,
    Udiv,
    Urem,
}

impl BinOp {
    fn pick(rng: &mut Mix) -> Self {
        match rng.below(10) {
            0 => BinOp::Add,
            1 => BinOp::Sub,
            2 => BinOp::Mul,
            3 => BinOp::And,
            4 => BinOp::Or,
            5 => BinOp::Xor,
            6 => BinOp::Shl,
            7 => BinOp::Lshr,
            8 => BinOp::Udiv,
            _ => BinOp::Urem,
        }
    }

    fn symbol(self) -> &'static str {
        match self {
            BinOp::Add => "bvadd",
            BinOp::Sub => "bvsub",
            BinOp::Mul => "bvmul",
            BinOp::And => "bvand",
            BinOp::Or => "bvor",
            BinOp::Xor => "bvxor",
            BinOp::Shl => "bvshl",
            BinOp::Lshr => "bvlshr",
            BinOp::Udiv => "bvudiv",
            BinOp::Urem => "bvurem",
        }
    }
}

impl Term {
    fn generate(rng: &mut Mix, width: u32, depth: usize) -> Term {
        let mask = if width == 64 {
            u64::MAX
        } else {
            (1u64 << width) - 1
        };
        if depth == 0 || rng.below(3) == 0 {
            return match rng.below(4) {
                0 => Term::Const(rng.next_u64() & mask),
                // The degenerate divisor / shift amount is drawn on purpose
                // (CLAUDE.md hard rule): a constant zero reaches `bvudiv` and
                // `bvurem` as a right operand through this arm.
                1 if rng.below(4) == 0 => Term::Const(0),
                _ => Term::Var(rng.below(VAR_NAMES.len() as u64)),
            };
        }
        match rng.below(6) {
            0 => Term::Not(Box::new(Term::generate(rng, width, depth - 1))),
            1 => Term::Neg(Box::new(Term::generate(rng, width, depth - 1))),
            _ => Term::Bin(
                BinOp::pick(rng),
                Box::new(Term::generate(rng, width, depth - 1)),
                Box::new(Term::generate(rng, width, depth - 1)),
            ),
        }
    }

    fn build(&self, a: &mut TermArena, width: u32, vars: &[TermId]) -> TermId {
        match self {
            Term::Var(i) => vars[*i],
            Term::Const(c) => a.bv_const(width, u128::from(*c)).unwrap(),
            Term::Not(t) => {
                let t = t.build(a, width, vars);
                a.bv_not(t).unwrap()
            }
            Term::Neg(t) => {
                let t = t.build(a, width, vars);
                a.bv_neg(t).unwrap()
            }
            Term::Bin(op, l, r) => {
                let l = l.build(a, width, vars);
                let r = r.build(a, width, vars);
                match op {
                    BinOp::Add => a.bv_add(l, r),
                    BinOp::Sub => a.bv_sub(l, r),
                    BinOp::Mul => a.bv_mul(l, r),
                    BinOp::And => a.bv_and(l, r),
                    BinOp::Or => a.bv_or(l, r),
                    BinOp::Xor => a.bv_xor(l, r),
                    BinOp::Shl => a.bv_shl(l, r),
                    BinOp::Lshr => a.bv_lshr(l, r),
                    BinOp::Udiv => a.bv_udiv(l, r),
                    BinOp::Urem => a.bv_urem(l, r),
                }
                .unwrap()
            }
        }
    }

    fn smt2(&self, width: u32) -> String {
        match self {
            Term::Var(i) => VAR_NAMES[*i].to_string(),
            Term::Const(c) => format!("(_ bv{c} {width})"),
            Term::Not(t) => format!("(bvnot {})", t.smt2(width)),
            Term::Neg(t) => format!("(bvneg {})", t.smt2(width)),
            Term::Bin(op, l, r) => {
                format!("({} {} {})", op.symbol(), l.smt2(width), r.smt2(width))
            }
        }
    }

    #[cfg(feature = "z3")]
    fn z3(&self, width: u32, vars: &[z3::ast::BV]) -> z3::ast::BV {
        match self {
            Term::Var(i) => vars[*i].clone(),
            Term::Const(c) => z3::ast::BV::from_u64(*c, width),
            Term::Not(t) => t.z3(width, vars).bvnot(),
            Term::Neg(t) => t.z3(width, vars).bvneg(),
            Term::Bin(op, l, r) => {
                let l = l.z3(width, vars);
                let r = r.z3(width, vars);
                match op {
                    BinOp::Add => l.bvadd(&r),
                    BinOp::Sub => l.bvsub(&r),
                    BinOp::Mul => l.bvmul(&r),
                    BinOp::And => l.bvand(&r),
                    BinOp::Or => l.bvor(&r),
                    BinOp::Xor => l.bvxor(&r),
                    BinOp::Shl => l.bvshl(&r),
                    BinOp::Lshr => l.bvlshr(&r),
                    BinOp::Udiv => l.bvudiv(&r),
                    BinOp::Urem => l.bvurem(&r),
                }
            }
        }
    }
}

#[derive(Clone, Copy, Debug)]
enum Cmp {
    Eq,
    Ne,
    Ult,
    Ule,
    Slt,
    Sle,
}

impl Cmp {
    fn pick(rng: &mut Mix) -> Self {
        match rng.below(6) {
            0 => Cmp::Eq,
            1 => Cmp::Ne,
            2 => Cmp::Ult,
            3 => Cmp::Ule,
            4 => Cmp::Slt,
            _ => Cmp::Sle,
        }
    }
}

/// A Boolean assertion: a comparison, or a small Boolean combination of two.
#[derive(Clone, Debug)]
enum Atom {
    Cmp(Cmp, Term, Term),
    And(Box<Atom>, Box<Atom>),
    Or(Box<Atom>, Box<Atom>),
    Not(Box<Atom>),
}

impl Atom {
    fn generate(rng: &mut Mix, width: u32) -> Atom {
        let leaf = |rng: &mut Mix| {
            Atom::Cmp(
                Cmp::pick(rng),
                Term::generate(rng, width, 2),
                Term::generate(rng, width, 2),
            )
        };
        match rng.below(8) {
            0 => Atom::And(Box::new(leaf(rng)), Box::new(leaf(rng))),
            1 => Atom::Or(Box::new(leaf(rng)), Box::new(leaf(rng))),
            2 => Atom::Not(Box::new(leaf(rng))),
            _ => leaf(rng),
        }
    }

    fn build(&self, a: &mut TermArena, width: u32, vars: &[TermId]) -> TermId {
        match self {
            Atom::Cmp(cmp, l, r) => {
                let l = l.build(a, width, vars);
                let r = r.build(a, width, vars);
                match cmp {
                    Cmp::Eq => a.eq(l, r).unwrap(),
                    Cmp::Ne => {
                        let e = a.eq(l, r).unwrap();
                        a.not(e).unwrap()
                    }
                    Cmp::Ult => a.bv_ult(l, r).unwrap(),
                    Cmp::Ule => a.bv_ule(l, r).unwrap(),
                    Cmp::Slt => a.bv_slt(l, r).unwrap(),
                    Cmp::Sle => a.bv_sle(l, r).unwrap(),
                }
            }
            Atom::And(l, r) => {
                let l = l.build(a, width, vars);
                let r = r.build(a, width, vars);
                a.and(l, r).unwrap()
            }
            Atom::Or(l, r) => {
                let l = l.build(a, width, vars);
                let r = r.build(a, width, vars);
                a.or(l, r).unwrap()
            }
            Atom::Not(t) => {
                let t = t.build(a, width, vars);
                a.not(t).unwrap()
            }
        }
    }

    fn smt2(&self, width: u32) -> String {
        match self {
            Atom::Cmp(cmp, l, r) => {
                let op = match cmp {
                    Cmp::Eq => "=",
                    Cmp::Ne => "distinct",
                    Cmp::Ult => "bvult",
                    Cmp::Ule => "bvule",
                    Cmp::Slt => "bvslt",
                    Cmp::Sle => "bvsle",
                };
                format!("({op} {} {})", l.smt2(width), r.smt2(width))
            }
            Atom::And(l, r) => format!("(and {} {})", l.smt2(width), r.smt2(width)),
            Atom::Or(l, r) => format!("(or {} {})", l.smt2(width), r.smt2(width)),
            Atom::Not(t) => format!("(not {})", t.smt2(width)),
        }
    }

    #[cfg(feature = "z3")]
    fn z3(&self, width: u32, vars: &[z3::ast::BV]) -> z3::ast::Bool {
        match self {
            Atom::Cmp(cmp, l, r) => {
                let l = l.z3(width, vars);
                let r = r.z3(width, vars);
                match cmp {
                    Cmp::Eq => l.eq(&r),
                    Cmp::Ne => l.ne(&r),
                    Cmp::Ult => l.bvult(&r),
                    Cmp::Ule => l.bvule(&r),
                    Cmp::Slt => l.bvslt(&r),
                    Cmp::Sle => l.bvsle(&r),
                }
            }
            Atom::And(l, r) => z3::ast::Bool::and(&[l.z3(width, vars), r.z3(width, vars)]),
            Atom::Or(l, r) => z3::ast::Bool::or(&[l.z3(width, vars), r.z3(width, vars)]),
            Atom::Not(t) => t.z3(width, vars).not(),
        }
    }
}

/// One step of a session.
#[derive(Clone, Debug)]
enum Op {
    Push,
    Pop,
    Assert(Atom),
    Check,
    CheckAssuming(Vec<Atom>),
}

/// A whole session: the width, and the ordered steps.
#[derive(Clone, Debug)]
struct Session {
    width: u32,
    ops: Vec<Op>,
}

impl Session {
    fn generate(rng: &mut Mix) -> Session {
        let width = WIDTHS[rng.below(WIDTHS.len() as u64)];
        let steps = 12 + rng.below(20);
        let mut depth = 0usize;
        let mut ops = Vec::with_capacity(steps);
        for _ in 0..steps {
            let op = match rng.below(10) {
                0 | 1 if depth < MAX_DEPTH => {
                    depth += 1;
                    Op::Push
                }
                2 if depth > 0 => {
                    depth -= 1;
                    Op::Pop
                }
                3..=5 => Op::Assert(Atom::generate(rng, width)),
                6 | 7 => Op::Check,
                _ => {
                    let n = 1 + rng.below(2);
                    Op::CheckAssuming((0..n).map(|_| Atom::generate(rng, width)).collect())
                }
            };
            ops.push(op);
        }
        // Every session ends with a check so the last assertions are decided.
        ops.push(Op::Check);
        Session { width, ops }
    }

    fn smt2(&self) -> String {
        let mut out = String::from("(set-logic QF_BV)\n");
        for name in VAR_NAMES {
            let _ = writeln!(out, "(declare-const {name} (_ BitVec {}))", self.width);
        }
        for op in &self.ops {
            match op {
                Op::Push => out.push_str("(push 1)\n"),
                Op::Pop => out.push_str("(pop 1)\n"),
                Op::Assert(atom) => {
                    let _ = writeln!(out, "(assert {})", atom.smt2(self.width));
                }
                Op::Check => out.push_str("(check-sat)\n"),
                Op::CheckAssuming(atoms) => {
                    let list: Vec<String> = atoms.iter().map(|a| a.smt2(self.width)).collect();
                    let _ = writeln!(out, "(check-sat-assuming ({}))", list.join(" "));
                }
            }
        }
        out
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Verdict {
    Sat,
    Unsat,
    Unknown,
}

fn label(result: &CheckResult) -> Verdict {
    match result {
        CheckResult::Sat(_) => Verdict::Sat,
        CheckResult::Unsat => Verdict::Unsat,
        CheckResult::Unknown(_) => Verdict::Unknown,
    }
}

/// The z3 side of a session: the same push/assert/check/pop stream on one
/// `z3::Solver`, so z3 is exercised as an INCREMENTAL oracle, not a one-shot
/// one. `None` when the feature is off.
#[cfg(feature = "z3")]
struct Z3Mirror {
    solver: z3::Solver,
    vars: Vec<z3::ast::BV>,
}

#[cfg(feature = "z3")]
impl Z3Mirror {
    fn new(width: u32) -> Self {
        let solver = z3::Solver::new();
        let mut params = z3::Params::new();
        params.set_u32("timeout", 5_000);
        solver.set_params(&params);
        let vars = VAR_NAMES
            .iter()
            .map(|name| z3::ast::BV::new_const(*name, width))
            .collect();
        Z3Mirror { solver, vars }
    }

    fn verdict(result: z3::SatResult) -> Verdict {
        match result {
            z3::SatResult::Sat => Verdict::Sat,
            z3::SatResult::Unsat => Verdict::Unsat,
            z3::SatResult::Unknown => Verdict::Unknown,
        }
    }
}

struct Tally {
    checks: u64,
    sat: u64,
    unsat: u64,
    unknown: u64,
    reused_checks: u64,
    z3_compared: u64,
    z3_unknown: u64,
}

/// Runs one session on the warm engine under `keep_trail`, adjudicating
/// every check three ways. Returns the first disagreement as text.
// One stream, read top to bottom as the differential it is: splitting the
// check arm from the scope arms would put the live-set bookkeeping they
// share across a function boundary.
#[allow(clippy::too_many_lines)]
fn run_session(session: &Session, keep_trail: bool, tally: &mut Tally) -> Option<String> {
    let width = session.width;
    let mut arena = TermArena::new();
    let syms: Vec<SymbolId> = VAR_NAMES
        .iter()
        .map(|name| arena.declare(name, Sort::BitVec(width)).unwrap())
        .collect();
    let vars: Vec<TermId> = syms.iter().map(|&s| arena.var(s)).collect();

    let config = SolverConfig {
        warm_keep_trail: keep_trail,
        ..SolverConfig::default()
    };
    let mut warm = IncrementalBvSolver::with_config(config);
    assert_eq!(
        warm.warm_keep_trail(),
        keep_trail,
        "the arm must be the one asked for"
    );

    #[cfg(feature = "z3")]
    let mirror = Z3Mirror::new(width);

    // The live assertion stack, one Vec per scope, for the one-shot reference.
    let mut scopes: Vec<Vec<TermId>> = vec![Vec::new()];
    let fail = |step: usize, what: &str| {
        Some(format!(
            "keep_trail={keep_trail} step {step}: {what}\n--- session ---\n{}",
            session.smt2()
        ))
    };

    for (step, op) in session.ops.iter().enumerate() {
        match op {
            Op::Push => {
                warm.push().expect("push");
                scopes.push(Vec::new());
                #[cfg(feature = "z3")]
                mirror.solver.push();
            }
            Op::Pop => {
                assert!(warm.pop(), "pop with a scope open");
                scopes.pop();
                #[cfg(feature = "z3")]
                mirror.solver.pop(1);
            }
            Op::Assert(atom) => {
                let term = atom.build(&mut arena, width, &vars);
                warm.assert(&arena, term).expect("assert");
                scopes.last_mut().expect("base scope").push(term);
                #[cfg(feature = "z3")]
                mirror.solver.assert(atom.z3(width, &mirror.vars));
            }
            Op::Check | Op::CheckAssuming(_) => {
                let temps: Vec<TermId> = match op {
                    Op::CheckAssuming(atoms) => atoms
                        .iter()
                        .map(|atom| atom.build(&mut arena, width, &vars))
                        .collect(),
                    _ => Vec::new(),
                };
                let result = if temps.is_empty() {
                    warm.check(&arena)
                } else {
                    warm.check_assuming(&arena, &temps)
                }
                .expect("warm check");
                tally.checks += 1;
                if warm.last_check_reused_trail_len() > 0 {
                    tally.reused_checks += 1;
                }
                let live: Vec<TermId> = scopes
                    .iter()
                    .flatten()
                    .copied()
                    .chain(temps.iter().copied())
                    .collect();
                let verdict = label(&result);
                match verdict {
                    Verdict::Sat => tally.sat += 1,
                    Verdict::Unsat => tally.unsat += 1,
                    Verdict::Unknown => tally.unknown += 1,
                }
                // (1) Replay: a warm `sat` must satisfy every live term.
                if let CheckResult::Sat(model) = &result {
                    let assignment = model.to_assignment();
                    for (i, &term) in live.iter().enumerate() {
                        match eval(&arena, term, &assignment) {
                            Ok(Value::Bool(true)) => {}
                            other => {
                                return fail(
                                    step,
                                    &format!(
                                        "warm sat model does not replay live term #{i}: {other:?}"
                                    ),
                                );
                            }
                        }
                    }
                }
                // (2) A fresh one-shot solve of the live set.
                let fresh = solve(&mut arena, &live, &SolverConfig::default()).expect("one-shot");
                let fresh_verdict = label(&fresh);
                if verdict != Verdict::Unknown
                    && fresh_verdict != Verdict::Unknown
                    && verdict != fresh_verdict
                {
                    return fail(
                        step,
                        &format!("warm {verdict:?} vs one-shot {fresh_verdict:?} on the live set"),
                    );
                }
                // (3) z3, driven incrementally through the same stream.
                #[cfg(feature = "z3")]
                {
                    let z3_temps: Vec<z3::ast::Bool> = match op {
                        Op::CheckAssuming(atoms) => {
                            atoms.iter().map(|a| a.z3(width, &mirror.vars)).collect()
                        }
                        _ => Vec::new(),
                    };
                    let z3_verdict = Z3Mirror::verdict(if z3_temps.is_empty() {
                        mirror.solver.check()
                    } else {
                        mirror.solver.check_assumptions(&z3_temps)
                    });
                    if z3_verdict == Verdict::Unknown {
                        tally.z3_unknown += 1;
                    } else {
                        tally.z3_compared += 1;
                        if verdict != Verdict::Unknown && verdict != z3_verdict {
                            return fail(step, &format!("warm {verdict:?} vs z3 {z3_verdict:?}"));
                        }
                        if fresh_verdict != Verdict::Unknown && fresh_verdict != z3_verdict {
                            return fail(
                                step,
                                &format!("one-shot {fresh_verdict:?} vs z3 {z3_verdict:?}"),
                            );
                        }
                    }
                }
            }
        }
    }
    None
}

fn configured_u64(name: &str, default: u64) -> u64 {
    match std::env::var(name) {
        Ok(text) => text
            .trim()
            .parse()
            .unwrap_or_else(|e| panic!("{name}={text:?}: {e}")),
        Err(_) => default,
    }
}

fn sweep(keep_trail: bool) {
    let sessions = configured_u64("AXEYUM_INCR_SESSIONS", 150);
    let seed = configured_u64("AXEYUM_INCR_SEED", 0);
    let mut tally = Tally {
        checks: 0,
        sat: 0,
        unsat: 0,
        unknown: 0,
        reused_checks: 0,
        z3_compared: 0,
        z3_unknown: 0,
    };
    let mut failures = Vec::new();
    for i in 0..sessions {
        let mut rng = Mix::new(seed.wrapping_mul(1_000_003).wrapping_add(i));
        let session = Session::generate(&mut rng);
        if let Some(failure) = run_session(&session, keep_trail, &mut tally) {
            failures.push(format!("session {i}: {failure}"));
            if failures.len() >= 3 {
                break;
            }
        }
    }
    println!(
        "incremental_bv_session_fuzz keep_trail={keep_trail}: sessions {sessions} checks {} sat {} unsat {} unknown {} reused-trail checks {} z3-compared {} z3-unknown {}",
        tally.checks,
        tally.sat,
        tally.unsat,
        tally.unknown,
        tally.reused_checks,
        tally.z3_compared,
        tally.z3_unknown
    );
    assert!(tally.checks > 0, "the sweep decided nothing");
    assert!(
        tally.sat > 0 && tally.unsat > 0,
        "the population must reach both verdicts: sat {} unsat {}",
        tally.sat,
        tally.unsat
    );
    if keep_trail {
        assert!(
            tally.reused_checks > 0,
            "the keep_trail arm never reused a trail entry: the arm is not exercising ADR-2145"
        );
    } else {
        assert_eq!(
            tally.reused_checks, 0,
            "the shipped schedule must reuse nothing (the gauge would be lying otherwise)"
        );
    }
    #[cfg(feature = "z3")]
    assert!(tally.z3_compared > 0, "z3 adjudicated nothing");
    assert!(
        failures.is_empty(),
        "{} session(s) disagreed:\n{}",
        failures.len(),
        failures.join("\n\n")
    );
}

#[test]
fn incremental_sessions_agree_with_one_shot_and_z3_keep_trail_off() {
    sweep(false);
}

#[test]
fn incremental_sessions_agree_with_one_shot_and_z3_keep_trail_on() {
    sweep(true);
}

/// The shipped default keeps the trail (ADR-2145's decision), and a solver
/// built with no explicit choice carries it. Skipped -- and says so -- when
/// the process-wide lever is set, because then the second half is a
/// statement about the environment rather than the default.
#[test]
fn the_shipped_default_keeps_the_trail() {
    // `black_box` so the pin is a runtime check of the constant rather than
    // something clippy folds away as an assertion on a literal; the point is
    // that a moved default kills exactly this test.
    assert!(
        std::hint::black_box(DEFAULT_WARM_KEEP_TRAIL),
        "ADR-2145 shipped the retained-trail schedule ON; moving it is a new decision"
    );
    if std::env::var_os("AXEYUM_WARM_KEEP_TRAIL").is_some() {
        eprintln!("AXEYUM_WARM_KEEP_TRAIL is set: the default-carrying half is not measured here");
        return;
    }
    assert!(IncrementalBvSolver::new().warm_keep_trail());
    assert!(SolverConfig::default().warm_keep_trail);
}

/// The directed shape the schedule exists for: a scope that forces a value is
/// popped and its sibling asserts the opposite. The popped scope's implication
/// must not survive into the sibling's check on either arm.
#[test]
fn a_popped_scope_does_not_constrain_its_sibling() {
    for keep_trail in [false, true] {
        let mut arena = TermArena::new();
        let x = arena.declare("x", Sort::BitVec(8)).unwrap();
        let x = arena.var(x);
        let five = arena.bv_const(8, 5).unwrap();
        let seven = arena.bv_const(8, 7).unwrap();
        let x_is_5 = arena.eq(x, five).unwrap();
        let x_is_7 = arena.eq(x, seven).unwrap();
        let config = SolverConfig {
            warm_keep_trail: keep_trail,
            ..SolverConfig::default()
        };
        let mut warm = IncrementalBvSolver::with_config(config);
        warm.push().unwrap();
        warm.assert(&arena, x_is_5).unwrap();
        assert!(matches!(warm.check(&arena).unwrap(), CheckResult::Sat(_)));
        assert!(warm.pop());
        warm.push().unwrap();
        warm.assert(&arena, x_is_7).unwrap();
        let sibling = warm.check(&arena).unwrap();
        let CheckResult::Sat(model) = sibling else {
            panic!(
                "keep_trail={keep_trail}: the popped scope leaked into its sibling: {sibling:?}"
            );
        };
        assert_eq!(
            eval(&arena, x_is_7, &model.to_assignment()).unwrap(),
            Value::Bool(true)
        );
        // Control: both together are unsat, so the checks above are not
        // "sat regardless".
        warm.push().unwrap();
        warm.assert(&arena, x_is_5).unwrap();
        assert!(matches!(warm.check(&arena).unwrap(), CheckResult::Unsat));
    }
}
