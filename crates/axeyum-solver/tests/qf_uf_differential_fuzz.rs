//! Adversarial differential fuzz for **pure EUF** (congruence closure),
//! cross-checked against the Z3 oracle.
//!
//! EUF congruence is the keystone the whole online-combination spine rests on,
//! but it was previously only fuzzed *indirectly* (through `uflia_`, which mixes
//! in linear integer arithmetic). This gate generates terms built purely from
//! uninterpreted functions `f: Int->Int`, `g: Int×Int->Int`, integer variables,
//! and constants — **no arithmetic operators** — related by `=`/`!=` and folded
//! into a Boolean formula by `and`/`or`. So the only reasoning under test is
//! congruence closure + the SAT-core case-splitting that drives it. (`Int` is
//! merely the carrier sort; with no `+`/`*` the problem is decided as EUF.)
//!
//! Soundness contract:
//! - axeyum `Sat`  ∧ Z3 `Unsat` → **PANIC** (wrong sat).
//! - axeyum `Unsat` ∧ Z3 `Sat`  → **PANIC** (wrong unsat — the worst bug).
//! - axeyum `Unknown` → fine; Z3 `Unknown`/timeout → skip.
//!
//! Deterministic (seeded LCG); each axeyum solve runs under a wall-clock cap on a
//! worker thread so a slow instance is skipped, not hung.

#![cfg(feature = "z3")]

use std::sync::mpsc;
use std::time::Duration;

use axeyum_ir::{FuncId, Sort, TermArena, TermId};
use axeyum_solver::{CheckResult, SolverConfig, solve};
use z3::ast::{Ast, Bool, Int};
use z3::{FuncDecl, Params, SatResult, Solver, Sort as Z3Sort};

const INSTANCES: u64 = 1500;
const AXEYUM_TIMEOUT: Duration = Duration::from_secs(3);
const Z3_TIMEOUT: Duration = Duration::from_secs(2);

/// Deterministic LCG (MMIX constants).
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
    fn flip(&mut self) -> bool {
        self.next_u64() & 1 == 1
    }
}

/// An EUF term: a small constant, a variable, or a (nested) application of the
/// uninterpreted `f`/`g`. Plain data (no IR/Z3 handles) → `Send` + `Clone`.
#[derive(Clone)]
enum Term {
    Const(i64),
    Var(usize),
    F(Box<Term>),
    G(Box<Term>, Box<Term>),
}

impl Term {
    fn generate(rng: &mut Lcg, num_vars: usize, depth: u32) -> Term {
        // At depth 0 only leaves; otherwise mix leaves and applications so terms
        // stay small but share structure (the interesting case for congruence).
        let choice = if depth == 0 {
            rng.below(2)
        } else {
            rng.below(4)
        };
        match choice {
            0 => Term::Const(i64::try_from(rng.below(4)).unwrap()), // 0..=3 (small ⇒ collisions)
            1 => Term::Var(rng.below(num_vars as u64)),
            2 => Term::F(Box::new(Term::generate(rng, num_vars, depth - 1))),
            _ => Term::G(
                Box::new(Term::generate(rng, num_vars, depth - 1)),
                Box::new(Term::generate(rng, num_vars, depth - 1)),
            ),
        }
    }

    fn build_ir(&self, a: &mut TermArena, vars: &[TermId], f: FuncId, g: FuncId) -> TermId {
        match self {
            Term::Const(k) => a.int_const(i128::from(*k)),
            Term::Var(i) => vars[*i],
            Term::F(t) => {
                let arg = t.build_ir(a, vars, f, g);
                a.apply(f, &[arg]).unwrap()
            }
            Term::G(t1, t2) => {
                let a1 = t1.build_ir(a, vars, f, g);
                let a2 = t2.build_ir(a, vars, f, g);
                a.apply(g, &[a1, a2]).unwrap()
            }
        }
    }

    fn build_z3(&self, vars: &[Int], f: &FuncDecl, g: &FuncDecl) -> Int {
        match self {
            Term::Const(k) => Int::from_i64(*k),
            Term::Var(i) => vars[*i].clone(),
            Term::F(t) => {
                let arg = t.build_z3(vars, f, g);
                f.apply(&[&arg as &dyn Ast]).as_int().unwrap()
            }
            Term::G(t1, t2) => {
                let a1 = t1.build_z3(vars, f, g);
                let a2 = t2.build_z3(vars, f, g);
                g.apply(&[&a1 as &dyn Ast, &a2 as &dyn Ast])
                    .as_int()
                    .unwrap()
            }
        }
    }

    fn dump(&self) -> String {
        match self {
            Term::Const(k) => k.to_string(),
            Term::Var(i) => ["x", "y", "z"][*i].to_string(),
            Term::F(t) => format!("f({})", t.dump()),
            Term::G(t1, t2) => format!("g({},{})", t1.dump(), t2.dump()),
        }
    }
}

/// `lhs = rhs` (or `!=`).
#[derive(Clone)]
struct Atom {
    lhs: Term,
    rhs: Term,
    ne: bool,
}

/// Atoms folded into a Boolean formula by `ops` (`true` = `and`, else `or`).
#[derive(Clone)]
struct Instance {
    num_vars: usize,
    atoms: Vec<Atom>,
    ops: Vec<bool>,
}

impl Instance {
    fn generate(rng: &mut Lcg) -> Instance {
        let num_vars = rng.below(2) + 2; // 2..=3
        let num_atoms = rng.below(4) + 2; // 2..=5
        let atoms = (0..num_atoms)
            .map(|_| Atom {
                lhs: Term::generate(rng, num_vars, 2),
                rhs: Term::generate(rng, num_vars, 2),
                ne: rng.flip(),
            })
            .collect();
        let ops = (0..num_atoms - 1).map(|_| rng.flip()).collect();
        Instance {
            num_vars,
            atoms,
            ops,
        }
    }

    fn build(&self) -> (TermArena, Vec<TermId>) {
        let mut a = TermArena::new();
        let names = ["x", "y", "z"];
        let vars: Vec<TermId> = (0..self.num_vars)
            .map(|i| {
                let s = a.declare(names[i], Sort::Int).unwrap();
                a.var(s)
            })
            .collect();
        let f = a.declare_fun("f", &[Sort::Int], Sort::Int).unwrap();
        let g = a
            .declare_fun("g", &[Sort::Int, Sort::Int], Sort::Int)
            .unwrap();

        let bools: Vec<TermId> = self
            .atoms
            .iter()
            .map(|atom| {
                let lhs = atom.lhs.build_ir(&mut a, &vars, f, g);
                let rhs = atom.rhs.build_ir(&mut a, &vars, f, g);
                let eq = a.eq(lhs, rhs).unwrap();
                if atom.ne { a.not(eq).unwrap() } else { eq }
            })
            .collect();

        let mut acc = bools[0];
        for (i, &child) in bools.iter().enumerate().skip(1) {
            acc = if self.ops[i - 1] {
                a.and(acc, child).unwrap()
            } else {
                a.or(acc, child).unwrap()
            };
        }
        (a, vec![acc])
    }

    fn to_z3(&self) -> Bool {
        let names = ["x", "y", "z"];
        let vars: Vec<Int> = (0..self.num_vars)
            .map(|i| Int::new_const(names[i]))
            .collect();
        let int_sort = Z3Sort::int();
        let f = FuncDecl::new("f", &[&int_sort], &int_sort);
        let g = FuncDecl::new("g", &[&int_sort, &int_sort], &int_sort);

        let bools: Vec<Bool> = self
            .atoms
            .iter()
            .map(|atom| {
                let lhs = atom.lhs.build_z3(&vars, &f, &g);
                let rhs = atom.rhs.build_z3(&vars, &f, &g);
                let eq = lhs.eq(&rhs);
                if atom.ne { eq.not() } else { eq }
            })
            .collect();

        let mut acc = bools[0].clone();
        for (i, child) in bools.iter().enumerate().skip(1) {
            acc = if self.ops[i - 1] {
                Bool::and(&[acc, child.clone()])
            } else {
                Bool::or(&[acc, child.clone()])
            };
        }
        acc
    }

    fn dump(&self) -> String {
        let mut lines = vec![format!(
            "vars: {}",
            ["x", "y", "z"][..self.num_vars].join(", ")
        )];
        for (i, atom) in self.atoms.iter().enumerate() {
            let op = if atom.ne { "!=" } else { "=" };
            lines.push(format!(
                "  atom[{i}]: {} {op} {}",
                atom.lhs.dump(),
                atom.rhs.dump()
            ));
        }
        lines.push(format!(
            "  ops: {}",
            self.ops
                .iter()
                .map(|&o| if o { "and" } else { "or" })
                .collect::<Vec<_>>()
                .join(", ")
        ));
        lines.join("\n")
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Verdict {
    Sat,
    Unsat,
    Unknown,
}

fn solve_axeyum_bounded(inst: Instance) -> Verdict {
    let (tx, rx) = mpsc::channel();
    std::thread::Builder::new()
        .stack_size(256 * 1024 * 1024)
        .spawn(move || {
            let (mut a, assertions) = inst.build();
            let v = match solve(&mut a, &assertions, &SolverConfig::default()) {
                Ok(CheckResult::Sat(_)) => Verdict::Sat,
                Ok(CheckResult::Unsat) => Verdict::Unsat,
                Ok(CheckResult::Unknown(_)) | Err(_) => Verdict::Unknown,
            };
            let _ = tx.send(v);
        })
        .expect("spawn solver thread");
    rx.recv_timeout(AXEYUM_TIMEOUT).unwrap_or(Verdict::Unknown)
}

fn z3_decide(inst: &Instance) -> Verdict {
    let solver = Solver::new();
    let mut params = Params::new();
    params.set_u32(
        "timeout",
        u32::try_from(Z3_TIMEOUT.as_millis()).unwrap_or(u32::MAX),
    );
    solver.set_params(&params);
    solver.assert(inst.to_z3());
    match solver.check() {
        SatResult::Sat => Verdict::Sat,
        SatResult::Unsat => Verdict::Unsat,
        SatResult::Unknown => Verdict::Unknown,
    }
}

#[test]
fn qf_uf_differential_fuzz_disagree_zero() {
    let mut agree = 0u64;
    let mut ax_unknown = 0u64;
    let mut z3_unknown = 0u64;

    for seed in 0..INSTANCES {
        let inst = Instance::generate(&mut Lcg::new(seed));
        let ax = solve_axeyum_bounded(inst.clone());
        let z3 = z3_decide(&inst);

        match (ax, z3) {
            (Verdict::Sat, Verdict::Unsat) | (Verdict::Unsat, Verdict::Sat) => {
                panic!(
                    "DISAGREEMENT (seed {seed}): axeyum = {ax:?}, Z3 = {z3:?}.\n{}",
                    inst.dump()
                );
            }
            (Verdict::Unknown, _) => ax_unknown += 1,
            (_, Verdict::Unknown) => z3_unknown += 1,
            _ => agree += 1,
        }
    }

    println!(
        "qf_uf fuzz: {INSTANCES} instances | {agree} agree | {ax_unknown} axeyum-unknown | {z3_unknown} z3-unknown(skipped) | 0 DISAGREE"
    );
    assert!(
        agree >= INSTANCES / 2,
        "expected >= {} agreements, got {agree} (axeyum-unknown {ax_unknown}) — EUF dispatch regression?",
        INSTANCES / 2
    );
}
