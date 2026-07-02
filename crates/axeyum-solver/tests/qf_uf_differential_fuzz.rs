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

use axeyum_ir::{FuncId, Sort, SortId, TermArena, TermId};
use axeyum_solver::{CheckResult, SolverConfig, solve};
use z3::ast::{Ast, Bool, Dynamic, Int};
use z3::{FuncDecl, Params, SatResult, Solver, Sort as Z3Sort, Symbol};

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

// ---------------------------------------------------------------------------
// Uninterpreted-sort ITE fuzz.
//
// The pure-EUF generator above never exercises the QF_UF *model assembly* path
// that must inject skeleton-only Bool condition symbols: it has no `ite` and no
// Bool leaves. This second generator builds formulas over a **declared
// uninterpreted sort** `U` — U-sorted variables, a unary function `h: U -> U`,
// and **nested `ite` guarded by Bool condition symbols** (which appear only in
// the Boolean skeleton, never as an equality side) — related by `=`/`!=` and
// folded by `and`/`or`. Deciding these SAT cases requires the P1.4 fix that
// injects those condition symbols into the built model so it replays. Same
// DISAGREE=0 contract, same seeded-LCG determinism.
// ---------------------------------------------------------------------------

const ITE_INSTANCES: u64 = 1500;

/// A Bool condition (a symbol or its negation) guarding an `ite`.
#[derive(Clone)]
enum Cond {
    Var(usize),
    Not(Box<Cond>),
}

impl Cond {
    fn generate(rng: &mut Lcg, num_conds: usize, depth: u32) -> Cond {
        // Mostly a bare symbol; occasionally a negation so `(not a)` appears.
        if depth > 0 && rng.below(3) == 0 {
            Cond::Not(Box::new(Cond::generate(rng, num_conds, depth - 1)))
        } else {
            Cond::Var(rng.below(num_conds as u64))
        }
    }

    fn build_ir(&self, a: &mut TermArena, conds: &[TermId]) -> TermId {
        match self {
            Cond::Var(i) => conds[*i],
            Cond::Not(c) => {
                let inner = c.build_ir(a, conds);
                a.not(inner).unwrap()
            }
        }
    }

    fn build_z3(&self, conds: &[Bool]) -> Bool {
        match self {
            Cond::Var(i) => conds[*i].clone(),
            Cond::Not(c) => c.build_z3(conds).not(),
        }
    }

    fn dump(&self) -> String {
        match self {
            Cond::Var(i) => ["a", "b", "c"][*i].to_string(),
            Cond::Not(c) => format!("(not {})", c.dump()),
        }
    }
}

/// A `U`-sorted term: a variable, an application of `h`, or a nested `ite`.
/// Plain data (no IR/Z3 handles) → `Send` + `Clone`.
#[derive(Clone)]
enum UTerm {
    Var(usize),
    H(Box<UTerm>),
    Ite(Cond, Box<UTerm>, Box<UTerm>),
}

impl UTerm {
    fn generate(rng: &mut Lcg, num_vars: usize, num_conds: usize, depth: u32) -> UTerm {
        let choice = if depth == 0 { 0 } else { rng.below(3) };
        match choice {
            0 => UTerm::Var(rng.below(num_vars as u64)),
            1 => UTerm::H(Box::new(UTerm::generate(
                rng,
                num_vars,
                num_conds,
                depth - 1,
            ))),
            _ => UTerm::Ite(
                Cond::generate(rng, num_conds, 1),
                Box::new(UTerm::generate(rng, num_vars, num_conds, depth - 1)),
                Box::new(UTerm::generate(rng, num_vars, num_conds, depth - 1)),
            ),
        }
    }

    fn build_ir(&self, a: &mut TermArena, vars: &[TermId], conds: &[TermId], h: FuncId) -> TermId {
        match self {
            UTerm::Var(i) => vars[*i],
            UTerm::H(t) => {
                let arg = t.build_ir(a, vars, conds, h);
                a.apply(h, &[arg]).unwrap()
            }
            UTerm::Ite(c, then_t, else_t) => {
                let cond = c.build_ir(a, conds);
                let then_ir = then_t.build_ir(a, vars, conds, h);
                let else_ir = else_t.build_ir(a, vars, conds, h);
                a.ite(cond, then_ir, else_ir).unwrap()
            }
        }
    }

    fn build_z3(&self, vars: &[Dynamic], conds: &[Bool], h: &FuncDecl) -> Dynamic {
        match self {
            UTerm::Var(i) => vars[*i].clone(),
            UTerm::H(t) => {
                let arg = t.build_z3(vars, conds, h);
                h.apply(&[&arg as &dyn Ast])
            }
            UTerm::Ite(c, then_t, else_t) => {
                let cond = c.build_z3(conds);
                let then_z3 = then_t.build_z3(vars, conds, h);
                let else_z3 = else_t.build_z3(vars, conds, h);
                cond.ite(&then_z3, &else_z3)
            }
        }
    }

    fn dump(&self) -> String {
        match self {
            UTerm::Var(i) => ["x", "y", "z"][*i].to_string(),
            UTerm::H(t) => format!("h({})", t.dump()),
            UTerm::Ite(c, then_t, else_t) => {
                format!("ite({},{},{})", c.dump(), then_t.dump(), else_t.dump())
            }
        }
    }
}

/// `lhs = rhs` (or `!=`) over the uninterpreted sort.
#[derive(Clone)]
struct UAtom {
    lhs: UTerm,
    rhs: UTerm,
    ne: bool,
}

/// Uninterpreted-sort atoms folded by `ops` (`true` = `and`, else `or`).
#[derive(Clone)]
struct IteInstance {
    num_vars: usize,
    num_conds: usize,
    atoms: Vec<UAtom>,
    ops: Vec<bool>,
}

impl IteInstance {
    fn generate(rng: &mut Lcg) -> IteInstance {
        let num_vars = rng.below(2) + 2; // 2..=3 U-sorted variables
        let num_conds = rng.below(2) + 2; // 2..=3 Bool condition symbols
        let num_atoms = rng.below(3) + 2; // 2..=4
        let atoms = (0..num_atoms)
            .map(|_| UAtom {
                lhs: UTerm::generate(rng, num_vars, num_conds, 2),
                rhs: UTerm::generate(rng, num_vars, num_conds, 2),
                ne: rng.flip(),
            })
            .collect();
        let ops = (0..num_atoms - 1).map(|_| rng.flip()).collect();
        IteInstance {
            num_vars,
            num_conds,
            atoms,
            ops,
        }
    }

    fn build(&self) -> (TermArena, Vec<TermId>) {
        let mut a = TermArena::new();
        let sort_id: SortId = a.declare_uninterpreted_sort("U");
        let u = Sort::Uninterpreted(sort_id);
        let vnames = ["x", "y", "z"];
        let vars: Vec<TermId> = (0..self.num_vars)
            .map(|i| {
                let s = a.declare(vnames[i], u).unwrap();
                a.var(s)
            })
            .collect();
        let cnames = ["a", "b", "c"];
        let conds: Vec<TermId> = (0..self.num_conds)
            .map(|i| {
                let s = a.declare(cnames[i], Sort::Bool).unwrap();
                a.var(s)
            })
            .collect();
        let h = a.declare_fun("h", &[u], u).unwrap();

        let bools: Vec<TermId> = self
            .atoms
            .iter()
            .map(|atom| {
                let lhs = atom.lhs.build_ir(&mut a, &vars, &conds, h);
                let rhs = atom.rhs.build_ir(&mut a, &vars, &conds, h);
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
        let u = Z3Sort::uninterpreted(Symbol::from("U"));
        let vnames = ["x", "y", "z"];
        let vars: Vec<Dynamic> = (0..self.num_vars)
            .map(|i| Dynamic::new_const(vnames[i], &u))
            .collect();
        let cnames = ["a", "b", "c"];
        let conds: Vec<Bool> = (0..self.num_conds)
            .map(|i| Bool::new_const(cnames[i]))
            .collect();
        let h = FuncDecl::new("h", &[&u], &u);

        let bools: Vec<Bool> = self
            .atoms
            .iter()
            .map(|atom| {
                let lhs = atom.lhs.build_z3(&vars, &conds, &h);
                let rhs = atom.rhs.build_z3(&vars, &conds, &h);
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
            "vars(U): {} | conds(Bool): {}",
            ["x", "y", "z"][..self.num_vars].join(", "),
            ["a", "b", "c"][..self.num_conds].join(", ")
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

fn solve_axeyum_ite_bounded(inst: IteInstance) -> Verdict {
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

fn z3_decide_ite(inst: &IteInstance) -> Verdict {
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
fn qf_uf_ite_uninterpreted_sort_fuzz_disagree_zero() {
    let mut agree = 0u64;
    let mut ax_unknown = 0u64;
    let mut z3_unknown = 0u64;

    for seed in 0..ITE_INSTANCES {
        // Offset the seed stream from the pure-EUF gate so the two fuzzes cover
        // disjoint instances.
        let inst = IteInstance::generate(&mut Lcg::new(seed ^ 0xA5A5_A5A5));
        let ax = solve_axeyum_ite_bounded(inst.clone());
        let z3 = z3_decide_ite(&inst);

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
        "qf_uf ite/uninterpreted-sort fuzz: {ITE_INSTANCES} instances | {agree} agree | {ax_unknown} axeyum-unknown | {z3_unknown} z3-unknown(skipped) | 0 DISAGREE"
    );
    assert!(
        agree >= ITE_INSTANCES / 4,
        "expected >= {} agreements, got {agree} (axeyum-unknown {ax_unknown}) — QF_UF ite model-assembly regression?",
        ITE_INSTANCES / 4
    );
}
