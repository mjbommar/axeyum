//! Adversarial differential soundness fuzzer for the **quantified-UFLIA sat
//! direction** opened by MBQI model-finding (P2.6 T2.6.5), against the Z3 oracle.
//!
//! The new capability certifies a candidate model of a top-level universal
//! `∀x. body` as a *genuine* model — returning `sat` — when `x` is `Int` and
//! occurs only as a direct argument of an uninterpreted function (the
//! almost-uninterpreted fragment). A wrong `sat` here (a "model" that does not
//! actually satisfy `∀x. body`) would be the worst possible bug, so this harness
//! exists to catch it: it deterministically generates thousands of small
//! quantified-UFLIA instances **inside the fragment** (`x` appears only under the
//! unary UFs `f`/`g`), decides each with both the pure-Rust public MBQI loop and
//! a direct Z3 query over the *same* universal + ground facts, and gates on the
//! joint verdict. The unified `solve` front door is covered separately by the
//! focused integration tests; calling MBQI directly keeps this differential
//! specific to the capability under test:
//!
//! - axeyum `Sat` ∧ Z3 `Unsat` → **PANIC** (wrong sat — the target bug).
//! - axeyum `Unsat` ∧ Z3 `Sat` → **PANIC** (wrong unsat).
//! - axeyum `Sat` → canonical `check_model` must accept the exact quantified
//!   source and certificate; the returned model is then additionally sampled:
//!   every ground fact must evaluate `true`, and the universal body is
//!   re-evaluated at a wide sweep of concrete `x`-values. Any failure panics
//!   regardless of Z3.
//! - axeyum `Unknown` is ALLOWED (incomplete is sound) — counted, never failed.
//! - Z3 `Unknown`/timeout → the instance is skipped (cannot adjudicate).
//!
//! Every generated construct has identical semantics in both engines (`f`/`g` are
//! uninterpreted on both sides; only Int arithmetic, the six comparators, and
//! `and`/`or` appear — no partial operators), so a jointly-decided disagreement
//! is a real bug, never a false alarm.
#![cfg(feature = "full")]
#![cfg(feature = "z3")]
// The generated-term algebra uses conventional single-letter coefficient/operand
// names (`a`, `b`, `c`, `f`, `g`, `l`, `r`, `x`) that read naturally as the small
// arithmetic they denote; clumping them for the sake of the lint would hurt, not
// help, readability of this fuzz harness.
#![allow(clippy::many_single_char_names)]

use std::{
    collections::{BTreeMap, BTreeSet},
    time::{Duration, Instant},
};

use axeyum_ir::{Assignment, FuncId, Sort, SymbolId, TermArena, TermId, TermNode, Value, eval};
use axeyum_solver::{
    CheckResult, Model, SolverConfig, check_auto, check_model, prove_unsat_by_mbqi,
};
use z3::ast::{Ast, Bool, Int};
use z3::{FuncDecl, Params, SatResult, Solver, Sort as Z3Sort};

/// Bounded per-commit smoke sweep. The full 2,000-instance campaign is retained
/// below as an explicit ignored test: putting its multi-minute-to-hour runtime in
/// `cargo test --workspace` made the canonical gate unable to finish reliably.
const SMOKE_INSTANCES: u64 = 256;
const FULL_INSTANCES: u64 = 2000;

/// Per-instance Z3 wall-clock budget.
const Z3_TIMEOUT: Duration = Duration::from_secs(2);

/// Per-instance axeyum solve timeout (via the config; keeps the sweep bounded).
const AXEYUM_TIMEOUT: Duration = Duration::from_secs(3);

/// Concrete `x`-values at which a returned `sat` model's universal body is
/// independently re-evaluated (an over-large-but-cheap sweep around the small
/// constants the generator uses).
const REPLAY_SWEEP: std::ops::RangeInclusive<i128> = -40..=40;

/// A deterministic LCG (MMIX constants) — no clock, fully reproducible.
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
    fn in_range(&mut self, lo: i64, hi: i64) -> i64 {
        let span = u64::try_from(hi - lo + 1).expect("non-negative span");
        lo + i64::try_from(self.next_u64() % span).expect("offset within span")
    }
}

#[derive(Clone, Copy)]
enum Cmp {
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
}

impl Cmp {
    fn pick(rng: &mut Lcg) -> Cmp {
        match rng.below(6) {
            0 => Cmp::Eq,
            1 => Cmp::Ne,
            2 => Cmp::Lt,
            3 => Cmp::Le,
            4 => Cmp::Gt,
            _ => Cmp::Ge,
        }
    }
    fn symbol(self) -> &'static str {
        match self {
            Cmp::Eq => "=",
            Cmp::Ne => "!=",
            Cmp::Lt => "<",
            Cmp::Le => "<=",
            Cmp::Gt => ">",
            Cmp::Ge => ">=",
        }
    }
    fn build(self, a: &mut TermArena, lhs: TermId, rhs: TermId) -> TermId {
        match self {
            Cmp::Eq => a.eq(lhs, rhs).unwrap(),
            Cmp::Ne => {
                let e = a.eq(lhs, rhs).unwrap();
                a.not(e).unwrap()
            }
            Cmp::Lt => a.int_lt(lhs, rhs).unwrap(),
            Cmp::Le => a.int_le(lhs, rhs).unwrap(),
            Cmp::Gt => a.int_gt(lhs, rhs).unwrap(),
            Cmp::Ge => a.int_ge(lhs, rhs).unwrap(),
        }
    }
    fn build_z3(self, lhs: &Int, rhs: &Int) -> Bool {
        match self {
            Cmp::Eq => lhs.eq(rhs),
            Cmp::Ne => lhs.ne(rhs),
            Cmp::Lt => lhs.lt(rhs),
            Cmp::Le => lhs.le(rhs),
            Cmp::Gt => lhs.gt(rhs),
            Cmp::Ge => lhs.ge(rhs),
        }
    }
}

/// An Int term. The bound variable `X` is produced **only** as the direct
/// argument of an `F`/`G` (uninterpreted) node, so every generated term keeps `x`
/// inside the almost-uninterpreted fragment (`x` never in an interpreted
/// position). `Y(i)` are ground Int variables; `Lin` is a linear combination
/// whose operands are themselves `x`-position-safe.
#[derive(Clone)]
enum T {
    X,
    Y(usize),
    C(i64),
    F(Box<T>),
    G(Box<T>),
    Lin(i64, Box<T>, i64, Box<T>, i64),
}

/// Generate a term that is safe to place in an **interpreted** position (never a
/// bare `X`): `x` may appear only nested under an `F`/`G`.
fn gen_term(rng: &mut Lcg, depth: usize, num_ground: usize) -> T {
    if depth == 0 {
        return if rng.below(2) == 0 {
            T::C(rng.in_range(-4, 4))
        } else {
            T::Y(rng.below(num_ground as u64))
        };
    }
    match rng.below(5) {
        0 => T::Y(rng.below(num_ground as u64)),
        1 => T::C(rng.in_range(-4, 4)),
        2 => T::F(Box::new(gen_uf_arg(rng, depth - 1, num_ground))),
        3 => T::G(Box::new(gen_uf_arg(rng, depth - 1, num_ground))),
        _ => T::Lin(
            rng.in_range(-3, 3),
            Box::new(gen_term(rng, depth - 1, num_ground)),
            rng.in_range(-3, 3),
            Box::new(gen_term(rng, depth - 1, num_ground)),
            rng.in_range(-3, 3),
        ),
    }
}

/// Generate the **argument of a UF application**, where a bare `X` IS allowed
/// (its direct parent is the enclosing `F`/`G`, keeping it in the fragment).
fn gen_uf_arg(rng: &mut Lcg, depth: usize, num_ground: usize) -> T {
    if depth == 0 {
        return match rng.below(3) {
            0 => T::X,
            1 => T::C(rng.in_range(-4, 4)),
            _ => T::Y(rng.below(num_ground as u64)),
        };
    }
    match rng.below(6) {
        0 => T::X,
        1 => T::Y(rng.below(num_ground as u64)),
        2 => T::C(rng.in_range(-4, 4)),
        3 => T::F(Box::new(gen_uf_arg(rng, depth - 1, num_ground))),
        4 => T::G(Box::new(gen_uf_arg(rng, depth - 1, num_ground))),
        // `Lin` operands go through `gen_term` (never a bare `X`), so `X` stays
        // out of the interpreted `+`/`*` positions.
        _ => T::Lin(
            rng.in_range(-3, 3),
            Box::new(gen_term(rng, depth - 1, num_ground)),
            rng.in_range(-3, 3),
            Box::new(gen_term(rng, depth - 1, num_ground)),
            rng.in_range(-3, 3),
        ),
    }
}

/// Generate a genuinely ground term. Unlike [`gen_term`], this never delegates
/// to [`gen_uf_arg`], so `X` cannot appear even below an uninterpreted function.
fn gen_ground_term(rng: &mut Lcg, depth: usize, num_ground: usize) -> T {
    if depth == 0 {
        return if rng.below(2) == 0 {
            T::C(rng.in_range(-4, 4))
        } else {
            T::Y(rng.below(num_ground as u64))
        };
    }
    match rng.below(5) {
        0 => T::Y(rng.below(num_ground as u64)),
        1 => T::C(rng.in_range(-4, 4)),
        2 => T::F(Box::new(gen_ground_term(rng, depth - 1, num_ground))),
        3 => T::G(Box::new(gen_ground_term(rng, depth - 1, num_ground))),
        _ => T::Lin(
            rng.in_range(-3, 3),
            Box::new(gen_ground_term(rng, depth - 1, num_ground)),
            rng.in_range(-3, 3),
            Box::new(gen_ground_term(rng, depth - 1, num_ground)),
            rng.in_range(-3, 3),
        ),
    }
}

impl T {
    fn uses_x(&self) -> bool {
        match self {
            T::X => true,
            T::Y(_) | T::C(_) => false,
            T::F(t) | T::G(t) => t.uses_x(),
            T::Lin(_, a, _, b, _) => a.uses_x() || b.uses_x(),
        }
    }
    fn build(&self, a: &mut TermArena, x: TermId, ys: &[TermId], f: FuncId, g: FuncId) -> TermId {
        match self {
            T::X => x,
            T::Y(i) => ys[*i],
            T::C(k) => a.int_const(i128::from(*k)),
            T::F(t) => {
                let arg = t.build(a, x, ys, f, g);
                a.apply(f, &[arg]).unwrap()
            }
            T::G(t) => {
                let arg = t.build(a, x, ys, f, g);
                a.apply(g, &[arg]).unwrap()
            }
            T::Lin(ca, t1, cb, t2, c) => {
                let k1 = a.int_const(i128::from(*ca));
                let e1 = t1.build(a, x, ys, f, g);
                let p1 = a.int_mul(k1, e1).unwrap();
                let k2 = a.int_const(i128::from(*cb));
                let e2 = t2.build(a, x, ys, f, g);
                let p2 = a.int_mul(k2, e2).unwrap();
                let kc = a.int_const(i128::from(*c));
                let s = a.int_add(p1, p2).unwrap();
                a.int_add(s, kc).unwrap()
            }
        }
    }
    fn build_z3(&self, x: &Int, ys: &[Int], f: &FuncDecl, g: &FuncDecl) -> Int {
        match self {
            T::X => x.clone(),
            T::Y(i) => ys[*i].clone(),
            T::C(k) => Int::from_i64(*k),
            T::F(t) => f
                .apply(&[&t.build_z3(x, ys, f, g) as &dyn Ast])
                .as_int()
                .expect("f returns Int"),
            T::G(t) => g
                .apply(&[&t.build_z3(x, ys, f, g) as &dyn Ast])
                .as_int()
                .expect("g returns Int"),
            T::Lin(ca, t1, cb, t2, c) => {
                let p1 = Int::mul(&[Int::from_i64(*ca), t1.build_z3(x, ys, f, g)]);
                let p2 = Int::mul(&[Int::from_i64(*cb), t2.build_z3(x, ys, f, g)]);
                Int::add(&[p1, p2, Int::from_i64(*c)])
            }
        }
    }
    fn dump(&self) -> String {
        match self {
            T::X => "x".to_string(),
            T::Y(i) => format!("y{i}"),
            T::C(k) => k.to_string(),
            T::F(t) => format!("f({})", t.dump()),
            T::G(t) => format!("g({})", t.dump()),
            T::Lin(a, t1, b, t2, c) => {
                format!("({a}*{} + {b}*{} + {c})", t1.dump(), t2.dump())
            }
        }
    }

    fn collect_integer_literals(&self, values: &mut BTreeSet<i128>) {
        match self {
            T::X | T::Y(_) => {}
            T::C(value) => {
                values.insert(i128::from(*value));
            }
            T::F(term) | T::G(term) => term.collect_integer_literals(values),
            T::Lin(a, left, b, right, c) => {
                values.extend([i128::from(*a), i128::from(*b), i128::from(*c)]);
                left.collect_integer_literals(values);
                right.collect_integer_literals(values);
            }
        }
    }
}

#[derive(Clone)]
struct Atom {
    lhs: T,
    rhs: T,
    cmp: Cmp,
}

/// A full instance: one universal `∀x. (a₀ ∧ a₁ ∧ …)` (the body a conjunction of
/// atoms, at least one mentioning `x`) plus some ground facts.
#[derive(Clone)]
struct Instance {
    num_ground: usize,
    body_atoms: Vec<Atom>,
    ground_atoms: Vec<Atom>,
}

const MAX_DEPTH: usize = 2;

impl Instance {
    fn generate(rng: &mut Lcg) -> Instance {
        let num_ground = rng.below(2) + 1; // 1..=2 ground vars
        let n_body = rng.below(2) + 1; // 1..=2 body atoms
        let n_ground = rng.below(3); // 0..=2 ground facts

        let mut body_atoms = Vec::with_capacity(n_body);
        for _ in 0..n_body {
            body_atoms.push(Atom {
                lhs: gen_term(rng, MAX_DEPTH, num_ground),
                rhs: gen_term(rng, MAX_DEPTH, num_ground),
                cmp: Cmp::pick(rng),
            });
        }
        // Force `x` to appear in the universal body so the model-finder is
        // genuinely exercised (a vacuous universal is a different route).
        let uses_x = body_atoms
            .iter()
            .any(|at| at.lhs.uses_x() || at.rhs.uses_x());
        if !uses_x {
            body_atoms[0].lhs = T::F(Box::new(T::X));
        }

        let mut ground_atoms = Vec::with_capacity(n_ground);
        for _ in 0..n_ground {
            // Ground facts must be x-free (they live outside the quantifier).
            ground_atoms.push(Atom {
                lhs: gen_ground_term(rng, MAX_DEPTH, num_ground),
                rhs: gen_ground_term(rng, MAX_DEPTH, num_ground),
                cmp: Cmp::pick(rng),
            });
        }

        Instance {
            num_ground,
            body_atoms,
            ground_atoms,
        }
    }

    /// Build the axeyum assertions: `[∀x. body, ground_facts…]`. Returns the
    /// arena, the bound symbol, the raw (unquantified) body term, and the ground
    /// fact terms, so a `sat` model can be independently replayed.
    fn build_axeyum(
        &self,
    ) -> (
        TermArena,
        SymbolId,
        Vec<SymbolId>,
        TermId,
        Vec<TermId>,
        Vec<TermId>,
    ) {
        let mut a = TermArena::new();
        let x_sym = a.declare("x", Sort::Int).unwrap();
        let x = a.var(x_sym);
        let ynames = ["y0", "y1"];
        let y_symbols: Vec<SymbolId> = (0..self.num_ground)
            .map(|i| a.declare(ynames[i], Sort::Int).unwrap())
            .collect();
        let ys: Vec<TermId> = y_symbols.iter().map(|&symbol| a.var(symbol)).collect();
        let f = a.declare_fun("f", &[Sort::Int], Sort::Int).unwrap();
        let g = a.declare_fun("g", &[Sort::Int], Sort::Int).unwrap();

        let body_terms: Vec<TermId> = self
            .body_atoms
            .iter()
            .map(|at| {
                let l = at.lhs.build(&mut a, x, &ys, f, g);
                let r = at.rhs.build(&mut a, x, &ys, f, g);
                at.cmp.build(&mut a, l, r)
            })
            .collect();
        let body = conj(&mut a, &body_terms);
        let forall = a.forall(x_sym, body).unwrap();

        let ground_terms: Vec<TermId> = self
            .ground_atoms
            .iter()
            .map(|at| {
                let l = at.lhs.build(&mut a, x, &ys, f, g);
                let r = at.rhs.build(&mut a, x, &ys, f, g);
                at.cmp.build(&mut a, l, r)
            })
            .collect();

        let mut assertions = vec![forall];
        assertions.extend(ground_terms.iter().copied());
        (a, x_sym, y_symbols, body, ground_terms, assertions)
    }

    fn to_z3(&self, solver: &Solver) {
        let x = Int::new_const("x");
        let ynames = ["y0", "y1"];
        let ys: Vec<Int> = (0..self.num_ground)
            .map(|i| Int::new_const(ynames[i]))
            .collect();
        let int_sort = Z3Sort::int();
        let f = FuncDecl::new("f", &[&int_sort], &int_sort);
        let g = FuncDecl::new("g", &[&int_sort], &int_sort);

        let body: Vec<Bool> = self
            .body_atoms
            .iter()
            .map(|at| {
                let l = at.lhs.build_z3(&x, &ys, &f, &g);
                let r = at.rhs.build_z3(&x, &ys, &f, &g);
                at.cmp.build_z3(&l, &r)
            })
            .collect();
        let body_refs: Vec<&Bool> = body.iter().collect();
        let body_conj = Bool::and(&body_refs);
        let forall = z3::ast::forall_const(&[&x as &dyn Ast], &[], &body_conj);
        solver.assert(&forall);

        for at in &self.ground_atoms {
            let l = at.lhs.build_z3(&x, &ys, &f, &g);
            let r = at.rhs.build_z3(&x, &ys, &f, &g);
            solver.assert(at.cmp.build_z3(&l, &r));
        }
    }

    fn dump(&self) -> String {
        let mut lines = vec![format!(
            "ground vars: {}",
            (0..self.num_ground)
                .map(|i| format!("y{i}"))
                .collect::<Vec<_>>()
                .join(", ")
        )];
        let body = self
            .body_atoms
            .iter()
            .map(|at| format!("{} {} {}", at.lhs.dump(), at.cmp.symbol(), at.rhs.dump()))
            .collect::<Vec<_>>()
            .join(" ∧ ");
        lines.push(format!("(assert (forall x. {body}))"));
        for at in &self.ground_atoms {
            lines.push(format!(
                "(assert {} {} {})",
                at.lhs.dump(),
                at.cmp.symbol(),
                at.rhs.dump()
            ));
        }
        lines.join("\n")
    }

    fn integer_literals(&self) -> BTreeSet<i128> {
        let mut values = BTreeSet::new();
        for atom in self.body_atoms.iter().chain(&self.ground_atoms) {
            atom.lhs.collect_integer_literals(&mut values);
            atom.rhs.collect_integer_literals(&mut values);
        }
        values
    }
}

fn conj(a: &mut TermArena, terms: &[TermId]) -> TermId {
    let mut it = terms.iter().copied();
    let first = it.next().expect("at least one body atom");
    it.fold(first, |acc, t| a.and(acc, t).unwrap())
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Verdict {
    Sat,
    Unsat,
    Unknown,
}

fn label(r: &CheckResult) -> Verdict {
    match r {
        CheckResult::Sat(_) => Verdict::Sat,
        CheckResult::Unsat => Verdict::Unsat,
        CheckResult::Unknown(_) => Verdict::Unknown,
    }
}

/// Independently replay an axeyum `sat`: ground facts must all be `true`, and the
/// universal body must be `true` at every swept concrete `x`. Returns `Some(msg)`
/// on a definite wrong sat, `None` if consistent (or indeterminate).
fn replay_violation(
    arena: &TermArena,
    model: &Model,
    x_sym: SymbolId,
    body: TermId,
    ground: &[TermId],
) -> Option<String> {
    let asg: Assignment = model.to_assignment();
    for (i, &g) in ground.iter().enumerate() {
        if let Ok(Value::Bool(false)) = eval(arena, g, &asg) {
            return Some(format!(
                "ground fact #{i} is FALSE under the returned model"
            ));
        }
    }
    for n in REPLAY_SWEEP {
        let mut probe = asg.clone();
        probe.set(x_sym, Value::Int(n));
        if let Ok(Value::Bool(false)) = eval(arena, body, &probe) {
            return Some(format!(
                "universal body is FALSE at x = {n} under the returned model"
            ));
        }
    }
    None
}

fn z3_decide(inst: &Instance) -> Verdict {
    let solver = Solver::new();
    let mut params = Params::new();
    params.set_u32(
        "timeout",
        u32::try_from(Z3_TIMEOUT.as_millis()).unwrap_or(u32::MAX),
    );
    solver.set_params(&params);
    inst.to_z3(&solver);
    match solver.check() {
        SatResult::Sat => Verdict::Sat,
        SatResult::Unsat => Verdict::Unsat,
        SatResult::Unknown => Verdict::Unknown,
    }
}

fn z3_ground_scalar_model(inst: &Instance) -> Option<Vec<i128>> {
    let solver = Solver::new();
    let mut params = Params::new();
    params.set_u32(
        "timeout",
        u32::try_from(Z3_TIMEOUT.as_millis()).unwrap_or(u32::MAX),
    );
    solver.set_params(&params);
    inst.to_z3(&solver);
    if solver.check() != SatResult::Sat {
        return None;
    }
    let model = solver.get_model()?;
    (0..inst.num_ground)
        .map(|index| {
            model
                .eval(&Int::new_const(format!("y{index}")), true)?
                .as_i64()
                .map(i128::from)
        })
        .collect()
}

#[derive(Default)]
struct OracleTally {
    sat: u64,
    unsat: u64,
    unknown: u64,
    example_seeds: Vec<u64>,
    z3_sat_seeds: Vec<u64>,
}

impl OracleTally {
    fn record(&mut self, verdict: Verdict, seed: u64) {
        match verdict {
            Verdict::Sat => {
                self.sat += 1;
                if self.z3_sat_seeds.len() < 64 {
                    self.z3_sat_seeds.push(seed);
                }
            }
            Verdict::Unsat => self.unsat += 1,
            Verdict::Unknown => self.unknown += 1,
        }
        if self.example_seeds.len() < 8 {
            self.example_seeds.push(seed);
        }
    }

    fn total(&self) -> u64 {
        self.sat + self.unsat + self.unknown
    }
}

#[derive(Default)]
struct Tally {
    total: u64,
    jointly_decided: u64,
    agreements: u64,
    ax_sat: u64,
    ax_unsat: u64,
    ax_unknown: u64,
    ax_error_skipped: u64,
    z3_unknown_skipped: u64,
    sat_replayed: u64,
    ax_unknown_by_reason: BTreeMap<String, OracleTally>,
    ax_error_by_reason: BTreeMap<String, OracleTally>,
}

fn report_and_check_tally(t: &Tally, minimum_jointly_decided: u64) {
    println!("=== quantified-UFLIA model-finder differential fuzz tally ===");
    println!("total instances:      {}", t.total);
    println!("jointly decided:      {}", t.jointly_decided);
    println!("agreements:           {}", t.agreements);
    println!("axeyum Sat:           {}", t.ax_sat);
    println!("axeyum Unsat:         {}", t.ax_unsat);
    println!("axeyum Unknown:       {}", t.ax_unknown);
    println!(
        "axeyum Err (skipped): {} (orthogonal arith_dpll replay-robustness gap; neutral)",
        t.ax_error_skipped
    );
    println!("Z3 Unknown (skipped): {}", t.z3_unknown_skipped);
    println!("Sat replays verified: {}", t.sat_replayed);
    println!("Axeyum Unknown by exact reason and Z3 adjudication:");
    for (reason, oracle) in &t.ax_unknown_by_reason {
        println!(
            "  {reason}: z3_sat={}, z3_unsat={}, z3_unknown={}, example_seeds={:?}, \
             z3_sat_seeds={:?}",
            oracle.sat, oracle.unsat, oracle.unknown, oracle.example_seeds, oracle.z3_sat_seeds
        );
    }
    println!("Axeyum Err by exact reason and Z3 adjudication:");
    for (reason, oracle) in &t.ax_error_by_reason {
        println!(
            "  {reason}: z3_sat={}, z3_unsat={}, z3_unknown={}, example_seeds={:?}, \
             z3_sat_seeds={:?}",
            oracle.sat, oracle.unsat, oracle.unknown, oracle.example_seeds, oracle.z3_sat_seeds
        );
    }
    println!("DISAGREEMENTS:        0");

    assert_eq!(
        t.ax_unknown_by_reason
            .values()
            .map(OracleTally::total)
            .sum::<u64>(),
        t.ax_unknown,
        "every Axeyum Unknown must retain an exact reason and oracle adjudication"
    );
    assert_eq!(
        t.ax_error_by_reason
            .values()
            .map(OracleTally::total)
            .sum::<u64>(),
        t.ax_error_skipped,
        "every Axeyum Err must retain an exact reason and oracle adjudication"
    );
    assert!(
        t.jointly_decided >= minimum_jointly_decided,
        "too few jointly-decided instances ({}); the differential gate is not \
         meaningfully exercised",
        t.jointly_decided
    );
    assert!(
        t.ax_sat > 0,
        "the quantified sat direction was never exercised (ax_sat = 0)"
    );
}

fn run_differential_fuzz(instances: u64, minimum_jointly_decided: u64) {
    let cfg = SolverConfig::new().with_timeout(AXEYUM_TIMEOUT);
    let mut t = Tally::default();

    for seed in 0..instances {
        t.total += 1;
        if seed % 250 == 0 {
            eprintln!(
                "[quant-uflia-mf-fuzz] seed {seed}/{instances} (joint={}, agree={}, \
                 ax_sat={}, ax_unsat={}, ax_unknown={})",
                t.jointly_decided, t.agreements, t.ax_sat, t.ax_unsat, t.ax_unknown
            );
        }
        let mut rng = Lcg::new(seed);
        let inst = Instance::generate(&mut rng);

        let (mut arena, x_sym, _, body, ground, assertions) = inst.build_axeyum();
        let ax_result = prove_unsat_by_mbqi(&mut arena, &assertions, &cfg);
        let z3_label = z3_decide(&inst);
        if z3_label == Verdict::Unknown {
            t.z3_unknown_skipped += 1;
        }

        // A `SolverError` is adjudication-neutral: it is never a sat/unsat
        // verdict, so it can never be a wrong sat/unsat. Retain its exact class
        // and oracle adjudication so an operational gap cannot disappear into
        // one aggregate skip count or be mistaken for MBQI incompleteness.
        let ax = match ax_result {
            Ok(ax) => ax,
            Err(error) => {
                t.ax_error_skipped += 1;
                t.ax_error_by_reason
                    .entry(error.to_string())
                    .or_default()
                    .record(z3_label, seed);
                continue;
            }
        };
        let ax_label = label(&ax);
        match ax_label {
            Verdict::Sat => t.ax_sat += 1,
            Verdict::Unsat => t.ax_unsat += 1,
            Verdict::Unknown => {
                t.ax_unknown += 1;
                let CheckResult::Unknown(reason) = &ax else {
                    unreachable!("unknown label must carry an UnknownReason")
                };
                t.ax_unknown_by_reason
                    .entry(format!("{:?}: {}", reason.kind, reason.detail))
                    .or_default()
                    .record(z3_label, seed);
            }
        }

        // Independent replay of a `sat` model: the model is keyed by this arena's
        // symbol/function ids, so `body`/`ground` replay directly against it.
        if let CheckResult::Sat(model) = &ax {
            assert!(
                check_model(&arena, &assertions, model)
                    .expect("canonical quantified model replay must not error"),
                "WRONG SAT (seed {seed}): canonical check_model rejected the exact source\ninstance:\n{}",
                inst.dump()
            );
            if let Some(why) = replay_violation(&arena, model, x_sym, body, &ground) {
                panic!(
                    "WRONG SAT (seed {seed}): axeyum returned Sat but {why} — a soundness \
                     bug in MBQI model-finding.\ninstance:\n{}",
                    inst.dump()
                );
            }
            t.sat_replayed += 1;
        }

        if z3_label == Verdict::Unknown {
            continue;
        }
        if ax_label == Verdict::Unknown {
            continue;
        }
        t.jointly_decided += 1;
        if ax_label == z3_label {
            t.agreements += 1;
        } else {
            panic!(
                "DISAGREEMENT (seed {seed}): axeyum = {ax_label:?}, Z3 = {z3_label:?} — a {} \
                 soundness bug.\ninstance:\n{}",
                match (ax_label, z3_label) {
                    (Verdict::Sat, Verdict::Unsat) => "WRONG-SAT",
                    (Verdict::Unsat, Verdict::Sat) => "WRONG-UNSAT",
                    _ => "verdict",
                },
                inst.dump()
            );
        }
    }

    report_and_check_tally(&t, minimum_jointly_decided);
}

#[test]
fn quantified_uflia_model_finder_differential_fuzz_disagree_zero() {
    run_differential_fuzz(SMOKE_INSTANCES, 100);
}

#[test]
fn evaluated_scalar_candidates_close_the_two_production_residuals() {
    let cfg = SolverConfig::new().with_timeout(AXEYUM_TIMEOUT);
    for seed in [23_u64, 231] {
        let mut rng = Lcg::new(seed);
        let inst = Instance::generate(&mut rng);
        assert_eq!(z3_decide(&inst), Verdict::Sat, "seed {seed}");
        let (mut arena, _, _, _, _, assertions) = inst.build_axeyum();
        let result = prove_unsat_by_mbqi(&mut arena, &assertions, &cfg).unwrap();
        let CheckResult::Sat(model) = result else {
            panic!("seed {seed} must complete to checked SAT, got {result:?}");
        };
        assert!(check_model(&arena, &assertions, &model).unwrap());
    }
}

#[test]
fn evaluated_scalar_retry_preserves_the_prior_seed_145_sat() {
    let seed = 145_u64;
    let mut rng = Lcg::new(seed);
    let inst = Instance::generate(&mut rng);
    assert_eq!(z3_decide(&inst), Verdict::Sat);
    let (mut arena, _, _, _, _, assertions) = inst.build_axeyum();
    let result = prove_unsat_by_mbqi(
        &mut arena,
        &assertions,
        &SolverConfig::new().with_timeout(AXEYUM_TIMEOUT),
    )
    .unwrap();
    let CheckResult::Sat(model) = result else {
        panic!("the deferred retry must not steal seed 145's prior SAT: {result:?}");
    };
    assert!(check_model(&arena, &assertions, &model).unwrap());
}

#[test]
fn two_binder_cartesian_profiles_agree_with_z3() {
    let cfg = SolverConfig::new().with_timeout(AXEYUM_TIMEOUT);
    let mut ax_sat = 0_u64;
    let mut ax_unsat = 0_u64;

    for seed in 0..64_i64 {
        let threshold = seed.rem_euclid(5) - 2;
        let expect_sat = seed % 2 == 0;
        let point_count = usize::try_from(seed.rem_euclid(3) + 1).unwrap();

        let mut arena = TermArena::new();
        let function = arena
            .declare_fun("f", &[Sort::Int, Sort::Int], Sort::Int)
            .unwrap();
        let x_sym = arena.declare("x", Sort::Int).unwrap();
        let y_sym = arena.declare("y", Sort::Int).unwrap();
        let x = arena.var(x_sym);
        let y = arena.var(y_sym);
        let application = arena.apply(function, &[x, y]).unwrap();
        let lower = arena.int_const(i128::from(threshold));
        let body = arena.int_ge(application, lower).unwrap();
        let inner = arena.forall(y_sym, body).unwrap();
        let forall = arena.forall(x_sym, inner).unwrap();
        let mut assertions = vec![forall];

        let z3_solver = Solver::new();
        let mut params = Params::new();
        params.set_u32(
            "timeout",
            u32::try_from(Z3_TIMEOUT.as_millis()).unwrap_or(u32::MAX),
        );
        z3_solver.set_params(&params);
        let z3_x = Int::new_const("x");
        let z3_y = Int::new_const("y");
        let int_sort = Z3Sort::int();
        let z3_function = FuncDecl::new("f", &[&int_sort, &int_sort], &int_sort);
        let z3_application = z3_function
            .apply(&[&z3_x as &dyn Ast, &z3_y as &dyn Ast])
            .as_int()
            .unwrap();
        let z3_body = z3_application.ge(Int::from_i64(threshold));
        z3_solver.assert(z3::ast::forall_const(
            &[&z3_x as &dyn Ast, &z3_y as &dyn Ast],
            &[],
            &z3_body,
        ));

        for point in 0..point_count {
            let a = seed.rem_euclid(7) + i64::try_from(point).unwrap();
            let b = seed.rem_euclid(11) - i64::try_from(point).unwrap();
            let value = if !expect_sat && point == 0 {
                threshold - 1
            } else {
                threshold + 1 + i64::try_from(point).unwrap()
            };
            let a_term = arena.int_const(i128::from(a));
            let b_term = arena.int_const(i128::from(b));
            let at_point = arena.apply(function, &[a_term, b_term]).unwrap();
            let value_term = arena.int_const(i128::from(value));
            assertions.push(arena.eq(at_point, value_term).unwrap());

            let z3_at_point = z3_function
                .apply(&[&Int::from_i64(a) as &dyn Ast, &Int::from_i64(b) as &dyn Ast])
                .as_int()
                .unwrap();
            z3_solver.assert(z3_at_point.eq(Int::from_i64(value)));
        }

        let axeyum = prove_unsat_by_mbqi(&mut arena, &assertions, &cfg).unwrap();
        let axeyum_verdict = label(&axeyum);
        match &axeyum {
            CheckResult::Sat(model) => {
                ax_sat += 1;
                assert!(check_model(&arena, &assertions, model).unwrap());
            }
            CheckResult::Unsat => ax_unsat += 1,
            CheckResult::Unknown(reason) => {
                panic!("seed {seed} unexpectedly declined: {reason:?}")
            }
        }
        let z3_verdict = match z3_solver.check() {
            SatResult::Sat => Verdict::Sat,
            SatResult::Unsat => Verdict::Unsat,
            SatResult::Unknown => panic!("Z3 unexpectedly declined seed {seed}"),
        };
        assert_eq!(axeyum_verdict, z3_verdict, "seed {seed}");
    }

    assert_eq!(ax_sat, 32);
    assert_eq!(ax_unsat, 32);
}

#[test]
#[ignore = "full 2,000-instance quantified-UFLIA differential campaign"]
fn quantified_uflia_model_finder_differential_fuzz_full() {
    run_differential_fuzz(FULL_INSTANCES, 100);
}

#[test]
#[ignore = "diagnostic; set AXEYUM_QUANT_UFLIA_DIAGNOSTIC_SEEDS to comma-separated seeds"]
fn diagnose_quantified_uflia_model_finder_seeds() {
    let raw = std::env::var("AXEYUM_QUANT_UFLIA_DIAGNOSTIC_SEEDS")
        .expect("set AXEYUM_QUANT_UFLIA_DIAGNOSTIC_SEEDS");
    let cfg = SolverConfig::new().with_timeout(AXEYUM_TIMEOUT);
    for field in raw.split(',') {
        let seed: u64 = field.trim().parse().expect("diagnostic seed must be u64");
        let mut rng = Lcg::new(seed);
        let inst = Instance::generate(&mut rng);
        let (mut arena, _, _, _, _, assertions) = inst.build_axeyum();
        let axeyum =
            prove_unsat_by_mbqi(&mut arena, &assertions, &cfg).map(|result| label(&result));
        println!(
            "=== seed {seed}: Axeyum={axeyum:?}, Z3={:?} ===\n{}",
            z3_decide(&inst),
            inst.dump()
        );
    }
}

#[test]
#[ignore = "diagnostic; set AXEYUM_QUANT_UFLIA_SCALAR_DIAGNOSTIC_SEEDS"]
fn diagnose_z3_scalar_completion_for_quantified_uflia_unknowns() {
    let raw = std::env::var("AXEYUM_QUANT_UFLIA_SCALAR_DIAGNOSTIC_SEEDS")
        .expect("set AXEYUM_QUANT_UFLIA_SCALAR_DIAGNOSTIC_SEEDS");
    let cfg = SolverConfig::new().with_timeout(AXEYUM_TIMEOUT);
    let mut sat = 0_u64;
    let mut unknown = 0_u64;

    for field in raw.split(',') {
        let seed: u64 = field.trim().parse().expect("diagnostic seed must be u64");
        let mut rng = Lcg::new(seed);
        let inst = Instance::generate(&mut rng);
        let Some(values) = z3_ground_scalar_model(&inst) else {
            panic!("seed {seed} must be Z3 SAT for scalar-completion diagnosis");
        };
        let (mut arena, _, y_symbols, _, _, mut assertions) = inst.build_axeyum();
        assert_eq!(y_symbols.len(), values.len());
        for (&symbol, &value) in y_symbols.iter().zip(&values) {
            let variable = arena.var(symbol);
            let constant = arena.int_const(value);
            assertions.push(arena.eq(variable, constant).unwrap());
        }
        let result = prove_unsat_by_mbqi(&mut arena, &assertions, &cfg)
            .expect("scalar-completion diagnostic must not error");
        match &result {
            CheckResult::Sat(model) => {
                sat += 1;
                assert!(check_model(&arena, &assertions, model).unwrap());
            }
            CheckResult::Unknown(_) => unknown += 1,
            CheckResult::Unsat => panic!(
                "seed {seed} became UNSAT under scalar values from a Z3 model; wrong refutation"
            ),
        }
        println!(
            "seed {seed}: z3_scalars={values:?}, Axeyum={:?}",
            label(&result)
        );
    }

    println!("Z3_SCALAR_COMPLETION|sat={sat}|unknown={unknown}");
}

fn push_scalar_candidate(values: &mut Vec<i128>, candidate: i128) {
    if values.len() < 16 && !values.contains(&candidate) {
        values.push(candidate);
    }
}

fn evaluated_int_candidate_pool(
    arena: &TermArena,
    assertions: &[TermId],
    model: &Model,
) -> BTreeSet<i128> {
    let assignment = model.to_assignment();
    let mut values = BTreeSet::from([0]);
    for (_, value) in model.iter() {
        if let Value::Int(integer) = value {
            values.insert(integer);
        }
    }
    for (_, function) in model.functions() {
        if let Value::Int(integer) = function.default_value() {
            values.insert(integer);
        }
        for (_, value) in function.value_entries() {
            if let Value::Int(integer) = value {
                values.insert(*integer);
            }
        }
    }

    let mut seen = BTreeSet::new();
    let mut stack: Vec<TermId> = assertions.iter().rev().copied().collect();
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        if arena.sort_of(term) == Sort::Int
            && let Ok(Value::Int(integer)) = eval(arena, term, &assignment)
        {
            values.insert(integer);
        }
        if let TermNode::App { args, .. } = arena.node(term) {
            stack.extend(args.iter().rev().copied());
        }
    }
    values
}

fn exact_source_symbols(arena: &TermArena, assertions: &[TermId]) -> BTreeSet<SymbolId> {
    let mut symbols = BTreeSet::new();
    let mut seen = BTreeSet::new();
    let mut stack: Vec<TermId> = assertions.iter().rev().copied().collect();
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        match arena.node(term) {
            TermNode::Symbol(symbol) => {
                symbols.insert(*symbol);
            }
            TermNode::App { args, .. } => stack.extend(args.iter().rev().copied()),
            _ => {}
        }
    }
    symbols
}

#[test]
#[ignore = "diagnostic; set AXEYUM_QUANT_UFLIA_SCALAR_DIAGNOSTIC_SEEDS"]
fn diagnose_fixed_query_evaluated_scalar_probe_for_quantified_uflia_unknowns() {
    const MAX_VALUES: usize = 16;
    const MAX_TUPLES: usize = 256;

    let raw = std::env::var("AXEYUM_QUANT_UFLIA_SCALAR_DIAGNOSTIC_SEEDS")
        .expect("set AXEYUM_QUANT_UFLIA_SCALAR_DIAGNOSTIC_SEEDS");
    let cfg = SolverConfig::new().with_timeout(AXEYUM_TIMEOUT);
    let mut sat = 0_u64;
    let mut unknown = 0_u64;
    let mut candidate_checks = 0_u64;

    for field in raw.split(',') {
        let seed: u64 = field.trim().parse().expect("diagnostic seed must be u64");
        let mut rng = Lcg::new(seed);
        let inst = Instance::generate(&mut rng);
        assert_eq!(z3_decide(&inst), Verdict::Sat);

        let (mut ground_arena, _, y_symbols, _, ground, ground_assertions) = inst.build_axeyum();
        let source_symbols = exact_source_symbols(&ground_arena, &ground_assertions);
        let relevant_y_symbols: Vec<SymbolId> = y_symbols
            .into_iter()
            .filter(|symbol| source_symbols.contains(symbol))
            .collect();
        let ground_model = match check_auto(&mut ground_arena, &ground, &cfg) {
            Ok(CheckResult::Sat(model)) => model,
            other => panic!("seed {seed} ground slice must be SAT, got {other:?}"),
        };
        let base_values =
            evaluated_int_candidate_pool(&ground_arena, &ground_assertions, &ground_model);
        let mut candidate_values = base_values.clone();
        for base in base_values.iter().copied() {
            if let Some(predecessor) = base.checked_sub(1) {
                candidate_values.insert(predecessor);
            }
            if let Some(successor) = base.checked_add(1) {
                candidate_values.insert(successor);
            }
        }

        let values: Vec<i128> = candidate_values.iter().copied().collect();
        let tuple_count = values
            .len()
            .checked_pow(u32::try_from(relevant_y_symbols.len()).unwrap())
            .unwrap_or(usize::MAX);
        let mut found = None;
        let deadline = Instant::now() + AXEYUM_TIMEOUT;
        if values.len() <= MAX_VALUES && tuple_count <= MAX_TUPLES {
            'assignments: for tuple_index in 0..tuple_count {
                let Some(remaining) = deadline.checked_duration_since(Instant::now()) else {
                    break;
                };
                let mut remaining_index = tuple_index;
                let mut chosen = vec![0; relevant_y_symbols.len()];
                for slot in (0..chosen.len()).rev() {
                    chosen[slot] = values[remaining_index % values.len()];
                    remaining_index /= values.len();
                }

                candidate_checks += 1;
                let (mut arena, _, candidate_y_symbols, _, _, mut fixed_assertions) =
                    inst.build_axeyum();
                let original_assertions = fixed_assertions.clone();
                let candidate_source_symbols = exact_source_symbols(&arena, &fixed_assertions);
                let candidate_relevant_y_symbols: Vec<SymbolId> = candidate_y_symbols
                    .into_iter()
                    .filter(|symbol| candidate_source_symbols.contains(symbol))
                    .collect();
                assert_eq!(candidate_relevant_y_symbols.len(), chosen.len());
                for (&symbol, &value) in candidate_relevant_y_symbols.iter().zip(&chosen) {
                    let variable = arena.var(symbol);
                    let constant = arena.int_const(value);
                    fixed_assertions.push(arena.eq(variable, constant).unwrap());
                }
                let candidate_cfg = SolverConfig::new().with_timeout(remaining);
                if let CheckResult::Sat(model) =
                    prove_unsat_by_mbqi(&mut arena, &fixed_assertions, &candidate_cfg)
                        .expect("evaluated-source scalar diagnostic must not error")
                    && check_model(&arena, &original_assertions, &model).unwrap()
                {
                    found = Some(chosen);
                    break 'assignments;
                }
            }
        }

        if found.is_some() {
            sat += 1;
        } else {
            unknown += 1;
        }
        println!(
            "seed {seed}: evaluated_base_pool={base_values:?}, neighbor_pool={candidate_values:?}, \
             relevant_symbols={}, tuples={tuple_count}, checked_sat_scalars={found:?}",
            relevant_y_symbols.len()
        );
    }

    println!(
        "FIXED_QUERY_EVALUATED_SCALAR_PROBE|sat={sat}|unknown={unknown}|candidate_checks={candidate_checks}"
    );
}

#[test]
#[ignore = "diagnostic; set AXEYUM_QUANT_UFLIA_SCALAR_DIAGNOSTIC_SEEDS"]
fn diagnose_bounded_source_scalar_completion_for_quantified_uflia_unknowns() {
    let raw = std::env::var("AXEYUM_QUANT_UFLIA_SCALAR_DIAGNOSTIC_SEEDS")
        .expect("set AXEYUM_QUANT_UFLIA_SCALAR_DIAGNOSTIC_SEEDS");
    let cfg = SolverConfig::new().with_timeout(AXEYUM_TIMEOUT);
    let mut sat = 0_u64;
    let mut unknown = 0_u64;
    let mut candidate_checks = 0_u64;

    for field in raw.split(',') {
        let seed: u64 = field.trim().parse().expect("diagnostic seed must be u64");
        let mut rng = Lcg::new(seed);
        let inst = Instance::generate(&mut rng);
        assert_eq!(z3_decide(&inst), Verdict::Sat);

        let (mut ground_arena, _, _, _, ground, _) = inst.build_axeyum();
        let ground_model = match check_auto(&mut ground_arena, &ground, &cfg) {
            Ok(CheckResult::Sat(model)) => model,
            other => panic!("seed {seed} ground slice must be SAT, got {other:?}"),
        };
        let mut candidates = Vec::new();
        push_scalar_candidate(&mut candidates, 0);
        for (_, value) in ground_model.iter() {
            if let Value::Int(integer) = value {
                push_scalar_candidate(&mut candidates, integer);
            }
        }
        for literal in inst.integer_literals() {
            push_scalar_candidate(&mut candidates, literal);
        }
        let bases = candidates.clone();
        for base in bases {
            if let Some(predecessor) = base.checked_sub(1) {
                push_scalar_candidate(&mut candidates, predecessor);
            }
            if let Some(successor) = base.checked_add(1) {
                push_scalar_candidate(&mut candidates, successor);
            }
        }

        let mut found = None;
        'assignments: for &first in &candidates {
            let second_values: &[i128] = if inst.num_ground == 1 {
                &[0]
            } else {
                &candidates
            };
            for &second in second_values {
                candidate_checks += 1;
                let values = [first, second];
                let (mut arena, _, y_symbols, _, _, mut assertions) = inst.build_axeyum();
                for (&symbol, &value) in y_symbols.iter().zip(&values) {
                    let variable = arena.var(symbol);
                    let constant = arena.int_const(value);
                    assertions.push(arena.eq(variable, constant).unwrap());
                }
                if let CheckResult::Sat(model) = prove_unsat_by_mbqi(&mut arena, &assertions, &cfg)
                    .expect("bounded scalar-completion diagnostic must not error")
                {
                    assert!(check_model(&arena, &assertions, &model).unwrap());
                    found = Some(values[..y_symbols.len()].to_vec());
                    break 'assignments;
                }
            }
        }

        if found.is_some() {
            sat += 1;
        } else {
            unknown += 1;
        }
        println!("seed {seed}: source_scalar_pool={candidates:?}, checked_sat_scalars={found:?}");
    }

    println!(
        "BOUNDED_SOURCE_SCALAR_COMPLETION|sat={sat}|unknown={unknown}|candidate_checks={candidate_checks}"
    );
}
