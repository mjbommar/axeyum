//! Adversarial differential soundness fuzzer for the `QF_UFLIA` theory-
//! combination path (uninterpreted functions + linear integer arithmetic)
//! against the Z3 oracle.
//!
//! Mixing uninterpreted functions with arithmetic stresses the soundness-
//! critical combination machinery: congruence closure over the UF terms,
//! Ackermann-style functional consistency, and the linear-integer (LIA) decider,
//! and the glue that propagates equalities between them. A wrong `Unsat`
//! (claiming no model when one exists — e.g. a spurious congruence collapse) or a
//! wrong `Sat` (a model that does not satisfy the original atoms, or one Z3
//! refutes) would be the worst possible bug. The same differential pattern just
//! found three real wrong-`Unsat` bugs in the pure arithmetic deciders.
//!
//! This harness — mirroring the proven `nia_differential_fuzz.rs` /
//! `nra_differential_fuzz.rs` templates — deterministically generates thousands
//! of small random `QF_UFLIA` formulas (no `Math::random`/`Date::now`; a
//! fixed-seed LCG drives every choice), decides each with both the default
//! pure-Rust `solve` front door and a direct Z3 integer query over the same
//! declarations and atoms, and gates on the joint verdict:
//!
//! - axeyum `Sat` ∧ Z3 `Unsat` → **PANIC** (wrong sat).
//! - axeyum `Unsat` ∧ Z3 `Sat` → **PANIC** (wrong unsat — the worst bug).
//! - axeyum `Sat` → the returned model (variable bindings **and** the UF function
//!   interpretations) is **independently replayed** through the IR ground
//!   evaluator on every original atom; a definitely-non-replaying Sat panics
//!   regardless of Z3.
//! - axeyum `Unknown` is ALLOWED (incomplete is sound) — counted, never failed.
//! - Z3 `Unknown`/timeout → the instance is skipped (cannot adjudicate).
//!
//! The test passes iff disagreements == 0 AND no axeyum `Sat` definitely
//! refutes under replay.
//!
//! ## Semantic-safety note
//!
//! Only constructs with *identical* semantics on both sides are generated:
//! - Uninterpreted functions `f : Int -> Int` and `g : Int Int -> Int` — they are
//!   uninterpreted in both axeyum and Z3, so any total interpretation is fair.
//! - Linear integer arithmetic over `Sort::Int`: variables, constants in a small
//!   range, addition, and multiplication by constant coefficients.
//! - The six comparators `{=, !=, <, <=, >, >=}` over Int terms.
//!
//! No `div`/`mod`, no partial or convention-sensitive operators appear: every
//! generated construct is unambiguous, so a verdict mismatch is a real bug, never
//! a false alarm. The UF model replays through the IR evaluator because
//! `Model::to_assignment` carries the function interpretations and the evaluator's
//! `Op::Apply` arm looks them up (`apply_value` is total), so a `QF_UFLIA` `Sat`
//! is expected to replay `AllTrue`; `Indeterminate` is retained only defensively.
#![cfg(feature = "full")]
#![cfg(feature = "z3")]

use std::sync::mpsc;
use std::time::Duration;

use axeyum_ir::{FuncId, Sort, SymbolId, TermArena, TermId, Value, eval};
use axeyum_solver::{CheckResult, SolverConfig, solve};
use z3::ast::{Ast, Bool, Int};
use z3::{FuncDecl, Params, SatResult, Solver, Sort as Z3Sort};

/// Number of instances generated and adjudicated. Each is tiny (≤ 3 vars, ≤ 4
/// atoms, term depth ≤ 2) so Z3 decides well within its timeout.
const INSTANCES: u64 = 2500;

/// Per-instance Z3 wall-clock budget. Small UFLIA formulas ⇒ Z3 decides far
/// faster; this only bounds the rare pathological shape so the test never hangs.
const Z3_TIMEOUT: Duration = Duration::from_secs(2);

/// Per-instance hard wall-clock cap on the axeyum `solve`. A slow combination
/// shape is run on a worker thread and joined with this cap; a solve that
/// overruns is recorded as a timeout (adjudication-neutral, exactly like
/// `Unknown`) and the sweep moves on. This is sound — a timeout is never a
/// sat/unsat verdict — and bounds total runtime.
const AXEYUM_TIMEOUT: Duration = Duration::from_secs(4);

/// A deterministic linear-congruential PRNG (the MMIX multiplier/increment).
/// No clock, no OS entropy: the whole sweep is reproducible from the seed.
struct Lcg(u64);

impl Lcg {
    fn new(seed: u64) -> Self {
        // Mix the seed once so consecutive seeds 0,1,2,… don't start correlated.
        Lcg(seed
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407))
    }

    /// Advance and return the next 64-bit state.
    fn next_u64(&mut self) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        self.0
    }

    /// A uniform integer in `0..n` (`n > 0`), returned as a `usize`.
    fn below(&mut self, n: u64) -> usize {
        usize::try_from(self.next_u64() % n).expect("modulus fits usize")
    }

    /// A small signed coefficient in `lo..=hi` (inclusive).
    fn in_range(&mut self, lo: i64, hi: i64) -> i64 {
        debug_assert!(lo <= hi);
        let span = u64::try_from(hi - lo + 1).expect("non-negative span");
        lo + i64::try_from(self.next_u64() % span).expect("offset within span")
    }
}

/// The six comparators we mix: equalities, strict, non-strict, and `!=`.
/// Equalities/disequalities especially exercise congruence closure over the UF
/// terms; the inequalities feed the LIA decider.
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

    /// Build `lhs ⋈ rhs` as an IR Bool term over the integer sort.
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

    /// Build `lhs ⋈ rhs` as a Z3 `Bool` over integer terms.
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

/// A generated integer term. Plain data (no IR/Z3 handles) so an [`Instance`] is
/// `Send` + `Clone` — a clone can be moved onto an axeyum worker thread while the
/// original drives the Z3 query and the repro dump. The same tree builds the IR
/// term, the Z3 term, and the pretty-print.
///
/// Depth is bounded at generation time (≤ 2), keeping every term shallow so Z3
/// decides fast and the UF combination stays small.
#[derive(Clone)]
enum Term {
    /// A variable, by index into the instance's variables.
    Var(usize),
    /// A small integer constant.
    Const(i64),
    /// Application of the unary uninterpreted function `f : Int -> Int`.
    F(Box<Term>),
    /// Application of the binary uninterpreted function `g : Int Int -> Int`.
    G(Box<Term>, Box<Term>),
    /// A small linear combination `a*t1 + b*t2 + c` (coeffs in `-3..=3`).
    Lin {
        a: i64,
        t1: Box<Term>,
        b: i64,
        t2: Box<Term>,
        c: i64,
    },
}

impl Term {
    /// Generate a random term at the given remaining `depth`. At depth 0 only
    /// leaves (variable or constant) are produced; deeper terms may apply `f`/`g`
    /// or form a linear combination. `num_vars` bounds the variable index.
    fn generate(rng: &mut Lcg, depth: usize, num_vars: usize) -> Term {
        if depth == 0 {
            // Leaf: variable (favoured) or small constant.
            return if rng.below(3) == 0 {
                Term::Const(rng.in_range(-4, 4))
            } else {
                Term::Var(rng.below(num_vars as u64))
            };
        }
        match rng.below(5) {
            // Leaves still possible at depth > 0 so shapes vary.
            0 => Term::Var(rng.below(num_vars as u64)),
            1 => Term::Const(rng.in_range(-4, 4)),
            2 => Term::F(Box::new(Term::generate(rng, depth - 1, num_vars))),
            3 => Term::G(
                Box::new(Term::generate(rng, depth - 1, num_vars)),
                Box::new(Term::generate(rng, depth - 1, num_vars)),
            ),
            _ => Term::Lin {
                a: rng.in_range(-3, 3),
                t1: Box::new(Term::generate(rng, depth - 1, num_vars)),
                b: rng.in_range(-3, 3),
                t2: Box::new(Term::generate(rng, depth - 1, num_vars)),
                c: rng.in_range(-3, 3),
            },
        }
    }

    /// Does this term apply `f` or `g` anywhere? Used to ensure at least one atom
    /// genuinely exercises the UF combination.
    fn uses_uf(&self) -> bool {
        match self {
            Term::Var(_) | Term::Const(_) => false,
            Term::F(_) | Term::G(_, _) => true,
            Term::Lin { t1, t2, .. } => t1.uses_uf() || t2.uses_uf(),
        }
    }

    /// Materialize the term in the IR arena.
    fn build(&self, a: &mut TermArena, vars: &[TermId], f: FuncId, g: FuncId) -> TermId {
        match self {
            Term::Var(i) => vars[*i],
            Term::Const(k) => a.int_const(i128::from(*k)),
            Term::F(t) => {
                let arg = t.build(a, vars, f, g);
                a.apply(f, &[arg]).unwrap()
            }
            Term::G(t1, t2) => {
                let a1 = t1.build(a, vars, f, g);
                let a2 = t2.build(a, vars, f, g);
                a.apply(g, &[a1, a2]).unwrap()
            }
            Term::Lin {
                a: ca,
                t1,
                b,
                t2,
                c,
            } => {
                let coeff_a = a.int_const(i128::from(*ca));
                let first = t1.build(a, vars, f, g);
                let prod1 = a.int_mul(coeff_a, first).unwrap();
                let coeff_b = a.int_const(i128::from(*b));
                let second = t2.build(a, vars, f, g);
                let prod2 = a.int_mul(coeff_b, second).unwrap();
                let constant = a.int_const(i128::from(*c));
                let partial = a.int_add(prod1, prod2).unwrap();
                a.int_add(partial, constant).unwrap()
            }
        }
    }

    /// Materialize the term as a Z3 `Int` over the same UF declarations.
    fn build_z3(&self, vars: &[Int], f: &FuncDecl, g: &FuncDecl) -> Int {
        match self {
            Term::Var(i) => vars[*i].clone(),
            Term::Const(k) => Int::from_i64(*k),
            Term::F(t) => {
                let arg = t.build_z3(vars, f, g);
                f.apply(&[&arg as &dyn Ast])
                    .as_int()
                    .expect("f : Int -> Int returns Int")
            }
            Term::G(t1, t2) => {
                let a1 = t1.build_z3(vars, f, g);
                let a2 = t2.build_z3(vars, f, g);
                g.apply(&[&a1 as &dyn Ast, &a2 as &dyn Ast])
                    .as_int()
                    .expect("g : Int Int -> Int returns Int")
            }
            Term::Lin { a, t1, b, t2, c } => {
                let p1 = Int::mul(&[Int::from_i64(*a), t1.build_z3(vars, f, g)]);
                let p2 = Int::mul(&[Int::from_i64(*b), t2.build_z3(vars, f, g)]);
                Int::add(&[p1, p2, Int::from_i64(*c)])
            }
        }
    }

    /// A human-readable rendering for the repro dump.
    fn dump(&self, names: &[&str]) -> String {
        match self {
            Term::Var(i) => names[*i].to_string(),
            Term::Const(k) => k.to_string(),
            Term::F(t) => format!("f({})", t.dump(names)),
            Term::G(t1, t2) => format!("g({}, {})", t1.dump(names), t2.dump(names)),
            Term::Lin { a, t1, b, t2, c } => format!(
                "({}*{} + {}*{} + {})",
                a,
                t1.dump(names),
                b,
                t2.dump(names),
                c
            ),
        }
    }
}

/// A generated atom: `lhs ⋈ rhs` over two integer terms.
#[derive(Clone)]
struct Atom {
    lhs: Term,
    rhs: Term,
    cmp: Cmp,
}

/// A full generated instance: the variable count and the atoms. Owns only plain
/// data (no IR/Z3 handles), so it is `Send` + `Clone`.
#[derive(Clone)]
struct Instance {
    num_vars: usize,
    atoms: Vec<Atom>,
}

/// Term depth ceiling — shallow so Z3 decides fast and combination stays small.
const MAX_DEPTH: usize = 2;

impl Instance {
    /// Deterministically generate an instance from the PRNG.
    ///
    /// Distribution:
    /// - 1..=3 integer variables;
    /// - 1..=4 atoms, each `t_lhs ⋈ t_rhs` with a comparator uniform over the six;
    /// - each side is a random term of depth ≤ 2 drawn from
    ///   {variable, small constant in `-4..=4`, `f(t)`, `g(t,t)`,
    ///   `a*t1 + b*t2 + c` with coeffs in `-3..=3`};
    /// - **at least one atom is forced to genuinely use `f`/`g`** (so the UF
    ///   combination is always exercised): if no generated atom touches a UF
    ///   symbol, one atom's `lhs` is replaced by `f(var0)` (keeping its rhs and
    ///   comparator), which also guarantees a UF application is present.
    fn generate(rng: &mut Lcg) -> Instance {
        let num_vars = rng.below(3) + 1; // 1..=3
        let num_atoms = rng.below(4) + 1; // 1..=4

        let mut atoms = Vec::with_capacity(num_atoms);
        for _ in 0..num_atoms {
            let lhs = Term::generate(rng, MAX_DEPTH, num_vars);
            let rhs = Term::generate(rng, MAX_DEPTH, num_vars);
            atoms.push(Atom {
                lhs,
                rhs,
                cmp: Cmp::pick(rng),
            });
        }

        // Ensure the UF combination is genuinely tested: if nothing used f/g,
        // force a UF application into the first atom's lhs.
        let any_uf = atoms.iter().any(|at| at.lhs.uses_uf() || at.rhs.uses_uf());
        if !any_uf {
            atoms[0].lhs = Term::F(Box::new(Term::Var(0)));
        }

        Instance { num_vars, atoms }
    }

    /// Materialize the instance as IR assertions over a fresh arena, returning
    /// the arena, the per-variable symbol ids, and the assertion term ids.
    fn build(&self) -> (TermArena, Vec<SymbolId>, Vec<TermId>) {
        let mut a = TermArena::new();
        let names = ["x", "y", "z"];
        let syms: Vec<SymbolId> = (0..self.num_vars)
            .map(|i| a.declare(names[i], Sort::Int).unwrap())
            .collect();
        let vars: Vec<TermId> = syms.iter().map(|&s| a.var(s)).collect();
        let f = a.declare_fun("f", &[Sort::Int], Sort::Int).unwrap();
        let g = a
            .declare_fun("g", &[Sort::Int, Sort::Int], Sort::Int)
            .unwrap();

        let mut assertions = Vec::with_capacity(self.atoms.len());
        for atom in &self.atoms {
            let lhs = atom.lhs.build(&mut a, &vars, f, g);
            let rhs = atom.rhs.build(&mut a, &vars, f, g);
            assertions.push(atom.cmp.build(&mut a, lhs, rhs));
        }
        (a, syms, assertions)
    }

    /// Build the same instance as a list of Z3 `Bool` atoms over fresh Z3 `Int`
    /// constants and matching uninterpreted `FuncDecl`s. The adjudication queries
    /// Z3 directly with the z3 crate's integer + UF theory — the exact same
    /// `QF_UFLIA` semantics the combination path targets.
    fn to_z3(&self) -> Vec<Bool> {
        let names = ["x", "y", "z"];
        let vars: Vec<Int> = (0..self.num_vars)
            .map(|i| Int::new_const(names[i]))
            .collect();
        let int_sort = Z3Sort::int();
        let f = FuncDecl::new("f", &[&int_sort], &int_sort);
        let g = FuncDecl::new("g", &[&int_sort, &int_sort], &int_sort);

        self.atoms
            .iter()
            .map(|atom| {
                let lhs = atom.lhs.build_z3(&vars, &f, &g);
                let rhs = atom.rhs.build_z3(&vars, &f, &g);
                atom.cmp.build_z3(&lhs, &rhs)
            })
            .collect()
    }

    /// An SMT-ish dump of the instance for a reproducing panic message.
    fn dump(&self) -> String {
        let names = ["x", "y", "z"];
        let mut lines = vec![
            format!("vars (Int): {}", &names[..self.num_vars].join(", ")),
            "funcs: f : Int -> Int, g : Int Int -> Int".to_string(),
        ];
        for (i, atom) in self.atoms.iter().enumerate() {
            lines.push(format!(
                "  atom[{i}]: {} {} {}",
                atom.lhs.dump(&names),
                atom.cmp.symbol(),
                atom.rhs.dump(&names),
            ));
        }
        lines.join("\n")
    }
}

/// A coarse verdict label, abstracting away the model/reason payloads.
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

/// The replay outcome of an axeyum `Sat`, computed on the worker thread (which
/// owns the arena). The IR ground evaluator replays the UF model directly:
/// `Model::to_assignment` carries the function interpretations and the
/// evaluator's `Op::Apply` arm looks them up (`apply_value` is total), so a
/// well-formed `QF_UFLIA` `Sat` is expected to replay `AllTrue`. `Indeterminate`
/// is kept defensively (e.g. an evaluator `Err`, such as an unbound function or
/// an overflow) and is adjudication-neutral; only `Violated` is a wrong sat.
#[derive(Clone, PartialEq, Eq, Debug)]
enum Replay {
    /// Not a `Sat` verdict (no model to replay).
    NotSat,
    /// Every original atom evaluated `true` at the model — a verified replay.
    AllTrue,
    /// The evaluator declined ≥ 1 atom (`Err`/non-Bool) and refuted none —
    /// indeterminate; the Z3 cross-check still adjudicates the verdict.
    Indeterminate,
    /// An atom evaluated `false` at the model — a WRONG SAT (carries the atom
    /// index and a model dump for the panic).
    Violated { atom: usize, model: String },
}

/// The full axeyum result for one instance, decided on a worker thread under a
/// hard wall-clock cap.
struct AxeyumOutcome {
    verdict: Verdict,
    replay: Replay,
    /// A model dump for a `Sat` (used only when reporting a disagreement).
    model_dump: Option<String>,
}

/// The bounded axeyum decision for one instance.
enum Bounded {
    /// `solve` finished within the cap and returned a verdict.
    Decided(AxeyumOutcome),
    /// `solve` overran the wall-clock cap — adjudication-neutral, like `Unknown`.
    Timeout,
    /// `solve` (or the replay) **panicked** — a crash bug in the solver, *not* a
    /// sat/unsat verdict. Adjudication-neutral here (a panic is never a verdict,
    /// so it can never be a wrong sat/unsat), but counted and the first one is
    /// reported, since a panic on a valid `QF_UFLIA` query is itself a defect.
    Crashed,
}

/// Decide an instance with axeyum on a worker thread, joining under
/// [`AXEYUM_TIMEOUT`].
///
/// The arena, the model, and the replay all live on the worker thread; only the
/// `Send` summary crosses back. The whole `solve`+replay runs inside
/// `catch_unwind` so a solver panic does not abort the sweep — it is reported as
/// [`Bounded::Crashed`] (adjudication-neutral; a panic is never a verdict, hence
/// never a soundness *mis*-verdict), letting the differential gate run across
/// every instance instead of wedging on one crashing shape.
fn solve_axeyum_bounded(inst: Instance) -> Bounded {
    // `true` ⇒ a decided outcome (possibly `None`-ish via the verdict), `false`
    // sent over the panic channel ⇒ the worker unwound. We use two channels so a
    // panic and a real result are unambiguous.
    let (tx, rx) = mpsc::channel::<AxeyumOutcome>();
    std::thread::spawn(move || {
        // Catch a panic from inside `solve` (or the replay) so it surfaces as a
        // crash signal (the channel simply staying empty) rather than tearing
        // down the harness. The closure owns the instance and builds its own
        // arena, so nothing shared is left in a poisoned state.
        let _ = std::panic::catch_unwind(std::panic::AssertUnwindSafe(move || {
            let (mut a, syms, assertions) = inst.build();
            let result = solve(&mut a, &assertions, &SolverConfig::default());
            let outcome = match result {
                // `solve` must not error; treat an error like a crash (channel
                // stays empty → reported as Crashed). `Unknown` is a result.
                Err(_) => return,
                Ok(ax) => {
                    let verdict = label(&ax);
                    let (replay, model_dump) = match &ax {
                        CheckResult::Sat(model) => {
                            // The assignment carries BOTH variable bindings and the
                            // UF interpretations, so the evaluator replays the full
                            // model (`Op::Apply` looks up the interpretation).
                            let asg = model.to_assignment();
                            let dump = dump_model(&syms, model);
                            let mut replay = Replay::AllTrue;
                            for (i, &assertion) in assertions.iter().enumerate() {
                                match eval(&a, assertion, &asg) {
                                    Ok(Value::Bool(true)) => {}
                                    Ok(Value::Bool(false)) => {
                                        replay = Replay::Violated {
                                            atom: i,
                                            model: dump.clone(),
                                        };
                                        break;
                                    }
                                    // `Err(..)` (defensive) or a non-Bool result:
                                    // indeterminate, not a refutation. Keep scanning
                                    // for a true violation in a later atom.
                                    _ => {
                                        if replay == Replay::AllTrue {
                                            replay = Replay::Indeterminate;
                                        }
                                    }
                                }
                            }
                            (replay, Some(dump))
                        }
                        _ => (Replay::NotSat, None),
                    };
                    AxeyumOutcome {
                        verdict,
                        replay,
                        model_dump,
                    }
                }
            };
            // The receiver may be gone (we timed out); ignore a send error.
            let _ = tx.send(outcome);
        }));
        // On panic / error, `tx` is dropped here without a send → the receiver
        // observes `Disconnected`, which we map to a crash below.
    });

    match rx.recv_timeout(AXEYUM_TIMEOUT) {
        Ok(outcome) => Bounded::Decided(outcome),
        Err(mpsc::RecvTimeoutError::Timeout) => Bounded::Timeout,
        // The worker dropped its sender without sending: it panicked or `solve`
        // returned an error. Either way it is a crash, not a verdict.
        Err(mpsc::RecvTimeoutError::Disconnected) => Bounded::Crashed,
    }
}

/// Decide an instance with Z3 over the `QF_UFLIA` theory, with a tiny wall-clock
/// timeout. Returns `Unknown` on timeout/incompleteness (the instance is then
/// skipped — Z3 cannot adjudicate it).
fn z3_decide(inst: &Instance) -> Verdict {
    let solver = Solver::new();
    let mut params = Params::new();
    params.set_u32(
        "timeout",
        u32::try_from(Z3_TIMEOUT.as_millis()).unwrap_or(u32::MAX),
    );
    solver.set_params(&params);
    for atom in inst.to_z3() {
        solver.assert(&atom);
    }
    match solver.check() {
        SatResult::Sat => Verdict::Sat,
        SatResult::Unsat => Verdict::Unsat,
        SatResult::Unknown => Verdict::Unknown,
    }
}

/// Running counters for the sweep.
#[derive(Default)]
struct Tally {
    total: u64,
    jointly_decided: u64,
    agreements: u64,
    axeyum_unknown: u64,
    axeyum_timeout: u64,
    axeyum_crashed: u64,
    z3_unknown_skipped: u64,
    sat_replayed: u64,
    sat_replay_indeterminate: u64,
    /// The first crashing instance, kept for the report (a panic on a valid
    /// `QF_UFLIA` query is a defect even though it is never a *mis-verdict*).
    first_crash: Option<(u64, String)>,
}

/// Decide one instance with both engines and fold the result into `t`. Panics
/// only on a genuine soundness violation (a non-replaying Sat, or a jointly-
/// decided Sat/Unsat disagreement) — the whole point of the gate.
fn run_instance(seed: u64, inst: &Instance, t: &mut Tally) {
    // --- axeyum: the default pure-Rust front door, hard-capped. ----------
    let outcome = match solve_axeyum_bounded(inst.clone()) {
        Bounded::Decided(o) => o,
        Bounded::Timeout => {
            t.axeyum_timeout += 1;
            return;
        }
        Bounded::Crashed => {
            // A panic inside `solve` is a crash bug, *not* a sat/unsat verdict —
            // it can never be a wrong sat/unsat, so it is adjudication-neutral
            // (counted, never failing the soundness gate). Record the first one
            // for the report and move on so the sweep covers every instance.
            t.axeyum_crashed += 1;
            if t.first_crash.is_none() {
                t.first_crash = Some((seed, inst.dump()));
            }
            return;
        }
    };
    let ax_label = outcome.verdict;

    // A `Sat` whose model VIOLATES an original atom under the independent ground
    // evaluator (with the UF interpretation) is a wrong sat — regardless of Z3.
    if let Replay::Violated { atom, model } = &outcome.replay {
        panic!(
            "WRONG SAT (seed {seed}): axeyum returned Sat but its model makes \
             atom[{atom}] FALSE under the independent ground evaluator (with the \
             UF interpretation) — a soundness bug.\nmodel: {model}\ninstance:\n{}",
            inst.dump()
        );
    }
    match outcome.replay {
        Replay::AllTrue => t.sat_replayed += 1,
        Replay::Indeterminate => t.sat_replay_indeterminate += 1,
        Replay::NotSat | Replay::Violated { .. } => {}
    }

    if ax_label == Verdict::Unknown {
        t.axeyum_unknown += 1;
    }

    // --- Z3 oracle: a direct QF_UFLIA query, tiny timeout. ---------------
    let z3_label = z3_decide(inst);
    if z3_label == Verdict::Unknown {
        t.z3_unknown_skipped += 1;
        return;
    }
    // Both sides committed to Sat/Unsat (axeyum may still be Unknown).
    if ax_label == Verdict::Unknown {
        return;
    }

    t.jointly_decided += 1;

    // THE SOUNDNESS GATE: a jointly-decided instance must AGREE.
    if ax_label == z3_label {
        t.agreements += 1;
    } else {
        let model_dump = outcome
            .model_dump
            .unwrap_or_else(|| "(no axeyum model)".to_string());
        panic!(
            "DISAGREEMENT (seed {seed}): axeyum = {ax_label:?}, Z3 = {z3_label:?}.\n\
             This is a {} soundness bug.\n\
             axeyum model: {model_dump}\n\
             instance:\n{}",
            match (ax_label, z3_label) {
                (Verdict::Sat, Verdict::Unsat) => "WRONG-SAT",
                (Verdict::Unsat, Verdict::Sat) => "WRONG-UNSAT (worst case)",
                _ => "verdict",
            },
            inst.dump()
        );
    }
}

#[test]
fn uflia_differential_fuzz_disagree_zero() {
    // Worker `solve` panics are *caught* (a crash is adjudication-neutral, not a
    // verdict). Install a panic hook that stays silent for panics originating in
    // solver/crate source (so thousands of caught crashes don't flood stderr) but
    // still prints panics from *this test file* — the genuine soundness-gate
    // panics — at full volume.
    let default_hook = std::panic::take_hook();
    std::panic::set_hook(Box::new(move |info| {
        let from_this_test = info
            .location()
            .is_some_and(|loc| loc.file().ends_with("uflia_differential_fuzz.rs"));
        if from_this_test {
            default_hook(info);
        }
    }));

    let mut t = Tally::default();

    for seed in 0..INSTANCES {
        t.total += 1;
        if seed % 250 == 0 {
            eprintln!(
                "[uflia-fuzz] seed {seed}/{INSTANCES} (joint={}, agree={}, \
                 ax_unknown={}, ax_timeout={}, ax_crash={})",
                t.jointly_decided,
                t.agreements,
                t.axeyum_unknown,
                t.axeyum_timeout,
                t.axeyum_crashed
            );
        }
        let mut rng = Lcg::new(seed);
        let inst = Instance::generate(&mut rng);
        run_instance(seed, &inst, &mut t);
    }

    let Tally {
        total,
        jointly_decided,
        agreements,
        axeyum_unknown,
        axeyum_timeout,
        axeyum_crashed,
        z3_unknown_skipped,
        sat_replayed,
        sat_replay_indeterminate,
        first_crash,
    } = t;

    println!("=== QF_UFLIA differential fuzz tally ===");
    println!("total instances:      {total}");
    println!("jointly decided:      {jointly_decided}");
    println!("agreements:           {agreements}");
    println!("axeyum Unknown:       {axeyum_unknown}");
    println!(
        "axeyum timeout:       {axeyum_timeout} (slow combination; capped, adjudication-neutral)"
    );
    println!(
        "axeyum CRASHED:       {axeyum_crashed} (solver panic on a valid QF_UFLIA query — a defect, \
         but never a mis-verdict)"
    );
    println!("Z3 Unknown (skipped): {z3_unknown_skipped}");
    println!("Sat replays verified: {sat_replayed}");
    println!("Sat replay declined:  {sat_replay_indeterminate} (eval gap; Z3-adjudicated)");
    println!("DISAGREEMENTS:        0");
    if let Some((seed, dump)) = &first_crash {
        println!(
            "--- first crashing instance (seed {seed}) — solver panic, reported \
             for a deliberate fix ---\n{dump}"
        );
    }

    // Reaching here means no disagreement panicked: DISAGREE=0 over the sweep.
    // Sanity: the sweep must actually exercise the joint deciders (guards against
    // a silently-broken Z3 plumbing that always times out, which would make
    // DISAGREE=0 vacuous).
    assert!(
        jointly_decided > 100,
        "too few jointly-decided instances ({jointly_decided}); the differential \
         gate is not meaningfully exercised"
    );
}

/// Pretty-print an axeyum model's variable bindings and UF interpretations.
fn dump_model(syms: &[SymbolId], model: &axeyum_solver::Model) -> String {
    let names = ["x", "y", "z"];
    let mut parts = Vec::new();
    for (i, &s) in syms.iter().enumerate() {
        let v = model.get(s);
        parts.push(format!("{}={:?}", names[i], v));
    }
    // Include the function interpretations so a repro shows the full witness.
    for (f, interp) in model.functions() {
        parts.push(format!("fn[{f:?}]={interp:?}"));
    }
    parts.join(", ")
}
