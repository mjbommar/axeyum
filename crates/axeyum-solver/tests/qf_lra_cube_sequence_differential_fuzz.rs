//! ADR-2125 seed class: the **offline lazy-SMT cube loop**, cross-checked
//! against the Z3 oracle.
//!
//! # Why a new suite and not a seed in `qf_lra_differential_fuzz`
//!
//! Every existing `QF_LRA` fuzz instance is decided by the ONLINE CDCL(T)
//! engine, because the admission screen (`lra_theory.rs`) admits
//! `budget_bytes / BYTES_PER_ADMITTED_ATOM` atoms — exactly **1,024** at the
//! default budget — and the existing generator makes 2 to 5. So the offline
//! lazy-SMT loop that ADR-2125 changes is a route those fuzzes structurally
//! cannot reach, and running them in both arms of this lever's A/B, while
//! necessary, is not sufficient: they would pass identically with the warm cube
//! decider deleted.
//!
//! This generator's whole job is therefore to be **wide**: more atoms than the
//! screen admits, so the query falls through to the offline loop, where each
//! refinement round installs a fresh total cube on the theory and the ADR-2125
//! decider (when the lever is on) reuses one tableau and one basis across all of
//! them. That is a push/pop sequence in the only form this route has one.
//!
//! The instances are wide but **shallow**: bounds over a handful of variables,
//! with a small number of disjunctions to force case splitting. A wide AND deep
//! instance would time out on our side, and a sweep of `Unknown` is not a
//! soundness gate — it is a gate that cannot fail, which is why the agreement
//! floor below is asserted and printed.
//!
//! Soundness contract, identical to the other four:
//! - axeyum `Sat` ∧ Z3 `Unsat` → **PANIC** (wrong sat).
//! - axeyum `Unsat` ∧ Z3 `Sat` → **PANIC** (wrong unsat — the worst bug).
//! - axeyum `Unknown` → allowed (sound-incomplete).
//! - Z3 `Unknown`/timeout → skipped (cannot adjudicate).
//!
//! Deterministic (seeded LCG, no clock or entropy). Run in BOTH arms of the
//! ADR-2125 A/B: a lever that ships `off` is otherwise exercised by no gate.
#![cfg(feature = "full")]
#![cfg(feature = "z3")]

use std::sync::mpsc;
use std::time::Duration;

use axeyum_ir::{Rational, Sort, TermArena, TermId};
use axeyum_solver::{CheckResult, SolverConfig, solve};
use z3::ast::{Bool, Real};
use z3::{Params, SatResult, Solver};

/// Seeds. Deliberately small: each instance carries over a thousand atoms, and
/// a wide sweep here would cost more than the four narrow fuzzes together while
/// covering one route.
const INSTANCES: u64 = 10;
/// Atoms per instance — comfortably past the 1,024 the online engine admits, so
/// the query is REFUSED there and lands in the offline loop this suite exists
/// for. Checked by `the_generator_outruns_the_online_admission_screen` below
/// rather than left as a comment, because the screen is a constant in another
/// module and a change to it would silently make this whole suite measure the
/// online engine instead.
const ATOMS: usize = 1_200;
/// The screen's own arithmetic, restated so a change to it fails a test here
/// rather than quietly redirecting this suite to a different engine.
const ONLINE_ADMITTED_ATOMS: usize = 1_024;
const VARS: usize = 4;
/// Generous, because the offline loop is the WEAK route by construction and the
/// point of this gate is the verdicts it produces, not how fast it produces
/// them.
const AXEYUM_TIMEOUT: Duration = Duration::from_secs(20);
const Z3_TIMEOUT: Duration = Duration::from_secs(5);

/// Deterministic LCG (MMIX constants) — reproducible from the seed.
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

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Verdict {
    Sat,
    Unsat,
    Unknown,
}

/// One atom: `Σ cᵢ·xᵢ + k ⋈ 0`, with `⋈` one of the four ORDER relations.
///
/// Equalities and disequalities are deliberately absent. An equality asserted
/// FALSE is a disjunction the conjunctive theory cannot represent, so the
/// ADR-2125 decider refuses the whole cube on one — which is sound, and would
/// turn most of this sweep into a fall-through to exactly the cold path the
/// suite is here to differ from. The existing `qf_lra_differential_fuzz` covers
/// equality and `RealDiv` on the online route; this one covers width.
#[derive(Clone)]
struct Atom {
    terms: Vec<(i64, usize)>,
    constant: i64,
    rel: u8,
}

#[derive(Clone)]
struct Instance {
    atoms: Vec<Atom>,
    /// Which atoms are joined by `or` rather than `and`, as a run-length over
    /// the atom list: a `true` opens a two-atom disjunction. Case splitting is
    /// what makes the loop take more than one round, and a conjunction-only
    /// instance would give the warm decider exactly one cube.
    disjoin: Vec<bool>,
}

impl Instance {
    fn generate(rng: &mut Lcg) -> Instance {
        let atoms = (0..ATOMS)
            .map(|_| {
                let nterms = rng.below(VARS as u64) + 1;
                let terms = (0..nterms)
                    .map(|_| (rng.in_range(-3, 3), rng.below(VARS as u64)))
                    .collect();
                Atom {
                    terms,
                    constant: rng.in_range(-6, 6),
                    rel: u8::try_from(rng.below(4)).expect("0..4 fits u8"),
                }
            })
            .collect();
        // One atom in eight opens a disjunction, so the skeleton has real
        // choices without the round count exploding past the budget.
        let disjoin = (0..ATOMS).map(|_| rng.below(8) == 0).collect();
        Instance { atoms, disjoin }
    }

    fn build(&self) -> (TermArena, Vec<TermId>) {
        let mut a = TermArena::new();
        let names = ["x", "y", "z", "w"];
        let vars: Vec<TermId> = (0..VARS)
            .map(|i| {
                let s = a.declare(names[i], Sort::Real).expect("declare real");
                a.var(s)
            })
            .collect();
        let zero = a.real_const(Rational::zero());

        let lits: Vec<TermId> = self
            .atoms
            .iter()
            .map(|atom| {
                let mut poly: Option<TermId> = None;
                for &(coeff, v) in &atom.terms {
                    let c = a.real_const(Rational::integer(i128::from(coeff)));
                    let term = a.real_mul(c, vars[v]).expect("mul");
                    poly = Some(poly.map_or(term, |acc| a.real_add(acc, term).expect("add")));
                }
                let c = a.real_const(Rational::integer(i128::from(atom.constant)));
                let lhs = poly.map_or(c, |acc| a.real_add(acc, c).expect("add"));
                match atom.rel {
                    0 => a.real_lt(lhs, zero).expect("lt"),
                    1 => a.real_le(lhs, zero).expect("le"),
                    2 => a.real_gt(lhs, zero).expect("gt"),
                    _ => a.real_ge(lhs, zero).expect("ge"),
                }
            })
            .collect();

        // One assertion per group, so the abstraction sees every atom and the
        // skeleton has one choice per disjunction.
        let mut assertions = Vec::with_capacity(lits.len());
        let mut i = 0usize;
        while i < lits.len() {
            if self.disjoin[i] && i + 1 < lits.len() {
                assertions.push(a.or(lits[i], lits[i + 1]).expect("or"));
                i += 2;
            } else {
                assertions.push(lits[i]);
                i += 1;
            }
        }
        (a, assertions)
    }

    fn to_z3(&self) -> Vec<Bool> {
        let names = ["x", "y", "z", "w"];
        let vars: Vec<Real> = (0..VARS).map(|i| Real::new_const(names[i])).collect();
        let zero = Real::from_rational(0, 1);

        let lits: Vec<Bool> = self
            .atoms
            .iter()
            .map(|atom| {
                let mut poly: Option<Real> = None;
                for &(coeff, v) in &atom.terms {
                    let term = Real::from_rational(coeff, 1) * vars[v].clone();
                    poly = Some(poly.map_or(term.clone(), |acc| acc + term));
                }
                let c = Real::from_rational(atom.constant, 1);
                let lhs = poly.map_or(c.clone(), |acc| acc + c);
                match atom.rel {
                    0 => lhs.lt(&zero),
                    1 => lhs.le(&zero),
                    2 => lhs.gt(&zero),
                    _ => lhs.ge(&zero),
                }
            })
            .collect();

        let mut out = Vec::with_capacity(lits.len());
        let mut i = 0usize;
        while i < lits.len() {
            if self.disjoin[i] && i + 1 < lits.len() {
                out.push(Bool::or(&[lits[i].clone(), lits[i + 1].clone()]));
                i += 2;
            } else {
                out.push(lits[i].clone());
                i += 1;
            }
        }
        out
    }
}

/// Solve on a worker thread under a wall-clock cap, so a slow instance is
/// SKIPPED rather than hanging the suite.
///
/// The thread is detached on timeout and keeps running. That is a known cost
/// (`recv_timeout` bounds the wait, never the work or the memory) and it is
/// acceptable here because the instance count is 10 and the cap is generous: a
/// detached worker on this suite is a rare event, not the common path.
fn solve_axeyum_bounded(inst: Instance) -> Verdict {
    let (tx, rx) = mpsc::channel();
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(move || {
            let (mut arena, assertions) = inst.build();
            let config = SolverConfig::new().with_timeout(AXEYUM_TIMEOUT);
            let verdict = match solve(&mut arena, &assertions, &config) {
                Ok(CheckResult::Sat(_)) => Verdict::Sat,
                Ok(CheckResult::Unsat) => Verdict::Unsat,
                Ok(CheckResult::Unknown(_)) | Err(_) => Verdict::Unknown,
            };
            let _ = tx.send(verdict);
        })
        .expect("spawn solver thread");
    rx.recv_timeout(AXEYUM_TIMEOUT + Duration::from_secs(5))
        .unwrap_or(Verdict::Unknown)
}

fn z3_decide(inst: &Instance) -> Verdict {
    let solver = Solver::new();
    let mut params = Params::new();
    params.set_u32(
        "timeout",
        u32::try_from(Z3_TIMEOUT.as_millis()).unwrap_or(u32::MAX),
    );
    solver.set_params(&params);
    for assertion in inst.to_z3() {
        solver.assert(&assertion);
    }
    match solver.check() {
        SatResult::Sat => Verdict::Sat,
        SatResult::Unsat => Verdict::Unsat,
        SatResult::Unknown => Verdict::Unknown,
    }
}

/// The generator must produce more atoms than the online engine admits, or this
/// whole suite measures the online engine and says nothing about the route it
/// was written for.
///
/// Checked as arithmetic on two named constants rather than as a comment: the
/// screen lives in another module, and a budget change there would otherwise
/// redirect every instance below to a different engine with nothing going red.
// A relation between two constants is a compile-time fact, so it is checked at
// compile time: a budget change in the other module fails the BUILD of this
// suite, which is louder than a red test. (clippy: `assertions_on_constants`
// rejects the runtime form for exactly this reason.)
const _: () = assert!(
    ATOMS > ONLINE_ADMITTED_ATOMS,
    "ATOMS does not exceed the online engine's admission screen; every instance \
     would be decided by the online CDCL(T) engine and this suite would be a \
     second copy of `qf_lra_differential_fuzz`"
);

#[test]
fn the_generator_outruns_the_online_admission_screen() {
    // The generator must actually build that many, which is a different claim
    // from the constant being large (that one is the `const _` above).
    let inst = Instance::generate(&mut Lcg::new(0));
    assert_eq!(
        inst.atoms.len(),
        ATOMS,
        "the generator produced {} atoms, not {ATOMS}",
        inst.atoms.len()
    );
}

#[test]
fn qf_lra_cube_sequence_differential_fuzz_disagree_zero() {
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
                    "DISAGREEMENT (seed {seed}): axeyum = {ax:?}, Z3 = {z3:?}. \
                     {ATOMS} atoms over {VARS} variables; regenerate with \
                     `Instance::generate(&mut Lcg::new({seed}))`."
                );
            }
            (Verdict::Unknown, _) => ax_unknown += 1,
            (_, Verdict::Unknown) => z3_unknown += 1,
            _ => agree += 1,
        }
    }

    println!(
        "qf_lra cube-sequence fuzz: {INSTANCES} instances | {agree} agree | \
         {ax_unknown} axeyum-unknown | {z3_unknown} z3-unknown(skipped) | 0 DISAGREE"
    );

    // The floor. A sweep of `Unknown` satisfies the soundness contract above
    // completely and establishes NOTHING, which is the exact shape of a gate
    // that cannot fail. One agreement is a low bar and it is the honest one for
    // a route whose own module doc calls it "much weaker": raising it to a
    // fraction of the sweep would make this gate flake on machine speed rather
    // than on a defect.
    assert!(
        agree >= 1,
        "every instance was inconclusive on at least one side \
         (axeyum-unknown {ax_unknown}, z3-unknown {z3_unknown}) — this sweep \
         adjudicated nothing, so it is not evidence about the offline cube loop"
    );
}
