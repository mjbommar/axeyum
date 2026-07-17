//! Adversarial differential fuzz for **enum datatypes** (`QF_DT`), cross-checked
//! against the Z3 oracle.
//!
//! Datatypes are `Validated` in the capability ledger (native expansion +
//! elimination + model replay) and have hand-authored corpus seeds, but were not
//! adversarially fuzzed. This gate stresses the finite-enum datatype reasoning:
//! one datatype with `k` nullary constructors, a few datatype-sorted variables,
//! and atoms that are either a **tester** `(_ is c_i) v_j` or a **variable
//! equality** `v_i = v_j` (optionally negated), folded into a Boolean formula by
//! `and`/`or`. So the reasoning under test is exactly-one-constructor-per-value,
//! distinctness of constructors, and equality/congruence over the enum — the
//! datatype theory's core.
//!
//! Soundness contract:
//! - axeyum `Sat`  ∧ Z3 `Unsat` → **PANIC** (wrong sat).
//! - axeyum `Unsat` ∧ Z3 `Sat`  → **PANIC** (wrong unsat — the worst bug).
//! - axeyum `Unknown` → fine; Z3 `Unknown`/timeout → skip.
#![cfg(feature = "full")]
#![cfg(feature = "z3")]

use std::sync::mpsc;
use std::time::Duration;

use axeyum_ir::{Sort, TermArena, TermId};
use axeyum_solver::{CheckResult, SolverConfig, solve};
use z3::ast::{Ast, Bool, Datatype};
use z3::{DatatypeBuilder, Params, SatResult, Solver};

const INSTANCES: u64 = 1500;
const AXEYUM_TIMEOUT: Duration = Duration::from_secs(3);
const Z3_TIMEOUT: Duration = Duration::from_secs(2);
/// Static constructor / variable names (enough for the generated bounds).
const CTORS: [&str; 4] = ["c0", "c1", "c2", "c3"];
const VARS: [&str; 3] = ["v0", "v1", "v2"];

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

/// `(_ is c_ctor) v_var` (a tester) or `v_lhs = v_rhs` (a variable equality).
#[derive(Clone)]
enum Atom {
    Test { var: usize, ctor: usize, neg: bool },
    Eq { lhs: usize, rhs: usize, neg: bool },
}

impl Atom {
    fn generate(rng: &mut Lcg, num_ctors: usize, num_vars: usize) -> Atom {
        if rng.flip() {
            Atom::Test {
                var: rng.below(num_vars as u64),
                ctor: rng.below(num_ctors as u64),
                neg: rng.flip(),
            }
        } else {
            Atom::Eq {
                lhs: rng.below(num_vars as u64),
                rhs: rng.below(num_vars as u64),
                neg: rng.flip(),
            }
        }
    }
    fn dump(&self) -> String {
        match self {
            Atom::Test { var, ctor, neg } => {
                let n = if *neg { "NOT " } else { "" };
                format!("{n}(_ is {})({})", CTORS[*ctor], VARS[*var])
            }
            Atom::Eq { lhs, rhs, neg } => {
                let op = if *neg { "!=" } else { "=" };
                format!("{} {op} {}", VARS[*lhs], VARS[*rhs])
            }
        }
    }
}

#[derive(Clone)]
struct Instance {
    num_ctors: usize,
    num_vars: usize,
    atoms: Vec<Atom>,
    ops: Vec<bool>,
}

impl Instance {
    fn generate(rng: &mut Lcg) -> Instance {
        let num_ctors = rng.below(3) + 2; // 2..=4
        let num_vars = rng.below(2) + 2; // 2..=3
        let num_atoms = rng.below(4) + 2; // 2..=5
        let atoms = (0..num_atoms)
            .map(|_| Atom::generate(rng, num_ctors, num_vars))
            .collect();
        let ops = (0..num_atoms - 1).map(|_| rng.flip()).collect();
        Instance {
            num_ctors,
            num_vars,
            atoms,
            ops,
        }
    }

    fn build(&self) -> (TermArena, Vec<TermId>) {
        let mut a = TermArena::new();
        let dt = a.declare_datatype("Enum");
        let ctors: Vec<_> = (0..self.num_ctors)
            .map(|i| a.add_constructor(dt, CTORS[i], &[]))
            .collect();
        let vars: Vec<TermId> = (0..self.num_vars)
            .map(|i| {
                let s = a.declare(VARS[i], Sort::Datatype(dt)).unwrap();
                a.var(s)
            })
            .collect();

        let bools: Vec<TermId> = self
            .atoms
            .iter()
            .map(|atom| match atom {
                Atom::Test { var, ctor, neg } => {
                    let t = a.dt_test(ctors[*ctor], vars[*var]).unwrap();
                    if *neg { a.not(t).unwrap() } else { t }
                }
                Atom::Eq { lhs, rhs, neg } => {
                    let e = a.eq(vars[*lhs], vars[*rhs]).unwrap();
                    if *neg { a.not(e).unwrap() } else { e }
                }
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
        let mut builder = DatatypeBuilder::new("Enum");
        for &name in CTORS.iter().take(self.num_ctors) {
            builder = builder.variant(name, vec![]);
        }
        let sort = builder.finish();
        let vars: Vec<Datatype> = (0..self.num_vars)
            .map(|i| Datatype::new_const(VARS[i], &sort.sort))
            .collect();

        let bools: Vec<Bool> = self
            .atoms
            .iter()
            .map(|atom| match atom {
                Atom::Test { var, ctor, neg } => {
                    let t = sort.variants[*ctor]
                        .tester
                        .apply(&[&vars[*var] as &dyn Ast])
                        .as_bool()
                        .unwrap();
                    if *neg { t.not() } else { t }
                }
                Atom::Eq { lhs, rhs, neg } => {
                    let e = vars[*lhs].eq(&vars[*rhs]);
                    if *neg { e.not() } else { e }
                }
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
            "enum Enum with {} ctors, vars {}",
            self.num_ctors,
            VARS[..self.num_vars].join(", ")
        )];
        for (i, atom) in self.atoms.iter().enumerate() {
            lines.push(format!("  atom[{i}]: {}", atom.dump()));
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
fn qf_dt_differential_fuzz_disagree_zero() {
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
        "qf_dt fuzz: {INSTANCES} instances | {agree} agree | {ax_unknown} axeyum-unknown | {z3_unknown} z3-unknown(skipped) | 0 DISAGREE"
    );
    assert!(
        agree >= INSTANCES / 2,
        "expected >= {} agreements, got {agree} (axeyum-unknown {ax_unknown}) — datatype dispatch regression?",
        INSTANCES / 2
    );
}
