//! Adversarial differential fuzz for **datatype SELECTORS** (`QF_DT`),
//! cross-checked against the Z3 oracle.
//!
//! `qf_dt_differential_fuzz` fuzzes enum datatypes: every constructor is
//! nullary, so it has no selector to apply and **structurally cannot** generate
//! the underspecified case. That is exactly the blindness CLAUDE.md's hard rule
//! names — *"every underspecified operator must have a fuzz generator that
//! deliberately emits the degenerate case"* — and it is why a wrong `unsat`
//! survived in `datatype_native` until 2026-09-12: `sel_{c,i}(t)` for a `t` not
//! built by `c` was pinned to `well_founded_default`, which is a MODEL
//! RESTRICTION, and nothing generated the shape (ADR-1930).
//!
//! This generator emits the degenerate argument on purpose, in both forms:
//!
//! - `sel_{c,0}(v)` over a VARIABLE, where the formula may force `v`'s
//!   constructor to be something other than `c`;
//! - `sel_{c,0}(construct_d(...))` over an explicit CONSTRUCTOR APPLICATION,
//!   both `d == c` (the exact read-over-construct fold) and `d != c` (the
//!   unspecified one).
//!
//! Fields are `Bool`, so a selector read is itself an atom and the whole
//! instance stays finite and fast for both solvers.
//!
//! Soundness contract, identical to the enum fuzz:
//! - axeyum `Sat` and Z3 `Unsat` → **PANIC** (wrong sat).
//! - axeyum `Unsat` and Z3 `Sat` → **PANIC** (wrong unsat — the worst bug).
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

/// `D = a(fa: Bool) | b(fb: Bool) | c`. Two field-carrying constructors so a
/// selector can be read off the *other* one, plus a nullary constructor so the
/// operand can be a value with no fields at all.
const CTOR_NAMES: [&str; 3] = ["a", "b", "c"];
const FIELD_NAMES: [&str; 3] = ["fa", "fb", ""];
/// Which constructors carry a field (index into `CTOR_NAMES`).
const FIELDED: [usize; 2] = [0, 1];
const VAR_NAMES: [&str; 3] = ["v0", "v1", "v2"];

/// The explicit constructor applications an atom may read a selector off.
/// Index 0 is the nullary `c`; the rest are `a(bool)` / `b(bool)`.
const OPERANDS: [(usize, Option<bool>); 5] = [
    (2, None),
    (0, Some(true)),
    (0, Some(false)),
    (1, Some(true)),
    (1, Some(false)),
];

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

#[derive(Clone)]
enum Atom {
    /// `(_ is ctor) v_var`
    Test { var: usize, ctor: usize, neg: bool },
    /// `v_lhs = v_rhs`
    Eq { lhs: usize, rhs: usize, neg: bool },
    /// `sel_{ctor,0}(v_var)` — underspecified whenever `v_var` is not `ctor`.
    SelVar { var: usize, ctor: usize, neg: bool },
    /// `sel_{ctor,0}(construct(...))` — underspecified whenever the operand's
    /// constructor differs from `ctor`, an exact fold when it matches.
    SelCtor {
        operand: usize,
        ctor: usize,
        neg: bool,
    },
    /// `v_var = construct(...)` — forces a variable's constructor and field,
    /// which is what makes a later `SelVar` read land on the *wrong* one.
    EqCtor {
        var: usize,
        operand: usize,
        neg: bool,
    },
}

impl Atom {
    fn generate(rng: &mut Lcg, num_vars: usize) -> Atom {
        let neg = rng.flip();
        match rng.below(5) {
            0 => Atom::Test {
                var: rng.below(num_vars as u64),
                ctor: rng.below(CTOR_NAMES.len() as u64),
                neg,
            },
            1 => Atom::Eq {
                lhs: rng.below(num_vars as u64),
                rhs: rng.below(num_vars as u64),
                neg,
            },
            2 => Atom::SelVar {
                var: rng.below(num_vars as u64),
                ctor: FIELDED[rng.below(FIELDED.len() as u64)],
                neg,
            },
            3 => Atom::SelCtor {
                operand: rng.below(OPERANDS.len() as u64),
                ctor: FIELDED[rng.below(FIELDED.len() as u64)],
                neg,
            },
            _ => Atom::EqCtor {
                var: rng.below(num_vars as u64),
                operand: rng.below(OPERANDS.len() as u64),
                neg,
            },
        }
    }

    fn dump(&self) -> String {
        let render_operand = |o: usize| match OPERANDS[o] {
            (ctor, None) => CTOR_NAMES[ctor].to_owned(),
            (ctor, Some(v)) => format!("{}({v})", CTOR_NAMES[ctor]),
        };
        match self {
            Atom::Test { var, ctor, neg } => format!(
                "{}(_ is {})({})",
                if *neg { "NOT " } else { "" },
                CTOR_NAMES[*ctor],
                VAR_NAMES[*var]
            ),
            Atom::Eq { lhs, rhs, neg } => format!(
                "{} {} {}",
                VAR_NAMES[*lhs],
                if *neg { "!=" } else { "=" },
                VAR_NAMES[*rhs]
            ),
            Atom::SelVar { var, ctor, neg } => format!(
                "{}{}({})",
                if *neg { "NOT " } else { "" },
                FIELD_NAMES[*ctor],
                VAR_NAMES[*var]
            ),
            Atom::SelCtor { operand, ctor, neg } => format!(
                "{}{}({})",
                if *neg { "NOT " } else { "" },
                FIELD_NAMES[*ctor],
                render_operand(*operand)
            ),
            Atom::EqCtor { var, operand, neg } => format!(
                "{} {} {}",
                VAR_NAMES[*var],
                if *neg { "!=" } else { "=" },
                render_operand(*operand)
            ),
        }
    }
}

#[derive(Clone)]
struct Instance {
    num_vars: usize,
    atoms: Vec<Atom>,
    ops: Vec<bool>,
}

impl Instance {
    fn generate(rng: &mut Lcg) -> Instance {
        let num_vars = rng.below(3) + 1; // 1..=3
        let num_atoms = rng.below(4) + 2; // 2..=5
        let atoms = (0..num_atoms)
            .map(|_| Atom::generate(rng, num_vars))
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
        let dt = a.declare_datatype("D");
        let ctors: Vec<_> = (0..CTOR_NAMES.len())
            .map(|i| {
                let fields: Vec<(String, Sort)> = if FIELD_NAMES[i].is_empty() {
                    Vec::new()
                } else {
                    vec![(FIELD_NAMES[i].to_owned(), Sort::Bool)]
                };
                a.add_constructor(dt, CTOR_NAMES[i], &fields)
            })
            .collect();
        let vars: Vec<TermId> = (0..self.num_vars)
            .map(|i| {
                let s = a.declare(VAR_NAMES[i], Sort::Datatype(dt)).unwrap();
                a.var(s)
            })
            .collect();
        let operands: Vec<TermId> = OPERANDS
            .iter()
            .map(|&(ctor, field)| match field {
                None => a.construct(ctors[ctor], &[]).unwrap(),
                Some(v) => {
                    let b = a.bool_const(v);
                    a.construct(ctors[ctor], &[b]).unwrap()
                }
            })
            .collect();

        let bools: Vec<TermId> = self
            .atoms
            .iter()
            .map(|atom| {
                let (term, neg) = match atom {
                    Atom::Test { var, ctor, neg } => {
                        (a.dt_test(ctors[*ctor], vars[*var]).unwrap(), *neg)
                    }
                    Atom::Eq { lhs, rhs, neg } => (a.eq(vars[*lhs], vars[*rhs]).unwrap(), *neg),
                    Atom::SelVar { var, ctor, neg } => {
                        (a.dt_select(ctors[*ctor], 0, vars[*var]).unwrap(), *neg)
                    }
                    Atom::SelCtor { operand, ctor, neg } => (
                        a.dt_select(ctors[*ctor], 0, operands[*operand]).unwrap(),
                        *neg,
                    ),
                    Atom::EqCtor { var, operand, neg } => {
                        (a.eq(vars[*var], operands[*operand]).unwrap(), *neg)
                    }
                };
                if neg { a.not(term).unwrap() } else { term }
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
        let mut builder = DatatypeBuilder::new("D");
        for (i, &name) in CTOR_NAMES.iter().enumerate() {
            builder = if FIELD_NAMES[i].is_empty() {
                builder.variant(name, vec![])
            } else {
                builder.variant(
                    name,
                    vec![(FIELD_NAMES[i], z3::DatatypeAccessor::Sort(z3::Sort::bool()))],
                )
            };
        }
        let sort = builder.finish();
        let vars: Vec<Datatype> = (0..self.num_vars)
            .map(|i| Datatype::new_const(VAR_NAMES[i], &sort.sort))
            .collect();
        let operands: Vec<Datatype> = OPERANDS
            .iter()
            .map(|&(ctor, field)| match field {
                None => sort.variants[ctor]
                    .constructor
                    .apply(&[])
                    .as_datatype()
                    .unwrap(),
                Some(v) => sort.variants[ctor]
                    .constructor
                    .apply(&[&Bool::from_bool(v) as &dyn Ast])
                    .as_datatype()
                    .unwrap(),
            })
            .collect();

        let bools: Vec<Bool> = self
            .atoms
            .iter()
            .map(|atom| {
                let (term, neg) = match atom {
                    Atom::Test { var, ctor, neg } => (
                        sort.variants[*ctor]
                            .tester
                            .apply(&[&vars[*var] as &dyn Ast])
                            .as_bool()
                            .unwrap(),
                        *neg,
                    ),
                    Atom::Eq { lhs, rhs, neg } => (vars[*lhs].eq(&vars[*rhs]), *neg),
                    Atom::SelVar { var, ctor, neg } => (
                        sort.variants[*ctor].accessors[0]
                            .apply(&[&vars[*var] as &dyn Ast])
                            .as_bool()
                            .unwrap(),
                        *neg,
                    ),
                    Atom::SelCtor { operand, ctor, neg } => (
                        sort.variants[*ctor].accessors[0]
                            .apply(&[&operands[*operand] as &dyn Ast])
                            .as_bool()
                            .unwrap(),
                        *neg,
                    ),
                    Atom::EqCtor { var, operand, neg } => {
                        (vars[*var].eq(&operands[*operand]), *neg)
                    }
                };
                if neg { term.not() } else { term }
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
            "D = a(fa: Bool) | b(fb: Bool) | c, vars {}",
            VAR_NAMES[..self.num_vars].join(", ")
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
fn qf_dt_selector_differential_fuzz_disagree_zero() {
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
        "qf_dt selector fuzz: {INSTANCES} instances | {agree} agree | {ax_unknown} axeyum-unknown | {z3_unknown} z3-unknown(skipped) | 0 DISAGREE"
    );
    // The BOUND is the point: this generator exists to emit the underspecified
    // selector case, so a run in which axeyum declines almost everything would
    // report "0 DISAGREE" while checking nothing. Before ADR-1930 the whole
    // `SelCtor` family was refused outright.
    assert!(
        agree >= INSTANCES / 2,
        "expected >= {} agreements, got {agree} (axeyum-unknown {ax_unknown}) — selector reasoning regressed to declining",
        INSTANCES / 2
    );
}
