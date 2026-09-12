//! Adversarial differential fuzz for **structural equality over a datatype that
//! has a datatype-typed field** (`QF_DT`), cross-checked against the Z3 oracle.
//!
//! The other two `QF_DT` fuzzes cannot reach this case: the enum fuzz has no
//! fields at all, and the selector fuzz gives every constructor a `Bool` field,
//! so every constructor is exactly comparable. A field whose sort is itself a
//! datatype has NO expansion variable in `datatype_native`'s tag/field reduction,
//! which is where the second wrong `unsat` lived (ADR-1930): the encoded
//! equality skipped such fields, making it weaker than real equality — and
//! weaker in a POSITIVE occurrence is **stronger** under a negation.
//! `is-b(x) AND is-b(y) AND x != y` then demanded a tag difference the testers
//! forbade and answered `unsat`, where two `b` values carrying different
//! payloads plainly exist.
//!
//! `D = a(fa: Bool) | b(fb: E) | c` over `E = e0 | e1`, so `b` is the inexact
//! constructor and `a`/`c` are exact. Atoms deliberately mix:
//!
//! - `x = y` and its negation over `D` — the shape above;
//! - a tester on `x`, so the formula can force both sides onto `b`;
//! - a read of the datatype-typed field, `is-e0(fb(x))`, so the payloads are
//!   constrained as well as compared;
//! - `x = a(bool)` / `x = c`, which pin a value exactly.
//!
//! Soundness contract, as in the sibling fuzzes:
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

const VAR_NAMES: [&str; 3] = ["v0", "v1", "v2"];
/// `D`'s constructors: `a` carries a `Bool`, `b` carries an `E`, `c` is nullary.
const D_CTORS: [&str; 3] = ["a", "b", "c"];
const E_CTORS: [&str; 2] = ["e0", "e1"];

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
    /// `(_ is D_CTORS[ctor]) v_var`
    Test { var: usize, ctor: usize, neg: bool },
    /// `v_lhs = v_rhs` — the shape this suite exists for.
    Eq { lhs: usize, rhs: usize, neg: bool },
    /// `fa(v_var)` — `a`'s `Bool` payload, read off whatever `v_var` is.
    ReadBool { var: usize, neg: bool },
    /// `(_ is E_CTORS[ctor]) (fb v_var)` — a read of the DATATYPE-typed payload.
    ReadPayload { var: usize, ctor: usize, neg: bool },
    /// `v_var = a(value)`, pinning a value exactly.
    PinA { var: usize, value: bool, neg: bool },
    /// `v_var = c`, pinning the nullary constructor.
    PinC { var: usize, neg: bool },
    /// `is_ctor(lhs) AND is_ctor(rhs) AND lhs != rhs` as ONE atom.
    ///
    /// The DEGENERATE ARGUMENT, emitted deliberately (CLAUDE.md's rule for an
    /// underspecified operator). This is the precondition for the wrong `unsat`
    /// the suite exists to cover: both sides forced onto the same constructor,
    /// and required to differ in a field the tag/field expansion cannot see.
    /// Leaving it to the random connective does not work -- measured, the
    /// restored mutant survived all 1500 seeds without this arm, because a
    /// disjunction is satisfiable as soon as one disjunct is and the shape needs
    /// three conjuncts to line up at once.
    SameCtorDiffer { lhs: usize, rhs: usize, ctor: usize },
}

impl Atom {
    fn generate(rng: &mut Lcg, num_vars: usize) -> Atom {
        let neg = rng.flip();
        match rng.below(7) {
            0 => Atom::Test {
                var: rng.below(num_vars as u64),
                ctor: rng.below(D_CTORS.len() as u64),
                neg,
            },
            1 | 2 => Atom::Eq {
                lhs: rng.below(num_vars as u64),
                rhs: rng.below(num_vars as u64),
                neg,
            },
            3 => Atom::ReadBool {
                var: rng.below(num_vars as u64),
                neg,
            },
            4 => Atom::ReadPayload {
                var: rng.below(num_vars as u64),
                ctor: rng.below(E_CTORS.len() as u64),
                neg,
            },
            5 => Atom::SameCtorDiffer {
                lhs: rng.below(num_vars as u64),
                rhs: rng.below(num_vars as u64),
                ctor: rng.below(D_CTORS.len() as u64),
            },
            _ => {
                if rng.flip() {
                    Atom::PinA {
                        var: rng.below(num_vars as u64),
                        value: rng.flip(),
                        neg,
                    }
                } else {
                    Atom::PinC {
                        var: rng.below(num_vars as u64),
                        neg,
                    }
                }
            }
        }
    }

    fn dump(&self) -> String {
        let n = |neg: &bool| if *neg { "NOT " } else { "" };
        match self {
            Atom::Test { var, ctor, neg } => {
                format!("{}(_ is {})({})", n(neg), D_CTORS[*ctor], VAR_NAMES[*var])
            }
            Atom::Eq { lhs, rhs, neg } => format!(
                "{} {} {}",
                VAR_NAMES[*lhs],
                if *neg { "!=" } else { "=" },
                VAR_NAMES[*rhs]
            ),
            Atom::ReadBool { var, neg } => format!("{}fa({})", n(neg), VAR_NAMES[*var]),
            Atom::ReadPayload { var, ctor, neg } => format!(
                "{}(_ is {})(fb({}))",
                n(neg),
                E_CTORS[*ctor],
                VAR_NAMES[*var]
            ),
            Atom::PinA { var, value, neg } => format!(
                "{} {} a({value})",
                VAR_NAMES[*var],
                if *neg { "!=" } else { "=" }
            ),
            Atom::PinC { var, neg } => {
                format!("{} {} c", VAR_NAMES[*var], if *neg { "!=" } else { "=" })
            }
            Atom::SameCtorDiffer { lhs, rhs, ctor } => format!(
                "(_ is {})({}) AND (_ is {})({}) AND {} != {}",
                D_CTORS[*ctor],
                VAR_NAMES[*lhs],
                D_CTORS[*ctor],
                VAR_NAMES[*rhs],
                VAR_NAMES[*lhs],
                VAR_NAMES[*rhs]
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
        // Biased 3:1 toward `and`. A disjunction is satisfiable as soon as ONE
        // disjunct is, so an unbiased connective spends most instances on
        // formulas that never force two variables onto the same constructor --
        // which is the precondition for the shape this suite exists to cover.
        // Measured: unbiased, the restored wrong-`unsat` mutant survived all
        // 1500 seeds; biased, it dies.
        let ops = (0..num_atoms - 1).map(|_| rng.below(4) != 0).collect();
        Instance {
            num_vars,
            atoms,
            ops,
        }
    }

    fn build(&self) -> (TermArena, Vec<TermId>) {
        let mut a = TermArena::new();
        let e_sort = a.declare_datatype("E");
        let e_ctors: Vec<_> = E_CTORS
            .iter()
            .map(|name| a.add_constructor(e_sort, name, &[]))
            .collect();
        let d_sort = a.declare_datatype("D");
        let ctor_a = a.add_constructor(d_sort, "a", &[("fa".into(), Sort::Bool)]);
        let ctor_b = a.add_constructor(d_sort, "b", &[("fb".into(), Sort::Datatype(e_sort))]);
        let ctor_c = a.add_constructor(d_sort, "c", &[]);
        let d_ctors = [ctor_a, ctor_b, ctor_c];

        let vars: Vec<TermId> = (0..self.num_vars)
            .map(|i| {
                let s = a.declare(VAR_NAMES[i], Sort::Datatype(d_sort)).unwrap();
                a.var(s)
            })
            .collect();

        let bools: Vec<TermId> = self
            .atoms
            .iter()
            .map(|atom| {
                let (term, neg) = match atom {
                    Atom::Test { var, ctor, neg } => {
                        (a.dt_test(d_ctors[*ctor], vars[*var]).unwrap(), *neg)
                    }
                    Atom::Eq { lhs, rhs, neg } => (a.eq(vars[*lhs], vars[*rhs]).unwrap(), *neg),
                    Atom::ReadBool { var, neg } => {
                        (a.dt_select(ctor_a, 0, vars[*var]).unwrap(), *neg)
                    }
                    Atom::ReadPayload { var, ctor, neg } => {
                        let payload = a.dt_select(ctor_b, 0, vars[*var]).unwrap();
                        (a.dt_test(e_ctors[*ctor], payload).unwrap(), *neg)
                    }
                    Atom::PinA { var, value, neg } => {
                        let b = a.bool_const(*value);
                        let built = a.construct(ctor_a, &[b]).unwrap();
                        (a.eq(vars[*var], built).unwrap(), *neg)
                    }
                    Atom::PinC { var, neg } => {
                        let built = a.construct(ctor_c, &[]).unwrap();
                        (a.eq(vars[*var], built).unwrap(), *neg)
                    }
                    Atom::SameCtorDiffer { lhs, rhs, ctor } => {
                        let l = a.dt_test(d_ctors[*ctor], vars[*lhs]).unwrap();
                        let r = a.dt_test(d_ctors[*ctor], vars[*rhs]).unwrap();
                        let same = a.eq(vars[*lhs], vars[*rhs]).unwrap();
                        let differ = a.not(same).unwrap();
                        let both = a.and(l, r).unwrap();
                        (a.and(both, differ).unwrap(), false)
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
        let mut e_builder = DatatypeBuilder::new("E");
        for &name in &E_CTORS {
            e_builder = e_builder.variant(name, vec![]);
        }
        let e = e_builder.finish();
        let d = DatatypeBuilder::new("D")
            .variant(
                "a",
                vec![("fa", z3::DatatypeAccessor::Sort(z3::Sort::bool()))],
            )
            .variant(
                "b",
                vec![("fb", z3::DatatypeAccessor::Sort(e.sort.clone()))],
            )
            .variant("c", vec![])
            .finish();

        let vars: Vec<Datatype> = (0..self.num_vars)
            .map(|i| Datatype::new_const(VAR_NAMES[i], &d.sort))
            .collect();

        let bools: Vec<Bool> = self
            .atoms
            .iter()
            .map(|atom| {
                let (term, neg) = match atom {
                    Atom::Test { var, ctor, neg } => (
                        d.variants[*ctor]
                            .tester
                            .apply(&[&vars[*var] as &dyn Ast])
                            .as_bool()
                            .unwrap(),
                        *neg,
                    ),
                    Atom::Eq { lhs, rhs, neg } => (vars[*lhs].eq(&vars[*rhs]), *neg),
                    Atom::ReadBool { var, neg } => (
                        d.variants[0].accessors[0]
                            .apply(&[&vars[*var] as &dyn Ast])
                            .as_bool()
                            .unwrap(),
                        *neg,
                    ),
                    Atom::ReadPayload { var, ctor, neg } => {
                        let payload = d.variants[1].accessors[0]
                            .apply(&[&vars[*var] as &dyn Ast])
                            .as_datatype()
                            .unwrap();
                        (
                            e.variants[*ctor]
                                .tester
                                .apply(&[&payload as &dyn Ast])
                                .as_bool()
                                .unwrap(),
                            *neg,
                        )
                    }
                    Atom::PinA { var, value, neg } => {
                        let built = d.variants[0]
                            .constructor
                            .apply(&[&Bool::from_bool(*value) as &dyn Ast])
                            .as_datatype()
                            .unwrap();
                        (vars[*var].eq(&built), *neg)
                    }
                    Atom::PinC { var, neg } => {
                        let built = d.variants[2].constructor.apply(&[]).as_datatype().unwrap();
                        (vars[*var].eq(&built), *neg)
                    }
                    Atom::SameCtorDiffer { lhs, rhs, ctor } => {
                        let l = d.variants[*ctor]
                            .tester
                            .apply(&[&vars[*lhs] as &dyn Ast])
                            .as_bool()
                            .unwrap();
                        let r = d.variants[*ctor]
                            .tester
                            .apply(&[&vars[*rhs] as &dyn Ast])
                            .as_bool()
                            .unwrap();
                        let differ = vars[*lhs].eq(&vars[*rhs]).not();
                        (Bool::and(&[l, r, differ]), false)
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
            "D = a(fa: Bool) | b(fb: E) | c over E = e0 | e1, vars {}",
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
fn qf_dt_equality_differential_fuzz_disagree_zero() {
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
        "qf_dt equality fuzz: {INSTANCES} instances | {agree} agree | {ax_unknown} axeyum-unknown | {z3_unknown} z3-unknown(skipped) | 0 DISAGREE"
    );
    // The BOUND is part of the assertion: the inexact-equality fragment is
    // exactly where declining everything would report "0 DISAGREE" while
    // checking nothing.
    assert!(
        agree >= INSTANCES / 2,
        "expected >= {} agreements, got {agree} (axeyum-unknown {ax_unknown}) — equality over a datatype-typed field regressed to declining",
        INSTANCES / 2
    );
}
