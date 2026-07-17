//! Adversarial differential soundness fuzzer for the **P1.9 · T1.9.2 simplex
//! fallback** in [`axeyum_solver::check_with_lra`] against the Z3 oracle.
//!
//! The plain `qf_lra_differential_fuzz` uses small (2–4 variable) systems that
//! Fourier–Motzkin decides directly, so it never reaches the new fallback. This
//! harness instead generates **large, dense, conjunctive** `QF_LRA` systems
//! (10–14 variables, 20–34 atoms) whose Fourier–Motzkin elimination blows past its
//! `MAX_FM_CONSTRAINTS` budget → `TimedOut` → the exact-rational **simplex** decides
//! them. A wrong `sat`/`unsat` from that path — the worst possible bug — would be
//! caught here as a disagreement with Z3.
//!
//! Deterministic (seeded LCG, no clock/entropy); each axeyum solve runs on a worker
//! thread under a hard wall-clock cap so a pathological shape is treated as
//! `unknown`, never allowed to wedge the sweep.
#![cfg(feature = "full")]
#![cfg(feature = "z3")]

use std::sync::mpsc;
use std::time::Duration;

use axeyum_ir::{Rational, Sort, TermArena, TermId, Value, eval};
use axeyum_solver::{CheckResult, check_with_lra};
use z3::ast::{Bool, Real};
use z3::{Params, SatResult, Solver};

const INSTANCES: u64 = 1200;
const Z3_TIMEOUT: Duration = Duration::from_secs(2);
const AXEYUM_TIMEOUT: Duration = Duration::from_secs(5);

/// Deterministic LCG (the MMIX constants); no clock, no OS entropy.
struct Lcg(u64);
impl Lcg {
    fn new(seed: u64) -> Self {
        Lcg(seed
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407))
    }
    fn next(&mut self) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        self.0
    }
    fn below(&mut self, n: u64) -> usize {
        usize::try_from(self.next() % n).expect("fits usize")
    }
    fn in_range(&mut self, lo: i64, hi: i64) -> i64 {
        let span = u64::try_from(hi - lo + 1).expect("non-negative span");
        lo + i64::try_from(self.next() % span).expect("within span")
    }
}

#[derive(Clone, Copy)]
enum Cmp {
    Le,
    Lt,
    Ge,
    Gt,
    Eq,
}
impl Cmp {
    fn pick(rng: &mut Lcg) -> Cmp {
        match rng.below(5) {
            0 => Cmp::Le,
            1 => Cmp::Lt,
            2 => Cmp::Ge,
            3 => Cmp::Gt,
            _ => Cmp::Eq,
        }
    }
}

/// One atom `Σ coeff_i · x_i + constant ⋈ 0`.
#[derive(Clone)]
struct Atom {
    terms: Vec<(i64, usize)>,
    constant: i64,
    cmp: Cmp,
}

/// A conjunctive instance (every atom asserted together — the exact shape
/// `check_with_lra` consumes). Plain data → `Send`.
#[derive(Clone)]
struct Instance {
    num_vars: usize,
    atoms: Vec<Atom>,
}

impl Instance {
    fn generate(rng: &mut Lcg) -> Instance {
        let num_vars = rng.below(5) + 10; // 10..=14
        let num_atoms = rng.below(15) + 20; // 20..=34
        let mut atoms = Vec::with_capacity(num_atoms);
        for _ in 0..num_atoms {
            // Dense atoms (about half the variables) so FM elimination explodes.
            let nterms = rng.below((num_vars / 2) as u64) + num_vars / 3 + 1;
            let mut terms = Vec::with_capacity(nterms);
            for _ in 0..nterms {
                terms.push((rng.in_range(-3, 3), rng.below(num_vars as u64)));
            }
            atoms.push(Atom {
                terms,
                constant: rng.in_range(-6, 6),
                cmp: Cmp::pick(rng),
            });
        }
        Instance { num_vars, atoms }
    }

    /// Materialize as a conjunctive list of IR assertions.
    fn build(&self) -> (TermArena, Vec<TermId>) {
        let mut a = TermArena::new();
        let syms: Vec<TermId> = (0..self.num_vars)
            .map(|i| {
                let s = a.declare(&format!("x{i}"), Sort::Real).unwrap();
                a.var(s)
            })
            .collect();
        let zero = a.real_const(Rational::zero());
        let mut assertions = Vec::with_capacity(self.atoms.len());
        for atom in &self.atoms {
            let mut poly: Option<TermId> = None;
            for &(coeff, v) in &atom.terms {
                let c = a.real_const(Rational::integer(i128::from(coeff)));
                let term = a.real_mul(c, syms[v]).unwrap();
                poly = Some(poly.map_or(term, |acc| a.real_add(acc, term).unwrap()));
            }
            let c = a.real_const(Rational::integer(i128::from(atom.constant)));
            let lhs = poly.map_or(c, |acc| a.real_add(acc, c).unwrap());
            let b = match atom.cmp {
                Cmp::Le => a.real_le(lhs, zero).unwrap(),
                Cmp::Lt => a.real_lt(lhs, zero).unwrap(),
                Cmp::Ge => a.real_ge(lhs, zero).unwrap(),
                Cmp::Gt => a.real_gt(lhs, zero).unwrap(),
                Cmp::Eq => a.eq(lhs, zero).unwrap(),
            };
            assertions.push(b);
        }
        (a, assertions)
    }

    fn to_z3(&self) -> Vec<Bool> {
        let vars: Vec<Real> = (0..self.num_vars)
            .map(|i| Real::new_const(format!("x{i}")))
            .collect();
        let zero = Real::from_rational(0, 1);
        self.atoms
            .iter()
            .map(|atom| {
                let mut poly: Option<Real> = None;
                for &(coeff, v) in &atom.terms {
                    let term = Real::from_rational(coeff, 1) * vars[v].clone();
                    poly = Some(poly.map_or(term.clone(), |acc| acc + term));
                }
                let c = Real::from_rational(atom.constant, 1);
                let lhs = poly.map_or(c.clone(), |acc| acc + c);
                match atom.cmp {
                    Cmp::Le => lhs.le(&zero),
                    Cmp::Lt => lhs.lt(&zero),
                    Cmp::Ge => lhs.ge(&zero),
                    Cmp::Gt => lhs.gt(&zero),
                    Cmp::Eq => lhs.eq(&zero),
                }
            })
            .collect()
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Verdict {
    Sat,
    Unsat,
    Unknown,
}

/// Decide with axeyum's `check_with_lra` on a worker thread under a hard cap. A
/// `Sat` model is independently replayed through the ground evaluator (a
/// non-replaying model is a wrong sat regardless of Z3).
fn axeyum_decide(inst: Instance) -> Option<(Verdict, bool)> {
    let (tx, rx) = mpsc::channel();
    std::thread::spawn(move || {
        let (arena, assertions) = inst.build();
        let out = match check_with_lra(&arena, &assertions) {
            Ok(CheckResult::Sat(model)) => {
                let asg = model.to_assignment();
                let ok = assertions
                    .iter()
                    .all(|&a| matches!(eval(&arena, a, &asg), Ok(Value::Bool(true))));
                (Verdict::Sat, ok)
            }
            Ok(CheckResult::Unsat) => (Verdict::Unsat, true),
            Ok(CheckResult::Unknown(_)) | Err(_) => (Verdict::Unknown, true),
        };
        let _ = tx.send(out);
    });
    rx.recv_timeout(AXEYUM_TIMEOUT).ok()
}

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

#[test]
fn simplex_lra_fallback_disagree_zero() {
    let mut jointly = 0u64;
    let mut agree = 0u64;
    let mut ax_unknown = 0u64;
    let mut ax_timeout = 0u64;
    let mut z3_unknown = 0u64;

    for seed in 0..INSTANCES {
        let mut rng = Lcg::new(seed);
        let inst = Instance::generate(&mut rng);

        let Some((ax, replayed)) = axeyum_decide(inst.clone()) else {
            ax_timeout += 1;
            continue;
        };
        assert!(
            replayed,
            "WRONG SAT (seed {seed}): check_with_lra returned Sat but the model does \
             not replay under the ground evaluator"
        );
        if ax == Verdict::Unknown {
            ax_unknown += 1;
        }

        let z3 = z3_decide(&inst);
        if z3 == Verdict::Unknown {
            z3_unknown += 1;
            continue;
        }
        if ax == Verdict::Unknown {
            continue;
        }
        jointly += 1;
        assert_eq!(
            ax,
            z3,
            "DISAGREEMENT (seed {seed}): axeyum={ax:?} z3={z3:?} — a {} soundness bug \
             in the simplex LRA fallback",
            match (ax, z3) {
                (Verdict::Sat, Verdict::Unsat) => "WRONG-SAT",
                (Verdict::Unsat, Verdict::Sat) => "WRONG-UNSAT (worst case)",
                _ => "verdict",
            }
        );
        agree += 1;
    }

    println!(
        "simplex-lra-fallback: joint={jointly} agree={agree} ax_unknown={ax_unknown} \
         ax_timeout={ax_timeout} z3_unknown={z3_unknown} DISAGREE=0"
    );
    assert!(
        jointly > 100,
        "too few jointly-decided instances ({jointly}); the fallback gate is not \
         meaningfully exercised"
    );
}
