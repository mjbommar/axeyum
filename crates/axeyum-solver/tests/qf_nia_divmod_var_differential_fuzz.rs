//! Adversarial differential soundness fuzzer for the **variable-divisor**
//! integer `div`/`mod` linearization (`check_with_nia`, P2.5 Phase E.0) vs Z3.
//!
//! The proven `nia_differential_fuzz` only ever divides by a *nonzero constant*
//! (its own doc says so), so it does **not** exercise the new capability this
//! slice adds: `(div u v)` / `(mod u v)` with a **variable** divisor `v`,
//! linearized via the `v ≠ 0`-guarded Euclidean identity `u = v·q + r ∧
//! 0 ≤ r < |v|` plus the self-division arm. This harness generates thousands of
//! small random integer conjunctions that each carry ≥ 1 variable-divisor
//! `div`/`mod` atom, decides each with the default pure-Rust front door and with a
//! direct Z3 integer query over the same terms, and gates:
//!
//! - axeyum `Sat` ∧ Z3 `Unsat`  → PANIC (wrong sat).
//! - axeyum `Unsat` ∧ Z3 `Sat`  → PANIC (wrong unsat — the worst bug).
//! - axeyum `Sat`               → the model is independently replayed through the
//!   IR ground evaluator on every original atom; a non-replaying Sat panics.
//! - axeyum `Unknown` / timeout → allowed (incomplete is sound).
//! - Z3 `Unknown` / timeout     → the instance is skipped.
//!
//! ## Division-by-zero corner (the key differential subtlety)
//!
//! SMT-LIB leaves `div`/`mod` by **zero** underspecified (Z3 picks any consistent
//! value — an unconstrained function). axeyum's linearization models it as a
//! **relaxation** (the `v = 0` branch leaves the fresh `q, r` free), so an `Unsat`
//! transfers soundly (Z3's models are a subset). axeyum's ground evaluator uses
//! the *total* convention `div a 0 = 0` / `mod a 0 = a`, and a `Sat` is accepted
//! only after replay against it — a fixed choice that Z3 can always also pick, so
//! a replayed `Sat` is a genuine Z3 model. Either way the joint verdict must
//! agree; the divisor is deliberately allowed to be zero so this corner is stressed.

#![cfg(feature = "z3")]

use std::sync::mpsc;
use std::time::Duration;

use axeyum_ir::{Sort, SymbolId, TermArena, TermId, Value, eval};
use axeyum_solver::{CheckResult, SolverConfig, solve};
use z3::ast::{Bool, Int};
use z3::{Params, SatResult, Solver};

const INSTANCES: u64 = 1500;
const Z3_TIMEOUT: Duration = Duration::from_secs(2);
/// Hard join cap on the axeyum worker thread. Kept slightly above the solve's own
/// configured budget so a normally-terminating solve returns before the join
/// fires (and the worker exits) rather than being abandoned as a leaked,
/// still-grinding thread.
const AXEYUM_TIMEOUT: Duration = Duration::from_secs(6);
/// Wall-clock budget handed to `solve` itself, so the bounded bit-blast width
/// ladder (which cannot bound a *variable* divisor) yields a timely `Unknown`
/// instead of spinning — the worker then exits cleanly. A timeout is
/// adjudication-neutral (never a sat/unsat verdict).
const AXEYUM_SOLVE_BUDGET: Duration = Duration::from_secs(3);

/// Deterministic MMIX linear-congruential PRNG (no clock, fully reproducible).
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

#[derive(Clone, Copy)]
enum DivMod {
    Div,
    Mod,
}

/// One generated atom. All coefficients/indices are plain data so an instance is
/// `Send` + `Clone` and builds identically for the IR and for Z3.
#[derive(Clone)]
enum GAtom {
    /// `c0 + c1·v[i] + c2·v[j] ⋈ rhs`.
    Lin {
        c0: i64,
        c1: i64,
        i: usize,
        c2: i64,
        j: usize,
        rhs: i64,
        cmp: Cmp,
    },
    /// `c0 + c1·v[i]·v[j] ⋈ rhs` (nonlinear product).
    Quad {
        c0: i64,
        c1: i64,
        i: usize,
        j: usize,
        rhs: i64,
        cmp: Cmp,
    },
    /// `(op (b0 + b1·v[i]) (v[d] + off)) ⋈ rhs` — a **variable** divisor.
    DivMod {
        op: DivMod,
        b0: i64,
        b1: i64,
        i: usize,
        d: usize,
        off: i64,
        rhs: i64,
        cmp: Cmp,
    },
    /// `v[i] ⋈ 0` — a sign/nonzero bound (drives some divisors provably nonzero).
    Bound { i: usize, cmp: Cmp },
}

#[derive(Clone)]
struct Instance {
    num_vars: usize,
    atoms: Vec<GAtom>,
}

impl Instance {
    fn generate(rng: &mut Lcg) -> Instance {
        let num_vars = rng.below(2) + 1; // 1..=2
        let num_atoms = rng.below(3) + 1; // 1..=3
        // Guarantee ≥ 1 variable-divisor div/mod atom.
        let host = rng.below(num_atoms as u64);
        let vi = |rng: &mut Lcg| rng.below(num_vars as u64);
        let mut atoms = Vec::with_capacity(num_atoms);
        for idx in 0..num_atoms {
            let atom = if idx == host || rng.below(2) == 0 {
                GAtom::DivMod {
                    op: if rng.below(2) == 0 {
                        DivMod::Div
                    } else {
                        DivMod::Mod
                    },
                    b0: rng.in_range(-3, 3),
                    b1: rng.in_range(-3, 3),
                    i: vi(rng),
                    d: vi(rng),
                    off: rng.in_range(-2, 2),
                    rhs: rng.in_range(-3, 3),
                    cmp: Cmp::pick(rng),
                }
            } else {
                match rng.below(3) {
                    0 => GAtom::Lin {
                        c0: rng.in_range(-3, 3),
                        c1: rng.in_range(-3, 3),
                        i: vi(rng),
                        c2: rng.in_range(-3, 3),
                        j: vi(rng),
                        rhs: rng.in_range(-3, 3),
                        cmp: Cmp::pick(rng),
                    },
                    1 => GAtom::Quad {
                        c0: rng.in_range(-3, 3),
                        c1: rng.in_range(-3, 3),
                        i: vi(rng),
                        j: vi(rng),
                        rhs: rng.in_range(-3, 3),
                        cmp: Cmp::pick(rng),
                    },
                    _ => GAtom::Bound {
                        i: vi(rng),
                        cmp: Cmp::pick(rng),
                    },
                }
            };
            atoms.push(atom);
        }
        Instance { num_vars, atoms }
    }

    fn build(&self) -> (TermArena, Vec<SymbolId>, Vec<TermId>) {
        let mut a = TermArena::new();
        let names = ["x", "y"];
        let syms: Vec<SymbolId> = (0..self.num_vars)
            .map(|i| a.declare(names[i], Sort::Int).unwrap())
            .collect();
        let vars: Vec<TermId> = syms.iter().map(|&s| a.var(s)).collect();
        let zero = a.int_const(0);

        let mut assertions = Vec::with_capacity(self.atoms.len());
        for atom in &self.atoms {
            let bool_term = match *atom {
                GAtom::Lin {
                    c0,
                    c1,
                    i,
                    c2,
                    j,
                    rhs,
                    cmp,
                } => {
                    let t0 = a.int_const(i128::from(c0));
                    let c1t = a.int_const(i128::from(c1));
                    let m1 = a.int_mul(c1t, vars[i]).unwrap();
                    let c2t = a.int_const(i128::from(c2));
                    let m2 = a.int_mul(c2t, vars[j]).unwrap();
                    let s = a.int_add(t0, m1).unwrap();
                    let lhs = a.int_add(s, m2).unwrap();
                    let rhs_t = a.int_const(i128::from(rhs));
                    cmp.build(&mut a, lhs, rhs_t)
                }
                GAtom::Quad {
                    c0,
                    c1,
                    i,
                    j,
                    rhs,
                    cmp,
                } => {
                    let prod = a.int_mul(vars[i], vars[j]).unwrap();
                    let c1t = a.int_const(i128::from(c1));
                    let m = a.int_mul(c1t, prod).unwrap();
                    let t0 = a.int_const(i128::from(c0));
                    let lhs = a.int_add(t0, m).unwrap();
                    let rhs_t = a.int_const(i128::from(rhs));
                    cmp.build(&mut a, lhs, rhs_t)
                }
                GAtom::DivMod {
                    op,
                    b0,
                    b1,
                    i,
                    d,
                    off,
                    rhs,
                    cmp,
                } => {
                    let t0 = a.int_const(i128::from(b0));
                    let b1t = a.int_const(i128::from(b1));
                    let m = a.int_mul(b1t, vars[i]).unwrap();
                    let dividend = a.int_add(t0, m).unwrap();
                    let offt = a.int_const(i128::from(off));
                    let divisor = a.int_add(vars[d], offt).unwrap();
                    let val = match op {
                        DivMod::Div => a.int_div(dividend, divisor).unwrap(),
                        DivMod::Mod => a.int_mod(dividend, divisor).unwrap(),
                    };
                    let rhs_t = a.int_const(i128::from(rhs));
                    cmp.build(&mut a, val, rhs_t)
                }
                GAtom::Bound { i, cmp } => cmp.build(&mut a, vars[i], zero),
            };
            assertions.push(bool_term);
        }
        (a, syms, assertions)
    }

    fn to_z3(&self) -> Vec<Bool> {
        let names = ["x", "y"];
        let vars: Vec<Int> = (0..self.num_vars)
            .map(|i| Int::new_const(names[i]))
            .collect();
        let zero = Int::from_i64(0);
        self.atoms
            .iter()
            .map(|atom| match *atom {
                GAtom::Lin {
                    c0,
                    c1,
                    i,
                    c2,
                    j,
                    rhs,
                    cmp,
                } => {
                    let m1 = Int::mul(&[Int::from_i64(c1), vars[i].clone()]);
                    let m2 = Int::mul(&[Int::from_i64(c2), vars[j].clone()]);
                    let lhs = Int::add(&[Int::from_i64(c0), m1, m2]);
                    cmp.build_z3(&lhs, &Int::from_i64(rhs))
                }
                GAtom::Quad {
                    c0,
                    c1,
                    i,
                    j,
                    rhs,
                    cmp,
                } => {
                    let prod = Int::mul(&[vars[i].clone(), vars[j].clone()]);
                    let m = Int::mul(&[Int::from_i64(c1), prod]);
                    let lhs = Int::add(&[Int::from_i64(c0), m]);
                    cmp.build_z3(&lhs, &Int::from_i64(rhs))
                }
                GAtom::DivMod {
                    op,
                    b0,
                    b1,
                    i,
                    d,
                    off,
                    rhs,
                    cmp,
                } => {
                    let m = Int::mul(&[Int::from_i64(b1), vars[i].clone()]);
                    let dividend = Int::add(&[Int::from_i64(b0), m]);
                    let divisor = Int::add(&[vars[d].clone(), Int::from_i64(off)]);
                    let val = match op {
                        DivMod::Div => dividend.div(&divisor),
                        DivMod::Mod => dividend.modulo(&divisor),
                    };
                    cmp.build_z3(&val, &Int::from_i64(rhs))
                }
                GAtom::Bound { i, cmp } => cmp.build_z3(&vars[i], &zero),
            })
            .collect()
    }

    fn dump(&self) -> String {
        let names = ["x", "y"];
        let mut lines = vec![format!("vars: {}", &names[..self.num_vars].join(", "))];
        for (k, atom) in self.atoms.iter().enumerate() {
            let s = match *atom {
                GAtom::Lin {
                    c0,
                    c1,
                    i,
                    c2,
                    j,
                    rhs,
                    cmp,
                } => format!(
                    "{c0} + {c1}*{} + {c2}*{} {} {rhs}",
                    names[i],
                    names[j],
                    cmp.symbol()
                ),
                GAtom::Quad {
                    c0,
                    c1,
                    i,
                    j,
                    rhs,
                    cmp,
                } => {
                    format!(
                        "{c0} + {c1}*{}*{} {} {rhs}",
                        names[i],
                        names[j],
                        cmp.symbol()
                    )
                }
                GAtom::DivMod {
                    op,
                    b0,
                    b1,
                    i,
                    d,
                    off,
                    rhs,
                    cmp,
                } => {
                    let opn = match op {
                        DivMod::Div => "div",
                        DivMod::Mod => "mod",
                    };
                    format!(
                        "({opn} ({b0}+{b1}*{}) ({}+{off})) {} {rhs}",
                        names[i],
                        names[d],
                        cmp.symbol()
                    )
                }
                GAtom::Bound { i, cmp } => format!("{} {} 0", names[i], cmp.symbol()),
            };
            lines.push(format!("  atom[{k}]: {s}"));
        }
        lines.join("\n")
    }
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

#[derive(Clone, PartialEq, Eq, Debug)]
enum Replay {
    NotSat,
    AllTrue,
    Indeterminate,
    Violated { atom: usize, model: String },
}

struct AxeyumOutcome {
    verdict: Verdict,
    replay: Replay,
    model_dump: Option<String>,
}

fn dump_model(syms: &[SymbolId], model: &axeyum_solver::Model) -> String {
    let names = ["x", "y"];
    let mut parts = Vec::new();
    for (i, &s) in syms.iter().enumerate() {
        parts.push(format!("{}={:?}", names[i], model.get(s)));
    }
    parts.join(", ")
}

fn solve_axeyum_bounded(inst: Instance) -> Option<AxeyumOutcome> {
    let (tx, rx) = mpsc::channel();
    std::thread::spawn(move || {
        let (a, syms, assertions) = inst.build();
        let mut a = a;
        let cfg = SolverConfig::default().with_timeout(AXEYUM_SOLVE_BUDGET);
        let outcome = match solve(&mut a, &assertions, &cfg) {
            Err(_) => None,
            Ok(ax) => {
                let verdict = label(&ax);
                let (replay, model_dump) = match &ax {
                    CheckResult::Sat(model) => {
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
                Some(AxeyumOutcome {
                    verdict,
                    replay,
                    model_dump,
                })
            }
        };
        let _ = tx.send(outcome);
    });
    match rx.recv_timeout(AXEYUM_TIMEOUT) {
        Ok(Some(outcome)) => Some(outcome),
        Ok(None) => panic!("axeyum solve returned an error (Unknown must be a result)"),
        Err(mpsc::RecvTimeoutError::Timeout) => None,
        Err(mpsc::RecvTimeoutError::Disconnected) => panic!("axeyum worker thread panicked"),
    }
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
fn qf_nia_divmod_var_differential_fuzz_disagree_zero() {
    let mut jointly_decided = 0u64;
    let mut agreements = 0u64;
    let mut ax_unknown = 0u64;
    let mut ax_timeout = 0u64;
    let mut z3_unknown = 0u64;
    let mut sat_replayed = 0u64;

    for seed in 0..INSTANCES {
        if seed % 250 == 0 {
            eprintln!(
                "[nia-divmod-fuzz] seed {seed}/{INSTANCES} (joint={jointly_decided}, \
                 agree={agreements}, ax_unknown={ax_unknown}, ax_timeout={ax_timeout})"
            );
        }
        let mut rng = Lcg::new(seed);
        let inst = Instance::generate(&mut rng);

        let Some(outcome) = solve_axeyum_bounded(inst.clone()) else {
            ax_timeout += 1;
            continue;
        };

        if let Replay::Violated { atom, model } = &outcome.replay {
            panic!(
                "WRONG SAT (seed {seed}): axeyum Sat but atom[{atom}] is FALSE under the \
                 ground evaluator.\nmodel: {model}\ninstance:\n{}",
                inst.dump()
            );
        }
        if outcome.replay == Replay::AllTrue {
            sat_replayed += 1;
        }
        let ax_label = outcome.verdict;
        if ax_label == Verdict::Unknown {
            ax_unknown += 1;
        }

        let z3_label = z3_decide(&inst);
        if z3_label == Verdict::Unknown {
            z3_unknown += 1;
            continue;
        }
        if ax_label == Verdict::Unknown {
            continue;
        }

        jointly_decided += 1;
        if ax_label == z3_label {
            agreements += 1;
        } else {
            let model_dump = outcome.model_dump.unwrap_or_else(|| "(none)".to_string());
            panic!(
                "DISAGREEMENT (seed {seed}): axeyum = {ax_label:?}, Z3 = {z3_label:?} — a {} bug.\n\
                 axeyum model: {model_dump}\ninstance:\n{}",
                match (ax_label, z3_label) {
                    (Verdict::Sat, Verdict::Unsat) => "WRONG-SAT",
                    (Verdict::Unsat, Verdict::Sat) => "WRONG-UNSAT (worst case)",
                    _ => "verdict",
                },
                inst.dump()
            );
        }
    }

    println!("=== QF_NIA variable-divisor div/mod differential fuzz ===");
    println!("jointly decided:      {jointly_decided}");
    println!("agreements:           {agreements}");
    println!("axeyum Unknown:       {ax_unknown}");
    println!("axeyum timeout:       {ax_timeout}");
    println!("Z3 Unknown (skipped): {z3_unknown}");
    println!("Sat replays verified: {sat_replayed}");
    println!("DISAGREEMENTS:        0");

    assert!(
        jointly_decided > 100,
        "too few jointly-decided instances ({jointly_decided}); gate not exercised"
    );
}
