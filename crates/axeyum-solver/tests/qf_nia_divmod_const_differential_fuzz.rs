//! Adversarial differential soundness fuzzer for the **constant-divisor** integer
//! `div`/`mod` linearization — DELIBERATELY including the degenerate
//! **constant-zero** divisor `(div x 0)` / `(mod x 0)` / `(div 0 0)` and nested
//! div-0 chains that the variable-divisor fuzz (`qf_nia_divmod_var_...`)
//! structurally CANNOT generate (its divisor is always a variable expression, so
//! it never routes through the constant-0 branch of `eliminate_int_divmod`).
//!
//! This is the gate that would have caught the P0 wrong-unsat (`a946f925`): the
//! constant-0 branch folded `div a 0` / `mod a 0` to a FIXED convention value,
//! refuting formulas that are satisfiable under a *different* underspecified value.
//! The current mechanism keeps every div-by-zero value **free** (and, on the
//! variable path, **congruent**), so:
//!
//! - axeyum `Sat`   ∧ Z3 `Unsat` → PANIC (wrong sat).
//! - axeyum `Unsat` ∧ Z3 `Sat`   → PANIC (wrong unsat — the P0 class).
//! - axeyum `Unknown` / timeout  → allowed (incomplete is sound).
//! - Z3 `Unknown` / timeout      → the instance is skipped.
//!
//! SMT-LIB leaves `div`/`mod` by zero underspecified; both engines model it as an
//! unconstrained (but functionally consistent) value, so the joint verdict must
//! still agree whenever both decide — that **verdict differential vs Z3** is the
//! authoritative soundness gate here.
//!
//! ## Why replay is diagnostic-only (not a wrong-sat panic) for THIS fuzz
//!
//! Unlike the variable-divisor fuzz, a `Sat` here is NOT gated by ground-evaluator
//! replay: a constant-zero divisor `mod a 0` is a *free* value, and a legitimate
//! model can pick a value the in-tree evaluator's total convention (`mod a 0 = a`,
//! `div a 0 = 0`) does not reproduce — e.g. `div(mod 3 0) (-1) = 3` is sat by
//! `mod 3 0 = -3`, but the evaluator computes `mod 3 0 = 3` ⇒ `div 3 (-1) = -3 ≠
//! 3`. That replay "violation" is a convention artifact, NOT a wrong sat (Z3
//! confirms sat). So replay is tracked for diagnostics only; the wrong-sat gate is
//! the verdict differential (`axeyum Sat ∧ Z3 Unsat`).
#![cfg(feature = "full")]
#![cfg(feature = "z3")]

use std::sync::mpsc;
use std::time::Duration;

use axeyum_ir::{Sort, SymbolId, TermArena, TermId, Value, eval};
use axeyum_solver::{CheckResult, SolverConfig, solve};
use z3::ast::{Bool, Int};
use z3::{Params, SatResult, Solver};

const INSTANCES: u64 = 1500;
const Z3_TIMEOUT: Duration = Duration::from_secs(2);
const AXEYUM_TIMEOUT: Duration = Duration::from_secs(6);
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
    /// A constant divisor drawn from a set that is HEAVILY weighted toward `0`
    /// (the P0 corner) but also covers small nonzero magnitudes (decidable cases
    /// that keep the fuzz's jointly-decided count healthy).
    fn divisor_const(&mut self) -> i64 {
        match self.below(8) {
            0..=2 => 0, // ~37% zero — the degenerate shape the P0 lived in
            3 => 1,
            4 => -1,
            5 => 2,
            6 => -2,
            _ => 3,
        }
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
impl DivMod {
    fn pick(rng: &mut Lcg) -> DivMod {
        if rng.below(2) == 0 {
            DivMod::Div
        } else {
            DivMod::Mod
        }
    }
    fn name(self) -> &'static str {
        match self {
            DivMod::Div => "div",
            DivMod::Mod => "mod",
        }
    }
}

/// A `div`/`mod` term with a **constant** divisor `k` (frequently `0`). Its
/// dividend is either a small linear expression or a nested constant-divisor
/// `div`/`mod` term (the div-0-chain shape of `div.01`).
#[derive(Clone)]
enum DTerm {
    /// `(op (c0 + c1·v[i]) k)`.
    Flat {
        op: DivMod,
        c0: i64,
        c1: i64,
        i: usize,
        k: i64,
    },
    /// `(op (op2 (c0 + c1·v[i]) k2) k)` — a nested chain, both divisors constant.
    Nested {
        op: DivMod,
        op2: DivMod,
        c0: i64,
        c1: i64,
        i: usize,
        k2: i64,
        k: i64,
    },
}
impl DTerm {
    fn generate(rng: &mut Lcg, num_vars: usize) -> DTerm {
        let vi = |rng: &mut Lcg| rng.below(num_vars as u64);
        if rng.below(2) == 0 {
            DTerm::Flat {
                op: DivMod::pick(rng),
                c0: rng.in_range(-3, 3),
                c1: rng.in_range(-2, 2),
                i: vi(rng),
                k: rng.divisor_const(),
            }
        } else {
            DTerm::Nested {
                op: DivMod::pick(rng),
                op2: DivMod::pick(rng),
                c0: rng.in_range(-3, 3),
                c1: rng.in_range(-2, 2),
                i: vi(rng),
                k2: rng.divisor_const(),
                k: rng.divisor_const(),
            }
        }
    }
    /// Whether this term (or its nested divisor) uses a zero constant divisor.
    fn hits_zero(&self) -> bool {
        match *self {
            DTerm::Flat { k, .. } => k == 0,
            DTerm::Nested { k, k2, .. } => k == 0 || k2 == 0,
        }
    }
    fn build(&self, a: &mut TermArena, vars: &[TermId]) -> TermId {
        match *self {
            DTerm::Flat { op, c0, c1, i, k } => {
                let t0 = a.int_const(i128::from(c0));
                let c1t = a.int_const(i128::from(c1));
                let m = a.int_mul(c1t, vars[i]).unwrap();
                let dividend = a.int_add(t0, m).unwrap();
                let kt = a.int_const(i128::from(k));
                match op {
                    DivMod::Div => a.int_div(dividend, kt).unwrap(),
                    DivMod::Mod => a.int_mod(dividend, kt).unwrap(),
                }
            }
            DTerm::Nested {
                op,
                op2,
                c0,
                c1,
                i,
                k2,
                k,
            } => {
                let t0 = a.int_const(i128::from(c0));
                let c1t = a.int_const(i128::from(c1));
                let m = a.int_mul(c1t, vars[i]).unwrap();
                let base = a.int_add(t0, m).unwrap();
                let k2t = a.int_const(i128::from(k2));
                let inner = match op2 {
                    DivMod::Div => a.int_div(base, k2t).unwrap(),
                    DivMod::Mod => a.int_mod(base, k2t).unwrap(),
                };
                let kt = a.int_const(i128::from(k));
                match op {
                    DivMod::Div => a.int_div(inner, kt).unwrap(),
                    DivMod::Mod => a.int_mod(inner, kt).unwrap(),
                }
            }
        }
    }
    fn build_z3(&self, vars: &[Int]) -> Int {
        match *self {
            DTerm::Flat { op, c0, c1, i, k } => {
                let m = Int::mul(&[Int::from_i64(c1), vars[i].clone()]);
                let dividend = Int::add(&[Int::from_i64(c0), m]);
                let kt = Int::from_i64(k);
                match op {
                    DivMod::Div => dividend.div(&kt),
                    DivMod::Mod => dividend.modulo(&kt),
                }
            }
            DTerm::Nested {
                op,
                op2,
                c0,
                c1,
                i,
                k2,
                k,
            } => {
                let m = Int::mul(&[Int::from_i64(c1), vars[i].clone()]);
                let base = Int::add(&[Int::from_i64(c0), m]);
                let k2t = Int::from_i64(k2);
                let inner = match op2 {
                    DivMod::Div => base.div(&k2t),
                    DivMod::Mod => base.modulo(&k2t),
                };
                let kt = Int::from_i64(k);
                match op {
                    DivMod::Div => inner.div(&kt),
                    DivMod::Mod => inner.modulo(&kt),
                }
            }
        }
    }
    fn dump(&self) -> String {
        let names = ["x", "y"];
        match *self {
            DTerm::Flat { op, c0, c1, i, k } => {
                format!("({} ({c0}+{c1}*{}) {k})", op.name(), names[i])
            }
            DTerm::Nested {
                op,
                op2,
                c0,
                c1,
                i,
                k2,
                k,
            } => format!(
                "({} ({} ({c0}+{c1}*{}) {k2}) {k})",
                op.name(),
                op2.name(),
                names[i]
            ),
        }
    }
}

/// One generated atom.
#[derive(Clone)]
enum GAtom {
    /// `dterm ⋈ rhs` — a constant-divisor div/mod compared to a constant.
    TermRel { t: DTerm, rhs: i64, cmp: Cmp },
    /// `t1 ⋈ t2` — two constant-divisor div/mod terms compared directly (the
    /// `div.01` equality/distinct shape that stresses congruence).
    Rel { t1: DTerm, t2: DTerm, cmp: Cmp },
    /// `v[i] ⋈ 0` — a sign/nonzero bound.
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
        let mut atoms = Vec::with_capacity(num_atoms);
        for _ in 0..num_atoms {
            let atom = match rng.below(4) {
                0 => GAtom::TermRel {
                    t: DTerm::generate(rng, num_vars),
                    rhs: rng.in_range(-3, 3),
                    cmp: Cmp::pick(rng),
                },
                1 | 2 => GAtom::Rel {
                    t1: DTerm::generate(rng, num_vars),
                    t2: DTerm::generate(rng, num_vars),
                    cmp: Cmp::pick(rng),
                },
                _ => GAtom::Bound {
                    i: rng.below(num_vars as u64),
                    cmp: Cmp::pick(rng),
                },
            };
            atoms.push(atom);
        }
        // Guarantee ≥ 1 constant-ZERO divisor somewhere (the degenerate shape).
        let has_zero = atoms.iter().any(|a| match a {
            GAtom::TermRel { t, .. } => t.hits_zero(),
            GAtom::Rel { t1, t2, .. } => t1.hits_zero() || t2.hits_zero(),
            GAtom::Bound { .. } => false,
        });
        if !has_zero {
            let i = rng.below(num_vars as u64);
            atoms.push(GAtom::TermRel {
                t: DTerm::Flat {
                    op: DivMod::pick(rng),
                    c0: rng.in_range(-3, 3),
                    c1: rng.in_range(-2, 2),
                    i,
                    k: 0,
                },
                rhs: rng.in_range(-3, 3),
                cmp: Cmp::pick(rng),
            });
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
            let bool_term = match atom {
                GAtom::TermRel { t, rhs, cmp } => {
                    let lhs = t.build(&mut a, &vars);
                    let rhs_t = a.int_const(i128::from(*rhs));
                    cmp.build(&mut a, lhs, rhs_t)
                }
                GAtom::Rel { t1, t2, cmp } => {
                    let l = t1.build(&mut a, &vars);
                    let r = t2.build(&mut a, &vars);
                    cmp.build(&mut a, l, r)
                }
                GAtom::Bound { i, cmp } => cmp.build(&mut a, vars[*i], zero),
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
            .map(|atom| match atom {
                GAtom::TermRel { t, rhs, cmp } => {
                    let lhs = t.build_z3(&vars);
                    cmp.build_z3(&lhs, &Int::from_i64(*rhs))
                }
                GAtom::Rel { t1, t2, cmp } => {
                    let l = t1.build_z3(&vars);
                    let r = t2.build_z3(&vars);
                    cmp.build_z3(&l, &r)
                }
                GAtom::Bound { i, cmp } => cmp.build_z3(&vars[*i], &zero),
            })
            .collect()
    }

    fn dump(&self) -> String {
        let names = ["x", "y"];
        let mut lines = vec![format!("vars: {}", &names[..self.num_vars].join(", "))];
        for (k, atom) in self.atoms.iter().enumerate() {
            let s = match atom {
                GAtom::TermRel { t, rhs, cmp } => {
                    format!("{} {} {rhs}", t.dump(), cmp.symbol())
                }
                GAtom::Rel { t1, t2, cmp } => {
                    format!("{} {} {}", t1.dump(), cmp.symbol(), t2.dump())
                }
                GAtom::Bound { i, cmp } => format!("{} {} 0", names[*i], cmp.symbol()),
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
fn qf_nia_divmod_const_differential_fuzz_disagree_zero() {
    let mut jointly_decided = 0u64;
    let mut agreements = 0u64;
    let mut ax_unknown = 0u64;
    let mut ax_timeout = 0u64;
    let mut z3_unknown = 0u64;
    let mut sat_replayed = 0u64;
    let mut zero_divisor_seen = 0u64;

    for seed in 0..INSTANCES {
        if seed % 250 == 0 {
            eprintln!(
                "[nia-divmod-const-fuzz] seed {seed}/{INSTANCES} (joint={jointly_decided}, \
                 agree={agreements}, ax_unknown={ax_unknown}, ax_timeout={ax_timeout})"
            );
        }
        let mut rng = Lcg::new(seed ^ 0x5f3d_c0de_1234_9a7b);
        let inst = Instance::generate(&mut rng);
        // The generator guarantees ≥ 1 zero divisor.
        zero_divisor_seen += 1;

        let Some(outcome) = solve_axeyum_bounded(inst.clone()) else {
            ax_timeout += 1;
            continue;
        };

        // Replay is DIAGNOSTIC-ONLY here (see module docs): a constant div-0 free
        // value the evaluator's total convention cannot reproduce makes a genuine
        // Sat "violate" replay, so we do NOT panic on it — the wrong-sat gate is
        // the verdict differential vs Z3 below. We only tally faithful replays.
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
                    (Verdict::Unsat, Verdict::Sat) => "WRONG-UNSAT (worst case — the P0 class)",
                    _ => "verdict",
                },
                inst.dump()
            );
        }
    }

    println!("=== QF_NIA constant-divisor (incl. zero) div/mod differential fuzz ===");
    println!("jointly decided:      {jointly_decided}");
    println!("agreements:           {agreements}");
    println!("axeyum Unknown:       {ax_unknown}");
    println!("axeyum timeout:       {ax_timeout}");
    println!("Z3 Unknown (skipped): {z3_unknown}");
    println!("Sat replays verified: {sat_replayed}");
    println!("zero-divisor instances: {zero_divisor_seen}");
    println!("DISAGREEMENTS:        0");

    assert!(
        jointly_decided > 100,
        "too few jointly-decided instances ({jointly_decided}); gate not exercised"
    );
}
