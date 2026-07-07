//! Adversarial differential fuzz for pure `QF_LRA` (linear real arithmetic)
//! with *Boolean structure*, cross-checked against the Z3 oracle.
//!
//! The existing arithmetic fuzzers cover nonlinear real (`nra_`), integer
//! (`nia_`), and UF+integer (`uflia_`). None directly stresses the **online LRA
//! DPLL(T) loop** — the incremental, backtrackable LRA theory solver with theory
//! propagation and 1-UIP theory-conflict learning that recently became the
//! default route for mixed UF+arithmetic. This gate generates linear-real atoms
//! combined by `and`/`or`/`not` into a Boolean formula, so the SAT core must
//! case-split and the LRA theory must answer partial-assignment consistency
//! queries — exactly the spine that is otherwise only fuzzed indirectly.
//!
//! Soundness contract (the whole point):
//! - axeyum `Sat`  ∧ Z3 `Unsat` → **PANIC** (wrong sat).
//! - axeyum `Unsat` ∧ Z3 `Sat`  → **PANIC** (wrong unsat — the worst bug).
//! - axeyum `Unknown` → fine (sound-incomplete is allowed).
//! - Z3 `Unknown`/timeout → skip (cannot adjudicate).
//!
//! Deterministic (seeded LCG, no clock/entropy); each axeyum solve runs under a
//! wall-clock cap on a worker thread so a slow instance is skipped, not hung.

#![cfg(feature = "z3")]

use std::sync::mpsc;
use std::time::Duration;

use axeyum_ir::{Rational, Sort, TermArena, TermId};
use axeyum_solver::{CheckResult, SolverConfig, solve};
use z3::ast::{Bool, Real};
use z3::{Params, SatResult, Solver};

const INSTANCES: u64 = 1500;
const AXEYUM_TIMEOUT: Duration = Duration::from_secs(3);
const Z3_TIMEOUT: Duration = Duration::from_secs(2);

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
    fn flip(&mut self) -> bool {
        self.next_u64() & 1 == 1
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
    fn build_ir(self, a: &mut TermArena, lhs: TermId, zero: TermId) -> TermId {
        match self {
            Cmp::Eq => a.eq(lhs, zero).unwrap(),
            Cmp::Ne => {
                let e = a.eq(lhs, zero).unwrap();
                a.not(e).unwrap()
            }
            Cmp::Lt => a.real_lt(lhs, zero).unwrap(),
            Cmp::Le => a.real_le(lhs, zero).unwrap(),
            Cmp::Gt => a.real_gt(lhs, zero).unwrap(),
            Cmp::Ge => a.real_ge(lhs, zero).unwrap(),
        }
    }
    fn build_z3(self, lhs: &Real, zero: &Real) -> Bool {
        match self {
            Cmp::Eq => lhs.eq(zero),
            Cmp::Ne => lhs.eq(zero).not(),
            Cmp::Lt => lhs.lt(zero),
            Cmp::Le => lhs.le(zero),
            Cmp::Gt => lhs.gt(zero),
            Cmp::Ge => lhs.ge(zero),
        }
    }
}

/// A divisor for the optional `RealDiv` wrap on an atom's LHS (GAP-R1). SMT-LIB
/// `/` by `0` is **UNDERSPEC** — any total (but functionally-consistent) value —
/// so a stray fold that pins it could wrongly refute a formula that is `Sat`
/// only under a particular `x/0` value (the `a946f925` shape, `RealDiv` analog).
/// The generator deliberately emits the **constant-`0`** divisor (a separate
/// fold branch from a variable divisor) and a variable that another atom can pin
/// to `0` (the NRA `r·y = x` purification path).
#[derive(Clone, Copy)]
enum Divisor {
    /// Divide by a literal constant — including `0` (the degenerate case).
    Const(i64),
    /// Divide by `var[i]`, which another atom may constrain to `0`.
    Var(usize),
}

/// A linear atom: `(Σ coeff_i · x_i + constant) ⋈ 0`, optionally divided by a
/// `Divisor` first (`(poly / d) ⋈ 0`), optionally negated.
#[derive(Clone)]
struct LinAtom {
    terms: Vec<(i64, usize)>,
    constant: i64,
    cmp: Cmp,
    neg: bool,
    divisor: Option<Divisor>,
}

/// A generated instance: linear atoms folded into a Boolean formula by `ops`
/// (`true` = `and`, `false` = `or`), left-associatively. Plain data → `Send`.
#[derive(Clone)]
struct Instance {
    num_vars: usize,
    atoms: Vec<LinAtom>,
    ops: Vec<bool>,
}

impl Instance {
    fn generate(rng: &mut Lcg) -> Instance {
        let num_vars = rng.below(3) + 2; // 2..=4
        let num_atoms = rng.below(4) + 2; // 2..=5
        let mut atoms = Vec::with_capacity(num_atoms);
        for _ in 0..num_atoms {
            let nterms = rng.below(num_vars as u64) + 1; // 1..=num_vars
            let mut terms = Vec::with_capacity(nterms);
            for _ in 0..nterms {
                terms.push((rng.in_range(-3, 3), rng.below(num_vars as u64)));
            }
            // ~1/4 of atoms wrap the LHS in a `RealDiv` (GAP-R1). The divisor is
            // biased toward the degenerate shapes: a constant (often `0`), or a
            // variable another atom can pin to `0`. A constant nonzero divisor
            // keeps the atom linear (LRA scaling); `0` and variable divisors are
            // the underspecified / purification axes.
            let divisor = if rng.below(4) == 0 {
                Some(match rng.below(3) {
                    // Constant `0` — the deliberate degenerate `(poly / 0)` case.
                    0 => Divisor::Const(0),
                    // Small nonzero constant divisor (stays linear).
                    1 => Divisor::Const(rng.in_range(-3, 3) | 1),
                    // Variable divisor — pinnable to `0` by another atom.
                    _ => Divisor::Var(rng.below(num_vars as u64)),
                })
            } else {
                None
            };
            atoms.push(LinAtom {
                terms,
                constant: rng.in_range(-3, 3),
                cmp: Cmp::pick(rng),
                neg: rng.flip(),
                divisor,
            });
        }
        let ops = (0..num_atoms - 1).map(|_| rng.flip()).collect();
        Instance {
            num_vars,
            atoms,
            ops,
        }
    }

    fn build(&self) -> (TermArena, Vec<TermId>) {
        let mut a = TermArena::new();
        let names = ["x", "y", "z", "w"];
        let vars: Vec<TermId> = (0..self.num_vars)
            .map(|i| {
                let s = a.declare(names[i], Sort::Real).unwrap();
                a.var(s)
            })
            .collect();
        let zero = a.real_const(Rational::zero());

        let bools: Vec<TermId> = self
            .atoms
            .iter()
            .map(|atom| {
                let mut poly: Option<TermId> = None;
                for &(coeff, v) in &atom.terms {
                    let c = a.real_const(Rational::integer(i128::from(coeff)));
                    let term = a.real_mul(c, vars[v]).unwrap();
                    poly = Some(poly.map_or(term, |acc| a.real_add(acc, term).unwrap()));
                }
                let c = a.real_const(Rational::integer(i128::from(atom.constant)));
                let mut lhs = poly.map_or(c, |acc| a.real_add(acc, c).unwrap());
                if let Some(d) = atom.divisor {
                    let dt = match d {
                        Divisor::Const(k) => a.real_const(Rational::integer(i128::from(k))),
                        Divisor::Var(v) => vars[v],
                    };
                    lhs = a.real_div(lhs, dt).unwrap();
                }
                let b = atom.cmp.build_ir(&mut a, lhs, zero);
                if atom.neg { a.not(b).unwrap() } else { b }
            })
            .collect();

        let mut acc = bools[0];
        for (i, &b) in bools.iter().enumerate().skip(1) {
            acc = if self.ops[i - 1] {
                a.and(acc, b).unwrap()
            } else {
                a.or(acc, b).unwrap()
            };
        }
        (a, vec![acc])
    }

    fn to_z3(&self) -> Bool {
        let names = ["x", "y", "z", "w"];
        let vars: Vec<Real> = (0..self.num_vars)
            .map(|i| Real::new_const(names[i]))
            .collect();
        let zero = Real::from_rational(0, 1);

        let bools: Vec<Bool> = self
            .atoms
            .iter()
            .map(|atom| {
                let mut poly: Option<Real> = None;
                for &(coeff, v) in &atom.terms {
                    let term = Real::from_rational(coeff, 1) * vars[v].clone();
                    poly = Some(poly.map_or(term.clone(), |acc| acc + term));
                }
                let c = Real::from_rational(atom.constant, 1);
                let mut lhs = poly.map_or(c.clone(), |acc| acc + c);
                if let Some(d) = atom.divisor {
                    let dt = match d {
                        Divisor::Const(k) => Real::from_rational(k, 1),
                        Divisor::Var(v) => vars[v].clone(),
                    };
                    lhs /= dt;
                }
                let b = atom.cmp.build_z3(&lhs, &zero);
                if atom.neg { b.not() } else { b }
            })
            .collect();

        let mut acc = bools[0].clone();
        for (i, b) in bools.iter().enumerate().skip(1) {
            acc = if self.ops[i - 1] {
                Bool::and(&[acc, b.clone()])
            } else {
                Bool::or(&[acc, b.clone()])
            };
        }
        acc
    }

    fn dump(&self) -> String {
        let names = ["x", "y", "z", "w"];
        let mut lines = vec![format!("vars: {}", names[..self.num_vars].join(", "))];
        for (i, atom) in self.atoms.iter().enumerate() {
            let parts: Vec<String> = atom
                .terms
                .iter()
                .map(|&(c, v)| format!("{c}*{}", names[v]))
                .collect();
            let neg = if atom.neg { "NOT " } else { "" };
            let div = match atom.divisor {
                None => String::new(),
                Some(Divisor::Const(k)) => format!(" / {k}"),
                Some(Divisor::Var(v)) => format!(" / {}", names[v]),
            };
            lines.push(format!(
                "  atom[{i}]: {neg}(({} + {}){div} {} 0)",
                parts.join(" + "),
                atom.constant,
                atom.cmp.symbol()
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
fn qf_lra_differential_fuzz_disagree_zero() {
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
        "qf_lra fuzz: {INSTANCES} instances | {agree} agree | {ax_unknown} axeyum-unknown | {z3_unknown} z3-unknown(skipped) | 0 DISAGREE"
    );
    // Sanity: the LRA path must actually decide a substantial share, else the
    // gate is vacuous (e.g. a dispatch regression sending everything to Unknown).
    // The `RealDiv`-by-variable atoms are nonlinear and legitimately raise the
    // axeyum-Unknown rate, so the floor is a third (not a half) of the sweep.
    assert!(
        agree >= INSTANCES / 3,
        "expected >= {} agreements, got {agree} (axeyum-unknown {ax_unknown}) — LRA dispatch regression?",
        INSTANCES / 3
    );
}

// ---------------------------------------------------------------------------
// GAP-R1 — explicit `RealDiv`-by-0 degenerate seeds. SMT-LIB `/` by `0` is
// UNDERSPEC: any total value, but **functionally consistent** (congruent). The
// `a946f925` RealDiv analog: a formula that is `Sat` only under a particular
// `x/0` value must NOT be refuted; and two occurrences of the SAME `x/0` must
// agree (congruence). Adjudicated by `Solver::new()` (no set-logic → Z3's
// default tactic models `/0` as the congruent uninterpreted value, matching
// axeyum's `real_div_zero`). Built as raw IR + Z3 (the linear-atom `Instance`
// form cannot express a bare `(/ x 0) = k`).
// ---------------------------------------------------------------------------

/// Decide a raw axeyum assertion set (tiny → no worker thread needed).
fn ax_decide(a: &mut TermArena, assertions: &[TermId]) -> Verdict {
    match solve(a, assertions, &SolverConfig::default()) {
        Ok(CheckResult::Sat(_)) => Verdict::Sat,
        Ok(CheckResult::Unsat) => Verdict::Unsat,
        Ok(CheckResult::Unknown(_)) | Err(_) => Verdict::Unknown,
    }
}

/// Decide a raw Z3 assertion set with the default (no-logic) tactic.
fn z3_decide_bools(bools: &[Bool]) -> Verdict {
    let solver = Solver::new();
    let mut params = Params::new();
    params.set_u32(
        "timeout",
        u32::try_from(Z3_TIMEOUT.as_millis()).unwrap_or(u32::MAX),
    );
    solver.set_params(&params);
    for b in bools {
        solver.assert(b.clone());
    }
    match solver.check() {
        SatResult::Sat => Verdict::Sat,
        SatResult::Unsat => Verdict::Unsat,
        SatResult::Unknown => Verdict::Unknown,
    }
}

fn real_k(a: &mut TermArena, k: i64) -> TermId {
    a.real_const(Rational::integer(i128::from(k)))
}

/// `(/ x 0) = 5` — the free `x/0` value: SAT on both. axeyum must NOT refute a
/// formula satisfiable only by choosing a particular `x/0`.
#[test]
fn seed_realdiv_const_zero_free_value_is_sat() {
    let mut a = TermArena::new();
    let x = {
        let s = a.declare("x", Sort::Real).unwrap();
        a.var(s)
    };
    let zero = real_k(&mut a, 0);
    let q = a.real_div(x, zero).unwrap();
    let five = real_k(&mut a, 5);
    let eq = a.eq(q, five).unwrap();
    let ax = ax_decide(&mut a, &[eq]);

    let zx = Real::new_const("x");
    let zq = zx / Real::from_rational(0, 1);
    let zeq = zq.eq(Real::from_rational(5, 1));
    let z3 = z3_decide_bools(&[zeq]);

    assert!(
        !(matches!(
            (ax, z3),
            (Verdict::Unsat, Verdict::Sat) | (Verdict::Sat, Verdict::Unsat)
        )),
        "(/ x 0) = 5: axeyum={ax:?}, Z3={z3:?} — RealDiv-by-0 must be a free value, not refuted"
    );
}

/// `(/ x 0) = 5 ∧ (/ x 0) = 6` — the SAME `x/0` term twice: congruence forbids
/// two values, so UNSAT on both. (A model that let `x/0` be both 5 and 6 would
/// be a wrong-SAT.)
#[test]
fn seed_realdiv_const_zero_congruence_is_unsat() {
    let mut a = TermArena::new();
    let x = {
        let s = a.declare("x", Sort::Real).unwrap();
        a.var(s)
    };
    let zero = real_k(&mut a, 0);
    let q = a.real_div(x, zero).unwrap();
    let five = real_k(&mut a, 5);
    let six = real_k(&mut a, 6);
    let e5 = a.eq(q, five).unwrap();
    let e6 = a.eq(q, six).unwrap();
    let ax = ax_decide(&mut a, &[e5, e6]);

    let zx = Real::new_const("x");
    let zq = zx / Real::from_rational(0, 1);
    let z3 = z3_decide_bools(&[
        zq.eq(Real::from_rational(5, 1)),
        zq.eq(Real::from_rational(6, 1)),
    ]);

    assert!(
        !(matches!(
            (ax, z3),
            (Verdict::Unsat, Verdict::Sat) | (Verdict::Sat, Verdict::Unsat)
        )),
        "(/ x 0)=5 ∧ (/ x 0)=6: axeyum={ax:?}, Z3={z3:?} — congruence must forbid two values"
    );
}

/// `(/ 0 0) = 7` — `0/0` is likewise a free congruent value: SAT on both.
#[test]
fn seed_realdiv_zero_over_zero_is_free() {
    let mut a = TermArena::new();
    let z0 = real_k(&mut a, 0);
    let z0b = real_k(&mut a, 0);
    let q = a.real_div(z0, z0b).unwrap();
    let seven = real_k(&mut a, 7);
    let eq = a.eq(q, seven).unwrap();
    let ax = ax_decide(&mut a, &[eq]);

    let zq = Real::from_rational(0, 1) / Real::from_rational(0, 1);
    let z3 = z3_decide_bools(&[zq.eq(Real::from_rational(7, 1))]);

    assert!(
        !(matches!(
            (ax, z3),
            (Verdict::Unsat, Verdict::Sat) | (Verdict::Sat, Verdict::Unsat)
        )),
        "(/ 0 0) = 7: axeyum={ax:?}, Z3={z3:?} — 0/0 must be a free value"
    );
}

/// Symbolic divisor pinned to `0` — the NRA `r·y = x` purification path. With
/// `y = 0`, a single `(/ x y) = 5` must stay SAT (free), and a conflicting pair
/// `(/ x y) = 5 ∧ (/ x y) = 6` must be UNSAT (congruence). Both checked.
#[test]
fn seed_realdiv_symbolic_divisor_pinned_zero() {
    // (a) single constraint under y = 0 → SAT (must not refute the free value).
    {
        let mut a = TermArena::new();
        let x = {
            let s = a.declare("x", Sort::Real).unwrap();
            a.var(s)
        };
        let y = {
            let s = a.declare("y", Sort::Real).unwrap();
            a.var(s)
        };
        let zero = real_k(&mut a, 0);
        let y_is_zero = a.eq(y, zero).unwrap();
        let q = a.real_div(x, y).unwrap();
        let five = real_k(&mut a, 5);
        let eq = a.eq(q, five).unwrap();
        let ax = ax_decide(&mut a, &[y_is_zero, eq]);

        let zx = Real::new_const("x");
        let zy = Real::new_const("y");
        let zq = zx / zy.clone();
        let z3 = z3_decide_bools(&[
            zy.eq(Real::from_rational(0, 1)),
            zq.eq(Real::from_rational(5, 1)),
        ]);
        assert!(
            !(matches!(
                (ax, z3),
                (Verdict::Unsat, Verdict::Sat) | (Verdict::Sat, Verdict::Unsat)
            )),
            "y=0 ∧ (/ x y)=5: axeyum={ax:?}, Z3={z3:?} — pinned /0 must not be refuted"
        );
    }
    // (b) conflicting pair under y = 0 → UNSAT (congruence).
    {
        let mut a = TermArena::new();
        let x = {
            let s = a.declare("x", Sort::Real).unwrap();
            a.var(s)
        };
        let y = {
            let s = a.declare("y", Sort::Real).unwrap();
            a.var(s)
        };
        let zero = real_k(&mut a, 0);
        let y_is_zero = a.eq(y, zero).unwrap();
        let q = a.real_div(x, y).unwrap();
        let five = real_k(&mut a, 5);
        let six = real_k(&mut a, 6);
        let e5 = a.eq(q, five).unwrap();
        let e6 = a.eq(q, six).unwrap();
        let ax = ax_decide(&mut a, &[y_is_zero, e5, e6]);

        let zx = Real::new_const("x");
        let zy = Real::new_const("y");
        let zq = zx / zy.clone();
        let z3 = z3_decide_bools(&[
            zy.eq(Real::from_rational(0, 1)),
            zq.eq(Real::from_rational(5, 1)),
            zq.eq(Real::from_rational(6, 1)),
        ]);
        assert!(
            !(matches!(
                (ax, z3),
                (Verdict::Unsat, Verdict::Sat) | (Verdict::Sat, Verdict::Unsat)
            )),
            "y=0 ∧ (/ x y)=5 ∧ (/ x y)=6: axeyum={ax:?}, Z3={z3:?} — congruence must hold"
        );
    }
}
