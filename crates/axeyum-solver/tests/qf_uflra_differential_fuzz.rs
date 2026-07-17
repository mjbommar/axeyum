//! Adversarial differential fuzz for `QF_UFLRA` (uninterpreted functions over
//! linear real arithmetic), cross-checked against the Z3 oracle.
//!
//! This targets the recently-landed **online EUF+LRA Nelson-Oppen combination**
//! — now the default `check_auto` route for mixed UF+real-arithmetic. It is the
//! one spine that neither `qf_lra_` (pure linear real) nor `qf_uf_` (pure
//! congruence) exercises: the interface where an equality the LRA solver derives
//! over a shared term (`x = y`) must propagate to congruence (`f(x) = f(y)`), and
//! vice versa. `uflia_` covers the integer combination; this covers the real one.
//!
//! Base terms are `x_i` or `f(x_i)` over `Real`; atoms are either a linear
//! comparison `Σ coeff·base + c ⋈ 0` (mixing real arithmetic with uninterpreted
//! `f`-applications the LRA treats as fresh reals) or an equality `base = base`
//! (the congruence handle). Atoms are folded into a Boolean formula by `and`/`or`.
//!
//! Soundness contract:
//! - axeyum `Sat`  ∧ Z3 `Unsat` → **PANIC** (wrong sat).
//! - axeyum `Unsat` ∧ Z3 `Sat`  → **PANIC** (wrong unsat — the worst bug).
//! - axeyum `Unknown` → fine; Z3 `Unknown`/timeout → skip.
#![cfg(feature = "full")]
#![cfg(feature = "z3")]

use std::sync::mpsc;
use std::time::Duration;

use axeyum_ir::{FuncId, Rational, Sort, TermArena, TermId};
use axeyum_solver::{CheckResult, SolverConfig, solve};
use z3::ast::{Ast, Bool, Real};
use z3::{FuncDecl, Params, SatResult, Solver, Sort as Z3Sort};

const INSTANCES: u64 = 1500;
const AXEYUM_TIMEOUT: Duration = Duration::from_secs(3);
const Z3_TIMEOUT: Duration = Duration::from_secs(2);

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

/// A base term: `x_i` (`applied = false`) or `f(x_i)` (`applied = true`).
#[derive(Clone, Copy)]
struct Base {
    var: usize,
    applied: bool,
}

impl Base {
    fn pick(rng: &mut Lcg, num_vars: usize) -> Base {
        Base {
            var: rng.below(num_vars as u64),
            applied: rng.flip(),
        }
    }
    fn build_ir(self, a: &mut TermArena, vars: &[TermId], f: FuncId) -> TermId {
        if self.applied {
            a.apply(f, &[vars[self.var]]).unwrap()
        } else {
            vars[self.var]
        }
    }
    fn build_z3(self, vars: &[Real], f: &FuncDecl) -> Real {
        if self.applied {
            f.apply(&[&vars[self.var] as &dyn Ast]).as_real().unwrap()
        } else {
            vars[self.var].clone()
        }
    }
    fn dump(self) -> String {
        let v = ["x", "y", "z"][self.var];
        if self.applied {
            format!("f({v})")
        } else {
            v.to_string()
        }
    }
}

/// Either a linear comparison `Σ coeff·base + c ⋈ 0`, or an equality between two
/// base terms (`= ` or `!=`) — the congruence handle.
#[derive(Clone)]
enum Atom {
    Arith {
        terms: Vec<(i64, Base)>,
        constant: i64,
        cmp: Cmp,
    },
    Eq {
        lhs: Base,
        rhs: Base,
        ne: bool,
    },
}

impl Atom {
    fn generate(rng: &mut Lcg, num_vars: usize) -> Atom {
        if rng.flip() {
            let n = rng.below(3) + 1; // 1..=3
            Atom::Arith {
                terms: (0..n)
                    .map(|_| (rng.in_range(-3, 3), Base::pick(rng, num_vars)))
                    .collect(),
                constant: rng.in_range(-3, 3),
                cmp: Cmp::pick(rng),
            }
        } else {
            Atom::Eq {
                lhs: Base::pick(rng, num_vars),
                rhs: Base::pick(rng, num_vars),
                ne: rng.flip(),
            }
        }
    }

    fn build_ir(&self, a: &mut TermArena, vars: &[TermId], f: FuncId, zero: TermId) -> TermId {
        match self {
            Atom::Arith {
                terms,
                constant,
                cmp,
            } => {
                let mut poly: Option<TermId> = None;
                for &(coeff, base) in terms {
                    let c = a.real_const(Rational::integer(i128::from(coeff)));
                    let b = base.build_ir(a, vars, f);
                    let term = a.real_mul(c, b).unwrap();
                    poly = Some(poly.map_or(term, |acc| a.real_add(acc, term).unwrap()));
                }
                let c = a.real_const(Rational::integer(i128::from(*constant)));
                let lhs = poly.map_or(c, |acc| a.real_add(acc, c).unwrap());
                cmp.build_ir(a, lhs, zero)
            }
            Atom::Eq { lhs, rhs, ne } => {
                let l = lhs.build_ir(a, vars, f);
                let r = rhs.build_ir(a, vars, f);
                let eq = a.eq(l, r).unwrap();
                if *ne { a.not(eq).unwrap() } else { eq }
            }
        }
    }

    fn build_z3(&self, vars: &[Real], f: &FuncDecl, zero: &Real) -> Bool {
        match self {
            Atom::Arith {
                terms,
                constant,
                cmp,
            } => {
                let mut poly: Option<Real> = None;
                for &(coeff, base) in terms {
                    let term = Real::from_rational(coeff, 1) * base.build_z3(vars, f);
                    poly = Some(poly.map_or(term.clone(), |acc| acc + term));
                }
                let c = Real::from_rational(*constant, 1);
                let lhs = poly.map_or(c.clone(), |acc| acc + c);
                cmp.build_z3(&lhs, zero)
            }
            Atom::Eq { lhs, rhs, ne } => {
                let rt = rhs.build_z3(vars, f);
                let eq = lhs.build_z3(vars, f).eq(&rt);
                if *ne { eq.not() } else { eq }
            }
        }
    }

    fn dump(&self) -> String {
        match self {
            Atom::Arith {
                terms,
                constant,
                cmp,
            } => {
                let parts: Vec<String> = terms
                    .iter()
                    .map(|(c, b)| format!("{c}*{}", b.dump()))
                    .collect();
                format!("{} + {constant} {} 0", parts.join(" + "), cmp.symbol())
            }
            Atom::Eq { lhs, rhs, ne } => {
                let op = if *ne { "!=" } else { "=" };
                format!("{} {op} {}", lhs.dump(), rhs.dump())
            }
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
        let num_vars = rng.below(2) + 2; // 2..=3
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
        let names = ["x", "y", "z"];
        let vars: Vec<TermId> = (0..self.num_vars)
            .map(|i| {
                let s = a.declare(names[i], Sort::Real).unwrap();
                a.var(s)
            })
            .collect();
        let f = a.declare_fun("f", &[Sort::Real], Sort::Real).unwrap();
        let zero = a.real_const(Rational::zero());

        let bools: Vec<TermId> = self
            .atoms
            .iter()
            .map(|atom| atom.build_ir(&mut a, &vars, f, zero))
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
        let names = ["x", "y", "z"];
        let vars: Vec<Real> = (0..self.num_vars)
            .map(|i| Real::new_const(names[i]))
            .collect();
        let real_sort = Z3Sort::real();
        let f = FuncDecl::new("f", &[&real_sort], &real_sort);
        let zero = Real::from_rational(0, 1);

        let bools: Vec<Bool> = self
            .atoms
            .iter()
            .map(|atom| atom.build_z3(&vars, &f, &zero))
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
            "vars: {}",
            ["x", "y", "z"][..self.num_vars].join(", ")
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
fn qf_uflra_differential_fuzz_disagree_zero() {
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
        "qf_uflra fuzz: {INSTANCES} instances | {agree} agree | {ax_unknown} axeyum-unknown | {z3_unknown} z3-unknown(skipped) | 0 DISAGREE"
    );
    assert!(
        agree >= INSTANCES / 3,
        "expected >= {} agreements, got {agree} (axeyum-unknown {ax_unknown}) — UFLRA combination regression?",
        INSTANCES / 3
    );
}
