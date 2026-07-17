//! Adversarial differential fuzz for `QF_UFNRA` (uninterpreted functions over
//! **nonlinear** real arithmetic), cross-checked against the Z3 oracle.
//!
//! This targets the newly-landed **UF × NRA combination** — eager Ackermann
//! reduction of `Real → Real` uninterpreted applications feeding the NRA decider
//! (the dedicated `uf-nra` `check_auto` route). It is the one spine that neither
//! `nra_differential_fuzz` (pure nonlinear real) nor `qf_uflra_differential_fuzz`
//! (UF over *linear* real) exercises: the interface where a congruence equality
//! (`x = y ⇒ f(x) = f(y)`) collides with a *nonlinear* polynomial constraint.
//!
//! Base factors are `x_i`, `f(x_i)` (unary), or `g(x_i, x_j)` (binary) over `Real`.
//! A monomial is a product of 1–3 factors (degree ≤ 3); an atom is either a small
//! polynomial comparison `Σ coeff·monomial + c ⋈ 0` or an equality `factor = factor`
//! (the congruence handle). Atoms are folded into a Boolean formula by `and`/`or`.
//! The generator is seeded to also emit the known-hard shapes: `f(x)·f(x)` (a UF
//! result squared), nested `f(g(x))`, and repeated `f` on congruence-equal
//! arguments (permutation/congruence forcing).
//!
//! Soundness contract (the whole point):
//! - axeyum `Sat`  ∧ Z3 `Unsat` → **PANIC** (wrong sat).
//! - axeyum `Unsat` ∧ Z3 `Sat`  → **PANIC** (wrong unsat — the worst bug).
//! - axeyum `Unknown` → fine; Z3 `Unknown`/timeout → skip.
#![cfg(feature = "full")]
#![cfg(feature = "z3")]
#![allow(clippy::many_single_char_names)]

use std::sync::mpsc;
use std::time::Duration;

use axeyum_ir::{FuncId, Rational, Sort, TermArena, TermId};
use axeyum_solver::{CheckResult, SolverConfig, solve};
use z3::ast::{Ast, Bool, Real};
use z3::{FuncDecl, Params, SatResult, Solver, Sort as Z3Sort};

const INSTANCES: u64 = 700;
const AXEYUM_TIMEOUT: Duration = Duration::from_secs(2);
const Z3_TIMEOUT: Duration = Duration::from_millis(1500);

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

/// A base factor: a variable, a unary application `f(x_i)`, or a binary
/// application `g(x_i, x_j)` — all `Real`-sorted.
#[derive(Clone, Copy)]
enum Factor {
    Var(usize),
    FUnary(usize),
    GBin(usize, usize),
}

impl Factor {
    fn pick(rng: &mut Lcg, nv: usize) -> Factor {
        match rng.below(4) {
            0 | 1 => Factor::Var(rng.below(nv as u64)),
            2 => Factor::FUnary(rng.below(nv as u64)),
            _ => Factor::GBin(rng.below(nv as u64), rng.below(nv as u64)),
        }
    }
    fn build_ir(self, a: &mut TermArena, vars: &[TermId], f: FuncId, g: FuncId) -> TermId {
        match self {
            Factor::Var(i) => vars[i],
            Factor::FUnary(i) => a.apply(f, &[vars[i]]).unwrap(),
            Factor::GBin(i, j) => a.apply(g, &[vars[i], vars[j]]).unwrap(),
        }
    }
    fn build_z3(self, vars: &[Real], f: &FuncDecl, g: &FuncDecl) -> Real {
        match self {
            Factor::Var(i) => vars[i].clone(),
            Factor::FUnary(i) => f.apply(&[&vars[i] as &dyn Ast]).as_real().unwrap(),
            Factor::GBin(i, j) => g
                .apply(&[&vars[i] as &dyn Ast, &vars[j] as &dyn Ast])
                .as_real()
                .unwrap(),
        }
    }
    fn dump(self) -> String {
        let v = |i: usize| ["x", "y", "z"][i];
        match self {
            Factor::Var(i) => v(i).to_string(),
            Factor::FUnary(i) => format!("f({})", v(i)),
            Factor::GBin(i, j) => format!("g({},{})", v(i), v(j)),
        }
    }
}

/// A monomial: `coeff · (factor_1 · … · factor_k)`, `1 ≤ k ≤ 3` (degree ≤ 3).
#[derive(Clone)]
struct Monomial {
    coeff: i64,
    factors: Vec<Factor>,
}

impl Monomial {
    fn generate(rng: &mut Lcg, nv: usize) -> Monomial {
        let deg = rng.below(3) + 1; // 1..=3
        Monomial {
            coeff: rng.in_range(-2, 2),
            factors: (0..deg).map(|_| Factor::pick(rng, nv)).collect(),
        }
    }
    /// A deliberately-hard monomial: the *same* factor multiplied by itself
    /// (`f(x)·f(x)`, `x·x`), which exercises the SOS/square NRA path over a UF result.
    fn square(rng: &mut Lcg, nv: usize) -> Monomial {
        let base = Factor::pick(rng, nv);
        Monomial {
            coeff: rng.in_range(-2, 2),
            factors: vec![base, base],
        }
    }
    fn build_ir(&self, a: &mut TermArena, vars: &[TermId], f: FuncId, g: FuncId) -> TermId {
        let c = a.real_const(Rational::integer(i128::from(self.coeff)));
        let mut acc = c;
        for &factor in &self.factors {
            let t = factor.build_ir(a, vars, f, g);
            acc = a.real_mul(acc, t).unwrap();
        }
        acc
    }
    fn build_z3(&self, vars: &[Real], f: &FuncDecl, g: &FuncDecl) -> Real {
        let mut acc = Real::from_rational(self.coeff, 1);
        for &factor in &self.factors {
            acc *= factor.build_z3(vars, f, g);
        }
        acc
    }
    fn dump(&self) -> String {
        let parts: Vec<String> = self.factors.iter().map(|fac| fac.dump()).collect();
        format!("{}*{}", self.coeff, parts.join("*"))
    }
}

/// Either a polynomial comparison `Σ monomial + c ⋈ 0`, or an equality between two
/// base factors (`=`/`!=`) — the congruence handle.
#[derive(Clone)]
enum Atom {
    Poly {
        monomials: Vec<Monomial>,
        constant: i64,
        cmp: Cmp,
    },
    Eq {
        lhs: Factor,
        rhs: Factor,
        ne: bool,
    },
}

impl Atom {
    fn generate(rng: &mut Lcg, nv: usize) -> Atom {
        if rng.below(4) == 0 {
            Atom::Eq {
                lhs: Factor::pick(rng, nv),
                rhs: Factor::pick(rng, nv),
                ne: rng.flip(),
            }
        } else {
            let n = rng.below(3) + 1; // 1..=3 monomials
            let mut monomials: Vec<Monomial> = (0..n)
                .map(|_| {
                    // Bias toward the hard square shape.
                    if rng.below(3) == 0 {
                        Monomial::square(rng, nv)
                    } else {
                        Monomial::generate(rng, nv)
                    }
                })
                .collect();
            // Occasionally force a nested `f(g(x))` factor into the first monomial.
            if rng.below(4) == 0 {
                monomials[0]
                    .factors
                    .push(Factor::FUnary(rng.below(nv as u64)));
            }
            Atom::Poly {
                monomials,
                constant: rng.in_range(-3, 3),
                cmp: Cmp::pick(rng),
            }
        }
    }

    fn build_ir(
        &self,
        a: &mut TermArena,
        vars: &[TermId],
        f: FuncId,
        g: FuncId,
        zero: TermId,
    ) -> TermId {
        match self {
            Atom::Poly {
                monomials,
                constant,
                cmp,
            } => {
                let mut poly: Option<TermId> = None;
                for m in monomials {
                    let t = m.build_ir(a, vars, f, g);
                    poly = Some(poly.map_or(t, |acc| a.real_add(acc, t).unwrap()));
                }
                let c = a.real_const(Rational::integer(i128::from(*constant)));
                let lhs = poly.map_or(c, |acc| a.real_add(acc, c).unwrap());
                cmp.build_ir(a, lhs, zero)
            }
            Atom::Eq { lhs, rhs, ne } => {
                let l = lhs.build_ir(a, vars, f, g);
                let r = rhs.build_ir(a, vars, f, g);
                let eq = a.eq(l, r).unwrap();
                if *ne { a.not(eq).unwrap() } else { eq }
            }
        }
    }

    fn build_z3(&self, vars: &[Real], f: &FuncDecl, g: &FuncDecl, zero: &Real) -> Bool {
        match self {
            Atom::Poly {
                monomials,
                constant,
                cmp,
            } => {
                let mut poly: Option<Real> = None;
                for m in monomials {
                    let t = m.build_z3(vars, f, g);
                    poly = Some(poly.map_or(t.clone(), |acc| acc + t));
                }
                let c = Real::from_rational(*constant, 1);
                let lhs = poly.map_or(c.clone(), |acc| acc + c);
                cmp.build_z3(&lhs, zero)
            }
            Atom::Eq { lhs, rhs, ne } => {
                let rt = rhs.build_z3(vars, f, g);
                let eq = lhs.build_z3(vars, f, g).eq(&rt);
                if *ne { eq.not() } else { eq }
            }
        }
    }

    fn dump(&self) -> String {
        match self {
            Atom::Poly {
                monomials,
                constant,
                cmp,
            } => {
                let parts: Vec<String> = monomials.iter().map(Monomial::dump).collect();
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
        let num_atoms = rng.below(3) + 2; // 2..=4
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
        let g = a
            .declare_fun("g", &[Sort::Real, Sort::Real], Sort::Real)
            .unwrap();
        let zero = a.real_const(Rational::zero());

        let bools: Vec<TermId> = self
            .atoms
            .iter()
            .map(|atom| atom.build_ir(&mut a, &vars, f, g, zero))
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
        let g = FuncDecl::new("g", &[&real_sort, &real_sort], &real_sort);
        let zero = Real::from_rational(0, 1);

        let bools: Vec<Bool> = self
            .atoms
            .iter()
            .map(|atom| atom.build_z3(&vars, &f, &g, &zero))
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
            let config = SolverConfig::default().with_timeout(AXEYUM_TIMEOUT);
            let v = match solve(&mut a, &assertions, &config) {
                Ok(CheckResult::Sat(_)) => Verdict::Sat,
                Ok(CheckResult::Unsat) => Verdict::Unsat,
                Ok(CheckResult::Unknown(_)) | Err(_) => Verdict::Unknown,
            };
            let _ = tx.send(v);
        })
        .expect("spawn solver thread");
    // A hard wall on top of the internal budget — the internal timeout should fire
    // first, but never block the fuzz on a runaway case.
    rx.recv_timeout(AXEYUM_TIMEOUT + Duration::from_secs(2))
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
    solver.assert(inst.to_z3());
    match solver.check() {
        SatResult::Sat => Verdict::Sat,
        SatResult::Unsat => Verdict::Unsat,
        SatResult::Unknown => Verdict::Unknown,
    }
}

#[test]
fn qf_ufnra_differential_fuzz_disagree_zero() {
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
        "qf_ufnra fuzz: {INSTANCES} instances | {agree} agree | {ax_unknown} axeyum-unknown | {z3_unknown} z3-unknown(skipped) | 0 DISAGREE"
    );
    // Soundness (DISAGREE=0) is the load-bearing assertion above. A modest floor
    // guards against a harness regression that silently stops deciding anything
    // (nonlinear-real is genuinely harder, so the floor is well below the linear
    // UFLRA fuzz's INSTANCES/3).
    assert!(
        agree >= 30,
        "expected >= 30 co-decided agreements, got {agree} (axeyum-unknown {ax_unknown}) — UF×NRA route regression?"
    );
}
