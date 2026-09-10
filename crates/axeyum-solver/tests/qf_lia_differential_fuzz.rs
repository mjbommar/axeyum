//! Adversarial differential fuzz for **pure `QF_LIA`** (quantifier-free linear
//! integer arithmetic) against the Z3 oracle.
//!
//! # Why this suite exists
//!
//! The three differential fuzzes that existed before this one
//! (`qf_lra_differential_fuzz`, `simplex_lra_fallback_differential`,
//! `qf_uflra_differential_fuzz`) are all **real**-arithmetic fuzzes. Pure
//! integer linear arithmetic — the LIA branch-and-bound / cut routes,
//! `lia_gcd`'s divisibility refutation, and the `int_real_relax` relaxation —
//! had no oracle cross-check at all. Its sibling suite
//! `difference_logic_differential_fuzz` covers only the unit-coefficient
//! fragment; this one deliberately generates **general** coefficients, so
//! `dl-online` declines and the LIA routes decide.
//!
//! # THIS SUITE COMPILES TO ZERO TESTS WITHOUT `--features z3`
//!
//! The file is `#![cfg(feature = "z3")]`. Built without that feature it is an
//! **empty binary**: `cargo test` prints `running 0 tests ... ok` and exits
//! `0` — a green-looking gate that checks nothing. Run it as
//!
//! ```text
//! cargo test -p axeyum-solver --features z3 --test qf_lia_differential_fuzz
//! ```
//!
//! and **confirm a nonzero test count** before believing the result.
//!
//! # Soundness contract
//!
//! - axeyum `Sat`   ∧ Z3 `Unsat` → **PANIC** (wrong sat).
//! - axeyum `Unsat` ∧ Z3 `Sat`   → **PANIC** (wrong unsat — the worst bug).
//! - axeyum `Unknown` → fine (sound-incomplete is allowed).
//! - Z3 `Unknown`/timeout → skip (cannot adjudicate).
//!
//! # Degenerate-case coverage (the Hard Rule)
//!
//! `QF_LIA` carries the repository's canonical underspecified operators:
//! **integer `div` and `mod` by zero**. SMT-LIB leaves both *underspecified but
//! functionally consistent* — any total value, the same one for the same
//! arguments. A wrong-unsat shipped (`a946f925`) because `div`/`mod` by a
//! **constant** zero was folded to a fixed convention while the differential
//! fuzz that "passed" only ever emitted *variable* divisors, so it structurally
//! could not generate `(div x 0)`. This generator emits, as separate branches:
//!
//! | corner class | shape | why it is degenerate |
//! |---|---|---|
//! | `DivByConstZero` | `(div p 0) ⋈ c` | the literal `a946f925` shape: a **constant** `0` divisor |
//! | `ModByConstZero` | `(mod p 0) ⋈ c` | the same, on the other underspecified operator |
//! | `DivZeroCongruence` | `(div p 0) = a` ∧ `(div p 0) = b`, `a ≠ b` | underspecified but **functionally consistent** — this MUST be unsat, and a fold to a fixed value makes it unsat for the wrong reason |
//! | `DivByVar` | `(div p y) ⋈ c` with `y` pinnable to `0` by another atom | the divisor reaches `0` through the solver, not the parser |
//! | `ModByVar` | `(mod p y) ⋈ c`, same | |
//! | `GcdInfeasible` | `2x + 4y = odd` | `lia_gcd`'s divisibility refutation: real-feasible, integer-infeasible |
//! | `GcdFeasible` | `2x + 4y = even` | the satisfiable companion, so a blanket `unsat` cannot pass the pair |
//! | `ZeroCoefficient` | every coefficient `0` | the polynomial collapses to a constant comparison |
//! | `ExtremeConstant` | `\|c\|` within 4 of `i64::MIN` / `i64::MAX` | large magnitudes and their sums |
//! | `StrictTightening` | `3x < 4` | integer tightening `3x ≤ 3`, exactly where an off-by-one lives |
//! | `Disequality` | `¬(2x + 3y = c)` | a disjunction of two half-spaces, not a single one |
//! | `AbsWrap` | `\|p\| ⋈ c` | a case split the linear routes cannot express directly |
//!
//! One of these is **mandatory** per instance (`seed % CORNERS.len()`), so
//! coverage is a property of the seed schedule and not of luck, and
//! [`corner_coverage_is_total`] fails if any class stops being emitted.
//!
//! # Determinism
//!
//! One seeded LCG per instance, seeded from the instance index. No clock, no
//! entropy, no hash-map iteration in any generated structure. A failure prints
//! its seed and a full textual dump.
#![cfg(feature = "z3")]

use std::collections::BTreeMap;
use std::sync::mpsc;
use std::time::Duration;

use axeyum_ir::{Sort, TermArena, TermId, render};
use axeyum_solver::{
    CheckResult, RouteAttributionGuard, SolverConfig, last_route_attribution, solve,
};
use z3::ast::{Bool, Int};
use z3::{Params, SatResult, Solver};

const INSTANCES: u64 = 960;
const AXEYUM_TIMEOUT: Duration = Duration::from_secs(5);
const Z3_TIMEOUT: Duration = Duration::from_secs(3);

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

// ---------------------------------------------------------------------------
// The generated fragment
// ---------------------------------------------------------------------------

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Rel {
    Lt,
    Le,
    Gt,
    Ge,
    Eq,
}

impl Rel {
    fn pick(rng: &mut Lcg) -> Rel {
        match rng.below(5) {
            0 => Rel::Lt,
            1 => Rel::Le,
            2 => Rel::Gt,
            3 => Rel::Ge,
            _ => Rel::Eq,
        }
    }
    fn symbol(self) -> &'static str {
        match self {
            Rel::Lt => "<",
            Rel::Le => "<=",
            Rel::Gt => ">",
            Rel::Ge => ">=",
            Rel::Eq => "=",
        }
    }
}

/// The right operand of a `div`/`mod` wrap.
///
/// `Const(0)` is a **separate branch** from `Var`, on purpose: that separation
/// is exactly what the `a946f925` fuzz lacked.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Divisor {
    Const(i64),
    Var(usize),
}

/// An optional operator wrapped around an atom's linear left-hand side.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Wrap {
    Div(Divisor),
    Mod(Divisor),
    Abs,
}

/// `wrap(Σ coeff_i·x_i + constant) ⋈ rhs`, optionally negated.
#[derive(Clone, Debug)]
struct LinAtom {
    terms: Vec<(i64, usize)>,
    constant: i64,
    wrap: Option<Wrap>,
    rel: Rel,
    rhs: i64,
    neg: bool,
}

/// The propositional skeleton over atom indices.
#[derive(Clone, Debug)]
enum Node {
    Atom(usize),
    Not(Box<Node>),
    And(Box<Node>, Box<Node>),
    Or(Box<Node>, Box<Node>),
    Implies(Box<Node>, Box<Node>),
    Xor(Box<Node>, Box<Node>),
    Ite(Box<Node>, Box<Node>, Box<Node>),
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
enum Corner {
    DivByConstZero,
    ModByConstZero,
    DivZeroCongruence,
    DivByVar,
    ModByVar,
    GcdInfeasible,
    GcdFeasible,
    ZeroCoefficient,
    ExtremeConstant,
    StrictTightening,
    Disequality,
    AbsWrap,
}

/// The number of `Corner` **variants**, pinned deliberately: [`CORNERS`] is
/// both the seed schedule and the coverage authority, so a comparison against
/// `CORNERS.len()` alone would move with a deletion and catch nothing. The
/// exhaustive `match`es over `Corner` force a NEW variant to be handled; this
/// constant forces a deletion from the schedule to be noticed.
const CORNER_VARIANT_COUNT: usize = 12;

/// Order is load-bearing: the mandatory corner for seed `s` is
/// `CORNERS[s % CORNERS.len()]`, so this list *is* the coverage schedule.
const CORNERS: [Corner; CORNER_VARIANT_COUNT] = [
    Corner::DivByConstZero,
    Corner::ModByConstZero,
    Corner::DivZeroCongruence,
    Corner::DivByVar,
    Corner::ModByVar,
    Corner::GcdInfeasible,
    Corner::GcdFeasible,
    Corner::ZeroCoefficient,
    Corner::ExtremeConstant,
    Corner::StrictTightening,
    Corner::Disequality,
    Corner::AbsWrap,
];

impl Corner {
    fn name(self) -> &'static str {
        match self {
            Corner::DivByConstZero => "DivByConstZero",
            Corner::ModByConstZero => "ModByConstZero",
            Corner::DivZeroCongruence => "DivZeroCongruence",
            Corner::DivByVar => "DivByVar",
            Corner::ModByVar => "ModByVar",
            Corner::GcdInfeasible => "GcdInfeasible",
            Corner::GcdFeasible => "GcdFeasible",
            Corner::ZeroCoefficient => "ZeroCoefficient",
            Corner::ExtremeConstant => "ExtremeConstant",
            Corner::StrictTightening => "StrictTightening",
            Corner::Disequality => "Disequality",
            Corner::AbsWrap => "AbsWrap",
        }
    }

    /// Emits the atoms this corner is defined by and returns a skeleton node
    /// mentioning them, so the corner cannot be generated and then dropped.
    fn emit(self, rng: &mut Lcg, num_vars: usize, atoms: &mut Vec<LinAtom>) -> Node {
        let push = |atoms: &mut Vec<LinAtom>, a: LinAtom| {
            atoms.push(a);
            atoms.len() - 1
        };
        let poly = |rng: &mut Lcg| -> Vec<(i64, usize)> {
            let n = rng.below(2) + 1;
            (0..n)
                .map(|_| (rng.in_range(-4, 4), rng.below(num_vars as u64)))
                .collect()
        };
        match self {
            Corner::DivByConstZero => {
                let i = push(
                    atoms,
                    LinAtom {
                        terms: poly(rng),
                        constant: rng.in_range(-3, 3),
                        wrap: Some(Wrap::Div(Divisor::Const(0))),
                        rel: Rel::pick(rng),
                        rhs: rng.in_range(-3, 3),
                        neg: rng.flip(),
                    },
                );
                Node::Atom(i)
            }
            Corner::ModByConstZero => {
                let i = push(
                    atoms,
                    LinAtom {
                        terms: poly(rng),
                        constant: rng.in_range(-3, 3),
                        wrap: Some(Wrap::Mod(Divisor::Const(0))),
                        rel: Rel::pick(rng),
                        rhs: rng.in_range(-3, 3),
                        neg: rng.flip(),
                    },
                );
                Node::Atom(i)
            }
            Corner::DivZeroCongruence => {
                // The SAME `(div p 0)` term compared against two DIFFERENT
                // constants. `div` by `0` is underspecified but **functionally
                // consistent**, so this conjunction is unsat for every solver
                // that respects congruence — and a fold to a fixed convention
                // gets the right answer here for the wrong reason, which the
                // companion `sat` shape below then catches.
                let terms = poly(rng);
                let constant = rng.in_range(-3, 3);
                let a = rng.in_range(-5, 5);
                let b = if rng.flip() { a } else { a + 1 };
                let i = push(
                    atoms,
                    LinAtom {
                        terms: terms.clone(),
                        constant,
                        wrap: Some(Wrap::Div(Divisor::Const(0))),
                        rel: Rel::Eq,
                        rhs: a,
                        neg: false,
                    },
                );
                let j = push(
                    atoms,
                    LinAtom {
                        terms,
                        constant,
                        wrap: Some(Wrap::Div(Divisor::Const(0))),
                        rel: Rel::Eq,
                        rhs: b,
                        neg: false,
                    },
                );
                Node::And(Box::new(Node::Atom(i)), Box::new(Node::Atom(j)))
            }
            Corner::DivByVar => {
                // A variable divisor, plus an atom that can pin it to `0`.
                let d = rng.below(num_vars as u64);
                let i = push(
                    atoms,
                    LinAtom {
                        terms: poly(rng),
                        constant: rng.in_range(-3, 3),
                        wrap: Some(Wrap::Div(Divisor::Var(d))),
                        rel: Rel::pick(rng),
                        rhs: rng.in_range(-3, 3),
                        neg: rng.flip(),
                    },
                );
                let pin = push(
                    atoms,
                    LinAtom {
                        terms: vec![(1, d)],
                        constant: 0,
                        wrap: None,
                        rel: Rel::Eq,
                        rhs: 0,
                        neg: rng.flip(),
                    },
                );
                Node::And(Box::new(Node::Atom(i)), Box::new(Node::Atom(pin)))
            }
            Corner::ModByVar => {
                let d = rng.below(num_vars as u64);
                let i = push(
                    atoms,
                    LinAtom {
                        terms: poly(rng),
                        constant: rng.in_range(-3, 3),
                        wrap: Some(Wrap::Mod(Divisor::Var(d))),
                        rel: Rel::pick(rng),
                        rhs: rng.in_range(-3, 3),
                        neg: rng.flip(),
                    },
                );
                let pin = push(
                    atoms,
                    LinAtom {
                        terms: vec![(1, d)],
                        constant: 0,
                        wrap: None,
                        rel: Rel::Eq,
                        rhs: 0,
                        neg: rng.flip(),
                    },
                );
                Node::And(Box::new(Node::Atom(i)), Box::new(Node::Atom(pin)))
            }
            Corner::GcdInfeasible => {
                // `2a·x + 2b·y = odd`: real-feasible, integer-infeasible. This
                // is `lia_gcd`'s whole reason to exist, and the shape a route
                // that only relaxes to the reals gets WRONG.
                let (x, y) = distinct_pair(rng, num_vars);
                let i = push(
                    atoms,
                    LinAtom {
                        terms: vec![(2 * rng.in_range(1, 3), x), (2 * rng.in_range(1, 3), y)],
                        constant: 0,
                        wrap: None,
                        rel: Rel::Eq,
                        rhs: 2 * rng.in_range(-4, 4) + 1,
                        neg: false,
                    },
                );
                Node::Atom(i)
            }
            Corner::GcdFeasible => {
                let (x, y) = distinct_pair(rng, num_vars);
                let i = push(
                    atoms,
                    LinAtom {
                        terms: vec![(2, x), (4, y)],
                        constant: 0,
                        wrap: None,
                        rel: Rel::Eq,
                        rhs: 2 * rng.in_range(-4, 4),
                        neg: false,
                    },
                );
                Node::Atom(i)
            }
            Corner::ZeroCoefficient => {
                let i = push(
                    atoms,
                    LinAtom {
                        terms: (0..=rng.below(2))
                            .map(|_| (0, rng.below(num_vars as u64)))
                            .collect(),
                        constant: rng.in_range(-3, 3),
                        wrap: None,
                        rel: Rel::pick(rng),
                        rhs: rng.in_range(-3, 3),
                        neg: rng.flip(),
                    },
                );
                Node::Atom(i)
            }
            Corner::ExtremeConstant => {
                // Written literally: `in_range(i64::MIN, …)` would overflow.
                let big = match rng.below(4) {
                    0 => i64::MIN + rng.in_range(0, 4),
                    1 => i64::MAX - rng.in_range(0, 4),
                    2 => i64::from(i32::MIN) + rng.in_range(0, 4),
                    _ => i64::from(i32::MAX) - rng.in_range(0, 4),
                };
                let i = push(
                    atoms,
                    LinAtom {
                        terms: vec![(rng.in_range(1, 3), rng.below(num_vars as u64))],
                        constant: 0,
                        wrap: None,
                        rel: Rel::pick(rng),
                        rhs: big,
                        neg: rng.flip(),
                    },
                );
                Node::Atom(i)
            }
            Corner::StrictTightening => {
                // `k·x < c` with `k ∤ c`: integer tightening to `k·x ≤ c-1`,
                // then the floor. An off-by-one here is a wrong verdict.
                let k = rng.in_range(2, 5);
                let i = push(
                    atoms,
                    LinAtom {
                        terms: vec![(k, rng.below(num_vars as u64))],
                        constant: 0,
                        wrap: None,
                        rel: if rng.flip() { Rel::Lt } else { Rel::Gt },
                        rhs: k * rng.in_range(-3, 3) + rng.in_range(1, k - 1),
                        neg: rng.flip(),
                    },
                );
                Node::Atom(i)
            }
            Corner::Disequality => {
                let (x, y) = distinct_pair(rng, num_vars);
                let i = push(
                    atoms,
                    LinAtom {
                        terms: vec![(2, x), (3, y)],
                        constant: 0,
                        wrap: None,
                        rel: Rel::Eq,
                        rhs: rng.in_range(-6, 6),
                        neg: true,
                    },
                );
                Node::Atom(i)
            }
            Corner::AbsWrap => {
                let i = push(
                    atoms,
                    LinAtom {
                        terms: poly(rng),
                        constant: rng.in_range(-3, 3),
                        wrap: Some(Wrap::Abs),
                        rel: Rel::pick(rng),
                        rhs: rng.in_range(-3, 5),
                        neg: rng.flip(),
                    },
                );
                Node::Atom(i)
            }
        }
    }
}

fn distinct_pair(rng: &mut Lcg, num_vars: usize) -> (usize, usize) {
    let x = rng.below(num_vars as u64);
    let mut y = rng.below(num_vars as u64);
    if y == x {
        y = (x + 1) % num_vars;
    }
    (x, y)
}

const VAR_NAMES: [&str; 4] = ["x", "y", "z", "w"];

/// A generated instance. Plain data → `Send`.
#[derive(Clone, Debug)]
struct Instance {
    seed: u64,
    num_vars: usize,
    corner: Corner,
    atoms: Vec<LinAtom>,
    roots: Vec<Node>,
}

impl Instance {
    fn generate(seed: u64) -> Instance {
        let mut rng = Lcg::new(seed);
        let corner = CORNERS[usize::try_from(seed).unwrap_or(0) % CORNERS.len()];
        let num_vars = rng.below(3) + 2; // 2..=4

        let mut atoms = Vec::new();
        let corner_root = corner.emit(&mut rng, num_vars, &mut atoms);

        // Filler: 1..=3 ordinary LIA atoms with general coefficients, so the
        // query is genuinely outside the difference fragment and `dl-online`
        // declines.
        let filler_count = rng.below(3) + 1;
        let mut filler = Vec::with_capacity(filler_count);
        for _ in 0..filler_count {
            let nterms = rng.below(num_vars as u64) + 1;
            atoms.push(LinAtom {
                terms: (0..nterms)
                    .map(|_| (rng.in_range(-4, 4), rng.below(num_vars as u64)))
                    .collect(),
                constant: rng.in_range(-4, 4),
                wrap: None,
                rel: Rel::pick(&mut rng),
                rhs: rng.in_range(-6, 6),
                neg: rng.flip(),
            });
            filler.push(Node::Atom(atoms.len() - 1));
        }
        let mut acc = filler[0].clone();
        for node in filler.iter().skip(1) {
            let (l, r) = (Box::new(acc), Box::new(node.clone()));
            acc = match rng.below(5) {
                0 => Node::And(l, r),
                1 => Node::Or(l, r),
                2 => Node::Implies(l, r),
                3 => Node::Xor(l, r),
                _ => Node::Ite(Box::new(Node::Not(l.clone())), l, r),
            };
        }

        Instance {
            seed,
            num_vars,
            corner,
            atoms,
            roots: vec![corner_root, acc],
        }
    }

    // -- axeyum IR ---------------------------------------------------------

    fn build(&self) -> (TermArena, Vec<TermId>) {
        let mut a = TermArena::new();
        let vars: Vec<TermId> = (0..self.num_vars)
            .map(|i| {
                let s = a.declare(VAR_NAMES[i], Sort::Int).expect("declare");
                a.var(s)
            })
            .collect();
        let atom_terms: Vec<TermId> = self
            .atoms
            .iter()
            .map(|atom| build_atom_ir(&mut a, &vars, atom))
            .collect();
        let assertions = self
            .roots
            .iter()
            .map(|root| build_node_ir(&mut a, root, &atom_terms))
            .collect();
        (a, assertions)
    }

    // -- Z3 ----------------------------------------------------------------

    fn to_z3(&self) -> Vec<Bool> {
        let vars: Vec<Int> = (0..self.num_vars)
            .map(|i| Int::new_const(VAR_NAMES[i]))
            .collect();
        let atom_terms: Vec<Bool> = self
            .atoms
            .iter()
            .map(|atom| build_atom_z3(&vars, atom))
            .collect();
        self.roots
            .iter()
            .map(|root| build_node_z3(root, &atom_terms))
            .collect()
    }

    fn dump(&self) -> String {
        let mut lines = vec![format!(
            "seed {} | corner {} | vars {}",
            self.seed,
            self.corner.name(),
            VAR_NAMES[..self.num_vars].join(", ")
        )];
        for (i, atom) in self.atoms.iter().enumerate() {
            let parts: Vec<String> = atom
                .terms
                .iter()
                .map(|&(c, v)| format!("{c}*{}", VAR_NAMES[v]))
                .collect();
            let body = format!("({} + {})", parts.join(" + "), atom.constant);
            let wrapped = match atom.wrap {
                None => body,
                Some(Wrap::Abs) => format!("(abs {body})"),
                Some(Wrap::Div(d)) => format!("(div {body} {})", divisor_name(d)),
                Some(Wrap::Mod(d)) => format!("(mod {body} {})", divisor_name(d)),
            };
            lines.push(format!(
                "  atom[{i}]: {}({wrapped} {} {})",
                if atom.neg { "NOT " } else { "" },
                atom.rel.symbol(),
                atom.rhs
            ));
        }
        for (i, root) in self.roots.iter().enumerate() {
            lines.push(format!("  assert[{i}]: {}", render_node(root)));
        }
        lines.join("\n")
    }
}

fn divisor_name(d: Divisor) -> String {
    match d {
        Divisor::Const(k) => format!("{k}"),
        Divisor::Var(v) => VAR_NAMES[v].to_string(),
    }
}

fn build_atom_ir(a: &mut TermArena, vars: &[TermId], atom: &LinAtom) -> TermId {
    let mut poly: Option<TermId> = None;
    for &(coeff, v) in &atom.terms {
        let c = a.int_const(i128::from(coeff));
        let term = a.int_mul(c, vars[v]).expect("int_mul");
        poly = Some(poly.map_or(term, |acc| a.int_add(acc, term).expect("int_add")));
    }
    let k = a.int_const(i128::from(atom.constant));
    let mut lhs = poly.map_or(k, |acc| a.int_add(acc, k).expect("int_add"));
    if let Some(wrap) = atom.wrap {
        lhs = match wrap {
            Wrap::Abs => a.int_abs(lhs).expect("int_abs"),
            Wrap::Div(d) => {
                let dt = divisor_ir(a, vars, d);
                a.int_div(lhs, dt).expect("int_div")
            }
            Wrap::Mod(d) => {
                let dt = divisor_ir(a, vars, d);
                a.int_mod(lhs, dt).expect("int_mod")
            }
        };
    }
    let rhs = a.int_const(i128::from(atom.rhs));
    let b = match atom.rel {
        Rel::Lt => a.int_lt(lhs, rhs),
        Rel::Le => a.int_le(lhs, rhs),
        Rel::Gt => a.int_gt(lhs, rhs),
        Rel::Ge => a.int_ge(lhs, rhs),
        Rel::Eq => a.eq(lhs, rhs),
    }
    .expect("relational term");
    if atom.neg { a.not(b).expect("not") } else { b }
}

fn divisor_ir(a: &mut TermArena, vars: &[TermId], d: Divisor) -> TermId {
    match d {
        Divisor::Const(k) => a.int_const(i128::from(k)),
        Divisor::Var(v) => vars[v],
    }
}

fn build_atom_z3(vars: &[Int], atom: &LinAtom) -> Bool {
    let mut poly: Option<Int> = None;
    for &(coeff, v) in &atom.terms {
        let term = Int::mul(&[Int::from_i64(coeff), vars[v].clone()]);
        poly = Some(poly.map_or(term.clone(), |acc| Int::add(&[acc, term])));
    }
    let k = Int::from_i64(atom.constant);
    let mut lhs = poly.map_or(k.clone(), |acc| Int::add(&[acc, k]));
    if let Some(wrap) = atom.wrap {
        let divisor = |d: Divisor| match d {
            Divisor::Const(c) => Int::from_i64(c),
            Divisor::Var(v) => vars[v].clone(),
        };
        lhs = match wrap {
            // SMT-LIB `abs`. Z3's `Int` has no `abs` builder, and the `ite`
            // form is exactly the SMT-LIB definition.
            Wrap::Abs => lhs
                .ge(&Int::from_i64(0))
                .ite(&lhs, &Int::sub(&[Int::from_i64(0), lhs.clone()])),
            // `Z3_mk_div` / `Z3_mk_mod` are SMT-LIB `div` / `mod` verbatim,
            // including the underspecified-by-zero case.
            Wrap::Div(d) => lhs.div(&divisor(d)),
            Wrap::Mod(d) => lhs.modulo(&divisor(d)),
        };
    }
    let rhs = Int::from_i64(atom.rhs);
    let b = match atom.rel {
        Rel::Lt => lhs.lt(&rhs),
        Rel::Le => lhs.le(&rhs),
        Rel::Gt => lhs.gt(&rhs),
        Rel::Ge => lhs.ge(&rhs),
        Rel::Eq => lhs.eq(&rhs),
    };
    if atom.neg { b.not() } else { b }
}

fn build_node_ir(a: &mut TermArena, node: &Node, atoms: &[TermId]) -> TermId {
    match node {
        Node::Atom(i) => atoms[*i],
        Node::Not(x) => {
            let t = build_node_ir(a, x, atoms);
            a.not(t).expect("not")
        }
        Node::And(l, r) => {
            let (l, r) = (build_node_ir(a, l, atoms), build_node_ir(a, r, atoms));
            a.and(l, r).expect("and")
        }
        Node::Or(l, r) => {
            let (l, r) = (build_node_ir(a, l, atoms), build_node_ir(a, r, atoms));
            a.or(l, r).expect("or")
        }
        Node::Implies(l, r) => {
            let (l, r) = (build_node_ir(a, l, atoms), build_node_ir(a, r, atoms));
            a.implies(l, r).expect("implies")
        }
        Node::Xor(l, r) => {
            let (l, r) = (build_node_ir(a, l, atoms), build_node_ir(a, r, atoms));
            a.xor(l, r).expect("xor")
        }
        Node::Ite(c, t, e) => {
            let (c, t, e) = (
                build_node_ir(a, c, atoms),
                build_node_ir(a, t, atoms),
                build_node_ir(a, e, atoms),
            );
            a.ite(c, t, e).expect("ite")
        }
    }
}

fn build_node_z3(node: &Node, atoms: &[Bool]) -> Bool {
    match node {
        Node::Atom(i) => atoms[*i].clone(),
        Node::Not(x) => build_node_z3(x, atoms).not(),
        Node::And(l, r) => Bool::and(&[build_node_z3(l, atoms), build_node_z3(r, atoms)]),
        Node::Or(l, r) => Bool::or(&[build_node_z3(l, atoms), build_node_z3(r, atoms)]),
        Node::Implies(l, r) => build_node_z3(l, atoms).implies(&build_node_z3(r, atoms)),
        Node::Xor(l, r) => build_node_z3(l, atoms).xor(&build_node_z3(r, atoms)),
        Node::Ite(c, t, e) => {
            build_node_z3(c, atoms).ite(&build_node_z3(t, atoms), &build_node_z3(e, atoms))
        }
    }
}

fn render_node(node: &Node) -> String {
    match node {
        Node::Atom(i) => format!("a{i}"),
        Node::Not(x) => format!("(not {})", render_node(x)),
        Node::And(l, r) => format!("(and {} {})", render_node(l), render_node(r)),
        Node::Or(l, r) => format!("(or {} {})", render_node(l), render_node(r)),
        Node::Implies(l, r) => format!("(=> {} {})", render_node(l), render_node(r)),
        Node::Xor(l, r) => format!("(xor {} {})", render_node(l), render_node(r)),
        Node::Ite(c, t, e) => format!(
            "(ite {} {} {})",
            render_node(c),
            render_node(t),
            render_node(e)
        ),
    }
}

// ---------------------------------------------------------------------------
// Adjudication
// ---------------------------------------------------------------------------

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Ax {
    Sat,
    Unsat,
    Unknown,
}

/// What one bounded axeyum solve produced: the verdict, and the label of the
/// route that decided it. The route is recorded so the sweep can *show* which
/// engines it actually exercised, rather than asserting it in prose.
#[derive(Clone, Debug)]
struct AxRun {
    verdict: Ax,
    route: Option<String>,
}

fn solve_axeyum_bounded(inst: Instance) -> AxRun {
    let (tx, rx) = mpsc::channel();
    std::thread::Builder::new()
        .stack_size(256 * 1024 * 1024)
        .spawn(move || {
            let (mut a, assertions) = inst.build();
            let _attribution = RouteAttributionGuard::enable();
            let verdict = match solve(&mut a, &assertions, &SolverConfig::default()) {
                Ok(CheckResult::Sat(_)) => Ax::Sat,
                Ok(CheckResult::Unsat) => Ax::Unsat,
                Ok(CheckResult::Unknown(_)) | Err(_) => Ax::Unknown,
            };
            let route = last_route_attribution()
                .decided_by()
                .map(|(_, attempt, _)| attempt.route.to_string());
            let _ = tx.send(AxRun { verdict, route });
        })
        .expect("spawn solver thread");
    rx.recv_timeout(AXEYUM_TIMEOUT).unwrap_or(AxRun {
        verdict: Ax::Unknown,
        route: None,
    })
}

fn z3_decide(inst: &Instance) -> Ax {
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
        SatResult::Sat => Ax::Sat,
        SatResult::Unsat => Ax::Unsat,
        SatResult::Unknown => Ax::Unknown,
    }
}

/// The single comparison every test here routes through — and therefore the
/// single place a planted wrong answer has to be injected to break the suite.
fn adjudicate(inst: &Instance, ax: Ax, z3: Ax) {
    if matches!((ax, z3), (Ax::Sat, Ax::Unsat) | (Ax::Unsat, Ax::Sat)) {
        panic!(
            "DISAGREEMENT: axeyum = {ax:?}, Z3 = {z3:?}\n\
             reproduce with seed {}\n{}",
            inst.seed,
            inst.dump()
        );
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[test]
fn qf_lia_matches_z3() {
    let mut agree = 0u64;
    let mut ax_unknown = 0u64;
    let mut z3_unknown = 0u64;
    let mut routes: BTreeMap<String, u64> = BTreeMap::new();

    for seed in 0..INSTANCES {
        let inst = Instance::generate(seed);
        let run = solve_axeyum_bounded(inst.clone());
        let z3 = z3_decide(&inst);
        adjudicate(&inst, run.verdict, z3);

        if let Some(route) = &run.route {
            *routes.entry(route.clone()).or_default() += 1;
        }
        match (run.verdict, z3) {
            (Ax::Unknown, _) => ax_unknown += 1,
            (_, Ax::Unknown) => z3_unknown += 1,
            _ => agree += 1,
        }
    }

    println!(
        "qf_lia fuzz: {INSTANCES} instances | {agree} agree | {ax_unknown} axeyum-unknown | \
         {z3_unknown} z3-unknown(skipped) | 0 DISAGREE"
    );
    for (route, n) in &routes {
        println!("  decided by {route:<28} {n:>4}");
    }

    // The `div`/`mod`-by-zero and `abs` corners are legitimately hard, so the
    // floor is a third of the sweep — far above zero, which is what a dispatch
    // or admission regression would produce.
    assert!(
        agree >= INSTANCES / 3,
        "expected >= {} agreements, got {agree} (axeyum-unknown {ax_unknown})",
        INSTANCES / 3
    );
    // And this must be a genuinely different population from
    // `difference_logic_differential_fuzz`: general coefficients mean the
    // difference-logic probe declines and a LIA route decides.
    let non_dl: u64 = routes
        .iter()
        .filter(|(route, _)| route.as_str() != "dl-online")
        .map(|(_, n)| *n)
        .sum();
    assert!(
        non_dl > 0,
        "every decided instance was decided by `dl-online` — this suite is a \
         duplicate of the difference-logic fuzz, not a LIA fuzz"
    );
}

/// The Hard-Rule guard: every corner class in [`CORNERS`] is actually emitted
/// by the seed schedule this sweep uses, and the schedule still lists every
/// variant.
#[test]
fn corner_coverage_is_total() {
    let mut counts: BTreeMap<&'static str, u64> = BTreeMap::new();
    for seed in 0..INSTANCES {
        let inst = Instance::generate(seed);
        *counts.entry(inst.corner.name()).or_default() += 1;
        assert!(
            !inst.atoms.is_empty() && !inst.roots.is_empty(),
            "seed {} produced an empty query",
            inst.seed
        );
    }
    for corner in CORNERS {
        let n = counts.get(corner.name()).copied().unwrap_or(0);
        println!("  {:<20} {n:>4} instances", corner.name());
        assert!(
            n > 0,
            "corner class {} was never generated — the fuzz is blind on it",
            corner.name()
        );
    }
    assert_eq!(
        counts.len(),
        CORNERS.len(),
        "generated corner classes do not match the declared schedule"
    );
    let mut distinct: Vec<Corner> = CORNERS.to_vec();
    distinct.sort_unstable();
    distinct.dedup();
    assert_eq!(
        distinct.len(),
        CORNER_VARIANT_COUNT,
        "the corner schedule lists {} distinct classes, not the {CORNER_VARIANT_COUNT} \
         declared — a class was deleted from `CORNERS` or duplicated",
        distinct.len()
    );

    // The `div`/`mod`-by-CONSTANT-ZERO branch is the `a946f925` shape and the
    // reason this whole section of CLAUDE.md exists. Derive its presence from
    // the generated queries, not from the schedule that claims it.
    let mut const_zero_divisors = 0u64;
    let mut var_divisors = 0u64;
    for seed in 0..INSTANCES {
        for atom in &Instance::generate(seed).atoms {
            match atom.wrap {
                Some(Wrap::Div(Divisor::Const(0)) | Wrap::Mod(Divisor::Const(0))) => {
                    const_zero_divisors += 1;
                }
                Some(Wrap::Div(Divisor::Var(_)) | Wrap::Mod(Divisor::Var(_))) => {
                    var_divisors += 1;
                }
                _ => {}
            }
        }
    }
    println!(
        "  div/mod by CONSTANT 0: {const_zero_divisors} atoms | by a VARIABLE: {var_divisors} atoms"
    );
    assert!(
        const_zero_divisors > 0,
        "no `div`/`mod` by a CONSTANT zero was generated — this is exactly the \
         blindness that shipped the `a946f925` wrong-unsat"
    );
    assert!(
        var_divisors > 0,
        "no `div`/`mod` by a variable divisor was generated"
    );
}

/// Hand-written, named degenerate queries whose verdict is fixed by SMT-LIB
/// semantics, cross-checked against Z3.
#[test]
fn named_degenerate_cases_match_z3() {
    let cases: &[(&str, usize, Vec<LinAtom>, Vec<Node>)] = &[
        (
            // `div` by a CONSTANT zero is UNDERSPECIFIED, not an error and not
            // a fixed convention: `(div x 0) = 5` is SATISFIABLE. A solver that
            // folded it to, say, `0` would answer `unsat` — the `a946f925` bug.
            "div_by_const_zero_is_satisfiable",
            2,
            vec![atom(
                vec![(1, 0)],
                0,
                Some(Wrap::Div(Divisor::Const(0))),
                Rel::Eq,
                5,
                false,
            )],
            vec![Node::Atom(0)],
        ),
        (
            "mod_by_const_zero_is_satisfiable",
            2,
            vec![atom(
                vec![(1, 0)],
                0,
                Some(Wrap::Mod(Divisor::Const(0))),
                Rel::Eq,
                7,
                false,
            )],
            vec![Node::Atom(0)],
        ),
        (
            // …but it IS functionally consistent: the same term cannot take two
            // values. UNSAT.
            "div_by_const_zero_is_congruent",
            2,
            vec![
                atom(
                    vec![(1, 0)],
                    0,
                    Some(Wrap::Div(Divisor::Const(0))),
                    Rel::Eq,
                    5,
                    false,
                ),
                atom(
                    vec![(1, 0)],
                    0,
                    Some(Wrap::Div(Divisor::Const(0))),
                    Rel::Eq,
                    6,
                    false,
                ),
            ],
            vec![Node::Atom(0), Node::Atom(1)],
        ),
        (
            "mod_by_const_zero_is_congruent",
            2,
            vec![
                atom(
                    vec![(1, 0)],
                    0,
                    Some(Wrap::Mod(Divisor::Const(0))),
                    Rel::Eq,
                    5,
                    false,
                ),
                atom(
                    vec![(1, 0)],
                    0,
                    Some(Wrap::Mod(Divisor::Const(0))),
                    Rel::Eq,
                    6,
                    false,
                ),
            ],
            vec![Node::Atom(0), Node::Atom(1)],
        ),
        (
            // A VARIABLE divisor pinned to zero by another atom: the same
            // underspecification, reached through the solver rather than the
            // parser. Satisfiable.
            "div_by_variable_pinned_to_zero_is_satisfiable",
            2,
            vec![
                atom(
                    vec![(1, 0)],
                    0,
                    Some(Wrap::Div(Divisor::Var(1))),
                    Rel::Eq,
                    5,
                    false,
                ),
                atom(vec![(1, 1)], 0, None, Rel::Eq, 0, false),
            ],
            vec![Node::Atom(0), Node::Atom(1)],
        ),
        (
            // `2x + 4y = 3`: real-feasible, integer-infeasible. `lia_gcd`.
            "gcd_refutation_unsat",
            2,
            vec![atom(vec![(2, 0), (4, 1)], 0, None, Rel::Eq, 3, false)],
            vec![Node::Atom(0)],
        ),
        (
            // The even companion: satisfiable, so a blanket `unsat` fails.
            "gcd_feasible_sat",
            2,
            vec![atom(vec![(2, 0), (4, 1)], 0, None, Rel::Eq, 4, false)],
            vec![Node::Atom(0)],
        ),
        (
            // `3x > 1 ∧ 3x < 3` has no integer solution (x would be in (1/3, 1)).
            // Real-feasible; this is the `int_real_relax` trap.
            "integer_gap_between_multiples_unsat",
            2,
            vec![
                atom(vec![(3, 0)], 0, None, Rel::Gt, 1, false),
                atom(vec![(3, 0)], 0, None, Rel::Lt, 3, false),
            ],
            vec![Node::Atom(0), Node::Atom(1)],
        ),
        (
            // …and one unit wider, which IS satisfiable (x = 1).
            "integer_gap_widened_sat",
            2,
            vec![
                atom(vec![(3, 0)], 0, None, Rel::Gt, 1, false),
                atom(vec![(3, 0)], 0, None, Rel::Le, 3, false),
            ],
            vec![Node::Atom(0), Node::Atom(1)],
        ),
        (
            // `|x| < 0` is unsat for every integer x.
            "abs_below_zero_unsat",
            2,
            vec![atom(vec![(1, 0)], 0, Some(Wrap::Abs), Rel::Lt, 0, false)],
            vec![Node::Atom(0)],
        ),
        (
            // `|x + 3| = 0` pins x = -3: satisfiable, and the sign branch must
            // be reachable.
            "abs_pins_negative_value_sat",
            2,
            vec![atom(vec![(1, 0)], 3, Some(Wrap::Abs), Rel::Eq, 0, false)],
            vec![Node::Atom(0)],
        ),
        (
            // Extreme magnitudes: `x >= i64::MAX-1 ∧ x <= i64::MIN+1` is unsat.
            "extreme_constants_unsat",
            2,
            vec![
                atom(vec![(1, 0)], 0, None, Rel::Ge, i64::MAX - 1, false),
                atom(vec![(1, 0)], 0, None, Rel::Le, i64::MIN + 1, false),
            ],
            vec![Node::Atom(0), Node::Atom(1)],
        ),
        (
            "extreme_constants_sat",
            2,
            vec![
                atom(vec![(1, 0)], 0, None, Rel::Le, i64::MAX - 1, false),
                atom(vec![(1, 0)], 0, None, Rel::Ge, i64::MIN + 1, false),
            ],
            vec![Node::Atom(0), Node::Atom(1)],
        ),
        (
            // Every coefficient zero: `0 < -1` is false regardless of x.
            "zero_coefficients_collapse_to_false",
            2,
            vec![atom(vec![(0, 0), (0, 1)], 0, None, Rel::Lt, -1, false)],
            vec![Node::Atom(0)],
        ),
        (
            // Disequality: `¬(2x + 3y = 1)` is satisfiable, and its conjunction
            // with the equality is not.
            "disequality_with_its_equality_unsat",
            2,
            vec![
                atom(vec![(2, 0), (3, 1)], 0, None, Rel::Eq, 1, true),
                atom(vec![(2, 0), (3, 1)], 0, None, Rel::Eq, 1, false),
            ],
            vec![Node::Atom(0), Node::Atom(1)],
        ),
    ];

    let mut checked = 0u32;
    let mut skipped = 0u32;
    let mut routes: BTreeMap<String, u64> = BTreeMap::new();
    for (name, num_vars, atoms, roots) in cases {
        let inst = Instance {
            seed: u64::MAX,
            num_vars: *num_vars,
            corner: Corner::DivByConstZero,
            atoms: atoms.clone(),
            roots: roots.clone(),
        };
        let run = solve_axeyum_bounded(inst.clone());
        let z3 = z3_decide(&inst);
        if z3 == Ax::Unknown {
            skipped += 1;
            continue;
        }
        if matches!(
            (run.verdict, z3),
            (Ax::Sat, Ax::Unsat) | (Ax::Unsat, Ax::Sat)
        ) {
            panic!(
                "DISAGREEMENT on named case `{name}`: axeyum = {:?}, Z3 = {z3:?}\n{}",
                run.verdict,
                inst.dump()
            );
        }
        if let Some(route) = &run.route {
            *routes.entry(route.clone()).or_default() += 1;
        }
        checked += 1;
    }
    println!(
        "named QF_LIA degenerate cases: {checked} adjudicated | {skipped} skipped (z3 unknown)"
    );
    for (route, n) in &routes {
        println!("  decided by {route:<28} {n:>4}");
    }
    assert_eq!(
        skipped, 0,
        "Z3 must decide every hand-written pin; {skipped} came back unknown"
    );
    assert_eq!(
        usize::try_from(checked).expect("count fits"),
        cases.len(),
        "every named case must be adjudicated"
    );
}

/// A fuzz that cannot reproduce its own counterexample is a rumor.
#[test]
fn generation_is_reproducible_from_the_seed() {
    for seed in [0u64, 1, 5, 11, 12, 37, 191, 959] {
        let a = Instance::generate(seed);
        let b = Instance::generate(seed);
        assert_eq!(
            a.dump(),
            b.dump(),
            "seed {seed} produced two different queries"
        );
        let (arena_a, asserts_a) = a.build();
        let (arena_b, asserts_b) = b.build();
        assert_eq!(
            asserts_a.len(),
            asserts_b.len(),
            "seed {seed}: assertion count differs"
        );
        for (x, y) in asserts_a.iter().zip(asserts_b.iter()) {
            assert_eq!(
                render(&arena_a, *x),
                render(&arena_b, *y),
                "seed {seed}: built terms differ"
            );
        }
    }
}

fn atom(
    terms: Vec<(i64, usize)>,
    constant: i64,
    wrap: Option<Wrap>,
    rel: Rel,
    rhs: i64,
    neg: bool,
) -> LinAtom {
    LinAtom {
        terms,
        constant,
        wrap,
        rel,
        rhs,
        neg,
    }
}
