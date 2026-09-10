//! Adversarial differential fuzz for **difference logic** (`QF_IDL` / `QF_RDL`)
//! against the Z3 oracle.
//!
//! # Why this suite exists
//!
//! `dispatch_difference_logic` (`auto.rs`) runs **first** in the quantifier-free
//! dispatch ladder, ahead of the whole linear-arithmetic chain. When it answers
//! `Sat` or `Unsat` the front door returns that answer immediately — no later
//! route ever sees the query, so a wrong verdict here is caught by nothing
//! downstream. Before this file, difference logic had **no** oracle
//! cross-check: the three existing differential fuzzes are
//! `qf_lra_differential_fuzz`, `simplex_lra_fallback_differential` and
//! `qf_uflra_differential_fuzz`, and none of them generates the difference
//! fragment (`x - y ⋈ c` with unit coefficients) that `dl_online::scan_dl`
//! accepts.
//!
//! # THIS SUITE COMPILES TO ZERO TESTS WITHOUT `--features z3`
//!
//! The file is `#![cfg(feature = "z3")]`. Built without that feature it is an
//! **empty binary**: `cargo test` prints `running 0 tests ... ok` and exits
//! `0`. That is a green-looking gate that checks nothing, and suites in this
//! repository have shipped inert for weeks that way. Run it as
//!
//! ```text
//! cargo test -p axeyum-solver --features z3 --test difference_logic_differential_fuzz
//! ```
//!
//! and **confirm a nonzero test count** before believing the result. The
//! `z3` feature implies `full`, and needs a system `libz3`.
//!
//! # Soundness contract (the whole point)
//!
//! - axeyum `Sat`   ∧ Z3 `Unsat` → **PANIC** (wrong sat).
//! - axeyum `Unsat` ∧ Z3 `Sat`   → **PANIC** (wrong unsat — the worst bug).
//! - axeyum `Unknown` → fine (sound-incomplete is allowed).
//! - Z3 `Unknown`/timeout → skip (cannot adjudicate).
//!
//! # Degenerate-case coverage (the Hard Rule)
//!
//! CLAUDE.md: *"Partial/underspecified operators carry a fuzz seed-class that
//! generates the degenerate argument."* A wrong-unsat shipped once (`a946f925`)
//! because the fuzz that "passed" structurally could not emit the corner the
//! bug lived in. Difference logic's corners are structural rather than
//! partial-operator corners, and every one of them below is a **separate
//! branch inside `scan_dl` / `edge_for`**:
//!
//! | corner class | shape | the branch it reaches |
//! |---|---|---|
//! | `SelfDifference` | `x - x ⋈ c` | `head == tail` → `AtomKind::Const`, not an edge |
//! | `ZeroWeight` | `x - y ⋈ 0` | a zero-weight edge (a cycle through it is length-0) |
//! | `NegatedBoundPair` | `x - y ≤ k` ∧ `y - x ≤ -k` | a **tight** 0-cycle: sat, and pins `x - y = k` |
//! | `TightNegativeCycle` | `x - y ≤ k` ∧ `y - x ≤ -k-1` | the minimal negative cycle: unsat by 1 unit |
//! | `ExtremeConstant` | `|c|` within 4 of `i64::MIN` / `i64::MAX` | large-magnitude weights and their sums |
//! | `Disequality` | `¬(x = y + c)` | equality's negation — a *disjunction* of two edges |
//! | `UnaryBound` | `x ⋈ c` | the implicit `ZERO_VERTEX` edge |
//! | `ConstantOnly` | `0 ⋈ c` | both sides `ZERO_VERTEX` → constant atom |
//! | `StrictRelation` | `x - y < c` | integer tightening `≤ ⌈c⌉-1`; real `δ` weight |
//! | `EqualityAtom` | `x = y + c` | `expand_equality`: one term → two atoms + gate |
//! | `BoolEqGate` | `(= atom_a atom_b)` | `bool_eq_gates`, the post-order skeleton path |
//! | `IteSkeleton` | `ite(a, b, c)` over atoms | `Op::Ite` in `is_skeleton_op` |
//! | `RationalBound` | `x - y ≤ 1/3` (real only) | the `lcm` denominator-scaling path |
//!
//! The generator makes one of these **mandatory** per instance
//! (`seed % CORNERS.len()`), so coverage is a property of the seed schedule and
//! not of luck, and [`corner_coverage_is_total`] fails if any class stops being
//! emitted.
//!
//! # Determinism
//!
//! One seeded LCG per instance, seeded from the instance index. No clock, no
//! entropy, no hash-map iteration in any generated structure. A failure prints
//! its seed and a full textual dump of the instance, and re-running that seed
//! rebuilds byte-identical terms.
#![cfg(feature = "z3")]

use std::collections::BTreeMap;
use std::sync::mpsc;
use std::time::Duration;

use axeyum_ir::{Rational, Sort, TermArena, TermId, render};
use axeyum_solver::{
    CheckResult, RouteAttributionGuard, RouteOutcome, SolverConfig, last_route_attribution, solve,
};
use z3::ast::{Bool, Int, Real};
use z3::{Params, SatResult, Solver};

/// Instances per fuzz sweep. Difference-logic queries here are tiny (2–4
/// variables, ≤ 8 atoms), so this stays a few seconds.
const INSTANCES: u64 = 1_040;
const AXEYUM_TIMEOUT: Duration = Duration::from_secs(5);
const Z3_TIMEOUT: Duration = Duration::from_secs(2);

/// The route label `dispatch_difference_logic` records
/// (`auto.rs`: `t.record_result("dl-online", &result)`).
const DL_ROUTE: &str = "dl-online";

// ---------------------------------------------------------------------------
// Deterministic RNG
// ---------------------------------------------------------------------------

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
    /// Inclusive small range. Deliberately **not** used for the extreme
    /// constants: `hi - lo` would overflow near `i64::MIN`, so those are
    /// written out literally in [`Corner::emit`].
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
enum Mode {
    Int,
    Real,
}

/// One side of a difference atom. `Zero` is the literal `0`, which `scan_dl`
/// maps to its implicit `ZERO_VERTEX`.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Side {
    Zero,
    Var(usize),
}

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

/// `lhs ⋈ (rhs + num/den)`, optionally negated.
///
/// Every atom in the difference fragment has this form: both sides carry a unit
/// coefficient (or are the constant `0`), so `lhs - rhs` is exactly the
/// difference `scan_dl` looks for.
#[derive(Clone, Copy, Debug)]
struct Atom {
    lhs: Side,
    rhs: Side,
    num: i64,
    den: i64,
    rel: Rel,
    neg: bool,
}

/// The propositional skeleton over atom indices. Every connective here is one
/// `is_skeleton_op` accepts, plus `Op::Eq` at `Bool` sort (the `bool_eq_gates`
/// post-order path, which is *not* in `is_skeleton_op` and takes its own
/// branch in `collect`).
#[derive(Clone, Debug)]
enum Node {
    Atom(usize),
    Not(Box<Node>),
    And(Box<Node>, Box<Node>),
    Or(Box<Node>, Box<Node>),
    Implies(Box<Node>, Box<Node>),
    Xor(Box<Node>, Box<Node>),
    Ite(Box<Node>, Box<Node>, Box<Node>),
    /// `(= b1 b2)` at `Bool` sort.
    BoolEq(Box<Node>, Box<Node>),
}

/// The degenerate structural corners of difference logic. See the module docs
/// for the branch each one reaches.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
enum Corner {
    SelfDifference,
    ZeroWeight,
    NegatedBoundPair,
    TightNegativeCycle,
    ExtremeConstant,
    Disequality,
    UnaryBound,
    ConstantOnly,
    StrictRelation,
    EqualityAtom,
    BoolEqGate,
    IteSkeleton,
    RationalBound,
}

/// Order is load-bearing: the mandatory corner for seed `s` is
/// `CORNERS[s % CORNERS.len()]`, so this list *is* the coverage schedule.
const CORNERS: [Corner; 13] = [
    Corner::SelfDifference,
    Corner::ZeroWeight,
    Corner::NegatedBoundPair,
    Corner::TightNegativeCycle,
    Corner::ExtremeConstant,
    Corner::Disequality,
    Corner::UnaryBound,
    Corner::ConstantOnly,
    Corner::StrictRelation,
    Corner::EqualityAtom,
    Corner::BoolEqGate,
    Corner::IteSkeleton,
    Corner::RationalBound,
];

impl Corner {
    fn name(self) -> &'static str {
        match self {
            Corner::SelfDifference => "SelfDifference",
            Corner::ZeroWeight => "ZeroWeight",
            Corner::NegatedBoundPair => "NegatedBoundPair",
            Corner::TightNegativeCycle => "TightNegativeCycle",
            Corner::ExtremeConstant => "ExtremeConstant",
            Corner::Disequality => "Disequality",
            Corner::UnaryBound => "UnaryBound",
            Corner::ConstantOnly => "ConstantOnly",
            Corner::StrictRelation => "StrictRelation",
            Corner::EqualityAtom => "EqualityAtom",
            Corner::BoolEqGate => "BoolEqGate",
            Corner::IteSkeleton => "IteSkeleton",
            Corner::RationalBound => "RationalBound",
        }
    }

    /// A corner that only exists in one mode forces it; the rest let the seed
    /// choose, so both `QF_IDL` and `QF_RDL` are exercised on each.
    fn forced_mode(self) -> Option<Mode> {
        match self {
            // A non-integer bound cannot be written in the integer fragment.
            Corner::RationalBound => Some(Mode::Real),
            _ => None,
        }
    }

    /// Emits the atoms this corner is *defined by*, appending them to `atoms`
    /// and returning a skeleton node that mentions them all (so the corner
    /// cannot be generated and then dropped on the floor).
    fn emit(self, rng: &mut Lcg, mode: Mode, num_vars: usize, atoms: &mut Vec<Atom>) -> Node {
        let v = |rng: &mut Lcg| rng.below(num_vars as u64);
        let push = |atoms: &mut Vec<Atom>, a: Atom| {
            atoms.push(a);
            atoms.len() - 1
        };
        match self {
            Corner::SelfDifference => {
                // `x - x ⋈ c` — both sides the SAME variable. `scan_dl` folds
                // this to a constant atom instead of an edge; the fold's sign
                // handling is what this exercises, so `c` straddles 0.
                let x = v(rng);
                let i = push(
                    atoms,
                    Atom {
                        lhs: Side::Var(x),
                        rhs: Side::Var(x),
                        num: rng.in_range(-2, 2),
                        den: 1,
                        rel: Rel::pick(rng),
                        neg: rng.flip(),
                    },
                );
                Node::Atom(i)
            }
            Corner::ZeroWeight => {
                let (x, y) = distinct_pair(rng, num_vars);
                let i = push(
                    atoms,
                    Atom {
                        lhs: Side::Var(x),
                        rhs: Side::Var(y),
                        num: 0,
                        den: 1,
                        rel: if rng.flip() { Rel::Le } else { Rel::Lt },
                        neg: false,
                    },
                );
                Node::Atom(i)
            }
            Corner::NegatedBoundPair => {
                // `x ≤ y + k` ∧ `y ≤ x - k`: a tight 0-cycle. Satisfiable, and
                // it pins `x - y = k` exactly — the shape where an off-by-one
                // in cycle weighting flips the verdict.
                let (x, y) = distinct_pair(rng, num_vars);
                let k = rng.in_range(-3, 3);
                let a = push(
                    atoms,
                    Atom {
                        lhs: Side::Var(x),
                        rhs: Side::Var(y),
                        num: k,
                        den: 1,
                        rel: Rel::Le,
                        neg: false,
                    },
                );
                let b = push(
                    atoms,
                    Atom {
                        lhs: Side::Var(y),
                        rhs: Side::Var(x),
                        num: -k,
                        den: 1,
                        rel: Rel::Le,
                        neg: false,
                    },
                );
                Node::And(Box::new(Node::Atom(a)), Box::new(Node::Atom(b)))
            }
            Corner::TightNegativeCycle => {
                // The same pair, one unit tighter: `x ≤ y + k` ∧ `y ≤ x - k - 1`
                // is unsatisfiable by exactly 1. In REAL mode the `-1` is a
                // genuine gap; in INT mode a strict variant would additionally
                // tighten. Both are generated.
                let (x, y) = distinct_pair(rng, num_vars);
                let k = rng.in_range(-3, 3);
                let strict = rng.flip();
                let a = push(
                    atoms,
                    Atom {
                        lhs: Side::Var(x),
                        rhs: Side::Var(y),
                        num: k,
                        den: 1,
                        rel: if strict { Rel::Lt } else { Rel::Le },
                        neg: false,
                    },
                );
                let b = push(
                    atoms,
                    Atom {
                        lhs: Side::Var(y),
                        rhs: Side::Var(x),
                        num: if strict { -k } else { -k - 1 },
                        den: 1,
                        rel: if strict { Rel::Le } else { Rel::Le },
                        neg: false,
                    },
                );
                Node::And(Box::new(Node::Atom(a)), Box::new(Node::Atom(b)))
            }
            Corner::ExtremeConstant => {
                // Within 4 of the 64-bit extremes. Written literally: `in_range`
                // would overflow computing `hi - lo` down here.
                let big = match rng.below(4) {
                    0 => i64::MIN + rng.in_range(0, 4),
                    1 => i64::MAX - rng.in_range(0, 4),
                    2 => i64::from(i32::MIN) + rng.in_range(0, 4),
                    _ => i64::from(i32::MAX) - rng.in_range(0, 4),
                };
                let (x, y) = distinct_pair(rng, num_vars);
                let i = push(
                    atoms,
                    Atom {
                        lhs: Side::Var(x),
                        rhs: if rng.flip() { Side::Var(y) } else { Side::Zero },
                        num: big,
                        den: 1,
                        rel: Rel::pick(rng),
                        neg: rng.flip(),
                    },
                );
                Node::Atom(i)
            }
            Corner::Disequality => {
                // `¬(x = y + c)`. Equality expands to TWO atoms and its
                // negation is a disjunction the SAT core must case-split — the
                // one place difference logic is not conjunctive.
                let (x, y) = distinct_pair(rng, num_vars);
                let i = push(
                    atoms,
                    Atom {
                        lhs: Side::Var(x),
                        rhs: Side::Var(y),
                        num: rng.in_range(-2, 2),
                        den: 1,
                        rel: Rel::Eq,
                        neg: true,
                    },
                );
                Node::Atom(i)
            }
            Corner::UnaryBound => {
                let x = v(rng);
                let i = push(
                    atoms,
                    Atom {
                        lhs: Side::Var(x),
                        rhs: Side::Zero,
                        num: rng.in_range(-3, 3),
                        den: 1,
                        rel: Rel::pick(rng),
                        neg: rng.flip(),
                    },
                );
                Node::Atom(i)
            }
            Corner::ConstantOnly => {
                let i = push(
                    atoms,
                    Atom {
                        lhs: Side::Zero,
                        rhs: Side::Zero,
                        num: rng.in_range(-2, 2),
                        den: 1,
                        rel: Rel::pick(rng),
                        neg: rng.flip(),
                    },
                );
                Node::Atom(i)
            }
            Corner::StrictRelation => {
                let (x, y) = distinct_pair(rng, num_vars);
                let i = push(
                    atoms,
                    Atom {
                        lhs: Side::Var(x),
                        rhs: Side::Var(y),
                        num: rng.in_range(-3, 3),
                        den: 1,
                        rel: if rng.flip() { Rel::Lt } else { Rel::Gt },
                        neg: rng.flip(),
                    },
                );
                Node::Atom(i)
            }
            Corner::EqualityAtom => {
                let (x, y) = distinct_pair(rng, num_vars);
                let i = push(
                    atoms,
                    Atom {
                        lhs: Side::Var(x),
                        rhs: Side::Var(y),
                        num: rng.in_range(-2, 2),
                        den: 1,
                        rel: Rel::Eq,
                        neg: false,
                    },
                );
                Node::Atom(i)
            }
            Corner::BoolEqGate => {
                let (x, y) = distinct_pair(rng, num_vars);
                let a = push(
                    atoms,
                    Atom {
                        lhs: Side::Var(x),
                        rhs: Side::Var(y),
                        num: rng.in_range(-2, 2),
                        den: 1,
                        rel: Rel::Le,
                        neg: false,
                    },
                );
                let b = push(
                    atoms,
                    Atom {
                        lhs: Side::Var(y),
                        rhs: Side::Var(x),
                        num: rng.in_range(-2, 2),
                        den: 1,
                        rel: Rel::Le,
                        neg: false,
                    },
                );
                Node::BoolEq(Box::new(Node::Atom(a)), Box::new(Node::Atom(b)))
            }
            Corner::IteSkeleton => {
                let (x, y) = distinct_pair(rng, num_vars);
                let c = push(
                    atoms,
                    Atom {
                        lhs: Side::Var(x),
                        rhs: Side::Zero,
                        num: rng.in_range(-2, 2),
                        den: 1,
                        rel: Rel::Le,
                        neg: false,
                    },
                );
                let t = push(
                    atoms,
                    Atom {
                        lhs: Side::Var(x),
                        rhs: Side::Var(y),
                        num: rng.in_range(-2, 2),
                        den: 1,
                        rel: Rel::Lt,
                        neg: false,
                    },
                );
                let e = push(
                    atoms,
                    Atom {
                        lhs: Side::Var(y),
                        rhs: Side::Var(x),
                        num: rng.in_range(-2, 2),
                        den: 1,
                        rel: Rel::Ge,
                        neg: false,
                    },
                );
                Node::Ite(
                    Box::new(Node::Atom(c)),
                    Box::new(Node::Atom(t)),
                    Box::new(Node::Atom(e)),
                )
            }
            Corner::RationalBound => {
                debug_assert_eq!(mode, Mode::Real);
                let (x, y) = distinct_pair(rng, num_vars);
                // Denominators whose lcm the scan must form. Kept small and
                // coprime-ish so the product stays far under `MAX_SCALE`.
                let den = [2i64, 3, 4, 6, 5][rng.below(5)];
                let i = push(
                    atoms,
                    Atom {
                        lhs: Side::Var(x),
                        rhs: Side::Var(y),
                        num: rng.in_range(-7, 7),
                        den,
                        rel: if rng.flip() { Rel::Le } else { Rel::Lt },
                        neg: rng.flip(),
                    },
                );
                Node::Atom(i)
            }
        }
    }
}

/// Two distinct variable indices (or the same one when only one variable
/// exists — which cannot happen here, `num_vars ≥ 2`).
fn distinct_pair(rng: &mut Lcg, num_vars: usize) -> (usize, usize) {
    let x = rng.below(num_vars as u64);
    let mut y = rng.below(num_vars as u64);
    if y == x {
        y = (x + 1) % num_vars;
    }
    (x, y)
}

/// A generated instance. Plain data → `Send`, so the bounded solve can run on a
/// worker thread.
#[derive(Clone, Debug)]
struct Instance {
    seed: u64,
    mode: Mode,
    num_vars: usize,
    corner: Corner,
    atoms: Vec<Atom>,
    roots: Vec<Node>,
}

const VAR_NAMES: [&str; 4] = ["x", "y", "z", "w"];

impl Instance {
    fn generate(seed: u64) -> Instance {
        let mut rng = Lcg::new(seed);
        let corner = CORNERS[usize::try_from(seed).unwrap_or(0) % CORNERS.len()];
        let mode = corner
            .forced_mode()
            .unwrap_or(if rng.flip() { Mode::Int } else { Mode::Real });
        let num_vars = rng.below(3) + 2; // 2..=4

        let mut atoms = Vec::new();
        // The mandatory corner first, so its atom indices are stable per seed.
        let corner_root = corner.emit(&mut rng, mode, num_vars, &mut atoms);

        // Filler: 1..=4 ordinary difference atoms combined into one more root.
        let filler_count = rng.below(4) + 1;
        let mut filler: Vec<Node> = Vec::with_capacity(filler_count);
        for _ in 0..filler_count {
            let (x, y) = distinct_pair(&mut rng, num_vars);
            let lhs = Side::Var(x);
            let rhs = if rng.below(4) == 0 {
                Side::Zero
            } else {
                Side::Var(y)
            };
            let (num, den) = match mode {
                Mode::Int => (rng.in_range(-4, 4), 1),
                Mode::Real if rng.below(3) == 0 => {
                    (rng.in_range(-5, 5), [2i64, 3, 4][rng.below(3)])
                }
                Mode::Real => (rng.in_range(-4, 4), 1),
            };
            atoms.push(Atom {
                lhs,
                rhs,
                num,
                den,
                rel: Rel::pick(&mut rng),
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
                _ => Node::Or(Box::new(Node::Not(l)), r),
            };
        }

        Instance {
            seed,
            mode,
            num_vars,
            corner,
            atoms,
            roots: vec![corner_root, acc],
        }
    }

    // -- axeyum IR ---------------------------------------------------------

    fn build(&self) -> (TermArena, Vec<TermId>) {
        let mut a = TermArena::new();
        let sort = match self.mode {
            Mode::Int => Sort::Int,
            Mode::Real => Sort::Real,
        };
        let vars: Vec<TermId> = (0..self.num_vars)
            .map(|i| {
                let s = a.declare(VAR_NAMES[i], sort).expect("declare");
                a.var(s)
            })
            .collect();

        let atom_terms: Vec<TermId> = self
            .atoms
            .iter()
            .map(|atom| self.build_atom(&mut a, &vars, atom))
            .collect();

        let assertions = self
            .roots
            .iter()
            .map(|root| build_node_ir(&mut a, root, &atom_terms))
            .collect();
        (a, assertions)
    }

    fn side_ir(&self, a: &mut TermArena, vars: &[TermId], side: Side) -> TermId {
        match side {
            Side::Var(i) => vars[i],
            Side::Zero => match self.mode {
                Mode::Int => a.int_const(0),
                Mode::Real => a.real_const(Rational::zero()),
            },
        }
    }

    fn build_atom(&self, a: &mut TermArena, vars: &[TermId], atom: &Atom) -> TermId {
        let lhs = self.side_ir(a, vars, atom.lhs);
        let base = self.side_ir(a, vars, atom.rhs);
        let rhs = match self.mode {
            Mode::Int => {
                let k = a.int_const(i128::from(atom.num));
                a.int_add(base, k).expect("int_add")
            }
            Mode::Real => {
                let k = a.real_const(
                    Rational::checked_new(i128::from(atom.num), i128::from(atom.den))
                        .expect("nonzero denominator"),
                );
                a.real_add(base, k).expect("real_add")
            }
        };
        let b = match (self.mode, atom.rel) {
            (Mode::Int, Rel::Lt) => a.int_lt(lhs, rhs),
            (Mode::Int, Rel::Le) => a.int_le(lhs, rhs),
            (Mode::Int, Rel::Gt) => a.int_gt(lhs, rhs),
            (Mode::Int, Rel::Ge) => a.int_ge(lhs, rhs),
            (Mode::Real, Rel::Lt) => a.real_lt(lhs, rhs),
            (Mode::Real, Rel::Le) => a.real_le(lhs, rhs),
            (Mode::Real, Rel::Gt) => a.real_gt(lhs, rhs),
            (Mode::Real, Rel::Ge) => a.real_ge(lhs, rhs),
            (_, Rel::Eq) => a.eq(lhs, rhs),
        }
        .expect("relational term");
        if atom.neg { a.not(b).expect("not") } else { b }
    }

    // -- Z3 ----------------------------------------------------------------

    fn to_z3(&self) -> Vec<Bool> {
        let atom_terms: Vec<Bool> = match self.mode {
            Mode::Int => {
                let vars: Vec<Int> = (0..self.num_vars)
                    .map(|i| Int::new_const(VAR_NAMES[i]))
                    .collect();
                self.atoms
                    .iter()
                    .map(|atom| {
                        let side = |s: Side| match s {
                            Side::Var(i) => vars[i].clone(),
                            Side::Zero => Int::from_i64(0),
                        };
                        let lhs = side(atom.lhs);
                        assert_eq!(atom.den, 1, "integer mode never carries a denominator");
                        let rhs = Int::add(&[side(atom.rhs), Int::from_i64(atom.num)]);
                        let b = match atom.rel {
                            Rel::Lt => lhs.lt(&rhs),
                            Rel::Le => lhs.le(&rhs),
                            Rel::Gt => lhs.gt(&rhs),
                            Rel::Ge => lhs.ge(&rhs),
                            Rel::Eq => lhs.eq(&rhs),
                        };
                        if atom.neg { b.not() } else { b }
                    })
                    .collect()
            }
            Mode::Real => {
                let vars: Vec<Real> = (0..self.num_vars)
                    .map(|i| Real::new_const(VAR_NAMES[i]))
                    .collect();
                self.atoms
                    .iter()
                    .map(|atom| {
                        let side = |s: Side| match s {
                            Side::Var(i) => vars[i].clone(),
                            Side::Zero => Real::from_rational(0, 1),
                        };
                        let lhs = side(atom.lhs);
                        let rhs =
                            Real::add(&[side(atom.rhs), Real::from_rational(atom.num, atom.den)]);
                        let b = match atom.rel {
                            Rel::Lt => lhs.lt(&rhs),
                            Rel::Le => lhs.le(&rhs),
                            Rel::Gt => lhs.gt(&rhs),
                            Rel::Ge => lhs.ge(&rhs),
                            Rel::Eq => lhs.eq(&rhs),
                        };
                        if atom.neg { b.not() } else { b }
                    })
                    .collect()
            }
        };
        self.roots
            .iter()
            .map(|root| build_node_z3(root, &atom_terms))
            .collect()
    }

    // -- reproduction ------------------------------------------------------

    fn dump(&self) -> String {
        let mut lines = vec![format!(
            "seed {} | mode {:?} | corner {} | vars {}",
            self.seed,
            self.mode,
            self.corner.name(),
            VAR_NAMES[..self.num_vars].join(", ")
        )];
        for (i, atom) in self.atoms.iter().enumerate() {
            let s = |side: Side| match side {
                Side::Var(v) => VAR_NAMES[v].to_string(),
                Side::Zero => "0".to_string(),
            };
            let konst = if atom.den == 1 {
                format!("{}", atom.num)
            } else {
                format!("{}/{}", atom.num, atom.den)
            };
            lines.push(format!(
                "  atom[{i}]: {}({} {} {} + {konst})",
                if atom.neg { "NOT " } else { "" },
                s(atom.lhs),
                atom.rel.symbol(),
                s(atom.rhs),
            ));
        }
        for (i, root) in self.roots.iter().enumerate() {
            lines.push(format!("  assert[{i}]: {}", render_node(root)));
        }
        lines.join("\n")
    }
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
        Node::BoolEq(l, r) => {
            let (l, r) = (build_node_ir(a, l, atoms), build_node_ir(a, r, atoms));
            a.eq(l, r).expect("bool eq")
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
        Node::BoolEq(l, r) => build_node_z3(l, atoms).eq(&build_node_z3(r, atoms)),
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
        Node::BoolEq(l, r) => format!("(= {} {})", render_node(l), render_node(r)),
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

/// What one bounded axeyum solve produced: the verdict, and whether the
/// **difference-logic route itself** decided it. The second field is what makes
/// this a fuzz of `dl-online` rather than of whatever route happened to catch
/// the query — a dispatch regression that silently stops routing here would
/// otherwise leave the suite green while testing nothing.
#[derive(Clone, Copy, Debug)]
struct AxRun {
    verdict: Ax,
    decided_by_dl: bool,
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
            let decided_by_dl = last_route_attribution().attempts().iter().any(|attempt| {
                attempt.route == DL_ROUTE && matches!(attempt.outcome, RouteOutcome::Decided(_))
            });
            let _ = tx.send(AxRun {
                verdict,
                decided_by_dl,
            });
        })
        .expect("spawn solver thread");
    rx.recv_timeout(AXEYUM_TIMEOUT).unwrap_or(AxRun {
        verdict: Ax::Unknown,
        decided_by_dl: false,
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

/// The one comparison every test in this file routes through. Panics — with the
/// seed and a full dump — on any verdict disagreement.
///
/// It is deliberately the single place a planted wrong answer has to be
/// injected to break the suite (the negative control): invert one arm here and
/// every test below must fail.
fn adjudicate(inst: &Instance, ax: Ax, z3: Ax) {
    match (ax, z3) {
        (Ax::Sat, Ax::Unsat) | (Ax::Unsat, Ax::Sat) => {
            panic!(
                "DISAGREEMENT: axeyum = {ax:?}, Z3 = {z3:?}\n\
                 reproduce with seed {}\n{}",
                inst.seed,
                inst.dump()
            );
        }
        _ => {}
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

/// The main sweep: `INSTANCES` seeded difference-logic queries, each compared
/// against Z3.
#[test]
fn difference_logic_matches_z3() {
    let mut agree = 0u64;
    let mut ax_unknown = 0u64;
    let mut z3_unknown = 0u64;
    let mut dl_decided = 0u64;
    let mut per_corner_dl: BTreeMap<&'static str, u64> = BTreeMap::new();

    for seed in 0..INSTANCES {
        let inst = Instance::generate(seed);
        let run = solve_axeyum_bounded(inst.clone());
        let z3 = z3_decide(&inst);
        adjudicate(&inst, run.verdict, z3);

        if run.decided_by_dl {
            dl_decided += 1;
            *per_corner_dl.entry(inst.corner.name()).or_default() += 1;
        }
        match (run.verdict, z3) {
            (Ax::Unknown, _) => ax_unknown += 1,
            (_, Ax::Unknown) => z3_unknown += 1,
            _ => agree += 1,
        }
    }

    println!(
        "difference-logic fuzz: {INSTANCES} instances | {agree} agree | \
         {ax_unknown} axeyum-unknown | {z3_unknown} z3-unknown(skipped) | \
         {dl_decided} decided BY dl-online | 0 DISAGREE"
    );
    for (corner, n) in &per_corner_dl {
        println!("  dl-online decided {n:>4} of the {corner} instances");
    }

    // A dispatch regression that stopped routing these to `dl-online` would
    // leave every assertion above satisfied while testing a different engine.
    // The floor is deliberately loose (the front door may simplify a trivial
    // instance away before dispatch) but far above zero.
    assert!(
        dl_decided >= INSTANCES / 4,
        "expected >= {} instances decided by `{DL_ROUTE}`, got {dl_decided} — dispatch regression?",
        INSTANCES / 4
    );
    // And the sweep must not be vacuous in the other direction either.
    assert!(
        agree >= INSTANCES / 2,
        "expected >= {} agreements, got {agree} (axeyum-unknown {ax_unknown})",
        INSTANCES / 2
    );
}

/// The Hard-Rule guard: **every** corner class in [`CORNERS`] is actually
/// emitted by the seed schedule this sweep uses.
///
/// Without this, a refactor that stopped generating (say) `SelfDifference`
/// would leave `difference_logic_matches_z3` green while it had gone blind on
/// exactly the branch a fold bug lives in — the `a946f925` shape.
#[test]
fn corner_coverage_is_total() {
    let mut counts: BTreeMap<&'static str, u64> = BTreeMap::new();
    let mut modes: BTreeMap<&'static str, (u64, u64)> = BTreeMap::new();
    for seed in 0..INSTANCES {
        let inst = Instance::generate(seed);
        *counts.entry(inst.corner.name()).or_default() += 1;
        let entry = modes.entry(inst.corner.name()).or_default();
        match inst.mode {
            Mode::Int => entry.0 += 1,
            Mode::Real => entry.1 += 1,
        }
        // The corner's defining atoms must survive into the built query: a
        // generator that emitted a corner and then dropped it would be
        // indistinguishable from one that never emitted it.
        assert!(
            !inst.atoms.is_empty() && !inst.roots.is_empty(),
            "seed {} produced an empty query",
            inst.seed
        );
    }
    for corner in CORNERS {
        let n = counts.get(corner.name()).copied().unwrap_or(0);
        let (ints, reals) = modes.get(corner.name()).copied().unwrap_or((0, 0));
        println!(
            "  {:<20} {n:>4} instances (int {ints}, real {reals})",
            corner.name()
        );
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
}

/// Hand-written, named degenerate queries whose verdict is fixed by the
/// mathematics, cross-checked against Z3.
///
/// The sweep above is statistical; these are pins. Each is the *minimal* form
/// of one corner, so a failure names the branch directly instead of handing
/// back a random instance to minimize.
#[test]
fn named_degenerate_cases_match_z3() {
    // `(lhs, rhs, num, den, rel, neg)` per atom, all roots conjoined.
    let cases: &[(&str, Mode, usize, Vec<Atom>, Vec<Node>)] = &[
        (
            // `x - x < 0` is FALSE for every x: the constant-fold branch.
            "self_difference_strict_false",
            Mode::Int,
            2,
            vec![atom(Side::Var(0), Side::Var(0), 0, 1, Rel::Lt, false)],
            vec![Node::Atom(0)],
        ),
        (
            // `x - x <= 0` is TRUE for every x: the other side of the fold.
            "self_difference_nonstrict_true",
            Mode::Int,
            2,
            vec![atom(Side::Var(0), Side::Var(0), 0, 1, Rel::Le, false)],
            vec![Node::Atom(0)],
        ),
        (
            // `¬(x - x <= 0)` — negating a constant-true atom.
            "self_difference_negated",
            Mode::Real,
            2,
            vec![atom(Side::Var(0), Side::Var(0), 0, 1, Rel::Le, true)],
            vec![Node::Atom(0)],
        ),
        (
            // The tight 0-cycle: satisfiable, pins `x = y + 3`.
            "tight_zero_cycle_sat",
            Mode::Int,
            2,
            vec![
                atom(Side::Var(0), Side::Var(1), 3, 1, Rel::Le, false),
                atom(Side::Var(1), Side::Var(0), -3, 1, Rel::Le, false),
            ],
            vec![Node::Atom(0), Node::Atom(1)],
        ),
        (
            // One unit tighter: the minimal negative cycle. Unsat.
            "minimal_negative_cycle_unsat",
            Mode::Int,
            2,
            vec![
                atom(Side::Var(0), Side::Var(1), 3, 1, Rel::Le, false),
                atom(Side::Var(1), Side::Var(0), -4, 1, Rel::Le, false),
            ],
            vec![Node::Atom(0), Node::Atom(1)],
        ),
        (
            // Integer strict tightening: `x < y + 1 ∧ y < x + 1` forces x = y,
            // which is SAT over Z but the tightening must be exact.
            "integer_strict_tightening_sat",
            Mode::Int,
            2,
            vec![
                atom(Side::Var(0), Side::Var(1), 1, 1, Rel::Lt, false),
                atom(Side::Var(1), Side::Var(0), 1, 1, Rel::Lt, false),
            ],
            vec![Node::Atom(0), Node::Atom(1)],
        ),
        (
            // The same shape over the REALS is satisfiable too, but through the
            // δ-weight path rather than tightening.
            "real_strict_pair_sat",
            Mode::Real,
            2,
            vec![
                atom(Side::Var(0), Side::Var(1), 1, 1, Rel::Lt, false),
                atom(Side::Var(1), Side::Var(0), 1, 1, Rel::Lt, false),
            ],
            vec![Node::Atom(0), Node::Atom(1)],
        ),
        (
            // `x < y ∧ y < x` — strict 2-cycle, unsat in both modes.
            "strict_two_cycle_unsat",
            Mode::Real,
            2,
            vec![
                atom(Side::Var(0), Side::Var(1), 0, 1, Rel::Lt, false),
                atom(Side::Var(1), Side::Var(0), 0, 1, Rel::Lt, false),
            ],
            vec![Node::Atom(0), Node::Atom(1)],
        ),
        (
            // Zero-weight cycle over ≤: satisfiable (x = y).
            "zero_weight_cycle_sat",
            Mode::Int,
            2,
            vec![
                atom(Side::Var(0), Side::Var(1), 0, 1, Rel::Le, false),
                atom(Side::Var(1), Side::Var(0), 0, 1, Rel::Le, false),
            ],
            vec![Node::Atom(0), Node::Atom(1)],
        ),
        (
            // Disequality against a pinned difference: unsat.
            "disequality_against_pinned_difference_unsat",
            Mode::Int,
            2,
            vec![
                atom(Side::Var(0), Side::Var(1), 3, 1, Rel::Le, false),
                atom(Side::Var(1), Side::Var(0), -3, 1, Rel::Le, false),
                atom(Side::Var(0), Side::Var(1), 3, 1, Rel::Eq, true),
            ],
            vec![Node::Atom(0), Node::Atom(1), Node::Atom(2)],
        ),
        (
            // The same, one apart: satisfiable.
            "disequality_against_pinned_difference_sat",
            Mode::Int,
            2,
            vec![
                atom(Side::Var(0), Side::Var(1), 3, 1, Rel::Le, false),
                atom(Side::Var(1), Side::Var(0), -3, 1, Rel::Le, false),
                atom(Side::Var(0), Side::Var(1), 4, 1, Rel::Eq, true),
            ],
            vec![Node::Atom(0), Node::Atom(1), Node::Atom(2)],
        ),
        (
            // Integer-only unsat: `x - y > 0 ∧ x - y < 1` has no integer
            // solution but IS satisfiable over the reals. The two modes MUST
            // disagree here, which is exactly what makes it a good pin.
            "integer_gap_unsat",
            Mode::Int,
            2,
            vec![
                atom(Side::Var(0), Side::Var(1), 0, 1, Rel::Gt, false),
                atom(Side::Var(0), Side::Var(1), 1, 1, Rel::Lt, false),
            ],
            vec![Node::Atom(0), Node::Atom(1)],
        ),
        (
            "real_gap_sat",
            Mode::Real,
            2,
            vec![
                atom(Side::Var(0), Side::Var(1), 0, 1, Rel::Gt, false),
                atom(Side::Var(0), Side::Var(1), 1, 1, Rel::Lt, false),
            ],
            vec![Node::Atom(0), Node::Atom(1)],
        ),
        (
            // Rational bounds whose lcm the scan must form: `x ≤ y + 1/3` and
            // `y ≤ x - 1/2` is unsat (1/3 < 1/2).
            "rational_scale_unsat",
            Mode::Real,
            2,
            vec![
                atom(Side::Var(0), Side::Var(1), 1, 3, Rel::Le, false),
                atom(Side::Var(1), Side::Var(0), -1, 2, Rel::Le, false),
            ],
            vec![Node::Atom(0), Node::Atom(1)],
        ),
        (
            // `x ≤ y + 1/2 ∧ y ≤ x - 1/3` is satisfiable — the same shape with
            // the fractions swapped, so a scaling sign error flips exactly one
            // of this pair.
            "rational_scale_sat",
            Mode::Real,
            2,
            vec![
                atom(Side::Var(0), Side::Var(1), 1, 2, Rel::Le, false),
                atom(Side::Var(1), Side::Var(0), -1, 3, Rel::Le, false),
            ],
            vec![Node::Atom(0), Node::Atom(1)],
        ),
        (
            // Large magnitudes: `x ≤ i64::MIN + 1 ∧ x ≥ i64::MAX - 1` is unsat.
            "extreme_constants_unsat",
            Mode::Int,
            2,
            vec![
                atom(Side::Var(0), Side::Zero, i64::MIN + 1, 1, Rel::Le, false),
                atom(Side::Var(0), Side::Zero, i64::MAX - 1, 1, Rel::Ge, false),
            ],
            vec![Node::Atom(0), Node::Atom(1)],
        ),
        (
            // …and the satisfiable companion, so the pair cannot both pass by a
            // blanket `unsat`.
            "extreme_constants_sat",
            Mode::Int,
            2,
            vec![
                atom(Side::Var(0), Side::Zero, i64::MIN + 1, 1, Rel::Ge, false),
                atom(Side::Var(0), Side::Zero, i64::MAX - 1, 1, Rel::Le, false),
            ],
            vec![Node::Atom(0), Node::Atom(1)],
        ),
        (
            // Constant-only atoms: `0 < 0 + (-1)` is false.
            "constant_only_false",
            Mode::Int,
            2,
            vec![atom(Side::Zero, Side::Zero, -1, 1, Rel::Lt, false)],
            vec![Node::Atom(0)],
        ),
        (
            // A Boolean equality gate over two difference atoms: `(= (x ≤ y)
            // (y ≤ x - 1))` is unsat, because the two can never agree.
            "bool_eq_gate_unsat",
            Mode::Int,
            2,
            vec![
                atom(Side::Var(0), Side::Var(1), 0, 1, Rel::Le, false),
                atom(Side::Var(1), Side::Var(0), -1, 1, Rel::Le, false),
            ],
            vec![Node::BoolEq(
                Box::new(Node::Atom(0)),
                Box::new(Node::Atom(1)),
            )],
        ),
        (
            // `ite` in the skeleton over difference atoms.
            "ite_skeleton_unsat",
            Mode::Int,
            2,
            vec![
                atom(Side::Var(0), Side::Var(1), 0, 1, Rel::Le, false),
                atom(Side::Var(0), Side::Var(1), -1, 1, Rel::Gt, false),
                atom(Side::Var(0), Side::Var(1), 1, 1, Rel::Lt, false),
            ],
            vec![
                Node::Ite(
                    Box::new(Node::Atom(0)),
                    Box::new(Node::Not(Box::new(Node::Atom(1)))),
                    Box::new(Node::Atom(2)),
                ),
                Node::Atom(0),
            ],
        ),
        (
            // A 3-cycle whose weights sum to -1: unsat, and the shortest cycle
            // a 2-node search would miss.
            "three_cycle_negative_unsat",
            Mode::Int,
            3,
            vec![
                atom(Side::Var(0), Side::Var(1), 1, 1, Rel::Le, false),
                atom(Side::Var(1), Side::Var(2), 1, 1, Rel::Le, false),
                atom(Side::Var(2), Side::Var(0), -3, 1, Rel::Le, false),
            ],
            vec![Node::Atom(0), Node::Atom(1), Node::Atom(2)],
        ),
        (
            // The same 3-cycle summing to 0: satisfiable.
            "three_cycle_tight_sat",
            Mode::Int,
            3,
            vec![
                atom(Side::Var(0), Side::Var(1), 1, 1, Rel::Le, false),
                atom(Side::Var(1), Side::Var(2), 1, 1, Rel::Le, false),
                atom(Side::Var(2), Side::Var(0), -2, 1, Rel::Le, false),
            ],
            vec![Node::Atom(0), Node::Atom(1), Node::Atom(2)],
        ),
    ];

    let mut checked = 0u32;
    let mut dl_decided = 0u32;
    let mut skipped_z3_unknown = 0u32;
    for (name, mode, num_vars, atoms, roots) in cases {
        let inst = Instance {
            // Named cases have no LCG seed; the name is the reproduction key,
            // and `u64::MAX` marks the dump so it cannot be mistaken for one.
            seed: u64::MAX,
            mode: *mode,
            num_vars: *num_vars,
            corner: Corner::SelfDifference,
            atoms: atoms.clone(),
            roots: roots.clone(),
        };
        let run = solve_axeyum_bounded(inst.clone());
        let z3 = z3_decide(&inst);
        if z3 == Ax::Unknown {
            skipped_z3_unknown += 1;
            continue;
        }
        if run.verdict == Ax::Sat && z3 == Ax::Unsat || run.verdict == Ax::Unsat && z3 == Ax::Sat {
            panic!(
                "DISAGREEMENT on named case `{name}`: axeyum = {:?}, Z3 = {z3:?}\n{}",
                run.verdict,
                inst.dump()
            );
        }
        if run.decided_by_dl {
            dl_decided += 1;
        }
        checked += 1;
    }
    println!(
        "named degenerate cases: {checked} adjudicated | {dl_decided} decided by `{DL_ROUTE}` | \
         {skipped_z3_unknown} skipped (z3 unknown)"
    );
    assert_eq!(
        skipped_z3_unknown, 0,
        "Z3 must decide every hand-written pin; {skipped_z3_unknown} came back unknown"
    );
    assert_eq!(
        usize::try_from(checked).expect("count fits"),
        cases.len(),
        "every named case must be adjudicated"
    );
}

/// Regenerating the same seed must produce a byte-identical query. A fuzz that
/// cannot reproduce its own counterexample is a rumor, and the failure message
/// above tells a reader to "reproduce with seed N" — this is the assertion that
/// makes that instruction true.
#[test]
fn generation_is_reproducible_from_the_seed() {
    for seed in [0u64, 1, 7, 12, 13, 41, 199, 1_039] {
        let a = Instance::generate(seed);
        let b = Instance::generate(seed);
        assert_eq!(
            a.dump(),
            b.dump(),
            "seed {seed} produced two different queries"
        );
        // And the built IR must agree too, not merely the rendering.
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

fn atom(lhs: Side, rhs: Side, num: i64, den: i64, rel: Rel, neg: bool) -> Atom {
    Atom {
        lhs,
        rhs,
        num,
        den,
        rel,
        neg,
    }
}
