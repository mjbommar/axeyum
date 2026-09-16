//! Adversarial differential soundness fuzzer for the nonlinear-real (NRA)
//! sat/unsat deciders against the Z3 oracle.
//!
//! The recently-built CAD/grid NRA path (`nra_real_root.rs`) gained the
//! algebraic-grid lift for all-equality 2-var coupled systems, complete 2-var
//! strict-inequality CAD, and recursive N-var strict-inequality CAD. These are
//! soundness-critical: a wrong `Unsat` (claiming no solution when one exists) or
//! a wrong `Sat` (a non-replaying model, or one Z3 refutes) would be the worst
//! possible bug.
//!
//! This harness deterministically generates thousands of small random NRA
//! instances (no `Math::random`/`Date::now` — a fixed-seed LCG drives every
//! choice), decides each with both the default pure-Rust `solve` front door and
//! the Z3 backend, and gates on the joint verdict:
//!
//! - axeyum `Sat` ∧ Z3 `Unsat` → **PANIC** (wrong sat).
//! - axeyum `Unsat` ∧ Z3 `Sat` → **PANIC** (wrong unsat — the worst bug).
//! - axeyum `Sat` → the returned model is **independently replayed** through the
//!   IR ground evaluator on every original atom; a non-replaying Sat panics
//!   regardless of Z3.
//! - axeyum `Unknown` is ALLOWED (incomplete is sound) — counted, never failed.
//! - Z3 `Unknown`/timeout → the instance is skipped (cannot adjudicate).
//!
//! The test passes iff disagreements == 0 AND every axeyum `Sat` replayed.
#![cfg(feature = "full")]
#![cfg(feature = "z3")]

use std::sync::mpsc;
use std::time::Duration;

use axeyum_ir::{Rational, Sort, SymbolId, TermArena, TermId, Value, eval};
use axeyum_solver::{CheckResult, SolverConfig, solve};
use z3::ast::{Bool, Real};
use z3::{Params, SatResult, Solver};

/// Number of instances generated and adjudicated. Each is tiny (≤ 4 vars, ≤ 4
/// atoms, degree ≤ 2 per atom) so Z3 decides in well under its 2 s timeout. A few
/// of the recursive-CAD axeyum shapes are *much* slower than Z3, so each axeyum
/// solve runs under a hard wall-clock cap (`AXEYUM_TIMEOUT`) and a slow one is
/// counted as a timeout (sound: it is treated like `Unknown`), keeping the whole
/// sweep within a few minutes.
const INSTANCES: u64 = 2000;

/// Per-instance Z3 wall-clock budget. Small polys ⇒ Z3 decides far faster; this
/// only bounds the rare pathological shape so the test never hangs.
const Z3_TIMEOUT: Duration = Duration::from_secs(2);

/// Per-instance hard wall-clock cap on the axeyum `solve`. The NRA path scopes
/// `SolverConfig::timeout` through the root-isolation/CAD deadline guard, but a
/// cooperative poll is not a hard preemption boundary: a single exact-arithmetic
/// operation can still overrun it. We therefore run each solve on a worker thread
/// and join with this outer cap; a solve that overruns is recorded as
/// `AxeyumTimeout` (adjudication-neutral, exactly like `Unknown`) and the sweep
/// moves on. This is sound — a timeout is never a sat/unsat verdict — and bounds
/// total runtime.
const AXEYUM_TIMEOUT: Duration = Duration::from_secs(4);

/// A deterministic linear-congruential PRNG (the MMIX multiplier/increment).
/// No clock, no OS entropy: the whole sweep is reproducible from the seed.
struct Lcg(u64);

impl Lcg {
    fn new(seed: u64) -> Self {
        // Mix the seed once so consecutive seeds 0,1,2,… don't start correlated.
        Lcg(seed
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407))
    }

    /// Advance and return the next 64-bit state.
    fn next_u64(&mut self) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        self.0
    }

    /// A uniform integer in `0..n` (`n > 0`), returned as a `usize`.
    fn below(&mut self, n: u64) -> usize {
        usize::try_from(self.next_u64() % n).expect("modulus fits usize")
    }

    /// A small signed coefficient in `lo..=hi` (inclusive).
    fn in_range(&mut self, lo: i64, hi: i64) -> i64 {
        debug_assert!(lo <= hi);
        let span = u64::try_from(hi - lo + 1).expect("non-negative span");
        lo + i64::try_from(self.next_u64() % span).expect("offset within span")
    }
}

/// The six comparators we mix: equalities, strict, non-strict, and `!=` (covers
/// the algebraic-grid lift, the strict CAD, and shapes that legitimately decline
/// to the abstraction layer).
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
            // (`below` is uniform over 0..6)
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

    /// Build `lhs ⋈ 0` as an IR Bool term.
    fn build(self, a: &mut TermArena, lhs: TermId, zero: TermId) -> TermId {
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
}

/// One monomial: an integer coefficient times a product of 0–2 variable factors
/// (an index list into the instance's variables). An empty factor list is a
/// constant term. Kept as plain data so the same monomial both builds the IR
/// term and pretty-prints for a reproducing dump.
#[derive(Clone)]
struct Monomial {
    /// Rational coefficient `num / den` (`den > 0`). The ordinary generator sets
    /// `den = 1` (integer coefficients, unchanged); the *tight-anchored* mode
    /// (see [`Instance::generate`]) uses large denominators (up to `10^28`) to drive
    /// the equality-anchored bignum CAD-entry path — the slice-7 axis.
    num: i128,
    den: i128,
    factors: Vec<usize>,
}

/// A generated atom: a polynomial `Σ monomials ⋈ 0`, optionally divided by a
/// variable (`(poly / var[divisor]) ⋈ 0`) to exercise `RealDiv` — including the
/// SMT-LIB div-by-zero congruence path (`eliminate_real_div`), which the
/// polynomial-only generator never reached.
#[derive(Clone)]
struct Atom {
    monomials: Vec<Monomial>,
    cmp: Cmp,
    /// `Some(v)` wraps the atom's LHS as `(poly / var[v])`.
    divisor: Option<usize>,
}

/// A full generated instance: the variable count and the atoms. Owns only plain
/// data (no IR handles), so it is `Send` + `Clone` — a clone can be moved onto an
/// axeyum worker thread while the original drives the Z3 query and dumps.
#[derive(Clone)]
struct Instance {
    num_vars: usize,
    atoms: Vec<Atom>,
    /// The Boolean SKELETON over the atoms, as a CNF: one inner `Vec` per
    /// clause, holding indices into `atoms`.
    ///
    /// **Empty means a plain conjunction** — one assertion per atom, which is
    /// what every pre-ADR-2126 generator produces and what the conjunctive route
    /// accepts. A non-empty skeleton makes `build` emit one assertion per clause
    /// as an `or`, which is the shape `nra_single_cell` refuses outright and the
    /// clause loop exists to decide (ADR-2126).
    clauses: Vec<Vec<usize>>,
}

impl Instance {
    /// Deterministically generate an instance from the PRNG.
    ///
    /// Distribution:
    /// - 2..=4 real variables;
    /// - 1..=4 atoms;
    /// - each atom: 1..=3 monomials, each a coefficient in `-3..=3` times a
    ///   product of 0..=2 variable factors (so degree ≤ 2 per atom, occasionally
    ///   a single var squared when the two factors collide), plus an optional
    ///   constant monomial in `-3..=3`;
    /// - comparator uniform over the six.
    fn generate(rng: &mut Lcg) -> Instance {
        // ~1 in 5 instances is a single-variable **tight-anchored** shape: an
        // algebraic equality `x² = c` (`c ∈ {2,3,5,6,7}`, an irrational √c witness)
        // plus strict/loose inequalities whose coefficients carry large denominators
        // (up to 10^28) — the `approx-sqrt` axis that exercises the equality-anchored
        // bignum CAD-entry path (slice 7). Z3 adjudicates; DISAGREE must stay 0.
        if rng.below(5) == 0 {
            return Instance::generate_tight_anchored(rng);
        }
        // ~1 in 4 of the remainder is the **FBBT shape**: a nonlinear component in
        // 1-2 variables coupled to the rest only through LINEAR atoms, with a
        // chain of linear atoms that bounds the nonlinear variables TRANSITIVELY.
        // The general distribution below structurally cannot reach it -- see
        // [`Instance::generate_fbbt_bound_chain`] for why, and why a new `unsat`
        // producer without its own seed class is an ungated one.
        if rng.below(4) == 0 {
            return Instance::generate_fbbt_bound_chain(rng);
        }
        // ~1 in 4 of what is left is the **single-cell shape** (ADR-2121): a
        // conjunction of 2..=4-variable polynomial comparisons of total degree
        // up to 8, no division. That is the fragment `nra_single_cell` accepts,
        // and the general distribution below cannot reach it -- it caps the
        // degree at 2 and divides by a variable a quarter of the time, so the
        // single-cell route declines almost every instance it generates.
        if rng.below(4) == 0 {
            return Instance::generate_single_cell_shape(rng);
        }
        let num_vars = rng.below(3) + 2; // 2..=4
        let num_atoms = rng.below(4) + 1; // 1..=4
        let mut atoms = Vec::with_capacity(num_atoms);
        for _ in 0..num_atoms {
            let num_monos = rng.below(3) + 1; // 1..=3
            let mut monomials = Vec::with_capacity(num_monos + 1);
            for _ in 0..num_monos {
                let coeff = rng.in_range(-3, 3);
                let degree = rng.below(3); // 0..=2 variable factors
                let mut factors = Vec::with_capacity(degree);
                for _ in 0..degree {
                    factors.push(rng.below(num_vars as u64));
                }
                monomials.push(Monomial {
                    num: i128::from(coeff),
                    den: 1,
                    factors,
                });
            }
            // Optional constant monomial (~half the time).
            if rng.below(2) == 0 {
                monomials.push(Monomial {
                    num: i128::from(rng.in_range(-3, 3)),
                    den: 1,
                    factors: Vec::new(),
                });
            }
            // ~1/4 of atoms divide by a variable, so multiple atoms can share the
            // same `(numerator, divisor)` and a divisor can be forced to 0 — the
            // congruence + div-by-zero cases `eliminate_real_div` must model.
            let divisor = if rng.below(4) == 0 {
                Some(rng.below(num_vars as u64))
            } else {
                None
            };
            atoms.push(Atom {
                monomials,
                cmp: Cmp::pick(rng),
                divisor,
            });
        }
        Instance {
            num_vars,
            atoms,
            clauses: Vec::new(),
        }
    }

    /// The **single-cell seed class** (ADR-2121): the exact fragment
    /// [`axeyum_solver::single_cell_decide_for_testing`] accepts.
    ///
    /// # Why this class had to be added
    ///
    /// `nra_single_cell` is a new `unsat` producer AND a new `sat` producer, so
    /// a bug in its projection is a wrong verdict in either direction, and this
    /// fuzz is the only check that compares it against an independent solver.
    ///
    /// The general generator above **structurally cannot reach it**. It caps a
    /// monomial at two variable factors (total degree 2), and the interesting
    /// behaviour of a CAD route -- root isolation, the arrangement, a projection
    /// that has something to project -- begins above that. It also divides by a
    /// variable in a quarter of its atoms, and the single-cell route declines
    /// every `RealDiv` it cannot collect. So the route would be exercised on
    /// almost nothing.
    ///
    /// This class builds the corner deliberately:
    ///
    /// - 2..=4 real variables, which is the slice's `MAX_CELL_VARS`;
    /// - 1..=4 atoms, all CONJUNCTIVE and none divided;
    /// - monomials of total degree up to 8 (`MAX_CELL_DEGREE`), built by drawing
    ///   0..=8 variable factors, so the same variable can repeat and a genuine
    ///   high per-variable degree occurs;
    /// - comparators uniform over all six, so equalities -- whose witnesses are
    ///   exactly the algebraic points the slice refuses to represent -- occur at
    ///   the same rate as strict inequalities and the route's decline path is
    ///   exercised as hard as its decide path;
    /// - ~1 in 6 atoms is FORCED to share its monomial support with the previous
    ///   atom, which is what makes two polynomials collide in the eliminated
    ///   variable and gives the pairwise resultant something to do.
    ///
    /// Z3 adjudicates, exactly as for the other classes.
    fn generate_single_cell_shape(rng: &mut Lcg) -> Instance {
        let num_vars = rng.below(3) + 2; // 2..=4
        let num_atoms = rng.below(4) + 1; // 1..=4
        let mut atoms: Vec<Atom> = Vec::with_capacity(num_atoms);
        let mut previous: Vec<Vec<usize>> = Vec::new();
        for i in 0..num_atoms {
            let num_monos = rng.below(3) + 1; // 1..=3
            let mut monomials = Vec::with_capacity(num_monos + 1);
            let share = i > 0 && !previous.is_empty() && rng.below(6) == 0;
            for k in 0..num_monos {
                let coeff = rng.in_range(-3, 3);
                let factors = if share && k < previous.len() {
                    // Reuse the previous atom's monomial support verbatim, so the
                    // two polynomials genuinely collide in the eliminated variable.
                    previous[k].clone()
                } else {
                    let degree = rng.below(9); // 0..=8 variable factors
                    (0..degree)
                        .map(|_| rng.below(num_vars as u64))
                        .collect::<Vec<usize>>()
                };
                monomials.push(Monomial {
                    num: i128::from(coeff),
                    den: 1,
                    factors,
                });
            }
            if rng.below(2) == 0 {
                monomials.push(Monomial {
                    num: i128::from(rng.in_range(-3, 3)),
                    den: 1,
                    factors: Vec::new(),
                });
            }
            previous = monomials.iter().map(|m| m.factors.clone()).collect();
            atoms.push(Atom {
                monomials,
                cmp: Cmp::pick(rng),
                divisor: None, // conjunctive polynomial fragment: no RealDiv
            });
        }
        Instance {
            num_vars,
            atoms,
            clauses: Vec::new(),
        }
    }

    /// The **clause-loop seed class** (ADR-2126): the same polynomial shapes the
    /// single-cell class emits, wrapped in a genuine Boolean skeleton.
    ///
    /// # Why this class had to be added
    ///
    /// `nra_clause_loop` is a NEW decision route, and every other generator in
    /// this file emits a plain CONJUNCTION — `build` writes one assertion per
    /// atom and nothing ever nests an `or`. So none of them can reach the loop
    /// at all: the conjunctive route decides or declines first and the loop is
    /// never offered the query. A fuzz that structurally cannot generate the
    /// shape under test is not a gate on it, which is the rule CLAUDE.md states
    /// after `a946f925`.
    ///
    /// The skeleton is a CNF over the atoms: 2..=3 clauses of 1..=3 atom
    /// indices, drawn with repetition so an atom can appear in several clauses
    /// and so a clause can be a unit. At least one clause is forced to have
    /// **two or more** literals, because a CNF of units is a conjunction wearing
    /// a hat and would leave this class measuring the conjunctive route again.
    ///
    /// Z3 adjudicates the same formula, built from the same skeleton.
    fn generate_clause_loop_shape(rng: &mut Lcg) -> Instance {
        let base = Instance::generate_single_cell_shape(rng);
        let n = base.atoms.len();
        let num_clauses = rng.below(2) + 2; // 2..=3
        let mut clauses: Vec<Vec<usize>> = Vec::with_capacity(num_clauses);
        for _ in 0..num_clauses {
            let width = rng.below(3) + 1; // 1..=3
            let mut lits: Vec<usize> = Vec::with_capacity(width);
            for _ in 0..width {
                lits.push(rng.below(n as u64));
            }
            clauses.push(lits);
        }
        // Force a genuine disjunction somewhere, or this class silently degrades
        // into the conjunctive one it exists to be different from.
        if !clauses.iter().any(|c| c.len() >= 2) && n >= 2 {
            let a = rng.below(n as u64);
            let b = (a + 1) % n;
            clauses[0] = vec![a, b];
        }
        Instance {
            num_vars: base.num_vars,
            atoms: base.atoms,
            clauses,
        }
    }

    /// The **FBBT seed class**: a nonlinear component in 1–2 variables, coupled
    /// to the rest of the query through LINEAR atoms only, with a chain of linear
    /// atoms that bounds the nonlinear variables TRANSITIVELY.
    ///
    /// # Why this class had to be added
    ///
    /// `nra_fbbt` (2026-09-09) derives constant bounds on a nonlinear component's
    /// variables from the query's linear atoms and re-offers the component to the
    /// exact deciders. It is a **new `unsat` producer**, so a wrong bound is a
    /// wrong `unsat`, and this fuzz is the only check that compares its verdicts
    /// against an independent solver.
    ///
    /// The general generator above **structurally cannot reach it**. It emits
    /// 1..=4 atoms with coefficients in `-3..=3` and a uniform comparator, so the
    /// probability that it produces (a) a nonlinear atom confined to ≤ 2 of its
    /// 2..=4 variables, (b) a linear atom giving one of the *other* variables a
    /// constant bound, and (c) a further linear atom carrying that bound onto the
    /// nonlinear variable, in the right directions, is negligible — and the last
    /// one is the whole mechanism. That is the shape CLAUDE.md's hard rule names:
    /// a corpus sweep plus a fuzz that avoids the corner is not a soundness gate
    /// (`a946f925`).
    ///
    /// So this class builds the corner deliberately:
    ///
    /// - variables `0..nl_vars` (1 or 2) carry ALL the nonlinear content;
    /// - the last variable gets a two-sided CONSTANT bound;
    /// - each earlier variable is tied to the next by two linear atoms, so the
    ///   bound propagates down the chain onto the nonlinear variables — a
    ///   transitive bound, which `nra::extract_bounds` (syntactic) cannot see;
    /// - one link is dropped at random, so roughly a third of the instances leave
    ///   a nonlinear variable UNBOUNDED and the route must decline rather than
    ///   invent an extreme;
    /// - comparators are randomised between strict and non-strict on every atom,
    ///   because the strictness of a derived bound is itself a claim the checker
    ///   has to justify (its `GUARD 4`).
    ///
    /// Z3 adjudicates, exactly as for the other classes.
    #[allow(
        clippy::too_many_lines,
        reason = "one seed class, written out atom by atom: the atoms and their \
                  comparators ARE the shape being generated, and splitting them \
                  across helpers hides which corner this class covers"
    )]
    fn generate_fbbt_bound_chain(rng: &mut Lcg) -> Instance {
        let num_vars = rng.below(2) + 3; // 3..=4
        // One variable carries the nonlinear content (index 0); every other
        // variable occurs ONLY in the linear chain. That is the population's shape:
        // 37 of the 75 QF_NRA losses have every nonlinear atom in 1-2 variables and
        // all of them declare more.
        let last = num_vars - 1;
        // A nonzero small coefficient: a zero one silently deletes the monomial it
        // was meant to create, which would quietly shrink this class back toward
        // the general one.
        let nonzero = |rng: &mut Lcg| -> i128 {
            let mag = i128::from(rng.in_range(1, 3));
            if rng.below(2) == 0 { mag } else { -mag }
        };
        let mut atoms = Vec::new();

        // --- the nonlinear atom, in variable 0 only ---
        //
        // DEGREE 2..=6, and the comparator is never `!=`. Both choices are from
        // measurement, not taste. At degree 2 the class reached the route ZERO
        // times in 2,000 instances: `decompose_multivariate`'s N-variable CAD
        // decides a small quadratic system outright, and this route is consulted
        // only after that has declined. And a `!=` atom over a polynomial is
        // satisfiable almost everywhere, so an instance carrying one is decided
        // upstream and never reaches the nonlinear decider at all -- the first
        // draft of this class emitted them and the funnel read `consulted = 0`.
        let degree = rng.below(5) + 2; // 2..=6
        let monomials = vec![
            Monomial {
                num: nonzero(rng),
                den: 1,
                factors: vec![0; degree],
            },
            Monomial {
                num: i128::from(rng.in_range(-3, 3)),
                den: 1,
                factors: vec![0],
            },
            // A constant large enough to matter against the derived box: the whole
            // question this route answers is whether the atom's solution set meets
            // the interval the LINEAR atoms imply, and a constant of magnitude 6
            // against `x^6` never decides anything either way.
            Monomial {
                num: i128::from(rng.in_range(-400, 400)),
                den: 1,
                factors: Vec::new(),
            },
        ];
        atoms.push(Atom {
            monomials,
            cmp: match rng.below(5) {
                0 => Cmp::Lt,
                1 => Cmp::Le,
                2 => Cmp::Gt,
                3 => Cmp::Ge,
                _ => Cmp::Eq,
            },
            divisor: None,
        });

        // --- the constant anchor on the LAST variable, both sides ---
        //
        // Dropped outright ~1 in 5 times, so that fraction of the class leaves the
        // nonlinear variable UNBOUNDED and the route must decline rather than
        // invent an extreme. Dropping a link in the MIDDLE of the chain instead
        // (the first draft) has the same effect but is indistinguishable from a
        // chain that simply does not reach, so it measures less.
        let anchored = rng.below(5) != 0;
        if anchored {
            let lo = i128::from(rng.in_range(-2, 0));
            let hi = lo + i128::from(rng.in_range(0, 2));
            atoms.push(Atom {
                monomials: vec![
                    Monomial {
                        num: 1,
                        den: 1,
                        factors: vec![last],
                    },
                    Monomial {
                        num: -hi,
                        den: 1,
                        factors: Vec::new(),
                    },
                ],
                cmp: if rng.below(2) == 0 { Cmp::Le } else { Cmp::Lt },
                divisor: None,
            });
            atoms.push(Atom {
                monomials: vec![
                    Monomial {
                        num: 1,
                        den: 1,
                        factors: vec![last],
                    },
                    Monomial {
                        num: -lo,
                        den: 1,
                        factors: Vec::new(),
                    },
                ],
                cmp: if rng.below(2) == 0 { Cmp::Ge } else { Cmp::Gt },
                divisor: None,
            });
        }

        // --- the chain: `x_i` tied to `x_{i+1}` on both sides ---
        //
        // `gap >= 1`, because a gap of 0 with the strict comparators below is
        // `x_i - x_{i+1} < 0` AND `x_i - x_{i+1} >= 0`, a LINEAR contradiction that
        // the front door refutes before any nonlinear route runs. The first draft
        // allowed `gap = 0` and most of its instances were exactly that.
        for i in (0..last).rev() {
            let gap = i128::from(rng.in_range(1, 3));
            // `x_i - x_{i+1} - gap <= 0`   (x_i bounded above by x_{i+1} + gap)
            atoms.push(Atom {
                monomials: vec![
                    Monomial {
                        num: 1,
                        den: 1,
                        factors: vec![i],
                    },
                    Monomial {
                        num: -1,
                        den: 1,
                        factors: vec![i + 1],
                    },
                    Monomial {
                        num: -gap,
                        den: 1,
                        factors: Vec::new(),
                    },
                ],
                cmp: if rng.below(2) == 0 { Cmp::Le } else { Cmp::Lt },
                divisor: None,
            });
            // `x_i - x_{i+1} + gap >= 0`   (x_i bounded below by x_{i+1} - gap)
            atoms.push(Atom {
                monomials: vec![
                    Monomial {
                        num: 1,
                        den: 1,
                        factors: vec![i],
                    },
                    Monomial {
                        num: -1,
                        den: 1,
                        factors: vec![i + 1],
                    },
                    Monomial {
                        num: gap,
                        den: 1,
                        factors: Vec::new(),
                    },
                ],
                cmp: if rng.below(2) == 0 { Cmp::Ge } else { Cmp::Gt },
                divisor: None,
            });
        }

        Instance {
            num_vars,
            atoms,
            clauses: Vec::new(),
        }
    }

    /// A single-variable **tight-anchored** instance (slice-7 axis): an equality
    /// `x² = c` (irrational √c witness) plus 1..=3 inequalities whose coefficients
    /// carry large denominators, so the equality-anchored bignum CAD-entry path is
    /// exercised (isolate `x²−c`, sign-test the big-coefficient atoms at √c). Never
    /// divides (the anchored path is polynomial). Z3 is the oracle.
    fn generate_tight_anchored(rng: &mut Lcg) -> Instance {
        // Candidate denominators: 1 (integer), and powers of ten that trip the i128
        // `MAX_ABS_COEFF = 2^40 ≈ 1.1×10^12` CAD-entry guard (10^3 does not, 10^13 /
        // 10^28 do — the latter also exercises the wide bignum-intermediate clearing).
        const DENS: [i128; 5] = [1, 1_000, 10i128.pow(13), 10i128.pow(20), 10i128.pow(28)];
        let cs = [2i128, 3, 5, 6, 7];
        let c = cs[rng.below(cs.len() as u64)];

        let mut atoms = Vec::new();
        // Equality `x² − c = 0`.
        atoms.push(Atom {
            monomials: vec![
                Monomial {
                    num: 1,
                    den: 1,
                    factors: vec![0, 0],
                },
                Monomial {
                    num: -c,
                    den: 1,
                    factors: Vec::new(),
                },
            ],
            cmp: Cmp::Eq,
            divisor: None,
        });

        // 1..=3 inequalities `a·x² + b·x + k ⋈ 0` with large-denominator coefficients.
        let num_ineq = rng.below(3) + 1;
        for _ in 0..num_ineq {
            let mono = |rng: &mut Lcg, factors: Vec<usize>| {
                let den = DENS[rng.below(DENS.len() as u64)];
                // Numerator near ±den so the coefficient is O(1) (tight around √c),
                // occasionally larger; kept well within i128.
                let scale = rng.in_range(-4, 4);
                let jitter = rng.in_range(-9, 9);
                Monomial {
                    num: i128::from(scale) * den + i128::from(jitter),
                    den,
                    factors,
                }
            };
            let monomials = vec![
                mono(rng, vec![0, 0]),
                mono(rng, vec![0]),
                mono(rng, Vec::new()),
            ];
            atoms.push(Atom {
                monomials,
                cmp: Cmp::pick(rng),
                divisor: None,
            });
        }
        Instance {
            num_vars: 1,
            atoms,
            clauses: Vec::new(),
        }
    }

    /// Materialize the instance as IR assertions over a fresh arena, returning
    /// the arena, the per-variable symbol ids, and the assertion term ids.
    fn build(&self) -> (TermArena, Vec<SymbolId>, Vec<TermId>) {
        let mut a = TermArena::new();
        let names = ["x", "y", "z", "w"];
        let syms: Vec<SymbolId> = (0..self.num_vars)
            .map(|i| a.declare(names[i], Sort::Real).unwrap())
            .collect();
        let vars: Vec<TermId> = syms.iter().map(|&s| a.var(s)).collect();
        let zero = a.real_const(Rational::zero());

        let mut assertions = Vec::with_capacity(self.atoms.len());
        for atom in &self.atoms {
            // Build the polynomial as a sum of monomial terms.
            let mut poly: Option<TermId> = None;
            for m in &atom.monomials {
                // coeff * (factor product)
                let coeff_t = a.real_const(Rational::checked_new(m.num, m.den).unwrap());
                let mut term = coeff_t;
                for &f in &m.factors {
                    term = a.real_mul(term, vars[f]).unwrap();
                }
                poly = Some(match poly {
                    None => term,
                    Some(acc) => a.real_add(acc, term).unwrap(),
                });
            }
            // A monomial list is never empty (≥ 1 monomial generated).
            let mut lhs = poly.expect("every atom has at least one monomial");
            if let Some(d) = atom.divisor {
                lhs = a.real_div(lhs, vars[d]).unwrap();
            }
            assertions.push(atom.cmp.build(&mut a, lhs, zero));
        }
        if self.clauses.is_empty() {
            return (a, syms, assertions);
        }
        // A Boolean skeleton: one assertion per clause, each an `or` over the
        // atom terms built above. The atom terms are SHARED between clauses --
        // the arena interns them -- which is exactly the `let`-bound shape the
        // real meti-tarski files have and the reason a top-of-term shape column
        // says nothing about them (ADR-2121's sizing correction).
        let mut out = Vec::with_capacity(self.clauses.len());
        for clause in &self.clauses {
            let mut acc: Option<TermId> = None;
            for &i in clause {
                let lit = assertions[i];
                acc = Some(match acc {
                    None => lit,
                    Some(prev) => a.or(prev, lit).unwrap(),
                });
            }
            out.push(acc.expect("every clause has at least one literal"));
        }
        (a, syms, out)
    }

    /// Build the same instance as a list of Z3 `Bool` atoms over fresh Z3
    /// `Real` constants. The `Z3Backend` oracle does not yet lower real terms
    /// (ADR-0015), so the adjudication queries Z3 directly with the z3 crate's
    /// real arithmetic — the exact same theory the deciders target.
    fn to_z3(&self) -> Vec<Bool> {
        let atoms = self.atom_bools();
        if self.clauses.is_empty() {
            return atoms;
        }
        // The SAME skeleton, so the oracle adjudicates the formula the solver
        // was given and not the conjunction underneath it.
        self.clauses
            .iter()
            .map(|clause| {
                let refs: Vec<&Bool> = clause.iter().map(|&i| &atoms[i]).collect();
                Bool::or(&refs)
            })
            .collect()
    }

    /// The atoms as Z3 `Bool`s, before any Boolean skeleton is applied.
    fn atom_bools(&self) -> Vec<Bool> {
        let names = ["x", "y", "z", "w"];
        let vars: Vec<Real> = (0..self.num_vars)
            .map(|i| Real::new_const(names[i]))
            .collect();
        let zero = Real::from_rational(0, 1);

        self.atoms
            .iter()
            .map(|atom| {
                // Sum the monomials.
                let mut poly: Option<Real> = None;
                for m in &atom.monomials {
                    // Arbitrary-precision exact rational via decimal strings, so the
                    // 10^28-denominator tight coefficients reach Z3 without loss.
                    let mut term =
                        Real::from_rational_str(&m.num.to_string(), &m.den.to_string()).unwrap();
                    for &f in &m.factors {
                        term *= vars[f].clone();
                    }
                    poly = Some(match poly {
                        None => term,
                        Some(acc) => acc + term,
                    });
                }
                let mut lhs = poly.expect("every atom has at least one monomial");
                if let Some(d) = atom.divisor {
                    lhs /= vars[d].clone();
                }
                match atom.cmp {
                    Cmp::Eq => lhs.eq(&zero),
                    Cmp::Ne => lhs.ne(&zero),
                    Cmp::Lt => lhs.lt(&zero),
                    Cmp::Le => lhs.le(&zero),
                    Cmp::Gt => lhs.gt(&zero),
                    Cmp::Ge => lhs.ge(&zero),
                }
            })
            .collect()
    }

    /// An SMT-ish dump of the instance for a reproducing panic message.
    fn dump(&self) -> String {
        let names = ["x", "y", "z", "w"];
        let mut lines = vec![format!("vars: {}", &names[..self.num_vars].join(", "))];
        for (i, atom) in self.atoms.iter().enumerate() {
            let parts: Vec<String> = atom
                .monomials
                .iter()
                .map(|m| {
                    let mut s = if m.den == 1 {
                        m.num.to_string()
                    } else {
                        format!("{}/{}", m.num, m.den)
                    };
                    for &f in &m.factors {
                        s.push('*');
                        s.push_str(names[f]);
                    }
                    s
                })
                .collect();
            let body = match atom.divisor {
                Some(d) => format!("({}) / {}", parts.join(" + "), names[d]),
                None => parts.join(" + "),
            };
            lines.push(format!("  atom[{i}]: {} {} 0", body, atom.cmp.symbol()));
        }
        lines.join("\n")
    }
}

/// A coarse verdict label, abstracting away the model/reason payloads.
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

/// The replay outcome of an axeyum `Sat`, computed on the worker thread (which
/// owns the arena). The IR ground evaluator is the soundness trust anchor, but it
/// is incomplete over the algebraic field: real `add`/`mul` of two distinct
/// `RealAlgebraic` operands is deferred past ADR-0038 slice 1 and returns
/// `Err(AlgebraicArithmeticUnsupported)`. So a `Sat` replay is one of:
#[derive(Clone, PartialEq, Eq, Debug)]
enum Replay {
    /// Not a `Sat` verdict (no model to replay).
    NotSat,
    /// Every original atom evaluated `true` at the model — a verified replay.
    AllTrue,
    /// The evaluator declined ≥ 1 atom (`Err`) and refuted none — indeterminate;
    /// the Z3 cross-check still adjudicates the verdict.
    Indeterminate,
    /// An atom evaluated `false` at the model — a WRONG SAT (carries the atom
    /// index and a model dump for the panic).
    Violated { atom: usize, model: String },
}

/// The full axeyum result for one instance, decided on a worker thread under a
/// hard wall-clock cap.
struct AxeyumOutcome {
    verdict: Verdict,
    replay: Replay,
    /// A model dump for a `Sat` (used only when reporting a disagreement).
    model_dump: Option<String>,
    /// For an `Unknown` verdict, the classified reason kind + detail string
    /// (captured only for the opt-in `NRA_DUMP_UNKNOWN` capability-gap dump).
    unknown_reason: Option<(String, String)>,
}

/// Decide an instance with axeyum on a worker thread, joining under
/// [`AXEYUM_TIMEOUT`]. Returns `None` if the solve overran the cap (recorded as a
/// timeout by the caller — adjudication-neutral, never a verdict).
///
/// The arena, the model, and the replay all live on the worker thread; only the
/// `Send` summary ([`AxeyumOutcome`]) crosses back. The instance is moved in as
/// plain `Send` data (it owns no IR handles).
fn solve_axeyum_bounded(inst: Instance) -> Option<AxeyumOutcome> {
    let (tx, rx) = mpsc::channel();
    // A detached worker: if it overruns the cap we stop waiting and move on. It
    // keeps running to completion in the background (memory is bounded; the test
    // process reaps it on exit), but never blocks the sweep.
    std::thread::spawn(move || {
        let (mut a, syms, assertions) = inst.build();
        let result = solve(&mut a, &assertions, &SolverConfig::default());
        let outcome = match result {
            Err(_) => None, // solve must not error; surface as a worker failure
            Ok(ax) => {
                let verdict = label(&ax);
                let unknown_reason = match &ax {
                    CheckResult::Unknown(r) => Some((format!("{:?}", r.kind), r.detail.clone())),
                    _ => None,
                };
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
                                // `Err(..)` (algebraic-field eval gap) or a non-Bool
                                // result: indeterminate, not a refutation. Keep
                                // scanning in case a later atom is truly violated.
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
                    unknown_reason,
                })
            }
        };
        // The receiver may be gone (we timed out); ignore a send error.
        let _ = tx.send(outcome);
    });

    match rx.recv_timeout(AXEYUM_TIMEOUT) {
        Ok(Some(outcome)) => Some(outcome),
        Ok(None) => {
            panic!("axeyum solve returned an error (Unknown must be a result, not an error)")
        }
        Err(mpsc::RecvTimeoutError::Timeout) => None,
        Err(mpsc::RecvTimeoutError::Disconnected) => {
            panic!("axeyum worker thread panicked")
        }
    }
}

/// Decide an instance with Z3 over real arithmetic, with a tiny wall-clock
/// timeout. Returns `Unknown` on timeout/incompleteness (the instance is then
/// skipped — Z3 cannot adjudicate it).
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
#[allow(
    clippy::too_many_lines,
    reason = "one sweep with its adjudication table and its tally; splitting it \
              would separate a verdict from the counters that qualify it"
)]
fn nra_differential_fuzz_disagree_zero() {
    let mut total = 0u64;
    let mut jointly_decided = 0u64;
    let mut agreements = 0u64;
    let mut axeyum_unknown = 0u64;
    let mut axeyum_timeout = 0u64;
    let mut z3_unknown_skipped = 0u64;
    let mut sat_replayed = 0u64;
    let mut sat_replay_indeterminate = 0u64;

    for seed in 0..INSTANCES {
        total += 1;
        if seed % 200 == 0 {
            eprintln!(
                "[nra-fuzz] seed {seed}/{INSTANCES} (joint={jointly_decided}, agree={agreements}, \
                 ax_unknown={axeyum_unknown}, ax_timeout={axeyum_timeout})"
            );
        }
        let mut rng = Lcg::new(seed);
        let inst = Instance::generate(&mut rng);

        // --- axeyum: the default pure-Rust front door, hard-capped. -----------
        // A slow recursive-CAD solve is recorded as a timeout (adjudication-
        // neutral, like Unknown) so it can never dominate the sweep or wedge it.
        let Some(outcome) = solve_axeyum_bounded(inst.clone()) else {
            axeyum_timeout += 1;
            continue;
        };
        let ax_label = outcome.verdict;

        // A `Sat` whose model VIOLATES an original atom under the independent
        // ground evaluator is a wrong sat — the worst bug — regardless of Z3.
        if let Replay::Violated { atom, model } = &outcome.replay {
            panic!(
                "WRONG SAT (seed {seed}): axeyum returned Sat but its model makes \
                 atom[{atom}] FALSE under the independent ground evaluator — a \
                 soundness bug.\nmodel: {model}\ninstance:\n{}",
                inst.dump()
            );
        }
        match outcome.replay {
            Replay::AllTrue => sat_replayed += 1,
            Replay::Indeterminate => sat_replay_indeterminate += 1,
            Replay::NotSat | Replay::Violated { .. } => {}
        }

        if ax_label == Verdict::Unknown {
            axeyum_unknown += 1;
        }

        // --- Z3 oracle: a direct real-arithmetic query, tiny timeout. ---------
        let z3_label = z3_decide(&inst);

        if z3_label == Verdict::Unknown {
            // Cannot adjudicate this instance; skip (Z3 timeout/incomplete).
            z3_unknown_skipped += 1;
            continue;
        }

        // Both sides committed to Sat/Unsat (axeyum may still be Unknown).
        if ax_label == Verdict::Unknown {
            // axeyum incomplete here; not a joint decision, nothing to adjudicate.
            // Opt-in capability-gap dump: Z3 decided but axeyum declined. Emits a
            // single machine-greppable line per gap when `NRA_DUMP_UNKNOWN` is set;
            // zero behavior change (no output) when the env var is unset.
            if std::env::var_os("NRA_DUMP_UNKNOWN").is_some() {
                let (kind, detail) = outcome
                    .unknown_reason
                    .clone()
                    .unwrap_or_else(|| ("?".to_string(), "(no reason)".to_string()));
                let dump = inst.dump().replace('\n', " | ");
                eprintln!(
                    "UNKNOWN_GAP seed={seed} z3={z3_label:?} kind={kind} detail={detail:?} \
                     vars={} atoms={} inst=[{dump}]",
                    inst.num_vars,
                    inst.atoms.len()
                );
            }
            continue;
        }

        jointly_decided += 1;

        // THE SOUNDNESS GATE: a jointly-decided instance must AGREE. A mismatch
        // panics immediately with a reproducing dump, so reaching the tally
        // below means the sweep found zero disagreements.
        if ax_label == z3_label {
            agreements += 1;
        } else {
            let model_dump = outcome
                .model_dump
                .unwrap_or_else(|| "(no axeyum model)".to_string());
            panic!(
                "DISAGREEMENT (seed {seed}): axeyum = {ax_label:?}, Z3 = {z3_label:?}.\n\
                 This is a {} soundness bug.\n\
                 axeyum model: {model_dump}\n\
                 instance:\n{}",
                match (ax_label, z3_label) {
                    (Verdict::Sat, Verdict::Unsat) => "WRONG-SAT",
                    (Verdict::Unsat, Verdict::Sat) => "WRONG-UNSAT (worst case)",
                    _ => "verdict",
                },
                inst.dump()
            );
        }
    }

    println!("=== NRA differential fuzz tally ===");
    println!("total instances:      {total}");
    println!("jointly decided:      {jointly_decided}");
    println!("agreements:           {agreements}");
    println!("axeyum Unknown:       {axeyum_unknown}");
    println!("axeyum timeout:       {axeyum_timeout} (slow CAD; capped, adjudication-neutral)");
    println!("Z3 Unknown (skipped): {z3_unknown_skipped}");
    println!("Sat replays verified: {sat_replayed}");
    println!(
        "Sat replay declined:  {sat_replay_indeterminate} (algebraic-field eval gap; Z3-adjudicated)"
    );
    println!("DISAGREEMENTS:        0");

    // Reaching here means no disagreement panicked: DISAGREE=0 over the sweep.
    // Sanity: the sweep must actually exercise the joint deciders, not skip
    // everything (guards against a silently-broken Z3 plumbing that always
    // times out, which would make DISAGREE=0 vacuous).
    assert!(
        jointly_decided > 100,
        "too few jointly-decided instances ({jointly_decided}); the differential \
         gate is not meaningfully exercised"
    );

    // COVERAGE of the derived-bound refutation route (`nra_fbbt`), read from the
    // route's own counters rather than inferred from the tally above.
    //
    // This assertion exists because the tally CANNOT support the claim it looks
    // like it supports. Measured 2026-09-09 over this whole sweep, with the route
    // on and with `AXEYUM_NRA_FBBT=off`: 1,927 jointly decided and 1,927
    // agreements in BOTH arms, identical. That reading is equally consistent with
    // "the route ran and changed no verdict" and with "the route was never
    // reached", and only the second would make the seed class decoration. So the
    // gate is on the counter, not on the verdicts.
    let coverage = axeyum_solver::nra_derived_bound_coverage();
    println!("FBBT funnel: {coverage:?}");
    assert!(
        coverage.components_offered > 0,
        "the FBBT seed class generated its shape but no component ever reached \
         the derived-bound route ({coverage:?}); the class is decoration and this \
         producer is not differentially gated"
    );
}

// ---------------------------------------------------------------------------
// GAP-R1 (NRA) — explicit `RealDiv`-by-0 seeds that route through the NONLINEAR
// purification path (`eliminate_real_div`, the `r·y = x` fold). The random
// sweep above already divides by a *variable* pinnable to 0; these pin the exact
// degenerate shapes — a **constant-`0`** divisor (a separate const-fold branch,
// the `a946f925` lesson) and a symbolic divisor pinned to 0 — each anchored by a
// genuinely nonlinear atom so the instance is NRA-dispatched, not LRA. `/0` is
// UNDERSPEC (free but congruent): a formula sat only under a particular `x/0`
// must NOT be refuted, and two occurrences of the same `x/0` must agree.
// ---------------------------------------------------------------------------

fn nra_ax(a: &mut TermArena, assertions: &[TermId]) -> Verdict {
    match solve(a, assertions, &SolverConfig::default()) {
        Ok(CheckResult::Sat(_)) => Verdict::Sat,
        Ok(CheckResult::Unsat) => Verdict::Unsat,
        Ok(CheckResult::Unknown(_)) | Err(_) => Verdict::Unknown,
    }
}

fn nra_z3(bools: &[Bool]) -> Verdict {
    let solver = Solver::new();
    let mut params = Params::new();
    params.set_u32(
        "timeout",
        u32::try_from(Z3_TIMEOUT.as_millis()).unwrap_or(u32::MAX),
    );
    solver.set_params(&params);
    for b in bools {
        solver.assert(b);
    }
    match solver.check() {
        SatResult::Sat => Verdict::Sat,
        SatResult::Unsat => Verdict::Unsat,
        SatResult::Unknown => Verdict::Unknown,
    }
}

fn not_a_disagreement(ax: Verdict, z3: Verdict) -> bool {
    !matches!(
        (ax, z3),
        (Verdict::Sat, Verdict::Unsat) | (Verdict::Unsat, Verdict::Sat)
    )
}

/// Nonlinear anchor + `(/ x 0) = 5`: free `x/0` ⇒ SAT (must not refute); and the
/// congruent pair `(/ x 0) = 5 ∧ (/ x 0) = 6` ⇒ UNSAT.
#[test]
fn seed_nra_realdiv_const_zero_free_and_congruent() {
    let rk = |a: &mut TermArena, k: i128| a.real_const(Rational::integer(k));
    // (a) SAT: x·y = 1 (nonlinear) ∧ (/ x 0) = 5.
    {
        let mut a = TermArena::new();
        let xs = a.declare("x", Sort::Real).unwrap();
        let ys = a.declare("y", Sort::Real).unwrap();
        let (x, y) = (a.var(xs), a.var(ys));
        let xy = a.real_mul(x, y).unwrap();
        let one = rk(&mut a, 1);
        let anchor = a.eq(xy, one).unwrap();
        let zero = rk(&mut a, 0);
        let q = a.real_div(x, zero).unwrap();
        let five = rk(&mut a, 5);
        let e5 = a.eq(q, five).unwrap();
        let ax = nra_ax(&mut a, &[anchor, e5]);

        let zx = Real::new_const("x");
        let zy = Real::new_const("y");
        let zq = zx.clone() / Real::from_rational(0, 1);
        let z3 = nra_z3(&[
            (zx * zy).eq(Real::from_rational(1, 1)),
            zq.eq(Real::from_rational(5, 1)),
        ]);
        assert!(
            not_a_disagreement(ax, z3),
            "x·y=1 ∧ (/ x 0)=5: axeyum={ax:?}, Z3={z3:?} — free /0 must not be refuted"
        );
    }
    // (b) UNSAT: congruence forbids (/ x 0) = 5 ∧ (/ x 0) = 6.
    {
        let mut a = TermArena::new();
        let xs = a.declare("x", Sort::Real).unwrap();
        let ys = a.declare("y", Sort::Real).unwrap();
        let (x, y) = (a.var(xs), a.var(ys));
        let xy = a.real_mul(x, y).unwrap();
        let one = rk(&mut a, 1);
        let anchor = a.eq(xy, one).unwrap();
        let zero = rk(&mut a, 0);
        let q = a.real_div(x, zero).unwrap();
        let five = rk(&mut a, 5);
        let six = rk(&mut a, 6);
        let e5 = a.eq(q, five).unwrap();
        let e6 = a.eq(q, six).unwrap();
        let ax = nra_ax(&mut a, &[anchor, e5, e6]);

        let zx = Real::new_const("x");
        let zy = Real::new_const("y");
        let zq = zx.clone() / Real::from_rational(0, 1);
        let z3 = nra_z3(&[
            (zx * zy).eq(Real::from_rational(1, 1)),
            zq.eq(Real::from_rational(5, 1)),
            zq.eq(Real::from_rational(6, 1)),
        ]);
        assert!(
            not_a_disagreement(ax, z3),
            "x·y=1 ∧ (/ x 0)=5 ∧ (/ x 0)=6: axeyum={ax:?}, Z3={z3:?} — congruence must hold"
        );
    }
}

/// The `r·y = x` purification path with the divisor pinned to 0: `x² = 2` (an
/// irrational anchor, genuinely NRA) ∧ `y = 0` ∧ conflicting `(/ x y)` values ⇒
/// UNSAT (congruence), and the single-constraint form ⇒ SAT (must not refute).
#[test]
fn seed_nra_realdiv_symbolic_divisor_pinned_zero() {
    let rk = |a: &mut TermArena, k: i128| a.real_const(Rational::integer(k));
    // (a) SAT single constraint.
    {
        let mut a = TermArena::new();
        let xs = a.declare("x", Sort::Real).unwrap();
        let ys = a.declare("y", Sort::Real).unwrap();
        let (x, y) = (a.var(xs), a.var(ys));
        let xx = a.real_mul(x, x).unwrap();
        let two = rk(&mut a, 2);
        let anchor = a.eq(xx, two).unwrap();
        let zero = rk(&mut a, 0);
        let y0 = a.eq(y, zero).unwrap();
        let q = a.real_div(x, y).unwrap();
        let five = rk(&mut a, 5);
        let e5 = a.eq(q, five).unwrap();
        let ax = nra_ax(&mut a, &[anchor, y0, e5]);

        let zx = Real::new_const("x");
        let zy = Real::new_const("y");
        let zq = zx.clone() / zy.clone();
        let z3 = nra_z3(&[
            (zx.clone() * zx).eq(Real::from_rational(2, 1)),
            zy.eq(Real::from_rational(0, 1)),
            zq.eq(Real::from_rational(5, 1)),
        ]);
        assert!(
            not_a_disagreement(ax, z3),
            "x²=2 ∧ y=0 ∧ (/ x y)=5: axeyum={ax:?}, Z3={z3:?} — pinned /0 must not be refuted"
        );
    }
    // (b) UNSAT conflicting pair.
    {
        let mut a = TermArena::new();
        let xs = a.declare("x", Sort::Real).unwrap();
        let ys = a.declare("y", Sort::Real).unwrap();
        let (x, y) = (a.var(xs), a.var(ys));
        let xx = a.real_mul(x, x).unwrap();
        let two = rk(&mut a, 2);
        let anchor = a.eq(xx, two).unwrap();
        let zero = rk(&mut a, 0);
        let y0 = a.eq(y, zero).unwrap();
        let q = a.real_div(x, y).unwrap();
        let five = rk(&mut a, 5);
        let six = rk(&mut a, 6);
        let e5 = a.eq(q, five).unwrap();
        let e6 = a.eq(q, six).unwrap();
        let ax = nra_ax(&mut a, &[anchor, y0, e5, e6]);

        let zx = Real::new_const("x");
        let zy = Real::new_const("y");
        let zq = zx.clone() / zy.clone();
        let z3 = nra_z3(&[
            (zx.clone() * zx).eq(Real::from_rational(2, 1)),
            zy.eq(Real::from_rational(0, 1)),
            zq.eq(Real::from_rational(5, 1)),
            zq.eq(Real::from_rational(6, 1)),
        ]);
        assert!(
            not_a_disagreement(ax, z3),
            "x²=2 ∧ y=0 ∧ (/ x y)=5 ∧ (/ x y)=6: axeyum={ax:?}, Z3={z3:?} — congruence must hold"
        );
    }
}

/// Pretty-print an axeyum model's bindings for the named symbols.
fn dump_model(syms: &[SymbolId], model: &axeyum_solver::Model) -> String {
    let names = ["x", "y", "z", "w"];
    let mut parts = Vec::new();
    for (i, &s) in syms.iter().enumerate() {
        let v = model.get(s);
        parts.push(format!("{}={:?}", names[i], v));
    }
    parts.join(", ")
}

// ---------------------------------------------------------------------------
// ADR-2121: the single-cell CAD route, adjudicated directly against z3.
//
// The route ships OFF behind `AXEYUM_NRA_CAD`, which is read once per process.
// A fuzz that set that variable would be a gate on one shell (and setting it
// from a test is racy, and `unsafe` in edition 2024, which is denied
// workspace-wide), so this calls the route through the explicit
// `single_cell_decide_for_testing` hook instead. That is not a weaker test: it
// exercises exactly the code the lever enables, with no ambient state, and the
// counters below say how much of it actually ran.
// ---------------------------------------------------------------------------

/// Instances for the single-cell sweep. Smaller than the main sweep's 2000
/// because each instance can carry degree-8 monomials in four variables, and the
/// route's projection is an exact Leibniz determinant.
const SINGLE_CELL_INSTANCES: u64 = 1500;

/// Every `unsat` and every `sat` the ADR-2121 single-cell route produces must
/// agree with z3, and every `sat` model must replay against the assertions.
///
/// An `unknown`/decline is not a failure — the route is a bounded slice and
/// declining is its designed behaviour. What the assertions at the end hold is
/// that it did NOT decline everything, so a route that quietly stopped working
/// fails here instead of passing vacuously.
#[test]
#[allow(
    clippy::too_many_lines,
    reason = "one sweep with its adjudication table and its tally; splitting it \
              would separate a verdict from the counters that qualify it"
)]
fn single_cell_differential_fuzz_disagree_zero() {
    let mut total = 0u64;
    let mut decided = 0u64;
    let mut sat_decided = 0u64;
    let mut unsat_decided = 0u64;
    let mut agreements = 0u64;
    let mut declined = 0u64;
    let mut z3_unknown_skipped = 0u64;
    let mut checked_cells = 0usize;
    // ADR-2126: is the EXACT delineability check (6a) ever REACHED?
    //
    // This is not a detail. Measured on the corpus, both `unsat` verdicts the
    // A/B gains are single-level refutations closed entirely by ATOM cells --
    // `deeper = 0`, so 6a never runs on either. "The checker is exact" would
    // then be a true statement about a check with no measured exercise, which
    // is the shape of an unfalsifiable claim. These two counters make the fuzz
    // say whether it reaches 6a, so the answer is a number and not a hope.
    let mut open_deeper_cells = 0usize;
    let mut exact_delineability_tests = 0usize;
    let mut causes: std::collections::BTreeMap<String, u64> = std::collections::BTreeMap::new();

    for seed in 0..SINGLE_CELL_INSTANCES {
        total += 1;
        let mut rng = Lcg::new(seed ^ 0x2121_0915_c4d0_51e1);
        let inst = Instance::generate_single_cell_shape(&mut rng);
        let (arena, syms, assertions) = inst.build();

        let outcome = axeyum_solver::single_cell_decide_for_testing(&arena, &assertions);
        let cause = axeyum_solver::single_cell_decline_cause().to_owned();

        let ax = match &outcome {
            None => {
                declined += 1;
                *causes.entry(cause.clone()).or_insert(0) += 1;
                continue;
            }
            Some(CheckResult::Unknown(_)) => {
                declined += 1;
                *causes.entry(format!("unknown:{cause}")).or_insert(0) += 1;
                continue;
            }
            Some(CheckResult::Sat(model)) => {
                // Every `sat` must replay against the ORIGINAL assertions. This
                // is checked here as well as inside the route, because "the
                // route checked it" is exactly the claim a fuzz exists to doubt.
                let asg = model.to_assignment();
                for (i, &a) in assertions.iter().enumerate() {
                    assert!(
                        matches!(eval(&arena, a, &asg), Ok(Value::Bool(true))),
                        "SINGLE-CELL WRONG SAT: seed {seed} assertion #{i} does not hold \
                         under the model\n{}\nmodel: {}",
                        inst.dump(),
                        dump_model(&syms, model)
                    );
                }
                sat_decided += 1;
                Verdict::Sat
            }
            Some(CheckResult::Unsat) => {
                // Every `unsat` must carry a check that actually walked the
                // covering. Counting `unsat` verdicts alone cannot tell an
                // accepted certificate from a checker that stopped looking.
                let stats = axeyum_solver::single_cell_last_check().unwrap_or_else(|| {
                    panic!(
                        "SINGLE-CELL UNSAT WITH NO RECORDED CHECK: seed {seed}\n{}",
                        inst.dump()
                    )
                });
                assert!(
                    stats.cells > 0 && stats.coverings > 0,
                    "SINGLE-CELL UNSAT WITH A VACUOUS CHECK: seed {seed} {stats:?}\n{}",
                    inst.dump()
                );
                checked_cells += stats.cells;
                open_deeper_cells += stats.open_deeper_cells;
                exact_delineability_tests += stats.delineability_exact_tests;
                unsat_decided += 1;
                Verdict::Unsat
            }
        };
        decided += 1;

        let z3 = z3_decide(&inst);
        if z3 == Verdict::Unknown {
            z3_unknown_skipped += 1;
            continue;
        }
        assert!(
            not_a_disagreement(ax, z3),
            "SINGLE-CELL DISAGREEMENT: seed {seed} axeyum={ax:?} z3={z3:?}\n{}",
            inst.dump()
        );
        if ax == z3 {
            agreements += 1;
        }
    }

    eprintln!(
        "[single-cell-fuzz] total={total} decided={decided} (sat={sat_decided} \
         unsat={unsat_decided}) agreements={agreements} declined={declined} \
         z3_unknown_skipped={z3_unknown_skipped} checked_cells={checked_cells} \
         open_deeper_cells={open_deeper_cells} \
         exact_delineability_tests={exact_delineability_tests}"
    );
    eprintln!("[single-cell-fuzz] decline causes:");
    for (k, v) in &causes {
        eprintln!("    {k:28} {v:6}");
    }

    // The route must have RUN. A sweep where it declined everything would pass
    // every assertion above while checking nothing, which is the vacuous-green
    // shape this repository has shipped before.
    assert!(
        decided > 0,
        "the single-cell route decided NOTHING in {total} instances: the fuzz \
         checked no verdict at all"
    );
    // And both directions must be exercised: a sweep that only ever refutes
    // never touches the sat-side replay, and one that only ever satisfies never
    // touches the certificate checker.
    // ADR-2126. The corpus A/B's two `unsat` verdicts are single-level
    // refutations with NO `Deeper` cell, so the exact delineability check never
    // runs on either. If the fuzz also never reaches it, then 6a has no measured
    // exercise anywhere outside its unit fixtures -- and "the checker is exact"
    // would be a claim about a check nothing observed. Whichever way this goes,
    // the number is printed above and this assertion is what makes it a finding
    // instead of a line in a log.
    assert!(
        open_deeper_cells > 0 && exact_delineability_tests > 0,
        "the EXACT delineability check (6a) was never reached in {total} instances: \
         open_deeper_cells={open_deeper_cells} exact_tests={exact_delineability_tests}. \
         Every refutation this sweep produced was closed by atom cells alone, so the \
         generalisation 6a exists to justify was never performed and the check has no \
         measured exercise here"
    );
    assert!(
        sat_decided > 0 && unsat_decided > 0,
        "single-cell fuzz exercised only one direction: sat={sat_decided} \
         unsat={unsat_decided}"
    );
    // Every decided instance z3 also decided must have AGREED.
    assert_eq!(
        agreements,
        decided - z3_unknown_skipped,
        "every jointly-decided instance must agree"
    );
}

/// The degenerate-argument class for this route's one underspecified operator.
///
/// `nra_single_cell` never divides: its collector declines any `RealDiv` it
/// cannot fold, so the route's exposure to SMT-LIB's underspecified `x/0` is
/// "refuses to look at it". CLAUDE.md's hard rule still applies — a route that
/// *claims* not to touch a partial operator has to be shown not to, on the
/// degenerate argument itself, or the claim is a comment.
///
/// Both shapes below are SATISFIABLE (SMT-LIB leaves `x/0` free), so the only
/// wrong answer this can produce is `unsat`. A decline is the expected result
/// and is accepted; `unsat` is not.
/// The **clause-loop differential sweep** (ADR-2126).
///
/// Boolean combinations of polynomial sign atoms through
/// [`axeyum_solver::clause_loop_decide_for_testing`], adjudicated by z3 on the
/// same formula. The loop is driven through the testing hook rather than by
/// setting `AXEYUM_NRA_CAD`, for the reason ADR-2121 records: the lever is read
/// once per process, so a fuzz that set it would be a gate on one shell.
///
/// **ADR-2131 changed this sweep's premise.** ADR-2126 wrote it when the arm
/// withheld every `unsat`, and its `Unsat` arm was therefore a `panic!` reading
/// "reaching one here means the withholding was removed and an uncertified
/// refutation is on a decision path". The withholding IS removed, and the
/// refutation is no longer uncertified: `certify_unsat` emits `unsat` only when
/// `nra_clause_cert::check_clause_refutation` accepts. So the panic fired on the
/// first certified `unsat` and was a stale premise rather than a finding.
///
/// An `unsat` is now ADJUDICATED rather than forbidden, which is strictly more
/// work than the old arm did: z3 decides the same instance, `unsat` is an
/// agreement, **`sat` is a `CLAUSE-LOOP WRONG UNSAT` panic with the dump**, and
/// `unknown` is skipped and counted.
///
/// Five assertions keep this from passing vacuously:
///
/// * `decided > 0` — a sweep that declines everything agrees with everything;
/// * `unsat_decided > 0` — the half this lane added. Without it a generator that
///   never produces a refutable instance would exercise the certified-`unsat`
///   path zero times and still pass, which is exactly the shape the old panic
///   arm was hiding;
/// * every `sat` is REPLAYED here against the original assertions, and every
///   `unsat` has its CERTIFICATE re-read here, because "the route checked it" is
///   exactly the claim a fuzz exists to doubt. An accepted certificate that
///   examined no lemma, no gate and no proof step is the vacuous pass a boolean
///   cannot distinguish, so the counts are asserted, not the acceptance;
/// * `agreements == decided - z3_unknown_skipped` — the tally is asserted rather
///   than assumed;
/// * the class must actually produce **disjunctions**: the generator's
///   skeleton is checked for a clause of width ≥ 2, because a CNF of units is a
///   conjunction wearing a hat and would leave this sweep measuring the
///   conjunctive route a second time.
#[test]
fn clause_loop_differential_fuzz_disagree_zero() {
    let mut total = 0u64;
    let mut decided = 0u64;
    let mut sat_decided = 0u64;
    let mut unsat_decided = 0u64;
    let mut certificate_cells = 0usize;
    let mut agreements = 0u64;
    let mut declined = 0u64;
    let mut z3_unknown_skipped = 0u64;
    let mut with_a_real_disjunction = 0u64;
    let mut causes: std::collections::BTreeMap<String, u64> = std::collections::BTreeMap::new();

    for seed in 0..SINGLE_CELL_INSTANCES {
        total += 1;
        let mut rng = Lcg::new(seed ^ 0x2126_0916_9c1a_05e2);
        let inst = Instance::generate_clause_loop_shape(&mut rng);
        if inst.clauses.iter().any(|c| c.len() >= 2) {
            with_a_real_disjunction += 1;
        }
        let (arena, syms, assertions) = inst.build();

        let outcome = axeyum_solver::clause_loop_decide_for_testing(&arena, &assertions);
        let cause = axeyum_solver::single_cell_decline_cause().to_owned();

        let ax = match &outcome {
            None | Some(CheckResult::Unknown(_)) => {
                declined += 1;
                *causes.entry(cause.clone()).or_insert(0) += 1;
                continue;
            }
            Some(CheckResult::Sat(model)) => {
                let asg = model.to_assignment();
                for (i, &a) in assertions.iter().enumerate() {
                    assert!(
                        matches!(eval(&arena, a, &asg), Ok(Value::Bool(true))),
                        "CLAUSE-LOOP WRONG SAT: seed {seed} assertion #{i} does not hold \
                         under the model\n{}\nmodel: {}",
                        inst.dump(),
                        dump_model(&syms, model)
                    );
                }
                sat_decided += 1;
                decided += 1;
                Verdict::Sat
            }
            Some(CheckResult::Unsat) => {
                unsat_decided += 1;
                certificate_cells += certificate_cells_of(seed, &inst);
                decided += 1;
                Verdict::Unsat
            }
        };

        let z3 = z3_decide(&inst);
        if z3 == Verdict::Unknown {
            z3_unknown_skipped += 1;
            continue;
        }
        // A WRONG UNSAT is the soundness event this whole sweep exists for, so
        // it gets its own message rather than being folded into the generic
        // disagreement: "we refuted something z3 satisfies" is a different
        // sentence from "the two arms differ", and the instance dump is what
        // makes it actionable.
        assert!(
            !(ax == Verdict::Unsat && z3 == Verdict::Sat),
            "CLAUSE-LOOP WRONG UNSAT: seed {seed} -- the loop refuted an instance \
             z3 satisfies. This is a soundness finding, not a tuning issue.\n{}",
            inst.dump()
        );
        assert!(
            ax == z3 || not_a_disagreement(ax, z3),
            "CLAUSE-LOOP DISAGREEMENT: seed {seed} axeyum={ax:?} z3={z3:?}\n{}",
            inst.dump()
        );
        agreements += 1;
    }

    let cause_summary: Vec<String> = causes.iter().map(|(k, v)| format!("{k} {v}")).collect();
    println!(
        "clause-loop fuzz: total={total} decided={decided} sat_decided={sat_decided} \
         unsat_decided={unsat_decided} agreements={agreements} declined={declined} \
         z3_unknown_skipped={z3_unknown_skipped} certificate_cells={certificate_cells} \
         disjunctive_instances={with_a_real_disjunction}\n  decline causes: {}",
        cause_summary.join(", ")
    );

    assert!(
        decided > 0,
        "the clause-loop sweep decided NOTHING, so it agreed with z3 vacuously"
    );
    // ADR-2131. The certified-`unsat` path is the half this lane added, and a
    // sweep that never reaches a refutation exercises it ZERO times while
    // passing every other assertion here. If this fires, the generator cannot
    // produce an instance the loop refutes and it needs widening -- say that
    // rather than deleting the assertion.
    assert!(
        unsat_decided > 0,
        "the clause-loop sweep reached NO certified `unsat` in {total} instances, \
         so the certificate path was never exercised; widen the generator"
    );
    assert!(
        certificate_cells > 0,
        "every accepted certificate examined ZERO cells across {unsat_decided} \
         `unsat` verdicts -- the checker accepted without looking"
    );
    assert_eq!(
        agreements,
        decided - z3_unknown_skipped.min(decided),
        "every decided instance z3 also decided must have been adjudicated"
    );
    assert!(
        with_a_real_disjunction * 2 > total,
        "fewer than half the instances carry a real disjunction ({with_a_real_disjunction} \
         of {total}); this class would be measuring the conjunctive route"
    );
}

/// The certificate the clause loop left behind for an `unsat`, re-read here.
///
/// ADR-2131. The route emits `unsat` only when
/// `nra_clause_cert::check_clause_refutation` accepts, so this DOUBTS the
/// certificate rather than trusting the route -- the same obligation
/// `every_unsat_leaves_an_accepted_certificate` carries, applied to every
/// instance the sweep refutes instead of to one fixture.
///
/// The counts are what is asserted, not the acceptance: an accepted certificate
/// that examined no lemma, no proof step and no assertion root is the vacuous
/// pass a boolean cannot distinguish. Returns the cells examined so the caller
/// can assert the sweep as a whole looked at something.
fn certificate_cells_of(seed: u64, inst: &Instance) -> usize {
    let stats = axeyum_solver::clause_loop_last_check().unwrap_or_else(|| {
        panic!(
            "CLAUSE-LOOP UNCERTIFIED UNSAT: seed {seed} produced `unsat` with NO \
             certificate stats, so nothing was checked.\n{}",
            inst.dump()
        )
    });
    assert!(
        stats.lemmas > 0 && stats.drat_steps > 0 && stats.roots > 0,
        "CLAUSE-LOOP VACUOUS CERTIFICATE: seed {seed} accepted with lemmas={} \
         drat_steps={} roots={} -- an acceptance that examined nothing.\n{}",
        stats.lemmas,
        stats.drat_steps,
        stats.roots,
        inst.dump()
    );
    stats.lemma_cells
}

#[test]
fn clause_loop_never_refutes_a_division_by_constant_zero() {
    // The degenerate-argument class CLAUDE.md's hard rule requires, at the fuzz
    // level rather than only in the unit tests. `(/ x 0)` inside a DISJUNCTION
    // is the shape the loop is the first route to reach, and both fixtures are
    // SATISFIABLE, so a route that folded division-by-zero to a convention and
    // refuted would fail here rather than silently agreeing.
    let mut a = TermArena::new();
    let x = a.declare("x", Sort::Real).unwrap();
    let y = a.declare("y", Sort::Real).unwrap();
    let xv = a.var(x);
    let yv = a.var(y);
    let zero = a.real_const(Rational::zero());
    let one = a.real_const(Rational::integer(1));
    let five = a.real_const(Rational::integer(5));

    // (or (> (/ x 0) 1) (> y 5)) /\ (> y 5)  -- satisfiable via the second arm.
    let div0 = a.real_div(xv, zero).unwrap();
    let lhs = a.real_gt(div0, one).unwrap();
    let rhs = a.real_gt(yv, five).unwrap();
    let disj = a.or(lhs, rhs).unwrap();
    let out = axeyum_solver::clause_loop_decide_for_testing(&a, &[disj, rhs]);
    assert!(
        !matches!(out, Some(CheckResult::Unsat)),
        "a satisfiable query with a constant-zero divisor was refuted: {out:?}"
    );

    // And with a SYMBOLIC divisor that can be zero.
    let div_by_y = a.real_div(xv, yv).unwrap();
    let lhs2 = a.real_gt(div_by_y, one).unwrap();
    let rhs2 = a.real_gt(xv, five).unwrap();
    let disj_symbolic = a.or(lhs2, rhs2).unwrap();
    let out2 = axeyum_solver::clause_loop_decide_for_testing(&a, &[disj_symbolic, rhs2]);
    assert!(
        !matches!(out2, Some(CheckResult::Unsat)),
        "a satisfiable query with a symbolic divisor was refuted: {out2:?}"
    );
}

#[test]
fn single_cell_never_refutes_a_division_by_constant_zero() {
    let mut a = TermArena::new();
    let x = a.declare("x", Sort::Real).unwrap();
    let y = a.declare("y", Sort::Real).unwrap();
    let xt = a.var(x);
    let yt = a.var(y);
    let zero = a.real_const(Rational::zero());
    let five = a.real_const(Rational::integer(5));

    // `(/ x 0) = 5 ∧ y*y > 1` -- free `x/0`, so SAT.
    let div = a.real_div(xt, zero).unwrap();
    let eq = Cmp::Eq.build(&mut a, div, five);
    let sq = a.real_mul(yt, yt).unwrap();
    let one = a.real_const(Rational::integer(1));
    let gt = Cmp::Gt.build(&mut a, sq, one);
    let out = axeyum_solver::single_cell_decide_for_testing(&a, &[eq, gt]);
    assert!(
        !matches!(out, Some(CheckResult::Unsat)),
        "the single-cell route REFUTED a satisfiable `x/0` query: {out:?} (cause {})",
        axeyum_solver::single_cell_decline_cause()
    );
    // z3 agrees it is satisfiable, so the assertion above is testing a real
    // property and not an accident of the encoding.
    let zx = Real::new_const("x");
    let zy = Real::new_const("y");
    let zdiv = zx / Real::from_rational(0, 1);
    let zeq = zdiv.eq(Real::from_rational(5, 1));
    let zgt = (zy.clone() * zy).gt(Real::from_rational(1, 1));
    assert_eq!(nra_z3(&[zeq, zgt]), Verdict::Sat, "control: z3 says sat");

    // And a DIVISION BY A VARIABLE that can be zero, same expectation.
    let mut b = TermArena::new();
    let bx = b.declare("x", Sort::Real).unwrap();
    let by = b.declare("y", Sort::Real).unwrap();
    let bxt = b.var(bx);
    let byt = b.var(by);
    let bfive = b.real_const(Rational::integer(5));
    let bdiv = b.real_div(bxt, byt).unwrap();
    let beq = Cmp::Eq.build(&mut b, bdiv, bfive);
    let bsq = b.real_mul(byt, byt).unwrap();
    let bzero = b.real_const(Rational::zero());
    let bgt = Cmp::Gt.build(&mut b, bsq, bzero);
    let bout = axeyum_solver::single_cell_decide_for_testing(&b, &[beq, bgt]);
    assert!(
        !matches!(bout, Some(CheckResult::Unsat)),
        "the single-cell route REFUTED a satisfiable symbolic-divisor query: {bout:?} (cause {})",
        axeyum_solver::single_cell_decline_cause()
    );
}
