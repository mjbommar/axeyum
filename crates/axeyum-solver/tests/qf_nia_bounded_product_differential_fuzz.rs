//! Adversarial differential soundness fuzzer for the **entailed-bound product
//! lemmas** of `nia_linearize`: the `McCormick` envelopes, the exact narrow-domain
//! case split, the derived product intervals, and the tangent-plane refinement
//! loop — all against the Z3 oracle.
//!
//! ## Why the existing NIA fuzzes are structurally blind here
//!
//! `nia_differential_fuzz` generates atoms of the form `Σ monomials ⋈ 0` and
//! **never emits an explicit variable bound**. Every lemma family this suite
//! covers is gated on [`harvest_const_bounds`] finding a top-level `v ≥ c` /
//! `v ≤ c` / `v = c` atom, so that generator *cannot* reach any of them — the same
//! "the fuzz that passed could not generate the case" trap that shipped a wrong
//! `unsat` for `div`-by-constant-zero (`a946f925`). This harness asserts bounds
//! explicitly and makes the products the point of the instance.
//!
//! ## The degenerate-product seed class (mandatory, per the standing hard rule)
//!
//! A product `r = a·b` under entailed bounds is most fragile exactly at its
//! degenerate arguments, so a fixed share of every instance deliberately emits:
//!
//!  - a factor **pinned to a single value** (`v = k`, `k` including `0`), so the
//!    query contains a literal `0 · b`;
//!  - a factor **sitting on its bound** (an atom forcing `v = lo` or `v = hi`);
//!  - a **`0`-literal factor** written directly into a product;
//!  - a **self-product** `v · v` of a bounded variable;
//!  - an **empty window** (`lo > hi`), where the box is contradictory and no lemma
//!    family may turn the query `sat`;
//!  - a **bound-violating shape** — a product constrained against its own derived
//!    interval (`v ∈ [0,1] ∧ w ∈ [0,1] ∧ v·w ≥ 2`), which must come out `unsat`
//!    for the right reason and never `sat`.
//!
//! ## Adjudication (identical gates to the proven NIA/NRA fuzzers)
//!
//!  - axeyum `Sat` ∧ Z3 `Unsat` → PANIC (wrong sat).
//!  - axeyum `Unsat` ∧ Z3 `Sat` → PANIC (wrong unsat — the worst bug).
//!  - axeyum `Sat` → the model is independently replayed through the IR ground
//!    evaluator on every original atom; a non-replaying `Sat` panics.
//!  - axeyum `Unknown` → allowed (incomplete is sound), counted.
//!  - Z3 `Unknown`/timeout → the instance is skipped.
#![cfg(feature = "full")]
#![cfg(feature = "z3")]

use std::sync::mpsc;
use std::time::Duration;

use axeyum_ir::{Sort, SymbolId, TermArena, TermId, Value, eval};
use axeyum_solver::{CheckResult, SolverConfig, solve};
use z3::ast::{Bool, Int};
use z3::{Params, SatResult, Solver};

const INSTANCES: u64 = 1200;
const Z3_TIMEOUT: Duration = Duration::from_secs(2);
/// Budget handed to `solve` itself, so the bounded ladder yields a timely
/// `Unknown` rather than spinning. A timeout is adjudication-neutral.
const AXEYUM_SOLVE_BUDGET: Duration = Duration::from_secs(3);
/// Hard join cap on the worker thread, kept above the solve's own budget.
const AXEYUM_WALL_TIMEOUT: Duration = Duration::from_secs(8);

/// Deterministic MMIX linear-congruential PRNG (no clock, no OS entropy).
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
        self.0 >> 11
    }

    fn below(&mut self, n: u64) -> usize {
        usize::try_from(self.next_u64() % n).unwrap_or(0)
    }

    fn in_range(&mut self, lo: i64, hi: i64) -> i64 {
        let span = u64::try_from(hi - lo + 1).unwrap_or(1);
        lo + i64::try_from(self.next_u64() % span).unwrap_or(0)
    }
}

/// The bound asserted for one variable.
#[derive(Clone, Copy, Debug)]
enum Bound {
    /// `lo ≤ v ≤ hi` (a NARROW window when `hi − lo ≤ 4`, which is what the exact
    /// case split keys on; an EMPTY one when `lo > hi`).
    Window(i64, i64),
    /// `v ≥ lo` only — the Farkas-multiplier shape, where the `McCormick` envelope
    /// degenerates unless the other factor is fully bounded.
    Lower(i64),
    /// `v = k` — a pinned factor; `k = 0` makes every product it appears in `0·b`.
    Pinned(i64),
    /// No bound at all.
    Free,
}

#[derive(Clone, Copy, Debug)]
enum Cmp {
    Lt,
    Le,
    Gt,
    Ge,
    Eq,
    Ne,
}

impl Cmp {
    fn pick(rng: &mut Lcg) -> Cmp {
        match rng.below(6) {
            0 => Cmp::Lt,
            1 => Cmp::Le,
            2 => Cmp::Gt,
            3 => Cmp::Ge,
            4 => Cmp::Eq,
            _ => Cmp::Ne,
        }
    }

    fn build(self, a: &mut TermArena, lhs: TermId, rhs: TermId) -> TermId {
        match self {
            Cmp::Lt => a.int_lt(lhs, rhs).unwrap(),
            Cmp::Le => a.int_le(lhs, rhs).unwrap(),
            Cmp::Gt => a.int_gt(lhs, rhs).unwrap(),
            Cmp::Ge => a.int_ge(lhs, rhs).unwrap(),
            Cmp::Eq => a.eq(lhs, rhs).unwrap(),
            Cmp::Ne => {
                let e = a.eq(lhs, rhs).unwrap();
                a.not(e).unwrap()
            }
        }
    }

    fn build_z3(self, lhs: &Int, rhs: &Int) -> Bool {
        match self {
            Cmp::Lt => lhs.lt(rhs),
            Cmp::Le => lhs.le(rhs),
            Cmp::Gt => lhs.gt(rhs),
            Cmp::Ge => lhs.ge(rhs),
            Cmp::Eq => lhs.eq(rhs),
            Cmp::Ne => lhs.ne(rhs),
        }
    }
}

/// One term of a generated atom: `coeff · Π factors`. An empty factor list is a
/// constant. A factor index of `usize::MAX` is the **literal zero** factor (the
/// degenerate `0 · b` seed).
#[derive(Clone)]
struct Monomial {
    coeff: i64,
    factors: Vec<usize>,
    zero_factor: bool,
}

#[derive(Clone)]
struct Atom {
    monomials: Vec<Monomial>,
    cmp: Cmp,
    rhs: i64,
}

#[derive(Clone)]
struct Instance {
    bounds: Vec<Bound>,
    atoms: Vec<Atom>,
    /// Recorded only for the failure dump.
    degenerate: bool,
}

impl Instance {
    /// Generate one instance. Every third seed is a **degenerate-product** seed:
    /// pinned factors (including `0`), literal-zero factors, self-products,
    /// factors forced onto their bound, and empty windows.
    fn generate(rng: &mut Lcg, degenerate: bool) -> Instance {
        let num_vars = rng.below(3) + 2; // 2..=4
        let mut bounds = Vec::with_capacity(num_vars);
        for _ in 0..num_vars {
            let b = if degenerate {
                match rng.below(5) {
                    // A pinned factor, deliberately biased towards zero.
                    0 => Bound::Pinned(if rng.below(2) == 0 {
                        0
                    } else {
                        rng.in_range(-2, 2)
                    }),
                    // A degenerate one-point window (lo == hi).
                    1 => {
                        let k = rng.in_range(-2, 2);
                        Bound::Window(k, k)
                    }
                    // An EMPTY window (lo > hi) — the box is contradictory.
                    2 => {
                        let k = rng.in_range(-2, 2);
                        Bound::Window(k + 1, k)
                    }
                    3 => Bound::Window(0, 1),
                    _ => Bound::Lower(0),
                }
            } else {
                match rng.below(4) {
                    0 => {
                        let lo = rng.in_range(-2, 2);
                        Bound::Window(lo, lo + rng.in_range(0, 4))
                    }
                    1 => Bound::Lower(rng.in_range(-2, 2)),
                    2 => Bound::Pinned(rng.in_range(-3, 3)),
                    _ => Bound::Free,
                }
            };
            bounds.push(b);
        }

        let num_atoms = rng.below(3) + 1; // 1..=3
        let mut atoms = Vec::with_capacity(num_atoms);
        for _ in 0..num_atoms {
            let num_monos = rng.below(3) + 1; // 1..=3
            let mut monomials = Vec::with_capacity(num_monos);
            for _ in 0..num_monos {
                // Degree 1..=3 so nested products `(a·b)·c` are generated too:
                // that is where the derived-interval propagation is exercised.
                let degree = rng.below(3) + 1;
                let mut factors = Vec::with_capacity(degree);
                for _ in 0..degree {
                    factors.push(rng.below(num_vars as u64));
                }
                // Degenerate seeds sometimes make it a SELF-product `v·v`.
                if degenerate && rng.below(3) == 0 && !factors.is_empty() {
                    let v = factors[0];
                    factors = vec![v, v];
                }
                monomials.push(Monomial {
                    coeff: rng.in_range(-3, 3),
                    factors,
                    // A literal `0` factor: the product is syntactically `0 · b`.
                    zero_factor: degenerate && rng.below(4) == 0,
                });
            }
            atoms.push(Atom {
                monomials,
                cmp: Cmp::pick(rng),
                rhs: rng.in_range(-4, 4),
            });
        }
        Instance {
            bounds,
            atoms,
            degenerate,
        }
    }

    fn build(&self) -> (TermArena, Vec<SymbolId>, Vec<TermId>) {
        let mut a = TermArena::new();
        let syms: Vec<SymbolId> = (0..self.bounds.len())
            .map(|i| a.declare(&format!("v{i}"), Sort::Int).unwrap())
            .collect();
        let vars: Vec<TermId> = syms.iter().map(|&s| a.var(s)).collect();
        let mut assertions = Vec::new();

        for (i, bound) in self.bounds.iter().enumerate() {
            match *bound {
                Bound::Window(lo, hi) => {
                    let lo_t = a.int_const(i128::from(lo));
                    let hi_t = a.int_const(i128::from(hi));
                    assertions.push(a.int_ge(vars[i], lo_t).unwrap());
                    assertions.push(a.int_le(vars[i], hi_t).unwrap());
                }
                Bound::Lower(lo) => {
                    let lo_t = a.int_const(i128::from(lo));
                    assertions.push(a.int_ge(vars[i], lo_t).unwrap());
                }
                Bound::Pinned(k) => {
                    let k_t = a.int_const(i128::from(k));
                    assertions.push(a.eq(vars[i], k_t).unwrap());
                }
                Bound::Free => {}
            }
        }

        for atom in &self.atoms {
            let mut lhs: Option<TermId> = None;
            for m in &atom.monomials {
                let mut term = a.int_const(i128::from(m.coeff));
                if m.zero_factor {
                    let zero = a.int_const(0);
                    term = a.int_mul(term, zero).unwrap();
                }
                for &f in &m.factors {
                    term = a.int_mul(term, vars[f]).unwrap();
                }
                lhs = Some(match lhs {
                    None => term,
                    Some(acc) => a.int_add(acc, term).unwrap(),
                });
            }
            let lhs = lhs.unwrap_or_else(|| a.int_const(0));
            let rhs = a.int_const(i128::from(atom.rhs));
            assertions.push(atom.cmp.build(&mut a, lhs, rhs));
        }
        (a, syms, assertions)
    }

    fn to_z3(&self) -> Vec<Bool> {
        let vars: Vec<Int> = (0..self.bounds.len())
            .map(|i| Int::new_const(format!("v{i}")))
            .collect();
        let mut out = Vec::new();
        for (i, bound) in self.bounds.iter().enumerate() {
            match *bound {
                Bound::Window(lo, hi) => {
                    out.push(vars[i].ge(Int::from_i64(lo)));
                    out.push(vars[i].le(Int::from_i64(hi)));
                }
                Bound::Lower(lo) => out.push(vars[i].ge(Int::from_i64(lo))),
                Bound::Pinned(k) => out.push(vars[i].eq(Int::from_i64(k))),
                Bound::Free => {}
            }
        }
        for atom in &self.atoms {
            let mut lhs: Option<Int> = None;
            for m in &atom.monomials {
                let mut term = Int::from_i64(m.coeff);
                if m.zero_factor {
                    term = &term * &Int::from_i64(0);
                }
                for &f in &m.factors {
                    term = &term * &vars[f];
                }
                lhs = Some(match lhs {
                    None => term,
                    Some(acc) => &acc + &term,
                });
            }
            let lhs = lhs.unwrap_or_else(|| Int::from_i64(0));
            out.push(atom.cmp.build_z3(&lhs, &Int::from_i64(atom.rhs)));
        }
        out
    }

    fn dump(&self) -> String {
        format!(
            "degenerate={} bounds={:?} atoms={}",
            self.degenerate,
            self.bounds,
            self.atoms.len()
        )
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

/// `Some((verdict, replay_violation))`; `None` means the worker overran its cap
/// (adjudication-neutral).
fn solve_axeyum_bounded(inst: Instance) -> Option<(Verdict, Option<String>)> {
    let (tx, rx) = mpsc::channel();
    std::thread::spawn(move || {
        let (mut a, _syms, assertions) = inst.build();
        let config = SolverConfig::default().with_timeout(AXEYUM_SOLVE_BUDGET);
        let outcome = match solve(&mut a, &assertions, &config) {
            Err(_) => None,
            Ok(ax) => {
                let verdict = label(&ax);
                let violation = match &ax {
                    CheckResult::Sat(model) => {
                        let asg = model.to_assignment();
                        let mut bad = None;
                        for (i, &assertion) in assertions.iter().enumerate() {
                            if matches!(eval(&a, assertion, &asg), Ok(Value::Bool(false))) {
                                bad = Some(format!("atom {i} evaluated false at the model"));
                                break;
                            }
                        }
                        bad
                    }
                    _ => None,
                };
                Some((verdict, violation))
            }
        };
        let _ = tx.send(outcome);
    });
    match rx.recv_timeout(AXEYUM_WALL_TIMEOUT) {
        Ok(Some(outcome)) => Some(outcome),
        Ok(None) => {
            panic!("axeyum solve returned an error (Unknown must be a result, not an error)")
        }
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
fn qf_nia_bounded_product_differential_fuzz_disagree_zero() {
    let mut total = 0u64;
    let mut jointly_decided = 0u64;
    let mut degenerate_decided = 0u64;
    let mut axeyum_unknown = 0u64;
    let mut axeyum_timeout = 0u64;
    let mut z3_unknown = 0u64;

    for seed in 0..INSTANCES {
        total += 1;
        // Every third seed is a degenerate-product seed. The share is fixed (not
        // random) so the class can never be silently generated away.
        let degenerate = seed % 3 == 0;
        let mut rng = Lcg::new(seed);
        let inst = Instance::generate(&mut rng, degenerate);

        let z3_label = z3_decide(&inst);
        if z3_label == Verdict::Unknown {
            z3_unknown += 1;
            continue;
        }

        let Some((ax_label, violation)) = solve_axeyum_bounded(inst.clone()) else {
            axeyum_timeout += 1;
            continue;
        };

        assert!(
            violation.is_none(),
            "WRONG SAT (seed {seed}): axeyum returned Sat but its model does not \
             satisfy the original atoms: {}.\n{}",
            violation.unwrap_or_default(),
            inst.dump()
        );

        if ax_label == Verdict::Unknown {
            axeyum_unknown += 1;
            continue;
        }
        jointly_decided += 1;
        if degenerate {
            degenerate_decided += 1;
        }
        assert_eq!(
            ax_label,
            z3_label,
            "DISAGREEMENT (seed {seed}): axeyum = {ax_label:?}, Z3 = {z3_label:?}.\n{}",
            inst.dump()
        );
    }

    eprintln!(
        "[bounded-product-fuzz] total={total} joint={jointly_decided} \
         (degenerate joint={degenerate_decided}) axeyum_unknown={axeyum_unknown} \
         axeyum_timeout={axeyum_timeout} z3_unknown={z3_unknown}"
    );
    assert!(
        jointly_decided > 0,
        "the harness decided nothing jointly — the generator or the gate is inert"
    );
    assert!(
        degenerate_decided > 0,
        "the DEGENERATE-PRODUCT seed class decided nothing jointly — the class is \
         inert and the gate is blind exactly where the lemmas are most fragile"
    );
}
