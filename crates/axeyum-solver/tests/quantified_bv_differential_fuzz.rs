//! Adversarial differential soundness fuzzer for the **quantified** bit-vector
//! decision path (`solve` over top-level `∀`, Track 2 P2.6) against the Z3 oracle.
//!
//! P2.6 slice 6 added a *closed-universal falsification* lever: a closed
//! `∀x⃗. body` (quantifier-free body over exactly its bound variables) is decided
//! by falsifying `¬body[x⃗ := c⃗]` — `Unsat` when the sentence is false, declined
//! when valid. That lever *creates new sat/unsat verdicts*, so it needs a
//! differential net: this harness deterministically generates hundreds of small
//! **closed** `∀x y. body` bit-vector sentences (a fixed-seed LCG drives every
//! choice — no clock, no entropy), lowers the *same* abstract body to both an
//! axeyum term and a Z3 `BV`/`Bool` (so the two sides are semantically identical
//! by construction), decides each with the default pure-Rust `solve` and with a
//! direct Z3 quantified query, and gates on the joint verdict:
//!
//! - axeyum `Unsat` ∧ Z3 `Sat` → **PANIC** (wrong unsat — the worst bug, the one
//!   the new lever could introduce).
//! - axeyum `Sat` ∧ Z3 `Unsat` → **PANIC** (wrong sat).
//! - axeyum `Unknown` is ALLOWED (incomplete is sound) — counted, never failed.
//! - Z3 `Unknown` → the instance is skipped (cannot adjudicate).
//!
//! The test passes iff disagreements == 0 over the whole sweep.
//!
//! Every construct — `bvnot, bvand, bvor, bvxor, bvadd` and `{=, and, or, not}` —
//! is total and convention-free, so the two engines' semantics coincide exactly;
//! the universal closure is built with `forall_const` on the same bound constants.

#![cfg(feature = "z3")]
#![allow(
    clippy::trivially_copy_pass_by_ref,
    clippy::many_single_char_names,
    clippy::similar_names
)]

use axeyum_ir::{Sort, SymbolId, TermArena, TermId};
use axeyum_solver::{CheckResult, SolverConfig, solve};
use z3::ast::{Ast, BV, Bool};
use z3::{SatResult, Solver};

/// Number of closed-universal sentences generated and adjudicated (well past the
/// ≥300 floor the mandate sets).
const INSTANCES: u64 = 600;

/// Bit-vector width. Small so both engines decide instantly.
const W: u32 = 4;

/// A deterministic linear-congruential PRNG (MMIX constants) — the house convention.
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
    fn bv(&mut self) -> u64 {
        self.next_u64() % (1 << W)
    }
}

/// Abstract bit-vector expression over the two bound variables (index 0/1).
enum BvE {
    Var(usize),
    Const(u64),
    And(Box<BvE>, Box<BvE>),
    Or(Box<BvE>, Box<BvE>),
    Xor(Box<BvE>, Box<BvE>),
    Add(Box<BvE>, Box<BvE>),
    Not(Box<BvE>),
}

/// Abstract Boolean expression — the universal's body.
enum BoolE {
    Eq(BvE, BvE),
    And(Box<BoolE>, Box<BoolE>),
    Or(Box<BoolE>, Box<BoolE>),
    Not(Box<BoolE>),
}

fn gen_bv(rng: &mut Lcg, depth: u32) -> BvE {
    if depth == 0 || rng.below(2) == 0 {
        return if rng.below(2) == 0 {
            BvE::Var(rng.below(2))
        } else {
            BvE::Const(rng.bv())
        };
    }
    let l = Box::new(gen_bv(rng, depth - 1));
    match rng.below(5) {
        0 => BvE::And(l, Box::new(gen_bv(rng, depth - 1))),
        1 => BvE::Or(l, Box::new(gen_bv(rng, depth - 1))),
        2 => BvE::Xor(l, Box::new(gen_bv(rng, depth - 1))),
        3 => BvE::Add(l, Box::new(gen_bv(rng, depth - 1))),
        _ => BvE::Not(l),
    }
}

fn gen_bool(rng: &mut Lcg, depth: u32) -> BoolE {
    if depth == 0 || rng.below(2) == 0 {
        return BoolE::Eq(gen_bv(rng, depth), gen_bv(rng, depth));
    }
    match rng.below(3) {
        0 => BoolE::And(
            Box::new(gen_bool(rng, depth - 1)),
            Box::new(gen_bool(rng, depth - 1)),
        ),
        1 => BoolE::Or(
            Box::new(gen_bool(rng, depth - 1)),
            Box::new(gen_bool(rng, depth - 1)),
        ),
        _ => BoolE::Not(Box::new(gen_bool(rng, depth - 1))),
    }
}

/// Lower an abstract BV expression to an axeyum term over the given bound vars.
fn lower_bv_axeyum(arena: &mut TermArena, e: &BvE, vars: &[TermId]) -> TermId {
    match e {
        BvE::Var(i) => vars[*i],
        BvE::Const(c) => arena.bv_const(W, u128::from(*c)).unwrap(),
        BvE::And(a, b) => {
            let (a, b) = (
                lower_bv_axeyum(arena, a, vars),
                lower_bv_axeyum(arena, b, vars),
            );
            arena.bv_and(a, b).unwrap()
        }
        BvE::Or(a, b) => {
            let (a, b) = (
                lower_bv_axeyum(arena, a, vars),
                lower_bv_axeyum(arena, b, vars),
            );
            arena.bv_or(a, b).unwrap()
        }
        BvE::Xor(a, b) => {
            let (a, b) = (
                lower_bv_axeyum(arena, a, vars),
                lower_bv_axeyum(arena, b, vars),
            );
            arena.bv_xor(a, b).unwrap()
        }
        BvE::Add(a, b) => {
            let (a, b) = (
                lower_bv_axeyum(arena, a, vars),
                lower_bv_axeyum(arena, b, vars),
            );
            arena.bv_add(a, b).unwrap()
        }
        BvE::Not(a) => {
            let a = lower_bv_axeyum(arena, a, vars);
            arena.bv_not(a).unwrap()
        }
    }
}

fn lower_bool_axeyum(arena: &mut TermArena, e: &BoolE, vars: &[TermId]) -> TermId {
    match e {
        BoolE::Eq(a, b) => {
            let (a, b) = (
                lower_bv_axeyum(arena, a, vars),
                lower_bv_axeyum(arena, b, vars),
            );
            arena.eq(a, b).unwrap()
        }
        BoolE::And(a, b) => {
            let (a, b) = (
                lower_bool_axeyum(arena, a, vars),
                lower_bool_axeyum(arena, b, vars),
            );
            arena.and(a, b).unwrap()
        }
        BoolE::Or(a, b) => {
            let (a, b) = (
                lower_bool_axeyum(arena, a, vars),
                lower_bool_axeyum(arena, b, vars),
            );
            arena.or(a, b).unwrap()
        }
        BoolE::Not(a) => {
            let a = lower_bool_axeyum(arena, a, vars);
            arena.not(a).unwrap()
        }
    }
}

fn lower_bv_z3(e: &BvE, vars: &[BV]) -> BV {
    match e {
        BvE::Var(i) => vars[*i].clone(),
        BvE::Const(c) => BV::from_u64(*c, W),
        BvE::And(a, b) => lower_bv_z3(a, vars).bvand(lower_bv_z3(b, vars)),
        BvE::Or(a, b) => lower_bv_z3(a, vars).bvor(lower_bv_z3(b, vars)),
        BvE::Xor(a, b) => lower_bv_z3(a, vars).bvxor(lower_bv_z3(b, vars)),
        BvE::Add(a, b) => lower_bv_z3(a, vars).bvadd(lower_bv_z3(b, vars)),
        BvE::Not(a) => lower_bv_z3(a, vars).bvnot(),
    }
}

fn lower_bool_z3(e: &BoolE, vars: &[BV]) -> Bool {
    match e {
        BoolE::Eq(a, b) => lower_bv_z3(a, vars).eq(lower_bv_z3(b, vars)),
        BoolE::And(a, b) => Bool::and(&[lower_bool_z3(a, vars), lower_bool_z3(b, vars)]),
        BoolE::Or(a, b) => Bool::or(&[lower_bool_z3(a, vars), lower_bool_z3(b, vars)]),
        BoolE::Not(a) => lower_bool_z3(a, vars).not(),
    }
}

#[test]
fn quantified_bv_differential_matches_z3() {
    let cfg = SolverConfig::default();
    let mut compared = 0u64;
    let mut axeyum_unknown = 0u64;
    let mut z3_unknown = 0u64;
    let mut disagree = 0u64;

    for seed in 0..INSTANCES {
        let mut rng = Lcg::new(seed);
        let body = gen_bool(&mut rng, 3);

        // axeyum side: (assert (forall x y. body)).
        let mut arena = TermArena::new();
        let x: SymbolId = arena.declare("x", Sort::BitVec(W)).unwrap();
        let y: SymbolId = arena.declare("y", Sort::BitVec(W)).unwrap();
        let xv = arena.var(x);
        let yv = arena.var(y);
        let ax_body = lower_bool_axeyum(&mut arena, &body, &[xv, yv]);
        let inner = arena.forall(y, ax_body).unwrap();
        let forall = arena.forall(x, inner).unwrap();
        let ax = solve(&mut arena, &[forall], &cfg).expect("axeyum solve ok");

        // z3 side: the same body, universally closed over the same two constants.
        let zx = BV::new_const("x", W);
        let zy = BV::new_const("y", W);
        let z3_body = lower_bool_z3(&body, &[zx.clone(), zy.clone()]);
        let z3_forall = z3::ast::forall_const(&[&zx as &dyn Ast, &zy as &dyn Ast], &[], &z3_body);
        let solver = Solver::new();
        solver.assert(&z3_forall);
        let z3v = solver.check();

        match (ax, z3v) {
            (CheckResult::Unknown(_), _) => axeyum_unknown += 1,
            (_, SatResult::Unknown) => z3_unknown += 1,
            (CheckResult::Sat(_), SatResult::Sat) | (CheckResult::Unsat, SatResult::Unsat) => {
                compared += 1;
            }
            (ax, z3v) => {
                disagree += 1;
                eprintln!("DISAGREE seed={seed}: axeyum={ax:?} z3={z3v:?}");
            }
        }
    }

    eprintln!(
        "quantified-BV differential: compared={compared} agree, axeyum_unknown={axeyum_unknown}, \
         z3_unknown={z3_unknown}, disagree={disagree}"
    );
    assert_eq!(
        disagree, 0,
        "axeyum vs Z3 disagreed on a quantified BV verdict"
    );
    assert!(
        compared >= 50,
        "too few adjudicated agreements ({compared}) — the sweep is degenerate"
    );
}

// ===========================================================================
// Nested-polarity extension (DEBT 3): a closed `∀x y. body` embedded under a
// top-level `or` / `and` / `not` / `ite` with free ground variables. The
// closed-universal falsification lever must fire ONLY on a *top-level positively-
// asserted* universal; a `∀` under `or`/`not`/`ite` being false does NOT make the
// assertion unsat. This sweep lowers each nested shape identically to axeyum and
// Z3 and gates on the joint verdict, so any wrong-polarity refutation (the hazard
// the lever could introduce) surfaces as a disagreement.
// ===========================================================================

/// Number of nested-polarity sentences adjudicated (well past the ≥200 floor).
const NESTED_INSTANCES: u64 = 400;

/// Generate a BV expression whose variables are drawn from the half-open index
/// range `[lo, hi)` — lets the universal's body range over the bound vars `{0,1}`
/// while a ground atom ranges over the free vars `{2,3}`.
fn gen_bv_range(rng: &mut Lcg, depth: u32, lo: usize, hi: usize) -> BvE {
    if depth == 0 || rng.below(2) == 0 {
        return if rng.below(2) == 0 {
            BvE::Var(lo + rng.below((hi - lo) as u64))
        } else {
            BvE::Const(rng.bv())
        };
    }
    let l = Box::new(gen_bv_range(rng, depth - 1, lo, hi));
    match rng.below(5) {
        0 => BvE::And(l, Box::new(gen_bv_range(rng, depth - 1, lo, hi))),
        1 => BvE::Or(l, Box::new(gen_bv_range(rng, depth - 1, lo, hi))),
        2 => BvE::Xor(l, Box::new(gen_bv_range(rng, depth - 1, lo, hi))),
        3 => BvE::Add(l, Box::new(gen_bv_range(rng, depth - 1, lo, hi))),
        _ => BvE::Not(l),
    }
}

/// Generate a Boolean expression over the BV variables in `[lo, hi)`.
fn gen_bool_range(rng: &mut Lcg, depth: u32, lo: usize, hi: usize) -> BoolE {
    if depth == 0 || rng.below(2) == 0 {
        return BoolE::Eq(
            gen_bv_range(rng, depth, lo, hi),
            gen_bv_range(rng, depth, lo, hi),
        );
    }
    match rng.below(3) {
        0 => BoolE::And(
            Box::new(gen_bool_range(rng, depth - 1, lo, hi)),
            Box::new(gen_bool_range(rng, depth - 1, lo, hi)),
        ),
        1 => BoolE::Or(
            Box::new(gen_bool_range(rng, depth - 1, lo, hi)),
            Box::new(gen_bool_range(rng, depth - 1, lo, hi)),
        ),
        _ => BoolE::Not(Box::new(gen_bool_range(rng, depth - 1, lo, hi))),
    }
}

/// The four nested-polarity wrapper shapes: the universal `∀` (already lowered)
/// combined with a ground bool `g` over the free vars.
#[derive(Clone, Copy)]
enum Shape {
    OrGround,
    AndGround,
    NotForall,
    IteThen,
}

fn shape_of(rng: &mut Lcg) -> Shape {
    match rng.below(4) {
        0 => Shape::OrGround,
        1 => Shape::AndGround,
        2 => Shape::NotForall,
        _ => Shape::IteThen,
    }
}

#[test]
fn quantified_bv_nested_polarity_matches_z3() {
    let cfg = SolverConfig::default();
    let mut compared = 0u64;
    let mut axeyum_unknown = 0u64;
    let mut axeyum_declined = 0u64;
    let mut z3_unknown = 0u64;
    let mut disagree = 0u64;

    for seed in 0..NESTED_INSTANCES {
        // Offset the seed stream so it does not alias the top-level sweep.
        let mut rng = Lcg::new(seed ^ 0xD1CE_5EED_A5A5_1234);
        let body = gen_bool_range(&mut rng, 3, 0, 2); // universal body over x, y
        let ground = gen_bool_range(&mut rng, 2, 2, 4); // ground atom over p, q
        let shape = shape_of(&mut rng);

        // ---- axeyum side ----
        let mut arena = TermArena::new();
        let x = arena.declare("x", Sort::BitVec(W)).unwrap();
        let y = arena.declare("y", Sort::BitVec(W)).unwrap();
        let p = arena.declare("p", Sort::BitVec(W)).unwrap();
        let q = arena.declare("q", Sort::BitVec(W)).unwrap();
        let vars = [arena.var(x), arena.var(y), arena.var(p), arena.var(q)];
        let ax_body = lower_bool_axeyum(&mut arena, &body, &vars);
        let inner = arena.forall(y, ax_body).unwrap();
        let ax_forall = arena.forall(x, inner).unwrap();
        let ax_ground = lower_bool_axeyum(&mut arena, &ground, &vars);
        let tru = arena.bool_const(true);
        let ax_assertion = match shape {
            Shape::OrGround => arena.or(ax_forall, ax_ground).unwrap(),
            Shape::AndGround => arena.and(ax_forall, ax_ground).unwrap(),
            Shape::NotForall => arena.not(ax_forall).unwrap(),
            Shape::IteThen => arena.ite(ax_ground, ax_forall, tru).unwrap(),
        };
        // An `Err` (a residual the front door declines) is NOT a verdict — treat it
        // as `unknown`, never a panic (unknown is first-class, never a wrong answer).
        let Ok(ax) = solve(&mut arena, &[ax_assertion], &cfg) else {
            axeyum_declined += 1;
            continue;
        };

        // ---- z3 side: the same nested structure over the same constants ----
        let zx = BV::new_const("x", W);
        let zy = BV::new_const("y", W);
        let zp = BV::new_const("p", W);
        let zq = BV::new_const("q", W);
        let zvars = [zx.clone(), zy.clone(), zp.clone(), zq.clone()];
        let z3_body = lower_bool_z3(&body, &zvars);
        let z3_forall = z3::ast::forall_const(&[&zx as &dyn Ast, &zy as &dyn Ast], &[], &z3_body);
        let z3_ground = lower_bool_z3(&ground, &zvars);
        let z3_true = Bool::from_bool(true);
        let z3_assertion = match shape {
            Shape::OrGround => Bool::or(&[z3_forall, z3_ground]),
            Shape::AndGround => Bool::and(&[z3_forall, z3_ground]),
            Shape::NotForall => z3_forall.not(),
            Shape::IteThen => z3_ground.ite(&z3_forall, &z3_true),
        };
        let solver = Solver::new();
        solver.assert(&z3_assertion);
        let z3v = solver.check();

        match (ax, z3v) {
            (CheckResult::Unknown(_), _) => axeyum_unknown += 1,
            (_, SatResult::Unknown) => z3_unknown += 1,
            (CheckResult::Sat(_), SatResult::Sat) | (CheckResult::Unsat, SatResult::Unsat) => {
                compared += 1;
            }
            (ax, z3v) => {
                disagree += 1;
                eprintln!("NESTED DISAGREE seed={seed}: axeyum={ax:?} z3={z3v:?}");
            }
        }
    }

    eprintln!(
        "nested-polarity differential: compared={compared} agree, \
         axeyum_unknown={axeyum_unknown}, axeyum_declined={axeyum_declined}, \
         z3_unknown={z3_unknown}, disagree={disagree}"
    );
    assert_eq!(
        disagree, 0,
        "axeyum vs Z3 disagreed on a nested-polarity quantified BV verdict"
    );
    assert!(
        compared >= 50,
        "too few adjudicated nested-polarity agreements ({compared}) — degenerate sweep"
    );
}
