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

use std::time::Duration;

use axeyum_ir::{Sort, SymbolId, TermArena, TermId};
use axeyum_solver::{CheckResult, Evidence, SolverConfig, produce_evidence, solve};
use z3::ast::{Ast, BV, Bool};
use z3::{FuncDecl, Params, SatResult, Solver, Sort as Z3Sort};

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

/// ADR-0124 alternation controls: half carry a concrete outer value that makes
/// the existential residual contradictory; half have an immediate witness.
#[test]
fn quantified_bv_alternation_counterexamples_match_z3() {
    let cfg = SolverConfig::new().with_timeout(Duration::from_secs(2));
    let mut certified_unsat = 0u64;
    let mut agreed_sat = 0u64;

    for case in 0..64u64 {
        let pivot = case % (1 << W);
        let sat_case = case % 2 == 1;

        let mut arena = TermArena::new();
        let x = arena.declare("alt_x", Sort::BitVec(W)).unwrap();
        let y = arena.declare("alt_y", Sort::BitVec(W)).unwrap();
        let x_term = arena.var(x);
        let y_term = arena.var(y);
        let pivot_term = arena.bv_const(W, u128::from(pivot)).unwrap();
        let guard = arena.eq(x_term, pivot_term).unwrap();
        let consequent = if sat_case {
            arena.eq(y_term, x_term).unwrap()
        } else {
            let reflexive = arena.eq(y_term, y_term).unwrap();
            arena.not(reflexive).unwrap()
        };
        let matrix = arena.implies(guard, consequent).unwrap();
        let exists = arena.exists(y, matrix).unwrap();
        let assertion = arena.forall(x, exists).unwrap();
        let report = produce_evidence(&mut arena, &[assertion], &cfg).unwrap();

        let zx = BV::new_const("alt_x", W);
        let zy = BV::new_const("alt_y", W);
        let zpivot = BV::from_u64(pivot, W);
        let zguard = zx.eq(zpivot);
        let zconsequent = if sat_case {
            zy.eq(&zx)
        } else {
            zy.eq(&zy).not()
        };
        let zmatrix = zguard.implies(&zconsequent);
        let zexists = z3::ast::exists_const(&[&zy as &dyn Ast], &[], &zmatrix);
        let zforall = z3::ast::forall_const(&[&zx as &dyn Ast], &[], &zexists);
        let solver = Solver::new();
        solver.assert(&zforall);
        let oracle = solver.check();

        match (&report.evidence, oracle, sat_case) {
            (Evidence::Sat(_), SatResult::Sat, true) => agreed_sat += 1,
            (Evidence::UnsatBvAlternationCounterexample(_), SatResult::Unsat, false) => {
                assert!(report.evidence.check(&arena, &[assertion]).unwrap());
                certified_unsat += 1;
            }
            (evidence, oracle, _) => panic!(
                "alternation disagreement case={case}: evidence={} oracle={oracle:?}",
                evidence.kind_label()
            ),
        }
    }

    assert_eq!(certified_unsat, 32);
    assert_eq!(agreed_sat, 32);
}

/// ADR-0125 scaling controls deliberately exceed ADR-0124's original
/// 128-binder cap while remaining semantically trivial enough for an
/// independent direct-Z3 verdict.
#[test]
fn scaled_bv_alternation_prefixes_match_z3() {
    const OUTER: usize = 160;
    let cfg = SolverConfig::new().with_timeout(Duration::from_secs(2));
    let mut certified_unsat = 0;
    let mut safe_sat = 0;

    for case in 0..16 {
        let sat_case = case % 2 == 1;
        let mut arena = TermArena::new();
        let binders = (0..OUTER)
            .map(|index| {
                arena
                    .declare(&format!("scaled_x_{index}"), Sort::Bool)
                    .unwrap()
            })
            .collect::<Vec<_>>();
        let y = arena.declare("scaled_y", Sort::Bool).unwrap();
        let guard = arena.var(binders[0]);
        let y_term = arena.var(y);
        let reflexive = arena.eq(y_term, y_term).unwrap();
        let consequent = if sat_case {
            reflexive
        } else {
            arena.not(reflexive).unwrap()
        };
        let matrix = arena.implies(guard, consequent).unwrap();
        let mut assertion = arena.exists(y, matrix).unwrap();
        for &binder in binders.iter().rev() {
            assertion = arena.forall(binder, assertion).unwrap();
        }
        let report = produce_evidence(&mut arena, &[assertion], &cfg).unwrap();

        let zouter = (0..OUTER)
            .map(|index| Bool::new_const(format!("scaled_x_{index}")))
            .collect::<Vec<_>>();
        let zy = Bool::new_const("scaled_y");
        let zconsequent = if sat_case {
            zy.eq(&zy)
        } else {
            zy.eq(&zy).not()
        };
        let zmatrix = zouter[0].implies(&zconsequent);
        let zexists = z3::ast::exists_const(&[&zy as &dyn Ast], &[], &zmatrix);
        let refs = zouter
            .iter()
            .map(|term| term as &dyn Ast)
            .collect::<Vec<_>>();
        let zforall = z3::ast::forall_const(&refs, &[], &zexists);
        let solver = Solver::new();
        solver.assert(&zforall);
        let oracle = solver.check();

        if sat_case {
            assert_eq!(oracle, SatResult::Sat);
            assert!(!matches!(
                report.evidence,
                Evidence::UnsatBvAlternationCounterexample(_)
            ));
            safe_sat += 1;
        } else {
            assert_eq!(oracle, SatResult::Unsat);
            assert!(matches!(
                report.evidence,
                Evidence::UnsatBvAlternationCounterexample(_)
            ));
            assert!(report.evidence.check(&arena, &[assertion]).unwrap());
            certified_unsat += 1;
        }
    }

    assert_eq!(certified_unsat, 8);
    assert_eq!(safe_sat, 8);
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

#[test]
fn sat_candidate_nested_trigger_matrix_matches_z3() {
    const CASES: usize = 64;
    const WIDTH: u32 = 16;

    let config = SolverConfig::default();
    let mut recovered_unsat = 0usize;
    let mut definitive_sat = 0usize;
    let mut unknown_sat = 0usize;
    for case in 0..CASES {
        let mode = case % 4;

        let mut arena = TermArena::new();
        let sort = Sort::BitVec(WIDTH);
        let a = arena.bv_var("candidate_matrix_a", WIDTH).unwrap();
        let b = arena.bv_var("candidate_matrix_b", WIDTH).unwrap();
        let c = arena.bv_var("candidate_matrix_c", WIDTH).unwrap();
        let p = arena.bool_var("candidate_matrix_p").unwrap();
        let f = arena
            .declare_fun("candidate_matrix_f", &[sort], sort)
            .unwrap();
        let g = arena
            .declare_fun("candidate_matrix_g", &[sort], sort)
            .unwrap();
        let gb = arena.apply(g, &[b]).unwrap();
        let fa = arena.apply(f, &[a]).unwrap();
        let a_eq_gb = arena.eq(a, gb).unwrap();
        let branch_literal = if mode == 2 {
            arena.not(a_eq_gb).unwrap()
        } else {
            a_eq_gb
        };
        let branch = arena.or(branch_literal, p).unwrap();
        let not_p = arena.not(p).unwrap();
        let fa_eq_c = arena.eq(fa, c).unwrap();
        let x = arena.declare("candidate_matrix_x", sort).unwrap();
        let xv = arena.var(x);
        let gx = arena.apply(g, &[xv]).unwrap();
        let fgx = arena.apply(f, &[gx]).unwrap();
        let fgx_eq_c = arena.eq(fgx, c).unwrap();
        let body = if mode == 3 {
            fgx_eq_c
        } else {
            arena.not(fgx_eq_c).unwrap()
        };
        let universal = arena.forall(x, body).unwrap();
        let mut assertions = vec![branch, fa_eq_c, universal];
        if mode != 1 {
            assertions.push(not_p);
        }
        let axeyum = solve(&mut arena, &assertions, &config).expect("candidate matrix solve");

        let bv_sort = Z3Sort::bitvector(WIDTH);
        let zf = FuncDecl::new("candidate_matrix_f", &[&bv_sort], &bv_sort);
        let zg = FuncDecl::new("candidate_matrix_g", &[&bv_sort], &bv_sort);
        let za = BV::new_const("candidate_matrix_a", WIDTH);
        let zb = BV::new_const("candidate_matrix_b", WIDTH);
        let zc = BV::new_const("candidate_matrix_c", WIDTH);
        let zp = Bool::new_const("candidate_matrix_p");
        let zgb = zg.apply(&[&zb as &dyn Ast]).as_bv().expect("g returns BV");
        let zfa = zf.apply(&[&za as &dyn Ast]).as_bv().expect("f returns BV");
        let za_eq_gb = za.eq(&zgb);
        let zbranch_literal = if mode == 2 { za_eq_gb.not() } else { za_eq_gb };
        let zbranch = Bool::or(&[zbranch_literal, zp.clone()]);
        let zx = BV::new_const("candidate_matrix_x", WIDTH);
        let zgx = zg.apply(&[&zx as &dyn Ast]).as_bv().expect("g returns BV");
        let zfgx = zf.apply(&[&zgx as &dyn Ast]).as_bv().expect("f returns BV");
        let zbody_eq = zfgx.eq(&zc);
        let zbody = if mode == 3 { zbody_eq } else { zbody_eq.not() };
        let zforall = z3::ast::forall_const(&[&zx as &dyn Ast], &[], &zbody);
        let z3 = Solver::new();
        z3.assert(&zbranch);
        z3.assert(zfa.eq(&zc));
        z3.assert(&zforall);
        if mode != 1 {
            z3.assert(zp.not());
        }
        let oracle = z3.check();

        match (mode, &axeyum, oracle) {
            (0, CheckResult::Unsat, SatResult::Unsat) => recovered_unsat += 1,
            (0, _, _) => panic!(
                "candidate-guided UNSAT case {case} did not agree: axeyum={axeyum:?} z3={oracle:?}"
            ),
            (_, CheckResult::Sat(_), SatResult::Sat) => definitive_sat += 1,
            (_, CheckResult::Unknown(_), SatResult::Sat) => unknown_sat += 1,
            _ => panic!(
                "candidate satisfiable control {case} disagreed: axeyum={axeyum:?} z3={oracle:?}"
            ),
        }
    }
    eprintln!(
        "SAT-candidate nested-trigger differential: recovered_unsat={recovered_unsat}, definitive_sat={definitive_sat}, unknown_sat={unknown_sat}"
    );
    assert_eq!(recovered_unsat, CASES / 4);
}

#[test]
fn reflexive_skolem_bv_matrix_matches_z3() {
    const CASES: usize = 64;
    const WIDTHS: [u32; 8] = [1, 2, 3, 4, 8, 16, 32, 64];

    let config = SolverConfig::new().with_timeout(Duration::from_millis(100));
    let mut certified_sat = 0usize;
    let mut agreed_unsat = 0usize;
    let mut safe_unknown = 0usize;
    let mut oracle_unknown = 0usize;
    for case in 0..CASES {
        let mode = case % 4;
        let width = WIDTHS[(case / 4) % WIDTHS.len()];

        let mut arena = TermArena::new();
        let sort = Sort::BitVec(width);
        let a = arena.declare("skolem_matrix_a", sort).unwrap();
        let b = arena.declare("skolem_matrix_b", sort).unwrap();
        let av = arena.var(a);
        let bv = arena.var(b);
        let body = match mode {
            0 => arena.bv_sle(av, bv).unwrap(),
            1 => arena.bv_ule(av, bv).unwrap(),
            2 => arena.bv_slt(av, bv).unwrap(),
            _ => {
                let not_a = arena.bv_not(av).unwrap();
                arena.bv_sle(not_a, bv).unwrap()
            }
        };
        let exists = arena.exists(b, body).unwrap();
        let assertion = arena.forall(a, exists).unwrap();
        let axeyum = solve(&mut arena, &[assertion], &config).expect("Skolem matrix solve");

        let za = BV::new_const("skolem_matrix_a", width);
        let zb = BV::new_const("skolem_matrix_b", width);
        let zbody = match mode {
            0 => za.bvsle(&zb),
            1 => za.bvule(&zb),
            2 => za.bvslt(&zb),
            _ => za.bvnot().bvsle(&zb),
        };
        let zexists = z3::ast::exists_const(&[&zb as &dyn Ast], &[], &zbody);
        let zforall = z3::ast::forall_const(&[&za as &dyn Ast], &[], &zexists);
        let oracle = Solver::new();
        let mut params = Params::new();
        params.set_u32("timeout", 100);
        oracle.set_params(&params);
        oracle.assert(&zforall);
        let z3 = oracle.check();

        match (mode, &axeyum, z3) {
            (0 | 1, CheckResult::Sat(model), SatResult::Sat) => {
                assert!(
                    axeyum_solver::check_model(&arena, &[assertion], model)
                        .expect("Skolem matrix model replay"),
                    "case {case}, width {width} returned an unreplayable model: {model:?}"
                );
                certified_sat += 1;
            }
            (0 | 1, _, _) => panic!(
                "identity Skolem case {case}, width {width} was not jointly Sat: axeyum={axeyum:?}, z3={z3:?}"
            ),
            (_, CheckResult::Sat(model), SatResult::Sat) => {
                assert!(
                    axeyum_solver::check_model(&arena, &[assertion], model)
                        .expect("Skolem matrix model replay"),
                    "case {case}, width {width} returned an unreplayable model: {model:?}"
                );
                certified_sat += 1;
            }
            (_, CheckResult::Unsat, SatResult::Unsat) => agreed_unsat += 1,
            (_, CheckResult::Unknown(_), SatResult::Sat | SatResult::Unsat) => safe_unknown += 1,
            (_, _, SatResult::Unknown) => oracle_unknown += 1,
            _ => panic!(
                "reflexive Skolem case {case}, width {width} disagreed: axeyum={axeyum:?}, z3={z3:?}"
            ),
        }
    }
    eprintln!(
        "reflexive Skolem differential: certified_sat={certified_sat}, agreed_unsat={agreed_unsat}, safe_unknown={safe_unknown}, oracle_unknown={oracle_unknown}"
    );
    assert!(certified_sat >= CASES / 2);
}

#[test]
#[allow(clippy::too_many_lines)]
fn vacuous_outer_guard_matrix_matches_z3() {
    const CASES: usize = 64;
    const WIDTHS: [u32; 8] = [1, 2, 8, 16, 32, 64, 129, 257];

    let config = SolverConfig::new().with_timeout(Duration::from_millis(100));
    let mut certified_guard_sat = 0usize;
    let mut safe_near_sat = 0usize;
    let mut agreed_unsat = 0usize;
    let mut safe_unknown = 0usize;
    for case in 0..CASES {
        let mode = case % 4;
        let width = WIDTHS[(case / 4) % WIDTHS.len()];
        let raw_constant = u128::try_from(case * 17 + 3).unwrap();
        let constant = if width < 128 {
            raw_constant & ((1u128 << width) - 1)
        } else {
            raw_constant
        };

        let mut arena = TermArena::new();
        let sort = Sort::BitVec(width);
        let a = arena.declare("guard_matrix_a", sort).unwrap();
        let b = arena.declare("guard_matrix_b", sort).unwrap();
        let p = arena.declare("guard_matrix_p", Sort::Bool).unwrap();
        let av = arena.var(a);
        let bv = arena.var(b);
        let kv = arena.bv_const(width, constant).unwrap();
        let equality = if mode == 1 {
            arena.eq(av, kv).unwrap()
        } else if mode == 3 {
            arena.eq(av, bv).unwrap()
        } else {
            arena.eq(kv, av).unwrap()
        };
        let antecedent = if mode == 2 {
            arena.not(equality).unwrap()
        } else {
            equality
        };
        let falsity = arena.bool_const(false);
        let matrix = arena.implies(antecedent, falsity).unwrap();
        let body = if mode == 3 {
            arena.forall(b, matrix).unwrap()
        } else {
            let inner = arena.exists(b, matrix).unwrap();
            arena.forall(p, inner).unwrap()
        };
        let assertion = arena.exists(a, body).unwrap();
        let axeyum = solve(&mut arena, &[assertion], &config).expect("guard matrix solve");

        let za = BV::new_const("guard_matrix_a", width);
        let zb = BV::new_const("guard_matrix_b", width);
        let zp = Bool::new_const("guard_matrix_p");
        let zk = BV::from_u64(u64::try_from(constant).unwrap(), width);
        let zequality = if mode == 1 {
            za.eq(&zk)
        } else if mode == 3 {
            za.eq(&zb)
        } else {
            zk.eq(&za)
        };
        let zantecedent = if mode == 2 {
            zequality.not()
        } else {
            zequality
        };
        let zmatrix = zantecedent.implies(Bool::from_bool(false));
        let zbody = if mode == 3 {
            z3::ast::forall_const(&[&zb as &dyn Ast], &[], &zmatrix)
        } else {
            let inner = z3::ast::exists_const(&[&zb as &dyn Ast], &[], &zmatrix);
            z3::ast::forall_const(&[&zp as &dyn Ast], &[], &inner)
        };
        let zassertion = z3::ast::exists_const(&[&za as &dyn Ast], &[], &zbody);
        let oracle = Solver::new();
        let mut params = Params::new();
        params.set_u32("timeout", 100);
        oracle.set_params(&params);
        oracle.assert(&zassertion);
        let z3 = oracle.check();

        match (mode, &axeyum, z3) {
            (0 | 1, CheckResult::Sat(model), SatResult::Sat) => {
                assert_eq!(model.quantified_guard_sat_certificates().count(), 1);
                assert!(
                    axeyum_solver::check_model(&arena, &[assertion], model)
                        .expect("guard matrix replay"),
                    "supported case {case}, width {width} failed replay"
                );
                certified_guard_sat += 1;
            }
            (0 | 1, _, _) => panic!(
                "supported guard case {case}, width {width} was not jointly Sat: axeyum={axeyum:?}, z3={z3:?}"
            ),
            (2, CheckResult::Sat(model), SatResult::Sat) => {
                assert_eq!(model.quantified_guard_sat_certificates().count(), 0);
                assert!(
                    axeyum_solver::check_model(&arena, &[assertion], model)
                        .expect("near-Sat replay")
                );
                safe_near_sat += 1;
            }
            (2, CheckResult::Unknown(_), SatResult::Sat)
            | (3, CheckResult::Unknown(_), SatResult::Unsat)
            | (_, _, SatResult::Unknown) => safe_unknown += 1,
            (3, CheckResult::Unsat, SatResult::Unsat) => agreed_unsat += 1,
            _ => panic!(
                "vacuous guard case {case}, width {width} disagreed: axeyum={axeyum:?}, z3={z3:?}"
            ),
        }
    }
    eprintln!(
        "vacuous guard differential: certified_guard_sat={certified_guard_sat}, safe_near_sat={safe_near_sat}, agreed_unsat={agreed_unsat}, safe_unknown={safe_unknown}"
    );
    assert_eq!(certified_guard_sat, CASES / 2);
}

#[test]
#[allow(clippy::too_many_lines)]
fn boolean_discharge_of_opaque_bv_closures_matches_z3() {
    const CASES: usize = 64;
    const WIDTHS: [u32; 8] = [1, 2, 8, 16, 32, 64, 129, 257];

    let config = SolverConfig::new().with_timeout(Duration::from_millis(100));
    let mut certified_sat = 0usize;
    let mut agreed_unsat = 0usize;
    let mut safe_unknown_sat = 0usize;
    for case in 0..CASES {
        let mode = case % 4;
        let width = WIDTHS[(case / 4) % WIDTHS.len()];

        let mut arena = TermArena::new();
        let sort = Sort::BitVec(width);
        let p = arena.declare("bool_discharge_p", Sort::Bool).unwrap();
        let x = arena.declare("bool_discharge_x", sort).unwrap();
        let y = arena.declare("bool_discharge_y", sort).unwrap();
        let z = arena.declare("bool_discharge_z", sort).unwrap();
        let pv = arena.var(p);
        let xv = arena.var(x);
        let yv = arena.var(y);
        let zv = arena.var(z);
        let opaque_xy = arena.bv_ult(xv, yv).unwrap();
        let assertion = match mode {
            0 => {
                let body = arena.or(opaque_xy, pv).unwrap();
                arena.forall(x, body).unwrap()
            }
            1 => {
                let opaque_xz = arena.bv_ult(xv, zv).unwrap();
                let inner = arena.exists(z, opaque_xz).unwrap();
                let body = arena.or(inner, pv).unwrap();
                arena.forall(x, body).unwrap()
            }
            2 => {
                let reflexive = arena.eq(xv, xv).unwrap();
                let falsity = arena.not(reflexive).unwrap();
                let body = arena.and(pv, falsity).unwrap();
                arena.forall(x, body).unwrap()
            }
            _ => {
                let body = arena.or(pv, opaque_xy).unwrap();
                let universal = arena.forall(x, body).unwrap();
                arena.not(universal).unwrap()
            }
        };
        let axeyum = solve(&mut arena, &[assertion], &config);

        let zp = Bool::new_const("bool_discharge_p");
        let zx = BV::new_const("bool_discharge_x", width);
        let zy = BV::new_const("bool_discharge_y", width);
        let zz = BV::new_const("bool_discharge_z", width);
        let zopaque_xy = zx.bvult(&zy);
        let zassertion = match mode {
            0 => {
                let body = Bool::or(&[zopaque_xy, zp.clone()]);
                z3::ast::forall_const(&[&zx as &dyn Ast], &[], &body)
            }
            1 => {
                let inner = z3::ast::exists_const(&[&zz as &dyn Ast], &[], &zx.bvult(&zz));
                let body = Bool::or(&[inner, zp.clone()]);
                z3::ast::forall_const(&[&zx as &dyn Ast], &[], &body)
            }
            2 => {
                let body = Bool::and(&[zp.clone(), zx.eq(&zx).not()]);
                z3::ast::forall_const(&[&zx as &dyn Ast], &[], &body)
            }
            _ => {
                let body = Bool::or(&[zp.clone(), zopaque_xy]);
                z3::ast::forall_const(&[&zx as &dyn Ast], &[], &body).not()
            }
        };
        let oracle = Solver::new();
        let mut params = Params::new();
        params.set_u32("timeout", 100);
        oracle.set_params(&params);
        oracle.assert(&zassertion);
        let z3 = oracle.check();

        match (mode, &axeyum, z3) {
            (0 | 1, Ok(CheckResult::Sat(model)), SatResult::Sat) => {
                assert_eq!(model.quantified_bool_model_sat_certificates().count(), 1);
                assert!(
                    axeyum_solver::check_model(&arena, &[assertion], model)
                        .expect("Boolean discharge replay"),
                    "supported case {case}, width {width} failed replay"
                );
                certified_sat += 1;
            }
            (0 | 1, _, _) => panic!(
                "supported Boolean discharge case {case}, width {width} was not jointly Sat: axeyum={axeyum:?}, z3={z3:?}"
            ),
            (2, Ok(CheckResult::Unsat), SatResult::Unsat) => agreed_unsat += 1,
            (2, Ok(CheckResult::Unknown(_)) | Err(_), SatResult::Unsat)
            | (3, Ok(CheckResult::Unknown(_)) | Err(_), SatResult::Sat) => {
                safe_unknown_sat += 1;
            }
            (3, Ok(CheckResult::Sat(model)), SatResult::Sat) => {
                assert!(
                    axeyum_solver::check_model(&arena, &[assertion], model)
                        .expect("negative control replay")
                );
                safe_unknown_sat += 1;
            }
            (_, _, SatResult::Unknown) => safe_unknown_sat += 1,
            _ => panic!(
                "Boolean discharge control {case}, width {width} disagreed: axeyum={axeyum:?}, z3={z3:?}"
            ),
        }
    }
    eprintln!(
        "Boolean BV-discharge differential: certified_sat={certified_sat}, agreed_unsat={agreed_unsat}, safe_controls={safe_unknown_sat}"
    );
    assert_eq!(certified_sat, CASES / 2);
}
