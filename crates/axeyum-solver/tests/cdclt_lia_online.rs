//! Parity + differential gates for the generic online CDCL(T) driver wired to
//! linear integer arithmetic (ADR-0055 criterion 2, slice a):
//! [`check_qf_lia_online_cdclt`] — the multiply-across-theories keystone (the same
//! generic [`axeyum_solver`] driver already proven on EUF and strings now drives a
//! third, arithmetic theory).
//!
//! The CDCL(T)-driver route must decide `QF_LIA` **identically** to the established
//! offline routes: the sibling online loop
//! [`axeyum_solver::check_qf_lia_online`] (self-contained `DPLL(T)`) and, for
//! conjunctive shapes, the trusted [`axeyum_solver::check_with_lia_simplex`]. Gates:
//!
//! 1. **Named shapes** — strict-integer tightening, transitivity, disjunctive
//!    refutation, and `sat`/model-replay cases; every online `unsat` is confirmed
//!    `unsat` by the offline route on the same query (no new unsat trust surface).
//! 2. **House-LCG differential fuzz** (no Z3 needed) — ≥2000 Boolean-structured
//!    random `QF_LIA` instances, CDCL(T) route vs the sibling online route.
//!    Identical verdicts required; a `Sat`/`Unsat` split is a soundness bug and
//!    panics. One route deciding where the other is `Unknown` is allowed (counted).
//! 3. **Deadline** — a zero-duration budget must degrade to `Unknown`.

use axeyum_ir::{Assignment, Sort, TermArena, TermId, Value, eval};
use axeyum_solver::{
    CheckResult, Model, SolverConfig, check_qf_lia_online, check_qf_lia_online_cdclt,
    check_with_lia_simplex,
};

/// Deterministic LCG (Numerical Recipes constants) — reproducible, no `rand`, no
/// clock (the house convention, matching `tests/lia_online.rs`).
struct Lcg(u64);

impl Lcg {
    fn new(seed: u64) -> Self {
        Self(seed)
    }
    fn next_u64(&mut self) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        self.0
    }
    fn below(&mut self, n: u64) -> u64 {
        self.next_u64() % n
    }
    fn small(&mut self, range: i128) -> i128 {
        let span = u64::try_from(2 * range + 1).expect("range fits u64");
        i128::from(self.below(span)) - range
    }
}

fn ivar(arena: &mut TermArena, name: &str) -> TermId {
    let s = arena.declare(name, Sort::Int).expect("declare int");
    arena.var(s)
}

fn online(arena: &TermArena, assertions: &[TermId]) -> CheckResult {
    check_qf_lia_online_cdclt(arena, assertions, &SolverConfig::default()).expect("decidable")
}

// ---------------------------------------------------------------------------
// Named-shape parity gates.
// ---------------------------------------------------------------------------

#[test]
fn strict_tightening_unsat_parity() {
    // 0 < x ∧ x < 1: integer-UNSAT though rationally SAT — the LIA point.
    let mut arena = TermArena::new();
    let x = ivar(&mut arena, "x");
    let zero = arena.int_const(0);
    let one = arena.int_const(1);
    let gt = arena.int_gt(x, zero).unwrap();
    let lt = arena.int_lt(x, one).unwrap();
    assert_eq!(online(&arena, &[gt, lt]), CheckResult::Unsat);
    assert_eq!(
        check_with_lia_simplex(&arena, &[gt, lt]).unwrap(),
        CheckResult::Unsat,
        "offline simplex agrees",
    );
}

#[test]
fn transitivity_unsat_parity() {
    // x < y ∧ y < z ∧ z < x — UNSAT.
    let mut arena = TermArena::new();
    let x = ivar(&mut arena, "x");
    let y = ivar(&mut arena, "y");
    let z = ivar(&mut arena, "z");
    let xy = arena.int_lt(x, y).unwrap();
    let yz = arena.int_lt(y, z).unwrap();
    let zx = arena.int_lt(z, x).unwrap();
    assert_eq!(online(&arena, &[xy, yz, zx]), CheckResult::Unsat);
    assert_eq!(
        check_with_lia_simplex(&arena, &[xy, yz, zx]).unwrap(),
        CheckResult::Unsat,
    );
}

#[test]
fn disjunctive_refutation_parity() {
    // (x < 0 ∨ x > 0) ∧ x = 0 — needs the Boolean search; UNSAT.
    let mut arena = TermArena::new();
    let x = ivar(&mut arena, "x");
    let zero = arena.int_const(0);
    let lt0 = arena.int_lt(x, zero).unwrap();
    let gt0 = arena.int_gt(x, zero).unwrap();
    let disj = arena.or(lt0, gt0).unwrap();
    let eq0 = arena.eq(x, zero).unwrap();
    assert_eq!(online(&arena, &[disj, eq0]), CheckResult::Unsat);
    // The sibling online route must agree.
    assert_eq!(
        check_qf_lia_online(&arena, &[disj, eq0], &SolverConfig::default()).unwrap(),
        CheckResult::Unsat,
    );
}

#[test]
fn satisfiable_range_parity_replays_integer_model() {
    // 5 <= x ∧ x <= 10 — SAT; the model must replay with integer values.
    let mut arena = TermArena::new();
    let x = ivar(&mut arena, "x");
    let five = arena.int_const(5);
    let ten = arena.int_const(10);
    let ge = arena.int_ge(x, five).unwrap();
    let le = arena.int_le(x, ten).unwrap();
    let CheckResult::Sat(model) = online(&arena, &[ge, le]) else {
        panic!("expected sat");
    };
    assert_integer_model(&arena, &[ge, le], &model);
}

#[test]
fn satisfiable_disjunction_parity() {
    // x < 0 ∨ x > 100 — SAT.
    let mut arena = TermArena::new();
    let x = ivar(&mut arena, "x");
    let zero = arena.int_const(0);
    let hundred = arena.int_const(100);
    let lt0 = arena.int_lt(x, zero).unwrap();
    let gt100 = arena.int_gt(x, hundred).unwrap();
    let disj = arena.or(lt0, gt100).unwrap();
    assert!(matches!(online(&arena, &[disj]), CheckResult::Sat(_)));
}

fn assert_integer_model(arena: &TermArena, assertions: &[TermId], model: &Model) {
    let mut assignment = Assignment::new();
    for (symbol, value) in model.iter() {
        assert!(
            matches!(value, Value::Int(_) | Value::Bool(_)),
            "CDCL(T) LIA sat model must assign integer/bool values, got {value:?}"
        );
        assignment.set(symbol, value);
    }
    for &a in assertions {
        assert_eq!(
            eval(arena, a, &assignment).ok(),
            Some(Value::Bool(true)),
            "CDCL(T) LIA sat model must satisfy every original assertion"
        );
    }
}

// ---------------------------------------------------------------------------
// House-LCG differential fuzz: CDCL(T) route vs the sibling online route.
// ---------------------------------------------------------------------------

/// Builds a random linear-integer atom `Σ cᵢ·xᵢ <rel> k` (small coefficients),
/// including equality — the same shape `tests/lia_online.rs` fuzzes.
fn random_atom(arena: &mut TermArena, vars: &[TermId], rng: &mut Lcg) -> TermId {
    let mut lhs: Option<TermId> = None;
    for &v in vars {
        let coeff = rng.small(3);
        if coeff == 0 {
            continue;
        }
        let c = arena.int_const(coeff);
        let term = arena.int_mul(c, v).expect("int mul");
        lhs = Some(match lhs {
            None => term,
            Some(acc) => arena.int_add(acc, term).expect("int add"),
        });
    }
    let lhs = lhs.unwrap_or_else(|| arena.int_const(0));
    let k = arena.int_const(rng.small(4));
    match rng.below(5) {
        0 => arena.int_lt(lhs, k).expect("int lt"),
        1 => arena.int_le(lhs, k).expect("int le"),
        2 => arena.int_gt(lhs, k).expect("int gt"),
        3 => arena.int_ge(lhs, k).expect("int ge"),
        _ => arena.eq(lhs, k).expect("int eq"),
    }
}

/// A random Boolean combination of a handful of atoms: each assertion is a
/// ≤2-literal clause (atom or its negation), so the skeleton exercises the driver's
/// Boolean search rather than a bare conjunction.
fn random_instance(arena: &mut TermArena, rng: &mut Lcg) -> Vec<TermId> {
    let nvars = 1 + usize::try_from(rng.below(3)).expect("fits"); // 1..=3 vars
    let vars: Vec<TermId> = (0..nvars).map(|i| ivar(arena, &format!("x{i}"))).collect();

    let npool = 2 + usize::try_from(rng.below(4)).expect("fits"); // 2..=5 atoms
    let pool: Vec<TermId> = (0..npool).map(|_| random_atom(arena, &vars, rng)).collect();

    let nclauses = 2 + usize::try_from(rng.below(3)).expect("fits"); // 2..=4 clauses
    let mut assertions = Vec::with_capacity(nclauses);
    for _ in 0..nclauses {
        let width = 1 + usize::try_from(rng.below(2)).expect("fits"); // 1..=2 literals
        let mut clause: Option<TermId> = None;
        for _ in 0..width {
            let atom = pool[usize::try_from(rng.below(npool as u64)).expect("fits")];
            let lit = if rng.below(2) == 0 {
                atom
            } else {
                arena.not(atom).expect("not")
            };
            clause = Some(match clause {
                None => lit,
                Some(acc) => arena.or(acc, lit).expect("or"),
            });
        }
        assertions.push(clause.expect("non-empty clause"));
    }
    assertions
}

#[test]
fn cdclt_lia_vs_sibling_online_differential_fuzz() {
    const INSTANCES: u64 = 2500;
    let mut agree = 0u64;
    let mut unsat_agree = 0u64;
    let mut sat_agree = 0u64;
    let mut cdclt_unknown = 0u64;
    let mut sibling_unknown = 0u64;

    for seed in 0..INSTANCES {
        let mut rng = Lcg::new(seed.wrapping_mul(0x9E37_79B9_7F4A_7C15).wrapping_add(1));
        let mut arena = TermArena::new();
        let assertions = random_instance(&mut arena, &mut rng);

        let on = check_qf_lia_online_cdclt(&arena, &assertions, &SolverConfig::default())
            .expect("cdclt decidable");
        let off = check_qf_lia_online(&arena, &assertions, &SolverConfig::default())
            .expect("sibling decidable");

        match (&on, &off) {
            (CheckResult::Unsat, CheckResult::Sat(_))
            | (CheckResult::Sat(_), CheckResult::Unsat) => {
                panic!(
                    "DISAGREEMENT (seed {seed}): cdclt = {on:?}, sibling online = {off:?} \
                     (a wrong sat/unsat is unacceptable)"
                );
            }
            (CheckResult::Unsat, CheckResult::Unsat) => {
                agree += 1;
                unsat_agree += 1;
                // Every CDCL(T) unsat is confirmed unsat by the trusted conjunctive
                // decider on the SAT-implied conflict? Not applicable to a Boolean
                // structure directly; the sibling-route agreement above is the gate.
            }
            (CheckResult::Sat(model), CheckResult::Sat(_)) => {
                // Independently replay the CDCL(T) model against the originals.
                assert_integer_model(&arena, &assertions, model);
                agree += 1;
                sat_agree += 1;
            }
            (CheckResult::Unknown(_), _) => cdclt_unknown += 1,
            (_, CheckResult::Unknown(_)) => sibling_unknown += 1,
        }
    }

    eprintln!(
        "cdclt-lia vs sibling-online: {INSTANCES} instances | {agree} agree \
         ({unsat_agree} unsat, {sat_agree} sat) | {cdclt_unknown} cdclt-unknown | \
         {sibling_unknown} sibling-unknown | 0 DISAGREE"
    );
    // Both routes decide the fragment completely; agreement dominates.
    assert!(
        agree >= INSTANCES / 2,
        "expected >= {} agreements, got {agree}",
        INSTANCES / 2
    );
    assert!(unsat_agree > 0, "fuzz produced no agreed UNSAT instances");
    assert!(sat_agree > 0, "fuzz produced no agreed SAT instances");
}

/// A second differential over pure conjunctions, cross-checked against the trusted
/// conjunctive [`check_with_lia_simplex`] (the offline decision procedure the whole
/// LIA stack is anchored on). Zero disagreements.
#[test]
fn cdclt_lia_conjunctions_vs_offline_simplex() {
    let mut decided = 0u64;
    let mut sat = 0u64;
    let mut unsat = 0u64;

    for seed in 0..600u64 {
        let mut rng = Lcg::new(seed.wrapping_mul(0xD1B5_4A32_D192_ED03).wrapping_add(7));
        let mut arena = TermArena::new();
        let nvars = 1 + usize::try_from(rng.below(3)).expect("fits");
        let vars: Vec<TermId> = (0..nvars)
            .map(|i| ivar(&mut arena, &format!("y{i}")))
            .collect();
        let natoms = 2 + usize::try_from(rng.below(4)).expect("fits");
        let assertions: Vec<TermId> = (0..natoms)
            .map(|_| random_atom(&mut arena, &vars, &mut rng))
            .collect();

        let on = check_qf_lia_online_cdclt(&arena, &assertions, &SolverConfig::default())
            .expect("cdclt decidable");
        let off = check_with_lia_simplex(&arena, &assertions).expect("offline decidable");

        match (&off, &on) {
            (CheckResult::Sat(_), CheckResult::Sat(model)) => {
                assert_integer_model(&arena, &assertions, model);
                sat += 1;
                decided += 1;
            }
            (CheckResult::Unsat, CheckResult::Unsat) => {
                unsat += 1;
                decided += 1;
            }
            (CheckResult::Unknown(_), _) | (_, CheckResult::Unknown(_)) => {}
            (a, b) => panic!("DISAGREEMENT seed {seed}: offline simplex = {a:?}, cdclt = {b:?}"),
        }
    }

    eprintln!("cdclt-lia conjunctions vs simplex: decided={decided} sat={sat} unsat={unsat}");
    assert!(decided > 0, "fuzz must decide some instances");
    assert!(sat > 0, "fuzz must cover a sat case");
    assert!(unsat > 0, "fuzz must cover an unsat case");
}

#[test]
fn deadline_gives_unknown_not_wrong_answer() {
    let mut arena = TermArena::new();
    let x = ivar(&mut arena, "x");
    let zero = arena.int_const(0);
    let one = arena.int_const(1);
    let gt = arena.int_gt(x, zero).unwrap();
    let lt = arena.int_lt(x, one).unwrap();
    let cfg = SolverConfig::default().with_timeout(std::time::Duration::ZERO);
    let r = check_qf_lia_online_cdclt(&arena, &[gt, lt], &cfg).expect("result");
    assert!(
        matches!(r, CheckResult::Unknown(_)),
        "zero-timeout must yield Unknown, got {r:?}"
    );
}
