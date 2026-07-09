//! Parity + differential gates for the generic online CDCL(T) driver wired to
//! linear real arithmetic (ADR-0055 criterion 2, slice a-lra):
//! [`check_qf_lra_online_cdclt`] — the LRA companion to the integer
//! [`axeyum_solver::check_qf_lia_online_cdclt`] slice (the same generic
//! [`axeyum_solver`] driver already proven on EUF, strings, and integers now drives
//! linear real arithmetic).
//!
//! The CDCL(T)-driver route must decide `QF_LRA` **identically** to the established
//! offline routes: the sibling online loop [`axeyum_solver::check_qf_lra_online`]
//! (self-contained `DPLL(T)`) and, for conjunctive shapes, the trusted
//! [`axeyum_solver::check_with_lra`] (Fourier–Motzkin). Gates:
//!
//! 1. **Named shapes** — strict bounds, transitivity, disjunctive refutation, and
//!    `sat`/model-replay cases; every online `unsat` is confirmed `unsat` by the
//!    offline route on the same query (no new unsat trust surface).
//! 2. **House-LCG differential fuzz** (no Z3 needed) — ≥2000 Boolean-structured
//!    random `QF_LRA` instances, CDCL(T) route vs the sibling online route.
//!    Identical verdicts required; a `Sat`/`Unsat` split is a soundness bug and
//!    panics. One route deciding where the other is `Unknown` is allowed (counted).
//! 3. **Deadline** — a zero-duration budget must degrade to `Unknown`.

use axeyum_ir::{Assignment, Rational, Sort, TermArena, TermId, Value, eval};
use axeyum_solver::{
    CheckResult, Model, SolverConfig, check_qf_lra_online, check_qf_lra_online_cdclt,
    check_with_lra, check_with_lra_dpll,
};

/// Deterministic LCG (Numerical Recipes constants) — reproducible, no `rand`, no
/// clock (the house convention, matching `tests/cdclt_lia_online.rs`).
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

fn rvar(arena: &mut TermArena, name: &str) -> TermId {
    let s = arena.declare(name, Sort::Real).expect("declare real");
    arena.var(s)
}

fn rconst(arena: &mut TermArena, n: i128) -> TermId {
    arena.real_const(Rational::integer(n))
}

fn online(arena: &TermArena, assertions: &[TermId]) -> CheckResult {
    check_qf_lra_online_cdclt(arena, assertions, &SolverConfig::default()).expect("decidable")
}

// ---------------------------------------------------------------------------
// Named-shape parity gates.
// ---------------------------------------------------------------------------

#[test]
fn strict_bounds_unsat_parity() {
    // x < 0 ∧ x > 0: real-UNSAT.
    let mut arena = TermArena::new();
    let x = rvar(&mut arena, "x");
    let zero = rconst(&mut arena, 0);
    let lt = arena.real_lt(x, zero).unwrap();
    let gt = arena.real_gt(x, zero).unwrap();
    assert_eq!(online(&arena, &[lt, gt]), CheckResult::Unsat);
    assert_eq!(
        check_with_lra(&arena, &[lt, gt]).unwrap(),
        CheckResult::Unsat,
        "offline Fourier–Motzkin agrees",
    );
}

#[test]
fn transitivity_unsat_parity() {
    // x < y ∧ y < z ∧ z < x — UNSAT.
    let mut arena = TermArena::new();
    let x = rvar(&mut arena, "x");
    let y = rvar(&mut arena, "y");
    let z = rvar(&mut arena, "z");
    let xy = arena.real_lt(x, y).unwrap();
    let yz = arena.real_lt(y, z).unwrap();
    let zx = arena.real_lt(z, x).unwrap();
    assert_eq!(online(&arena, &[xy, yz, zx]), CheckResult::Unsat);
    assert_eq!(
        check_with_lra(&arena, &[xy, yz, zx]).unwrap(),
        CheckResult::Unsat,
    );
}

#[test]
fn disjunctive_refutation_parity() {
    // (x < 0 ∨ x > 0) ∧ x = 0 — needs the Boolean search; UNSAT.
    let mut arena = TermArena::new();
    let x = rvar(&mut arena, "x");
    let zero = rconst(&mut arena, 0);
    let lt0 = arena.real_lt(x, zero).unwrap();
    let gt0 = arena.real_gt(x, zero).unwrap();
    let disj = arena.or(lt0, gt0).unwrap();
    let eq0 = arena.eq(x, zero).unwrap();
    assert_eq!(online(&arena, &[disj, eq0]), CheckResult::Unsat);
    // The sibling online route must agree.
    assert_eq!(
        check_qf_lra_online(&arena, &[disj, eq0], &SolverConfig::default()).unwrap(),
        CheckResult::Unsat,
    );
}

#[test]
fn satisfiable_range_parity_replays_real_model() {
    // 5 <= x ∧ x <= 10 — SAT; the model must replay with real values.
    let mut arena = TermArena::new();
    let x = rvar(&mut arena, "x");
    let five = rconst(&mut arena, 5);
    let ten = rconst(&mut arena, 10);
    let ge = arena.real_ge(x, five).unwrap();
    let le = arena.real_le(x, ten).unwrap();
    let CheckResult::Sat(model) = online(&arena, &[ge, le]) else {
        panic!("expected sat");
    };
    assert_real_model(&arena, &[ge, le], &model);
}

#[test]
fn satisfiable_disjunction_parity() {
    // x < 0 ∨ x > 100 — SAT.
    let mut arena = TermArena::new();
    let x = rvar(&mut arena, "x");
    let zero = rconst(&mut arena, 0);
    let hundred = rconst(&mut arena, 100);
    let lt0 = arena.real_lt(x, zero).unwrap();
    let gt100 = arena.real_gt(x, hundred).unwrap();
    let disj = arena.or(lt0, gt100).unwrap();
    assert!(matches!(online(&arena, &[disj]), CheckResult::Sat(_)));
}

fn assert_real_model(arena: &TermArena, assertions: &[TermId], model: &Model) {
    let mut assignment = Assignment::new();
    for (symbol, value) in model.iter() {
        assert!(
            matches!(value, Value::Real(_) | Value::Bool(_)),
            "CDCL(T) LRA sat model must assign real/bool values, got {value:?}"
        );
        assignment.set(symbol, value);
    }
    for &a in assertions {
        assert_eq!(
            eval(arena, a, &assignment).ok(),
            Some(Value::Bool(true)),
            "CDCL(T) LRA sat model must satisfy every original assertion"
        );
    }
}

// ---------------------------------------------------------------------------
// House-LCG differential fuzz: CDCL(T) route vs the sibling online route.
// ---------------------------------------------------------------------------

/// Builds a random linear-real atom `Σ cᵢ·xᵢ <rel> k` (small coefficients),
/// including equality.
fn random_atom(arena: &mut TermArena, vars: &[TermId], rng: &mut Lcg) -> TermId {
    let mut lhs: Option<TermId> = None;
    for &v in vars {
        let coeff = rng.small(3);
        if coeff == 0 {
            continue;
        }
        let c = rconst(arena, coeff);
        let term = arena.real_mul(c, v).expect("real mul");
        lhs = Some(match lhs {
            None => term,
            Some(acc) => arena.real_add(acc, term).expect("real add"),
        });
    }
    let lhs = lhs.unwrap_or_else(|| rconst(arena, 0));
    let k = rconst(arena, rng.small(4));
    match rng.below(5) {
        0 => arena.real_lt(lhs, k).expect("real lt"),
        1 => arena.real_le(lhs, k).expect("real le"),
        2 => arena.real_gt(lhs, k).expect("real gt"),
        3 => arena.real_ge(lhs, k).expect("real ge"),
        _ => arena.eq(lhs, k).expect("real eq"),
    }
}

/// A random Boolean combination of a handful of atoms: each assertion is a
/// ≤2-literal clause (atom or its negation), so the skeleton exercises the driver's
/// Boolean search rather than a bare conjunction.
fn random_instance(arena: &mut TermArena, rng: &mut Lcg) -> Vec<TermId> {
    let nvars = 1 + usize::try_from(rng.below(3)).expect("fits"); // 1..=3 vars
    let vars: Vec<TermId> = (0..nvars).map(|i| rvar(arena, &format!("x{i}"))).collect();

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
fn cdclt_lra_vs_sibling_online_differential_fuzz() {
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

        let on = check_qf_lra_online_cdclt(&arena, &assertions, &SolverConfig::default())
            .expect("cdclt decidable");
        let off = check_qf_lra_online(&arena, &assertions, &SolverConfig::default())
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
            }
            (CheckResult::Sat(model), CheckResult::Sat(_)) => {
                // Independently replay the CDCL(T) model against the originals.
                assert_real_model(&arena, &assertions, model);
                agree += 1;
                sat_agree += 1;
            }
            (CheckResult::Unknown(_), _) => cdclt_unknown += 1,
            (_, CheckResult::Unknown(_)) => sibling_unknown += 1,
        }
    }

    eprintln!(
        "cdclt-lra vs sibling-online: {INSTANCES} instances | {agree} agree \
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
/// conjunctive [`check_with_lra`] (the offline decision procedure the whole LRA
/// stack is anchored on). Zero disagreements.
#[test]
fn cdclt_lra_conjunctions_vs_offline_fourier_motzkin() {
    let mut decided = 0u64;
    let mut sat = 0u64;
    let mut unsat = 0u64;

    for seed in 0..600u64 {
        let mut rng = Lcg::new(seed.wrapping_mul(0xD1B5_4A32_D192_ED03).wrapping_add(7));
        let mut arena = TermArena::new();
        let nvars = 1 + usize::try_from(rng.below(3)).expect("fits");
        let vars: Vec<TermId> = (0..nvars)
            .map(|i| rvar(&mut arena, &format!("y{i}")))
            .collect();
        let natoms = 2 + usize::try_from(rng.below(4)).expect("fits");
        let assertions: Vec<TermId> = (0..natoms)
            .map(|_| random_atom(&mut arena, &vars, &mut rng))
            .collect();

        let on = check_qf_lra_online_cdclt(&arena, &assertions, &SolverConfig::default())
            .expect("cdclt decidable");
        let off = check_with_lra(&arena, &assertions).expect("offline decidable");

        match (&off, &on) {
            (CheckResult::Sat(_), CheckResult::Sat(model)) => {
                assert_real_model(&arena, &assertions, model);
                sat += 1;
                decided += 1;
            }
            (CheckResult::Unsat, CheckResult::Unsat) => {
                unsat += 1;
                decided += 1;
            }
            (CheckResult::Unknown(_), _) | (_, CheckResult::Unknown(_)) => {}
            (a, b) => panic!("DISAGREEMENT seed {seed}: offline FM = {a:?}, cdclt = {b:?}"),
        }
    }

    eprintln!(
        "cdclt-lra conjunctions vs Fourier–Motzkin: decided={decided} sat={sat} unsat={unsat}"
    );
    assert!(decided > 0, "fuzz must decide some instances");
    assert!(sat > 0, "fuzz must cover a sat case");
    assert!(unsat > 0, "fuzz must cover an unsat case");
}

#[test]
fn deadline_gives_unknown_not_wrong_answer() {
    let mut arena = TermArena::new();
    let x = rvar(&mut arena, "x");
    let zero = rconst(&mut arena, 0);
    let lt = arena.real_lt(x, zero).unwrap();
    let gt = arena.real_gt(x, zero).unwrap();
    let cfg = SolverConfig::default().with_timeout(std::time::Duration::ZERO);
    let r = check_qf_lra_online_cdclt(&arena, &[lt, gt], &cfg).expect("result");
    assert!(
        matches!(r, CheckResult::Unknown(_)),
        "zero-timeout must yield Unknown, got {r:?}"
    );
}

#[test]
fn default_lra_wrapper_leads_with_generic_cdclt() {
    let mut arena = TermArena::new();
    let x = rvar(&mut arena, "x");
    let zero = rconst(&mut arena, 0);
    let lt = arena.real_lt(x, zero).unwrap();
    let gt = arena.real_gt(x, zero).unwrap();
    let cfg = SolverConfig::default().with_timeout(std::time::Duration::ZERO);
    let CheckResult::Unknown(reason) =
        check_with_lra_dpll(&mut arena, &[lt, gt], &cfg).expect("result")
    else {
        panic!("zero-timeout default LRA route must yield Unknown");
    };
    assert!(
        reason.detail.contains("online CDCL(T) LRA driver"),
        "default LRA route did not lead with generic CDCL(T): {reason:?}"
    );
}
