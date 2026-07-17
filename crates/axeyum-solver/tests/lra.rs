//! End-to-end conjunctive `QF_LRA`: exact-rational Fourier–Motzkin (ADR-0015).
//!
//! These tests exercise [`check_with_lra`]: a conjunction of linear real
//! constraints is decided over exact rationals, and any `sat` model is replayed
//! against the original query with the ground evaluator — the trust anchor for
//! the first non-`QF_BV` procedure.
#![cfg(feature = "full")]

use axeyum_ir::{Rational, Sort, TermArena, Value, eval};
use axeyum_solver::{
    CheckResult, FarkasAtom, FarkasCertificate, check_with_lra, check_with_lra_simplex,
    lra_farkas_certificate, lra_unsat_core,
};

fn solve(arena: &TermArena, assertions: &[axeyum_ir::TermId]) -> CheckResult {
    check_with_lra(arena, assertions).expect("supported `QF_LRA` query decides without error")
}

#[test]
fn strict_bounds_admit_a_rational_between_them() {
    // 2*x > 1 && x < 1  =>  x in (1/2, 1); a rational model exists (e.g. 3/4).
    let mut arena = TermArena::new();
    let x_sym = arena.declare("x", Sort::Real).unwrap();
    let x = arena.var(x_sym);
    let two = arena.real_ratio(2, 1);
    let one = arena.real_ratio(1, 1);
    let two_x = arena.real_mul(two, x).unwrap();
    let lower = arena.real_gt(two_x, one).unwrap();
    let upper = arena.real_lt(x, one).unwrap();

    let CheckResult::Sat(model) = solve(&arena, &[lower, upper]) else {
        panic!("expected a satisfiable strict interval");
    };
    // The model replays, and the witness is strictly inside (1/2, 1).
    let assignment = model.to_assignment();
    assert_eq!(eval(&arena, lower, &assignment).unwrap(), Value::Bool(true));
    assert_eq!(eval(&arena, upper, &assignment).unwrap(), Value::Bool(true));
    let xv = model.get(x_sym).unwrap().as_real().unwrap();
    assert!(xv > Rational::new(1, 2) && xv < Rational::new(1, 1));
}

#[test]
fn empty_interval_is_unsat() {
    // x < 0 && x > 0 has no real model.
    let mut arena = TermArena::new();
    let x_sym = arena.declare("x", Sort::Real).unwrap();
    let x = arena.var(x_sym);
    let zero = arena.real_ratio(0, 1);
    let lt = arena.real_lt(x, zero).unwrap();
    let gt = arena.real_gt(x, zero).unwrap();
    assert_eq!(solve(&arena, &[lt, gt]), CheckResult::Unsat);
}

#[test]
fn two_variable_system_is_sat_and_replays() {
    // x + y == 1 && x - y <= 0 && x >= 0 : satisfiable (e.g. x = 1/2, y = 1/2).
    let mut arena = TermArena::new();
    let x_sym = arena.declare("x", Sort::Real).unwrap();
    let y_sym = arena.declare("y", Sort::Real).unwrap();
    let x = arena.var(x_sym);
    let y = arena.var(y_sym);
    let one = arena.real_ratio(1, 1);
    let zero = arena.real_ratio(0, 1);
    let sum = arena.real_add(x, y).unwrap();
    let eq = arena.eq(sum, one).unwrap();
    let diff = arena.real_sub(x, y).unwrap();
    let le = arena.real_le(diff, zero).unwrap();
    let nonneg = arena.real_ge(x, zero).unwrap();

    let CheckResult::Sat(model) = solve(&arena, &[eq, le, nonneg]) else {
        panic!("expected a satisfiable two-variable system");
    };
    let assignment = model.to_assignment();
    for &a in &[eq, le, nonneg] {
        assert_eq!(eval(&arena, a, &assignment).unwrap(), Value::Bool(true));
    }
}

#[test]
fn fractional_equality_pins_a_noninteger_value() {
    // 3*x == 1  =>  x == 1/3 (a value no integer theory could represent).
    let mut arena = TermArena::new();
    let x_sym = arena.declare("x", Sort::Real).unwrap();
    let x = arena.var(x_sym);
    let three = arena.real_ratio(3, 1);
    let one = arena.real_ratio(1, 1);
    let three_x = arena.real_mul(three, x).unwrap();
    let eq = arena.eq(three_x, one).unwrap();

    let CheckResult::Sat(model) = solve(&arena, &[eq]) else {
        panic!("expected a satisfiable fractional equality");
    };
    assert_eq!(
        model.get(x_sym).unwrap().as_real().unwrap(),
        Rational::new(1, 3)
    );
}

#[test]
fn transitive_chain_is_unsat() {
    // x < y && y < z && z < x is unsatisfiable (strict cycle).
    let mut arena = TermArena::new();
    let x = arena.real_var("x").unwrap();
    let y = arena.real_var("y").unwrap();
    let z = arena.real_var("z").unwrap();
    let xy = arena.real_lt(x, y).unwrap();
    let yz = arena.real_lt(y, z).unwrap();
    let zx = arena.real_lt(z, x).unwrap();
    assert_eq!(solve(&arena, &[xy, yz, zx]), CheckResult::Unsat);
}

#[test]
fn empty_interval_unsat_yields_a_verifying_farkas_certificate() {
    // x < 0 && x > 0: the refutation is 1·(x < 0) + 1·(-x < 0) => 0 < 0.
    let mut arena = TermArena::new();
    let x_sym = arena.declare("x", Sort::Real).unwrap();
    let x = arena.var(x_sym);
    let zero = arena.real_ratio(0, 1);
    let lt = arena.real_lt(x, zero).unwrap();
    let gt = arena.real_gt(x, zero).unwrap();

    let cert = lra_farkas_certificate(&arena, &[lt, gt])
        .expect("decides without error")
        .expect("an unsatisfiable conjunction has a Farkas certificate");
    assert!(cert.verify(), "the returned certificate must verify");
    // Two atoms (the two strict inequalities), both with positive multipliers.
    assert_eq!(cert.atoms.len(), 2);
    assert_eq!(cert.multipliers.len(), 2);
    assert!(cert.multipliers.iter().all(|m| *m >= Rational::zero()));
    assert!(cert.multipliers.iter().any(|m| *m > Rational::zero()));
}

#[test]
fn transitive_cycle_unsat_certificate_verifies() {
    // x < y && y < z && z < x: summing all three cancels every variable => 0 < 0.
    let mut arena = TermArena::new();
    let x = arena.real_var("x").unwrap();
    let y = arena.real_var("y").unwrap();
    let z = arena.real_var("z").unwrap();
    let xy = arena.real_lt(x, y).unwrap();
    let yz = arena.real_lt(y, z).unwrap();
    let zx = arena.real_lt(z, x).unwrap();

    let cert = lra_farkas_certificate(&arena, &[xy, yz, zx])
        .expect("decides without error")
        .expect("the strict cycle is unsatisfiable");
    assert!(cert.verify());
    assert_eq!(cert.atoms.len(), 3);
}

#[test]
fn equality_derived_unsat_certificate_verifies() {
    // 3*x == 1 && x == 1 is unsatisfiable (x would be both 1/3 and 1). The
    // equalities expand to four `<= 0` atoms; the certificate must still verify.
    let mut arena = TermArena::new();
    let x_sym = arena.declare("x", Sort::Real).unwrap();
    let x = arena.var(x_sym);
    let three = arena.real_ratio(3, 1);
    let one = arena.real_ratio(1, 1);
    let three_x = arena.real_mul(three, x).unwrap();
    let eq_third = arena.eq(three_x, one).unwrap();
    let eq_one = arena.eq(x, one).unwrap();

    assert_eq!(solve(&arena, &[eq_third, eq_one]), CheckResult::Unsat);
    let cert = lra_farkas_certificate(&arena, &[eq_third, eq_one])
        .expect("decides without error")
        .expect("the conflicting equalities are unsatisfiable");
    assert!(cert.verify());
    assert_eq!(cert.atoms.len(), 4); // two atoms per equality
}

#[test]
fn satisfiable_query_has_no_certificate() {
    // x < 1 is satisfiable, so there is no refutation to certify.
    let mut arena = TermArena::new();
    let x_sym = arena.declare("x", Sort::Real).unwrap();
    let x = arena.var(x_sym);
    let one = arena.real_ratio(1, 1);
    let lt = arena.real_lt(x, one).unwrap();
    assert!(
        lra_farkas_certificate(&arena, &[lt])
            .expect("decides without error")
            .is_none()
    );
}

#[test]
fn tampered_certificate_is_rejected_by_the_independent_checker() {
    // Take a genuine refutation, then corrupt it three ways; each must fail
    // verification — the checker depends only on the atoms and multipliers.
    let mut arena = TermArena::new();
    let x_sym = arena.declare("x", Sort::Real).unwrap();
    let x = arena.var(x_sym);
    let zero = arena.real_ratio(0, 1);
    let lt = arena.real_lt(x, zero).unwrap();
    let gt = arena.real_gt(x, zero).unwrap();
    let cert = lra_farkas_certificate(&arena, &[lt, gt]).unwrap().unwrap();
    assert!(cert.verify());

    // (1) Dropping one multiplier leaves an uncancelled `±x` => not a constant.
    let mut dropped = cert.clone();
    dropped.multipliers[0] = Rational::zero();
    assert!(!dropped.verify());

    // (2) A negative multiplier is not a valid (nonnegative) Farkas combination.
    let mut negative = cert.clone();
    negative.multipliers[0] = Rational::integer(-1);
    assert!(!negative.verify());

    // (3) The all-zero combination is vacuous (0 <= 0 is satisfiable).
    let zeroed = FarkasCertificate {
        atoms: cert.atoms.clone(),
        multipliers: vec![Rational::zero(), Rational::zero()],
        origins: cert.origins.clone(),
        vars: cert.vars.clone(),
    };
    assert!(!zeroed.verify());
}

#[test]
fn a_handmade_nonrefutation_does_not_verify() {
    // Two satisfiable atoms (x <= 0 and y <= 0) cannot be combined into a
    // contradiction, whatever nonnegative multipliers are tried.
    let atoms = vec![
        FarkasAtom {
            coeffs: vec![(0, Rational::integer(1))],
            constant: Rational::zero(),
            strict: false,
        },
        FarkasAtom {
            coeffs: vec![(1, Rational::integer(1))],
            constant: Rational::zero(),
            strict: false,
        },
    ];
    let bogus = FarkasCertificate {
        atoms,
        multipliers: vec![Rational::integer(2), Rational::integer(3)],
        origins: vec![0, 1],
        // `verify()` never consults `vars`; an empty map suffices for this check.
        vars: Vec::new(),
    };
    assert!(!bogus.verify());
}

#[test]
fn unsat_core_isolates_the_conflicting_assertions() {
    // Assertions: [x > 5, y < 10, x < 1, z > 0]. Only #0 (x > 5) and #2 (x < 1)
    // conflict; the y and z assertions are irrelevant. The core must be {0, 2}.
    let mut arena = TermArena::new();
    let x = arena.real_var("x").unwrap();
    let y = arena.real_var("y").unwrap();
    let z = arena.real_var("z").unwrap();
    let zero = arena.real_ratio(0, 1);
    let one = arena.real_ratio(1, 1);
    let five = arena.real_ratio(5, 1);
    let ten = arena.real_ratio(10, 1);
    let assertions = [
        arena.real_gt(x, five).unwrap(),
        arena.real_lt(y, ten).unwrap(),
        arena.real_lt(x, one).unwrap(),
        arena.real_gt(z, zero).unwrap(),
    ];

    let core = lra_unsat_core(&arena, &assertions)
        .expect("decides without error")
        .expect("the query is unsatisfiable");
    assert_eq!(
        core,
        vec![0, 2],
        "core must be exactly the conflicting pair"
    );

    // The core subset is itself unsatisfiable; dropping a core member is sat.
    let subset: Vec<_> = core.iter().map(|&i| assertions[i]).collect();
    assert_eq!(check_with_lra(&arena, &subset).unwrap(), CheckResult::Unsat);
    assert!(matches!(
        check_with_lra(&arena, &[assertions[0], assertions[1], assertions[3]]).unwrap(),
        CheckResult::Sat(_)
    ));
}

#[test]
fn unsat_core_handles_equality_assertions() {
    // [3*x == 1, x == 1, y > 0] : the two equalities conflict; y is irrelevant.
    let mut arena = TermArena::new();
    let x = arena.real_var("x").unwrap();
    let y = arena.real_var("y").unwrap();
    let zero = arena.real_ratio(0, 1);
    let one = arena.real_ratio(1, 1);
    let three = arena.real_ratio(3, 1);
    let three_x = arena.real_mul(three, x).unwrap();
    let assertions = [
        arena.eq(three_x, one).unwrap(),
        arena.eq(x, one).unwrap(),
        arena.real_gt(y, zero).unwrap(),
    ];

    let core = lra_unsat_core(&arena, &assertions)
        .expect("decides without error")
        .expect("the conflicting equalities are unsatisfiable");
    assert_eq!(core, vec![0, 1]);
}

#[test]
fn unsat_core_is_minimal_dropping_redundant_conflicts() {
    // [x > 5, x < 1, x < 2] : {x>5, x<1} and {x>5, x<2} both conflict. A minimal
    // core keeps just two assertions — every member necessary — never all three.
    let mut arena = TermArena::new();
    let x = arena.real_var("x").unwrap();
    let one = arena.real_ratio(1, 1);
    let two = arena.real_ratio(2, 1);
    let five = arena.real_ratio(5, 1);
    let assertions = [
        arena.real_gt(x, five).unwrap(),
        arena.real_lt(x, one).unwrap(),
        arena.real_lt(x, two).unwrap(),
    ];

    let core = lra_unsat_core(&arena, &assertions)
        .expect("decides without error")
        .expect("unsatisfiable");
    assert_eq!(core.len(), 2, "minimal core drops the redundant bound");
    // Whichever two survive, x > 5 must be one of them, and the pair is unsat.
    assert!(core.contains(&0), "x > 5 is essential to every conflict");
    let subset: Vec<_> = core.iter().map(|&i| assertions[i]).collect();
    assert_eq!(check_with_lra(&arena, &subset).unwrap(), CheckResult::Unsat);
    // Every member is necessary: removing any one leaves a satisfiable set.
    for &drop in &core {
        let rest: Vec<_> = core
            .iter()
            .filter(|&&i| i != drop)
            .map(|&i| assertions[i])
            .collect();
        assert!(
            matches!(check_with_lra(&arena, &rest).unwrap(), CheckResult::Sat(_)),
            "dropping a core member must restore satisfiability"
        );
    }
}

#[test]
fn satisfiable_query_has_no_unsat_core() {
    let mut arena = TermArena::new();
    let x = arena.real_var("x").unwrap();
    let one = arena.real_ratio(1, 1);
    let lt = arena.real_lt(x, one).unwrap();
    assert!(lra_unsat_core(&arena, &[lt]).unwrap().is_none());
}

#[test]
fn disjunction_is_unsupported() {
    // (x < 0) or (x > 0) needs case splitting (DPLL(T)); out of scope.
    let mut arena = TermArena::new();
    let x_sym = arena.declare("x", Sort::Real).unwrap();
    let x = arena.var(x_sym);
    let zero = arena.real_ratio(0, 1);
    let lt = arena.real_lt(x, zero).unwrap();
    let gt = arena.real_gt(x, zero).unwrap();
    let disj = arena.or(lt, gt).unwrap();
    let mut backend_err = false;
    if let Err(axeyum_solver::SolverError::Unsupported(_)) = check_with_lra(&arena, &[disj]) {
        backend_err = true;
    }
    assert!(backend_err, "disjunction must be reported unsupported");
}

/// Deterministic fuzz over random small linear real systems. The oracle-free
/// invariant: `check_with_lra` must never trip its own soundness alarm (a
/// `SolverError::Backend` from a failed Farkas self-check or `sat` replay), and
/// every `unsat` must hand back a certificate that verifies independently. This
/// exercises the multiplier accumulation across multi-variable elimination
/// chains, which the hand-written cases only touch lightly.
#[test]
fn fuzz_farkas_self_check_never_trips() {
    // A small linear-congruential generator keeps the run fully deterministic
    // (determinism is a project promise — no external rng, no wall-clock seed).
    let mut state: u64 = 0x9E37_79B9_7F4A_7C15;
    let mut next = || {
        state = state
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        (state >> 33) as u32
    };

    let mut sat_seen = 0u32;
    let mut unsat_seen = 0u32;

    for _ in 0..3000 {
        let mut arena = TermArena::new();
        let nvars = 1 + (next() % 3) as usize; // 1..=3 real variables
        let vars: Vec<_> = (0..nvars)
            .map(|i| arena.real_var(&format!("x{i}")).unwrap())
            .collect();
        let zero = arena.real_ratio(0, 1);

        let nconstraints = 2 + (next() % 4) as usize; // 2..=5 constraints
        let mut assertions = Vec::with_capacity(nconstraints);
        for _ in 0..nconstraints {
            // Build lhs = const + sum coeff_i * x_i with small integer coeffs.
            let constant = i128::from(next() % 11) - 5; // -5..=5
            let mut lhs = arena.real_ratio(constant, 1);
            for &v in &vars {
                let coeff = i128::from(next() % 7) - 3; // -3..=3
                if coeff != 0 {
                    let c = arena.real_ratio(coeff, 1);
                    let term = arena.real_mul(c, v).unwrap();
                    lhs = arena.real_add(lhs, term).unwrap();
                }
            }
            // Compare lhs to 0 with a random order relation.
            let atom = match next() % 4 {
                0 => arena.real_lt(lhs, zero),
                1 => arena.real_le(lhs, zero),
                2 => arena.real_gt(lhs, zero),
                _ => arena.real_ge(lhs, zero),
            }
            .unwrap();
            assertions.push(atom);
        }

        // The procedure must always decide cleanly (no soundness alarm).
        let result = check_with_lra(&arena, &assertions)
            .expect("random linear real system decides without a soundness alarm");
        match result {
            CheckResult::Sat(model) => {
                sat_seen += 1;
                // The model must replay against every assertion.
                let assignment = model.to_assignment();
                for &a in &assertions {
                    assert_eq!(
                        eval(&arena, a, &assignment).unwrap(),
                        Value::Bool(true),
                        "fuzz sat model must satisfy every assertion"
                    );
                }
            }
            CheckResult::Unsat => {
                unsat_seen += 1;
                let cert = lra_farkas_certificate(&arena, &assertions)
                    .unwrap()
                    .expect("a linear-system unsat carries a Farkas certificate");
                assert!(cert.verify(), "fuzz unsat certificate must verify");
            }
            CheckResult::Unknown(_) => panic!("conjunctive QF_LRA is a total decision procedure"),
        }
    }

    // The generator must have produced a healthy mix of both outcomes, so both
    // the model-replay and Farkas-certificate paths are genuinely exercised.
    assert!(sat_seen > 0, "expected some satisfiable systems");
    assert!(unsat_seen > 0, "expected some unsatisfiable systems");
}

#[test]
fn simplex_decides_basic_cases() {
    // Strict interval (sat), empty interval (unsat), fractional pin (sat).
    let mut arena = TermArena::new();
    let x_sym = arena.declare("x", Sort::Real).unwrap();
    let x = arena.var(x_sym);
    let zero = arena.real_ratio(0, 1);
    let one = arena.real_ratio(1, 1);
    let two = arena.real_ratio(2, 1);
    let two_x = arena.real_mul(two, x).unwrap();
    let gt_half = arena.real_gt(two_x, one).unwrap(); // x > 1/2
    let lt_one = arena.real_lt(x, one).unwrap(); // x < 1
    let CheckResult::Sat(model) = check_with_lra_simplex(&arena, &[gt_half, lt_one]).unwrap()
    else {
        panic!("expected a satisfiable strict interval");
    };
    let xv = model.get(x_sym).unwrap().as_real().unwrap();
    assert!(xv > Rational::new(1, 2) && xv < Rational::new(1, 1));

    let lt0 = arena.real_lt(x, zero).unwrap();
    let gt0 = arena.real_gt(x, zero).unwrap();
    assert_eq!(
        check_with_lra_simplex(&arena, &[lt0, gt0]).unwrap(),
        CheckResult::Unsat
    );
}

#[test]
fn simplex_handles_a_two_variable_system() {
    // x + y == 1 && x - y <= 0 && x >= 0 — satisfiable, model replays.
    let mut arena = TermArena::new();
    let x = arena.real_var("x").unwrap();
    let y = arena.real_var("y").unwrap();
    let one = arena.real_ratio(1, 1);
    let zero = arena.real_ratio(0, 1);
    let sum = arena.real_add(x, y).unwrap();
    let eq = arena.eq(sum, one).unwrap();
    let diff = arena.real_sub(x, y).unwrap();
    let le = arena.real_le(diff, zero).unwrap();
    let nonneg = arena.real_ge(x, zero).unwrap();
    assert!(matches!(
        check_with_lra_simplex(&arena, &[eq, le, nonneg]).unwrap(),
        CheckResult::Sat(_)
    ));
}

#[test]
fn fuzz_simplex_agrees_with_fourier_motzkin() {
    // Differential fuzz: the exact-rational simplex must agree with the
    // Fourier–Motzkin engine on the sat/unsat verdict for every random
    // conjunctive system, neither tripping a soundness alarm. Two independent
    // exact LRA decision procedures cross-validating each other.
    let mut state: u64 = 0x2545_F491_4F6C_DD1D;
    let mut next = || {
        state = state
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        (state >> 33) as u32
    };

    let mut sat_seen = 0u32;
    let mut unsat_seen = 0u32;
    for _ in 0..2000 {
        let mut arena = TermArena::new();
        let nvars = 1 + (next() % 3) as usize;
        let vars: Vec<_> = (0..nvars)
            .map(|i| arena.real_var(&format!("x{i}")).unwrap())
            .collect();
        let zero = arena.real_ratio(0, 1);

        let nconstraints = 2 + (next() % 4) as usize;
        let mut assertions = Vec::with_capacity(nconstraints);
        for _ in 0..nconstraints {
            let constant = i128::from(next() % 11) - 5;
            let mut lhs = arena.real_ratio(constant, 1);
            for &v in &vars {
                let coeff = i128::from(next() % 7) - 3;
                if coeff != 0 {
                    let c = arena.real_ratio(coeff, 1);
                    let term = arena.real_mul(c, v).unwrap();
                    lhs = arena.real_add(lhs, term).unwrap();
                }
            }
            let atom = match next() % 4 {
                0 => arena.real_lt(lhs, zero),
                1 => arena.real_le(lhs, zero),
                2 => arena.real_gt(lhs, zero),
                _ => arena.real_ge(lhs, zero),
            }
            .unwrap();
            assertions.push(atom);
        }

        let fm = check_with_lra(&arena, &assertions).expect("FM decides without alarm");
        let sx =
            check_with_lra_simplex(&arena, &assertions).expect("simplex decides without alarm");
        let agree = matches!(
            (&fm, &sx),
            (CheckResult::Sat(_), CheckResult::Sat(_)) | (CheckResult::Unsat, CheckResult::Unsat)
        );
        assert!(
            agree,
            "simplex and Fourier–Motzkin disagreed: fm={fm:?} sx={sx:?}"
        );
        match fm {
            CheckResult::Sat(_) => sat_seen += 1,
            CheckResult::Unsat => unsat_seen += 1,
            CheckResult::Unknown(_) => panic!("conjunctive QF_LRA is total"),
        }
    }
    assert!(sat_seen > 0 && unsat_seen > 0, "expected a mix of outcomes");
}
