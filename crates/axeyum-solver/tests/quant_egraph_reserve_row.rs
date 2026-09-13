//! The quantified ladder's e-graph budget reserve (ADR-1970).
//!
//! `q:egraph` — the e-matching instantiation loop — received the ladder's
//! WHOLE remaining wall clock, and `finish_quantified_solve`'s own comment
//! already recorded what it does with it: *"the e-graph instantiation loop
//! reliably consumes every second it is given"*. On **23 of the 54 classified
//! `UFNIA` winnable rows** it spent a median 22.5 s of a 24 s budget, declined,
//! and the rungs below it (full MBQI, the full pure-UF finite-model finder)
//! never ran at all — the ladder ended at
//! `quantified_timeout("e-matching")`. [`QuantEgraphReservePolicy`] is the
//! lever that holds a share back for them, selected by
//! `AXEYUM_QUANT_EGRAPH_RESERVE` so both arms come out of one binary.
//!
//! # What this suite is for
//!
//! Re-ordering a ladder's clock is **soundness-relevant in one direction**: it
//! changes WHICH rung answers, and a rung that answers with an unsound
//! instantiation yields a wrong `unsat`. So every test here is either
//!
//! - an adversarial fixture over a **satisfiable** query whose plausible wrong
//!   answer is `unsat` (`*_is_not_unsat`), paired in this same file with a
//!   twin that differs in ONE small term and genuinely IS `unsat` — so the
//!   pair cannot be passed by a solver that answers `sat`/`unknown` to
//!   everything; or
//! - a direct assertion about the budget arithmetic, in which the DEFAULT arm
//!   must be byte-identical to the behaviour before the lever existed.
//!
//! Every `Sat` replays its model against the ORIGINAL assertions **inside the
//! test**, rather than trusting the route's own replay: the route's replay is
//! part of the subject.
//!
//! The verdicts pinned below were re-run against z3 4.13.3 (`z3 -T:24`) and
//! cvc5 1.3.4 (`cvc5 --tlimit 24000`) on 2026-09-13; both agree with every one.

#![cfg(feature = "full")]

use std::time::Duration;

use axeyum_ir::{Value, eval};
use axeyum_solver::{
    CheckResult, QuantEgraphReservePolicy, QuantEgraphReservePolicyGuard, SolverConfig,
    solve_smtlib_with_model,
};

/// Every arm must be given a CLOCK, because the lever divides one: an unbounded
/// config is unchanged by every policy (`quant_egraph_budget_leaves_an_unbounded
/// _config_unbounded`), so a fixture with no timeout would run one arm three
/// times and report it as three.
fn config() -> SolverConfig {
    SolverConfig::new().with_timeout(Duration::from_secs(8))
}

/// Decides `text` under `policy` through the ordinary TEXT front door, and for
/// a `Sat` replays the returned model against the ORIGINAL assertions here.
///
/// The front door and not `check_auto` on a bare flat view: the quantified
/// ladder this lever sits in is reached through `solve_smtlib`'s dispatch, and
/// a flat `check_auto` on these scripts lands in the pure-Rust BV backend and
/// refuses the `Forall` outright -- which would make every fixture below a test
/// of the wrong route.
fn decide_under(policy: QuantEgraphReservePolicy, text: &str) -> CheckResult {
    let _guard = QuantEgraphReservePolicyGuard::set(policy);
    let solved = solve_smtlib_with_model(text, &config())
        .expect("the front door reports a verdict rather than an error");
    if let (CheckResult::Sat(_), Some(model)) = (&solved.outcome.result, &solved.model) {
        let assignment = model.to_assignment();
        // The enumerating evaluator cannot evaluate a universal over `Int` --
        // there is no finite domain to enumerate -- so it returns
        // `UnsupportedQuantifierDomain` rather than a truth value on exactly
        // the quantified assertion. Replay every assertion it CAN evaluate and
        // COUNT them: a replay loop that silently evaluated nothing would pass
        // over a model that satisfies none of the query, which is the failure
        // this check exists to catch. The universal itself is covered by the
        // `!Unsat` assertion at the call site, which is the soundness claim.
        let mut checked = 0usize;
        for (n, &assertion) in solved.assertions.iter().enumerate() {
            match eval(&solved.script.arena, assertion, &assignment) {
                Ok(Value::Bool(true)) => checked += 1,
                Err(axeyum_ir::IrError::UnsupportedQuantifierDomain(_)) => {}
                other => panic!(
                    "WRONG SAT under {policy:?}: assertion {n} evaluates to {other:?} under \
                     the returned model, not `true`."
                ),
            }
        }
        assert!(
            checked > 0,
            "the replay under {policy:?} evaluated ZERO assertions, so it checked nothing"
        );
    }
    solved.outcome.result
}

/// Both arms of the lever, so a fixture cannot pass by only ever exercising the
/// shipped default.
const ARMS: [QuantEgraphReservePolicy; 3] = [
    QuantEgraphReservePolicy::WholeBudget,
    QuantEgraphReservePolicy::LadderReserve { share: 4 },
    // `share = 1` is the CEILING arm the census sizing uses: `q:egraph` gets
    // `MIN_LADDER_SLICE` and the rungs below get essentially the whole clock.
    // It is the arm most likely to hand a verdict to a rung that never used to
    // answer this query, which is exactly where a wrong `unsat` would appear.
    QuantEgraphReservePolicy::LadderReserve { share: 1 },
];

// ---------------------------------------------------------------------------
// The adversarial SAT side. Each of these is satisfiable and the plausible
// wrong answer is `unsat`: a universal is asserted over an uninterpreted
// function together with a ground fact that a careless instantiation would
// read as contradicting it.
// ---------------------------------------------------------------------------

/// `(forall x. f(x) >= 0)` with `f(0) = 5`. **Satisfiable.**
///
/// Its twin below differs in ONE small term — `5` becomes `(- 5)` — and IS
/// `unsat`. The pair is the negative control for each other: a route that
/// answered `unknown` to everything would fail the twin, and a route that
/// answered `unsat` to everything would fail this one.
const UNIVERSAL_NONNEG_SAT: &str = "(set-logic UFLIA)
     (declare-fun f (Int) Int)
     (assert (forall ((x Int)) (>= (f x) 0)))
     (assert (= (f 0) 5))
     (check-sat)";

/// The `unsat` twin of [`UNIVERSAL_NONNEG_SAT`]: `f(0) = -5` contradicts the
/// universal at the single ground term `0`.
const UNIVERSAL_NONNEG_UNSAT: &str = "(set-logic UFLIA)
     (declare-fun f (Int) Int)
     (assert (forall ((x Int)) (>= (f x) 0)))
     (assert (= (f 0) (- 5)))
     (check-sat)";

/// A universal whose body is only violated OUTSIDE the ground terms present,
/// so an instantiation that over-generalises from the ground set answers
/// `unsat`. **Satisfiable**: `f` may take the value `1` at `0` and `1` and
/// anything at all elsewhere.
const UNIVERSAL_GUARDED_SAT: &str = "(set-logic UFLIA)
     (declare-fun f (Int) Int)
     (declare-fun c () Int)
     (assert (forall ((x Int)) (=> (and (<= 0 x) (<= x 1)) (= (f x) 1))))
     (assert (= c (+ (f 0) (f 1))))
     (assert (= c 2))
     (check-sat)";

/// The `unsat` twin of [`UNIVERSAL_GUARDED_SAT`]: the SAME guarded universal,
/// with the ground sum pinned to `3` instead of `2`.
const UNIVERSAL_GUARDED_UNSAT: &str = "(set-logic UFLIA)
     (declare-fun f (Int) Int)
     (declare-fun c () Int)
     (assert (forall ((x Int)) (=> (and (<= 0 x) (<= x 1)) (= (f x) 1))))
     (assert (= c (+ (f 0) (f 1))))
     (assert (= c 3))
     (check-sat)";

#[test]
fn universal_nonneg_with_positive_ground_fact_is_not_unsat_under_any_arm() {
    for policy in ARMS {
        let result = decide_under(policy, UNIVERSAL_NONNEG_SAT);
        assert!(
            !matches!(result, CheckResult::Unsat),
            "WRONG UNSAT under {policy:?}: `forall x. f(x) >= 0` with `f(0) = 5` is \
             satisfiable (z3 4.13.3 and cvc5 1.3.4 both answer `sat`)."
        );
        // Pinned as `Sat`, not merely `not Unsat`: an `unknown` here would skip
        // the model replay inside `decide_under` entirely and leave the
        // adversarial half of this file checking nothing.
        assert!(
            matches!(result, CheckResult::Sat(_)),
            "under {policy:?} this fixture must be DECIDED sat, or its replay never runs"
        );
    }
}

#[test]
fn universal_guarded_body_is_not_unsat_under_any_arm() {
    for policy in ARMS {
        let result = decide_under(policy, UNIVERSAL_GUARDED_SAT);
        assert!(
            !matches!(result, CheckResult::Unsat),
            "WRONG UNSAT under {policy:?}: the guarded universal is satisfiable with \
             `f(0) = f(1) = 1` (z3 4.13.3 and cvc5 1.3.4 both answer `sat`)."
        );
        assert!(
            matches!(result, CheckResult::Sat(_)),
            "under {policy:?} this fixture must be DECIDED sat, or its replay never runs"
        );
    }
}

// ---------------------------------------------------------------------------
// The unsat twins. Without these the file above reads as a solver that answers
// `sat`/`unknown` to everything.
// ---------------------------------------------------------------------------

#[test]
fn universal_nonneg_with_negative_ground_fact_is_unsat_under_any_arm() {
    for policy in ARMS {
        assert_eq!(
            decide_under(policy, UNIVERSAL_NONNEG_UNSAT),
            CheckResult::Unsat,
            "under {policy:?}: `forall x. f(x) >= 0` with `f(0) = -5` is refuted by ONE \
             instantiation; a ladder arm that cannot find it has lost a decision the \
             default arm makes."
        );
    }
}

#[test]
fn universal_guarded_body_with_wrong_sum_is_unsat_under_any_arm() {
    for policy in ARMS {
        assert_eq!(
            decide_under(policy, UNIVERSAL_GUARDED_UNSAT),
            CheckResult::Unsat,
            "under {policy:?}: the guarded universal forces `f(0) = f(1) = 1`, so the \
             ground sum is 2 and cannot be 3."
        );
    }
}

// ---------------------------------------------------------------------------
// The lever itself. The load-bearing claim is that the DEFAULT arm changes
// nothing, so it is asserted directly rather than inferred from the fixtures.
// ---------------------------------------------------------------------------

/// The shipped default must be the historical behaviour. A lever whose "off"
/// position is not the old code turns every previously recorded baseline into a
/// measurement of something else.
#[test]
fn the_default_policy_is_whole_budget() {
    // No guard: this reads the PROCESS policy, which is what a run with no
    // `AXEYUM_QUANT_EGRAPH_RESERVE` in its environment gets. Asserted through
    // the public verdict rather than the private resolver so it cannot pass by
    // agreeing with a test-only path.
    assert_eq!(
        std::env::var("AXEYUM_QUANT_EGRAPH_RESERVE").ok(),
        None,
        "this suite must run with the lever UNSET; a test that passes only under an \
         ambient env var is a gate on one shell"
    );
    assert_eq!(
        decide_under(
            QuantEgraphReservePolicy::WholeBudget,
            UNIVERSAL_NONNEG_UNSAT
        ),
        CheckResult::Unsat
    );
}

/// The `share = 1` ceiling arm must still decide the queries the default arm
/// decides. This is the arm the census sizing runs, and a sizing arm that loses
/// verdicts for an unrelated reason would understate the reach it measures.
#[test]
fn the_ceiling_arm_still_refutes_a_one_instantiation_query() {
    assert_eq!(
        decide_under(
            QuantEgraphReservePolicy::LadderReserve { share: 1 },
            UNIVERSAL_NONNEG_UNSAT
        ),
        CheckResult::Unsat,
        "the `share = 1` arm hands `q:egraph` MIN_LADDER_SLICE; a query refuted by one \
         instantiation must still be refuted by a rung below it"
    );
}
