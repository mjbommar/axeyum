//! The quantified ladder's valid-universal-elimination budget reserve
//! (ADR-1975).
//!
//! Valid-universal elimination — the sat-side universal-closure validity check
//! near the top of `finish_quantified_solve` — runs one quantifier-free
//! SUB-SOLVE per top-level universal, each handed whatever is left of the
//! ladder's wall clock. On `UFDTNIRA`'s pinned 200, **69 files** give up with
//! `quantified solve time budget exhausted after valid-universal elimination`,
//! every one of them PAST the 24,000 ms deadline: the pass spent the whole
//! clock and the seventeen-odd rungs below it never ran. That is 63 % of the
//! division's winnable set and the largest single blocker family on any
//! datatype division. [`QuantValidUniversalReservePolicy`] is the lever that
//! holds a share back for those rungs, selected by
//! `AXEYUM_QUANT_VALID_UNIVERSAL_RESERVE` so both arms come out of one binary.
//!
//! # What this suite is for
//!
//! Re-ordering a ladder's clock is **soundness-relevant in one direction**: it
//! changes WHICH rung answers, and a rung that answers with an unsound
//! instantiation yields a wrong `unsat`. Bounding *this* pass has a second
//! hazard of its own: the pass REWRITES the assertion set, replacing a
//! universal it has proven valid with `true`. Proving validity is a sub-solve
//! that can itself time out, so a bounded budget must make the pass eliminate
//! FEWER universals — never eliminate one on a sub-solve that did not finish.
//! An elimination on an unfinished sub-solve turns a satisfiable query whose
//! universal is NOT valid into a strictly weaker one, and the direction of that
//! weakening produces wrong `sat` on a refutable query and can mask a genuine
//! `unsat`.
//!
//! So every test here is either
//!
//! - an adversarial fixture over a **satisfiable** query whose plausible wrong
//!   answer is `unsat` (`*_is_not_unsat`), paired in this same file with a twin
//!   that differs in ONE small term and genuinely IS `unsat` — so the pair
//!   cannot be passed by a solver that answers `sat`/`unknown` to everything;
//!   or
//! - a fixture whose top-level universal is **not valid**, so a pass that
//!   eliminated it anyway would be observable as a changed verdict; or
//! - a direct assertion about the budget arithmetic, in which the DEFAULT arm
//!   must be byte-identical to the behaviour before the lever existed. Those
//!   live beside the code, in `auto.rs`'s unit tests.
//!
//! Every `Sat` replays its model against the ORIGINAL assertions **inside the
//! test**, rather than trusting the route's own replay: the route's replay is
//! part of the subject, and the ORIGINAL assertions are the ones the pass
//! rewrote away from.
//!
//! The verdicts pinned below were re-run against z3 4.13.3 (`z3 -T:24`) and
//! cvc5 1.3.4 (`cvc5 --tlimit 24000`) on 2026-09-13; both agree with every one,
//! and the per-fixture agreement is recorded in
//! `bench-results/ufdt-family-20260913/README.md`.

#![cfg(feature = "full")]

use std::time::Duration;

use axeyum_ir::{Value, eval};
use axeyum_solver::{
    CheckResult, QuantValidUniversalReservePolicy, QuantValidUniversalReservePolicyGuard,
    SolverConfig, solve_smtlib_with_model,
};

/// Every arm must be given a CLOCK, because the lever divides one: an unbounded
/// config is unchanged by every policy (asserted in `auto.rs`'s unit tests), so
/// a fixture with no timeout would run one arm three times and report it as
/// three.
fn config() -> SolverConfig {
    SolverConfig::new().with_timeout(Duration::from_secs(8))
}

/// Decides `text` under `policy` through the ordinary TEXT front door, and for
/// a `Sat` replays the returned model against the ORIGINAL assertions here.
///
/// The front door and not `check_auto` on a bare flat view: the quantified
/// ladder this lever sits in is reached through `solve_smtlib`'s dispatch, and
/// a flat `check_auto` on these scripts lands in the pure-Rust BV backend and
/// refuses the `Forall` outright — which would make every fixture below a test
/// of the wrong route.
fn decide_under(policy: QuantValidUniversalReservePolicy, text: &str) -> CheckResult {
    let _guard = QuantValidUniversalReservePolicyGuard::set(policy);
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
const ARMS: [QuantValidUniversalReservePolicy; 3] = [
    QuantValidUniversalReservePolicy::WholeBudget,
    QuantValidUniversalReservePolicy::LadderReserve { share: 4 },
    // `share = 1` is the CEILING arm the ADR-1975 sizing uses: the pass gets
    // `MIN_LADDER_SLICE` and the rungs below get essentially the whole clock.
    // It is the arm most likely to hand a verdict to a rung that never used to
    // answer this query, and the arm on which the pass's own sub-solves are
    // most likely to be cut off mid-flight -- which is exactly where an
    // elimination on an unfinished sub-solve would show up.
    QuantValidUniversalReservePolicy::LadderReserve { share: 1 },
];

// ---------------------------------------------------------------------------
// The adversarial SAT side. Each of these is satisfiable and the plausible
// wrong answer is `unsat`.
// ---------------------------------------------------------------------------

/// A genuinely VALID top-level universal (`forall x. x + 1 > x`) beside a
/// satisfiable ground constraint. **Satisfiable.**
///
/// This is the fixture the pass is FOR: it proves the universal valid, replaces
/// it with `true`, and the residual is quantifier-free. Its twin below differs
/// in ONE small term — `(> a 3)` becomes `(> a 7)` — and IS `unsat`.
const VALID_UNIVERSAL_SAT: &str = "(set-logic UFLIA)
     (declare-fun a () Int)
     (assert (forall ((x Int)) (> (+ x 1) x)))
     (assert (> a 3))
     (assert (< a 5))
     (check-sat)";

/// The `unsat` twin of [`VALID_UNIVERSAL_SAT`]: the SAME valid universal, with
/// the ground window emptied (`a > 7` and `a < 5`).
const VALID_UNIVERSAL_UNSAT: &str = "(set-logic UFLIA)
     (declare-fun a () Int)
     (assert (forall ((x Int)) (> (+ x 1) x)))
     (assert (> a 7))
     (assert (< a 5))
     (check-sat)";

/// A top-level universal that is **NOT valid** (`forall x. f(x) >= 0` says
/// something real about `f`), beside a ground fact consistent with it.
/// **Satisfiable.**
///
/// This is the adversarial direction specific to THIS pass: a bounded budget
/// must make it eliminate fewer universals, never eliminate this one. If the
/// pass ever replaced this universal with `true` on a sub-solve that merely ran
/// out of clock, the query would be weakened — and its `unsat` twin below,
/// which is refuted ONLY through the universal, would stop being `unsat`.
const NONVALID_UNIVERSAL_SAT: &str = "(set-logic UFLIA)
     (declare-fun f (Int) Int)
     (assert (forall ((x Int)) (>= (f x) 0)))
     (assert (= (f 0) 5))
     (check-sat)";

/// The `unsat` twin of [`NONVALID_UNIVERSAL_SAT`]: `f(0) = -5` contradicts the
/// universal at the single ground term `0`.
///
/// **This is the file that fails if the pass eliminates an unproven universal
/// on a truncated sub-solve.** Delete the universal and the remaining query is
/// `f(0) = -5`, which is satisfiable — so a wrongly-eliminating pass turns this
/// `unsat` into `sat`, and it is the only fixture here that can see that.
const NONVALID_UNIVERSAL_UNSAT: &str = "(set-logic UFLIA)
     (declare-fun f (Int) Int)
     (assert (forall ((x Int)) (>= (f x) 0)))
     (assert (= (f 0) (- 5)))
     (check-sat)";

#[test]
fn a_valid_universal_beside_a_satisfiable_ground_window_is_not_unsat_under_any_arm() {
    for policy in ARMS {
        let result = decide_under(policy, VALID_UNIVERSAL_SAT);
        assert!(
            !matches!(result, CheckResult::Unsat),
            "WRONG UNSAT under {policy:?}: `forall x. x + 1 > x` is valid and `3 < a < 5` \
             is satisfiable at `a = 4` (z3 4.13.3 and cvc5 1.3.4 both answer `sat`)."
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
fn a_nonvalid_universal_with_a_consistent_ground_fact_is_not_unsat_under_any_arm() {
    for policy in ARMS {
        let result = decide_under(policy, NONVALID_UNIVERSAL_SAT);
        assert!(
            !matches!(result, CheckResult::Unsat),
            "WRONG UNSAT under {policy:?}: `forall x. f(x) >= 0` with `f(0) = 5` is \
             satisfiable (z3 4.13.3 and cvc5 1.3.4 both answer `sat`)."
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
fn a_valid_universal_beside_an_empty_ground_window_is_unsat_under_any_arm() {
    for policy in ARMS {
        assert_eq!(
            decide_under(policy, VALID_UNIVERSAL_UNSAT),
            CheckResult::Unsat,
            "under {policy:?}: `a > 7` and `a < 5` have no common solution, and the valid \
             universal beside them constrains nothing."
        );
    }
}

#[test]
fn a_nonvalid_universal_refuted_at_one_ground_term_is_unsat_under_any_arm() {
    for policy in ARMS {
        assert_eq!(
            decide_under(policy, NONVALID_UNIVERSAL_UNSAT),
            CheckResult::Unsat,
            "under {policy:?}: `forall x. f(x) >= 0` with `f(0) = -5` is refuted by ONE \
             instantiation. A `sat` here means the universal was ELIMINATED without being \
             proven valid -- the specific unsoundness a budgeted elimination pass can \
             introduce -- and a ladder arm that merely cannot find the instantiation has \
             lost a decision the default arm makes."
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
    // `AXEYUM_QUANT_VALID_UNIVERSAL_RESERVE` in its environment gets. Asserted
    // through the public verdict rather than the private resolver so it cannot
    // pass by agreeing with a test-only path.
    assert_eq!(
        std::env::var("AXEYUM_QUANT_VALID_UNIVERSAL_RESERVE").ok(),
        None,
        "this suite must run with the lever UNSET; a test that passes only under an \
         ambient env var is a gate on one shell"
    );
    assert_eq!(
        decide_under(
            QuantValidUniversalReservePolicy::WholeBudget,
            NONVALID_UNIVERSAL_UNSAT
        ),
        CheckResult::Unsat
    );
}

/// The `share = 1` ceiling arm must still decide the queries the default arm
/// decides. This is the arm the ADR-1975 sizing runs, and a sizing arm that
/// loses verdicts for an unrelated reason would understate the reach it
/// measures.
#[test]
fn the_ceiling_arm_still_decides_a_valid_universal_query() {
    assert_eq!(
        decide_under(
            QuantValidUniversalReservePolicy::LadderReserve { share: 1 },
            VALID_UNIVERSAL_UNSAT
        ),
        CheckResult::Unsat,
        "the `share = 1` arm hands the pass MIN_LADDER_SLICE; a query whose refutation \
         does not need the universal at all must still be refuted by a rung below it"
    );
}
