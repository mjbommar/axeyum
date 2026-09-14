//! The Skolemized e-graph retry's budget share (lane `QBUDGET`, ADR-1995).
//!
//! The e-graph instantiation loop runs **twice** on a quantified query that
//! reaches `q:mbqi`: once at `finish_quantified_solve`'s `q:egraph` rung on the
//! original assertions, and once inside `prove_unsat_by_ematching` on the
//! Skolemized ones. The second pass — `skolemized_egraph_retry` — takes a
//! **half** slice of what the root deadline has left, held back for
//! `q:uf-fmf-full`, the pure-UF finite-model finder.
//!
//! On `UFNIA`/`UFLIA` that reserve is not spent by anything: the finder declines
//! a non-pure-UF query in one cheap scan, and 61 of 400 files on the committed
//! census (`bench-results/ufnia-uflia-census-20260913/census/*.tsv`) end with
//! this loop's own give-up string having left a median 8,681 ms (`UFNIA`) /
//! 2,574 ms (`UFLIA`) of the 24,000 ms root deadline unspent.
//! `AXEYUM_QINST_EGRAPH_RETRY_SHARE` hands that back so the question can be
//! measured from one binary. **It ships OFF.**
//!
//! # What this suite is for
//!
//! Re-proportioning a ladder's clock is **soundness-relevant in one direction**:
//! it changes WHICH rung answers, and a rung that answers from an unsound
//! instantiation yields a wrong `unsat`. So the fixtures here are satisfiable
//! queries whose plausible wrong answer is `unsat`, each paired with a twin that
//! differs in ONE small term and genuinely IS `unsat` — so the pair cannot be
//! passed by a solver answering `sat`/`unknown` to everything, nor by one
//! answering `unsat` to everything.
//!
//! The four fixtures are **reused verbatim** from
//! `tests/quant_egraph_reserve_row.rs` (ADR-1970), which pinned their verdicts
//! against z3 4.13.3 and cvc5 1.3.4 on 2026-09-13. They are reused rather than
//! re-derived because the two levers sit on the same ladder and a fixture that
//! discriminates for one discriminates for the other; this file does not
//! re-assert that external agreement as its own measurement.
//!
//! # What this suite is NOT
//!
//! It is not evidence that the retry rung is *reached often*. These fixtures are
//! small enough that the ladder may decide them above the rung. The route's hit
//! rate is a corpus measurement and is published with the A/B in
//! `bench-results/qbudget-20260913/README.md`, not inferred here.

#![cfg(feature = "full")]

use std::time::Duration;

use axeyum_ir::{Value, eval};
use axeyum_solver::{
    CheckResult, QinstEgraphRetryShareGuard, SolverConfig, last_qinst_egraph_retry_budget,
    prove_unsat_by_ematching, reset_last_qinst_egraph_retry_budget, solve_smtlib_with_model,
};

/// Every arm must be given a CLOCK, because the lever divides one: an unbounded
/// config keeps no timeout to slice, so a fixture with no timeout would run one
/// arm three times and report it as three.
fn config() -> SolverConfig {
    SolverConfig::new().with_timeout(Duration::from_secs(8))
}

/// The arms, so a fixture cannot pass by only ever exercising the shipped
/// default.
///
/// `1` is the CEILING arm the sizing uses: the retry takes the whole remaining
/// root clock, which is strictly more than any budget policy on this rung can
/// grant, and it is the arm most likely to hand a verdict to a pass that never
/// used to reach one — which is where a wrong `unsat` would appear.
const ARMS: [u32; 3] = [2, 1, 4];

/// Decides `text` with the retry share set to `share`, and for a `Sat` replays
/// the returned model against the ORIGINAL assertions here.
///
/// The front door and not `check_auto` on a bare flat view: the quantified
/// ladder this lever sits in is reached through `solve_smtlib`'s dispatch, and a
/// flat `check_auto` on these scripts lands in the pure-Rust BV backend and
/// refuses the `Forall` outright — which would make every fixture below a test
/// of the wrong route.
fn decide_under(share: u32, text: &str) -> CheckResult {
    let _guard = QinstEgraphRetryShareGuard::set(share);
    let solved = solve_smtlib_with_model(text, &config())
        .expect("the front door reports a verdict rather than an error");
    if let (CheckResult::Sat(_), Some(model)) = (&solved.outcome.result, &solved.model) {
        let assignment = model.to_assignment();
        // The enumerating evaluator cannot evaluate a universal over `Int` --
        // there is no finite domain to enumerate -- so it returns
        // `UnsupportedQuantifierDomain` on exactly the quantified assertion.
        // Replay every assertion it CAN evaluate and COUNT them: a replay loop
        // that silently evaluated nothing would pass over a model satisfying
        // none of the query, which is the failure this check exists to catch.
        let mut checked = 0usize;
        for (n, &assertion) in solved.assertions.iter().enumerate() {
            match eval(&solved.script.arena, assertion, &assignment) {
                Ok(Value::Bool(true)) => checked += 1,
                Err(axeyum_ir::IrError::UnsupportedQuantifierDomain(_)) => {}
                other => panic!(
                    "WRONG SAT at share={share}: assertion {n} evaluates to {other:?} under \
                     the returned model, not `true`."
                ),
            }
        }
        assert!(
            checked > 0,
            "the replay at share={share} evaluated ZERO assertions, so it checked nothing"
        );
    }
    solved.outcome.result
}

// ---------------------------------------------------------------------------
// The adversarial SAT side: satisfiable, with `unsat` as the plausible wrong
// answer.
// ---------------------------------------------------------------------------

/// `(forall x. f(x) >= 0)` with `f(0) = 5`. **Satisfiable.**
const UNIVERSAL_NONNEG_SAT: &str = "(set-logic UFLIA)
     (declare-fun f (Int) Int)
     (assert (forall ((x Int)) (>= (f x) 0)))
     (assert (= (f 0) 5))
     (check-sat)";

/// The `unsat` twin: `f(0) = -5` contradicts the universal at the single ground
/// term `0`.
const UNIVERSAL_NONNEG_UNSAT: &str = "(set-logic UFLIA)
     (declare-fun f (Int) Int)
     (assert (forall ((x Int)) (>= (f x) 0)))
     (assert (= (f 0) (- 5)))
     (check-sat)";

/// A universal violated only OUTSIDE the ground terms present, so an
/// instantiation that over-generalises from the ground set answers `unsat`.
/// **Satisfiable**: `f` may be `1` at `0` and `1` and anything elsewhere.
const UNIVERSAL_GUARDED_SAT: &str = "(set-logic UFLIA)
     (declare-fun f (Int) Int)
     (declare-fun c () Int)
     (assert (forall ((x Int)) (=> (and (<= 0 x) (<= x 1)) (= (f x) 1))))
     (assert (= c (+ (f 0) (f 1))))
     (assert (= c 2))
     (check-sat)";

/// The `unsat` twin: the SAME guarded universal with the ground sum pinned to
/// `3` instead of `2`.
const UNIVERSAL_GUARDED_UNSAT: &str = "(set-logic UFLIA)
     (declare-fun f (Int) Int)
     (declare-fun c () Int)
     (assert (forall ((x Int)) (=> (and (<= 0 x) (<= x 1)) (= (f x) 1))))
     (assert (= c (+ (f 0) (f 1))))
     (assert (= c 3))
     (check-sat)";

#[test]
fn universal_nonneg_with_positive_ground_fact_is_not_unsat_under_any_arm() {
    for share in ARMS {
        let result = decide_under(share, UNIVERSAL_NONNEG_SAT);
        assert!(
            !matches!(result, CheckResult::Unsat),
            "WRONG UNSAT at share={share}: `forall x. f(x) >= 0` with `f(0) = 5` is \
             satisfiable."
        );
        // Pinned as `Sat`, not merely `not Unsat`: an `unknown` here would skip
        // the model replay inside `decide_under` entirely and leave the
        // adversarial half of this file checking nothing.
        assert!(
            matches!(result, CheckResult::Sat(_)),
            "at share={share} this fixture must be DECIDED sat, or its replay never runs"
        );
    }
}

#[test]
fn universal_guarded_body_is_not_unsat_under_any_arm() {
    for share in ARMS {
        let result = decide_under(share, UNIVERSAL_GUARDED_SAT);
        assert!(
            !matches!(result, CheckResult::Unsat),
            "WRONG UNSAT at share={share}: the guarded universal is satisfiable with \
             `f(0) = f(1) = 1`."
        );
        assert!(
            matches!(result, CheckResult::Sat(_)),
            "at share={share} this fixture must be DECIDED sat, or its replay never runs"
        );
    }
}

// ---------------------------------------------------------------------------
// The unsat twins. Without these the file above reads as a solver that answers
// `sat`/`unknown` to everything.
// ---------------------------------------------------------------------------

#[test]
fn universal_nonneg_with_negative_ground_fact_is_unsat_under_any_arm() {
    for share in ARMS {
        assert_eq!(
            decide_under(share, UNIVERSAL_NONNEG_UNSAT),
            CheckResult::Unsat,
            "at share={share}: `forall x. f(x) >= 0` with `f(0) = -5` is refuted by ONE \
             instantiation; an arm that cannot find it has lost a decision the default \
             arm makes."
        );
    }
}

#[test]
fn universal_guarded_body_with_wrong_sum_is_unsat_under_any_arm() {
    for share in ARMS {
        assert_eq!(
            decide_under(share, UNIVERSAL_GUARDED_UNSAT),
            CheckResult::Unsat,
            "at share={share}: the guarded universal forces `f(0) = f(1) = 1`, so the \
             ground sum is 2 and cannot be 3."
        );
    }
}

// ---------------------------------------------------------------------------
// The lever on the DISPATCH PATH. Everything above would stay green if
// `skolemized_egraph_retry` stopped consulting the lever, because the ladder
// decides these fixtures either way. This is the test that does not.
// ---------------------------------------------------------------------------

/// A query with a **nested** quantifier under the universal, so
/// `prove_unsat_by_mbqi_inner`'s single-binder guard cannot take it and the
/// Skolemizing e-matching route — the one that owns `skolemized_egraph_retry` —
/// is the route that runs.
const NESTED_QUANT_UNSAT: &str = "(set-logic UFLIA)
     (declare-fun f (Int Int) Int)
     (assert (forall ((x Int)) (exists ((y Int)) (= (f x y) 0))))
     (assert (forall ((x Int) (y Int)) (> (f x y) 0)))
     (check-sat)";

/// **The load-bearing test of this lane's change.** It asserts that the rung
/// applies the ARM's budget, read back from the dispatch site itself.
///
/// Reverting `skolemized_egraph_retry` to apply the bare
/// `QINST_EGRAPH_RETRY_SLICE` constant leaves every other test in this file and
/// in `auto.rs` green — the arithmetic helpers still compute the right numbers,
/// and the fixtures above are decided identically under every arm. This one
/// fails, because the recorded budget stops tracking the arm.
///
/// Verified by deleting exactly that: with the call site on the constant, this
/// test is the only one in the workspace that dies.
#[test]
fn the_retry_rung_applies_the_arms_budget() {
    let budget = Duration::from_secs(8);
    let mut observed = Vec::new();
    for share in [2u32, 1, 4] {
        let _guard = QinstEgraphRetryShareGuard::set(share);
        reset_last_qinst_egraph_retry_budget();
        let script = axeyum_smtlib::parse_script(NESTED_QUANT_UNSAT)
            .expect("the fixture parses as an SMT-LIB script");
        let mut arena = script.arena;
        let assertions = script.assertions.clone();
        // Directly on the route that owns the rung, so the ladder above cannot
        // decide the query before the rung is reached. The VERDICT is not the
        // subject here (the rung declining is fine); the applied budget is.
        let _ = prove_unsat_by_ematching(
            &mut arena,
            &assertions,
            &SolverConfig::new().with_timeout(budget),
        );
        observed.push((share, last_qinst_egraph_retry_budget()));
    }

    for (share, applied) in &observed {
        let applied = applied.unwrap_or_else(|| {
            panic!(
                "the Skolemized e-graph retry never ran at share={share}, so this test \
                 measured nothing. It is the ONLY check that the dispatch site consults \
                 the lever; a fixture that stops reaching the rung must be replaced, not \
                 tolerated."
            )
        });
        // `slice_of` clamps to the remaining budget, and the rung enters with a
        // little of the 8 s already spent by Skolemization, so compare against
        // the share's fraction of the WHOLE budget with a generous floor rather
        // than for exact equality.
        let ceiling = budget / *share;
        assert!(
            applied <= ceiling,
            "at share={share} the rung was handed {applied:?}, which is more than the \
             arm's {ceiling:?} of the root budget"
        );
        assert!(
            applied >= ceiling / 2,
            "at share={share} the rung was handed only {applied:?}, far under the arm's \
             {ceiling:?}; the dispatch site is not applying this arm"
        );
    }

    // The arms must be DISTINGUISHABLE at the dispatch site. Equality here is
    // precisely the inert-lever failure, and no assertion above catches it:
    // each arm's band is checked only against itself.
    let at = |s: u32| {
        observed
            .iter()
            .find(|(share, _)| *share == s)
            .and_then(|(_, applied)| *applied)
            .expect("every arm recorded a budget")
    };
    assert!(
        at(1) > at(2) && at(2) > at(4),
        "the three arms must hand the rung strictly decreasing budgets; got \
         share=1 -> {:?}, share=2 -> {:?}, share=4 -> {:?}. Equal values mean the \
         dispatch site is ignoring the lever.",
        at(1),
        at(2),
        at(4)
    );
}

/// The shipped default must be the historical behaviour. A lever whose "off"
/// position is not the old code turns every previously recorded baseline into a
/// measurement of something else.
#[test]
fn the_lever_ships_off() {
    assert_eq!(
        std::env::var("AXEYUM_QINST_EGRAPH_RETRY_SHARE").ok(),
        None,
        "this suite must run with the lever UNSET; a test that passes only under an \
         ambient env var is a gate on one shell"
    );
    reset_last_qinst_egraph_retry_budget();
    let script =
        axeyum_smtlib::parse_script(NESTED_QUANT_UNSAT).expect("the fixture parses as a script");
    let mut arena = script.arena;
    let assertions = script.assertions.clone();
    let _ = prove_unsat_by_ematching(
        &mut arena,
        &assertions,
        &SolverConfig::new().with_timeout(Duration::from_secs(8)),
    );
    let applied = last_qinst_egraph_retry_budget()
        .expect("the rung runs on this fixture; see `the_retry_rung_applies_the_arms_budget`");
    assert!(
        applied <= Duration::from_secs(4) && applied >= Duration::from_secs(2),
        "with no lever in the environment the rung must get the shipped HALF slice of \
         the 8 s budget; got {applied:?}"
    );
}
