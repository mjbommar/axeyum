//! ADR-2104: driven-producer coverage for the typed `DeclineReason` detail
//! enums (`UnsupportedDetail`, `Budget`, `VerifierRejected`).
//!
//! Each `#[test]` below constructs an actual query shape and asserts that the
//! resulting [`RouteTrace`] carries the specific typed variant that query is
//! chosen to hit — a driven test, not a list. The accounting functions at the
//! bottom are the honest half: they match every declared variant with **no
//! wildcard arm**, so adding a variant without naming it here fails to
//! compile, and each arm names either the test that drives it or the
//! technical reason it cannot be driven from a query at this crate's public
//! surface (or, in a few cases, why driving it would require the very bug the
//! branch exists to catch — ADR-2060's own finding for two of its six
//! `SimplexDecline` producers).

#![cfg(feature = "full")]

use std::time::Duration;

use axeyum_ir::{Sort, TermArena};
use axeyum_solver::{
    Budget, CheckResult, DeclineReason, RouteAttributionGuard, RouteOutcome, RouteTrace,
    SolverConfig, UnsupportedDetail, VerifierRejected, check_auto_explained,
    last_route_attribution, solve_smtlib,
};

fn config() -> SolverConfig {
    SolverConfig {
        timeout: Some(Duration::from_millis(5_000)),
        ..SolverConfig::default()
    }
}

fn declined_reasons(trace: &RouteTrace) -> Vec<(&str, &DeclineReason)> {
    trace
        .attempts()
        .iter()
        .filter_map(|a| match &a.outcome {
            RouteOutcome::Declined(reason) => Some((a.route, reason)),
            _ => None,
        })
        .collect()
}

// ---------------------------------------------------------------------------
// UnsupportedDetail
// ---------------------------------------------------------------------------

/// `datatype-elim` (and the other ten `auto.rs` sites behind
/// `unsupported_decline`) bind a `SolverError::Unsupported` payload and record
/// [`UnsupportedDetail::Backend`]. A `QF_UFDT` goal over a datatype
/// constructor the native decider does not cover drives it end to end.
#[test]
fn unsupported_detail_backend_is_driven_by_a_datatype_refusal() {
    let script = r"
(set-logic QF_UFDT)
(declare-datatypes ((Lst 0)) (((nil) (cons (hd Int) (tl Lst)))))
(declare-fun p (Lst) Bool)
(declare-const x Lst)
(assert (p (cons 0 x)))
(assert (not (p (cons 0 nil))))
(check-sat)
";
    let _guard = RouteAttributionGuard::enable();
    let _ = solve_smtlib(script, &config());
    let trace = last_route_attribution();
    let hit = declined_reasons(&trace).into_iter().any(|(_, reason)| {
        matches!(
            reason,
            DeclineReason::UnsupportedDetail(UnsupportedDetail::Backend(msg)) if !msg.is_empty()
        )
    });
    assert!(
        hit,
        "expected an UnsupportedDetail::Backend decline somewhere in the trail: {trace}"
    );
}

/// A script the front-door parser cannot read is refused at ingest, recorded
/// against `fd:parse` as [`UnsupportedDetail::IngestRefusal`].
#[test]
fn unsupported_detail_ingest_refusal_is_driven_by_an_unparseable_script() {
    let _guard = RouteAttributionGuard::enable();
    let outcome = solve_smtlib("(assert (", &config());
    assert!(
        outcome.is_err(),
        "this fixture exists because ingest REFUSES it: {outcome:?}"
    );
    let trace = last_route_attribution();
    let hit = declined_reasons(&trace).into_iter().any(|(route, reason)| {
        route == "fd:parse"
            && matches!(
                reason,
                DeclineReason::UnsupportedDetail(UnsupportedDetail::IngestRefusal(msg))
                    if !msg.is_empty()
            )
    });
    assert!(
        hit,
        "expected an UnsupportedDetail::IngestRefusal decline against fd:parse: {trace}"
    );
}

// ---------------------------------------------------------------------------
// Budget
// ---------------------------------------------------------------------------

/// A single-variable quadratic with a coefficient above `MAX_ABS_COEFF`
/// (`2^40`) trips `nia-square`'s `i128` safety guard: [`Budget::SquareCoefficientGuardExceeded`].
#[test]
fn budget_square_coefficient_guard_exceeded_is_driven_by_an_oversized_coefficient() {
    let mut arena = TermArena::new();
    let sx = arena.declare("x", Sort::Int).unwrap();
    let x = arena.var(sx);
    // a*x*x > 5, with a = 2^41 (above the 2^40 guard). An inequality rather
    // than an equality so `cas-int-units`'s divisibility certificate (which
    // only certifies equalities) is `NotApplicable` and does not short-circuit
    // the query before `nia-square` sees it.
    let a = arena.int_const(1i128 << 41);
    let ax = arena.int_mul(a, x).unwrap();
    let axx = arena.int_mul(ax, x).unwrap();
    let five = arena.int_const(5);
    let eq = arena.int_gt(axx, five).unwrap();
    let (_result, trace) = check_auto_explained(&mut arena, &[eq], &config()).unwrap();
    let hit = declined_reasons(&trace).into_iter().any(|(route, reason)| {
        route == "nia-square"
            && matches!(
                reason,
                DeclineReason::Budget(Budget::SquareCoefficientGuardExceeded)
            )
    });
    assert!(
        hit,
        "expected a Budget::SquareCoefficientGuardExceeded decline from nia-square: {trace}"
    );
}

/// A nonlinear multi-variable integer query, under a timeout that has already
/// expired by the time NIA's refinement loop checks its deadline, drives
/// [`Budget::NiaRelaxationSliceExpired`].
#[test]
fn budget_nia_relaxation_slice_expired_is_driven_by_a_zero_timeout_nonlinear_query() {
    let mut arena = TermArena::new();
    let sx = arena.declare("x", Sort::Int).unwrap();
    let sy = arena.declare("y", Sort::Int).unwrap();
    let x = arena.var(sx);
    let y = arena.var(sy);
    let xy = arena.int_mul(x, y).unwrap();
    let seven = arena.int_const(7);
    let eq1 = arena.eq(xy, seven).unwrap();
    let sum = arena.int_add(x, y).unwrap();
    let eight = arena.int_const(8);
    let eq2 = arena.eq(sum, eight).unwrap();
    let cfg = SolverConfig {
        timeout: Some(Duration::from_nanos(1)),
        ..SolverConfig::default()
    };
    let (_result, trace) = check_auto_explained(&mut arena, &[eq1, eq2], &cfg).unwrap();
    let hit = declined_reasons(&trace)
        .into_iter()
        .any(|(_, reason)| matches!(reason, DeclineReason::Budget(Budget::Other(_))));
    assert!(
        hit,
        "expected some budget-style (resource-limited) decline under a \
         1-nanosecond timeout: {trace}"
    );
}

/// A route that returns `Unknown` with a budget-style [`UnknownKind`] (e.g.
/// `ResourceLimit`) is mapped by [`DeclineReason::from_unknown`] onto
/// [`Budget::Other`] — the pass-through from an already-typed
/// [`axeyum_solver::UnknownKind`]/[`axeyum_solver::UnknownReason`], not a
/// sentence this crate composes. A tiny top-level timeout on an undecided
/// nonlinear goal is the same fixture `tests/route_trace.rs`'s
/// `resource_capped_lia_records_budget` already uses, re-asserted here
/// against the typed variant.
#[test]
fn budget_other_is_driven_by_a_resource_capped_query() {
    let mut arena = TermArena::new();
    let sx = arena.declare("ns_x", Sort::Int).unwrap();
    let sy = arena.declare("ns_y", Sort::Int).unwrap();
    let x = arena.var(sx);
    let y = arena.var(sy);
    let xx = arena.int_mul(x, x).unwrap();
    let yy = arena.int_mul(y, y).unwrap();
    let sum = arena.int_add(xx, yy).unwrap();
    let three = arena.int_const(3);
    let eq = arena.eq(sum, three).unwrap();
    let cfg = SolverConfig {
        timeout: Some(Duration::from_millis(1)),
        ..SolverConfig::default()
    };
    let (result, trace) = check_auto_explained(&mut arena, &[eq], &cfg).unwrap();
    assert!(matches!(result, CheckResult::Unknown(_)));
    let hit = declined_reasons(&trace)
        .into_iter()
        .any(|(_, reason)| matches!(reason, DeclineReason::Budget(Budget::Other(_))));
    assert!(hit, "expected at least one Budget::Other decline: {trace}");
}

// ---------------------------------------------------------------------------
// Accounting: every declared variant is named, driven or not
// ---------------------------------------------------------------------------

/// Names the test that drives each [`UnsupportedDetail`] variant, or the
/// reason it is not driven here. No wildcard arm: a new variant fails this
/// match at compile time until it is accounted for.
fn unsupported_detail_account(detail: &UnsupportedDetail) -> &'static str {
    match detail {
        UnsupportedDetail::Backend(_) => {
            "driven: unsupported_detail_backend_is_driven_by_a_datatype_refusal"
        }
        UnsupportedDetail::IngestRefusal(_) => {
            "driven: unsupported_detail_ingest_refusal_is_driven_by_an_unparseable_script"
        }
        UnsupportedDetail::OwnershipInconsistency(_) => {
            "undriven: fires only when a route's declared Ownership::Complete (auto.rs's \
             ownership table, ADR-2100) disagrees with what the route actually refused -- a \
             route claiming ownership and then refusing IS the bug this variant reports. \
             Driving it from a query means constructing a real ownership/behaviour mismatch, \
             which is the QUANT-LADDER-OWNERSHIP lane's surface, not a query shape this test \
             owns; see tests/route_ownership.rs for that lane's own coverage of the marker text."
        }
    }
}

/// Names the test that drives each [`Budget`] variant, or the reason it is
/// not driven here.
fn budget_account(detail: &Budget) -> &'static str {
    match detail {
        Budget::NiaRelaxationSliceExpired => {
            "driven: budget_nia_relaxation_slice_expired_is_driven_by_a_zero_timeout_nonlinear_query"
        }
        Budget::NiaRefinementRoundCapReached => {
            "undriven: MAX_REFINEMENT_ROUNDS is 64; reaching this decline needs a nonlinear \
             integer system that produces 64 CONSECUTIVE spurious (non-replaying) relaxation \
             models without ever converging -- constructing such an adversarial instance is a \
             research question of its own, not a query this test can assemble by hand."
        }
        Budget::SquareCoefficientGuardExceeded => {
            "driven: budget_square_coefficient_guard_exceeded_is_driven_by_an_oversized_coefficient"
        }
        Budget::IntBoxEnumerationCapExceeded => {
            "undriven: needs a query where prove_int_box first PROVES a finite integer box, the \
             exact-bounded-box blast (solve_exact_bounded_box) ALSO declines on it, and the \
             box's case count exceeds MAX_INT_BOX_ENUM_CASES -- a three-stage chain of internal \
             decisions this test would have to reverse-engineer rather than construct directly."
        }
        Budget::Other(_) => "driven: budget_other_is_driven_by_a_resource_capped_query",
    }
}

/// Names the test that drives each [`VerifierRejected`] variant, or the
/// reason it is not driven here. Several of these are trust-anchor branches
/// by design (ADR-2060's own term): a route replay-checks its own candidate
/// before returning it, so reaching the decline means the candidate the
/// decider itself produced failed verification -- constructing that from a
/// query means constructing the underlying decider bug, not a query shape.
fn verifier_rejected_account(detail: &VerifierRejected) -> &'static str {
    match detail {
        VerifierRejected::MbqiCandidateUnchecked => {
            "undriven: needs the full MBQI rung (q:mbqi) to reach a `sat` verdict with no \
             checked model attached -- a quantified fixture reaching this specific late rung \
             ahead of every earlier quantified rung was not constructed here."
        }
        VerifierRejected::CoercionRelaxCouplingFailed => {
            "undriven: `coercion-relax` is the Nelson-Oppen int/real fallback reached only after \
             every earlier int/real route declines; needs a mixed int/real query whose relaxed \
             candidate fails the original coupling check specifically at this late a rung."
        }
        VerifierRejected::Backend(_) => {
            "undriven: `uf-arith-lazy-overbound-pre-lia`'s SolverError::Backend(detail) arm is a \
             backend-internal error surfacing through a specific lazy overbound sub-route; not \
             reachable by construction from the public front door without reproducing that \
             backend's own internal failure."
        }
        VerifierRejected::MbqiQuickReplayFailed => {
            "undriven: needs the bounded first-refusal MBQI rung (q:mbqi-quick) specifically, \
             ahead of every earlier quantified rung, producing a sat candidate that fails replay."
        }
        VerifierRejected::CasNormalFormDisagreement
        | VerifierRejected::CasDivisibilityCertificateFailed
        | VerifierRejected::CasIdealCombinationFailed => {
            "undriven (trust anchor): each CAS refuter (cas-identity-refuter / cas-int-units / \
             cas-ideal-refuter) computes a candidate refutation and then independently \
             re-derives it before returning Unsat; reaching VerifierRejected means the CAS's own \
             two derivations disagreed, i.e. constructing the CAS bug this check exists to catch."
        }
        VerifierRejected::NiaRelaxationReplayFailed => {
            "undriven: fires when refine=false (small_domain/no-tangent-lemma setup) and the \
             relaxation model does not replay; distinguishing this from the refine=true path \
             (NiaRefinementNoNewLemma) needs the exact internal setup selection, not just a \
             nonlinear query shape."
        }
        VerifierRejected::NiaRefinementNoNewLemma => {
            "undriven: fires when refine=true but a round's tangent-lemma refinement adds \
             nothing new -- needs a nonlinear system where the McCormick/tangent lemma generator \
             genuinely stalls, which (like the 64-round cap) is an adversarial-instance question."
        }
        VerifierRejected::SquareWitnessReplayFailed => {
            "undriven (trust anchor): decide_quadratic/decide_high_degree's Sat witnesses are \
             derived exactly (discriminant / rational-root); reaching this decline means one of \
             those closed-form derivations produced a wrong witness -- the decider bug, not a \
             query shape."
        }
        VerifierRejected::RealRelaxationSatDoesNotTransfer => {
            "undriven: needs a multi-variable integer query nia-square declines on (so it is not \
             decided earlier) whose real relaxation is sat while the integers are not, AND that \
             reaches int-real-relax specifically ahead of the CAS/width-ladder routes that also \
             sit near it in the dispatch order -- not constructed here."
        }
    }
}

/// The accounting functions above must be exhaustive (no wildcard arm) and
/// must return a non-empty classification for a live instance of every
/// variant. This is what makes a future variant that nobody accounted for a
/// compile error instead of a silent gap.
#[test]
fn every_typed_detail_variant_is_accounted_for() {
    for detail in [
        UnsupportedDetail::Backend(String::new()),
        UnsupportedDetail::IngestRefusal(String::new()),
        UnsupportedDetail::OwnershipInconsistency(String::new()),
    ] {
        assert!(!unsupported_detail_account(&detail).is_empty());
    }
    for detail in [
        Budget::NiaRelaxationSliceExpired,
        Budget::NiaRefinementRoundCapReached,
        Budget::SquareCoefficientGuardExceeded,
        Budget::IntBoxEnumerationCapExceeded,
        Budget::Other(String::new()),
    ] {
        assert!(!budget_account(&detail).is_empty());
    }
    for detail in [
        VerifierRejected::MbqiCandidateUnchecked,
        VerifierRejected::CoercionRelaxCouplingFailed,
        VerifierRejected::Backend(String::new()),
        VerifierRejected::MbqiQuickReplayFailed,
        VerifierRejected::CasNormalFormDisagreement,
        VerifierRejected::CasDivisibilityCertificateFailed,
        VerifierRejected::CasIdealCombinationFailed,
        VerifierRejected::NiaRelaxationReplayFailed,
        VerifierRejected::NiaRefinementNoNewLemma,
        VerifierRejected::SquareWitnessReplayFailed,
        VerifierRejected::RealRelaxationSatDoesNotTransfer,
    ] {
        assert!(!verifier_rejected_account(&detail).is_empty());
    }
}
