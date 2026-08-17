//! A missing certificate must not cost a verdict.
//!
//! `int_blast` deliberately rejects `int.pow2`: its value is exponential in its
//! operand, so there is no faithful finite bit-vector encoding, and the rejection
//! exists so the query can fall through to a route that does handle it. The
//! rejection site says exactly that.
//!
//! `certify_bounded_int_blast` mapped every `IntBlastError` to a backend error,
//! which turned that fall-through into a hard stop. Measured on
//! `QF_NIA/cvc5-regress-clean/cli__regress0__nl__pow2-native-{2,7}.smt2` — both
//! declared `unsat`, both decided `unsat` by `check_auto` in 0.13ms via
//! `int-box-eval`:
//!
//! ```text
//! solve:            unsat
//! produce_evidence: error backend failure: int-blast failed:
//!                   integer bit-blast does not support operator IntPow2
//! ```
//!
//! The dominance audit recorded that as `solver-error` (it is two of the
//! repository's two counted proof-production errors) and `smtcomp_cli --evidence`
//! rendered it `unknown`. So the two front doors disagreed on a decided query,
//! and the disagreement was silent at the CLI.
//!
//! The fix is a decline, not new capability: `produce_evidence` now reports
//! `unsat` with **uncertified** evidence. The certificate gap is real and stays
//! visible; what it no longer does is swallow the verdict.

#![cfg(feature = "full")]

use axeyum_smtlib::parse_script;
use axeyum_solver::{CheckResult, Evidence, SolverConfig, produce_evidence, solve_smtlib};

/// `0 <= x < 16 ∧ 2^x < x` — unsatisfiable, and `int.pow2` puts it outside the
/// integer bit-blaster. This is `pow2-native-2.smt2`, inline.
const POW2_UNSAT: &str = "(set-logic QF_NIA)\n\
     (declare-fun x () Int)\n\
     (assert (and (<= 0 x) (< x 16)))\n\
     (assert (< (int.pow2 x) x))\n\
     (check-sat)";

/// No `int.pow2`, and inside the bounded-int-blast route's reach. The control:
/// if this stopped certifying, the fix above would have disabled the route
/// rather than taught it to decline.
const BOUNDED_UNSAT: &str = "(set-logic QF_NIA)\n\
     (declare-fun a () Int)\n\
     (declare-fun b () Int)\n\
     (assert (and (<= 0 a) (< a 8)))\n\
     (assert (and (<= 0 b) (< b 8)))\n\
     (assert (= (* a b) 65))\n\
     (check-sat)";

fn evidence_of(text: &str) -> Evidence {
    let mut parsed = parse_script(text).expect("query parses");
    let assertions = parsed.assertions.clone();
    produce_evidence(&mut parsed.arena, &assertions, &SolverConfig::default())
        .expect("evidence production must not ERROR: a route that does not apply declines")
        .evidence
}

/// The regression: evidence production returns `unsat`, not an error.
#[test]
fn an_int_pow2_query_keeps_its_verdict_through_evidence_production() {
    let evidence = evidence_of(POW2_UNSAT);
    assert!(
        matches!(evidence, Evidence::Unsat(_)),
        "expected an unsat evidence report; got kind={}. An `int.pow2` query is \
         outside the integer bit-blaster, which is a reason to decline that route \
         and not a reason to lose the refutation",
        evidence.kind_label()
    );
}

/// The two front doors must agree. `solve` always decided this one; only
/// `produce_evidence` did not.
#[test]
fn solve_and_evidence_production_agree_on_the_verdict() {
    let solved = solve_smtlib(POW2_UNSAT, &SolverConfig::default()).expect("front door runs");
    assert!(
        matches!(solved.result, CheckResult::Unsat),
        "premise of this suite: the solver decides this query"
    );
    assert!(matches!(evidence_of(POW2_UNSAT), Evidence::Unsat(_)));
}

/// The gap is real and stays visible: this route has no certificate for
/// `int.pow2`, and the honest report is an UNCERTIFIED unsat. If this ever
/// becomes certified that is good news — assert it deliberately rather than
/// letting a silent upgrade go unnoticed.
#[test]
fn the_certificate_gap_is_reported_rather_than_papered_over() {
    let evidence = evidence_of(POW2_UNSAT);
    assert_eq!(
        evidence.kind_label(),
        "unsat-uncertified",
        "an `int.pow2` refutation carries no certificate through this route; if it \
         now does, update this test and say which route produced it"
    );
    assert!(!evidence.is_certified());
}

/// The control. Teaching the route to decline must not stop it certifying the
/// queries it was always for.
#[test]
fn a_bounded_int_query_without_pow2_still_certifies() {
    let evidence = evidence_of(BOUNDED_UNSAT);
    // The KIND, not merely `is_certified`: a dozen routes certify, so asserting
    // only certification would still pass if this query quietly fell through to
    // one of them — and then the control would no longer be watching the route
    // the fix touched.
    assert_eq!(
        evidence.kind_label(),
        "unsat-bounded-int-blast",
        "this control exists to show the fix taught the route to DECLINE rather \
         than disabled it, so it has to keep routing here"
    );
    assert!(
        evidence.is_certified(),
        "and it must still certify; without this, disabling the route entirely \
         would pass every other test in this file"
    );
}
