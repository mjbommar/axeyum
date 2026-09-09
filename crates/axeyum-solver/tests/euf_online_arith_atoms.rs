//! `euf-online`'s Boolean-skeleton admission: the policy, its soundness gate,
//! and the shape the dispatcher's own normalization creates.
//!
//! # What this suite is about
//!
//! Measured 2026-09-08 on
//! `QF_UFLIA/mathsat/EufLaArithmetic/medium/medium9.smt2`: `euf-online` run
//! **alone** answers `unsat` in 2 ms, and through the front door the SAME route
//! is reached and declines in 1.3 ms with *"boolean skeleton outside the online
//! CDCL(T) encoder"*. The route was never un-admitted; its Tseitin encoder had
//! no arm for an arithmetic comparison at Boolean position and gave up on the
//! whole query.
//!
//! **`check_auto_dispatch`'s own first statement is what puts the atom there.**
//! `lift_arith_ite` hoists each Int/Real `ite(c, a, b)` into `¬c ∨ t=a` /
//! `c ∨ t=b`. In the source file the condition `(< (+ x y) 9)` occurs ONLY as an
//! `ite` condition buried inside a congruence term, where this encoder never
//! looks at it. The lift moves it to Boolean position. Every fixture below is
//! written in the LIFTED form, which is what the route actually receives.
//!
//! # The three things a test here has to be able to fail on
//!
//! 1. **The arms must differ.** `Refuse` reproduces the historical decline and
//!    `AbstractSliced` decides. A suite that only asserted "the new arm decides"
//!    would still pass if the policy were ignored and the encoder always
//!    abstracted.
//! 2. **The abstraction must not manufacture a verdict.** Abstracting an atom
//!    only ADDS models, so `unsat` transfers and `sat` does not — the
//!    soundness-negative fixture is an arithmetically-unsatisfiable query whose
//!    abstraction is trivially satisfiable, and the route must NOT say `sat`
//!    (nor, since it cannot see the arithmetic, `unsat`).
//! 3. **A query needing no abstraction must be untouched.** Pure `QF_UF` keeps
//!    the caller's whole budget and the same verdict under every arm.
#![cfg(feature = "full")]

use std::time::Duration;

use axeyum_smtlib::{ScriptCommand, parse_script};
use axeyum_solver::{
    CheckResult, EufOnlineAtomPolicy, EufOnlineAtomPolicyGuard, EufOnlineAtomStatsGuard,
    SolverConfig, check_qf_uf_online_cdclt, last_euf_online_atom_stats,
};

/// Runs `euf-online` on `text` under `policy`, exactly as the dispatcher does
/// (one route, the parsed flat assertion view, a finite budget).
fn euf_online(text: &str, policy: EufOnlineAtomPolicy) -> CheckResult {
    let _guard = EufOnlineAtomPolicyGuard::set(policy);
    let mut script = parse_script(text).expect("parse");
    let assertions: Vec<axeyum_ir::TermId> = script
        .commands
        .iter()
        .filter_map(|command| match command {
            ScriptCommand::Assert(term) => Some(*term),
            _ => None,
        })
        .collect();
    let config = SolverConfig {
        timeout: Some(Duration::from_secs(10)),
        ..SolverConfig::default()
    };
    check_qf_uf_online_cdclt(&mut script.arena, &assertions, &config)
}

/// `medium9`'s refutation in miniature, already in the form `lift_arith_ite`
/// produces: a congruence contradiction (`f(1)` is both `5` and `6`, and the two
/// literals are distinct) sitting beside the two lifted `ite` clauses whose
/// guard `(< (+ p q) 9)` is an ARITHMETIC atom at Boolean position.
///
/// The congruence half alone decides this. That is the whole point: the encoder
/// used to throw away a refutation it already had because of an atom that
/// contributes nothing to it.
const LIFTED_ITE_UNSAT: &str = "\
(set-logic QF_UFLIA)
(declare-fun f (Int) Int)
(declare-fun p () Int)
(declare-fun q () Int)
(declare-fun t () Int)
(assert (= (f 1) 5))
(assert (= (f 1) 6))
(assert (or (not (< (+ p q) 9)) (= t (+ p q))))
(assert (or (< (+ p q) 9) (= t 2)))
(check-sat)
";

/// The SOUNDNESS-NEGATIVE fixture. `(< z 0)` and `(< 5 z)` are two DISTINCT
/// terms, so the abstraction gives them two independent variables and the
/// skeleton `p ∧ q` is satisfiable — while the query itself is unsatisfiable
/// over the integers. The route must therefore say neither `sat` (it has no
/// model of the original: the candidate cannot replay) nor `unsat` (it cannot
/// see the arithmetic that refutes it).
///
/// The `f` application keeps the query inside this route's fragment; without an
/// equality atom the route returns before it encodes anything and the fixture
/// would be vacuous.
const ABSTRACTION_IS_SATISFIABLE_QUERY_IS_NOT: &str = "\
(set-logic QF_UFLIA)
(declare-fun f (Int) Int)
(declare-fun z () Int)
(assert (= (f z) (f z)))
(assert (< z 0))
(assert (< 5 z))
(check-sat)
";

/// Pure `QF_UF`: nothing here is outside the encoder, so the policy has no
/// occasion to act and every arm must agree.
const PURE_UF_UNSAT: &str = "\
(set-logic QF_UF)
(declare-sort U 0)
(declare-fun g (U) U)
(declare-fun a () U)
(declare-fun b () U)
(assert (= a b))
(assert (not (= (g a) (g b))))
(check-sat)
";

/// THE REGRESSION. Under the historical arm this query is refused; under the
/// shipped arm it is decided. Both halves are asserted in one test so a policy
/// that silently stopped being consulted fails here rather than passing on the
/// half that still holds.
#[test]
fn lifted_arith_ite_is_refused_by_the_historical_arm_and_decided_by_the_default() {
    match euf_online(LIFTED_ITE_UNSAT, EufOnlineAtomPolicy::Refuse) {
        CheckResult::Unknown(reason) => assert!(
            reason.detail.contains("boolean skeleton outside"),
            "the Refuse arm must decline for the ENCODER reason, not some other \
             one; got: {}",
            reason.detail
        ),
        other => panic!(
            "the Refuse arm must reproduce the historical decline, got {other:?}; \
             if this now decides, the policy is no longer consulted"
        ),
    }
    match euf_online(LIFTED_ITE_UNSAT, EufOnlineAtomPolicy::AbstractSliced) {
        CheckResult::Unsat => {}
        other => panic!(
            "the shipped arm must decide the congruence refutation the lifted \
             arithmetic atom used to hide, got {other:?}"
        ),
    }
}

/// SOUNDNESS-NEGATIVE. The abstraction is satisfiable and the query is not, so
/// the only two acceptable answers are "unknown" — never `sat`, and never the
/// `unsat` it has no evidence for.
#[test]
fn abstraction_never_reports_a_verdict_it_cannot_justify() {
    for policy in [
        EufOnlineAtomPolicy::AbstractSliced,
        EufOnlineAtomPolicy::AbstractWholeBudget,
    ] {
        match euf_online(ABSTRACTION_IS_SATISFIABLE_QUERY_IS_NOT, policy) {
            CheckResult::Unknown(_) => {}
            CheckResult::Sat(_) => panic!(
                "WRONG-SAT under {}: the skeleton is satisfiable only because two \
                 arithmetic atoms were abstracted to independent variables; the \
                 replay gate must reject it",
                policy.name()
            ),
            CheckResult::Unsat => panic!(
                "WRONG-UNSAT under {}: the abstraction weakens the query, so no \
                 refutation of it can come from arithmetic this route cannot see",
                policy.name()
            ),
        }
    }
}

/// A query with nothing to abstract must be byte-identical across the arms.
/// This is what makes the change safe for `QF_UF`, and it is the control that
/// separates "the abstraction fires where it should" from "the abstraction
/// fires everywhere".
#[test]
fn a_query_with_nothing_to_abstract_is_unchanged_by_the_policy() {
    for policy in [
        EufOnlineAtomPolicy::Refuse,
        EufOnlineAtomPolicy::AbstractSliced,
        EufOnlineAtomPolicy::AbstractWholeBudget,
    ] {
        match euf_online(PURE_UF_UNSAT, policy) {
            CheckResult::Unsat => {}
            other => panic!(
                "pure QF_UF must be unaffected by the arithmetic-atom policy; \
                 arm {} gave {other:?}",
                policy.name()
            ),
        }
    }
}

/// The counters have to distinguish the FOUR states a reader cares about —
/// never entered / entered and abstracted nothing / entered and abstracted /
/// entered and gave up — because the decline string alone distinguished none of
/// them, and that is why this took a division-sized measurement to find.
///
/// The `refused` half is not decoration: the first version of this instrument
/// recorded only on the path that finished encoding, so the arm that REFUSES —
/// the one the instrument exists to expose — reported an all-zero line. This
/// test is what found that.
#[test]
fn the_counters_separate_abstracted_from_refused_from_merely_entered() {
    let abstracted = {
        let _stats = EufOnlineAtomStatsGuard::enable();
        let _ = euf_online(LIFTED_ITE_UNSAT, EufOnlineAtomPolicy::AbstractSliced);
        last_euf_online_atom_stats()
    };
    assert_eq!(abstracted.entered, 1, "the route was entered exactly once");
    assert_eq!(
        abstracted.abstracted_queries, 1,
        "the lifted arithmetic guard is exactly what must be abstracted"
    );
    assert!(
        abstracted.abstracted_atoms >= 1,
        "at least the `(< (+ p q) 9)` guard, got {}",
        abstracted.abstracted_atoms
    );
    assert_eq!(
        abstracted.refused, 0,
        "the shipped arm encoded this query; nothing was refused"
    );
    assert_eq!(abstracted.policy, "sliced");

    let untouched = {
        let _stats = EufOnlineAtomStatsGuard::enable();
        let _ = euf_online(PURE_UF_UNSAT, EufOnlineAtomPolicy::AbstractSliced);
        last_euf_online_atom_stats()
    };
    assert_eq!(untouched.entered, 1);
    assert_eq!(
        untouched.abstracted_queries, 0,
        "a pure QF_UF query has nothing outside the encoder, so a nonzero count \
         here means the abstraction fires where it is not needed"
    );
    assert_eq!(untouched.abstracted_atoms, 0);

    let refused = {
        let _stats = EufOnlineAtomStatsGuard::enable();
        let _ = euf_online(LIFTED_ITE_UNSAT, EufOnlineAtomPolicy::Refuse);
        last_euf_online_atom_stats()
    };
    assert_eq!(
        refused.abstracted_queries, 0,
        "the Refuse arm abstracts nothing by construction"
    );
    assert_eq!(
        refused.entered, 1,
        "a refusal is an ENTRY: the route was reached and threw the query away, \
         which is the finding this instrument exists to make visible"
    );
    assert_eq!(
        refused.refused, 1,
        "the refusal must be COUNTED, not merely returned"
    );
    assert_eq!(refused.policy, "refuse");
}
