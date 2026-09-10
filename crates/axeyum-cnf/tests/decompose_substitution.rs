//! Roadmap item 2.1's exit criterion, and the three negative controls that make
//! it able to fail.
//!
//! > *A curated instance with `k` equivalence classes shrinks by the expected
//! > variable count; `DRAT` accepted; the pass runs under the 1.5 valve.*
//!
//! Every number below is **stated in advance** from the fixture's construction,
//! not read off the output. The curated instance is built by naming three
//! equivalence classes of known size, so "the expected variable count" is
//! arithmetic on those sizes:
//!
//! | class | members | variables it removes |
//! |---|---|---|
//! | A | `x0 ≡ x1 ≡ x2` | 2 |
//! | B | `x3 ≡ ¬x4` | 1 |
//! | C | `x5 ≡ x6 ≡ x7 ≡ x8` | 3 |
//!
//! `k = 3`, `sum(sizes) - k = 6`, and the instance has 12 variables, so the
//! reduced formula must occur over exactly `12 - 6 = 6`.
//!
//! # Why the negative controls are the load-bearing half
//!
//! "The pass eliminated 6 variables and the proof checked" is also what a pass
//! that eliminated the *wrong* 6 variables would report, if the checker could
//! not tell. So:
//!
//! * `no_equivalence_*` shows the pass declining to invent a substitution, and
//!   the valve declining to run it at all.
//! * `a_substitution_between_non_equivalent_literals_*` builds by hand the
//!   derivation the pass would emit **if its components were wrong**, and
//!   requires the checker to reject it *and* the wrongly-substituted formula to
//!   flip a verdict. That is the control that separates "the pass works" from
//!   "the pass does nothing and nothing notices".
//! * `a_component_holding_both_polarities_*` covers the one case that is not a
//!   substitution at all.

use axeyum_cnf::inprocess::{InprocessSchedule, TickValve, inprocess_scheduled};
use axeyum_cnf::ticks::{TickEffort, TickGrant, TickValveAccount};
use axeyum_cnf::{
    CnfClause, CnfFormula, CnfLit, CnfVar, DecomposeOptions, DratStep, InprocessObserver,
    OccurrencePass, ProofCoverage, ProofSolveOutcome, ReductionLink, SatResult, check_drat,
    check_drat_backward, compact, decompose, decompose_within_recorded, solve_with_drat_proof,
    solve_with_native_core,
};

/// An observer that funds **only** equivalent-literal substitution.
///
/// `RecordingObserver::granting` funds every pass, and on these fixtures an
/// unbudgeted BVE eliminates the whole formula — so a test using it would be
/// measuring BVE and reporting it as substitution. Isolating the pass is what
/// makes "the reduced formula has 6 variables" a statement about this pass.
#[derive(Debug, Default)]
struct DecomposeOnly {
    counts: Vec<(String, f64)>,
}

impl DecomposeOnly {
    /// The first value recorded under `name`.
    fn get(&self, name: &str) -> Option<f64> {
        self.counts
            .iter()
            .find(|(key, _)| key == name)
            .map(|(_, value)| *value)
    }

    /// Every value recorded under `name`, in order — the right reading for a
    /// valve held across several rounds, where the whole question is what
    /// changed between them.
    ///
    /// Returned as `i64`. Every counter this test file reads is a whole number
    /// (a count or a 0/1 flag), and comparing those as floats is both a lint and
    /// a real hazard: `== 1.0` is the wrong shape of assertion for a quantity
    /// that is never fractional.
    fn all(&self, name: &str) -> Vec<i64> {
        self.counts
            .iter()
            .filter(|(key, _)| key == name)
            .map(|(_, value)| {
                let rounded = value.round();
                assert!(
                    (rounded - value).abs() < 1e-9,
                    "counter {name} = {value} is not a whole number"
                );
                #[allow(clippy::cast_possible_truncation)]
                {
                    rounded as i64
                }
            })
            .collect()
    }
}

impl InprocessObserver for DecomposeOnly {
    fn grant(&mut self, _pass: OccurrencePass, _formula: &CnfFormula) -> Option<u64> {
        None
    }
    fn count(&mut self, name: &str, value: f64) {
        self.counts.push((name.to_owned(), value));
    }
    fn decompose_grant(&mut self, _formula: &CnfFormula) -> Option<u64> {
        Some(u64::MAX)
    }
}

/// The default-observer arm: every pass declined, including substitution, which
/// is what `decompose_grant`'s **default** body does. Wrapping `DecomposeOnly`
/// keeps one counter store.
#[derive(Debug, Default)]
struct NoDecompose(DecomposeOnly);

impl InprocessObserver for NoDecompose {
    fn grant(&mut self, _pass: OccurrencePass, _formula: &CnfFormula) -> Option<u64> {
        None
    }
    fn count(&mut self, name: &str, value: f64) {
        self.0.counts.push((name.to_owned(), value));
    }
    // `decompose_grant` deliberately not overridden: the default is the subject.
}

fn v(i: usize) -> CnfVar {
    CnfVar::new(i).expect("var")
}
fn p(i: usize) -> CnfLit {
    CnfLit::positive(v(i))
}
fn n(i: usize) -> CnfLit {
    CnfLit::positive(v(i)).negated()
}
fn formula(nvars: usize, clauses: &[&[CnfLit]]) -> CnfFormula {
    let mut f = CnfFormula::new(nvars);
    for c in clauses {
        f.add_clause(CnfClause::new(c.to_vec())).expect("in range");
    }
    f
}

/// Variables with at least one occurrence.
fn occurring(f: &CnfFormula) -> usize {
    let mut seen = vec![false; f.variable_count()];
    for clause in f.clauses() {
        for lit in clause.lits() {
            seen[lit.var().index()] = true;
        }
    }
    seen.iter().filter(|s| **s).count()
}

// ---------------------------------------------------------------------------
// The curated instance
// ---------------------------------------------------------------------------

/// `k = 3` equivalence classes of sizes 3, 2 and 4 over 12 variables.
///
/// The classes are written as implication **cycles**, which is the only thing
/// this pass reads: `x0 → x1 → x2 → x0` is `(¬x0 ∨ x1)`, `(¬x1 ∨ x2)`,
/// `(¬x2 ∨ x0)`. Class B is an *inverted* class (`x3 ≡ ¬x4`) so the fixture
/// exercises the polarity half of the representative rule and not only the
/// trivial one.
///
/// The payload clauses are all ternary and stay ternary after substitution, so
/// the count of what was removed is not confounded by clauses that collapsed for
/// some other reason.
const EXPECTED_CLASSES: usize = 3;
const EXPECTED_SUBSTITUTED: usize = 6;
const CURATED_VARIABLES: usize = 12;

fn curated() -> CnfFormula {
    formula(
        CURATED_VARIABLES,
        &[
            // class A: x0 → x1 → x2 → x0
            &[n(0), p(1)],
            &[n(1), p(2)],
            &[n(2), p(0)],
            // class B: x3 → ¬x4 → x3
            &[n(3), n(4)],
            &[p(4), p(3)],
            // class C: x5 → x6 → x7 → x8 → x5
            &[n(5), p(6)],
            &[n(6), p(7)],
            &[n(7), p(8)],
            &[n(8), p(5)],
            // payload, written through the non-representative members so the
            // substitution has something to rewrite
            &[p(0), p(5), p(9)],
            &[n(1), n(6), p(10)],
            &[p(2), n(7), p(11)],
            &[n(3), p(9), n(10)],
            &[p(4), p(10), p(11)],
            &[n(9), n(11), p(8)],
        ],
    )
}

#[test]
fn the_curated_instance_shrinks_by_the_expected_variable_count() {
    let f = curated();
    assert_eq!(occurring(&f), CURATED_VARIABLES, "every variable occurs");

    let out = decompose(&f);

    assert_eq!(out.stats.classes, EXPECTED_CLASSES);
    assert_eq!(out.stats.variables_substituted, EXPECTED_SUBSTITUTED);
    assert_eq!(
        out.equivalences.substituted_count(),
        EXPECTED_SUBSTITUTED,
        "the model lift must cover exactly the variables that left"
    );
    assert_eq!(
        occurring(&out.formula),
        CURATED_VARIABLES - EXPECTED_SUBSTITUTED,
        "the reduced formula must occur over 12 - 6 = 6 variables"
    );

    // The representatives are the minimum-variable member of each class, and the
    // inverted class keeps its polarity.
    assert_eq!(out.equivalences.representative(v(1)), Some(p(0)));
    assert_eq!(out.equivalences.representative(v(2)), Some(p(0)));
    assert_eq!(out.equivalences.representative(v(4)), Some(n(3)));
    assert_eq!(out.equivalences.representative(v(6)), Some(p(5)));
    assert_eq!(out.equivalences.representative(v(7)), Some(p(5)));
    assert_eq!(out.equivalences.representative(v(8)), Some(p(5)));
    for kept in [0usize, 3, 5, 9, 10, 11] {
        assert_eq!(
            out.equivalences.representative(v(kept)),
            None,
            "variable {kept} is a representative or free and must survive"
        );
    }

    // All nine equivalence binaries became tautologies and left. Four of the six
    // payload clauses were rewritten; the other two — `(x0 ∨ x5 ∨ x9)` and
    // `(¬x3 ∨ x9 ∨ ¬x10)` — name only representatives and free variables, so
    // they are carried through untouched and cost no proof step.
    assert_eq!(out.stats.clauses_removed, 9);
    assert_eq!(out.stats.clauses_rewritten, 4);
    assert_eq!(out.formula.clauses().len(), 6);

    // And `compact` turns "occurs over 6" into a `variable_count` of 6, which is
    // the number an admission gate reads.
    let (compacted, _) = compact(&out.formula);
    assert_eq!(compacted.variable_count(), 6);
}

#[test]
fn the_curated_instance_keeps_its_verdict_and_its_models() {
    let f = curated();
    let out = decompose(&f);

    // Every model of the reduced formula lifts to a model of the original, and
    // every model of the original already satisfies the reduced one. Together
    // that is exact equisatisfiability, checked by enumeration rather than
    // asserted.
    let width = f.variable_count();
    let mut reduced_models = 0usize;
    let mut original_models = 0usize;
    for mask in 0u32..(1 << width) {
        let a: Vec<bool> = (0..width).map(|i| mask >> i & 1 == 1).collect();
        let in_reduced = out.formula.evaluate(&a).expect("width");
        let in_original = f.evaluate(&a).expect("width");
        if in_reduced {
            reduced_models += 1;
            let lifted = out.equivalences.extend(&a);
            assert!(
                f.evaluate(&lifted).expect("width"),
                "reduced model {a:?} lifted to {lifted:?}, which the original rejects"
            );
        }
        if in_original {
            original_models += 1;
            assert!(
                in_reduced,
                "original model {a:?} does not satisfy the reduced formula"
            );
        }
    }
    assert!(original_models > 0, "the fixture must be satisfiable");
    assert!(reduced_models >= original_models);
    // Compare the VERDICT, not the model: two satisfiable formulas need not
    // agree on which model the core happens to find, and asserting on the
    // assignment would make this test fail for a reason it is not about.
    assert!(matches!(
        solve_with_native_core(&f).expect("solve"),
        SatResult::Sat(_)
    ));
    assert!(matches!(
        solve_with_native_core(&out.formula).expect("solve"),
        SatResult::Sat(_)
    ));
}

#[test]
fn the_curated_instance_derivation_is_accepted_by_both_drat_checkers() {
    let f = curated();
    let mut proof = Vec::new();
    let out = decompose_within_recorded(&f, DecomposeOptions::DEFAULT, Some(&mut proof));

    // 2 equivalence binaries per substituted variable, 1 delete per tautology,
    // and 2 steps per rewritten clause: 12 + 9 + 8 = 29. A clause the
    // substitution did not touch costs nothing.
    assert_eq!(out.stats.proof_steps, proof.len());
    assert_eq!(proof.len(), 2 * EXPECTED_SUBSTITUTED + 9 + 2 * 4);

    // `Ok(false)` is the correct answer for a satisfiable formula: every step
    // verified, and no step derived the empty clause. Only `Err` is a soundness
    // alarm.
    assert_eq!(check_drat(&f, &proof), Ok(false));
    assert_eq!(check_drat_backward(&f, &proof), Ok(false));

    // Every prefix verifies on its own, which is the ordering claim: each `Add`
    // is derivable from what precedes it, not merely from the final clause set.
    for cut in 1..=proof.len() {
        assert!(
            check_drat(&f, &proof[..cut]).is_ok(),
            "prefix of {cut} steps failed to verify"
        );
    }
}

// ---------------------------------------------------------------------------
// The proof obligation: an `unsat` under substitution, checked through the link
// ---------------------------------------------------------------------------

/// An unsatisfiable instance whose core is written through non-representative
/// members of two equivalence classes, so the substitution rewrites every clause
/// the refutation needs.
///
/// The core is all eight clauses over `(x0, x2, x4)`, which is unsatisfiable;
/// `x1 ≡ x0` and `x3 ≡ x2` let half of them be written with `x1`/`x3` instead.
/// Substitution therefore does real work on the exact clauses the search will
/// resolve, which is what makes the link a real test rather than a formality.
fn curated_unsat() -> CnfFormula {
    formula(
        5,
        &[
            &[n(0), p(1)],
            &[p(0), n(1)],
            &[n(2), p(3)],
            &[p(2), n(3)],
            &[p(0), p(2), p(4)],
            &[p(1), p(2), n(4)],
            &[p(0), n(3), p(4)],
            &[p(1), n(2), n(4)],
            &[n(0), p(3), p(4)],
            &[n(1), p(2), n(4)],
            &[n(0), n(3), p(4)],
            &[n(1), n(2), n(4)],
        ],
    )
}

#[test]
fn an_unsat_under_substitution_verifies_against_the_original_formula() {
    let original = curated_unsat();
    assert!(matches!(
        solve_with_native_core(&original).expect("solve"),
        SatResult::Unsat(_)
    ));

    let mut steps: Vec<DratStep> = Vec::new();
    let out = decompose_within_recorded(&original, DecomposeOptions::DEFAULT, Some(&mut steps));
    assert_eq!(out.stats.variables_substituted, 2);
    assert!(!out.stats.unsat, "substitution must not refute this one");

    let mut link = ReductionLink::identity();
    link.record(steps.iter().cloned());
    assert!(link.is_checkable());
    assert!(
        link.prefix_len() > 0,
        "the reduction must have derived steps"
    );

    // Compaction is what the shipping schedule does next, and it is the half
    // that makes the search's steps talk about different variables than the
    // prefix does.
    let (compacted, map) = compact(&out.formula);
    let new_to_old: Vec<usize> = (0..map.live_count()).map(|i| map.original_of(i)).collect();
    link.rename(&new_to_old);
    assert!(
        compacted.variable_count() < original.variable_count(),
        "the fixture must actually renumber, or the renaming is the identity \
         and this test checks nothing"
    );
    assert_eq!(compacted.variable_count(), 3);

    // Anti-vacuity: the prefix on its own must NOT refute the formula, or the
    // search's contribution is untested.
    assert_eq!(
        check_drat(&original, link.prefix()),
        Ok(false),
        "the reduction prefix alone must not derive the empty clause"
    );

    let ProofSolveOutcome::Unsat(search_proof) = solve_with_drat_proof(&compacted) else {
        panic!("the compacted formula must still be unsat");
    };
    assert!(!search_proof.is_empty(), "the search must contribute steps");

    let checked = link.check_unsat(&original, &compacted, &search_proof, usize::MAX);
    assert_eq!(
        checked.coverage,
        ProofCoverage::Original,
        "the certificate must cover the caller's formula, not the reduced one"
    );
    assert!(checked.verified, "checker error: {:?}", checked.error);
    assert_eq!(checked.prefix_steps, link.prefix_len());
    assert_eq!(checked.search_steps, search_proof.len());
}

#[test]
fn dropping_the_renaming_makes_the_same_certificate_fail() {
    // The vacuity guard on the test above: if the check passed with the
    // renaming removed, it would not be testing the renaming.
    let original = curated_unsat();
    let mut steps: Vec<DratStep> = Vec::new();
    let out = decompose_within_recorded(&original, DecomposeOptions::DEFAULT, Some(&mut steps));
    let mut link = ReductionLink::identity();
    link.record(steps.iter().cloned());
    let (compacted, _) = compact(&out.formula);
    // ... and deliberately do NOT call `link.rename`.
    let ProofSolveOutcome::Unsat(search_proof) = solve_with_drat_proof(&compacted) else {
        panic!("unsat");
    };
    let checked = link.check_unsat(&original, &compacted, &search_proof, usize::MAX);
    assert!(
        !checked.verified,
        "an unlifted search proof must not verify against the original: the \
         prefix names original variables and the search names compacted ones"
    );
}

// ---------------------------------------------------------------------------
// Negative control 1: nothing to substitute, and the valve declining
// ---------------------------------------------------------------------------

/// Binary clauses, but no implication cycle: a chain and a fork, so every
/// component is a singleton. The pass must eliminate nothing.
fn no_equivalence() -> CnfFormula {
    formula(
        6,
        &[
            &[n(0), p(1)],
            &[n(1), p(2)],
            &[n(2), p(3)],
            &[p(3), p(4)],
            &[p(0), p(4), p(5)],
            &[n(1), n(4), p(5)],
        ],
    )
}

#[test]
fn no_equivalence_means_nothing_eliminated_and_nothing_derived() {
    let f = no_equivalence();
    let mut proof = Vec::new();
    let out = decompose_within_recorded(&f, DecomposeOptions::DEFAULT, Some(&mut proof));

    assert!(out.stats.ran, "the pass did look: it built the graph");
    assert!(
        out.stats.binary_clauses > 0,
        "the fixture has edges to walk"
    );
    assert_eq!(out.stats.classes, 0);
    assert_eq!(out.stats.variables_substituted, 0);
    assert!(out.equivalences.is_identity());
    assert!(proof.is_empty(), "nothing to justify, so nothing emitted");
    assert_eq!(out.formula, f, "the formula must come back untouched");
    assert_eq!(occurring(&out.formula), 6);

    // And the cost is linear in the formula, not in the variable space: setup
    // (6 clauses + 6 variables) plus one charge per clause, per edge, per node
    // and per substitution candidate.
    assert!(
        out.stats.work_spent < 100,
        "a 6-clause no-equivalence run spent {} units",
        out.stats.work_spent
    );
}

#[test]
fn the_valve_refuses_the_pass_when_the_search_has_not_paid_for_it() {
    // `DECOMPOSE_EFFORT` is 10 % of the accrued window, refused below 1x the
    // clause count. With no search ticks at all the bootstrap reference (2e6)
    // applies, so a small formula is admitted; a formula with more clauses than
    // the allowance is refused.
    let mut admitted = TickValve::shipping(DecomposeOnly::default());
    let small = no_equivalence();
    let schedule = InprocessSchedule::OFF;
    admitted.round(|valve| inprocess_scheduled(&small, schedule, None, valve));
    assert_eq!(
        admitted.decompose_account().effort().per_mille,
        100,
        "the cheapest pass gets the largest slice"
    );
    assert_eq!(admitted.inner().get("decompose_admitted"), Some(1.0));
    assert_eq!(
        admitted.inner().get("decompose_tick_admitted"),
        Some(1.0),
        "control arm: the same fixture must be able to run, or 'refused' is \
         indistinguishable from 'the fixture cannot run at all'"
    );
    let ran_work = admitted
        .inner()
        .get("decompose_work_spent")
        .expect("an admitted pass reports its meter");
    assert!(ran_work > 0.0, "the admitted pass paid its setup");

    // Now the refusing arm: one tick of accrued window buys 0 allowance, and a
    // 6-clause formula demands 6.
    let mut refused = TickValve::shipping(DecomposeOnly::default());
    refused.advance_search_ticks(1);
    refused.round(|valve| inprocess_scheduled(&small, schedule, None, valve));
    assert_eq!(refused.inner().get("decompose_tick_admitted"), Some(0.0));
    assert_eq!(refused.inner().get("decompose_tick_threshold"), Some(6.0));
    // The discriminator between "refused" and "ran and found nothing" is the
    // meter, not the result: a pass that ran with a budget of zero would still
    // have paid its `O(|F|)` setup.
    assert_eq!(
        refused.inner().get("decompose_admitted"),
        Some(0.0),
        "a refusal must be a recorded zero, not a missing key"
    );
    // The discriminator between "refused" and "ran and found nothing" is the
    // meter: a pass that ran with a budget of zero would still have paid its
    // `O(|F|)` graph setup, so it would have reported one.
    assert_eq!(
        refused.inner().get("decompose_work_spent"),
        None,
        "a refused pass reports no meter at all, because it never built one"
    );
    let (granted, refused_rounds, backed_off) = refused.decompose_account().rounds();
    assert_eq!((granted, refused_rounds, backed_off), (0, 1, 0));
}

#[test]
fn a_pass_that_keeps_finding_nothing_is_offered_exponentially_less_often() {
    // The back-off half of the 1.5 valve, on a fixture that genuinely has no
    // equivalence to find.
    let f = no_equivalence();
    let schedule = InprocessSchedule::OFF;
    let mut valve = TickValve::shipping(DecomposeOnly::default());
    for round in 0..8u64 {
        valve.advance_search_ticks((round + 1) * 10_000_000);
        valve.round(|v| inprocess_scheduled(&f, schedule, None, v));
    }
    let (granted, refused, backed_off) = valve.decompose_account().rounds();
    assert_eq!(granted + refused + backed_off, 8, "one decision per round");
    assert!(
        backed_off > 0,
        "a pass that found nothing eight times must have been backed off: \
         granted={granted} refused={refused}"
    );
    assert!(
        granted < 8,
        "the valve admitted every one of the 8 rounds: the back-off is inert"
    );
    assert!(
        valve.decompose_account().backoff().run_length() > 1,
        "the skip run must double on each fruitless round"
    );
    // The counter stream is the ordered record, and it must agree.
    let admitted = valve.inner().all("decompose_tick_admitted");
    assert_eq!(admitted.len(), 8);
    assert_eq!(
        admitted.iter().filter(|v| **v == 1).count(),
        usize::try_from(granted).expect("fits")
    );
}

#[test]
fn the_valve_admits_the_curated_instance_and_the_pass_reports_through_it() {
    let f = curated();
    let schedule = InprocessSchedule {
        recording: true,
        ..InprocessSchedule::OFF
    };
    let mut valve = TickValve::shipping(DecomposeOnly::default());
    let out = valve.round(|v| inprocess_scheduled(&f, schedule, None, v));

    assert_eq!(valve.inner().get("decompose_tick_admitted"), Some(1.0));
    assert_eq!(
        valve.inner().all("decompose_variables_substituted"),
        vec![i64::try_from(EXPECTED_SUBSTITUTED).expect("fits")]
    );
    assert_eq!(
        valve.inner().all("decompose_classes"),
        vec![i64::try_from(EXPECTED_CLASSES).expect("fits")]
    );
    // A productive round clears the back-off rather than arming it.
    assert_eq!(valve.decompose_account().backoff().rounds_left(), 0);

    // The schedule's own product: a compacted formula over 6 variables, a
    // recorded prefix, and a model lift that covers the substituted variables.
    assert_eq!(out.formula.variable_count(), 6);
    assert!(out.link.prefix_len() > 0);
    assert!(out.link.is_checkable());
    assert!(!out.equivalences.is_identity());
    assert!(!out.decompose_unsat);

    // `lift_model` composes all three lifts. A model of the compacted formula
    // must replay against the caller's formula through it.
    let SatResult::Sat(model) = solve_with_native_core(&out.formula).expect("solve") else {
        panic!("the reduced formula is satisfiable");
    };
    let lifted = out.lift_model(model.values());
    assert!(
        f.evaluate(&lifted).expect("width"),
        "lifted model {lifted:?} does not satisfy the original"
    );
}

#[test]
fn an_observer_that_does_not_override_the_grant_never_runs_the_pass() {
    // The whole safety story for every existing caller: `decompose_grant`'s
    // DEFAULT body returns `None`, so a formula full of equivalences comes back
    // untouched from an observer that has not opted in. `NoDecompose` is exactly
    // such an observer — it implements the trait and leaves that method alone.
    let f = curated();
    let mut declining = NoDecompose::default();
    let out = inprocess_scheduled(&f, InprocessSchedule::OFF, None, &mut declining);
    assert_eq!(declining.0.get("decompose_admitted"), Some(0.0));
    assert!(out.equivalences.is_identity());
    assert!(!out.decompose_unsat);
    assert_eq!(occurring(&out.formula), CURATED_VARIABLES);
    assert_eq!(out.formula.clauses().len(), f.clauses().len());

    // The control arm: the same fixture, the same schedule, an observer that
    // DOES override it. Without this, "nothing happened" would be
    // indistinguishable from "this schedule cannot substitute anything".
    let mut granting = DecomposeOnly::default();
    let out = inprocess_scheduled(&f, InprocessSchedule::OFF, None, &mut granting);
    assert_eq!(granting.get("decompose_admitted"), Some(1.0));
    assert_eq!(
        occurring(&out.formula),
        CURATED_VARIABLES - EXPECTED_SUBSTITUTED
    );
}

// ---------------------------------------------------------------------------
// Negative control 2: a substitution between literals that are NOT equivalent
// ---------------------------------------------------------------------------

/// `(x0 ∨ x1) ∧ (¬x0 ∨ ¬x1)` — satisfiable, and `x1` is equivalent to `¬x0`,
/// **not** to `x0`.
fn anti_equivalent() -> CnfFormula {
    formula(2, &[&[p(0), p(1)], &[n(0), n(1)]])
}

#[test]
fn a_substitution_between_non_equivalent_literals_flips_the_verdict_and_fails_drat() {
    let f = anti_equivalent();
    assert!(matches!(
        solve_with_native_core(&f).expect("solve"),
        SatResult::Sat(_)
    ));

    // What the pass actually does: it finds `x1 ≡ ¬x0`, and the verdict holds.
    let mut honest_proof = Vec::new();
    let honest = decompose_within_recorded(&f, DecomposeOptions::DEFAULT, Some(&mut honest_proof));
    assert_eq!(honest.equivalences.representative(v(1)), Some(n(0)));
    assert_eq!(check_drat(&f, &honest_proof), Ok(false));
    assert!(matches!(
        solve_with_native_core(&honest.formula).expect("solve"),
        SatResult::Sat(_)
    ));

    // What a pass with a wrong component would do: merge `x1` into `x0`. Build
    // exactly the derivation this module emits, with the wrong representative.
    let wrong_proof = vec![
        DratStep::Add(vec![n(1), p(0)]),
        DratStep::Add(vec![p(1), n(0)]),
        DratStep::Add(vec![p(0)]),
        DratStep::Delete(vec![p(0), p(1)]),
        DratStep::Add(vec![n(0)]),
        DratStep::Delete(vec![n(0), n(1)]),
    ];
    let verdict = check_drat(&f, &wrong_proof);
    assert!(
        verdict.is_err(),
        "the checker accepted a substitution between non-equivalent literals: \
         {verdict:?}"
    );
    // The backward checker only verifies steps in the empty clause's dependency
    // cone, so a proof that derives nothing gives it nothing to reject. Close
    // the derivation the way the wrongly substituted formula would — it really
    // is refutable once the bad merge is believed — and the backward checker
    // rejects it too.
    assert_eq!(
        check_drat_backward(&f, &wrong_proof),
        Ok(false),
        "backward checking of a non-refuting proof is vacuous by construction; \
         it is the closed proof below that must be rejected"
    );
    let mut closed = wrong_proof.clone();
    closed.push(DratStep::Add(Vec::new()));
    assert!(
        check_drat_backward(&f, &closed).is_err(),
        "the backward checker accepted a refutation built on a substitution \
         between non-equivalent literals"
    );

    // ...and the wrongly substituted formula really does say something else, so
    // the checker is the only thing standing between the bug and a wrong
    // verdict.
    let wrongly_substituted = formula(2, &[&[p(0)], &[n(0)]]);
    assert!(matches!(
        solve_with_native_core(&wrongly_substituted).expect("solve"),
        SatResult::Unsat(_)
    ));
}

// ---------------------------------------------------------------------------
// Negative control 3: a component holding both polarities of one variable
// ---------------------------------------------------------------------------

#[test]
fn a_component_holding_both_polarities_reports_unsat_with_a_checkable_proof() {
    // x0 → x1 → ¬x0 and ¬x0 → ¬x1 → x0: one component holds x0 and ¬x0.
    let f = formula(
        3,
        &[
            &[n(0), p(1)],
            &[n(1), n(0)],
            &[p(0), n(1)],
            &[p(1), p(0)],
            &[p(2), p(0)],
        ],
    );
    assert!(matches!(
        solve_with_native_core(&f).expect("solve"),
        SatResult::Unsat(_)
    ));

    let mut proof = Vec::new();
    let out = decompose_within_recorded(&f, DecomposeOptions::DEFAULT, Some(&mut proof));
    assert!(out.stats.unsat);
    assert_eq!(out.stats.variables_substituted, 0);
    assert_eq!(
        out.formula, f,
        "the input comes back unchanged: the refutation is in the proof"
    );

    assert_eq!(proof.len(), 3);
    assert_eq!(proof[2], DratStep::Add(Vec::new()));
    // `Ok(true)`: the steps verified AND derived the empty clause. This is a
    // complete refutation of the caller's formula on its own.
    assert_eq!(check_drat(&f, &proof), Ok(true));
    assert_eq!(check_drat_backward(&f, &proof), Ok(true));
}

#[test]
fn the_schedule_surfaces_a_substitution_refutation_through_the_link() {
    let f = formula(
        3,
        &[
            &[n(0), p(1)],
            &[n(1), n(0)],
            &[p(0), n(1)],
            &[p(1), p(0)],
            &[p(2), p(0)],
        ],
    );
    let schedule = InprocessSchedule {
        recording: true,
        ..InprocessSchedule::OFF
    };
    let mut valve = TickValve::shipping(DecomposeOnly::default());
    let out = valve.round(|v| inprocess_scheduled(&f, schedule, None, v));

    assert!(out.decompose_unsat);
    assert_eq!(valve.inner().get("decompose_unsat"), Some(1.0));
    assert!(out.link.is_checkable());
    // The prefix alone refutes the caller's formula, with no search steps at
    // all — the strongest form the link's own contract can take.
    let checked = out.link.check_unsat(&f, &out.formula, &[], usize::MAX);
    assert_eq!(checked.coverage, ProofCoverage::Original);
    assert!(checked.verified, "checker error: {:?}", checked.error);
    assert_eq!(checked.search_steps, 0);
}

// ---------------------------------------------------------------------------
// Determinism
// ---------------------------------------------------------------------------

#[test]
fn the_pass_is_a_function_of_the_formula_and_the_options() {
    let f = curated();
    let mut first = Vec::new();
    let a = decompose_within_recorded(&f, DecomposeOptions::DEFAULT, Some(&mut first));
    let mut second = Vec::new();
    let b = decompose_within_recorded(&f, DecomposeOptions::DEFAULT, Some(&mut second));
    assert_eq!(a.formula, b.formula);
    assert_eq!(a.equivalences, b.equivalences);
    assert_eq!(a.stats, b.stats);
    assert_eq!(
        first, second,
        "the derivation must be step-for-step identical"
    );
}

#[test]
fn a_tighter_round_cap_can_only_substitute_less_never_differently() {
    let f = curated();
    let all = decompose(&f);
    let one = decompose_within_recorded(
        &f,
        DecomposeOptions {
            max_rounds: 1,
            ..DecomposeOptions::DEFAULT
        },
        None,
    );
    assert!(one.stats.variables_substituted <= all.stats.variables_substituted);
    for var in 0..f.variable_count() {
        if let Some(lit) = one.equivalences.representative(v(var)) {
            assert_eq!(
                all.equivalences.representative(v(var)),
                Some(lit),
                "variable {var} was substituted differently under a tighter cap"
            );
        }
    }
}

#[test]
fn a_grant_below_the_setup_cost_declines_rather_than_substituting_partially() {
    let f = curated();
    let mut proof = Vec::new();
    let out = decompose_within_recorded(
        &f,
        DecomposeOptions {
            work_budget: Some(1),
            ..DecomposeOptions::DEFAULT
        },
        Some(&mut proof),
    );
    assert!(!out.stats.ran);
    assert!(out.stats.work_exhausted);
    assert_eq!(out.stats.variables_substituted, 0);
    assert!(proof.is_empty());
    assert_eq!(out.formula, f);
}

#[test]
fn the_ungated_effort_is_a_real_control_arm_and_the_gated_one_is_not_vacuous() {
    // Pairing rule from the 1.5 suite: a test that shows a gate refusing needs a
    // second arm showing the same input running.
    let f = no_equivalence();
    let clauses = f.clauses().len() as u64;
    let gated = TickEffort {
        per_mille: 100,
        threshold_per_clause: 1,
        ..TickEffort::MAJOR_PASS
    };
    let mut gated_account = TickValveAccount::new(gated);
    let mut ungated_account = TickValveAccount::new(TickEffort::UNGATED);
    // One accrued tick: 10 % of 1 is 0, which is below a threshold of 6.
    assert!(matches!(
        gated_account.request(1, clauses),
        TickGrant::Refused { .. }
    ));
    assert!(matches!(
        ungated_account.request(1, clauses),
        TickGrant::Granted { .. }
    ));
}
