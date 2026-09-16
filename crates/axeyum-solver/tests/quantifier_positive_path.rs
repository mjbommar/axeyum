//! Quantifier activation by assignment: tracking a POSITIVE POSITION through
//! `not`, `=>` and the branches of an `ite` when registering a nested universal
//! (ADR-2120, `AXEYUM_QINST_POSITIVE_PATH` / [`PositivePathLevelGuard`]).
//!
//! **What the mechanism is.** A universal under a disjunction is not a unit
//! fact. `A ∨ (∀y. B(y))` does not entail `B(t)`, so the matched tuple cannot
//! become a bare instance — and today it is discarded outright, which
//! [ADR-2113] measured at 100.0 % of 2,139,815 rejections on `UFLIA`. Both
//! reference solvers instead emit a CLAUSE that carries the quantifier's own
//! literal: z3 builds `¬q ∨ body[x:=t]` and prepends `¬q` into the same clause
//! (`qi_queue.cpp:274-289`); cvc5 builds `(=> q body)` and lets its CNF stream
//! produce the identical clause (`instantiate.cpp:293`). We reach the same
//! clause from the other side: `positive_instance_formula` replaces the
//! universal inside its owner, so for `A ∨ ∀y.B(y)` the conclusion is
//! `A ∨ B(t)` — the residual context `A` IS the activation literal, carried in
//! the term, and the ground solver's own search is the assignment that
//! discharges it. Backtracking retracts nothing because there is nothing to
//! retract: the clause is valid.
//!
//! **Soundness is the monotone-replacement lemma and these tests do not
//! establish it — they try to REFUTE it.** At a POSITIVE position, replacing a
//! subformula by anything it entails cannot strengthen the whole; `∀y.B ⊨ B(t)`
//! for every ground `t`. So the adversarial fixtures below are SATISFIABLE
//! queries whose universal sits under exactly the connectives level 1 newly
//! tracks. If the widened rule could manufacture a refutation, this is where it
//! would appear.
//!
//! **The one that matters most is `SAT_OTHER_DISJUNCT_TRUE`.** Its universal is
//! false at the witness, and its owner is satisfied by the OTHER disjunct. A
//! mechanism that admitted the bare instance instead of the clause — the exact
//! defect the `rej_nocontext` drop exists to prevent — refutes it. So does one
//! whose polarity bookkeeping is wrong by a single flip.
//!
//! [ADR-2113]: `docs/research/09-decisions/adr-2113-uflia-the-instance-we-never-produce.md`

#![cfg(feature = "full")]

use std::time::Duration;

use axeyum_ir::{Sort, TermArena};
use axeyum_smtlib::parse_script;
use axeyum_solver::{
    CheckResult, PositivePathLevelGuard, SolverConfig, prove_quantified_unsat_via_egraph,
    solve_smtlib,
};

/// Level 0 is the shipped arm; level 1 is what ADR-2120 measures. Both are
/// exercised everywhere below, because a fixture run only at the arm under test
/// cannot show that the shipped arm still agrees.
const LEVELS: [usize; 2] = [0, 1];

fn config() -> SolverConfig {
    SolverConfig {
        timeout: Some(Duration::from_secs(10)),
        ..SolverConfig::default()
    }
}

/// The E-matching refutation loop alone, so a verdict is attributable to the
/// registration rule rather than to one of the front door's other routes.
fn ematch(text: &str) -> CheckResult {
    let mut script = parse_script(text).expect("parses");
    prove_quantified_unsat_via_egraph(&mut script.arena, &script.assertions, &config())
        .expect("no solver error")
}

// ---------------------------------------------------------------------------
// SOUNDNESS-NEGATIVE. A satisfiable query must not be refuted at any level.
// ---------------------------------------------------------------------------

/// **THE fixture this lane's mutation control aims at.**
///
/// `p` is true, so `(or p (forall ((y U)) (q y)))` is satisfied by its FIRST
/// disjunct and says nothing whatever about `q`. `(not (q w))` is therefore
/// consistent with it, and the query is SAT.
///
/// It is refuted the moment the engine admits the bare instance `q(w)` rather
/// than the clause `p ∨ q(w)`. That is exactly the inference
/// `rej_nocontext` exists to prevent, and exactly what a widened registration
/// rule would get wrong if it handed the tuple on without going through
/// `positive_instance_formula`. The witness `w` is a declared constant so the
/// trigger `q(y)` has something ground to match — a fixture whose trigger never
/// fires would pass by never running the inference under test.
const SAT_OTHER_DISJUNCT_TRUE: &str = r"
    (set-logic UF)
    (declare-sort U 0)
    (declare-fun q (U) Bool)
    (declare-const w U)
    (declare-const p Bool)
    (assert p)
    (assert (or p (forall ((y U)) (q y))))
    (assert (not (q w)))
    (check-sat)
";

/// The same shape reached through `=>` — a step level 0 refuses and level 1
/// tracks, with the antecedent flipping and the consequent keeping polarity.
///
/// `(=> r (or s (forall ((y U)) (q y))))` with `r` FALSE says nothing about
/// `q`, so `(not (q w))` is consistent and the query is SAT. Admitting `q(w)`
/// bare refutes it.
const SAT_UNDER_IMPLIES: &str = r"
    (set-logic UF)
    (declare-sort U 0)
    (declare-fun q (U) Bool)
    (declare-const w U)
    (declare-const r Bool)
    (declare-const s Bool)
    (assert (not r))
    (assert (=> r (or s (forall ((y U)) (q y)))))
    (assert (not (q w)))
    (check-sat)
";

/// **The polarity control.** The universal sits under a `not`, so it is at a
/// NEGATIVE position: `¬(∀y. q(y))` is an EXISTENTIAL, and replacing it by
/// `¬q(w)` would STRENGTHEN the owner rather than weaken it. A rule that
/// tracked the step but not the flip admits that replacement, and it is
/// unsound — here it would let the engine conclude `¬q(w)`, contradicting the
/// asserted `q(w)` and refuting a SAT query.
const SAT_UNDER_NOT: &str = r"
    (set-logic UF)
    (declare-sort U 0)
    (declare-fun q (U) Bool)
    (declare-const w U)
    (declare-const t Bool)
    (assert (or t (not (forall ((y U)) (q y)))))
    (assert (q w))
    (check-sat)
";

/// The arithmetic shape — the `UFLIA` one this lane sized — so the GROUND
/// closure is exercised and not only the congruence closure. `c < 0` puts the
/// goal outside the universal's own guard, and the outer disjunct `g` is true,
/// so the query is SAT twice over.
const SAT_UFLIA_SPLIT: &str = r"
    (set-logic UFLIA)
    (declare-fun p (Int) Int)
    (declare-const c Int)
    (declare-const g Bool)
    (assert g)
    (assert (or g (forall ((i Int)) (=> (>= i 0) (= (p i) 0)))))
    (assert (< c 0))
    (assert (not (= (p c) 0)))
    (check-sat)
";

/// The `ite` CONDITION, which is refused at EVERY level because it occurs at
/// both polarities in `ite(c,t,e) ≡ (c ∧ t) ∨ (¬c ∧ e)`. Nothing here may be
/// replaced, and the query is SAT.
const SAT_UNDER_ITE_CONDITION: &str = r"
    (set-logic UF)
    (declare-sort U 0)
    (declare-fun q (U) Bool)
    (declare-const w U)
    (declare-const u Bool)
    (declare-const v Bool)
    (assert u)
    (assert v)
    (assert (ite (forall ((y U)) (q y)) u v))
    (assert (not (q w)))
    (check-sat)
";

const SAT_FIXTURES: [(&str, &str); 5] = [
    ("SAT_OTHER_DISJUNCT_TRUE", SAT_OTHER_DISJUNCT_TRUE),
    ("SAT_UNDER_IMPLIES", SAT_UNDER_IMPLIES),
    ("SAT_UNDER_NOT", SAT_UNDER_NOT),
    ("SAT_UFLIA_SPLIT", SAT_UFLIA_SPLIT),
    ("SAT_UNDER_ITE_CONDITION", SAT_UNDER_ITE_CONDITION),
];

#[test]
fn a_satisfiable_query_is_not_refuted_at_any_level() {
    for level in LEVELS {
        for (name, text) in SAT_FIXTURES {
            let _guard = PositivePathLevelGuard::set(level);
            let verdict = ematch(text);
            assert!(
                !matches!(verdict, CheckResult::Unsat),
                "{name} at level {level}: a SATISFIABLE query was refuted -- a \
                 positive replacement may only add a formula the owner entails, \
                 so an `unsat` here is an unsound replacement (a bare instance \
                 where the clause was required, or a polarity flip missed), \
                 never a legitimate refutation"
            );
        }
    }
}

#[test]
fn the_front_door_also_refuses_the_satisfiable_queries_at_a_raised_level() {
    // The loop alone is the attributable instrument; the front door is what
    // ships. A lever tested only through the isolated route is a lever whose
    // shipped path has no soundness test. `solve_smtlib`, not `check_auto`:
    // the latter is the quantifier-FREE dispatch and would come back
    // `Unsupported` on every one of these, which `assert!(!unsat)` would have
    // swallowed as a pass.
    //
    // This runs on THIS thread, which is what makes the guard apply at all --
    // see `the_positive_path_guard_does_not_cross_a_thread_boundary`.
    for level in LEVELS {
        for (name, text) in SAT_FIXTURES {
            let _guard = PositivePathLevelGuard::set(level);
            let outcome = solve_smtlib(text, &config()).expect("no solver error");
            assert!(
                !matches!(outcome.result, CheckResult::Unsat),
                "front door, {name} at level {level}: a SATISFIABLE query was refuted"
            );
        }
    }
}

// ---------------------------------------------------------------------------
// POSITIVE. The refutations the shipped arm already finds must survive, and the
// widened arm must not lose one.
// ---------------------------------------------------------------------------

/// A plain unit universal with a contradicting ground fact: nothing about this
/// depends on the positive-path rule, so BOTH arms must refute it. This is the
/// no-loss direction, and it is also the check that the suite's instrument
/// works at all — every other test here asserts a NON-refutation, and a
/// harness that refuted nothing would pass all of them.
const UNSAT_UNIT: &str = r"
    (set-logic UF)
    (declare-sort U 0)
    (declare-fun q (U) Bool)
    (declare-const w U)
    (assert (forall ((y U)) (q y)))
    (assert (not (q w)))
    (check-sat)
";

/// The shape the lane is built for, made UNSAT: the other disjunct is FALSE, so
/// the owner forces the universal and `q(w)` follows. The clause `¬p ∨ q(w)`
/// plus `¬p` propagates `q(w)`, which contradicts `¬q(w)`.
///
/// This is the fixture that says the mechanism DOES something: it is the same
/// shape as `SAT_OTHER_DISJUNCT_TRUE` with one polarity changed.
const UNSAT_OTHER_DISJUNCT_FALSE: &str = r"
    (set-logic UF)
    (declare-sort U 0)
    (declare-fun q (U) Bool)
    (declare-const w U)
    (declare-const p Bool)
    (assert (not p))
    (assert (or p (forall ((y U)) (q y))))
    (assert (not (q w)))
    (check-sat)
";

#[test]
fn a_refutation_the_shipped_level_finds_survives_the_raised_level() {
    // The no-loss direction, stated as a comparison rather than as an absolute:
    // whatever level 0 refutes, level 1 must refute too. Asserting `Unsat`
    // outright would make this test a claim about the engine's strength on a
    // particular day; asserting the IMPLICATION makes it a claim about the
    // lever, which is what the lever is responsible for.
    for (name, text) in [
        ("UNSAT_UNIT", UNSAT_UNIT),
        ("UNSAT_OTHER_DISJUNCT_FALSE", UNSAT_OTHER_DISJUNCT_FALSE),
    ] {
        let shipped = {
            let _guard = PositivePathLevelGuard::set(0);
            ematch(text)
        };
        let raised = {
            let _guard = PositivePathLevelGuard::set(1);
            ematch(text)
        };
        if matches!(shipped, CheckResult::Unsat) {
            assert!(
                matches!(raised, CheckResult::Unsat),
                "{name}: level 0 refutes and level 1 does not -- the widened \
                 rule may only ADD registrations, so it cannot remove a \
                 refutation"
            );
        }
    }
}

/// The instrument's own non-vacuity: at least one fixture in this file really
/// is refuted, so the `!matches!(.., Unsat)` assertions above are asserting
/// something a working engine could fail.
#[test]
fn the_unsat_control_is_actually_refuted() {
    let verdict = ematch(UNSAT_UNIT);
    assert!(
        matches!(verdict, CheckResult::Unsat),
        "UNSAT_UNIT was not refuted: every soundness-negative assertion in this \
         file is then vacuous, because a harness that refutes nothing passes \
         all of them"
    );
}

// ---------------------------------------------------------------------------
// The lever's own contract.
// ---------------------------------------------------------------------------

/// The guard is a THREAD-LOCAL, so it is inert on any thread but the one that
/// set it — and `AXEYUM_QINST_POSITIVE_PATH` is not.
///
/// This is pinned rather than commented because the shipped consumer,
/// `smtcomp_cli`, runs the solve on a **watchdog worker thread**. An A/B that
/// set the guard and measured through a worker would read the SHIPPED arm on
/// both sides and publish a null that no value of the lever could have moved.
/// The A/B therefore uses the environment variable, and this test is what says
/// why it must.
#[test]
fn the_positive_path_guard_does_not_cross_a_thread_boundary() {
    let outer = PositivePathLevelGuard::set(1);
    let inside_worker = std::thread::spawn(|| {
        // No guard is set on THIS thread -- that absence is the whole point.
        registrations_with_context(SAT_UNDER_IMPLIES)
    })
    .join()
    .expect("worker finished");
    drop(outer);

    let shipped = registrations_with_context(SAT_UNDER_IMPLIES);
    assert_eq!(
        inside_worker, shipped,
        "the worker thread saw a level the guard set on another thread: an A/B \
         driven through `smtcomp_cli`'s watchdog worker would then be measuring \
         the guard, not the environment variable"
    );

    let _raised = PositivePathLevelGuard::set(1);
    let here = registrations_with_context(SAT_UNDER_IMPLIES);
    assert!(
        here > shipped,
        "the guard does not change the registration count ON ITS OWN THREAD \
         either, so this test could not have distinguished the two arms and its \
         equality above proves nothing (shipped {shipped}, raised {here})"
    );
}

/// How many nested universals of `text` get a `PositiveContext` at the level in
/// force on this thread.
///
/// This is the observable the lever moves, read through the public API rather
/// than reconstructed: `witness_tuples_via_egraph` would not do, because a
/// registration without a context is matched and then dropped, so its tuples
/// are indistinguishable from a registration that never fired.
fn registrations_with_context(text: &str) -> usize {
    let mut script = parse_script(text).expect("parses");
    axeyum_solver::positive_context_registrations(&mut script.arena, &script.assertions)
}

#[test]
fn the_level_guard_restores_the_previous_setting() {
    let before = registrations_with_context(SAT_UNDER_IMPLIES);
    {
        let _guard = PositivePathLevelGuard::set(1);
        assert!(
            registrations_with_context(SAT_UNDER_IMPLIES) > before,
            "the guard did not take effect, so its restoration cannot be observed"
        );
    }
    assert_eq!(
        registrations_with_context(SAT_UNDER_IMPLIES),
        before,
        "the guard leaked past its own lifetime"
    );
}

#[test]
fn the_registration_set_is_deterministic_across_runs() {
    // Determinism is a public API promise. The walk is indexed by argument
    // POSITION, so this is a check that nothing on the path reads a hash map's
    // iteration order.
    for level in LEVELS {
        let _guard = PositivePathLevelGuard::set(level);
        let first = registrations_with_context(SAT_UFLIA_SPLIT);
        for run in 1..4 {
            assert_eq!(
                registrations_with_context(SAT_UFLIA_SPLIT),
                first,
                "level {level}, run {run}: the registration count moved between \
                 identical runs"
            );
        }
    }
}

/// A body with nothing for the widened rule to reach must behave identically at
/// both levels — the OFF-path equivalence check. Without it, "level 1 finds
/// more" is consistent with "level 1 finds more EVERYWHERE", which would make
/// the shipped arm unreachable rather than preserved.
#[test]
fn a_shape_the_widening_does_not_reach_is_identical_at_both_levels() {
    for text in [UNSAT_UNIT, SAT_OTHER_DISJUNCT_TRUE] {
        let shipped = {
            let _guard = PositivePathLevelGuard::set(0);
            registrations_with_context(text)
        };
        let raised = {
            let _guard = PositivePathLevelGuard::set(1);
            registrations_with_context(text)
        };
        assert_eq!(
            shipped, raised,
            "a shape whose path is `and`/`or` only (or has no nested universal \
             at all) registered differently at the two levels"
        );
    }
}

/// The certificate must exist, not merely be possible.
///
/// ADR-2120 §3 found that a positive replacement was pushed into the ground set
/// with NO derivation recorded, so `collect_ground_derivations` declined at its
/// `derivations.get(&term)?` and every `unsat` downstream of one shipped
/// uncertified. This test asks the checker directly: a replacement certificate
/// built from the fixture must be accepted, and the same certificate with its
/// conclusion replaced by an unrelated term must be REFUSED.
#[test]
fn a_positive_replacement_certificate_is_checked_and_a_wrong_one_is_refused() {
    use axeyum_solver::{
        QuantifierGroundDerivation, QuantifierPositiveReplacementCertificate,
        check_quantifier_ground_derivation,
    };

    let mut arena = TermArena::new();
    let carrier = arena.declare_uninterpreted_sort("PprS");
    let sort = Sort::Uninterpreted(carrier);
    let predicate = arena.declare_fun("ppr_q", &[sort], Sort::Bool).unwrap();
    let binder = arena.declare("ppr_y", sort).unwrap();
    let bound = arena.var(binder);
    let q_y = arena.apply(predicate, &[bound]).unwrap();
    let universal = arena.forall(binder, q_y).unwrap();
    let side = arena.declare("ppr_p", Sort::Bool).unwrap();
    let side_var = arena.var(side);
    let owner = arena.or(side_var, universal).unwrap();
    let witness = arena.declare("ppr_w", sort).unwrap();
    let witness_term = arena.var(witness);
    let q_w = arena.apply(predicate, &[witness_term]).unwrap();
    let conclusion = arena.or(side_var, q_w).unwrap();

    let good = QuantifierGroundDerivation::PositiveReplacement(Box::new(
        QuantifierPositiveReplacementCertificate {
            owner,
            path: vec![1],
            vars: vec![binder],
            bindings: vec![witness_term],
            conclusion,
            owner_derivation: None,
        },
    ));
    assert!(
        check_quantifier_ground_derivation(&mut arena, &[owner], &good),
        "the checker refused a correct positive replacement: `p or forall y. q(y)` \
         does entail `p or q(w)`"
    );

    // Same certificate, wrong conclusion. The checker re-derives from
    // `(owner, path, vars, bindings)` alone, so this must fail on the
    // comparison rather than on anything the producer told it.
    let wrong = QuantifierGroundDerivation::PositiveReplacement(Box::new(
        QuantifierPositiveReplacementCertificate {
            owner,
            path: vec![1],
            vars: vec![binder],
            bindings: vec![witness_term],
            conclusion: q_w,
            owner_derivation: None,
        },
    ));
    assert!(
        !check_quantifier_ground_derivation(&mut arena, &[owner], &wrong),
        "the checker ACCEPTED the BARE instance `q(w)` as the conclusion of a \
         replacement into `p or forall y. q(y)`. That is precisely the unsound \
         inference `rej_nocontext` exists to prevent"
    );

    // And an owner that is not an assertion and carries no derivation must be
    // refused: `None` is a claim that the owner is asserted, never permission
    // to skip the check.
    assert!(
        !check_quantifier_ground_derivation(&mut arena, &[conclusion], &good),
        "the checker accepted a replacement whose owner is neither an assertion \
         nor carried by an `owner_derivation`"
    );
}

// ---------------------------------------------------------------------------
// THE CONVERSION. A test that only ever asserts "nothing was refuted" is passed
// by an engine that refutes nothing, so the suite has to show the mechanism
// DOING something as well as not doing the wrong thing.
// ---------------------------------------------------------------------------

/// Level 1 refutes `UNSAT_OTHER_DISJUNCT_FALSE`; level 0 returns `unknown`.
///
/// This is the whole lane in one assertion. The query's ONLY universal is
/// nested, so the shipped arm never starts the instantiation loop at all —
/// `partition_top_level_foralls` finds nothing and the refusal "no universal is
/// asserted; the nested quantifiers present are registered, not instantiated"
/// is returned before any registration is compiled. At level 1 the loop runs on
/// the registrations, the positive replacement turns the matched tuple into the
/// CLAUSE `p ∨ q(w)`, the ground solver has `¬p` and `¬q(w)`, and the
/// refutation follows.
///
/// The pair with `SAT_OTHER_DISJUNCT_TRUE` is what makes both halves load
/// bearing: the two fixtures differ in ONE polarity — `p` against `¬p` — and
/// the engine must separate them. A mechanism that admitted the bare instance
/// `q(w)` would refute BOTH, and this test alone would still pass.
#[test]
fn the_widened_level_converts_a_refutation_the_shipped_level_cannot_reach() {
    let shipped = {
        let _guard = PositivePathLevelGuard::set(0);
        ematch(UNSAT_OTHER_DISJUNCT_FALSE)
    };
    let raised = {
        let _guard = PositivePathLevelGuard::set(1);
        ematch(UNSAT_OTHER_DISJUNCT_FALSE)
    };
    assert!(
        !matches!(shipped, CheckResult::Unsat),
        "the SHIPPED level already refutes this, so the conversion this test \
         exists to pin does not exist and every `level 1 is better` claim in \
         ADR-2120 is measuring something else"
    );
    assert!(
        matches!(raised, CheckResult::Unsat),
        "level 1 did not refute `p or forall y. q(y)` with `not p` and \
         `not q(w)` -- the activation mechanism is not reaching the \
         registration, so every soundness-negative test in this file is \
         vacuous: it is passing because nothing runs"
    );
}

/// And the refutation is CERTIFIED, not merely reached.
///
/// ADR-2120 §3: before this lane a positive replacement was pushed into the
/// ground set with no derivation recorded, so `collect_ground_derivations`
/// declined at its `derivations.get(&term)?` and the `unsat` shipped with no
/// evidence behind it. Widening the rule without closing that would have turned
/// a path taken on 3 files into one taken on 97. This asks for the derivations
/// and requires that they exist and that at least one is the new variant.
#[test]
fn the_converted_refutation_carries_its_replacement_derivation() {
    use axeyum_solver::{
        QuantifierGroundDerivation, prove_quantified_unsat_via_egraph_with_instances,
    };

    let _guard = PositivePathLevelGuard::set(1);
    let mut script = parse_script(UNSAT_OTHER_DISJUNCT_FALSE).expect("parses");
    let mut certificate = None;
    let verdict = prove_quantified_unsat_via_egraph_with_instances(
        &mut script.arena,
        &script.assertions,
        &config(),
        &mut certificate,
    )
    .expect("no solver error");
    assert!(
        matches!(verdict, CheckResult::Unsat),
        "the fixture was not refuted, so this test cannot say anything about \
         its certificate"
    );
    let derivations = certificate.expect(
        "the refutation carried NO derivations: `collect_ground_derivations` \
         declined, which is exactly the uncertified path ADR-2120 closed",
    );
    assert!(
        derivations.iter().any(|derivation| matches!(
            derivation,
            QuantifierGroundDerivation::PositiveReplacement(_)
        )),
        "the certificate carries derivations but not one positive replacement, \
         so the refutation did not come through the mechanism under test: \
         {derivations:?}"
    );
}
