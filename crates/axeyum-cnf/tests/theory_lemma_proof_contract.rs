//! The CDCL(T) proof contract, pinned at the checker boundary (ADR-1704).
//!
//! The native core's identity ([ADR-0012], [ADR-1703]) is that every learned
//! clause is RUP against the CNF, so the learned sequence *is* a DRAT proof and
//! `check_drat` / `check_lrat` make `unsat` sound regardless of search bugs.
//! **A theory lemma is not RUP against the CNF.** ADR-1704 therefore forbids
//! slice S7 from learning a theory lemma into the RUP stream unlabelled, and
//! requires the two-stream artifact instead: the Boolean DRAT/LRAT stream is
//! checked over the CNF *extended by the enumerated theory lemmas as additional
//! input clauses*, and the lemma list is carried, counted, and discharged
//! separately by the per-theory checkers.
//!
//! This file is the falsifiable half of that ADR. It is not a test of the
//! checkers' internals; it is the contract's boundary written down as an
//! executable assertion, so that a future change which quietly learns a theory
//! lemma into the RUP stream cannot land green.
//!
//! # The fixture
//!
//! Three Boolean variables abstract three difference-logic atoms:
//!
//! ```text
//!   x1 == (a - b <= 0)      x2 == (b - c <= 0)      x3 == (c - a <= -1)
//! ```
//!
//! The Boolean skeleton asserts all three: `(x1) & (x2) & (x3)`. That skeleton
//! is **satisfiable** — propositionally there is nothing wrong with asserting
//! three unrelated atoms. Only the *theory* refutes it: the three atoms form a
//! negative cycle (`0 + 0 + -1 < 0`), so the theory emits the lemma
//!
//! ```text
//!   (~x1 | ~x2 | ~x3)
//! ```
//!
//! which is exactly the shape `DlTheory` would hand a driver as a conflict
//! clause. The lemma's *justification* is the negative cycle, an object no
//! propositional checker can see or reconstruct. Everything below follows from
//! that one fact.
//!
//! [ADR-0012]: ../../../docs/research/09-decisions/adr-0012-proof-producing-sat-core.md
//! [ADR-1703]: ../../../docs/research/09-decisions/adr-1703-the-native-core-is-the-sat-engine-batsat-is-demoted-to-a-differential-oracle.md

use axeyum_cnf::{
    CnfClause, CnfFormula, CnfLit, CnfVar, DratError, DratStep, LratError, LratStep, check_drat,
    check_lrat,
};

/// DIMACS-style literal: `1` is `x1`, `-1` is `~x1`.
fn lit(value: i64) -> CnfLit {
    let var = CnfVar::new(usize::try_from(value.unsigned_abs() - 1).unwrap()).unwrap();
    if value < 0 {
        CnfLit::positive(var).negated()
    } else {
        CnfLit::positive(var)
    }
}

fn formula(variable_count: usize, clauses: &[&[i64]]) -> CnfFormula {
    let mut f = CnfFormula::new(variable_count);
    for clause in clauses {
        f.add_clause(CnfClause::new(clause.iter().copied().map(lit).collect()))
            .unwrap();
    }
    f
}

/// The Boolean skeleton alone: three asserted atoms, no propositional conflict.
fn skeleton() -> CnfFormula {
    formula(3, &[&[1], &[2], &[3]])
}

/// The theory lemma the difference-logic solver would emit for the negative
/// cycle: at least one of the three atoms must be false.
fn theory_lemma() -> Vec<CnfLit> {
    vec![lit(-1), lit(-2), lit(-3)]
}

/// The skeleton **extended by the theory lemma as an additional input clause** —
/// the artifact ADR-1704 requires a CDCL(T) `unsat` to present to the checker.
/// The lemma is clause id 4 for LRAT purposes.
fn skeleton_plus_lemma() -> CnfFormula {
    formula(3, &[&[1], &[2], &[3], &[-1, -2, -3]])
}

// ---------------------------------------------------------------------------
// Ground truth about the fixture. If these drift, every assertion below is
// measuring something other than what its name says.
// ---------------------------------------------------------------------------

/// The skeleton is satisfiable, so the lemma is genuinely *not* a propositional
/// consequence of it. Without this, "the checker rejects the lemma" could be
/// true for an uninteresting reason.
#[test]
fn the_boolean_skeleton_alone_is_satisfiable() {
    let f = skeleton();
    assert!(
        f.evaluate(&[true, true, true]).unwrap(),
        "x1=x2=x3=true satisfies the skeleton; only the theory refutes it"
    );
}

// ---------------------------------------------------------------------------
// (a) A theory lemma presented as a DERIVED step is REJECTED.
// ---------------------------------------------------------------------------

/// The lemma on its own is neither RUP nor RAT against the skeleton, so a DRAT
/// proof that simply adds it is rejected at that step. This is ADR-1704's
/// premise, checked rather than asserted in prose.
#[test]
fn drat_rejects_the_theory_lemma_as_a_derived_addition() {
    let f = skeleton();
    let proof = vec![DratStep::Add(theory_lemma())];
    assert_eq!(
        check_drat(&f, &proof),
        Err(DratError::StepNotVerified { step: 0 }),
        "a theory lemma is not RUP (nor RAT) against the CNF"
    );
}

/// The whole refutation, written the way S7 must NOT write it: the theory lemma
/// learned into the RUP stream as if the Boolean core had derived it, followed
/// by the empty clause. The checker declines at the lemma.
#[test]
fn drat_rejects_a_refutation_that_learns_the_theory_lemma_unlabelled() {
    let f = skeleton();
    let proof = vec![DratStep::Add(theory_lemma()), DratStep::Add(Vec::new())];
    assert_eq!(
        check_drat(&f, &proof),
        Err(DratError::StepNotVerified { step: 0 }),
        "the refutation-modulo-theory does not check as a plain DRAT refutation"
    );
}

/// The LRAT half. There is no hint chain that justifies the lemma, because no
/// chain exists; supplying none is the honest encoding of "the theory said so".
#[test]
fn lrat_rejects_the_theory_lemma_as_a_derived_addition() {
    let f = skeleton();
    let proof = vec![
        LratStep::Add {
            id: 4,
            clause: theory_lemma(),
            hints: Vec::new(),
        },
        LratStep::Add {
            id: 5,
            clause: Vec::new(),
            hints: vec![1, 2, 3, 4],
        },
    ];
    assert_eq!(
        check_lrat(&f, &proof),
        Err(LratError::StepNotVerified { id: 4 }),
        "no antecedent chain over the CNF justifies a theory lemma"
    );
}

// ---------------------------------------------------------------------------
// (b) The SAME refutation is ACCEPTED when the lemma is an INPUT clause.
// ---------------------------------------------------------------------------

/// ADR-1704's accepting composition, Boolean half: the lemma is enumerated as an
/// additional input clause and the Boolean stream is checked over the extended
/// formula. The empty clause is then RUP and `check_drat` accepts.
///
/// What this establishes is exactly "the extended CNF is unsatisfiable" — the
/// refutation is *modulo* the enumerated lemmas, and the lemmas themselves are
/// discharged elsewhere, by the theory checkers, or counted as unchecked.
#[test]
fn drat_accepts_the_refutation_when_the_lemma_is_an_input_clause() {
    let f = skeleton_plus_lemma();
    let proof = vec![DratStep::Add(Vec::new())];
    assert_eq!(
        check_drat(&f, &proof),
        Ok(true),
        "the empty clause is RUP against CNF + theory lemmas"
    );
}

/// The LRAT half of the accepting composition. The lemma is formula clause 4, so
/// the empty clause's hint chain can name it like any other input clause.
#[test]
fn lrat_accepts_the_refutation_when_the_lemma_is_an_input_clause() {
    let f = skeleton_plus_lemma();
    let proof = vec![LratStep::Add {
        id: 5,
        clause: Vec::new(),
        hints: vec![1, 2, 3, 4],
    }];
    assert_eq!(
        check_lrat(&f, &proof),
        Ok(true),
        "hints 1,2,3 propagate x1,x2,x3; hint 4 (the lemma) is the conflict"
    );
}

// ---------------------------------------------------------------------------
// Mutation checks. Each of the two assertions above is shown to FAIL when
// inverted, so neither can pass for a reason unrelated to its subject.
// ---------------------------------------------------------------------------

/// Inversion of (a): the checkers are not simply refusing every addition over
/// this skeleton. A clause that genuinely *is* RUP against it is accepted by the
/// same call, so the rejections above are about the theory lemma specifically.
#[test]
fn control_drat_accepts_a_genuinely_rup_addition_over_the_same_skeleton() {
    let f = skeleton();
    // (x1 | ~x2): negating it forces x1 false, which the unit clause (x1)
    // immediately contradicts. RUP, and nothing to do with any theory.
    let proof = vec![DratStep::Add(vec![lit(1), lit(-2)])];
    assert_eq!(
        check_drat(&f, &proof),
        Ok(false),
        "a real RUP addition verifies; only the theory lemma does not"
    );
}

/// Inversion of (a) for LRAT: the same shape with a real hint chain is accepted,
/// so `StepNotVerified` above is not what this checker says to everything.
#[test]
fn control_lrat_accepts_a_genuinely_hinted_addition_over_the_same_skeleton() {
    let f = skeleton();
    let proof = vec![LratStep::Add {
        id: 4,
        clause: vec![lit(1), lit(-2)],
        hints: vec![1],
    }];
    assert_eq!(
        check_lrat(&f, &proof),
        Ok(false),
        "hint 1 (the unit x1) conflicts with the negated clause; verified, but no empty clause"
    );
}

/// Inversion of (b), DRAT: delete the lemma from the input and the accepted
/// proof stops checking. The acceptance above is carried entirely by the lemma
/// being present as an input clause — which is why ADR-1704 makes the lemma list
/// part of the artifact and counts it.
#[test]
fn control_removing_the_lemma_from_the_input_breaks_the_accepted_drat_proof() {
    let f = skeleton();
    let proof = vec![DratStep::Add(Vec::new())];
    assert_eq!(
        check_drat(&f, &proof),
        Err(DratError::StepNotVerified { step: 0 }),
        "without the lemma among the input clauses the empty clause is not RUP"
    );
}

/// Inversion of (b), LRAT: the same proof over the un-extended formula names a
/// clause id that does not exist, and is declined.
#[test]
fn control_removing_the_lemma_from_the_input_breaks_the_accepted_lrat_proof() {
    let f = skeleton();
    let proof = vec![LratStep::Add {
        id: 5,
        clause: Vec::new(),
        hints: vec![1, 2, 3, 4],
    }];
    assert_eq!(
        check_lrat(&f, &proof),
        Err(LratError::UnknownClause { id: 4 }),
        "hint 4 is the lemma; without it in the input there is no such clause"
    );
}

// ---------------------------------------------------------------------------
// The metric ADR-1704 requires: the lemma count is readable off the artifact.
// ---------------------------------------------------------------------------

/// The two-stream artifact's assumption count is a plain arithmetic fact about
/// the two formulas, not a field a producer can assert. This pins the definition
/// used by the ADR: `theory_lemma_count = |extended CNF| - |Boolean CNF|`, and
/// it is nonzero exactly when the refutation is modulo a theory.
#[test]
fn the_theory_lemma_count_is_read_off_the_artifact_not_asserted() {
    let boolean = skeleton();
    let extended = skeleton_plus_lemma();
    let lemma_count = extended.clauses().len() - boolean.clauses().len();
    assert_eq!(lemma_count, 1, "one enumerated theory lemma");
    assert!(
        lemma_count > 0,
        "a nonzero count is what forbids naming this artifact a pure DRAT refutation"
    );
    // Every extra clause is a lemma, and each one is a clause the Boolean CNF
    // does not contain: the count cannot be inflated or hidden by reordering.
    assert!(
        extended.clauses()[..boolean.clauses().len()] == boolean.clauses()[..],
        "the extended CNF is the Boolean CNF followed by the enumerated lemmas"
    );
}
