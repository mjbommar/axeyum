//! Differential test: the file-backed backward checker against the in-memory
//! one, and both against the reference forward checker (ADR-0426).
//!
//! `check_drat_backward_reader` is trusted-path code. It exists to make a check
//! fit in memory, and the only thing that makes that worth having is that it
//! reaches the *same* verdict as the checker it replaces. A file-backed checker
//! that accepts a proof the in-memory one rejects — or the reverse — would be a
//! P0, so this file was written before the optimisation it guards.
//!
//! What is compared, on every input:
//!
//! 1. `check_drat_backward(&formula, &parse_drat(text))` — the in-memory route.
//! 2. `check_drat_backward_reader(&formula, Cursor::new(text))` — the
//!    file-backed route.
//! 3. `check_drat` — the reference forward checker, where it is expected to
//!    agree. It is *deliberately* not required to agree everywhere: a backward
//!    checker accepts a proof whose refutation is valid but which carries
//!    unjustified dead weight, and that difference is the documented contract of
//!    both this module and `drat-trim`. Where the forward checker's verdict is
//!    asserted, it is asserted for both backward routes identically, so any
//!    divergence still shows up.
//!
//! The generators deliberately produce broken proofs as well as valid ones. A
//! differential test that only ever feeds two checkers valid input agrees on
//! everything and tests nothing — the hard-won lesson recorded in this
//! campaign's action items is that a control chosen carelessly passes while
//! testing nothing.

use std::fmt::Write as _;
use std::io::Cursor;

use axeyum_cnf::{
    CnfClause, CnfFormula, CnfLit, CnfVar, DratError, DratStep, ProofSolveOutcome, check_drat,
    check_drat_backward, check_drat_backward_reader, parse_drat, solve_with_drat_proof, write_drat,
};

fn lit(value: i64) -> CnfLit {
    let var = CnfVar::new(usize::try_from(value.unsigned_abs() - 1).expect("nonzero literal"))
        .expect("variable index fits");
    if value < 0 {
        CnfLit::positive(var).negated()
    } else {
        CnfLit::positive(var)
    }
}

fn formula(variable_count: usize, clauses: &[&[i64]]) -> CnfFormula {
    let mut f = CnfFormula::new(variable_count);
    for clause in clauses {
        f.add_clause(CnfClause::new(clause.iter().map(|&v| lit(v)).collect()))
            .expect("clause is over the formula's variables");
    }
    f
}

/// Runs both backward routes over the same proof text and asserts they agree
/// exactly — verdict for verdict, error for error, failing step for failing
/// step. Returns the shared result.
///
/// The in-memory route is fed the *parsed* text rather than the original step
/// vector, so both routes see literally the same bytes: a divergence can only
/// come from the checkers, never from two different proofs.
#[track_caller]
fn agree(f: &CnfFormula, text: &str) -> Result<bool, DratError> {
    let steps = parse_drat(text).expect("test proofs parse");
    let in_memory = check_drat_backward(f, &steps);
    let file_backed = check_drat_backward_reader(f, Cursor::new(text.as_bytes()));
    assert_eq!(
        in_memory, file_backed,
        "in-memory and file-backed backward checkers disagree on:\n{text}"
    );
    in_memory
}

/// A tiny deterministic PRNG. Explicit seeds, no external dependency, and the
/// same sequence on every run and every platform — determinism is a public API
/// promise of this workspace and a fuzz that cannot be replayed is not evidence.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }

    fn below(&mut self, bound: usize) -> usize {
        usize::try_from(self.next() % bound as u64).expect("bound fits")
    }
}

// ---------------------------------------------------------------------------
// Fixed shapes
// ---------------------------------------------------------------------------

#[test]
fn empty_proof_agrees() {
    let f = formula(1, &[&[1]]);
    assert_eq!(agree(&f, ""), Ok(false));
}

#[test]
fn proof_without_an_empty_clause_agrees() {
    let f = formula(2, &[&[1, 2], &[1, -2]]);
    assert_eq!(agree(&f, "1 0\n"), Ok(false));
}

#[test]
fn unit_contradiction_agrees() {
    let f = formula(1, &[&[1], &[-1]]);
    assert_eq!(agree(&f, "0\n"), Ok(true));
}

#[test]
fn four_clause_contradiction_agrees() {
    let f = formula(2, &[&[1, 2], &[1, -2], &[-1, 2], &[-1, -2]]);
    assert_eq!(agree(&f, "1 0\n0\n"), Ok(true));
}

#[test]
fn an_unjustified_step_fails_identically_on_both_routes() {
    let f = formula(2, &[&[1, 2], &[1, -2]]);
    // `-1` is not RUP over the formula and its pivot `-1` has no complement in
    // any clause to resolve against, so it is not RAT either.
    let outcome = agree(&f, "-1 0\n0 0\n");
    assert!(matches!(outcome, Err(DratError::StepNotVerified { .. })));
}

#[test]
fn a_truncated_proof_fails_identically_on_both_routes() {
    let f = formula(2, &[&[1, 2], &[1, -2], &[-1, 2], &[-1, -2]]);
    // The intermediate lemma `1` is missing, so the empty clause is not RUP.
    assert!(matches!(
        agree(&f, "0\n"),
        Err(DratError::StepNotVerified { .. })
    ));
}

#[test]
fn deletions_are_matched_identically() {
    let f = formula(2, &[&[1, 2], &[1, -2], &[-1, 2], &[-1, -2]]);
    // A deletion given in a different literal order, and one that matches
    // nothing at all (which both checkers ignore).
    assert_eq!(agree(&f, "1 0\nd 2 1 0\nd 1 2 0\nd 7 0\n0 0\n"), Ok(true));
}

#[test]
fn a_repeated_clause_is_deleted_once_per_deletion() {
    // Two identical clauses; deleting once must leave one live, so the
    // refutation still stands. This is the path where the deletion index has to
    // hold several records under one key.
    let f = formula(2, &[&[1, 2], &[1, 2], &[1, -2], &[-1, 2], &[-1, -2]]);
    assert_eq!(agree(&f, "1 0\nd 1 2 0\n0\n"), Ok(true));
}

#[test]
fn a_clause_with_repeated_literals_is_keyed_by_its_set() {
    // `1 1 2` and `2 1` have the same literal *set*, which is what a deletion
    // matches on, and the reference checker deduplicates the same way.
    let f = formula(2, &[&[1, 1, 2], &[1, -2], &[-1, 2], &[-1, -2]]);
    assert_eq!(agree(&f, "1 0\nd 2 1 0\n0\n"), Ok(true));
}

#[test]
fn comments_and_blank_lines_agree() {
    let f = formula(2, &[&[1, 2], &[1, -2], &[-1, 2], &[-1, -2]]);
    assert_eq!(agree(&f, "c header\n\n1 0\nc mid\n0\n\n"), Ok(true));
}

#[test]
fn steps_after_the_empty_clause_are_ignored_identically() {
    let f = formula(2, &[&[1, 2], &[1, -2], &[-1, 2], &[-1, -2]]);
    // The file-backed route stops reading at the empty clause; the in-memory
    // route truncates the slice there. Trailing garbage must change neither.
    assert_eq!(agree(&f, "1 0\n0\n-1 0\nd 99 0\n"), Ok(true));
}

#[test]
fn a_proof_over_variables_the_formula_does_not_have_agrees() {
    // The plan sizes its vectors by the widest variable *the proof* mentions,
    // which the streaming builder has to accumulate as it goes rather than in a
    // pre-pass.
    let f = formula(2, &[&[1, 2], &[1, -2], &[-1, 2], &[-1, -2]]);
    assert_eq!(agree(&f, "1 5 0\nd 1 5 0\n1 0\n0\n"), Ok(true));
}

// ---------------------------------------------------------------------------
// Real proofs from the workspace's own solver
// ---------------------------------------------------------------------------

/// Pigeonhole `PHP(n+1, n)`: unsatisfiable, and hard enough that the proof has
/// real structure (deletions, long clauses, a deep core).
fn pigeonhole(holes: usize) -> CnfFormula {
    let pigeons = holes + 1;
    let variable = |pigeon: usize, hole: usize| -> i64 {
        i64::try_from(pigeon * holes + hole + 1).expect("pigeonhole variable fits")
    };
    let mut clauses: Vec<Vec<i64>> = Vec::new();
    for pigeon in 0..pigeons {
        clauses.push((0..holes).map(|hole| variable(pigeon, hole)).collect());
    }
    for hole in 0..holes {
        for a in 0..pigeons {
            for b in (a + 1)..pigeons {
                clauses.push(vec![-variable(a, hole), -variable(b, hole)]);
            }
        }
    }
    let mut f = CnfFormula::new(pigeons * holes);
    for clause in &clauses {
        f.add_clause(CnfClause::new(clause.iter().map(|&v| lit(v)).collect()))
            .expect("clause is over the formula's variables");
    }
    f
}

#[test]
fn solver_produced_pigeonhole_proofs_agree() {
    for holes in 2..=5 {
        let f = pigeonhole(holes);
        let ProofSolveOutcome::Unsat(proof) = solve_with_drat_proof(&f) else {
            panic!("PHP({}, {holes}) is unsatisfiable", holes + 1);
        };
        let text = write_drat(&proof);
        assert!(!text.is_empty(), "a refutation has steps");
        assert_eq!(
            agree(&f, &text),
            Ok(true),
            "PHP({}, {holes}) must be refuted by both routes",
            holes + 1
        );
        // The reference forward checker accepts a proof this workspace's own
        // core produced, so all three agree here. It is only run on the short
        // proofs: `check_drat` re-scans an accumulating clause database per
        // step, so its cost is superlinear and PHP(6,5)'s proof would dominate
        // the whole suite (the module docs measure 38,015 steps at 200.6 s).
        if proof.len() <= 2_000 {
            assert_eq!(check_drat(&f, &proof), Ok(true));
        }
    }
}

// ---------------------------------------------------------------------------
// Randomised differential
// ---------------------------------------------------------------------------

/// A random 3-CNF over `variables` variables, at a clause/variable ratio around
/// the satisfiability threshold so both verdicts occur.
fn random_3cnf(rng: &mut Rng, variables: usize, clauses: usize) -> CnfFormula {
    // Three *distinct* variables per clause, so fewer than three would spin
    // forever looking for a third. It did, for ten minutes, before this guard.
    assert!(variables >= 3, "a 3-CNF needs at least three variables");
    let mut f = CnfFormula::new(variables);
    for _ in 0..clauses {
        let mut lits = Vec::new();
        while lits.len() < 3 {
            let var = rng.below(variables) + 1;
            if lits
                .iter()
                .any(|existing: &i64| usize::try_from(existing.unsigned_abs()) == Ok(var))
            {
                continue;
            }
            let sign = if rng.next().is_multiple_of(2) {
                1i64
            } else {
                -1i64
            };
            lits.push(sign * i64::try_from(var).expect("variable index fits"));
        }
        f.add_clause(CnfClause::new(lits.iter().map(|&v| lit(v)).collect()))
            .expect("clause is over the formula's variables");
    }
    f
}

#[test]
fn random_solver_proofs_agree() {
    let mut rng = Rng(0x5eed_1234_9abc_def1);
    let mut refuted = 0usize;
    for _ in 0..200 {
        let variables = 3 + rng.below(8);
        let clauses = variables * 4 + rng.below(variables * 2);
        let f = random_3cnf(&mut rng, variables, clauses);
        if let ProofSolveOutcome::Unsat(proof) = solve_with_drat_proof(&f) {
            let text = write_drat(&proof);
            assert_eq!(agree(&f, &text), Ok(true), "on:\n{text}");
            refuted += 1;
        }
    }
    // A control on the control: if nothing was refuted, the loop above asserted
    // nothing about refutations.
    assert!(
        refuted >= 20,
        "the generator produced only {refuted} unsatisfiable instances; \
         this test would have passed while checking almost nothing"
    );
}

/// Mutates a valid proof and requires the two routes to agree on the wreckage.
///
/// This is the half that matters. Both checkers accept every valid proof by
/// construction; a disagreement can only surface on inputs where one of them
/// says no, and those have to be manufactured.
#[test]
fn corrupted_proofs_agree() {
    let mut rng = Rng(0xdead_beef_0000_1111);
    let mut rejected = 0usize;
    let mut accepted = 0usize;
    for _ in 0..400 {
        let variables = 3 + rng.below(6);
        let clauses = variables * 4 + rng.below(variables * 2);
        let f = random_3cnf(&mut rng, variables, clauses);
        let ProofSolveOutcome::Unsat(proof) = solve_with_drat_proof(&f) else {
            continue;
        };
        if proof.is_empty() {
            continue;
        }
        let mut broken = proof.clone();
        match rng.below(4) {
            // Drop a step.
            0 => {
                let victim = rng.below(broken.len());
                broken.remove(victim);
            }
            // Flip a literal's sign.
            1 => {
                let victim = rng.below(broken.len());
                let lits = match &mut broken[victim] {
                    DratStep::Add(lits) | DratStep::Delete(lits) => lits,
                };
                if lits.is_empty() {
                    continue;
                }
                let slot = rng.below(lits.len());
                lits[slot] = lits[slot].negated();
            }
            // Swap two adjacent steps.
            2 => {
                if broken.len() < 2 {
                    continue;
                }
                let victim = rng.below(broken.len() - 1);
                broken.swap(victim, victim + 1);
            }
            // Insert an arbitrary clause.
            _ => {
                let victim = rng.below(broken.len());
                let var = rng.below(variables) + 1;
                let sign = if rng.next().is_multiple_of(2) {
                    1i64
                } else {
                    -1i64
                };
                let value = sign * i64::try_from(var).expect("variable index fits");
                broken.insert(victim, DratStep::Add(vec![lit(value)]));
            }
        }
        let text = write_drat(&broken);
        match agree(&f, &text) {
            Ok(_) => accepted += 1,
            Err(_) => rejected += 1,
        }
    }
    // Controls that fail without the mutation: a corruption pass that never
    // produced a rejection would have exercised only the agreeing path.
    assert!(
        rejected >= 10,
        "only {rejected} corrupted proofs were rejected; the mutation is too gentle \
         to test the disagreeing path"
    );
    assert!(
        accepted >= 10,
        "only {accepted} corrupted proofs were still accepted; the mutation is too \
         violent to test the agreeing path"
    );
}

/// Proofs built by hand out of random clause additions and deletions, most of
/// which are nonsense. Nothing here comes from a solver, so the shapes are ones
/// no producer in this workspace would ever emit — which is exactly where two
/// implementations of the same algorithm drift apart.
#[test]
fn arbitrary_step_sequences_agree() {
    let mut rng = Rng(0x1234_5678_9abc_def0);
    let mut refuted = 0usize;
    let mut rejected = 0usize;
    let mut no_refutation = 0usize;
    for _ in 0..600 {
        let variables = 3 + rng.below(4);
        let clauses = variables * 4 + rng.below(6);
        let f = random_3cnf(&mut rng, variables, clauses);
        let mut text = String::new();
        let steps = 1 + rng.below(8);
        for _ in 0..steps {
            let delete = rng.below(3) == 0;
            if delete {
                text.push_str("d ");
            }
            let width = rng.below(3);
            for _ in 0..width {
                let var = rng.below(variables) + 1;
                let sign = if rng.next().is_multiple_of(2) {
                    ""
                } else {
                    "-"
                };
                write!(text, "{sign}{var} ").expect("writing to a String cannot fail");
            }
            text.push_str("0\n");
        }
        match agree(&f, &text) {
            Ok(true) => refuted += 1,
            Ok(false) => no_refutation += 1,
            Err(_) => rejected += 1,
        }
    }
    // Three-way control: every branch of the verdict space must have been
    // reached, or this generator is testing one path and calling it a fuzz.
    assert!(refuted >= 5, "no refutation was produced ({refuted})");
    assert!(rejected >= 5, "no proof was rejected ({rejected})");
    assert!(
        no_refutation >= 5,
        "no proof lacked an empty clause ({no_refutation})"
    );
}
