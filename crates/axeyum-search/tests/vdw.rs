//! Van der Waerden numbers, end to end, with no external solver or checker.
//!
//! Each value is established from **both sides**: `n = N − 1` satisfiable with
//! the colouring replayed by [`ColouringFamily::first_violation`], which shares
//! no code with the encoder, and `n = N` unsatisfiable with a DRAT proof from
//! axeyum's own CDCL core re-derived by axeyum's own backward checker. No
//! kissat, no drat-trim, no z3 (ADR-0002).
//!
//! The load-bearing test in this file is
//! `whole_palette_symmetry_breaking_produces_a_wrong_unsat`. Van der Waerden's
//! off-diagonal instances are the second family in this crate whose colours are
//! not interchangeable, and the encoder's default symmetry breaking is unsound
//! for them. The control shows it producing a demonstrably wrong `unsat` rather
//! than asserting that it would.

use axeyum_cnf::{ProofSolveOutcome, check_drat_backward, solve_with_drat_proof};
use axeyum_search::colouring::ColouringProblem;
use axeyum_search::vdw::VanDerWaerden;
use axeyum_search::{ColouringFamily, parse_family};

/// Decides one instance and re-checks whatever verdict comes back: a `sat`
/// model is decoded and replayed through the independent enumerator, an `unsat`
/// proof is re-derived by the backward checker. Returns `true` for satisfiable.
fn decide(family: &dyn ColouringFamily, points: usize) -> bool {
    let problem = family.problem(points).expect("problem");
    assert!(
        !problem.forbidden().is_empty(),
        "no constraints at n={points}: every formula would be satisfiable"
    );
    let formula = problem.encode().expect("encode");
    match solve_with_drat_proof(&formula) {
        ProofSolveOutcome::Sat(model) => {
            let witness = problem.decode_model(model.values()).expect("decode");
            family
                .verify_witness(&witness)
                .expect("the sat model is not a valid colouring");
            true
        }
        ProofSolveOutcome::Unsat(steps) => {
            assert!(!steps.is_empty(), "a zero-step proof is not a refutation");
            assert!(
                check_drat_backward(&formula, &steps).expect("check"),
                "our own backward checker rejected our own proof"
            );
            false
        }
        other => panic!("n={points} undecided: {other:?}"),
    }
}

/// Both sides of one value, with the published number as the expectation.
fn value_is(spec: &str, expected: usize) {
    let family = parse_family(spec).expect("family spec");
    assert!(
        decide(family.as_ref(), expected - 1),
        "{}: n = {} should be satisfiable",
        family.label(),
        expected - 1
    );
    assert!(
        !decide(family.as_ref(), expected),
        "{}: n = {expected} should be unsatisfiable",
        family.label()
    );
}

#[test]
fn off_diagonal_row_reproduces_the_published_values() {
    // Ahmed, Kullmann and Snevily (arXiv:1102.5433), Table 1.
    value_is("vdw:k1=3,k2=4", 18);
    value_is("vdw:k1=3,k2=5", 22);
    value_is("vdw:k1=3,k2=6", 32);
    value_is("vdw:k1=3,k2=7", 46);
}

#[test]
fn diagonal_values_reproduce_chvatal() {
    // W(2,3) = 9 and W(3,3) = 27, Chvatal 1970. `w(2;3,3)` is the same number
    // reached through the off-diagonal spelling, and the two must agree.
    value_is("vdw:c=2,k=3", 9);
    value_is("vdw:k1=3,k2=3", 9);
    value_is("vdw:c=3,k=3", 27);
    value_is("vdw:c=2,k=4", 35);
}

/// **The negative control.** Colour classes may be ordered by least element
/// only between colours that forbid the same sets. `w(2;3,4)` forbids 3-term
/// progressions in colour 1 and 4-term progressions in colour 2, so pinning
/// point 1 to colour 1 — which is exactly what the whole-palette break does —
/// is not a symmetry, and here it deletes every good colouring.
///
/// `n = 17` is satisfiable: `w(2;3,4) = 18`, and the witness is produced and
/// replayed below. Encoded with the whole palette declared interchangeable the
/// same instance comes back **`unsat`**, with a valid DRAT proof of a formula
/// that should never have been built.
///
/// A conventional pipeline cannot catch this. The generator emits a CNF; the
/// solver refutes it correctly; the proof checker verifies the refutation
/// correctly; a referee re-running both agrees. The failed precondition lives
/// in the modelling layer, above the point where the chain begins.
///
/// The instance matters as much as the test. `w(2;3,5)` over `n = 1..=21` and
/// `w(2;3,6)` over `n = 1..=31` were both scanned and **neither ever flips** —
/// the over-strong constraint happens not to bite there — so a control built on
/// either would have passed while testing nothing.
#[test]
fn whole_palette_symmetry_breaking_produces_a_wrong_unsat() {
    let family = VanDerWaerden::off_diagonal(3, 4).expect("family");
    assert!(family.colour_dependent());
    assert_eq!(family.symmetry_blocks(), vec![vec![1], vec![2]]);

    let points = 17;
    let per_colour: Vec<Vec<Vec<usize>>> = (1..=family.colours())
        .map(|colour| family.constraints_for_colour(colour, points))
        .collect();

    let sound = ColouringProblem::per_colour(
        points,
        family.colours(),
        per_colour.clone(),
        family.symmetry_blocks(),
    )
    .expect("sound problem");
    let formula = sound.encode().expect("encode");
    let ProofSolveOutcome::Sat(model) = solve_with_drat_proof(&formula) else {
        panic!("n = 17 is satisfiable: w(2;3,4) = 18");
    };
    let witness = sound.decode_model(model.values()).expect("decode");
    family
        .verify_witness(&witness)
        .expect("the witness must survive the independent enumerator");
    // The reason the break is wrong, made concrete: every good colouring of
    // [1,17] gives point 1 the colour that avoids four-term progressions, so
    // "point 1 takes colour 1" rules them all out.
    assert_eq!(
        witness.colouring()[0],
        2,
        "point 1 takes colour 2 in the witness"
    );

    let whole = ColouringProblem::per_colour(
        points,
        family.colours(),
        per_colour,
        vec![(1..=family.colours()).collect()],
    )
    .expect("whole-palette problem");
    let broken = whole.encode().expect("encode");
    let ProofSolveOutcome::Unsat(steps) = solve_with_drat_proof(&broken) else {
        panic!(
            "the whole-palette break no longer produces a wrong unsat; \
             this control has stopped controlling anything"
        );
    };
    // The refutation is valid — that is the point. Everything downstream of the
    // modelling layer reports success on a formula that is not the problem.
    assert!(!steps.is_empty());
    assert!(
        check_drat_backward(&broken, &steps).expect("check"),
        "the wrong-unsat proof is itself a valid DRAT refutation"
    );
}

/// The diagonal case must keep the uniform path, because there the colours
/// really are interchangeable and the stronger whole-palette break is both
/// sound and worth having.
#[test]
fn diagonal_instances_keep_the_uniform_encoding() {
    for (colours, k) in [(2usize, 3usize), (3, 3), (4, 3), (2, 5)] {
        let family = VanDerWaerden::diagonal(colours, k).expect("family");
        assert!(!family.colour_dependent(), "W({colours},{k}) is uniform");
        let problem = family.problem(20).expect("problem");
        assert!(!problem.is_off_diagonal());
        assert!(problem.symmetry_blocks().is_none());
        // ... and it is the same problem the colour-agnostic constructor builds.
        let uniform = ColouringProblem::new(20, colours, VanDerWaerden::progressions(k, 20))
            .expect("uniform");
        assert_eq!(problem.encode().expect("a"), uniform.encode().expect("b"));
    }
}

/// The subsumption reduction that dominates the off-diagonal Schur family does
/// nothing at all here, and this is the measurement rather than the argument.
#[test]
fn the_antichain_reduction_has_nothing_to_remove() {
    for k in [3usize, 4, 5, 8, 12] {
        for points in [30usize, 97, 135] {
            assert_eq!(
                VanDerWaerden::subsumed_pair(k, points),
                None,
                "a length-{k} progression inside [1,{points}] contains another"
            );
        }
    }
    // The clause count is therefore exactly the progression count, per colour.
    let family = VanDerWaerden::off_diagonal(3, 20).expect("family");
    let problem = family.problem(388).expect("problem");
    assert_eq!(
        problem.forbidden().len(),
        VanDerWaerden::progression_count(3, 388) + VanDerWaerden::progression_count(20, 388)
    );
}
