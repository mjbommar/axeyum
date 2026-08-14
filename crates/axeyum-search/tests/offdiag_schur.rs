//! Off-diagonal generalized Schur numbers, end to end.
//!
//! Three things are checked here that the unit tests cannot check on their own:
//!
//! 1. **The published values come back out.** Off-diagonal instances are decided
//!    from both sides — `n = N - 1` satisfiable with the model replayed by
//!    [`ColouringFamily::first_violation`], `n = N` refuted with a DRAT proof
//!    re-derived by the in-tree backward checker.
//! 2. **The symmetry breaking is load-bearing and correctly restricted.** A
//!    negative control applies the whole-palette colour ordering to an
//!    off-diagonal instance and shows it produce a **wrong `unsat`**. A symmetry
//!    break that cannot be shown to break something when misapplied has not been
//!    tested.
//! 3. **Subsumption never crosses a colour scope.** The minimal antichain is a
//!    property of one colour's equation; sharing one across colours that forbid
//!    different equations would drop clauses that nothing implies.
//!
//! Everything runs through the pure-Rust proof-producing CDCL core and the
//! pure-Rust backward DRAT checker. No external solver and no external checker
//! takes part (ADR-0002).

use std::collections::HashSet;

use axeyum_cnf::{ProofSolveOutcome, check_drat_backward, solve_with_drat_proof};
use axeyum_search::colouring::ColouringProblem;
use axeyum_search::offdiag::OffDiagonalSchur;
use axeyum_search::{ColouringFamily, parse_family};

/// Decides one instance and returns `"sat"` or `"unsat"`, checking whatever it
/// gets: a model is replayed through the family's independent enumerator, a
/// refutation through the backward DRAT checker.
fn decide(family: &OffDiagonalSchur, problem: &ColouringProblem) -> &'static str {
    let formula = problem.encode().expect("encode");
    match solve_with_drat_proof(&formula) {
        ProofSolveOutcome::Sat(model) => {
            let witness = problem
                .decode_model(model.values())
                .expect("model decodes to a colouring");
            family
                .verify_witness(&witness)
                .expect("SOUNDNESS ALARM: sat model is not a valid colouring");
            "sat"
        }
        ProofSolveOutcome::Unsat(steps) => {
            assert!(!steps.is_empty(), "a zero-step proof is not a refutation");
            assert!(
                check_drat_backward(&formula, &steps).expect("check"),
                "our own backward checker rejected our own proof"
            );
            "unsat"
        }
        other => panic!("undecided: {other:?}"),
    }
}

/// `S(3; s,t,u) = N` means satisfiable at `N - 1` and unsatisfiable at `N`.
/// Both sides or it is not a value.
fn assert_threshold(k: &[usize], value: usize) {
    let family = OffDiagonalSchur::new(k.to_vec()).expect("family");
    let below = family
        .minimal_problem(value - 1)
        .expect("problem below the threshold");
    assert_eq!(
        decide(&family, &below),
        "sat",
        "{}: n = {} should be colourable",
        family.label(),
        value - 1
    );
    let at = family
        .minimal_problem(value)
        .expect("problem at the threshold");
    assert_eq!(
        decide(&family, &at),
        "unsat",
        "{}: n = {value} should not be colourable",
        family.label()
    );
}

#[test]
fn published_off_diagonal_values_come_back_out() {
    // The cheap end of Ahmed-Schaal's eleven exact values. `(4,5,6)` and
    // `(4,5,7)` are the load-bearing ones: three distinct equations, so the
    // instance admits NO colour symmetry at all and an over-strong symmetry
    // break shows up here first.
    let published = [
        (vec![4usize, 4, 4], 43usize),
        (vec![4, 4, 5], 54),
        (vec![4, 4, 6], 65),
        (vec![4, 5, 5], 69),
        (vec![4, 5, 6], 83),
        (vec![4, 5, 7], 97),
    ];
    let mut checked = 0usize;
    for (k, value) in &published {
        assert_threshold(k, *value);
        checked += 1;
    }
    assert_eq!(checked, 6, "the regression ran no instances");
}

#[test]
fn the_diagonal_case_is_the_generalized_schur_number() {
    // Every k equal to 3 is Schur's own number: S(3;3,3,3) = 14, which the
    // crate's `Schur` family also reports.
    assert_threshold(&[3, 3, 3], 14);
}

#[test]
fn whole_palette_symmetry_breaking_produces_a_wrong_unsat() {
    // THE NEGATIVE CONTROL. `S(3;3,4,5)` at n = 41 is satisfiable, and the
    // witness below is replayed by the independent enumerator. Encoding the
    // same instance with the colour ordering imposed across the whole palette —
    // the stock uniform-family symmetry break, justified only by colours being
    // interchangeable — turns it into `unsat`.
    //
    // That is a wrong `unsat`: the encoding, not the mathematics, removed every
    // model. It is exactly the failure `OffDiagonalSchur::symmetry_blocks`
    // exists to prevent, and this test fails if the restriction is ever relaxed.
    let family = OffDiagonalSchur::triple(3, 4, 5).expect("family");
    let points = 41usize;
    assert_eq!(
        family.symmetry_blocks(),
        vec![vec![1], vec![2], vec![3]],
        "three distinct equations admit no colour symmetry at all"
    );

    let correct = family.problem(points).expect("problem");
    assert_eq!(decide(&family, &correct), "sat");

    let per_colour: Vec<Vec<Vec<usize>>> = (1..=family.colours())
        .map(|colour| family.constraints_for_colour(colour, points))
        .collect();
    let over_strong = ColouringProblem::per_colour(
        points,
        family.colours(),
        per_colour,
        vec![vec![1, 2, 3]], // deliberately wrong: these colours do not commute
    )
    .expect("problem");
    assert_eq!(
        decide(&family, &over_strong),
        "unsat",
        "if this is no longer a wrong answer, the control has stopped controlling \
         anything and the restriction is untested"
    );
}

#[test]
fn subsumption_never_crosses_a_colour_scope() {
    // `S(3;4,4,8)`: colours 1 and 2 forbid L(4), colour 3 forbids L(8). The
    // minimal antichain of L(4) says nothing about L(8) and vice versa.
    let family = OffDiagonalSchur::triple(4, 4, 8).expect("family");
    let points = 40usize;
    let problem = family.minimal_problem(points).expect("problem");

    let four = OffDiagonalSchur::minimal_solution_sets(4, points).expect("L(4)");
    let eight = OffDiagonalSchur::minimal_solution_sets(8, points).expect("L(8)");
    assert_ne!(four, eight, "the two equations must not share a list");
    assert_eq!(
        problem.forbidden().len(),
        2 * four.len() + eight.len(),
        "colour-major flattening of two L(4) lists and one L(8) list"
    );

    // Every constraint carries the scope of the equation it came from, and the
    // set really is a solution set of THAT equation.
    let four_sets: HashSet<&Vec<usize>> = four.iter().collect();
    let eight_sets: HashSet<&Vec<usize>> = eight.iter().collect();
    let mut per_scope = [0usize; 4];
    for (index, set) in problem.forbidden().iter().enumerate() {
        let scope = problem.scope(index).expect("off-diagonal problems scope");
        per_scope[scope] += 1;
        match scope {
            1 | 2 => assert!(
                four_sets.contains(set),
                "colour {scope} got a non-L(4) set {set:?}"
            ),
            3 => assert!(
                eight_sets.contains(set),
                "colour 3 got a non-L(8) set {set:?}"
            ),
            other => panic!("scope {other} out of range"),
        }
    }
    assert_eq!(per_scope, [0, four.len(), four.len(), eight.len()]);

    // And the reduction is genuinely per-equation: L(8)'s antichain contains
    // sets that are NOT solution sets of L(4), so a shared antichain would have
    // been visibly wrong.
    let four_full: HashSet<Vec<usize>> = OffDiagonalSchur::solution_sets(4, points)
        .into_iter()
        .collect();
    assert!(
        eight.iter().any(|set| !four_full.contains(set)),
        "the two equations happen to coincide here; pick a sharper instance"
    );
}

#[test]
fn the_reduced_encoding_decides_exactly_what_the_full_one_decides() {
    // Subsumption is claimed to preserve models, not merely satisfiability.
    // Check the strong form on instances small enough to encode both ways.
    let mut compared = 0usize;
    for k in [
        vec![3usize, 3, 4],
        vec![4, 4, 5],
        vec![3, 4, 5],
        vec![4, 5, 6],
    ] {
        let family = OffDiagonalSchur::new(k.clone()).expect("family");
        for points in [12usize, 25, 38] {
            let full = family.problem(points).expect("full problem");
            let reduced = family.minimal_problem(points).expect("reduced problem");
            assert!(
                reduced.forbidden().len() <= full.forbidden().len(),
                "the reduction must not invent clauses"
            );
            assert_eq!(
                decide(&family, &full),
                decide(&family, &reduced),
                "k={k:?} n={points}: reduced and full encodings disagree"
            );
            // Same models, not just the same verdict: any colouring is judged
            // identically by both.
            let mut state = 0x5eed_2026_0813_u64;
            for _ in 0..64 {
                let colouring: Vec<usize> = (0..points)
                    .map(|_| {
                        state = state
                            .wrapping_mul(6_364_136_223_846_793_005)
                            .wrapping_add(1);
                        ((state >> 33) % 3) as usize + 1
                    })
                    .collect();
                assert_eq!(
                    full.first_monochromatic(&colouring).is_none(),
                    reduced.first_monochromatic(&colouring).is_none(),
                    "k={k:?} n={points}: {colouring:?} judged differently"
                );
            }
            compared += 1;
        }
    }
    assert_eq!(compared, 12, "the comparison ran no instances");
}

#[test]
fn a_family_spec_reaches_the_same_instance() {
    let spec = parse_family("offdiag-schur:s=4,t=4,u=5").expect("spec");
    assert_eq!(spec.label(), "S(3;4,4,5)");
    let direct = OffDiagonalSchur::triple(4, 4, 5).expect("family");
    assert_eq!(
        spec.problem(30).expect("via spec"),
        direct.problem(30).expect("direct")
    );
}

#[test]
fn uniform_families_are_untouched_by_the_off_diagonal_path() {
    // The Rado and Schur encodings must stay exactly what the claim ledger's
    // stored certificates were produced against: no scopes, whole-palette
    // symmetry breaking.
    for spec in ["rado:a=3,b=2,k=4", "rado:a=1,b=1,k=3", "schur:k=3"] {
        let family = parse_family(spec).expect("spec");
        let problem = family.problem(20).expect("problem");
        assert!(!problem.is_off_diagonal(), "{spec} must stay uniform");
        assert!(
            problem.symmetry_blocks().is_none(),
            "{spec} must keep the legacy whole-palette symmetry breaking"
        );
        for index in 0..problem.forbidden().len() {
            assert_eq!(problem.scope(index), None, "{spec} must not scope anything");
        }
    }
}
