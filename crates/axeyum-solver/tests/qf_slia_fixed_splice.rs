//! Focused coverage for the correlated bound on generated fixed-position splices.
#![cfg(feature = "full")]

use std::time::Duration;

use axeyum_smtlib::parse_script;
use axeyum_solver::{CheckResult, SolverConfig, online_string_verdict, solve_smtlib};

fn config() -> SolverConfig {
    SolverConfig::new().with_timeout(Duration::from_secs(5))
}

/// `PyExZ3` spells a one-character overwrite as two substrings around a literal.
/// Naively summing their independent bounds yields `8 + 1 + 8 = 17`, although the
/// exact result never exceeds the base's eight-character bound. Exercise every
/// short-string branch as well as the full-bound case; each SAT model is replayed
/// by the front door against the original formula.
#[test]
fn fixed_splice_uses_correlated_bound_and_preserves_short_strings() {
    for (source, expected) in [
        ("", "X"),
        ("a", "aX"),
        ("ab", "aX"),
        ("abc", "aXc"),
        ("abcdefgh", "aXcdefgh"),
    ] {
        let script = format!(
            r#"(set-logic QF_SLIA)
(declare-fun s () String)
(assert (= s "{source}"))
(assert (= (str.++ (str.++ (str.substr s 0 (- 1 0)) "X")
                    (str.substr s 2 (- (str.len s) 2)))
           "{expected}"))
(check-sat)
"#
        );
        let result = solve_smtlib(&script, &config())
            .unwrap_or_else(|error| panic!("fixed splice must parse and solve: {error:?}"));
        assert!(
            matches!(result.result, CheckResult::Sat(_)),
            "fixed splice over {source:?} must equal {expected:?}; got {:?}",
            result.result
        );
    }
}

/// `PyEx` spells a first-occurrence character replacement as a prefix through the
/// match, a replacement inside that prefix, and the untouched suffix. The two
/// pieces have large independent packed maxima, but their lengths are correlated:
/// equal-length needle/replacement pairs reconstruct exactly one base-length word.
#[test]
fn split_replace_rejoin_uses_the_base_bound() {
    for (source, expected) in [
        ("", ""),
        ("bbb", "bbb"),
        ("A", "a"),
        ("BAAB", "BaAB"),
        ("BAAAAAAAAAAB", "BaAAAAAAAAAB"),
    ] {
        let script = format!(
            r#"(set-logic QF_SLIA)
(declare-fun s () String)
(assert (= s "{source}"))
(assert (=
  (str.++
    (str.replace
      (str.substr s 0 (+ (str.indexof s "A" 0) 1))
      "A" "a")
    (str.substr s
      (+ (str.indexof s "A" 0) 1)
      (- (str.len s) (+ (str.indexof s "A" 0) 1))))
  "{expected}"))
(check-sat)
"#
        );
        let parsed = parse_script(&script)
            .unwrap_or_else(|error| panic!("split/replace/rejoin must parse: {error:?}"));
        assert!(
            parsed.word_only_fallback.is_none(),
            "the exact correlated bound must retain the bounded encoding"
        );
        assert!(parsed.prefer_source_string_routes);
        assert!(
            matches!(
                solve_smtlib(&script, &config())
                    .expect("solve split/replace/rejoin")
                    .result,
                CheckResult::Sat(_)
            ),
            "first A replacement over {source:?} must produce {expected:?}"
        );
    }

    // An unequal-length replacement over the 256-byte literal cap still declines
    // the bounded parse (the historic 2-byte "zz" shape now parses bounded), so
    // the source SAT fallback must still carry the pipeline.
    let zz = "z".repeat(300);
    let unequal_lengths = format!(
        r#"(set-logic QF_SLIA)
(declare-fun s () String)
(assert (=
  (str.++
    (str.replace
      (str.substr s 0 (+ (str.indexof s "A" 0) 1))
      "A" "{zz}")
    (str.substr s
      (+ (str.indexof s "A" 0) 1)
      (- (str.len s) (+ (str.indexof s "A" 0) 1))))
  "{zz}"))
(check-sat)
"#
    );
    let unequal = parse_script(&unequal_lengths)
        .expect("the source SAT fallback retains the unequal-length pipeline");
    assert!(unequal.word_only_fallback.is_some());
    assert!(unequal.source_string_sat_problem.is_some());
    assert!(
        matches!(
            solve_smtlib(&unequal_lengths, &config())
                .expect("solve unequal-length pipeline")
                .result,
            CheckResult::Sat(_)
        ),
        "s = \"A\" is a replayed witness for the unequal-length pipeline"
    );
}

#[test]
fn large_split_replace_pipeline_retains_the_fast_source_fallback() {
    let mut script = String::from("(set-logic QF_SLIA)\n(declare-fun s () String)\n");
    let assertion = r#"(assert (str.contains
  (str.++
    (str.replace
      (str.substr s 0 (+ (str.indexof s "A" 0) 1))
      "A" "a")
    (str.substr s
      (+ (str.indexof s "A" 0) 1)
      (- (str.len s) (+ (str.indexof s "A" 0) 1))))
  "Z"))
"#;
    for _ in 0..65 {
        script.push_str(assertion);
    }
    script.push_str("(check-sat)\n");

    // Under the original 13/26-byte caps this over-limit pipeline declined the
    // bounded parse entirely (word-only fallback). With the 256/512-byte caps it
    // parses bounded; the fast-source property survives as
    // `prefer_source_string_routes`, which hands the source-level ladder first
    // refusal before the packed DAG is ever solved.
    let parsed = parse_script(&script).expect("large pipeline parses bounded under the wide caps");
    assert!(parsed.word_only_fallback.is_none());
    assert!(parsed.prefer_source_string_routes);
    assert!(
        matches!(
            solve_smtlib(&script, &config())
                .expect("solve large pipeline")
                .result,
            CheckResult::Sat(_)
        ),
        "s = \"Z\" (contains needs no \"A\") is a replayed witness"
    );
}

/// The UNSAT-only word relaxation may treat a repeated fixed splice as one opaque
/// Seq term: every real model induces the same abstract value, so an equality plus
/// disequality is a valid original-theory contradiction. The generated ground and
/// empty-length guards must survive into the Boolean skeleton as well.
#[test]
fn opaque_fixed_splice_equality_conflict_is_unsat() {
    let input = r#"(set-logic QF_SLIA)
(declare-fun s () String)
(declare-fun end () String)
(assert
  (and
    (not (not (= (ite (= (str.++ (str.++ (str.substr s 0 (- 0 0)) "X")
                                      (str.substr s 1 (- (str.len s) 1))) end)
                         1 0) 0)))
    (not (= (ite (= end (str.++ (str.++ (str.substr s 0 (- 0 0)) "X")
                                  (str.substr s 1 (- (str.len s) 1))))
                 1 0) 0))
    (not (not (= (ite (<= (str.len s) 0) 1 0) 0)))
    (>= (- 0 0) 0)
    (>= (- (str.len s) 1) 0)))
(check-sat)
"#;
    let mut script = parse_script(input).expect("parse fixed-splice conflict");
    assert!(script.word_skeleton_opaque_terms > 0);
    assert_eq!(
        online_string_verdict(&mut script, &config()),
        Some(CheckResult::Unsat)
    );
    assert_eq!(
        solve_smtlib(input, &config())
            .expect("solve fixed-splice conflict")
            .result,
        CheckResult::Unsat
    );
}

/// A model of the opaque relaxation does not prove the original splice formula
/// satisfiable. The public online entry point must therefore discard SAT whenever
/// the skeleton contains an opaque fixed-splice term.
#[test]
fn opaque_fixed_splice_relaxation_never_reports_sat() {
    let input = r#"(set-logic QF_SLIA)
(declare-fun s () String)
(declare-fun end () String)
(assert (= end (str.++ (str.++ (str.substr s 0 (- 0 0)) "X")
                         (str.substr s 1 (- (str.len s) 1)))))
(assert (not (<= (str.len s) 0)))
(assert (>= (- 0 0) 0))
(assert (>= (- (str.len s) 1) 0))
(check-sat)
"#;
    let mut script = parse_script(input).expect("parse satisfiable fixed-splice relaxation");
    assert!(script.word_skeleton_opaque_terms > 0);
    assert_eq!(online_string_verdict(&mut script, &config()), None);
}

#[test]
fn guaranteed_constant_pin_folds_a_later_fixed_splice() {
    let input = r#"(set-logic QF_SLIA)
(declare-fun s () String)
(assert (= s "log"))
(assert (not (not (= (ite (= (str.++ (str.++ (str.substr s 0 2) "t")
                                      (str.substr s 3 (- (str.len s) 3)))
                             "lot")
                        1 0)
                     0))))
(assert (>= (- (str.len s) 3) 0))
(check-sat)
"#;
    let mut script = parse_script(input).expect("parse constant-pinned splice");
    assert_eq!(
        online_string_verdict(&mut script, &config()),
        Some(CheckResult::Unsat)
    );
}

#[test]
fn equal_distinct_index_splices_imply_the_in_range_base() {
    let input = r#"(set-logic QF_SLIA)
(declare-fun s () String)
(declare-fun end () String)
(assert (not (= s end)))
(assert (= end (str.++ (str.++ (str.substr s 0 2) "t")
                         (str.substr s 3 (- (str.len s) 3)))))
(assert (= end (str.++ (str.++ (str.substr s 0 0) "d")
                         (str.substr s 1 (- (str.len s) 1)))))
(assert (>= (- (str.len s) 1) 0))
(check-sat)
"#;
    let mut script = parse_script(input).expect("parse equal distinct-index splices");
    assert_eq!(
        online_string_verdict(&mut script, &config()),
        Some(CheckResult::Unsat)
    );
}

#[test]
fn out_of_range_equal_splices_do_not_imply_the_base() {
    let input = r#"(set-logic QF_SLIA)
(declare-fun s () String)
(declare-fun end () String)
(assert (= s ""))
(assert (= end "x"))
(assert (not (= s end)))
(assert (= end (str.++ (str.++ (str.substr s 0 0) "x")
                         (str.substr s 1 (- (str.len s) 1)))))
(assert (= end (str.++ (str.++ (str.substr s 0 2) "x")
                         (str.substr s 3 (- (str.len s) 3)))))
(check-sat)
"#;
    let mut script = parse_script(input).expect("parse out-of-range splice model");
    assert_ne!(
        online_string_verdict(&mut script, &config()),
        Some(CheckResult::Unsat)
    );
    assert!(!script.source_string_semantic_unsat);
}

#[test]
fn exact_splice_conflict_survives_an_unrelated_skeleton_decline() {
    let input = r#"(set-logic QF_SLIA)
(declare-fun s () String)
(assert (= s "lot"))
(assert (= (str.++ (str.++ (str.substr s 0 0) "l")
                    (str.substr s 1 (- (str.len s) 1)))
           "log"))
(assert (= (str.len s) 3))
(check-sat)
"#;
    let script = parse_script(input).expect("parse independent fixed-splice conflict");
    assert!(script.word_skeleton.is_empty());
    assert!(script.source_string_semantic_unsat);
    assert_eq!(
        solve_smtlib(input, &config())
            .expect("solve independent fixed-splice conflict")
            .result,
        CheckResult::Unsat
    );
}

#[test]
fn exact_splice_disequality_conflict_survives_an_unrelated_skeleton_decline() {
    let input = r#"(set-logic QF_SLIA)
(declare-fun s () String)
(assert (= s "log"))
(assert (not (= (str.++ (str.++ (str.substr s 0 2) "t")
                         (str.substr s 3 (- (str.len s) 3)))
                "lot")))
(assert (= (str.len s) 3))
(check-sat)
"#;
    let script = parse_script(input).expect("parse independent fixed-splice disequality");
    assert!(script.word_skeleton.is_empty());
    assert!(script.source_string_semantic_unsat);
    assert_eq!(
        solve_smtlib(input, &config())
            .expect("solve independent fixed-splice disequality")
            .result,
        CheckResult::Unsat
    );
}

#[test]
fn exact_pinned_view_content_conflict_sets_the_semantic_refuter() {
    let input = r#"(set-logic QF_SLIA)
(declare-fun url () String)
(assert (= (str.substr url 0 (str.indexof url ":" 0)) "http"))
(assert (not (not (not (= (ite
  (str.contains (str.substr url 0 (str.indexof url ":" 0)) "A") 1 0) 0)))))
(check-sat)
"#;
    let script = parse_script(input).expect("parse pinned-view content conflict");
    assert!(script.source_string_semantic_unsat);
    assert_eq!(
        solve_smtlib(input, &config())
            .expect("solve pinned-view content conflict")
            .result,
        CheckResult::Unsat
    );
}

#[test]
fn exact_pinned_view_content_mutation_stays_satisfiable() {
    let input = r#"(set-logic QF_SLIA)
(declare-fun url () String)
(assert (= (str.substr url 0 (str.indexof url ":" 0)) "http"))
(assert (str.contains (str.substr url 0 (str.indexof url ":" 0)) "t"))
(check-sat)
"#;
    let script = parse_script(input).expect("parse pinned-view content model");
    assert!(!script.source_string_semantic_unsat);
    assert_ne!(
        solve_smtlib(input, &config())
            .expect("solve pinned-view content model")
            .result,
        CheckResult::Unsat
    );
}

#[test]
fn word_only_fallback_retains_exact_path_conflicts() {
    // The pad literal must exceed the 256-byte cap so the bounded parse still
    // declines into the word-only fallback (the historic 14-byte pad now parses).
    let pad = "abcdefghijklmn".repeat(19); // 266 bytes > 256
    let input = format!(
        r#"(set-logic QF_SLIA)
(declare-fun s () String)
(declare-fun pad () String)
(assert (= pad "{pad}"))
(assert (= (str.indexof s "x" 0) 0))
(assert (not (not (not (= (ite (= (str.len s) 0) 1 0) 0)))))
(assert (not (not (= (ite (= (str.len s) 0) 1 0) 0))))
(check-sat)
"#
    );
    let input = input.as_str();
    let script = parse_script(input).expect("parse word-only fallback conflict");
    assert!(script.word_only_fallback.is_some());
    assert!(script.source_string_semantic_unsat);
    assert_eq!(
        solve_smtlib(input, &config())
            .expect("solve word-only fallback conflict")
            .result,
        CheckResult::Unsat
    );
}

#[test]
fn semantic_refuter_never_masks_a_non_capacity_parse_decline() {
    let input = r"(set-logic QF_SLIA)
(declare-fun s () String)
(assert (= (unknown.word.operator s) s))
(assert (not (= (unknown.word.operator s) s)))
(check-sat)
";
    assert!(
        parse_script(input).is_err(),
        "an untyped unsupported operator must remain a parse decline"
    );
}

#[test]
fn satisfiable_splice_mutation_does_not_set_the_semantic_refuter() {
    let input = r#"(set-logic QF_SLIA)
(declare-fun s () String)
(assert (= s "lot"))
(assert (= (str.++ (str.++ (str.substr s 0 0) "l")
                    (str.substr s 1 (- (str.len s) 1)))
           "lot"))
(assert (= (str.len s) 3))
(check-sat)
"#;
    let script = parse_script(input).expect("parse satisfiable fixed-splice mutation");
    assert!(script.word_skeleton.is_empty());
    assert!(!script.source_string_semantic_unsat);
    assert_ne!(
        solve_smtlib(input, &config())
            .expect("solve satisfiable fixed-splice mutation")
            .result,
        CheckResult::Unsat
    );
}

#[test]
fn scoped_splice_conflict_does_not_escape_a_pop() {
    let input = r#"(set-logic QF_SLIA)
(declare-fun s () String)
(assert (= s "lot"))
(push 1)
(assert (= (str.++ (str.++ (str.substr s 0 0) "l")
                    (str.substr s 1 (- (str.len s) 1)))
           "log"))
(pop 1)
(check-sat)
"#;
    let script = parse_script(input).expect("parse scoped fixed-splice mutation");
    assert!(!script.source_string_semantic_unsat);
    assert_ne!(
        solve_smtlib(input, &config())
            .expect("solve scoped fixed-splice mutation")
            .result,
        CheckResult::Unsat
    );
}

#[test]
fn exact_source_rewrite_refutes_noetzli_term_and_predicate_families() {
    for assertion in [
        r#"(not (= (str.contains x (str.substr "A" z z)) true))"#,
        r#"(not (= (str.replace "A" y (str.replace y y x))
                    (str.replace x x (str.replace "A" y x))))"#,
        r"(not (= (str.substr x z 1) (str.at x z)))",
        r#"(not (= (str.substr x 0 (str.indexof "A" "B" z)) ""))"#,
        r"(not (= (str.from_int (+ 0 z)) (str.from_int z)))",
    ] {
        let input = format!(
            r"(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun y () String)
(declare-fun z () Int)
(assert {assertion})
(check-sat)
"
        );
        let script = parse_script(&input).expect("parse exact source rewrite");
        assert!(
            script.source_string_semantic_unsat,
            "source normalizer must refute {assertion}"
        );
        assert_eq!(
            solve_smtlib(&input, &config())
                .expect("solve exact source rewrite")
                .result,
            CheckResult::Unsat,
            "exact source rewrite must survive the bounded-string gate: {assertion}"
        );
    }
}

#[test]
fn singleton_replace_inverse_refutes_public_nested_replace_families() {
    for assertion in [
        r#"(not (= (= "A" (str.replace x "A" "B")) false))"#,
        r#"(not (= (str.contains "A" (str.replace x "A" "B")) (= x "")))"#,
        r#"(not (= (= "B" (str.replace x "A" "B"))
                    (= "A" (str.replace x "B" "A"))))"#,
        r#"(not (= (str.contains "B" (str.replace x "A" "B"))
                    (str.contains "A" (str.replace x "B" "A"))))"#,
        r#"(not (= (str.replace "A" (str.replace x y x) x) "A"))"#,
        r#"(not (= (str.replace "A" (str.replace x y x) "")
                    (str.replace "A" x (str.replace "" y x))))"#,
        r#"(not (= (str.replace "A" (str.replace x "A" "B") y)
                    (str.++ (str.replace "" x y) "A")))"#,
        r#"(not (= (str.replace "A" (str.replace y x "A") y)
                    (str.replace "A" (str.replace x y "A") x)))"#,
        r#"(not (= (str.replace "A" (str.replace "B" x "A") x)
                    (str.replace "A" (str.replace x "B" "A") x)))"#,
        r#"(not (= (str.replace "B" (str.replace x y x) x) "B"))"#,
        r#"(not (= (str.replace "" x (str.replace "" y "A"))
                    (str.replace "" x (str.replace x y "A"))))"#,
        r#"(not (= (str.replace "" (str.++ x y) "B")
                    (str.replace "" x (str.replace x y "B"))))"#,
    ] {
        let input = format!(
            r"(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun y () String)
(assert {assertion})
(check-sat)
"
        );
        let script = parse_script(&input).expect("parse singleton inverse theorem");
        assert!(
            script.source_string_semantic_unsat,
            "source singleton inverse must refute {assertion}"
        );
    }

    let front_door = r#"(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun y () String)
(assert (not (= (str.replace "A" (str.replace x y x) x) "A")))
(check-sat)
"#;
    assert_eq!(
        solve_smtlib(front_door, &config())
            .expect("solve representative singleton inverse theorem")
            .result,
        CheckResult::Unsat,
        "the source singleton inverse must survive the bounded gate"
    );
}

#[test]
fn exact_source_rewrite_does_not_assume_the_packed_string_bound() {
    for assertion in [
        // A longer unbounded string can carry `A` at index 100.
        r#"(= (str.at x 100) "A")"#,
        // A string longer than the packed bound differs from its first 8 chars.
        r"(not (= (str.substr x 0 8) x))",
    ] {
        let input = format!(
            r"(set-logic QF_SLIA)
(declare-fun x () String)
(assert {assertion})
(check-sat)
"
        );
        let script = parse_script(&input).expect("parse bound-sensitive model");
        assert!(
            !script.source_string_semantic_unsat,
            "source normalizer must not use the packed bound: {assertion}"
        );
        assert_ne!(
            solve_smtlib(&input, &config())
                .expect("solve bound-sensitive model")
                .result,
            CheckResult::Unsat,
            "a satisfiable beyond-bound formula must not become UNSAT: {assertion}"
        );
    }
}

#[test]
fn exact_source_rewrite_declines_nonidentity_symbolic_terms() {
    let input = r"(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun y () String)
(assert (not (= (str.++ x y) (str.++ y x))))
(check-sat)
";
    let script = parse_script(input).expect("parse nonidentity terms");
    assert!(!script.source_string_semantic_unsat);
    assert_ne!(
        solve_smtlib(input, &config())
            .expect("solve nonidentity terms")
            .result,
        CheckResult::Unsat
    );
}

#[test]
fn exact_source_rewrite_does_not_use_assertions_after_check_sat() {
    let input = r"(set-logic QF_SLIA)
(declare-fun x () String)
(check-sat)
(assert (not (= (str.replace x x x) x)))
";
    let script = parse_script(input).expect("parse post-query assertion");
    assert!(!script.source_string_semantic_unsat);
    assert!(matches!(
        solve_smtlib(input, &config())
            .expect("solve assertion stack at check-sat")
            .result,
        CheckResult::Sat(_)
    ));
}

#[test]
fn exact_source_relations_refute_noetzli_predicate_families() {
    for assertion in [
        r"(not (= (str.contains x (str.at x z)) true))",
        r"(not (= (str.suffixof y (str.at x z))
                    (str.prefixof y (str.at x z))))",
        r#"(not (= (str.prefixof x (str.replace x "A" "B"))
                    (= x (str.replace x "A" "B"))))"#,
        r"(not (= (= x (str.++ y x)) (= x (str.++ x y))))",
        r#"(not (= (= x (str.substr x z z)) (= x "")))"#,
        r"(not (str.suffixof (str.substr x z (- (str.len x) z)) x))",
    ] {
        let input = format!(
            r"(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun y () String)
(declare-fun z () Int)
(assert {assertion})
(check-sat)
"
        );
        let script = parse_script(&input).expect("parse exact source relation");
        assert!(
            script.source_string_semantic_unsat,
            "source relation must refute {assertion}"
        );
        assert_eq!(
            solve_smtlib(&input, &config())
                .expect("solve exact source relation")
                .result,
            CheckResult::Unsat,
            "source relation must survive the bounded-string gate: {assertion}"
        );
    }
}

#[test]
fn exact_source_relations_decline_nearby_non_theorems() {
    for assertion in [
        // Prefix and suffix differ once the subject may have length two.
        r#"(not (= (str.suffixof "A" "AB") (str.prefixof "A" "AB")))"#,
        // An `at` view of a different source need not occur in `x`.
        r"(not (str.contains x (str.at y z)))",
        // Offset zero can preserve a nonempty source exactly.
        r#"(not (= (= x (str.substr x 0 z)) (= x "")))"#,
        // No cancellation is valid when neither concat component is the peer.
        r"(not (= x (str.++ y y)))",
    ] {
        let input = format!(
            r"(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun y () String)
(declare-fun z () Int)
(assert {assertion})
(check-sat)
"
        );
        let script = parse_script(&input).expect("parse relational non-theorem");
        assert!(
            !script.source_string_semantic_unsat,
            "source relation must decline {assertion}"
        );
        assert_ne!(
            solve_smtlib(&input, &config())
                .expect("solve relational non-theorem")
                .result,
            CheckResult::Unsat,
            "satisfiable relational control must not become UNSAT: {assertion}"
        );
    }
}

#[test]
fn exact_source_alphabets_refute_disjoint_rewrite_families() {
    for assertion in [
        r#"(not (= (= "A" (str.from_int z)) false))"#,
        r#"(not (= (= "A" (str.at "B" z)) false))"#,
        r#"(not (= (str.prefixof "A" (str.substr "B" 0 z)) false))"#,
        r#"(not (= (str.contains (str.from_int z) "A") false))"#,
        r#"(not (= (str.replace "A" (str.from_int z) "") "A"))"#,
        r#"(not (= (str.replace "A" (str.at "B" z) "") "A"))"#,
        r"(not (= (str.at (str.at x z) 0) (str.at x z)))",
        r#"(not (= (str.at "" z) ""))"#,
    ] {
        let input = format!(
            r"(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun z () Int)
(assert {assertion})
(check-sat)
"
        );
        let script = parse_script(&input).expect("parse exact alphabet relation");
        assert!(
            script.source_string_semantic_unsat,
            "source alphabet must refute {assertion}"
        );
        assert_eq!(
            solve_smtlib(&input, &config())
                .expect("solve exact alphabet relation")
                .result,
            CheckResult::Unsat,
            "source alphabet result must survive the bounded-string gate: {assertion}"
        );
    }
}

#[test]
fn exact_source_alphabets_decline_overlapping_or_nullable_controls() {
    for assertion in [
        // Decimal strings can contain decimal characters.
        r#"(not (= "1" (str.from_int z)))"#,
        // An empty needle is always contained, including in a disjoint alphabet.
        r#"(not (str.contains "A" (str.at "B" z)))"#,
        // A nullable disjoint needle prefixes its replacement when nonempty.
        r#"(not (= (str.replace "A" (str.at "B" z) "C") "A"))"#,
        // An unknown source may contain the supposedly disjoint literal.
        r#"(not (= x "A"))"#,
    ] {
        let input = format!(
            r"(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun z () Int)
(assert {assertion})
(check-sat)
"
        );
        let script = parse_script(&input).expect("parse alphabet non-theorem");
        assert!(
            !script.source_string_semantic_unsat,
            "source alphabet must decline {assertion}"
        );
        assert_ne!(
            solve_smtlib(&input, &config())
                .expect("solve alphabet non-theorem")
                .result,
            CheckResult::Unsat,
            "satisfiable alphabet control must not become UNSAT: {assertion}"
        );
    }
}

#[test]
fn exact_source_view_bounds_refute_noetzli_index_families() {
    for assertion in [
        r#"(not (= (str.substr x 0 (str.indexof x x z)) ""))"#,
        r#"(not (= (str.substr x z (- 0 z)) ""))"#,
        r#"(not (= (str.substr x (- 0 z) z) ""))"#,
        r#"(not (= (str.substr x (str.len x) z) ""))"#,
        r#"(not (= (str.at x (str.len x)) ""))"#,
        r#"(not (= (str.at (str.substr x 1 z) z) ""))"#,
        r#"(not (= (str.substr (str.substr x 1 z) z z) ""))"#,
        r"(not (= (str.substr (str.substr x 1 z) 0 z) (str.substr x 1 z)))",
        r#"(not (= (str.at x (str.indexof x "" z)) (str.at x z)))"#,
        r#"(not (= (str.at "A" (str.indexof x x z)) (str.at "A" z)))"#,
    ] {
        let input = format!(
            r"(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun z () Int)
(assert {assertion})
(check-sat)
"
        );
        let script = parse_script(&input).expect("parse exact view-bound relation");
        assert!(
            script.source_string_semantic_unsat,
            "source view bounds must refute {assertion}"
        );
        assert_eq!(
            solve_smtlib(&input, &config())
                .expect("solve exact view-bound relation")
                .result,
            CheckResult::Unsat,
            "source view-bound result must survive the bounded-string gate: {assertion}"
        );
    }
}

#[test]
fn exact_source_view_bounds_decline_nearby_in_range_controls() {
    for assertion in [
        r#"(not (= (str.substr x 0 z) ""))"#,
        r#"(not (= (str.substr x z (- 1 z)) ""))"#,
        r#"(not (= (str.at x (- (str.len x) 1)) ""))"#,
        r#"(not (= (str.at (str.substr x 0 z) 0) ""))"#,
        r"(not (= (str.substr (str.substr x 0 z) 0 1) (str.substr x 0 z)))",
        r#"(not (= (str.at x (str.indexof y "" z)) (str.at x z)))"#,
    ] {
        let input = format!(
            r"(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun y () String)
(declare-fun z () Int)
(assert {assertion})
(check-sat)
"
        );
        let script = parse_script(&input).expect("parse view-bound non-theorem");
        assert!(
            !script.source_string_semantic_unsat,
            "source view bounds must decline {assertion}"
        );
        assert_ne!(
            solve_smtlib(&input, &config())
                .expect("solve view-bound non-theorem")
                .result,
            CheckResult::Unsat,
            "satisfiable view-bound control must not become UNSAT: {assertion}"
        );
    }
}

#[test]
fn exact_source_conditional_replace_refutes_noetzli_families() {
    for assertion in [
        r#"(not (= (str.contains "" x) (= x "")))"#,
        r#"(not (= (str.replace "" y "") ""))"#,
        r#"(not (= (str.replace (str.replace "" x y) "A" "B")
                    (str.replace "" x (str.replace y "A" "B"))))"#,
        r#"(not (= (str.replace (str.replace "" x "A") "A" y)
                    (str.replace "" x y)))"#,
        r#"(not (= (str.replace x (str.replace "" y "") "A")
                    (str.++ "A" x)))"#,
        r#"(not (= (str.replace (str.replace "B" x "A") "B" "A")
                    (str.replace "A" x "A")))"#,
        r#"(not (= (str.replace (str.replace "B" x y) x y)
                    (str.replace "B" x (str.replace y x y))))"#,
        r#"(not (= (str.replace (str.replace "" x y) x "A")
                    (str.replace "" x (str.++ "A" y))))"#,
        r#"(not (= (str.replace (str.++ x x) "A" y)
                    (str.++ (str.replace x "A" y) x)))"#,
        r#"(not (= (str.replace (str.++ x "A") "B" y)
                    (str.++ (str.replace x "B" y) "A")))"#,
        r#"(not (= (str.replace (str.++ x y) x "A")
                    (str.++ "A" y)))"#,
    ] {
        let input = format!(
            r"(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun y () String)
(assert {assertion})
(check-sat)
"
        );
        let script = parse_script(&input).expect("parse exact conditional replace");
        assert!(
            script.source_string_semantic_unsat,
            "conditional replace must refute {assertion}"
        );
        assert_eq!(
            solve_smtlib(&input, &config())
                .expect("solve exact conditional replace")
                .result,
            CheckResult::Unsat,
            "conditional replace must survive the bounded-string gate: {assertion}"
        );
    }
}

#[test]
fn exact_source_conditional_replace_declines_branch_sensitive_controls() {
    for assertion in [
        r#"(not (= (str.replace "" x y) y))"#,
        r#"(not (= (str.replace "A" x y) "A"))"#,
        r#"(not (= (str.replace "B" x "A") (str.replace "A" x "A")))"#,
        r#"(not (= (str.replace "" x y) (str.replace "" y x)))"#,
        r#"(not (= (str.replace "B" x y) (str.replace "B" y x)))"#,
        r#"(not (= (str.replace (str.++ (str.at x 0) "A") "A" "B")
                    (str.++ (str.replace (str.at x 0) "A" "B") "A")))"#,
        r#"(not (= (str.replace (str.++ (str.at x 0) (str.at y 0))
                                (str.at y 0) "A")
                    (str.++ (str.at x 0) "A")))"#,
    ] {
        let input = format!(
            r"(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun y () String)
(assert {assertion})
(check-sat)
"
        );
        let script = parse_script(&input).unwrap_or_else(|error| {
            panic!("parse conditional replace non-theorem {assertion}: {error}")
        });
        assert!(
            !script.source_string_semantic_unsat,
            "conditional replace must decline {assertion}"
        );
        assert_ne!(
            solve_smtlib(&input, &config())
                .expect("solve conditional replace non-theorem")
                .result,
            CheckResult::Unsat,
            "satisfiable conditional replace control must not become UNSAT: {assertion}"
        );
    }
}

#[test]
fn exact_source_length_dominated_replace_refutes_noetzli_families() {
    for assertion in [
        r"(not (= (str.replace x (str.++ x x) x) x))",
        r"(not (= (str.replace x (str.replace x y x) x) x))",
        r"(not (= (str.contains x (str.replace x y x))
                    (= x (str.replace x y x))))",
    ] {
        let input = format!(
            r"(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun y () String)
(assert {assertion})
(check-sat)
"
        );
        let script = parse_script(&input).expect("parse length-dominated replace theorem");
        assert!(
            script.source_string_semantic_unsat,
            "length-dominated replace must refute {assertion}"
        );
        assert_eq!(
            solve_smtlib(&input, &config())
                .expect("solve length-dominated replace theorem")
                .result,
            CheckResult::Unsat,
            "length-dominated replace must survive the bounded-string gate: {assertion}"
        );
    }
}

#[test]
fn exact_source_length_dominated_replace_declines_unordered_control() {
    let assertion = r"(not (= (str.replace x y x) x))";
    let input = format!(
        r"(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun y () String)
(assert {assertion})
(check-sat)
"
    );
    let script = parse_script(&input).expect("parse unordered replace control");
    assert!(
        !script.source_string_semantic_unsat,
        "unordered replace must decline {assertion}"
    );
    assert_ne!(
        solve_smtlib(&input, &config())
            .expect("solve unordered replace control")
            .result,
        CheckResult::Unsat,
        "satisfiable unordered replace control must not become UNSAT: {assertion}"
    );
}

#[test]
fn exact_source_symmetric_equality_atoms_refute_noetzli_families() {
    for assertion in [
        r"(not (= (str.contains (str.at x 0) x)
                    (= x (str.at x 0))))",
        r"(not (= (str.prefixof (str.replace x y x) x)
                    (= x (str.replace x y x))))",
    ] {
        let input = format!(
            r"(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun y () String)
(assert {assertion})
(check-sat)
"
        );
        let script = parse_script(&input).expect("parse symmetric equality theorem");
        assert!(
            script.source_string_semantic_unsat,
            "symmetric equality normalization must refute {assertion}"
        );
        assert_eq!(
            solve_smtlib(&input, &config())
                .expect("solve symmetric equality theorem")
                .result,
            CheckResult::Unsat,
            "symmetric equality must survive the bounded-string gate: {assertion}"
        );
    }
}

#[test]
fn exact_source_self_replacement_views_refute_noetzli_families() {
    for assertion in [
        r"(not (= (str.at (str.replace x y x) 0) (str.at x 0)))",
        r"(not (= (str.contains (str.replace x y x) x) true))",
        r#"(not (= (str.prefixof "A" (str.replace x y x))
                    (str.prefixof "A" x)))"#,
        r#"(not (= (str.replace "A" (str.replace x "A" x) y)
                    (str.replace "A" x y)))"#,
    ] {
        let input = format!(
            r"(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun y () String)
(assert {assertion})
(check-sat)
"
        );
        let script = parse_script(&input).expect("parse self-replacement view theorem");
        assert!(
            script.source_string_semantic_unsat,
            "self-replacement view must refute {assertion}"
        );
        assert_eq!(
            solve_smtlib(&input, &config())
                .expect("solve self-replacement view theorem")
                .result,
            CheckResult::Unsat,
            "self-replacement view must survive the bounded-string gate: {assertion}"
        );
    }
}

#[test]
fn exact_source_self_replacement_views_decline_wider_controls() {
    for assertion in [
        r#"(not (= (str.prefixof "AA" (str.replace x y x))
                    (str.prefixof "AA" x)))"#,
        r#"(not (= (str.contains (str.replace x y x) "AA")
                    (str.contains x "AA")))"#,
        r#"(not (= (= "A" (str.replace x y x)) (= x "A")))"#,
    ] {
        let input = format!(
            r"(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun y () String)
(assert {assertion})
(check-sat)
"
        );
        let script = parse_script(&input).expect("parse wider self-replacement control");
        assert!(
            !script.source_string_semantic_unsat,
            "wider self-replacement view must decline {assertion}"
        );
        assert_ne!(
            solve_smtlib(&input, &config())
                .expect("solve wider self-replacement control")
                .result,
            CheckResult::Unsat,
            "satisfiable wider self-replacement control must not become UNSAT: {assertion}"
        );
    }
}

#[test]
fn exact_source_affine_one_code_point_views_refute_noetzli_families() {
    for assertion in [
        r#"(not (= (str.at "A" (- 0 z)) (str.at "A" z)))"#,
        r#"(not (= (str.at "B" (+ z z)) (str.at "B" z)))"#,
        r#"(not (= (str.substr "A" z (- z 1)) ""))"#,
        r#"(not (= (str.substr "B" (+ z z) z) ""))"#,
    ] {
        let input = format!(
            r"(set-logic QF_SLIA)
(declare-fun z () Int)
(assert {assertion})
(check-sat)
"
        );
        let script = parse_script(&input).expect("parse affine one-code-point theorem");
        assert!(
            script.source_string_semantic_unsat,
            "affine one-code-point view must refute {assertion}"
        );
        assert_eq!(
            solve_smtlib(&input, &config())
                .expect("solve affine one-code-point theorem")
                .result,
            CheckResult::Unsat,
            "affine one-code-point view must survive the bounded-string gate: {assertion}"
        );
    }
}

#[test]
fn exact_source_affine_one_code_point_views_decline_near_misses() {
    for assertion in [
        r#"(not (= (str.at "A" (+ z 1)) (str.at "A" z)))"#,
        r#"(not (= (str.substr "A" z (+ z 1)) ""))"#,
    ] {
        let input = format!(
            r"(set-logic QF_SLIA)
(declare-fun z () Int)
(assert {assertion})
(check-sat)
"
        );
        let script = parse_script(&input).expect("parse affine one-code-point control");
        assert!(
            !script.source_string_semantic_unsat,
            "affine one-code-point near miss must decline {assertion}"
        );
        assert_ne!(
            solve_smtlib(&input, &config())
                .expect("solve affine one-code-point control")
                .result,
            CheckResult::Unsat,
            "satisfiable affine one-code-point control must not become UNSAT: {assertion}"
        );
    }
}

#[test]
fn exact_source_equality_paths_and_self_expanded_needles_refute_noetzli_families() {
    for assertion in [
        r#"(not (= (= y (str.replace "A" y x))
                    (= x (str.replace "A" x y))))"#,
        r#"(not (= (= y (str.replace "" y x))
                    (= x (str.replace "" x y))))"#,
        r#"(not (= (str.replace x (str.++ x "A") y) x))"#,
        r#"(not (= (str.replace x (str.++ "B" x) y) x))"#,
        r#"(not (= (str.replace y (str.replace "A" "" y) x)
                    (str.replace x x y)))"#,
        r#"(not (= (str.replace "B" x (str.replace "A" x ""))
                    (str.replace "B" x "A")))"#,
        r"(not (= (str.replace x (str.replace y x y) z)
                    (str.replace x y z)))",
    ] {
        let input = format!(
            r"(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun y () String)
(declare-fun z () String)
(assert {assertion})
(check-sat)
"
        );
        let script = parse_script(&input).expect("parse equality-path replacement theorem");
        assert!(
            script.source_string_semantic_unsat,
            "equality-path replacement theorem must refute {assertion}"
        );
        assert_eq!(
            solve_smtlib(&input, &config())
                .expect("solve equality-path replacement theorem")
                .result,
            CheckResult::Unsat,
            "equality-path theorem must survive the bounded-string gate: {assertion}"
        );
    }
}

#[test]
fn exact_source_self_expanded_needles_decline_near_misses() {
    let assertion = r"(not (= (str.replace x (str.replace y z y) w) (str.replace x y w)))";
    let input = format!(
        r"(set-logic QF_SLIA)
(declare-fun w () String)
(declare-fun x () String)
(declare-fun y () String)
(declare-fun z () String)
(assert {assertion})
(check-sat)
"
    );
    let script = parse_script(&input).expect("parse self-expanded needle control");
    assert!(
        !script.source_string_semantic_unsat,
        "self-expanded needle near miss must decline"
    );
    assert_ne!(
        solve_smtlib(&input, &config())
            .expect("solve self-expanded needle control")
            .result,
        CheckResult::Unsat,
        "satisfiable self-expanded needle control must not become UNSAT"
    );
}

#[test]
fn exact_source_one_code_point_word_boundaries_refute_noetzli_families() {
    for assertion in [
        r#"(not (= (str.prefixof x (str.replace "A" x "B")) (= x "")))"#,
        r#"(not (= (str.suffixof x (str.replace "B" x "A")) (= x "")))"#,
        r#"(not (= (str.prefixof y (str.replace "A" x y))
                    (str.prefixof x (str.replace "A" y x))))"#,
        r#"(not (= (str.contains (str.replace "B" x "A") x) (= x "")))"#,
        r#"(not (= (not (str.prefixof x "A"))
                    (= "A" (str.replace "A" x "B"))))"#,
    ] {
        let input = format!(
            r"(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun y () String)
(assert {assertion})
(check-sat)
"
        );
        let script = parse_script(&input).expect("parse one-code-point word-boundary theorem");
        assert!(
            script.source_string_semantic_unsat,
            "one-code-point word-boundary theorem must refute {assertion}"
        );
        assert_eq!(
            solve_smtlib(&input, &config())
                .expect("solve one-code-point word-boundary theorem")
                .result,
            CheckResult::Unsat,
            "boundary theorem must survive the bounded-string gate: {assertion}"
        );
    }
}

#[test]
fn exact_source_one_code_point_word_boundaries_decline_unbounded_words() {
    let assertion = r#"(not (= (str.prefixof x y) (or (= x "") (= x y))))"#;
    let input = format!(
        r"(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun y () String)
(assert {assertion})
(check-sat)
"
    );
    let script = parse_script(&input).expect("parse unbounded word-boundary control");
    assert!(
        !script.source_string_semantic_unsat,
        "unbounded word-boundary near miss must decline"
    );
    assert_ne!(
        solve_smtlib(&input, &config())
            .expect("solve unbounded word-boundary control")
            .result,
        CheckResult::Unsat,
        "satisfiable unbounded word-boundary control must not become UNSAT"
    );
}

#[test]
fn exact_source_index_totality_views_refute_noetzli_families() {
    for assertion in [
        r#"(not (= (str.at "A" (str.indexof x y 1)) ""))"#,
        r"(not (= (str.at (str.at x 0) 0) (str.at x 0)))",
        r#"(not (= (str.at "B" (str.indexof x "" z)) (str.at "B" z)))"#,
        r"(not (= (str.at (str.at x z) z) (str.at x (str.indexof x x z))))",
        r#"(not (= (str.substr x z (str.indexof x "" 1)) (str.at x z)))"#,
        r#"(not (= (str.substr x z (str.indexof x "" z)) (str.substr x z z)))"#,
        r#"(not (= (str.substr x (str.indexof y "" z) z)
                    (str.substr x z (str.indexof y "" z))))"#,
        r#"(not (= (str.substr "A" (str.indexof x y z) z) ""))"#,
        r#"(not (= (str.substr "B" z (str.indexof x "" 1))
                    (str.substr "B" z (str.len x))))"#,
        r"(not (= (str.at (str.from_int z) z)
                    (str.from_int (str.indexof x x z))))",
    ] {
        let input = format!(
            r"(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun y () String)
(declare-fun z () Int)
(assert {assertion})
(check-sat)
"
        );
        let script = parse_script(&input).expect("parse exact index-totality theorem");
        assert!(
            script.source_string_semantic_unsat,
            "index-totality theorem must refute {assertion}"
        );
        assert_eq!(
            solve_smtlib(&input, &config())
                .expect("solve exact index-totality theorem")
                .result,
            CheckResult::Unsat,
            "index-totality theorem must survive the bounded-string gate: {assertion}"
        );
    }
}

#[test]
fn exact_source_index_totality_views_decline_long_word_controls() {
    for assertion in [
        r#"(not (= (str.at "AB" (str.indexof x "" z)) (str.at "AB" z)))"#,
        r#"(not (= (str.substr "AB" z (str.indexof x "" 1))
                    (str.substr "AB" z (str.len x))))"#,
    ] {
        let input = format!(
            r"(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun z () Int)
(assert {assertion})
(check-sat)
"
        );
        let script = parse_script(&input).expect("parse exact index-totality control");
        assert!(
            !script.source_string_semantic_unsat,
            "long-word index-totality near miss must decline: {assertion}"
        );
        assert_ne!(
            solve_smtlib(&input, &config())
                .expect("solve exact index-totality control")
                .result,
            CheckResult::Unsat,
            "satisfiable long-word index-totality control must not become UNSAT: {assertion}"
        );
    }
}

#[test]
fn exact_source_small_subject_indexof_refutes_view_families() {
    for assertion in [
        r#"(not (= (str.at x (str.indexof "A" x 1)) ""))"#,
        r#"(not (= (str.substr x 0 (str.indexof "A" x 1)) ""))"#,
        r#"(not (= (str.from_int (str.indexof "" x 1)) ""))"#,
    ] {
        let input = format!(
            r"(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun z () Int)
(assert {assertion})
(check-sat)
"
        );
        let script = parse_script(&input).expect("parse exact small-subject indexof");
        assert!(
            script.source_string_semantic_unsat,
            "small-subject indexof must refute {assertion}"
        );
        assert_eq!(
            solve_smtlib(&input, &config())
                .expect("solve exact small-subject indexof")
                .result,
            CheckResult::Unsat,
            "small-subject indexof must survive the bounded-string gate: {assertion}"
        );
    }
}

#[test]
fn exact_source_small_subject_indexof_declines_nonidentities() {
    for assertion in [
        r#"(not (= (str.indexof "A" x 0) 0))"#,
        r#"(not (= (str.at y (str.indexof "A" x 0)) (str.at y 0)))"#,
        r#"(not (= (str.indexof "" x 0) (- 1)))"#,
    ] {
        let input = format!(
            r"(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun y () String)
(assert {assertion})
(check-sat)
"
        );
        let script = parse_script(&input)
            .unwrap_or_else(|error| panic!("parse small-subject indexof control: {error}"));
        assert!(
            !script.source_string_semantic_unsat,
            "small-subject indexof must decline {assertion}"
        );
        assert_ne!(
            solve_smtlib(&input, &config())
                .expect("solve small-subject indexof control")
                .result,
            CheckResult::Unsat,
            "satisfiable small-subject indexof control must not become UNSAT: {assertion}"
        );
    }
}

#[test]
fn exact_source_one_code_point_views_refute_noetzli_families() {
    for assertion in [
        r#"(not (= (= "B" (str.at "B" z)) (= "A" (str.at "A" z))))"#,
        r#"(not (= (= "B" (str.substr "B" 0 z))
                    (= "A" (str.substr "A" 0 z))))"#,
        r#"(not (= (str.at (str.substr "A" 0 z) 0)
                    (str.substr "A" 0 z)))"#,
        r#"(not (= (str.substr "A" z 2) (str.at "A" z)))"#,
        r#"(not (= (str.replace (str.at "A" z) "A" "B")
                    (str.at "B" z)))"#,
        r#"(not (= (str.replace (str.substr "B" 0 z) "B" x)
                    (str.replace (str.substr "A" 0 z) "A" x)))"#,
    ] {
        let input = format!(
            r"(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun z () Int)
(assert {assertion})
(check-sat)
"
        );
        let script = parse_script(&input).expect("parse exact one-code-point view");
        assert!(
            script.source_string_semantic_unsat,
            "one-code-point view must refute {assertion}"
        );
        assert_eq!(
            solve_smtlib(&input, &config())
                .expect("solve exact one-code-point view")
                .result,
            CheckResult::Unsat,
            "one-code-point view must survive the bounded-string gate: {assertion}"
        );
    }
}

#[test]
fn exact_source_one_code_point_views_decline_nonidentities() {
    for assertion in [
        r#"(not (= (str.at "A" z) "A"))"#,
        r#"(not (= (str.substr "A" z x) (str.at "A" z)))"#,
        r#"(not (= (str.replace (str.at "A" z) "A" "B")
                    (str.at "C" z)))"#,
    ] {
        let input = format!(
            r"(set-logic QF_SLIA)
(declare-fun x () Int)
(declare-fun z () Int)
(assert {assertion})
(check-sat)
"
        );
        let script = parse_script(&input).expect("parse one-code-point view control");
        assert!(
            !script.source_string_semantic_unsat,
            "one-code-point view must decline {assertion}"
        );
        assert_ne!(
            solve_smtlib(&input, &config())
                .expect("solve one-code-point view control")
                .result,
            CheckResult::Unsat,
            "satisfiable one-code-point control must not become UNSAT: {assertion}"
        );
    }
}

#[test]
fn exact_source_one_code_point_concat_views_refute_noetzli_families() {
    for assertion in [
        r#"(not (= (str.prefixof "A" (str.++ x x))
                    (str.prefixof "A" x)))"#,
        r#"(not (= (= "A" (str.++ x "B")) false))"#,
        r#"(not (= (str.contains (str.++ x x) "A")
                    (str.contains x "A")))"#,
        r#"(not (= (str.contains (str.++ y x) "B")
                    (str.contains (str.++ x y) "B")))"#,
        r#"(not (= (str.replace "A" (str.++ x "B") y) "A"))"#,
        r#"(not (= (str.replace "A" (str.++ "A" x) y)
                    (str.replace "A" (str.++ x "A") y)))"#,
    ] {
        let input = format!(
            r"(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun y () String)
(assert {assertion})
(check-sat)
"
        );
        let script = parse_script(&input).expect("parse exact one-code-point concat view");
        assert!(
            script.source_string_semantic_unsat,
            "one-code-point concat view must refute {assertion}"
        );
        assert_eq!(
            solve_smtlib(&input, &config())
                .expect("solve exact one-code-point concat view")
                .result,
            CheckResult::Unsat,
            "one-code-point concat view must survive the bounded-string gate: {assertion}"
        );
    }
}

#[test]
fn exact_source_one_code_point_concat_views_decline_cross_boundary_controls() {
    for assertion in [
        r#"(not (= (str.contains (str.++ x y) "AB")
                    (or (str.contains x "AB") (str.contains y "AB"))))"#,
        r#"(not (= (str.prefixof "AB" (str.++ x y))
                    (str.prefixof "AB" x)))"#,
        r#"(not (= (= "AB" (str.++ x y))
                    (and (= x "A") (= y "B"))))"#,
        r#"(not (= (str.replace "A" (str.++ x "A") y) "A"))"#,
    ] {
        let input = format!(
            r"(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun y () String)
(assert {assertion})
(check-sat)
"
        );
        let script = parse_script(&input).expect("parse concat boundary control");
        assert!(
            !script.source_string_semantic_unsat,
            "one-code-point concat view must decline {assertion}"
        );
        assert_ne!(
            solve_smtlib(&input, &config())
                .expect("solve concat boundary control")
                .result,
            CheckResult::Unsat,
            "satisfiable concat boundary control must not become UNSAT: {assertion}"
        );
    }
}

#[test]
fn exact_source_concat_index_routes_refute_noetzli_families() {
    for assertion in [
        r"(not (= (str.at (str.++ x x) 0) (str.at x 0)))",
        r#"(not (= (str.at (str.++ "A" x) 1) (str.at x 0)))"#,
        r#"(not (= (str.at (str.replace y "" "A") 1)
                    (str.at (str.replace x x y) 0)))"#,
        r#"(not (= (str.substr (str.++ "A" x) 1 z)
                    (str.substr x 0 z)))"#,
        r#"(not (= (str.substr (str.++ "B" x) z z)
                    (str.substr x (- z 1) z)))"#,
        r#"(not (= (str.substr (str.replace y "" "A") 1 z)
                    (str.substr (str.replace x x y) 0 z)))"#,
    ] {
        let input = format!(
            r"(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun y () String)
(declare-fun z () Int)
(assert {assertion})
(check-sat)
"
        );
        let script = parse_script(&input).expect("parse exact concat index route");
        assert!(
            script.source_string_semantic_unsat,
            "concat index route must refute {assertion}"
        );
        assert_eq!(
            solve_smtlib(&input, &config())
                .expect("solve exact concat index route")
                .result,
            CheckResult::Unsat,
            "concat index route must survive the bounded-string gate: {assertion}"
        );
    }
}

#[test]
fn exact_source_unary_concat_commutativity_refutes_noetzli_families() {
    for assertion in [
        r#"(not (= (str.++ (str.at "A" z) "A")
                    (str.++ "A" (str.at "A" z))))"#,
        r#"(not (= (str.++ (str.substr "B" 0 z) "B")
                    (str.++ "B" (str.substr "B" 0 z))))"#,
        r#"(not (= (str.++ (str.replace "A" x "") "A")
                    (str.++ "A" (str.replace "A" x ""))))"#,
        r#"(not (= (str.++ (str.replace "B" x "B") "B")
                    (str.++ "B" (str.replace "B" x "B"))))"#,
    ] {
        let input = format!(
            r"(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun z () Int)
(assert {assertion})
(check-sat)
"
        );
        let script = parse_script(&input).expect("parse unary concat commutativity theorem");
        assert!(
            script.source_string_semantic_unsat,
            "unary concat commutativity must refute {assertion}"
        );
        assert_eq!(
            solve_smtlib(&input, &config())
                .expect("solve unary concat commutativity theorem")
                .result,
            CheckResult::Unsat,
            "unary concat commutativity must survive the bounded-string gate: {assertion}"
        );
    }
}

#[test]
fn exact_source_concat_routes_decline_satisfiable_controls() {
    for assertion in [
        r"(not (= (str.++ x y) (str.++ y x)))",
        r#"(not (= (str.++ (str.at "A" z) "B")
                    (str.++ "B" (str.at "A" z))))"#,
        r#"(not (= (str.substr (str.++ "A" x) 0 z)
                    (str.substr x (- 1) z)))"#,
    ] {
        let input = format!(
            r"(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun y () String)
(declare-fun z () Int)
(assert {assertion})
(check-sat)
"
        );
        let script = parse_script(&input).expect("parse concat route control");
        assert!(
            !script.source_string_semantic_unsat,
            "satisfiable concat route control must decline: {assertion}"
        );
        assert_ne!(
            solve_smtlib(&input, &config())
                .expect("solve concat route control")
                .result,
            CheckResult::Unsat,
            "satisfiable concat route control must not become UNSAT: {assertion}"
        );
    }
}

#[test]
fn exact_source_fixed_word_languages_refute_noetzli_families() {
    for assertion in [
        r#"(not (= (str.suffixof x "AA") (str.prefixof x "AA")))"#,
        r#"(not (= (str.suffixof x (str.replace "A" y "A"))
                    (str.prefixof x (str.replace "A" y "A"))))"#,
        r#"(not (= (str.prefixof "A" (str.at x 0)) (str.prefixof "A" x)))"#,
        r#"(not (= (str.contains "A" (str.++ x x)) (= x "")))"#,
        r#"(not (= (str.contains "AA" x) (str.prefixof x "AA")))"#,
        r#"(not (= (str.contains (str.replace "A" x "A") y)
                    (str.prefixof y (str.replace "A" x "A"))))"#,
        r#"(not (= (str.contains "A" (str.replace "A" x "")) true))"#,
        r#"(not (= (str.replace "A" (str.++ x x) x) "A"))"#,
        r#"(not (= (str.replace "A" (str.++ x x) y)
                    (str.++ (str.replace "" x y) "A")))"#,
    ] {
        let input = format!(
            r"(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun y () String)
(declare-fun z () Int)
(assert {assertion})
(check-sat)
"
        );
        let script = parse_script(&input).expect("parse fixed-word language theorem");
        assert!(
            script.source_string_semantic_unsat,
            "fixed-word language must refute {assertion}"
        );
        assert_eq!(
            solve_smtlib(&input, &config())
                .expect("solve fixed-word language theorem")
                .result,
            CheckResult::Unsat,
            "fixed-word language must survive the bounded-string gate: {assertion}"
        );
    }
}

#[test]
fn exact_source_fixed_word_languages_decline_satisfiable_controls() {
    for assertion in [
        r#"(not (= (str.suffixof x "AB") (str.prefixof x "AB")))"#,
        r#"(not (= (str.contains "AB" x) (str.prefixof x "AB")))"#,
        r#"(not (= (str.prefixof "AB" x) (= (str.at x 0) "AB")))"#,
    ] {
        let input = format!(
            r"(set-logic QF_SLIA)
(declare-fun x () String)
(assert {assertion})
(check-sat)
"
        );
        let script = parse_script(&input).expect("parse fixed-word language control");
        assert!(
            !script.source_string_semantic_unsat,
            "satisfiable fixed-word language control must decline: {assertion}"
        );
        assert_ne!(
            solve_smtlib(&input, &config())
                .expect("solve fixed-word language control")
                .result,
            CheckResult::Unsat,
            "satisfiable fixed-word language control must not become UNSAT: {assertion}"
        );
    }
}

#[test]
fn exact_source_boolean_paths_refute_correlated_empty_replacements() {
    for assertion in [
        r#"(not (= (str.replace "" (str.++ x y) x) ""))"#,
        r#"(not (= (str.replace "" (str.++ x y) y) ""))"#,
        r#"(not (= (str.replace "" (str.replace x "" y) x) ""))"#,
        r#"(not (= (str.replace "" (str.replace x "" y) y) ""))"#,
    ] {
        let input = format!(
            r"(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun y () String)
(assert {assertion})
(check-sat)
"
        );
        let script = parse_script(&input).expect("parse correlated empty replacement theorem");
        assert!(
            script.source_string_semantic_unsat,
            "Boolean path facts must refute {assertion}"
        );
        assert_eq!(
            solve_smtlib(&input, &config())
                .expect("solve correlated empty replacement theorem")
                .result,
            CheckResult::Unsat,
            "Boolean path facts must survive the bounded-string gate: {assertion}"
        );
    }
}

#[test]
fn exact_source_boolean_paths_decline_correlated_empty_controls() {
    for assertion in [
        r#"(not (= (str.replace "" (str.++ x y) "A") ""))"#,
        r#"(not (= (str.replace "" (str.replace x "" y) "A") ""))"#,
    ] {
        let input = format!(
            r"(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun y () String)
(assert {assertion})
(check-sat)
"
        );
        let script = parse_script(&input).expect("parse correlated empty replacement control");
        assert!(
            !script.source_string_semantic_unsat,
            "satisfiable Boolean path control must decline: {assertion}"
        );
        assert_ne!(
            solve_smtlib(&input, &config())
                .expect("solve correlated empty replacement control")
                .result,
            CheckResult::Unsat,
            "satisfiable Boolean path control must not become UNSAT: {assertion}"
        );
    }
}

#[test]
fn exact_source_affine_substr_views_refute_noetzli_families() {
    for assertion in [
        r#"(not (= (str.substr "A" 0 (+ z z)) (str.substr "A" 0 z)))"#,
        r#"(not (= (str.substr "B" 0 (+ z z)) (str.substr "B" 0 z)))"#,
        r#"(not (= (str.substr "A" z (+ 1 z)) (str.at "A" z)))"#,
        r#"(not (= (str.substr "B" z (+ 1 z)) (str.at "B" z)))"#,
        r#"(not (= (str.substr "A" (- z 1) z) (str.at "A" (- 1 z))))"#,
        r#"(not (= (str.substr "B" (- z 1) z) (str.at "B" (- 1 z))))"#,
        r"(not (= (str.substr (str.substr y 0 1) 0 1)
                    (str.at (str.replace x x y) 0)))",
        r"(not (= (str.substr (str.substr y 1 1) 0 1)
                    (str.at (str.replace x x y) 1)))",
        r"(not (= (str.substr (str.substr y z 1) 0 1)
                    (str.at (str.replace x x y) z)))",
    ] {
        let input = format!(
            r"(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun y () String)
(declare-fun z () Int)
(assert {assertion})
(check-sat)
"
        );
        let script = parse_script(&input).expect("parse affine one-code-point theorem");
        assert!(
            script.source_string_semantic_unsat,
            "affine one-code-point view must refute {assertion}"
        );
        assert_eq!(
            solve_smtlib(&input, &config())
                .expect("solve affine one-code-point theorem")
                .result,
            CheckResult::Unsat,
            "affine one-code-point view must survive the bounded-string gate: {assertion}"
        );
    }
}

#[test]
fn exact_source_affine_substr_views_decline_satisfiable_controls() {
    for assertion in [
        r#"(not (= (str.substr "A" 0 (+ z z 1)) (str.substr "A" 0 z)))"#,
        r#"(not (= (str.substr "A" z z) (str.at "A" z)))"#,
        r#"(not (= (str.substr "A" (- z 1) (- z 1)) (str.at "A" (- 1 z))))"#,
    ] {
        let input = format!(
            r"(set-logic QF_SLIA)
(declare-fun z () Int)
(assert {assertion})
(check-sat)
"
        );
        let script = parse_script(&input).expect("parse affine one-code-point control");
        assert!(
            !script.source_string_semantic_unsat,
            "satisfiable affine one-code-point control must decline: {assertion}"
        );
        assert_ne!(
            solve_smtlib(&input, &config())
                .expect("solve affine one-code-point control")
                .result,
            CheckResult::Unsat,
            "satisfiable affine one-code-point control must not become UNSAT: {assertion}"
        );
    }
}

#[test]
fn exact_source_boolean_ac_views_refute_noetzli_families() {
    let mut assertions = Vec::new();
    for literal in [r#""A""#, r#""B""#] {
        assertions.push(format!(
            r"(not (= (= {literal} (str.++ y x)) (= {literal} (str.++ x y))))"
        ));
        assertions.push(format!(
            r"(not (= (str.contains {literal} (str.++ y x))
                       (str.contains {literal} (str.++ x y))))"
        ));
        assertions.push(format!(
            r#"(not (= (= {literal} (str.replace x "" y))
                       (= {literal} (str.++ x y))))"#
        ));
        assertions.push(format!(
            r#"(not (= (str.contains {literal} (str.replace x "" y))
                       (str.contains {literal} (str.++ x y))))"#
        ));
        for replacement in ["x", r#""""#, r#""A""#, r#""B""#] {
            assertions.push(format!(
                r"(not (= (str.replace {literal} (str.++ y x) {replacement})
                           (str.replace {literal} (str.++ x y) {replacement})))"
            ));
        }
    }

    assert_eq!(assertions.len(), 16);
    for assertion in assertions {
        let input = format!(
            r"(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun y () String)
(assert {assertion})
(check-sat)
"
        );
        let script = parse_script(&input).expect("parse Boolean AC string theorem");
        assert!(
            script.source_string_semantic_unsat,
            "Boolean AC string theorem must refute {assertion}"
        );
        assert_eq!(
            solve_smtlib(&input, &config())
                .expect("solve Boolean AC string theorem")
                .result,
            CheckResult::Unsat,
            "Boolean AC string theorem must survive the bounded-string gate: {assertion}"
        );
    }
}

#[test]
fn exact_source_boolean_ac_views_decline_satisfiable_controls() {
    for assertion in [
        r#"(not (= (= "AB" (str.++ y x)) (= "AB" (str.++ x y))))"#,
        r#"(not (= (str.contains "AB" (str.++ y x))
                   (str.contains "AB" (str.++ x y))))"#,
        r#"(not (= (str.replace "AB" (str.++ y x) "")
                   (str.replace "AB" (str.++ x y) "")))"#,
    ] {
        let input = format!(
            r"(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun y () String)
(assert {assertion})
(check-sat)
"
        );
        let script = parse_script(&input).expect("parse Boolean AC string control");
        assert!(
            !script.source_string_semantic_unsat,
            "satisfiable Boolean AC string control must decline: {assertion}"
        );
        assert_ne!(
            solve_smtlib(&input, &config())
                .expect("solve Boolean AC string control")
                .result,
            CheckResult::Unsat,
            "satisfiable Boolean AC string control must not become UNSAT: {assertion}"
        );
    }
}

#[test]
fn exact_source_one_code_point_replace_views_refute_noetzli_families() {
    let mut assertions = Vec::new();
    for base in [r#""A""#, r#""B""#] {
        assertions.push(format!(
            r#"(not (= (str.substr {base} 0 (str.indexof "A" "" z))
                       (str.at {base} (- 1 z))))"#
        ));
        for replacement in [r#""A""#, r#""B""#] {
            assertions.push(format!(
                r"(not (= (str.substr (str.replace {base} x {replacement}) 1 z)
                           (str.substr {base} (str.len x) z)))"
            ));
            assertions.push(format!(
                r#"(not (= (str.substr (str.replace {base} x {replacement}) z z)
                           (str.substr {base} 0 (str.indexof "A" x z))))"#
            ));
        }
    }
    for needle in [r#""A""#, r#""B""#] {
        for replacement in [r#""A""#, r#""B""#] {
            assertions.push(format!(
                r#"(not (= (str.replace "" (str.replace x {needle} "") {replacement})
                           (str.at {replacement} (str.indexof {needle} x 0))))"#
            ));
        }
    }

    assert_eq!(assertions.len(), 14);
    for assertion in assertions {
        let input = format!(
            r"(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun z () Int)
(assert {assertion})
(check-sat)
"
        );
        let script = parse_script(&input).expect("parse one-code-point replacement view theorem");
        assert!(
            script.source_string_semantic_unsat,
            "one-code-point replacement view must refute {assertion}"
        );
        assert_eq!(
            solve_smtlib(&input, &config())
                .expect("solve one-code-point replacement view theorem")
                .result,
            CheckResult::Unsat,
            "one-code-point replacement view must survive the bounded-string gate: {assertion}"
        );
    }
}

#[test]
fn exact_source_one_code_point_replace_views_decline_satisfiable_controls() {
    for assertion in [
        r#"(not (= (str.substr (str.replace "A" x "BC") 1 z)
                   (str.substr "A" (str.len x) z)))"#,
        r#"(not (= (str.substr (str.replace "AB" x "C") 1 z)
                   (str.substr "AB" (str.len x) z)))"#,
        r#"(not (= (str.substr (str.replace "A" x "B") z z)
                   (str.substr "A" 0 (str.indexof "AA" x z))))"#,
        r#"(not (= (str.replace "" (str.replace x "AB" "") "C")
                   (str.at "C" (str.indexof "AB" x 0))))"#,
        r#"(not (= (str.replace "" (str.replace x "A" "") "BC")
                   (str.at "BC" (str.indexof "A" x 0))))"#,
    ] {
        let input = format!(
            r"(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun z () Int)
(assert {assertion})
(check-sat)
"
        );
        let script = parse_script(&input).expect("parse one-code-point replacement view control");
        assert!(
            !script.source_string_semantic_unsat,
            "satisfiable one-code-point replacement view control must decline: {assertion}"
        );
        assert_ne!(
            solve_smtlib(&input, &config())
                .expect("solve one-code-point replacement view control")
                .result,
            CheckResult::Unsat,
            "satisfiable one-code-point replacement view control must not become UNSAT: {assertion}"
        );
    }
}

#[test]
fn exact_source_one_code_point_deletion_languages_refute_noetzli_families() {
    let mut assertions = Vec::new();
    for (needle, other) in [(r#""A""#, r#""B""#), (r#""B""#, r#""A""#)] {
        assertions.push(format!(
            r#"(not (= (str.prefixof x (str.replace {needle} x "")) (= x "")))"#
        ));
        assertions.push(format!(
            r#"(not (= (str.suffixof x (str.replace {needle} x "")) (= x "")))"#
        ));
        assertions.push(format!(
            r#"(not (= (= {needle} (str.replace x {needle} ""))
                       (= x (str.++ {needle} {needle}))))"#
        ));
        assertions.push(format!(
            r#"(not (= (str.suffixof {needle} (str.replace x {needle} ""))
                       (str.suffixof {needle} (str.replace x {needle} {other}))))"#
        ));
        assertions.push(format!(
            r#"(not (= (str.contains {needle} (str.replace x {needle} ""))
                       (str.prefixof x (str.++ {needle} {needle}))))"#
        ));
        assertions.push(format!(
            r#"(not (= (= "" (str.replace x {needle} ""))
                       (str.prefixof x {needle})))"#
        ));
        assertions.push(format!(
            r#"(not (= (str.prefixof (str.++ {needle} {needle}) x)
                       (str.prefixof {needle} (str.replace x {needle} ""))))"#
        ));
    }
    assertions.push(
        r#"(not (= (str.contains "B" (str.replace x "A" ""))
                   (str.contains "A" (str.replace x "B" ""))))"#
            .to_owned(),
    );

    assert_eq!(assertions.len(), 15);
    for assertion in assertions {
        let input = format!(
            r"(set-logic QF_SLIA)
(declare-fun x () String)
(assert {assertion})
(check-sat)
"
        );
        let script = parse_script(&input).expect("parse one-code-point deletion theorem");
        assert!(
            script.source_string_semantic_unsat,
            "one-code-point deletion theorem must refute {assertion}"
        );
        assert_eq!(
            solve_smtlib(&input, &config())
                .expect("solve one-code-point deletion theorem")
                .result,
            CheckResult::Unsat,
            "one-code-point deletion theorem must survive the bounded-string gate: {assertion}"
        );
    }
}

#[test]
fn exact_source_one_code_point_deletion_languages_decline_satisfiable_controls() {
    for assertion in [
        r#"(not (= (str.prefixof x (str.replace "AA" x "")) (= x "")))"#,
        r#"(not (= (str.suffixof x (str.replace "AA" x "")) (= x "")))"#,
        r#"(not (= (str.suffixof "A" (str.replace x "A" ""))
                   (str.suffixof "A" (str.replace x "A" "BA"))))"#,
        r#"(not (= (= "A" (str.replace x "A" "B")) (= x "AA")))"#,
    ] {
        let input = format!(
            r"(set-logic QF_SLIA)
(declare-fun x () String)
(assert {assertion})
(check-sat)
"
        );
        let script = parse_script(&input).expect("parse one-code-point deletion control");
        assert!(
            !script.source_string_semantic_unsat,
            "satisfiable one-code-point deletion control must decline: {assertion}"
        );
        assert_ne!(
            solve_smtlib(&input, &config())
                .expect("solve one-code-point deletion control")
                .result,
            CheckResult::Unsat,
            "satisfiable one-code-point deletion control must not become UNSAT: {assertion}"
        );
    }
}

#[test]
fn exact_source_replace_emptiness_boolean_normalization_refutes_noetzli_families() {
    let assertions = [
        r#"(not (= (= "" (str.replace x y "B")) (= "" (str.replace x y "A"))))"#,
        r#"(not (= (str.contains "" (str.replace x y "B")) (= "" (str.replace x y "A"))))"#,
        r#"(not (= (= "" (str.replace x "B" "A")) (= x "")))"#,
        r#"(not (= (str.replace (str.replace "B" x "") "B" "A") (str.replace "A" (str.replace "B" x "A") "")))"#,
        r#"(not (= (str.replace "A" (str.at "B" z) "A") (str.replace "A" (str.at "A" z) "A")))"#,
        r#"(not (= (str.replace "A" (str.substr "B" 0 z) "A") (str.replace "A" (str.substr "A" 0 z) "A")))"#,
        r#"(not (= (str.replace "A" (str.replace x y "B") "A") (str.replace "A" (str.replace x y "A") "A")))"#,
        r#"(not (= (str.replace "A" (str.replace "A" x "A") x) (str.++ x (str.replace "" x "A"))))"#,
        r#"(not (= (str.replace "A" (str.replace "A" x "A") y) (str.replace y (str.++ x y) "A")))"#,
        r#"(not (= (str.replace "A" (str.replace "A" x "B") "") (str.at "A" (str.indexof "A" x 0))))"#,
        r#"(not (= (str.replace "A" (str.replace "B" x y) y) "A"))"#,
        r#"(not (= (str.replace "A" (str.replace "" x y) "") (str.replace "A" (str.++ x y) x)))"#,
        r#"(not (= (str.replace "A" (str.replace "" x "B") y) (str.replace "A" (str.replace "" x y) y)))"#,
        r#"(not (= (str.replace "B" (str.at "B" z) "B") (str.replace "B" (str.at "A" z) "B")))"#,
        r#"(not (= (str.replace "B" (str.substr "B" 0 z) "B") (str.replace "B" (str.substr "A" 0 z) "B")))"#,
        r#"(not (= (str.replace "B" (str.replace x y "B") "B") (str.replace "B" (str.replace x y "A") "B")))"#,
        r#"(not (= (str.replace "B" (str.replace "A" x y) y) "B"))"#,
        r#"(not (= (str.replace "B" (str.replace "B" x "A") x) (str.++ x (str.replace "" x "B"))))"#,
        r#"(not (= (str.replace "B" (str.replace "B" x "A") "") (str.at "B" (str.indexof "B" x 0))))"#,
        r#"(not (= (str.replace "B" (str.replace "B" x "B") y) (str.replace y (str.++ x y) "B")))"#,
        r#"(not (= (str.replace "B" (str.replace "" x y) "") (str.replace "B" (str.++ x y) x)))"#,
        r#"(not (= (str.replace "B" (str.replace "" x "A") y) (str.replace "B" (str.replace "" x y) y)))"#,
        r#"(not (= (str.replace "" (str.at "A" z) "A") (str.replace "A" (str.at "A" z) "")))"#,
        r#"(not (= (str.replace "" (str.at "A" z) "B") (str.replace "B" (str.at "B" z) "")))"#,
        r#"(not (= (str.replace "" (str.at "B" z) x) (str.replace "" (str.at "A" z) x)))"#,
        r#"(not (= (str.replace "" (str.replace x y "A") x) ""))"#,
        r#"(not (= (str.replace "" (str.replace x y "A") y) (str.replace "" x y)))"#,
        r#"(not (= (str.replace "" (str.replace x y "B") x) ""))"#,
        r#"(not (= (str.replace "" (str.replace x y "B") y) (str.replace "" x y)))"#,
        r#"(not (= (str.replace "" (str.replace x y "B") "A") (str.replace "" (str.replace x y "A") "A")))"#,
        r#"(not (= (str.replace "" (str.replace x y "B") "B") (str.replace "" (str.replace x y "A") "B")))"#,
        r#"(not (= (str.replace "" (str.replace x "A" y) y) (str.replace "" x y)))"#,
        r#"(not (= (str.replace "" (str.replace x "A" "B") y) (str.replace "" x y)))"#,
        r#"(not (= (str.replace "" (str.replace x "B" y) y) (str.replace "" x y)))"#,
        r#"(not (= (str.replace "" (str.replace x "B" "A") y) (str.replace "" x y)))"#,
        r#"(not (= (str.replace "" (str.replace y x "") y) (str.replace "" (str.replace x y "") x)))"#,
        r#"(not (= (str.replace "" (str.replace "A" x y) x) (str.replace "" (str.replace x "A" y) x)))"#,
        r#"(not (= (str.replace "" (str.replace "A" x y) y) ""))"#,
        r#"(not (= (str.replace "" (str.replace "A" x y) "A") (str.replace "" (str.replace x "A" y) x)))"#,
        r#"(not (= (str.replace "" (str.replace "B" x y) x) (str.replace "" (str.replace x "B" y) x)))"#,
        r#"(not (= (str.replace "" (str.replace "B" x y) y) ""))"#,
        r#"(not (= (str.replace "" (str.replace "B" x y) "B") (str.replace "" (str.replace x "B" y) x)))"#,
        r#"(not (= (str.replace "" (str.replace "" x y) x) x))"#,
        r#"(not (= (str.replace "" (str.replace "" x y) y) (str.replace y (str.++ x y) x)))"#,
        r#"(not (= (str.replace "" (str.replace "" x "A") y) (str.replace "" (str.replace "" x y) y)))"#,
        r#"(not (= (str.replace "" (str.replace "" x "B") y) (str.replace "" (str.replace "" x y) y)))"#,
        r#"(not (= (str.replace (str.replace "A" x "") "A" "B") (str.replace "B" (str.replace "A" x "B") "")))"#,
    ];

    assert_eq!(assertions.len(), 47);
    for (index, assertion) in assertions.into_iter().enumerate() {
        let input = format!(
            r"(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun y () String)
(declare-fun z () Int)
(assert {assertion})
(check-sat)
"
        );
        let script = parse_script(&input).expect("parse replacement-emptiness theorem");
        assert!(
            script.source_string_semantic_unsat,
            "replacement-emptiness theorem must refute {assertion}"
        );
        if matches!(index, 0 | 25 | 46) {
            assert_eq!(
                solve_smtlib(&input, &config())
                    .expect("solve replacement-emptiness theorem")
                    .result,
                CheckResult::Unsat,
                "replacement-emptiness theorem must survive the bounded-string gate: {assertion}"
            );
        }
    }
}

#[test]
fn exact_source_replace_emptiness_boolean_normalization_declines_satisfiable_controls() {
    for assertion in [
        r#"(not (= (= "" (str.replace x y r)) (= x "")))"#,
        r#"(not (= (str.replace "" (str.replace x y "") x) ""))"#,
        r#"(not (= (= x "") (= x "A")))"#,
        r#"(not (= (str.replace "" (str.replace "" x "A") y) y))"#,
    ] {
        let input = format!(
            r"(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun y () String)
(declare-fun r () String)
(assert {assertion})
(check-sat)
"
        );
        let script = parse_script(&input).expect("parse replacement-emptiness control");
        assert!(
            !script.source_string_semantic_unsat,
            "satisfiable replacement-emptiness control must decline: {assertion}"
        );
        assert_ne!(
            solve_smtlib(&input, &config())
                .expect("solve replacement-emptiness control")
                .result,
            CheckResult::Unsat,
            "satisfiable replacement-emptiness control must not become UNSAT: {assertion}"
        );
    }
}

#[test]
fn exact_source_self_replacement_boolean_equivalences_refute_noetzli_families() {
    let assertions = [
        r"(not (= (= x (str.replace y x y)) (= x y)))",
        r"(not (= (str.prefixof x (str.replace y x y)) (str.prefixof x y)))",
        r"(not (= (str.suffixof x (str.replace y x y)) (str.suffixof x y)))",
        r"(not (= (str.contains x (str.replace y x y)) (str.contains x y)))",
        r"(not (= (str.prefixof (str.replace x y x) y) (str.prefixof x y)))",
        r"(not (= (str.suffixof (str.replace x y x) y) (str.suffixof x y)))",
        r#"(not (= (= "" (str.replace x "A" y)) (str.prefixof x (str.replace "" y "A"))))"#,
        r#"(not (= (str.contains "" (str.replace x "A" y)) (str.prefixof x (str.replace "" y "A"))))"#,
        r#"(not (= (= "" (str.replace x "B" y)) (str.prefixof x (str.replace "" y "B"))))"#,
        r#"(not (= (str.contains "" (str.replace x "B" y)) (str.prefixof x (str.replace "" y "B"))))"#,
        r#"(not (= (str.contains (str.replace "A" x "") x) (= x "")))"#,
        r#"(not (= (str.contains (str.replace "B" x "") x) (= x "")))"#,
    ];

    assert_eq!(assertions.len(), 12);
    for (index, assertion) in assertions.into_iter().enumerate() {
        let input = format!(
            r"(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun y () String)
(assert {assertion})
(check-sat)
"
        );
        let script = parse_script(&input).expect("parse self-replacement/Boolean theorem");
        assert!(
            script.source_string_semantic_unsat,
            "self-replacement/Boolean theorem must refute {assertion}"
        );
        if matches!(index, 0 | 6 | 11) {
            assert_eq!(
                solve_smtlib(&input, &config())
                    .expect("solve self-replacement/Boolean theorem")
                    .result,
                CheckResult::Unsat,
                "self-replacement/Boolean theorem must survive the bounded-string gate: {assertion}"
            );
        }
    }
}

#[test]
fn exact_source_self_replacement_boolean_equivalences_decline_satisfiable_controls() {
    for assertion in [
        r"(not (= (str.prefixof z (str.replace y x y)) (str.prefixof z y)))",
        r"(not (= (= y (str.replace y x y)) (= x y)))",
        r#"(not (= (= "" (str.replace x "A" y)) (= x "")))"#,
        r#"(not (= (str.contains (str.replace "AA" x "") x) (= x "")))"#,
    ] {
        let input = format!(
            r"(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun y () String)
(declare-fun z () String)
(assert {assertion})
(check-sat)
"
        );
        let script = parse_script(&input).expect("parse self-replacement/Boolean control");
        assert!(
            !script.source_string_semantic_unsat,
            "satisfiable self-replacement/Boolean control must decline: {assertion}"
        );
        assert_ne!(
            solve_smtlib(&input, &config())
                .expect("solve self-replacement/Boolean control")
                .result,
            CheckResult::Unsat,
            "satisfiable self-replacement/Boolean control must not become UNSAT: {assertion}"
        );
    }
}

#[test]
fn exact_source_head_totality_views_refute_noetzli_families() {
    let assertions = [
        r#"(not (= (str.prefixof "A" (str.++ x "A")) (str.contains "A" (str.at x 0))))"#,
        r#"(not (= (str.prefixof "B" (str.++ x "B")) (str.contains "B" (str.at x 0))))"#,
        r#"(not (= (= "" (str.at x 0)) (= x "")))"#,
        r#"(not (= (str.contains "" (str.at x 0)) (= x "")))"#,
        r#"(not (= (= "" (str.at x 1)) (= x (str.at x 0))))"#,
        r#"(not (= (str.contains "" (str.at x 1)) (= x (str.at x 0))))"#,
        r#"(not (= (str.substr "A" (str.indexof "" x 0) z) (str.substr "A" (str.len x) z)))"#,
        r#"(not (= (str.substr "B" (str.indexof "" x 0) z) (str.substr "B" (str.len x) z)))"#,
        r"(not (= (str.substr (str.at x 0) 0 z) (str.at (str.substr x 0 z) 0)))",
        r"(not (= (str.substr (str.at x 1) 0 z) (str.at (str.substr x 1 z) 0)))",
        r"(not (= (str.substr (str.at x z) 0 z) (str.at (str.substr x z z) 0)))",
        r#"(not (= (str.replace x (str.at x 0) "") (str.substr x 1 (str.len x))))"#,
        r#"(not (= (str.replace "A" (str.at x 0) "A") (str.replace "A" x "A")))"#,
        r#"(not (= (str.at "A" (str.len x)) (str.replace "" x "A")))"#,
        r#"(not (= (str.replace "B" (str.at x 0) "B") (str.replace "B" x "B")))"#,
        r#"(not (= (str.replace "" (str.at x 0) x) ""))"#,
        r#"(not (= (str.replace "" (str.at x 0) y) (str.replace "" x y)))"#,
        r#"(not (= (str.at "B" (str.len x)) (str.replace "" x "B")))"#,
        r#"(not (= (str.replace (str.at x 0) "A" "B") (str.at (str.replace x "A" "B") 0)))"#,
        r#"(not (= (str.replace (str.at x 0) "B" "A") (str.at (str.replace x "B" "A") 0)))"#,
    ];

    assert_eq!(assertions.len(), 20);
    for (index, assertion) in assertions.into_iter().enumerate() {
        let input = format!(
            r"(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun y () String)
(declare-fun z () Int)
(assert {assertion})
(check-sat)
"
        );
        let script = parse_script(&input).expect("parse head-totality theorem");
        assert!(
            script.source_string_semantic_unsat,
            "head-totality theorem must refute {assertion}"
        );
        if matches!(index, 0 | 11 | 19) {
            assert_eq!(
                solve_smtlib(&input, &config())
                    .expect("solve head-totality theorem")
                    .result,
                CheckResult::Unsat,
                "head-totality theorem must survive the bounded-string gate: {assertion}"
            );
        }
    }
}

#[test]
fn exact_source_head_totality_views_decline_satisfiable_controls() {
    for assertion in [
        r#"(not (= (= "" (str.at x (- 1))) (= x (str.substr x 0 (- 1)))))"#,
        r"(not (= (str.substr (str.at x i) 1 n) (str.at (str.substr x i n) 0)))",
        r#"(not (= (str.replace x (str.at x 1) "") (str.substr x 1 (str.len x))))"#,
        r#"(not (= (str.replace (str.at x 0) "A" "BC") (str.at (str.replace x "A" "BC") 0)))"#,
        r"(not (= (str.len x) 1))",
    ] {
        let input = format!(
            r"(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun i () Int)
(declare-fun n () Int)
(assert {assertion})
(check-sat)
"
        );
        let script = parse_script(&input).expect("parse head-totality control");
        assert!(
            !script.source_string_semantic_unsat,
            "satisfiable head-totality control must decline: {assertion}"
        );
        assert_ne!(
            solve_smtlib(&input, &config())
                .expect("solve head-totality control")
                .result,
            CheckResult::Unsat,
            "satisfiable head-totality control must not become UNSAT: {assertion}"
        );
    }
}

#[test]
fn exact_source_one_code_point_paths_refute_noetzli_families() {
    let assertions = [
        r#"(not (= (str.replace "A" (str.substr "A" 0 z) "") (str.substr "A" 0 (- 1 z))))"#,
        r#"(not (= (str.replace "" (str.substr "A" 0 z) x) (str.replace "" (str.substr x 0 z) x)))"#,
        r#"(not (= (str.replace "A" (str.++ x "A") x) (str.substr "A" 0 (str.len x))))"#,
        r#"(not (= (str.replace "" (str.replace "" x "A") "B") (str.substr "B" 0 (str.len x))))"#,
        r#"(not (= (= x (str.replace x "A" "")) (= x (str.replace x "A" "B"))))"#,
        r#"(not (= (= x (str.replace x "B" "")) (= x (str.replace x "B" "A"))))"#,
        r#"(not (= (not (str.contains x "A")) (= x (str.replace x "A" "B"))))"#,
        r#"(not (= (not (str.contains x "B")) (= x (str.replace x "B" "A"))))"#,
        r#"(not (= (str.prefixof "A" (str.replace x "A" "B")) false))"#,
        r#"(not (= (str.prefixof "B" (str.replace x "A" "B"))
                    (str.prefixof "A" (str.replace x "B" "A"))))"#,
        r#"(not (= (str.prefixof "B" (str.replace x "B" "A")) false))"#,
        r#"(not (= (str.replace x (str.replace x "A" "B") "A")
                    (str.replace x (str.replace x "A" x) "A")))"#,
        r#"(not (= (str.replace x (str.replace x "B" "A") "B")
                    (str.replace x (str.replace x "B" x) "B")))"#,
        r#"(not (= (str.replace "A" (str.++ x "A") "") (str.substr "A" 0 (str.len x))))"#,
        r#"(not (= (str.replace "B" (str.substr "B" 0 z) "") (str.substr "B" 0 (- 1 z))))"#,
        r#"(not (= (str.replace "B" (str.++ x "B") x) (str.substr "B" 0 (str.len x))))"#,
        r#"(not (= (str.replace "B" (str.++ x "B") "") (str.substr "B" 0 (str.len x))))"#,
        r#"(not (= (str.replace "" (str.substr "A" 0 z) "A") (str.substr "A" 0 (- 1 z))))"#,
        r#"(not (= (str.replace "" (str.substr "A" 0 z) "B") (str.substr "B" 0 (- 1 z))))"#,
        r#"(not (= (str.replace "" (str.substr "B" 0 z) x) (str.replace "" (str.substr x 0 z) x)))"#,
    ];

    assert_eq!(assertions.len(), 20);
    for (index, assertion) in assertions.into_iter().enumerate() {
        let input = format!(
            r"(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun z () Int)
(assert {assertion})
(check-sat)
"
        );
        let script = parse_script(&input).expect("parse one-code-point path theorem");
        assert!(
            script.source_string_semantic_unsat,
            "one-code-point path theorem must refute {assertion}"
        );
        if matches!(index, 0 | 4 | 9 | 19) {
            assert_eq!(
                solve_smtlib(&input, &config())
                    .expect("solve one-code-point path theorem")
                    .result,
                CheckResult::Unsat,
                "one-code-point path theorem must survive the bounded-string gate: {assertion}"
            );
        }
    }
}

#[test]
fn exact_source_one_code_point_paths_decline_satisfiable_controls() {
    for assertion in [
        r#"(not (= (= x (str.replace x "A" "")) (= x (str.replace x "B" ""))))"#,
        r#"(not (= (str.prefixof "A" (str.replace x "A" "A")) false))"#,
        r#"(not (= (str.replace "A" (str.substr "A" 1 z) "") (str.substr "A" 0 (- 1 z))))"#,
        r#"(not (= (str.replace "A" (str.++ x "A") x) (str.substr "A" 0 (str.len y))))"#,
    ] {
        let input = format!(
            r"(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun y () String)
(declare-fun z () Int)
(assert {assertion})
(check-sat)
"
        );
        let script = parse_script(&input).expect("parse one-code-point path control");
        assert!(
            !script.source_string_semantic_unsat,
            "satisfiable one-code-point path control must decline: {assertion}"
        );
        assert_ne!(
            solve_smtlib(&input, &config())
                .expect("solve one-code-point path control")
                .result,
            CheckResult::Unsat,
            "satisfiable one-code-point path control must not become UNSAT: {assertion}"
        );
    }
}

#[test]
fn exact_source_from_int_views_refute_noetzli_families() {
    let assertions = [
        r#"(not (= (str.contains "B" (str.from_int z)) (str.contains "A" (str.from_int z))))"#,
        r#"(not (= (= "" (str.from_int z)) (str.contains "A" (str.from_int z))))"#,
        r#"(not (= (str.contains "" (str.from_int z)) (str.contains "A" (str.from_int z))))"#,
        r#"(not (= (str.substr (str.from_int z) z z) ""))"#,
        r#"(not (= (str.replace "" (str.from_int z) "A") (str.substr "A" 0 (- 0 z))))"#,
        r#"(not (= (str.replace "" (str.from_int z) "B") (str.substr "B" 0 (- 0 z))))"#,
    ];

    for assertion in assertions {
        let input = format!(
            r"(set-logic QF_SLIA)
(declare-fun z () Int)
(assert {assertion})
(check-sat)
"
        );
        let script = parse_script(&input).expect("parse symbolic from-int theorem");
        assert!(
            script.source_string_semantic_unsat,
            "symbolic from-int theorem must refute {assertion}"
        );
        assert_eq!(
            solve_smtlib(&input, &config())
                .expect("solve symbolic from-int theorem")
                .result,
            CheckResult::Unsat,
            "symbolic from-int theorem must survive the bounded-string gate: {assertion}"
        );
    }
}

#[test]
fn exact_source_from_int_views_decline_satisfiable_controls() {
    for assertion in [
        r#"(not (= (str.contains "1" (str.from_int z)) (str.contains "A" (str.from_int z))))"#,
        r"(not (= (str.contains (str.from_int z) x) (str.suffixof x (str.from_int z))))",
        r#"(not (= (str.substr (str.from_int z) 0 z) ""))"#,
        r#"(not (= (str.replace "" (str.from_int z) "A") (str.substr "A" 0 (- 1 z))))"#,
    ] {
        let input = format!(
            r"(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun z () Int)
(assert {assertion})
(check-sat)
"
        );
        let script = parse_script(&input).expect("parse symbolic from-int control");
        assert!(
            !script.source_string_semantic_unsat,
            "satisfiable symbolic from-int control must decline: {assertion}"
        );
        assert_ne!(
            solve_smtlib(&input, &config())
                .expect("solve symbolic from-int control")
                .result,
            CheckResult::Unsat,
            "satisfiable symbolic from-int control must not become UNSAT: {assertion}"
        );
    }
}

#[test]
fn exact_source_correlated_substring_index_views_refute_noetzli_family() {
    let assertions = [
        r"(not (= (str.substr x z (- 1 z)) (str.at x (str.indexof x x z))))",
        r#"(not (= (str.substr x (- 1 z) z) (str.substr x 0 (str.indexof "A" "" z))))"#,
        r#"(not (= (str.substr "A" 0 (str.indexof x "A" 1))
                    (str.at x (str.indexof x "A" 1))))"#,
        r#"(not (= (str.substr "B" 0 (str.indexof x "B" 1))
                    (str.at x (str.indexof x "B" 1))))"#,
        r"(not (= (str.substr (str.substr x 0 z) 1 z) (str.substr x 1 (- z 1))))",
    ];

    for assertion in assertions {
        let input = format!(
            r"(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun z () Int)
(assert {assertion})
(check-sat)
"
        );
        let script = parse_script(&input).expect("parse correlated substring/index theorem");
        assert!(
            script.source_string_semantic_unsat,
            "correlated substring/index theorem must refute {assertion}"
        );
        assert_eq!(
            solve_smtlib(&input, &config())
                .expect("solve correlated substring/index theorem")
                .result,
            CheckResult::Unsat,
            "correlated substring/index theorem must survive the bounded-string gate: {assertion}"
        );
    }
}

#[test]
fn exact_source_correlated_substring_index_views_decline_satisfiable_controls() {
    for assertion in [
        r"(not (= (str.substr x z (- 2 z)) (str.at x (str.indexof x x z))))",
        r#"(not (= (str.substr x (- 1 z) z) (str.substr x 0 (str.indexof "AA" "" z))))"#,
        r#"(not (= (str.substr "A" 0 (str.indexof x "B" 1))
                    (str.at x (str.indexof x "B" 1))))"#,
        r"(not (= (str.substr (str.substr x 1 z) 1 z) (str.substr x 1 (- z 1))))",
    ] {
        let input = format!(
            r"(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun z () Int)
(assert {assertion})
(check-sat)
"
        );
        let script = parse_script(&input).expect("parse correlated substring/index control");
        assert!(
            !script.source_string_semantic_unsat,
            "satisfiable correlated substring/index control must decline: {assertion}"
        );
        assert_ne!(
            solve_smtlib(&input, &config())
                .expect("solve correlated substring/index control")
                .result,
            CheckResult::Unsat,
            "satisfiable correlated substring/index control must not become UNSAT: {assertion}"
        );
    }
}

#[test]
fn exact_source_first_occurrence_algebra_refutes_noetzli_families() {
    let assertions = [
        r#"(not (= (str.++ (str.replace "" x y) x) (str.++ x (str.replace "" x y))))"#,
        r#"(not (= (str.++ (str.replace "" x y) y) (str.++ y (str.replace "" x y))))"#,
        r"(not (= (str.replace x y (str.replace y x y)) x))",
        r#"(not (= (str.replace x (str.replace "A" y x) "A") (str.replace x (str.replace y "A" x) y)))"#,
        r#"(not (= (str.replace x (str.replace "B" y x) "B") (str.replace x (str.replace y "B" x) y)))"#,
        r#"(not (= (str.replace (str.substr x 0 z) "A" "B") (str.substr (str.replace x "A" "B") 0 z)))"#,
        r#"(not (= (str.replace (str.substr x 0 z) "B" "A") (str.substr (str.replace x "B" "A") 0 z)))"#,
        r#"(not (= (str.replace (str.++ "A" x) x "A") "AA"))"#,
        r#"(not (= (str.replace (str.++ "A" x) x "") "A"))"#,
        r#"(not (= (str.replace (str.++ "B" x) x "B") "BB"))"#,
        r#"(not (= (str.replace (str.++ "B" x) x "") "B"))"#,
        r"(not (= (str.replace (str.replace x y x) x y) (str.replace x (str.replace x y x) y)))",
        r#"(not (= (str.replace (str.replace x "A" x) "A" y) (str.replace x "A" (str.replace x "A" y))))"#,
        r#"(not (= (str.replace (str.replace x "A" "B") x "B") (str.replace (str.replace x "A" x) x "B")))"#,
        r#"(not (= (str.replace (str.replace x "A" "") x "") (str.replace (str.replace x "A" x) x "")))"#,
        r#"(not (= (str.replace (str.replace x "B" x) "B" y) (str.replace x "B" (str.replace x "B" y))))"#,
        r#"(not (= (str.replace (str.replace x "B" "A") x "A") (str.replace (str.replace x "B" x) x "A")))"#,
        r#"(not (= (str.replace (str.replace x "B" "") x "") (str.replace (str.replace x "B" x) x "")))"#,
        r#"(not (= (str.replace (str.replace x "B" "") "A" "") (str.replace (str.replace x "A" "") "B" "")))"#,
        r#"(not (= (str.replace (str.replace "A" x "A") "A" y) (str.++ y (str.replace "" x "A"))))"#,
        r#"(not (= (str.replace (str.replace "A" x "B") "B" y) (str.replace "A" x y)))"#,
        r#"(not (= (str.replace (str.replace "B" x "A") "A" y) (str.replace "B" x y)))"#,
        r#"(not (= (str.replace (str.replace "B" x "B") "B" y) (str.++ y (str.replace "" x "B"))))"#,
    ];

    assert_eq!(assertions.len(), 23);
    for (index, assertion) in assertions.into_iter().enumerate() {
        let input = format!(
            r"(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun y () String)
(declare-fun z () Int)
(assert {assertion})
(check-sat)
"
        );
        let script = parse_script(&input).expect("parse first-occurrence algebra theorem");
        assert!(
            script.source_string_semantic_unsat,
            "first-occurrence algebra theorem must refute {assertion}"
        );
        if matches!(index, 0 | 4 | 10 | 18 | 22) {
            assert_eq!(
                solve_smtlib(&input, &config())
                    .expect("solve first-occurrence algebra theorem")
                    .result,
                CheckResult::Unsat,
                "first-occurrence algebra theorem must survive the bounded-string gate: {assertion}"
            );
        }
    }
}

#[test]
fn exact_source_first_occurrence_algebra_declines_counterexamples() {
    for assertion in [
        r#"(not (= (str.replace "AAA" (str.replace "AA" "A" "AA") "AA") "AAA"))"#,
        r#"(not (= (str.replace (str.replace "ABBA" "BA" "ABBA") "BA" "ABBA") (str.replace "ABBA" "BA" (str.replace "ABBA" "BA" "ABBA"))))"#,
        r#"(not (= (str.replace (str.replace "ABBA" "BA" "ABBA") "BA" "A") (str.replace "ABBA" "BA" (str.replace "ABBA" "BA" "A"))))"#,
        r#"(not (= (str.replace (str.replace "ABBA" "BA" "ABBA") "BA" "B") (str.replace "ABBA" "BA" (str.replace "ABBA" "BA" "B"))))"#,
        r#"(not (= (str.replace (str.replace "ABBA" "BA" "ABBA") "BA" "") (str.replace "ABBA" "BA" (str.replace "ABBA" "BA" ""))))"#,
        r#"(not (= (str.replace (str.substr "AB" 0 1) "AB" "CD") (str.substr (str.replace "AB" "AB" "CD") 0 1)))"#,
        r#"(not (= (str.replace (str.++ "A" "") "" "B") "AB"))"#,
        r#"(not (= (str.replace (str.replace "A" "B" "A") "A" "") (str.replace "A" "B" "")))"#,
    ] {
        let input = format!(
            r"(set-logic QF_SLIA)
(assert {assertion})
(check-sat)
"
        );
        let script = parse_script(&input).expect("parse first-occurrence algebra control");
        assert!(
            !script.source_string_semantic_unsat,
            "satisfiable first-occurrence algebra control must decline: {assertion}"
        );
        assert_ne!(
            solve_smtlib(&input, &config())
                .expect("solve first-occurrence algebra control")
                .result,
            CheckResult::Unsat,
            "satisfiable first-occurrence algebra control must not become UNSAT: {assertion}"
        );
    }
}

/// Soundness-negative gate for `exact_singleton_outer_source_identity`.
///
/// The schema `replace(replace(S, a, r), S, X) = replace(replace(S, a, S), S, X)`
/// is valid **only when `X == r`**. When `a` occurs in `S` at first index `i`,
/// `replace(S, a, r)` cannot contain `S`, so the left side stays
/// `S[0..i] ++ r ++ S[i+1..]`; `replace(S, a, S)` does contain `S` at exactly
/// `i`, so the right side is `S[0..i] ++ X ++ S[i+1..]`. They agree iff
/// `X == r`.
///
/// The matcher originally omitted that condition and folded these four
/// satisfiable disequalities to `true`, producing a wrong `unsat` through the
/// public `solve_smtlib` front door. cvc5 1.3.4 and z3 both answer `sat` on
/// every case below.
///
/// The exhaustive identity test could not catch this: it instantiates the
/// schema with one `replacement` binding reused in both positions, which is
/// exactly the `X == r` case the matcher is allowed to accept. Only perturbing
/// an *accepted* schema away from its side condition exposes the gap.
#[test]
fn singleton_outer_source_identity_declines_mismatched_replacements() {
    for (assertion, witness) in [
        (
            r#"(not (= (str.replace (str.replace x "A" "") x "B") (str.replace (str.replace x "A" x) x "B")))"#,
            "A",
        ),
        (
            r#"(not (= (str.replace (str.replace x "A" "B") x "") (str.replace (str.replace x "A" x) x "")))"#,
            "A",
        ),
        (
            r#"(not (= (str.replace (str.replace x "B" "") x "A") (str.replace (str.replace x "B" x) x "A")))"#,
            "B",
        ),
        (
            r#"(not (= (str.replace (str.replace x "B" "A") x "") (str.replace (str.replace x "B" x) x "")))"#,
            "B",
        ),
    ] {
        let input = format!(
            r"(set-logic QF_SLIA)
(declare-fun x () String)
(assert {assertion})
(check-sat)
"
        );
        let script = parse_script(&input).expect("parse mismatched-replacement mutant");
        assert!(
            !script.source_string_semantic_unsat,
            "mismatched outer/inner replacement must not fold to true \
             (satisfiable at x = {witness:?}): {assertion}"
        );
        assert_ne!(
            solve_smtlib(&input, &config())
                .expect("solve mismatched-replacement mutant")
                .result,
            CheckResult::Unsat,
            "mismatched outer/inner replacement must never return UNSAT \
             (satisfiable at x = {witness:?}): {assertion}"
        );
    }
}

#[test]
fn exact_source_first_occurrence_predicates_refute_noetzli_families() {
    let assertions = [
        r#"(not (= (str.prefixof x (str.++ "A" x)) (str.suffixof x (str.++ x "A"))))"#,
        r#"(not (= (str.prefixof x (str.++ "B" x)) (str.suffixof x (str.++ x "B"))))"#,
        r#"(not (= (str.contains (str.replace x y "A") x) (str.suffixof x (str.replace x y "A"))))"#,
        r#"(not (= (str.contains (str.replace x y "B") x) (str.suffixof x (str.replace x y "B"))))"#,
        r#"(not (= (str.contains (str.replace x y "") "A") (str.contains (str.replace x y "B") "A")))"#,
        r#"(not (= (str.contains (str.replace x y "") "B") (str.contains (str.replace x y "A") "B")))"#,
        r#"(not (= (str.contains (str.replace x "A" y) y) (str.contains (str.replace x y "A") "A")))"#,
        r#"(not (= (str.contains (str.replace x "B" y) y) (str.contains (str.replace x y "B") "B")))"#,
        r#"(not (= (str.suffixof (str.replace x "A" "") x) (str.prefixof x (str.replace x "A" x))))"#,
        r#"(not (= (str.suffixof (str.replace x "B" "") x) (str.prefixof x (str.replace x "B" x))))"#,
    ];

    for (index, assertion) in assertions.into_iter().enumerate() {
        let input = format!(
            r"(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun y () String)
(assert {assertion})
(check-sat)
"
        );
        let script = parse_script(&input).expect("parse first-occurrence predicate theorem");
        assert!(
            script.source_string_semantic_unsat,
            "first-occurrence predicate theorem must refute {assertion}"
        );
        if matches!(index, 0 | 3 | 6 | 9) {
            assert_eq!(
                solve_smtlib(&input, &config())
                    .expect("solve first-occurrence predicate theorem")
                    .result,
                CheckResult::Unsat,
                "first-occurrence predicate theorem must survive the bounded-string gate: {assertion}"
            );
        }
    }
}

#[test]
fn exact_source_first_occurrence_predicates_decline_ground_counterexamples() {
    for assertion in [
        r#"(not (= (str.prefixof "A" (str.++ "A" "A")) (str.suffixof "A" (str.++ "A" "B"))))"#,
        r#"(not (= (str.contains (str.replace "BA" "A" "AA") "BA") (str.suffixof "BA" (str.replace "BA" "A" "AA"))))"#,
        r#"(not (= (str.contains (str.replace "" "" "") "A") (str.contains (str.replace "" "" "A") "A")))"#,
        r#"(not (= (str.suffixof (str.replace "AB" "A" "") "AB") (str.prefixof "AB" (str.replace "AB" "B" "AB"))))"#,
        r#"(not (= (str.contains (str.from_int 12) "1") (str.suffixof "1" (str.from_int 12))))"#,
    ] {
        let input = format!(
            r"(set-logic QF_SLIA)
(assert {assertion})
(check-sat)
"
        );
        let script = parse_script(&input).expect("parse first-occurrence predicate control");
        assert!(
            !script.source_string_semantic_unsat,
            "ground predicate counterexample must not refute: {assertion}"
        );
        assert!(
            matches!(
                solve_smtlib(&input, &config())
                    .expect("solve first-occurrence predicate control")
                    .result,
                CheckResult::Sat(_)
            ),
            "ground predicate counterexample must remain SAT: {assertion}"
        );
    }
}

/// The last seven Noetzli residuals are satisfiable counterexample queries, not
/// missing UNSAT identities. The bounded source-witness probe must find a small
/// model and its returned assignment must replay every original parsed assertion.
#[test]
fn bounded_source_witness_closes_last_noetzli_counterexamples() {
    let assertions = [
        r"(not (= (str.contains (str.from_int z) x) (str.suffixof x (str.from_int z))))",
        r#"(not (= (str.replace x (str.replace y "A" y) y) x))"#,
        r#"(not (= (str.replace x (str.replace y "B" y) y) x))"#,
        r"(not (= (str.replace (str.replace x y x) y x) (str.replace x y (str.replace x y x))))",
        r#"(not (= (str.replace (str.replace x y x) y "A") (str.replace x y (str.replace x y "A"))))"#,
        r#"(not (= (str.replace (str.replace x y x) y "B") (str.replace x y (str.replace x y "B"))))"#,
        r#"(not (= (str.replace (str.replace x y x) y "") (str.replace x y (str.replace x y ""))))"#,
    ];
    let fast = SolverConfig::new().with_timeout(Duration::from_millis(250));
    for assertion in assertions {
        let input = format!(
            r"(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun y () String)
(declare-fun z () Int)
(assert {assertion})
(check-sat)
"
        );
        let outcome = solve_smtlib(&input, &fast).expect("solve Noetzli SAT residual");
        let CheckResult::Sat(model) = outcome.result else {
            panic!("Noetzli counterexample must decide SAT: {assertion}");
        };

        // Reparse independently, rerun the bounded source search, and replay its
        // witness through the exact source evaluator. The returned model must carry
        // those same Seq/Int bindings.
        let parsed = parse_script(&input).expect("reparse Noetzli SAT residual");
        let problem = parsed
            .source_string_sat_problem
            .as_ref()
            .expect("Noetzli residual has a source SAT problem");
        let witness = problem
            .bounded_witness(20_000, 4, 4)
            .expect("Noetzli residual has a bounded source witness");
        assert!(problem.replays(&witness));
        // ROUTE-AGNOSTIC on purpose. This used to assert the model equalled the
        // bounded-source witness exactly, which only holds when THAT route
        // produced it — the packed route finds a different, equally valid model
        // for the same satisfiable query (measured: a 7-character witness where
        // the source search returns "AAA"). Demanding one specific answer made
        // the test a race between routes, and it flipped purely on the budget.
        //
        // The property that actually matters is that the returned model is
        // READABLE: every source-level String variable is bound to a string
        // value, not left unbound or handed back as the internal packing. That
        // holds on both routes and is what a consumer of `(get-model)` needs.
        for (symbol, _) in witness.strings {
            match model.get(symbol) {
                Some(axeyum_ir::Value::Seq(elements)) => {
                    for element in elements {
                        assert!(
                            matches!(element, axeyum_ir::Value::Bv { width, .. }
                                if width == axeyum_ir::Sort::STRING_ELEM_WIDTH),
                            "a string element must be a code point for {assertion}"
                        );
                    }
                }
                other => panic!(
                    "returned model must bind every source String to a readable \
                     string value for {assertion}, got {other:?}"
                ),
            }
        }
        for (symbol, _) in witness.integers {
            assert!(
                matches!(model.get(symbol), Some(axeyum_ir::Value::Int(_))),
                "returned model must bind every source Int for {assertion}"
            );
        }
    }
}

#[test]
fn bounded_source_witness_is_capped_and_replay_fail_closed() {
    let replay_input = r"(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun y () String)
(declare-fun z () Int)
(assert (not (= (str.contains (str.from_int z) x) (str.suffixof x (str.from_int z)))))
(check-sat)
";
    let replay_script = parse_script(replay_input).expect("parse replay control");
    let replay_problem = replay_script
        .source_string_sat_problem
        .as_ref()
        .expect("replay control has source SAT problem");
    let witness = replay_problem
        .bounded_witness(20_000, 4, 4)
        .expect("replay control has a witness");
    assert!(replay_problem.replays(&witness));

    let mut duplicate = witness.clone();
    duplicate.strings.push(duplicate.strings[0].clone());
    assert!(
        !replay_problem.replays(&duplicate),
        "a duplicate source binding must fail replay"
    );
    let mut missing = witness.clone();
    missing.integers.clear();
    assert!(
        !replay_problem.replays(&missing),
        "a missing source binding must fail replay"
    );
    let mut mutated = witness;
    mutated.strings[0].1.clear();
    assert!(
        !replay_problem.replays(&mutated),
        "a mutated source witness must fail replay"
    );

    let capped_input = r"(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun y () String)
(declare-fun z () String)
(assert (not (= (str.replace x y z) x)))
(check-sat)
";
    let capped_script = parse_script(capped_input).expect("parse assignment-cap control");
    let capped_problem = capped_script
        .source_string_sat_problem
        .as_ref()
        .expect("assignment-cap control has source SAT problem");
    assert!(
        capped_problem.bounded_witness(20_000, 4, 4).is_none(),
        "31^3 assignments must exceed the 20,000-step source-witness cap"
    );

    let false_input = r"(set-logic QF_SLIA)
(declare-fun x () String)
(assert (and (= x x) false))
(check-sat)
";
    let false_script = parse_script(false_input).expect("parse false-query control");
    let false_problem = false_script
        .source_string_sat_problem
        .as_ref()
        .expect("false-query control has source SAT problem");
    assert!(
        false_problem.bounded_witness(20_000, 4, 4).is_none(),
        "the SAT-only source probe must not fabricate a witness"
    );
}
