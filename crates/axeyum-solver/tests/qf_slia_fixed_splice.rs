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

/// PyEx spells a first-occurrence character replacement as a prefix through the
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

    let unequal_lengths = r#"(set-logic QF_SLIA)
(declare-fun s () String)
(assert (=
  (str.++
    (str.replace
      (str.substr s 0 (+ (str.indexof s "A" 0) 1))
      "A" "zz")
    (str.substr s
      (+ (str.indexof s "A" 0) 1)
      (- (str.len s) (+ (str.indexof s "A" 0) 1))))
  "zz"))
(check-sat)
"#;
    let unequal =
        parse_script(unequal_lengths).expect("unequal-length case remains a sound word fallback");
    assert!(
        unequal.word_only_fallback.is_some(),
        "unequal-length replacement must not receive the correlated bound"
    );
    assert!(!unequal.prefer_source_string_routes);
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

    let parsed = parse_script(&script).expect("large pipeline uses source-level fallback");
    assert!(parsed.word_only_fallback.is_some());
    assert!(!parsed.prefer_source_string_routes);
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
    assert!(!script.fixed_splice_semantic_unsat);
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
    assert!(script.fixed_splice_semantic_unsat);
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
    assert!(script.fixed_splice_semantic_unsat);
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
    assert!(script.fixed_splice_semantic_unsat);
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
    assert!(!script.fixed_splice_semantic_unsat);
    assert_ne!(
        solve_smtlib(input, &config())
            .expect("solve pinned-view content model")
            .result,
        CheckResult::Unsat
    );
}

#[test]
fn word_only_fallback_retains_exact_path_conflicts() {
    let input = r#"(set-logic QF_SLIA)
(declare-fun s () String)
(declare-fun pad () String)
(assert (= pad "abcdefghijklmn"))
(assert (= (str.indexof s "x" 0) 0))
(assert (not (not (not (= (ite (= (str.len s) 0) 1 0) 0)))))
(assert (not (not (= (ite (= (str.len s) 0) 1 0) 0))))
(check-sat)
"#;
    let script = parse_script(input).expect("parse word-only fallback conflict");
    assert!(script.word_only_fallback.is_some());
    assert!(script.fixed_splice_semantic_unsat);
    assert_eq!(
        solve_smtlib(input, &config())
            .expect("solve word-only fallback conflict")
            .result,
        CheckResult::Unsat
    );
}

#[test]
fn semantic_refuter_never_masks_a_non_capacity_parse_decline() {
    let input = r#"(set-logic QF_SLIA)
(declare-fun s () String)
(assert (= (unknown.word.operator s) s))
(assert (not (= (unknown.word.operator s) s)))
(check-sat)
"#;
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
    assert!(!script.fixed_splice_semantic_unsat);
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
    assert!(!script.fixed_splice_semantic_unsat);
    assert_ne!(
        solve_smtlib(input, &config())
            .expect("solve scoped fixed-splice mutation")
            .result,
        CheckResult::Unsat
    );
}
