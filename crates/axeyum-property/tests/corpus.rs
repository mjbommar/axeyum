//! Committed graduated corpus gate for the typed property SDK.

#[path = "support/corpus_cases.rs"]
mod corpus_cases;

type TestResult = Result<(), Box<dyn std::error::Error>>;

#[test]
fn property_sdk_corpus_matches_committed_scoreboard() -> TestResult {
    let reports = corpus_cases::run_property_corpus()?;

    corpus_cases::assert_reports_match(&reports);
    assert_eq!(
        corpus_cases::tally(&reports),
        corpus_cases::expected_totals()
    );
    assert_eq!(
        corpus_cases::render_json(&reports),
        include_str!("../../../docs/consumer-track/property/corpus.json")
    );
    assert_eq!(
        corpus_cases::render_markdown(&reports),
        include_str!("../../../docs/consumer-track/property/SCOREBOARD.md")
    );
    Ok(())
}
