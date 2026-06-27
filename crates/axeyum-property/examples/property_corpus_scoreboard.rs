//! Regenerate the committed `axeyum-property` corpus scoreboard artifacts.
//!
//! Usage:
//! ```text
//! cargo run -p axeyum-property --example property_corpus_scoreboard -- json docs/consumer-track/property/corpus.json
//! cargo run -p axeyum-property --example property_corpus_scoreboard -- markdown docs/consumer-track/property/SCOREBOARD.md
//! ```

#[path = "../tests/support/corpus_cases.rs"]
mod corpus_cases;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut args = std::env::args().skip(1);
    let Some(format) = args.next() else {
        print_usage_and_exit();
    };
    let output_path = args.next();
    if args.next().is_some() {
        print_usage_and_exit();
    }

    let reports = corpus_cases::run_property_corpus()?;
    corpus_cases::assert_reports_match(&reports);
    assert_eq!(
        corpus_cases::tally(&reports),
        corpus_cases::expected_totals()
    );

    let output = match format.as_str() {
        "json" => corpus_cases::render_json(&reports),
        "markdown" => corpus_cases::render_markdown(&reports),
        _ => print_usage_and_exit(),
    };

    if let Some(path) = output_path {
        std::fs::write(&path, output)?;
        eprintln!("wrote {path}");
    } else {
        print!("{output}");
    }
    Ok(())
}

fn print_usage_and_exit() -> ! {
    eprintln!(
        "usage: cargo run -p axeyum-property --example property_corpus_scoreboard -- <json|markdown> [out]"
    );
    std::process::exit(2);
}
