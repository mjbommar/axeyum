//! Lexical intake budgets must decline before parsing unchecked populations.
use axeyum_smtlib::{SmtError, parse_script_within, read_all, read_all_within};
use std::time::{Duration, Instant};

#[test]
fn expired_reader_budget_rejects_each_lexical_population() {
    let long = "x".repeat(16_384);
    for source in [
        String::new(),
        format!(";{long}\n(assert true)"),
        format!("\"{long}\""),
        format!("|{long}|"),
        long,
        "(assert true)".into(),
    ] {
        assert!(matches!(
            read_all_within(&source, Some(Instant::now())),
            Err(SmtError::DeadlineExceeded(_))
        ));
    }
}

#[test]
fn bounded_reader_preserves_tokens_and_quoted_literals() {
    let source = "; comment\n(assert (= |12| \"a\"\"b\"))";
    let expected = read_all(source).expect("ordinary reader");
    assert_eq!(read_all_within(source, None).unwrap(), expected);
    assert_eq!(
        read_all_within(source, Instant::now().checked_add(Duration::from_secs(60))).unwrap(),
        expected
    );
}

#[test]
fn parser_deadline_covers_the_initial_lexical_pass() {
    let source = format!(";{}\n(check-sat)", "x".repeat(16_384));
    match parse_script_within(&source, Some(Instant::now())) {
        Err(SmtError::DeadlineExceeded(phase)) => assert_eq!(phase, "s-expression intake"),
        other => panic!("expected lexical deadline, got {other:?}"),
    }
}

#[test]
fn syntax_errors_remain_errors_with_available_budget() {
    assert!(matches!(
        read_all_within(")", Instant::now().checked_add(Duration::from_secs(60))),
        Err(SmtError::Syntax(_))
    ));
    assert!(parse_script_within("(check-sat)", None).is_ok());
}
