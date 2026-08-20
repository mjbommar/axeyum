//! The length/code-point refutation, end to end and against the whole committed
//! string corpus.
//!
//! Two obligations, and the second is the one that matters.
//!
//! 1. The three corpus shapes it was written for reach
//!    [`Evidence::UnsatStringLength`] through the SHIPPED route — the text front
//!    door — and re-validate. A unit test in `string_length_cert` can only show
//!    that the module works; it cannot show that anything calls it. A hook
//!    placed where an earlier arm returns first is dead, and this repository has
//!    shipped exactly that (`produce_real_zero_product_evidence`, first placed
//!    after the route `match`, never fired on either file it was written for).
//!
//! 2. **The producer never fires on a satisfiable query.** Every committed
//!    `QF_S`/`QF_SLIA`/`QF_SEQ` file is swept, the refutation is attempted on the
//!    raw source, and any hit must be on a file whose declared `:status` is
//!    `unsat`. This is oracle-free — the declared status is ground truth carried
//!    by the corpus — so it runs everywhere, and it is the check that would catch
//!    a lemma whose side condition is too weak. The sweep also asserts a nonzero
//!    hit count, because a producer that certified nothing would pass it
//!    vacuously.

#![cfg(feature = "full")]

use std::time::Duration;

use axeyum_solver::{
    Evidence, EvidenceCheck, SolverConfig, produce_evidence_smtlib_with_script,
    string_length_refutation,
};

fn cfg() -> SolverConfig {
    SolverConfig {
        timeout: Some(Duration::from_secs(30)),
        ..SolverConfig::default()
    }
}

fn corpus_root() -> std::path::PathBuf {
    std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../corpus/public-curated/non-incremental")
}

/// The three shapes, by corpus path.
const CERTIFIED: &[&str] = &[
    "QF_S/cvc5-regress-clean/r0_QF_SLIA_str004.smt2",
    "QF_S/cvc5-regress-clean/r0_QF_S_str005.smt2",
    "QF_S/cvc5-regress-clean/r1_QF_SLIA_str-code-unsat-2.smt2",
];

/// The declared `:status`, or `None` when the file does not carry one.
fn declared_status(text: &str) -> Option<&'static str> {
    // `:status` is a set-info keyword; the value is the next token.
    let after = text.split(":status").nth(1)?;
    let word: String = after
        .trim_start()
        .chars()
        .take_while(char::is_ascii_alphabetic)
        .collect();
    match word.as_str() {
        "unsat" => Some("unsat"),
        "sat" => Some("sat"),
        _ => None,
    }
}

/// Obligation 1: the shipped route reaches the certificate, and it re-validates.
#[test]
fn the_three_corpus_shapes_certify_through_the_shipped_route() {
    for rel in CERTIFIED {
        let path = corpus_root().join(rel);
        let text = std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("read {rel}: {e}"));
        assert_eq!(
            declared_status(&text),
            Some("unsat"),
            "[{rel}] the corpus file must be an unsat-truth query"
        );

        let produced = produce_evidence_smtlib_with_script(&text, &cfg())
            .unwrap_or_else(|e| panic!("[{rel}] produce_evidence_smtlib_with_script: {e:?}"));
        assert!(
            matches!(produced.report.evidence, Evidence::UnsatStringLength(_)),
            "[{rel}] the length certificate is not reachable through the front door; \
             got kind={}. A producer nothing calls is not a producer",
            produced.report.evidence.kind_label()
        );
        assert!(
            produced.report.evidence.is_certified(),
            "[{rel}] the variant must claim certification"
        );
        assert_eq!(
            produced.check_outcome().expect("check runs"),
            EvidenceCheck::Verified,
            "[{rel}] claiming certification means surviving the re-check"
        );
    }
}

/// Obligation 2: over the whole committed string corpus, a certificate implies
/// the file is `unsat`.
///
/// The producer is run on the RAW SOURCE, deliberately bypassing the solver: this
/// asks whether the abstraction alone can be talked into refuting a satisfiable
/// query, which is the failure a too-weak lemma side condition would produce.
#[test]
fn the_producer_never_refutes_a_satisfiable_corpus_file() {
    let mut certified = Vec::new();
    let mut examined = 0usize;
    let mut violations = Vec::new();

    for logic in ["QF_S", "QF_SLIA", "QF_SEQ"] {
        let dir = corpus_root().join(logic).join("cvc5-regress-clean");
        let Ok(entries) = std::fs::read_dir(&dir) else {
            continue;
        };
        let mut paths: Vec<std::path::PathBuf> = entries
            .filter_map(Result::ok)
            .map(|e| e.path())
            .filter(|p| p.extension().is_some_and(|e| e == "smt2"))
            .collect();
        // Deterministic order: a public API promise, and it makes a failure
        // reproducible from the printed name alone.
        paths.sort();
        for path in paths {
            let Ok(text) = std::fs::read_to_string(&path) else {
                continue;
            };
            examined += 1;
            let Ok(commands) = axeyum_smtlib::read_all(&text) else {
                continue;
            };
            if string_length_refutation(&commands).is_none() {
                continue;
            }
            let name = path.display().to_string();
            match declared_status(&text) {
                Some("unsat") => certified.push(name),
                other => violations.push(format!(
                    "{name}: certified a refutation of a file whose declared status is {other:?}"
                )),
            }
        }
    }

    assert!(
        examined > 100,
        "only {examined} corpus files were examined; the sweep is not pointed at the corpus"
    );
    assert!(
        violations.is_empty(),
        "WRONG VERDICT — the length abstraction refuted a query the corpus does not \
         call unsat:\n{}",
        violations.join("\n")
    );
    assert!(
        !certified.is_empty(),
        "the sweep certified nothing, so it cannot distinguish a working producer \
         from one that always declines"
    );
    println!(
        "certified {} of {examined} string corpus files:",
        certified.len()
    );
    for name in &certified {
        println!("  {name}");
    }
}

/// A produced certificate must survive re-validation against an arena that
/// shares nothing with the producing run — including the *wrong* arena.
///
/// The certificate is subject-independent by construction (a string script's
/// flat view is the bounded packed-BV encoding, not the query), so this is what
/// "independent" can mean for it: the checker must reach the same answer with no
/// help at all from the producing run's state.
#[test]
fn the_certificate_re_validates_against_an_unrelated_arena() {
    let text = std::fs::read_to_string(corpus_root().join(CERTIFIED[0])).expect("read");
    let produced = produce_evidence_smtlib_with_script(&text, &cfg()).expect("produce");
    let unrelated = axeyum_smtlib::parse_script(
        "(set-logic QF_BV)(declare-fun q () (_ BitVec 4))(assert (= q #x1))(check-sat)",
    )
    .expect("parses");
    assert_eq!(
        produced
            .report
            .evidence
            .check_outcome(&unrelated.arena, &unrelated.assertions)
            .expect("check runs"),
        EvidenceCheck::Verified
    );
}
