//! The SMT-LIB **session** front door (ADR-0541): one response per output
//! command, in script order.
//!
//! Every expectation here was measured against `/usr/bin/z3` 4.13.3 and
//! `/nas3/data/axeyum/harness/bin/cvc5` 1.3.4 on 2026-08-21 before it was
//! written down; where the two references disagree the choice is stated in the
//! test that makes it.
#![cfg(feature = "full")]

use axeyum_solver::{CheckResult, SmtLibResponse, SolverConfig, solve_smtlib_session};

fn session(text: &str) -> Vec<SmtLibResponse> {
    solve_smtlib_session(text, &SolverConfig::new()).expect("session")
}

/// The stdout line each response prints, so a test can assert on what a consumer
/// actually sees rather than on the shape of an enum.
fn line(response: &SmtLibResponse) -> String {
    match response {
        SmtLibResponse::CheckSat(CheckResult::Sat(_)) => "sat".to_owned(),
        SmtLibResponse::CheckSat(CheckResult::Unsat) => "unsat".to_owned(),
        SmtLibResponse::CheckSat(CheckResult::Unknown(_)) => "unknown".to_owned(),
        SmtLibResponse::Model(text) | SmtLibResponse::Proof(text) | SmtLibResponse::Echo(text) => {
            text.clone()
        }
        SmtLibResponse::Values(pairs) => format!(
            "({})",
            pairs
                .iter()
                .map(|(t, v)| format!("({t} {v})"))
                .collect::<Vec<_>>()
                .join(" ")
        ),
        SmtLibResponse::UnsatCore(items) | SmtLibResponse::Assertions(items) => {
            format!("({})", items.join(" "))
        }
        SmtLibResponse::Success => "success".to_owned(),
        SmtLibResponse::Unsupported { .. } => "unsupported".to_owned(),
        SmtLibResponse::Error { message, .. } => format!("(error {message})"),
    }
}

fn lines(text: &str) -> Vec<String> {
    session(text).iter().map(line).collect()
}

// ---------------------------------------------------------------------------
// Verdicts: the session must not be a second opinion.
// ---------------------------------------------------------------------------

/// `solve_smtlib_incremental` is this walk with the output commands switched
/// off, so the verdict streams are the same object, not two agreeing ones.
#[test]
fn verdict_stream_matches_the_incremental_front_door() {
    let text = "(set-logic QF_LIA)\n(declare-const x Int)\n(assert (> x 5))\n(check-sat)\n\
                (push 1)\n(assert (< x 3))\n(check-sat)\n(pop 1)\n(check-sat)\n";
    let config = SolverConfig::new();
    let incremental: Vec<String> = axeyum_solver::solve_smtlib_incremental(text, &config)
        .expect("incremental")
        .iter()
        .map(|r| line(&SmtLibResponse::CheckSat(r.clone())))
        .collect();
    // z3 4.13.3 on this script: sat / unsat / sat [measured 2026-08-21].
    assert_eq!(incremental, ["sat", "unsat", "sat"]);
    assert_eq!(lines(text), incremental);
}

/// Output commands are dropped by the verdict-only front door, so adding them to
/// a script must not add anything to its result vector.
#[test]
fn incremental_front_door_still_answers_only_check_sat() {
    let text = "(set-option :produce-models true)\n(declare-const x Int)\n(assert (> x 5))\n\
                (check-sat)\n(get-model)\n(get-value (x))\n(echo \"hi\")\n";
    let results =
        axeyum_solver::solve_smtlib_incremental(text, &SolverConfig::new()).expect("incremental");
    assert_eq!(results.len(), 1, "one check-sat, one result");
}

// ---------------------------------------------------------------------------
// get-value / get-model
// ---------------------------------------------------------------------------

/// z3 4.13.3 prints `((x 6) ((+ x 1) 7))` for this script [measured].
#[test]
fn get_value_echoes_the_term_as_written() {
    let text = "(declare-const x Int)\n(assert (> x 5))\n(check-sat)\n(get-value (x (+ x 1)))\n";
    let out = lines(text);
    assert_eq!(out[0], "sat");
    assert_eq!(out[1], "((x 6) ((+ x 1) 7))");
}

/// z3 4.13.3 prints `(define-fun x () Int 6)` inside the model block [measured].
#[test]
fn get_model_renders_declared_constants() {
    let text = "(declare-const x Int)\n(assert (> x 5))\n(check-sat)\n(get-model)\n";
    let out = lines(text);
    assert_eq!(out[0], "sat");
    assert!(
        out[1].contains("(define-fun x () Int 6)"),
        "unexpected model: {}",
        out[1]
    );
}

/// A declared `String` is a packed bit-vector in the IR (ADR-0029). Both the
/// model and `get-value` must hand back the string, matching z3's `"AB"`
/// [measured].
#[test]
fn string_values_render_as_string_literals() {
    let text = "(set-logic QF_S)\n(declare-const s String)\n(assert (= s \"AB\"))\n(check-sat)\n\
         (get-value (s))\n(get-model)\n";
    let out = lines(text);
    assert_eq!(out[0], "sat");
    assert_eq!(out[1], "((s \"AB\"))");
    assert!(
        out[2].contains("(define-fun s () String \"AB\")"),
        "unexpected model: {}",
        out[2]
    );
}

/// A bit-vector-valued term in a script using the bounded string encoding cannot
/// be told apart from a *packed string*, so it is refused rather than printed as
/// `#b…`. A wrong-looking model is worse than a refused one.
#[test]
fn get_value_declines_a_bare_bit_vector_in_a_string_script() {
    let text = "(set-logic QF_SLIA)\n(declare-const s String)\n(declare-const b (_ BitVec 8))\n\
                (assert (= s \"A\"))\n(check-sat)\n(get-value (b))\n";
    let out = lines(text);
    assert_eq!(out[0], "sat");
    assert_eq!(out[1], "unsupported");
}

/// An uninterpreted carrier token is a model artifact, not a term: z3 prints its
/// own `U!val!0` names plus a universe block, which is a z3 extension rather
/// than SMT-LIB. Inventing a spelling would hand a consumer something that looks
/// like a model and is not one, so the whole command is refused.
#[test]
fn get_model_declines_an_uninterpreted_sort() {
    let text = "(set-logic QF_UF)\n(declare-sort U 0)\n(declare-const a U)\n\
                (declare-const b U)\n(assert (not (= a b)))\n(check-sat)\n(get-model)\n";
    let out = lines(text);
    assert_eq!(out[0], "sat");
    assert_eq!(out[1], "unsupported");
}

/// z3 4.13.3: `(error "line 5 column 10: model is not available")` [measured].
/// Both references answer `(get-model)` in a script that never set the option,
/// so the default is `true` and only an explicit `false` refuses.
#[test]
fn produce_models_false_makes_get_model_an_error() {
    let text = "(set-option :produce-models false)\n(declare-const x Int)\n(assert (> x 5))\n\
                (check-sat)\n(get-model)\n";
    let out = lines(text);
    assert_eq!(out[0], "sat");
    assert!(out[1].starts_with("(error"), "got {}", out[1]);
    // ...and the same script without the option answers.
    let allowed = lines(&text.replace(":produce-models false", ":produce-models true"));
    assert!(allowed[1].contains("define-fun"), "got {}", allowed[1]);
}

/// `get-value` has its own `:produce-models` guard and its own "was the last
/// verdict `sat`" guard. Both were unkilled by any test until a mutation run
/// deleted them and nothing died — the `get-model` tests above cover a
/// different code path, and "close enough" is how a guard that cannot fail gets
/// shipped.
#[test]
fn produce_models_false_makes_get_value_an_error() {
    let text = "(set-option :produce-models false)\n(declare-const x Int)\n(assert (> x 5))\n\
                (check-sat)\n(get-value (x))\n";
    let out = lines(text);
    assert_eq!(out[0], "sat");
    assert!(out[1].starts_with("(error"), "got {}", out[1]);
    let allowed = lines(&text.replace(":produce-models false", ":produce-models true"));
    assert_eq!(allowed[1], "((x 6))");
}

#[test]
fn get_value_after_unsat_is_an_error() {
    let text = "(declare-const x Int)\n(assert (> x 5))\n(assert (< x 3))\n(check-sat)\n\
                (get-value (x))\n";
    let out = lines(text);
    assert_eq!(out[0], "unsat");
    assert!(out[1].contains("was not sat"), "got {}", out[1]);
}

#[test]
fn get_model_after_unsat_is_an_error() {
    let text = "(declare-const x Int)\n(assert (> x 5))\n(assert (< x 3))\n(check-sat)\n\
                (get-model)\n";
    let out = lines(text);
    assert_eq!(out[0], "unsat");
    assert!(out[1].starts_with("(error"), "got {}", out[1]);
}

#[test]
fn get_model_before_any_check_sat_is_an_error() {
    let out = lines("(declare-const x Int)\n(assert (> x 5))\n(get-model)\n");
    assert_eq!(out.len(), 1);
    assert!(out[0].contains("before any check-sat"), "got {}", out[0]);
}

/// A model command answers about the query that was *decided*. Asserting more
/// after the `check-sat` would make it answer about a query nobody decided, so
/// it errors instead — the state SMT-LIB calls illegal.
#[test]
fn get_model_after_a_new_assert_is_an_error() {
    let text = "(declare-const x Int)\n(assert (> x 5))\n(check-sat)\n(assert (< x 3))\n\
                (get-model)\n";
    let out = lines(text);
    assert_eq!(out[0], "sat");
    assert!(
        out[1].contains("changed since the last check-sat"),
        "got {}",
        out[1]
    );
}

// ---------------------------------------------------------------------------
// get-unsat-core / get-proof
// ---------------------------------------------------------------------------

/// z3 4.13.3 prints `(a1 a2)`; cvc5 1.3.4 the same names [measured].
#[test]
fn get_unsat_core_names_the_needed_assertions() {
    let text = "(set-option :produce-unsat-cores true)\n(declare-const x Int)\n\
                (assert (! (> x 5) :named a1))\n(assert (! (< x 3) :named a2))\n\
                (assert (! (> x 0) :named a3))\n(check-sat)\n(get-unsat-core)\n";
    let out = lines(text);
    assert_eq!(out[0], "unsat");
    assert_eq!(out[1], "(a1 a2)");
}

/// Both references error rather than answer when the option was not set
/// [measured], so the default is `false`.
#[test]
fn get_unsat_core_without_the_option_is_an_error() {
    let text = "(declare-const x Int)\n(assert (! (> x 5) :named a1))\n\
                (assert (! (< x 3) :named a2))\n(check-sat)\n(get-unsat-core)\n";
    let out = lines(text);
    assert_eq!(out[0], "unsat");
    assert!(out[1].contains(":produce-unsat-cores"), "got {}", out[1]);
}

#[test]
fn get_unsat_core_after_sat_is_an_error() {
    let text = "(set-option :produce-unsat-cores true)\n(declare-const x Int)\n\
                (assert (! (> x 5) :named a1))\n(check-sat)\n(get-unsat-core)\n";
    let out = lines(text);
    assert_eq!(out[0], "sat");
    assert!(out[1].contains("was not unsat"), "got {}", out[1]);
}

/// The proof is re-checked by the in-tree Alethe checker before it is returned,
/// so a returned proof is a checked one.
#[test]
fn get_proof_emits_a_rechecked_alethe_refutation() {
    let text = "(set-logic QF_LIA)\n(set-option :produce-proofs true)\n(declare-const x Int)\n\
                (assert (> x 5))\n(assert (< x 3))\n(check-sat)\n(get-proof)\n";
    let out = lines(text);
    assert_eq!(out[0], "unsat");
    assert!(
        out[1].contains("(step"),
        "expected an Alethe proof, got {}",
        out[1]
    );
    assert!(
        out[1].contains("(cl)"),
        "expected the empty clause, got {}",
        out[1]
    );
}

#[test]
fn get_proof_without_the_option_is_an_error() {
    let text = "(set-logic QF_LIA)\n(declare-const x Int)\n(assert (> x 5))\n(assert (< x 3))\n\
                (check-sat)\n(get-proof)\n";
    let out = lines(text);
    assert_eq!(out[0], "unsat");
    assert!(out[1].contains(":produce-proofs"), "got {}", out[1]);
}

#[test]
fn get_proof_after_sat_is_an_error() {
    let text = "(set-logic QF_LIA)\n(set-option :produce-proofs true)\n(declare-const x Int)\n\
                (assert (> x 5))\n(check-sat)\n(get-proof)\n";
    let out = lines(text);
    assert_eq!(out[0], "sat");
    assert!(out[1].contains("was not unsat"), "got {}", out[1]);
}

// ---------------------------------------------------------------------------
// set-option
// ---------------------------------------------------------------------------

/// The point of the whole change: an option this solver does not honor says so.
/// Before ADR-0541 it was accepted and ignored, which a consumer cannot see.
/// cvc5 1.3.4 answers `unsupported` here [measured]; z3 4.13.3 raises an error,
/// and SMT-LIB §4.1.7 prescribes `unsupported`.
#[test]
fn an_unhonored_option_says_unsupported() {
    let out = lines("(set-option :nonsense-option-xyz true)\n(check-sat)\n");
    assert_eq!(out, ["unsupported", "sat"]);
}

/// ...and an honored one is silent, which is what both references do at their
/// default `:print-success false`.
#[test]
fn an_honored_option_is_silent() {
    let out = lines("(set-option :produce-models true)\n(check-sat)\n");
    assert_eq!(out, ["sat"]);
}

#[test]
fn print_success_acknowledges_subsequent_commands() {
    let out = lines("(set-option :print-success true)\n(set-option :produce-models true)\n");
    assert_eq!(out, ["success", "success"]);
}

/// A `b_value` is exactly `true` or `false` (SMT-LIB §3.9); anything else is a
/// malformed value, not a silent `false`.
#[test]
fn a_malformed_option_value_is_an_error() {
    let out = lines("(set-option :produce-models yes)\n(check-sat)\n");
    assert!(out[0].contains("expects true or false"), "got {}", out[0]);
}

// ---------------------------------------------------------------------------
// set-logic
// ---------------------------------------------------------------------------

/// z3 4.13.3 prints `unsupported` and then decides the script anyway
/// [measured]; cvc5 1.3.4 makes it a parse error. z3's is the SMT-LIB §4.1.7
/// response.
#[test]
fn a_name_that_is_not_a_logic_says_unsupported_and_still_decides() {
    let out = lines(
        "(set-logic NONSENSE_XYZ)\n(declare-const x Int)\n(assert (> x 5))\n\
                     (check-sat)\n",
    );
    assert_eq!(out, ["unsupported", "sat"]);
}

/// The positive control the first version of this failed: `BV` is declared by 59
/// tracked benchmark files and a hand-written list of logic names omitted it.
/// Every logic any tracked file declares must pass.
#[test]
fn every_logic_the_corpus_declares_is_recognized() {
    // The 40 distinct `set-logic` values across the 1,430 tracked `.smt2` files,
    // enumerated 2026-08-21.
    const CORPUS_LOGICS: &[&str] = &[
        "ALL",
        "BV",
        "LIA",
        "QF_ABV",
        "QF_ABVFP",
        "QF_ALIA",
        "QF_AUFBV",
        "QF_AUFLIA",
        "QF_AX",
        "QF_BV",
        "QF_BVFP",
        "QF_DT",
        "QF_FF",
        "QF_FP",
        "QF_LIA",
        "QF_LRA",
        "QF_NIA",
        "QF_NRA",
        "QF_S",
        "QF_SEQ",
        "QF_SLIA",
        "QF_UF",
        "QF_UFBV",
        "QF_UFBVFS",
        "QF_UFBVLIA",
        "QF_UFC",
        "QF_UFDTLIA",
        "QF_UFFF",
        "QF_UFLIA",
        "QF_UFLIAFS",
        "QF_UFLIRAFS",
        "QF_UFLRAFS",
        "QF_UFNIA",
        "QF_UFNIRA",
        "QF_UFNRA",
        "QF_UFNRAT",
        "QF_UFSLIA",
        "UF",
        "UFLIA",
        "UFNIA",
    ];
    for logic in CORPUS_LOGICS {
        let out = lines(&format!("(set-logic {logic})\n(check-sat)\n"));
        assert_eq!(
            out,
            ["sat"],
            "`{logic}` is declared by tracked benchmarks and must not draw `unsupported`"
        );
    }
}

/// Pins the measurement behind the decision NOT to check logic conformance.
///
/// Five tracked files declare `QF_SLIA` and use `(_ BitVec n)` sequence
/// elements, which `QF_SLIA` does not have. Z3 4.13.3 rejects all five at the
/// parser (`unknown sort 'BitVec'`); axeyum decides one of them. Enforcement
/// would therefore cost one decided file — which is *not* the reason to decline.
/// The reason is in `is_smtlib_logic_name`'s docs: enforcement needs a complete
/// logic → theory table, and a table with a hole refuses a correct file.
///
/// This test keeps the claim honest by re-deriving the count from the tree.
#[test]
fn logic_conformance_would_reject_five_corpus_files() {
    use std::path::Path;
    let root = Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(Path::parent)
        .expect("workspace root")
        .join("corpus");
    let mut flagged = Vec::new();
    let mut scanned = 0usize;
    let mut stack = vec![root.clone()];
    while let Some(dir) = stack.pop() {
        let Ok(entries) = std::fs::read_dir(&dir) else {
            continue;
        };
        for entry in entries.flatten() {
            let path = entry.path();
            if path.is_dir() {
                stack.push(path);
            } else if path.extension().is_some_and(|e| e == "smt2") {
                let Ok(text) = std::fs::read_to_string(&path) else {
                    continue;
                };
                scanned += 1;
                let body: String = text
                    .lines()
                    .map(|l| l.split(';').next().unwrap_or(""))
                    .collect::<Vec<_>>()
                    .join("\n");
                let Some(logic) = body
                    .split("(set-logic")
                    .nth(1)
                    .and_then(|rest| rest.split(')').next())
                    .map(str::trim)
                else {
                    continue;
                };
                if !logic.contains("BV") && logic != "ALL" && body.contains("(_ BitVec") {
                    flagged.push(path);
                }
            }
        }
    }
    // Positive control: the scan must have looked at the corpus at all. An empty
    // answer from a scan that ran over nothing is the trap this guards.
    assert!(scanned > 1_000, "only scanned {scanned} .smt2 files");
    assert_eq!(
        flagged.len(),
        5,
        "the conformance-violation census moved: {flagged:?}"
    );
}

// ---------------------------------------------------------------------------
// echo, and the commands nobody here answers
// ---------------------------------------------------------------------------

#[test]
fn echo_prints_its_argument_verbatim() {
    assert_eq!(lines("(echo \"hello\")\n"), ["\"hello\""]);
}

/// Nothing is silent. A command this front door does not answer says
/// `unsupported`, because silence is indistinguishable from an answer of
/// "nothing" — the exact defect this whole change exists to remove.
#[test]
fn unanswered_output_commands_say_unsupported() {
    for command in [
        "(get-info :name)",
        "(get-option :produce-models)",
        "(get-assignment)",
        "(get-objectives)",
        "(get-unsat-assumptions)",
    ] {
        let out = lines(&format!(
            "(declare-const x Int)\n(assert (> x 5))\n(check-sat)\n{command}\n"
        ));
        assert_eq!(out, ["sat", "unsupported"], "for {command}");
    }
}

// ---------------------------------------------------------------------------
// :timeout
// ---------------------------------------------------------------------------

/// `:timeout` is honored, not decoration — and the caller's timeout is a
/// **ceiling** on it, so a script cannot award itself more budget than the
/// operator granted.
///
/// The instance matters. An earlier version of this test used an inline
/// bit-vector query and killed nothing under mutation, because the query was
/// decided in milliseconds either way: the assertion held whether or not the
/// ceiling existed, which is the definition of a guard that cannot fail. This
/// one uses a committed benchmark measured at **> 30 s** on this host with no
/// timeout at all, so removing the `min` makes the run take the script's full
/// 20 s and the assertion fails.
#[test]
fn a_script_timeout_cannot_exceed_the_callers_ceiling() {
    use std::path::Path;
    let file = Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(Path::parent)
        .expect("workspace root")
        .join("corpus/qfbv-curated/brummayerbiere3__mulhs16.smt2");
    let body = std::fs::read_to_string(&file).expect("the corpus instance");
    let text = format!("(set-option :timeout 20000)\n{body}");
    let started = std::time::Instant::now();
    let config = SolverConfig::new().with_timeout(std::time::Duration::from_millis(200));
    let out = solve_smtlib_session(&text, &config).expect("session");
    let elapsed = started.elapsed();
    assert!(
        elapsed < std::time::Duration::from_secs(10),
        "the 200 ms ceiling did not bite: {elapsed:?}"
    );
    assert_eq!(out.len(), 1, "one check-sat");
    assert_eq!(
        line(&out[0]),
        "unknown",
        "the budget must be what stopped it"
    );
}

/// ...and the script's `:timeout` is what stops the run when it is *below* the
/// ceiling. Without this the pair above is satisfied by ignoring `:timeout`
/// entirely and always using the caller's value.
#[test]
fn a_script_timeout_below_the_ceiling_is_what_bites() {
    use std::path::Path;
    let file = Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(Path::parent)
        .expect("workspace root")
        .join("corpus/qfbv-curated/brummayerbiere3__mulhs16.smt2");
    let body = std::fs::read_to_string(&file).expect("the corpus instance");
    let text = format!("(set-option :timeout 300)\n{body}");
    let started = std::time::Instant::now();
    // No caller ceiling at all: only the script's 300 ms can stop this.
    let out = solve_smtlib_session(&text, &SolverConfig::new()).expect("session");
    let elapsed = started.elapsed();
    assert!(
        elapsed < std::time::Duration::from_secs(10),
        "the script's :timeout did not bite: {elapsed:?}"
    );
    assert_eq!(line(&out[0]), "unknown");
}

// ---------------------------------------------------------------------------
// The structural guard: nothing the parser accepts may be silently dropped.
// ---------------------------------------------------------------------------

/// Reads the **parser's own** command vocabulary out of `parse_command` and
/// requires every output command in it to produce a response.
///
/// This is the guard against the defect coming back rather than against the
/// defect. `get-model` was a silent no-op for months while the parser accepted
/// it and a library entry point existed for it; a per-command test suite would
/// not have noticed, because the command nobody wired is exactly the command
/// nobody wrote a test for. Deriving the vocabulary from the source means a
/// **new** command that draws no response fails here on the day it is added.
///
/// The two allow-lists are the whole content of the test, so they are explicit:
/// `SILENT_BY_DESIGN` is the commands that legitimately print nothing, and
/// `NOT_A_COMMAND` is the match arms that are not command keywords.
#[test]
fn every_command_the_parser_accepts_draws_a_response_or_is_listed() {
    use std::path::Path;

    /// Commands that change state and print nothing. SMT-LIB gives each of them
    /// only a `success`/`error` acknowledgement, which is suppressed at the
    /// default `:print-success false` — both references print nothing here.
    const SILENT_BY_DESIGN: &[&str] = &[
        "assert",
        "check-sat",          // answered, but as a verdict rather than a response body
        "check-sat-assuming", // ditto
        "declare-const",
        "declare-datatype",
        "declare-datatypes",
        "declare-fun",
        "declare-sort",
        "define-const",
        "define-fun",
        "define-sort",
        "exit", // a stated divergence: this front door does not stop at it
        "maximize",
        "minimize",
        "pop",
        "push",
        "reset", // rejected at parse time, never reaches a driver
        "reset-assertions",
        "set-info",
        "set-logic",  // silent for a real logic; `unsupported` otherwise
        "set-option", // silent for an honored option; `unsupported` otherwise
    ];

    let parse_rs = Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(Path::parent)
        .expect("workspace root")
        .join("crates/axeyum-smtlib/src/parse.rs");
    let source = std::fs::read_to_string(&parse_rs).expect("the parser source");
    let start = source
        .find("fn parse_command<'a>(")
        .expect("parse_command must exist -- if it was renamed this guard is blind");
    let body = &source[start..];
    let end = body
        .find(r#"other => return Err(SmtError::Unsupported(format!("command `{other}`")))"#)
        .expect("the fallback arm of parse_command");
    let body = &body[..end];

    // Every `"keyword" =>` / `"keyword" | "keyword" =>` arm in the dispatch.
    let mut keywords: Vec<String> = Vec::new();
    for (i, _) in body.match_indices('"') {
        let rest = &body[i + 1..];
        let Some(close) = rest.find('"') else {
            continue;
        };
        let word = &rest[..close];
        if word.is_empty()
            || !word
                .chars()
                .all(|c| c.is_ascii_lowercase() || c.is_ascii_digit() || c == '-')
        {
            continue;
        }
        // Keep only tokens that are followed by `=>` or `|`, i.e. match patterns.
        let after = rest[close + 1..].trim_start();
        if (after.starts_with("=>") || after.starts_with('|'))
            && !keywords.iter().any(|k| k == word)
        {
            keywords.push(word.to_owned());
        }
    }
    // Positive control: an empty or tiny vocabulary means the extraction broke,
    // and an extraction that finds nothing passes this test vacuously.
    assert!(
        keywords.len() >= 20,
        "only extracted {} command keywords from parse_command: {keywords:?}",
        keywords.len()
    );
    for required in [
        "get-model",
        "get-value",
        "get-unsat-core",
        "get-proof",
        "assert",
    ] {
        assert!(
            keywords.iter().any(|k| k == required),
            "`{required}` missing from the extracted vocabulary -- the extraction is wrong"
        );
    }

    let mut silent = Vec::new();
    for keyword in &keywords {
        if SILENT_BY_DESIGN.contains(&keyword.as_str()) {
            continue;
        }
        // A minimal script that reaches the command after a decided `sat` query.
        let argument = match keyword.as_str() {
            "get-value" => " (x)",
            "get-info" | "get-option" => " :produce-models",
            "echo" => " \"e\"",
            _ => "",
        };
        let text = format!(
            "(declare-const x Int)\n(assert (> x 5))\n(check-sat)\n({keyword}{argument})\n"
        );
        let Ok(responses) = solve_smtlib_session(&text, &SolverConfig::new()) else {
            // A parse error is a loud refusal, which is what this test is about.
            continue;
        };
        if responses.len() < 2 {
            silent.push(keyword.clone());
        }
    }
    assert!(
        silent.is_empty(),
        "these commands are accepted and produce NO response: {silent:?}. \
         Answer them, or add them to SILENT_BY_DESIGN with a reason."
    );
}
