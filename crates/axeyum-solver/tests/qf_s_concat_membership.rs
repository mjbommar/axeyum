//! Front-door integration gates for **membership over a symbolic `str.++`** (P2.7,
//! task #49): `(str.in_re (str.++ …) R)` whose subject is a concatenation of string
//! variables and literals, and membership atoms coupled with `str.++` word
//! equations.
//!
//! The parser rewrites `(str.in_re (str.++ p…) R)` into `w ∈ R ∧ w = p…` with a
//! fresh `w`, and the online CDCL(T) string route composes the membership with the
//! word part: it witnesses each membership class, pins the witnesses as extra word
//! equations, and re-solves so the concat components are chosen consistently — then
//! the combined model **replays at the `Seq` level against the skeleton** (the
//! concatenation *and* the membership both hold under the model). That replay is the
//! sole gate on `sat`, so no wrong `sat` is possible even if the shape heuristic is
//! imprecise; an undecided shape stays first-class `unknown`.

#![allow(clippy::similar_names)]

use std::time::Duration;

use axeyum_ir::{Sort, Value};
use axeyum_smtlib::parse_script;
use axeyum_solver::{CheckResult, SolverConfig, decide_word_only_script};
use axeyum_strings::regex::{Regex, matches};

fn cfg() -> SolverConfig {
    SolverConfig {
        timeout: Some(Duration::from_secs(10)),
        ..SolverConfig::default()
    }
}

/// Decides a word-first-fallback script through the harness-parity front door.
fn decide(src: &str) -> Result<CheckResult, String> {
    let mut script = parse_script(src).map_err(|e| e.to_string())?;
    decide_word_only_script(&mut script, &cfg()).map_err(|e| format!("{e:?}"))
}

/// The `!weq!<name>` model binding for a declared string variable, as code points,
/// looked up in the **script's own arena** (its `SymbolId`s are what the model uses).
fn binding(
    script: &mut axeyum_smtlib::Script,
    model: &axeyum_solver::Model,
    name: &str,
) -> Vec<u32> {
    // `TermArena::declare` is idempotent, so re-declaring the shared `!weq!` symbol
    // returns the same `SymbolId` the route bound.
    let sym = script
        .arena
        .declare(&format!("!weq!{name}"), Sort::string())
        .expect("declare weq symbol");
    match model.get(sym) {
        Some(Value::Seq(elems)) => elems
            .iter()
            .map(|v| u32::try_from(v.scalar_code()).unwrap_or(0))
            .collect(),
        _ => Vec::new(),
    }
}

fn lit_regex(s: &[u32]) -> Regex {
    let mut acc: Option<Regex> = None;
    for &c in s {
        acc = Some(match acc {
            None => Regex::character(c),
            Some(prev) => Regex::concat(prev, Regex::character(c)),
        });
    }
    acc.unwrap_or(Regex::Empty)
}

// ---------------------------------------------------------------------------
// SAT: membership over a symbolic concatenation, with a Seq-level witness replay.
// ---------------------------------------------------------------------------

#[test]
fn concat_membership_simple_sat_replays_at_seq_level() {
    // (x ++ "B" ++ y) ∈ L("AB").  Only solution: x = "A", y = "".  A symbolic
    // `str.++` in `str.in_re` trips the bounded cap, so this exercises the word-first
    // fallback membership-over-concat route.
    let s = r#"(set-logic QF_S)
(declare-const x String)
(declare-const y String)
(assert (str.in_re (str.++ x "B" y) (str.to_re "AB")))
(check-sat)"#;
    let mut script = parse_script(s).expect("parse");
    let CheckResult::Sat(model) = decide_word_only_script(&mut script, &cfg()).expect("decide")
    else {
        panic!("expected sat");
    };
    // Rebuild the witnessed concatenation and independently re-check it is in L("AB")
    // through the reference matcher — the Seq-level replay the soundness bar demands.
    let x = binding(&mut script, &model, "x");
    let y = binding(&mut script, &model, "y");
    let mut concat = x.clone();
    concat.push(u32::from(b'B'));
    concat.extend_from_slice(&y);
    let ab = lit_regex(&[u32::from(b'A'), u32::from(b'B')]);
    assert!(
        matches(&ab, &concat),
        "witnessed concat {concat:?} (x={x:?}, y={y:?}) must be in L(\"AB\")"
    );
}

#[test]
fn concat_membership_coupled_with_variable_membership_sat() {
    // cvc5 regress `issue5510`: (x ++ "B" ++ y) ∈ (A(A*|B))*  ∧  y ∈ "A".  The
    // membership on `y` must feed the decomposition of the concat (y is "A"), so the
    // concat's witness ends in "…BA".
    let s = r#"(set-logic QF_S)
(declare-fun x () String)
(declare-fun y () String)
(assert (str.in_re (str.++ x "B" y) (re.* (re.++ (str.to_re "A") (re.union (re.* (str.to_re "A")) (str.to_re "B"))))))
(assert (str.in_re y (str.to_re "A")))
(check-sat)"#;
    assert!(matches!(decide(s), Ok(CheckResult::Sat(_))), "expected sat");
}

#[test]
fn membership_coupled_with_str_concat_word_equation_sat() {
    // cvc5 regress `issue2060`: action ∈ "foobar:ab".*  ∧  action = a1 ++ k ++ a2
    // ∧ a1 = "foobar:a".  A single-variable membership coupled with a `str.++` word
    // equation — the witness for `action` must be threaded through the equation so
    // a1/k/a2 decompose consistently.
    let s = r#"(set-logic QF_S)
(declare-const action String)
(declare-const example_key String)
(assert (str.in_re action (re.++ (str.to_re "foobar:ab") (re.* re.allchar))))
(declare-const action_1 String)
(declare-const action_2 String)
(assert (and (= action (str.++ action_1 example_key action_2)) (= action_1 "foobar:a")))
(check-sat)"#;
    assert!(matches!(decide(s), Ok(CheckResult::Sat(_))), "expected sat");
}

#[test]
fn negated_concat_membership_sat() {
    // cvc5 regress `issue5520` shape: ("a" ++ x ++ "ca") ∈ R  (concat with leading
    // and trailing literals). A satisfiable membership over a symbolic concat.
    let s = r#"(set-logic QF_S)
(declare-fun x () String)
(assert (str.in_re (str.++ "a" x "ca") (re.* (re.union (str.to_re "a") (str.to_re "c")))))
(check-sat)"#;
    assert!(matches!(decide(s), Ok(CheckResult::Sat(_))), "expected sat");
}

// ---------------------------------------------------------------------------
// Soundness negatives: an UNSAT / undecidable membership-over-concat must NEVER be
// reported `sat`.
// ---------------------------------------------------------------------------

#[test]
fn concat_membership_unsat_shape_never_reported_sat() {
    // (x ++ "B" ++ y) ∈ L("AAA").  Every value of the concat contains a 'B', but
    // "AAA" has none, so this is UNSAT.  The route does not (yet) certify concat
    // emptiness, so it declines — but it must NEVER answer `sat`.
    let s = r#"(set-logic QF_S)
(declare-const x String)
(declare-const y String)
(assert (str.in_re (str.++ x "B" y) (str.to_re "AAA")))
(check-sat)"#;
    // A decline (reproduced bounded parse error) or a first-class `unknown` are both
    // sound here — only a `sat` would be a wrong verdict.
    assert!(
        !matches!(decide(s), Ok(CheckResult::Sat(_))),
        "UNSAT membership-over-concat wrongly reported sat"
    );
}

#[test]
fn concat_membership_empty_language_never_reported_sat() {
    // (x ++ "B" ++ y) ∈ re.none — the empty language, so UNSAT. Must never be `sat`.
    let s = r#"(set-logic QF_S)
(declare-const x String)
(declare-const y String)
(assert (str.in_re (str.++ x "B" y) re.none))
(check-sat)"#;
    assert!(
        !matches!(decide(s), Ok(CheckResult::Sat(_))),
        "membership over re.none must never be sat"
    );
}
