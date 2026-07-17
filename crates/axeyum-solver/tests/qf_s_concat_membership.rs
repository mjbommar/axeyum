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
#![cfg(feature = "full")]
#![allow(clippy::similar_names)]

use std::time::Duration;

use axeyum_ir::Value;
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

/// The model binding for a declared string variable, as code points, looked up in
/// the **script's own arena** (its `SymbolId`s are what the model uses).
fn binding(script: &axeyum_smtlib::Script, model: &axeyum_solver::Model, name: &str) -> Vec<u32> {
    // Current front-door models bind the user-declared symbol. Older word-route
    // internals use internal `!weq!<name>` aliases, so keep that fallback without
    // crossing the arena's public/internal symbol namespaces.
    let mut candidates = Vec::new();
    if let Some(sym) = script.arena.find_symbol(name) {
        candidates.push(sym);
    }
    if let Some(sym) = script.arena.find_internal_symbol(&format!("!weq!{name}")) {
        candidates.push(sym);
    }
    for sym in candidates {
        if let Some(Value::Seq(elems)) = model.get(sym) {
            return elems
                .iter()
                .map(|v| u32::try_from(v.scalar_code()).unwrap_or(0))
                .collect();
        }
    }
    Vec::new()
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
    let x = binding(&script, &model, "x");
    let y = binding(&script, &model, "y");
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
fn concat_membership_unsat_shape_certified_unsat() {
    // (x ++ "B" ++ y) ∈ L("AAA").  Every value of the concat contains a 'B', but
    // "AAA" has none, so this is UNSAT — certified by the coarse-shape emptiness check
    // (task #55): `shape = Σ*·"B"·Σ*`, and `"AAA" ∩ shape = ∅`.  It must NEVER be `sat`.
    let s = r#"(set-logic QF_S)
(declare-const x String)
(declare-const y String)
(assert (str.in_re (str.++ x "B" y) (str.to_re "AAA")))
(check-sat)"#;
    assert!(
        !matches!(decide(s), Ok(CheckResult::Sat(_))),
        "UNSAT membership-over-concat wrongly reported sat"
    );
    assert_eq!(
        decide(s),
        Ok(CheckResult::Unsat),
        "coarse-shape emptiness should certify this concat membership UNSAT"
    );
}

#[test]
fn concat_membership_empty_language_certified_unsat() {
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
    assert_eq!(decide(s), Ok(CheckResult::Unsat));
}

// ---------------------------------------------------------------------------
// Task #55: coarse-shape concat emptiness (unsat), joint product-search (sat), and
// the trivial-length-atom skeleton pass — the deferred `norn-*` decide-rate slice.
// ---------------------------------------------------------------------------

#[test]
fn concat_emptiness_over_part_language_certified_unsat() {
    // The `norn-simp-rew` reason: b ++ x with x ∈ (a-u)* must be ∉ (a-u)*, but
    // b ∈ [a-u] and x ∈ (a-u)* ⇒ b ++ x ∈ (a-u)* — contradiction. The coarse-shape
    // emptiness uses x's OWN positive membership as the part shape:
    // `shape = "b"·(a-u)*`, `negatives = {(a-u)*}`, and `"b"(a-u)* ∩ ∁(a-u)* = ∅`.
    let s = r#"(set-logic QF_S)
(declare-const x String)
(assert (str.in_re x (re.* (re.range "a" "u"))))
(assert (not (str.in_re (str.++ "b" x) (re.* (re.range "a" "u")))))
(check-sat)"#;
    assert_eq!(
        decide(s),
        Ok(CheckResult::Unsat),
        "b ++ x ∈ (a-u)* forced by x ∈ (a-u)* — negated membership is UNSAT"
    );
}

#[test]
fn joint_product_search_tight_whole_loose_parts_sat_replays() {
    // The `norn-360` shape: the WHOLE `x ++ "z" ++ y` is tight (x only a's, y only
    // b's, via `a* z b*`), while the parts are only loosely `(a|b)*`. The staged
    // per-part witness cannot align them (it might pick x = "b"); the joint search over
    // `⋂R ∩ shape` must. The Seq-level replay is the sole `sat` gate.
    let s = r#"(set-logic QF_S)
(declare-const x String)
(declare-const y String)
(assert (str.in_re (str.++ x "z" y) (re.++ (re.* (str.to_re "a")) (re.++ (str.to_re "z") (re.* (str.to_re "b"))))))
(assert (str.in_re x (re.* (re.union (str.to_re "a") (str.to_re "b")))))
(assert (str.in_re y (re.* (re.union (str.to_re "a") (str.to_re "b")))))
(check-sat)"#;
    let mut script = parse_script(s).expect("parse");
    let CheckResult::Sat(model) = decide_word_only_script(&mut script, &cfg()).expect("decide")
    else {
        panic!("expected sat");
    };
    // Independently re-check the witnessed concatenation against every constraint.
    let x = binding(&script, &model, "x");
    let y = binding(&script, &model, "y");
    let mut whole = x.clone();
    whole.push(u32::from(b'z'));
    whole.extend_from_slice(&y);
    let a_star = Regex::star(Regex::character(u32::from(b'a')));
    let b_star = Regex::star(Regex::character(u32::from(b'b')));
    let whole_re = Regex::concat(
        Regex::concat(a_star, Regex::character(u32::from(b'z'))),
        b_star,
    );
    assert!(
        matches(&whole_re, &whole),
        "witnessed x={x:?} y={y:?} whole={whole:?} must be in a* z b*"
    );
}

#[test]
fn joint_product_search_negated_concat_membership_sat_replays() {
    // The `norn-nel-bug` shape: a positive AND a negated concat membership over the
    // same `"a" ++ v ++ "b"`. The joint search must pick v so the whole avoids the
    // negated language while the parts stay loose. Seq-level replay is the sole gate.
    let s = r#"(set-logic QF_S)
(declare-const v String)
(assert (str.in_re v (re.* (re.range "a" "u"))))
(assert (str.in_re (str.++ "a" v "b") (re.* (re.range "a" "u"))))
(assert (not (str.in_re (str.++ "a" v "b") (re.++ (re.* (str.to_re "a")) (re.++ (str.to_re "b") (re.* (str.to_re "b")))))))
(check-sat)"#;
    assert!(
        matches!(decide(s), Ok(CheckResult::Sat(_))),
        "expected sat via the joint product search"
    );
}

#[test]
fn concat_membership_actually_sat_not_over_refuted() {
    // Soundness: a concat that IS satisfiable must NOT be certified unsat by the
    // coarse-shape emptiness. b ++ x ∈ (a-u)* with x ∈ (a-u)* is SAT (x = "" ⇒ "b").
    // `shape = "b"(a-u)*`, `positives = {(a-u)*, shape}`, non-empty ⇒ never refuted.
    let s = r#"(set-logic QF_S)
(declare-const x String)
(assert (str.in_re x (re.* (re.range "a" "u"))))
(assert (str.in_re (str.++ "b" x) (re.* (re.range "a" "u"))))
(check-sat)"#;
    assert!(
        matches!(decide(s), Ok(CheckResult::Sat(_))),
        "a satisfiable concat membership must not be over-refuted to unsat"
    );
}

#[test]
fn trivial_length_guard_does_not_collapse_word_skeleton() {
    // A tautological `(<= 0 (str.len x))` guard must NOT collapse the membership
    // skeleton (task #55): the online route builds and decides the row.
    let with_trivial = r#"(set-logic QF_S)
(declare-const x String)
(assert (str.in_re x (re.range "a" "u")))
(assert (<= 0 (str.len x)))
(check-sat)"#;
    let script = parse_script(with_trivial).expect("parse");
    assert!(
        !script.word_skeleton.is_empty(),
        "a trivial (<= 0 (str.len x)) guard must not collapse the word skeleton"
    );

    // A NON-trivial length atom is still outside the skeleton fragment — it declines
    // (the pass is deliberately narrow to only the always-true shapes).
    let with_real_len = r#"(set-logic QF_S)
(declare-const x String)
(assert (str.in_re x (re.range "a" "u")))
(assert (<= (str.len x) 5))
(check-sat)"#;
    let script2 = parse_script(with_real_len).expect("parse");
    assert!(
        script2.word_skeleton.is_empty(),
        "a real length bound must still collapse the word skeleton (narrow pass)"
    );
}
