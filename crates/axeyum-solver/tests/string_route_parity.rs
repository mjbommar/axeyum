//! Differential gate: the **two independent string decision procedures**, head
//! to head on instances both can decide.
//!
//! ## Why this did not exist
//!
//! This workspace decides `QF_S` two ways:
//!
//! * the **bounded** route (`axeyum_solver::strings`) — a string is a
//!   `(len, content)` pair of bit-vectors, no new IR sort, regex membership by a
//!   Thompson NFA simulated over the bounded positions. Reached through the
//!   shipped front door [`solve_smtlib`].
//! * the **online CDCL(T)** route ([`check_qf_s_online_cdclt`]) over the
//!   `axeyum-strings` crate — regex derivatives, word-equation arrangements,
//!   certified theory conflicts.
//!
//! They are composed *complementarily*, which is the problem. `apply_word_route`
//! adds `sat` **only where the verdict is `unknown`**, and
//! `upgrade_bounded_string_unknown` turns `unknown` into `unsat` via the
//! unbounded abstraction. Each route only ever fills the other's gaps, so **in
//! the shipped product the two can never be observed disagreeing** — a wrong
//! verdict from either is invisible to the other by construction.
//!
//! Every existing string differential (`qf_s_online_differential_fuzz`,
//! `simplex_lra_fallback_differential`, …) compares *one* route against Z3, and
//! the Z3 fuzzes need `--features z3`, so on a default checkout nothing at all
//! relates these two procedures. `docs/refactor-2026-08/03-solver-decomposition.md`
//! records the measurement that produced this file.
//!
//! ## What it asserts
//!
//! For each instance, run both routes and require:
//!
//! 1. neither contradicts the declared `:status` (ground truth, never consulted
//!    while solving);
//! 2. where **both** are conclusive, they agree.
//!
//! `unknown` from either side is not a failure — the routes have genuinely
//! different completeness — but a run in which *nothing* was conclusive on both
//! sides proves nothing, so [`the_two_routes_agree_where_both_decide`] **fails
//! closed** below a floor. That is the trap this repository keeps hitting: a
//! differential that quietly compares nothing still exits 0.
//!
//! Gated on `full` because both entry points live behind it. Run it as
//! `cargo test -p axeyum-solver --features full --test string_route_parity` and
//! CONFIRM A NONZERO TEST COUNT — without the flag this file compiles to an
//! empty binary that prints "running 0 tests ... ok" and exits 0.
#![cfg(feature = "full")]

use axeyum_solver::{
    CheckResult, SolverConfig, check_qf_s_online_cdclt_with_memberships, solve_smtlib,
};

/// `(name, script)`. Every script declares its `:status`, so each route is also
/// checked against ground truth independently of the other.
///
/// Deliberately small and hand-written rather than sampled from the corpus: both
/// routes must be *able* to decide these, which is what makes disagreement
/// meaningful. Shapes are chosen to sit inside the bounded route's `max_len ≤ 16`
/// window while still exercising the operators where the two procedures reason
/// completely differently — membership, concatenation, and their interaction.
const CORPUS: &[(&str, &str)] = &[
    (
        "literal membership, holds",
        r#"(set-logic QF_S)
(set-info :status sat)
(declare-fun x () String)
(assert (= x "ab"))
(assert (str.in_re x (re.++ (str.to_re "a") (str.to_re "b"))))
(check-sat)"#,
    ),
    (
        "literal membership, refuted",
        r#"(set-logic QF_S)
(set-info :status unsat)
(declare-fun x () String)
(assert (= x "ab"))
(assert (str.in_re x (re.++ (str.to_re "a") (str.to_re "c"))))
(check-sat)"#,
    ),
    (
        "star membership of a fixed word",
        r#"(set-logic QF_S)
(set-info :status sat)
(declare-fun x () String)
(assert (= x "aaa"))
(assert (str.in_re x (re.* (str.to_re "a"))))
(check-sat)"#,
    ),
    (
        "star membership refuted by one wrong character",
        r#"(set-logic QF_S)
(set-info :status unsat)
(declare-fun x () String)
(assert (= x "aab"))
(assert (str.in_re x (re.* (str.to_re "a"))))
(check-sat)"#,
    ),
    (
        "union membership",
        r#"(set-logic QF_S)
(set-info :status sat)
(declare-fun x () String)
(assert (= x "b"))
(assert (str.in_re x (re.union (str.to_re "a") (str.to_re "b"))))
(check-sat)"#,
    ),
    (
        "concatenation equality, holds",
        r#"(set-logic QF_S)
(set-info :status sat)
(declare-fun x () String)
(declare-fun y () String)
(assert (= x "ab"))
(assert (= y "cd"))
(assert (= (str.++ x y) "abcd"))
(check-sat)"#,
    ),
    (
        "concatenation equality, refuted",
        r#"(set-logic QF_S)
(set-info :status unsat)
(declare-fun x () String)
(declare-fun y () String)
(assert (= x "ab"))
(assert (= y "cd"))
(assert (= (str.++ x y) "abce"))
(check-sat)"#,
    ),
    (
        "two literals cannot be equal",
        r#"(set-logic QF_S)
(set-info :status unsat)
(declare-fun x () String)
(assert (= x "a"))
(assert (= x "b"))
(check-sat)"#,
    ),
    (
        "membership and a word equation together",
        r#"(set-logic QF_S)
(set-info :status unsat)
(declare-fun x () String)
(declare-fun y () String)
(assert (= x "a"))
(assert (= y "b"))
(assert (str.in_re (str.++ x y) (str.to_re "ba")))
(check-sat)"#,
    ),
    (
        "empty word is in the star of anything",
        r#"(set-logic QF_S)
(set-info :status sat)
(declare-fun x () String)
(assert (= x ""))
(assert (str.in_re x (re.* (str.to_re "z"))))
(check-sat)"#,
    ),
];

/// `sat` / `unsat` / `unknown`, so the two routes' differently-typed results are
/// comparable without unwrapping a `Model`.
fn verdict(result: &CheckResult) -> &'static str {
    match result {
        CheckResult::Sat(_) => "sat",
        CheckResult::Unsat => "unsat",
        CheckResult::Unknown(_) => "unknown",
    }
}

/// The bounded route, through the SHIPPED front door.
///
/// Deliberately not a hand-assembled call into `axeyum_solver::strings`:
/// `solve_smtlib` is what applies `StringGate::confirm` and the composition
/// around it, and a diagnostic that bypasses the gate is exactly how
/// `explain_corpus` came to print a wrong `unsat` (see CLAUDE.md). Comparing the
/// route as shipped is the only comparison worth making.
fn bounded_route(script: &str) -> String {
    let config = SolverConfig::default();
    let outcome = solve_smtlib(script, &config).expect("the bounded front door parses and solves");
    verdict(&outcome.result).to_string()
}

/// The online CDCL(T) route, on the parser's `Seq`-level side channel.
///
/// **Not** `script.assertions`: those are the *packed bit-vector* view the
/// bounded route consumes, and feeding them here declines every query with
/// "non-sequence equality atom outside the `QF_S` online CDCL(T) scope" — measured
/// on all ten instances below before this function was written this way. The two
/// procedures do not share an input representation at all; the parser builds a
/// first-class `Sort::Seq` word-equation problem as a side channel
/// (`Script::word_skeleton`, `parse.rs:510`) and that is what
/// `apply_online_string_route` feeds the route in `smtlib.rs`.
///
/// This is a large part of why no differential existed: the obvious comparison
/// silently compares nothing.
fn online_route(script: &str) -> Option<String> {
    let mut parsed = axeyum_smtlib::parse_script(script).expect("script parses");
    if parsed.word_skeleton.is_empty() {
        return None; // the parser captured no Seq-level problem for this script
    }
    if parsed.word_skeleton_opaque_terms > 0 {
        // The shipped route refuses to trust `sat` on an opaque fixed-splice
        // skeleton, so comparing its raw verdict here would be comparing
        // something the product never uses.
        return None;
    }
    let config = SolverConfig::default();
    let skeleton = parsed.word_skeleton.clone();
    let memberships = parsed.word_skeleton_memberships.clone();
    let result = check_qf_s_online_cdclt_with_memberships(
        &mut parsed.arena,
        &skeleton,
        &memberships,
        &config,
    );
    Some(verdict(&result).to_string())
}

fn declared_status(script: &str) -> String {
    axeyum_smtlib::parse_script(script)
        .expect("script parses")
        .status
        .expect("every corpus entry declares :status")
}

/// Layer 1: neither route contradicts the declared `:status`.
///
/// This is oracle-free — the status is the benchmark's own ground truth — so it
/// runs on a default checkout, unlike the Z3 differentials.
#[test]
fn neither_route_contradicts_the_declared_status() {
    for (name, script) in CORPUS {
        let expected = declared_status(script);
        let mut routes = vec![("bounded", bounded_route(script))];
        if let Some(online) = online_route(script) {
            routes.push(("online", online));
        }
        for (route, got) in routes {
            assert!(
                got == expected || got == "unknown",
                "{route} route answered {got} on {name}, whose declared status is {expected}"
            );
        }
    }
}

/// Layer 2: where both routes are conclusive, they agree — and enough of them
/// are conclusive for that to mean something.
#[test]
fn the_two_routes_agree_where_both_decide() {
    /// Instances on which BOTH routes must reach a verdict, pinned at the
    /// measured value (9 of 10; the tenth is `unknown` on both sides).
    ///
    /// This is not decoration. The first version of this file fed the online
    /// route `script.assertions` instead of the parser's `Seq` side channel, so
    /// it decided **0 of 10** and every comparison was vacuous — and without
    /// this floor the suite would have reported two green tests over an empty
    /// comparison. Raise it as coverage improves; never lower it to make a red
    /// run green.
    const MIN_BOTH_CONCLUSIVE: usize = 9;

    let mut both = 0usize;
    let mut only_bounded = Vec::new();
    let mut only_online = Vec::new();

    for (name, script) in CORPUS {
        let bounded = bounded_route(script);
        let Some(online) = online_route(script) else {
            only_bounded.push(*name);
            continue;
        };
        match (bounded.as_str(), online.as_str()) {
            ("unknown", "unknown") => {}
            ("unknown", _) => only_online.push(*name),
            (_, "unknown") => only_bounded.push(*name),
            (b, o) => {
                assert_eq!(
                    b, o,
                    "the two string routes DISAGREE on {name}: bounded={b}, online={o}. \
                     One of them is wrong; the shipped composition cannot see this \
                     because each route only fills the other's gaps."
                );
                both += 1;
            }
        }
    }

    assert!(
        both >= MIN_BOTH_CONCLUSIVE,
        "only {both} of {} instances were decided by BOTH routes (floor {MIN_BOTH_CONCLUSIVE}); \
         this gate compared almost nothing. bounded-only: {only_bounded:?}, online-only: {only_online:?}",
        CORPUS.len()
    );
}
