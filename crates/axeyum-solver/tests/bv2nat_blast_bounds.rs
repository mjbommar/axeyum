//! Bound-sensitivity soundness probes for the `bv2nat`-linear blast (P2.7 A.2).
//!
//! The bounded string front-end (ADR-0029) encodes a declared `String` as a
//! packed BV with a **well-formedness bound** `len(s) <= STRING_MAX_LEN`. That
//! bound is an encoding artifact, not a user constraint: in real (unbounded)
//! SMT-LIB string semantics a string of any length exists. A complete decision
//! over the *lowered* query must therefore never surface a bound-induced
//! contradiction as `unsat` — `(= (str.len s) 9)` with `STRING_MAX_LEN = 8` is
//! `sat` in the real theory (Z3 agrees) and must stay `sat`/`unknown` here.

use axeyum_solver::{CheckResult, SmtLibOutcome, SolverConfig, solve_smtlib};

fn run(text: &str) -> SmtLibOutcome {
    solve_smtlib(text, &SolverConfig::default()).expect("solve")
}

/// A length constraint *beyond* the encoder's bound: real semantics `sat`.
/// The bounded lowering cannot represent the witness, so `unknown` is the
/// honest verdict; `unsat` would be a wrong verdict vs the string theory.
#[test]
fn str_len_beyond_bound_is_never_unsat() {
    let out = run("\
(declare-const s String)
(assert (= (str.len s) 9))
(check-sat)
");
    assert!(
        !matches!(out.result, CheckResult::Unsat),
        "len(s) = 9 exceeds the encoding bound but is sat in the real string \
         theory; got {:?}",
        out.result
    );
}

/// Same class through an inequality: `len(s) > 8` is `sat` in the real theory.
#[test]
fn str_len_above_bound_inequality_is_never_unsat() {
    let out = run("\
(declare-const s String)
(assert (> (str.len s) 8))
(check-sat)
");
    assert!(
        !matches!(out.result, CheckResult::Unsat),
        "len(s) > 8 exceeds the encoding bound but is sat in the real string \
         theory; got {:?}",
        out.result
    );
}

/// Sum of two lengths beyond either bound but within the concat's reach: real
/// semantics `sat`; the bounded encoder can even witness it (8 + 8 = 16), so
/// `sat` is expected — this pins the sum shape as a non-regression.
#[test]
fn str_len_sum_within_reach_stays_sat() {
    let out = run("\
(declare-const a String)
(declare-const b String)
(assert (= (+ (str.len a) (str.len b)) 10))
(check-sat)
");
    assert!(
        matches!(out.result, CheckResult::Sat(_)),
        "|a| + |b| = 10 is within the two bounds (8+8); got {:?}",
        out.result
    );
}

/// A regex forcing a match longer than the encoding bound: `u ∈ L("abcdefghij")`
/// requires `len(u) = 10 > 8`. Real semantics: `sat` (Z3 agrees). The regex
/// match-length interval (`10 ≤ len(u) ≤ 10`) trips the bound-bite detector, so
/// the bounded `unsat` downgrades to an honest `unknown`.
#[test]
fn in_re_longer_than_bound_is_never_unsat() {
    let out = run("\
(declare-const u String)
(assert (str.in_re u (str.to_re \"abcdefghij\")))
(check-sat)
");
    assert!(
        !matches!(out.result, CheckResult::Unsat),
        "a 10-char regex match exists in the real theory (u can exceed the \
         bound); got {:?}",
        out.result
    );
}

/// The genuinely-unsat regex direction still decides: `u ∈ L(\"abc\")` forces
/// `len(u) = 3`, contradicting `len(u) = 2` at *every* bound — confirmed by the
/// unbounded length abstraction, so the `unsat` passes the gate.
#[test]
fn in_re_length_conflict_decides_unsat() {
    let out = run("\
(declare-const u String)
(assert (str.in_re u (str.to_re \"abc\")))
(assert (= (str.len u) 2))
(check-sat)
");
    assert!(
        matches!(out.result, CheckResult::Unsat),
        "u ∈ L(abc) with len(u) = 2 is unsat at every bound; got {:?}",
        out.result
    );
}

/// The genuinely-unsat direction must still decide: a *negative* length is
/// impossible at every length, bounded or not.
#[test]
fn str_len_negative_decides_unsat() {
    let out = run("\
(declare-const s String)
(assert (< (str.len s) 0))
(check-sat)
");
    assert!(
        matches!(out.result, CheckResult::Unsat),
        "a negative length is unsat in every semantics; got {:?}",
        out.result
    );
}

/// The pure-BV bound-bite class (found 2026-07-01, pre-existing on HEAD):
/// pinned 5-char strings concatenated (10 chars) as a prefix of an 8-bounded
/// variable. Real semantics: `sat` (Z3 agrees — `u` can be longer than the
/// encoding bound); the lowered BV query is unsat only because of the bound.
/// Caught by the bound-bite detector: the recorded length facts
/// (`len(s)=5`, `len(t)=5`, `prefixof ⟹ len(s)+len(t) ≤ len(u)`) force
/// `len(u) ≥ 10 > 8`, so the `unsat` downgrades to an honest `unknown`.
#[test]
fn concat_prefixof_beyond_bound_is_never_unsat() {
    let out = run("\
(declare-const s String)
(declare-const t String)
(declare-const u String)
(assert (= s \"abcde\"))
(assert (= t \"fghij\"))
(assert (str.prefixof (str.++ s t) u))
(check-sat)
");
    assert!(
        !matches!(out.result, CheckResult::Unsat),
        "prefixof(10-char, u) is sat in the real theory (u can be longer than \
         the bound); got {:?}",
        out.result
    );
}

/// A symbolically over-bound substring (every constant route to a > 8-char
/// string is already rejected at parse — sound): `substr(a, 0, 12) = b ++ c`
/// with `len(b) = 8 ∧ len(c) = 4` forces `len(a) ≥ 12 > 8`. Real semantics:
/// `sat` (Z3 agrees). The `len(substr) ≤ len(a)` fact + the equality's length
/// fact + the concat homomorphism trip the bound-bite detector, so the bounded
/// `unsat` downgrades to `unknown`.
#[test]
fn substr_longer_than_bound_is_never_unsat() {
    let out = run("\
(declare-const a String)
(declare-const b String)
(declare-const c String)
(assert (= (str.substr a 0 12) (str.++ b c)))
(assert (= (str.len b) 8))
(assert (= (str.len c) 4))
(check-sat)
");
    assert!(
        !matches!(out.result, CheckResult::Unsat),
        "a 12-char substring exists in the real theory (a can exceed the \
         bound); got {:?}",
        out.result
    );
}

/// Far beyond the bound *and* beyond the length field's range: `len(s) = 100`
/// over a 4-bit length field was refutable by the `bv2nat` range refuter alone
/// (pre-existing wrong-unsat class — Z3 says `sat`, a 100-char string exists).
/// The gate downgrades it like the rest of the family.
#[test]
fn str_len_far_beyond_bound_is_never_unsat() {
    let out = run("\
(declare-const s String)
(assert (= (str.len s) 100))
(check-sat)
");
    assert!(
        !matches!(out.result, CheckResult::Unsat),
        "len(s) = 100 is sat in the real string theory; got {:?}",
        out.result
    );
}

/// The lexicographic-gap class (coarse atoms): `"aaaaaaaa" < s < "aaaaaaab"`
/// is `sat` only with `len(s) ≥ 9` (s must extend the 8-`a` prefix) — Z3 says
/// `sat`, the bounded encoding cannot witness it. No length fact is derivable
/// from `str.<`, so the bite detector cannot see this; the *coarse-atom*
/// guard downgrades every unconfirmed bounded `unsat` on such scripts.
#[test]
fn lex_order_gap_beyond_bound_is_never_unsat() {
    let out = run("\
(declare-const s String)
(assert (str.< \"aaaaaaaa\" s))
(assert (str.< s \"aaaaaaab\"))
(check-sat)
");
    assert!(
        !matches!(out.result, CheckResult::Unsat),
        "a 9-char witness exists in the real theory; got {:?}",
        out.result
    );
}
