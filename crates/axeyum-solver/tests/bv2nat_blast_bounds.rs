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

/// Perf regression (found 2026-07-02 after a 9-hour scoreboard hang): a
/// regex-complement atom encodes to a heavily-shared reach-set DAG, and the
/// blast's Boolean-skeleton scan walked it once per root→node path —
/// exponential. With the memoized walk this decides in milliseconds; the
/// combination (`re.comp` + a `str.len` atom) is exactly what triggers the
/// blast on top of the complement encoding.
#[test]
fn re_comp_with_len_atom_decides_promptly() {
    use std::time::{Duration, Instant};
    let start = Instant::now();
    let out = run("\
(declare-const s String)
(assert (str.in_re s (re.comp (str.to_re \"a\"))))
(assert (= (str.len s) 1))
(assert (not (= s \"a\")))
(check-sat)
");
    assert!(
        matches!(out.result, CheckResult::Sat(_)),
        "a 1-char non-\"a\" string matches comp(a); got {:?}",
        out.result
    );
    assert!(
        start.elapsed() < Duration::from_secs(30),
        "the blast scan must be DAG-linear, took {:?}",
        start.elapsed()
    );
}

// ---------------------------------------------------------------------------
// P2.7 A.2 residual recoveries (2026-07-02): the gate's step-1 LIA projection,
// the empty-string exact-equality fact, and empty-language regex folding. Each
// recovered *unsat* is paired with a soundness probe that must still NOT be
// wrongly refuted.
// ---------------------------------------------------------------------------

/// Length homomorphism refutation: `xx = xx ++ yy` forces `len(yy) = 0`, which
/// contradicts `len(yy) > len(xx)` (with `len ≥ 0`). Bound-independent (holds
/// for strings of any length). The full abstraction mixes packed-BV
/// well-formedness with the LIA facts and returns `unknown`; the step-1a LIA
/// **projection** (drop the pure-BV assertions) decides it `unsat`.
#[test]
fn concat_len_fixpoint_decides_unsat() {
    let out = run("\
(declare-const xx String)
(declare-const yy String)
(assert (> (str.len yy) (str.len xx)))
(assert (= xx (str.++ xx yy)))
(check-sat)
");
    assert!(
        matches!(out.result, CheckResult::Unsat),
        "len(xx) = len(xx) + len(yy) ∧ len(yy) > len(xx) is unsat; got {:?}",
        out.result
    );
}

/// Soundness pair for the projection: dropping the well-formedness constraints
/// only *weakens* the length system, so a genuinely satisfiable shape must stay
/// non-`unsat`. `xx = xx ++ yy` is `sat` (yy = "").
#[test]
fn concat_len_fixpoint_sat_stays_sat() {
    let out = run("\
(declare-const xx String)
(declare-const yy String)
(assert (= xx (str.++ xx yy)))
(check-sat)
");
    assert!(
        !matches!(out.result, CheckResult::Unsat),
        "yy = \"\" satisfies xx = xx ++ yy; got {:?}",
        out.result
    );
}

/// Empty-string exact equality: `s = "" ⟺ len(s) = 0`, so `len(s) = 0 ∧ s ≠ ""`
/// is `unsat`. The weaker `fresh_bool ∧ (len = 0)` relaxation left this
/// satisfiable; the exact fact refutes it in step 1. Bound-independent.
#[test]
fn empty_string_len_zero_decides_unsat() {
    let out = run("\
(declare-const yy String)
(assert (= (str.len yy) 0))
(assert (not (= yy \"\")))
(check-sat)
");
    assert!(
        matches!(out.result, CheckResult::Unsat),
        "len(yy) = 0 ∧ yy ≠ \"\" is unsat; got {:?}",
        out.result
    );
}

/// Soundness pair for the exact empty-string fact: a non-empty length is
/// consistent with a non-empty string, so this must stay non-`unsat`.
#[test]
fn empty_string_nonzero_len_stays_sat() {
    let out = run("\
(declare-const yy String)
(assert (= (str.len yy) 1))
(assert (not (= yy \"\")))
(check-sat)
");
    assert!(
        matches!(out.result, CheckResult::Sat(_)),
        "a 1-char string is non-empty; got {:?}",
        out.result
    );
}

/// Empty-language regex fold: `re.comp re.all` = `Σ* \\ Σ*` = `∅`, so
/// `s ∈ re.comp re.all` is `false` for a string of *any* length — the atom
/// folds to the constant `false` (a non-coarse ground atom), and the bounded
/// `unsat` passes the gate. Bound-independent.
#[test]
fn comp_all_empty_language_decides_unsat() {
    let out = run("\
(declare-const s String)
(assert (str.in_re s (re.comp re.all)))
(check-sat)
");
    assert!(
        matches!(out.result, CheckResult::Unsat),
        "L(comp(re.all)) = ∅ so the atom is false; got {:?}",
        out.result
    );
}

/// Empty-language via `re.inter` of disjoint languages: `comp(Σ Σ*)` = `{ε}`
/// and `a Σ*` needs length ≥ 1, so the product accepts nothing → `unsat`.
#[test]
fn inter_disjoint_empty_language_decides_unsat() {
    let out = run("\
(declare-const x String)
(assert (str.in_re x (re.inter (re.comp (re.++ re.allchar (re.* re.allchar))) (re.++ (str.to_re \"a\") (re.* re.allchar)))))
(check-sat)
");
    assert!(
        matches!(out.result, CheckResult::Unsat),
        "the intersection language is empty; got {:?}",
        out.result
    );
}

/// Soundness pair for the empty-language fold: a **non-empty** regex whose
/// shortest word exceeds the encoder bound must NOT fold to `false` (its
/// language is not empty — there is a word, just a long one). The unbounded
/// reachability test sees the accepting state, so the atom keeps its bounded
/// encoding and the bounded `unsat` is honestly downgraded (real theory `sat`).
#[test]
fn long_but_nonempty_regex_is_never_unsat() {
    let out = run("\
(declare-const s String)
(assert (str.in_re s (re.++ (str.to_re \"aaaaaaaaa\") (re.* re.allchar))))
(check-sat)
");
    assert!(
        !matches!(out.result, CheckResult::Unsat),
        "a 9-char-prefixed word exists in the real theory; got {:?}",
        out.result
    );
}
