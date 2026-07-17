//! Task #77 — the flat word route decides `sat` for `str.++`-equality word
//! equations coupling `str.from_int`/`str.substr` to their integer argument, and
//! stays sound (`unknown`, never a wrong verdict) when the coupling cannot be
//! inverted or is arithmetically constrained.
//!
//! Each script's string content exceeds the bounded ADR-0029 caps, so the bounded
//! encoder declines at parse and the word-first fallback is the sole decider. The
//! `sat` witnesses are replay-checked (the arrangement replay over the fresh-variable
//! word problem plus the exact `f(int) == word` inversion of every obligation).
#![cfg(feature = "full")]

use axeyum_ir::Value;
use axeyum_solver::{CheckResult, SolverConfig, solve_smtlib};

/// The sorted `Int` values bound in a `sat` model (task #79 pin inspection); panics if
/// the script is not decided `sat`. Symbol names are not exposed through `solve_smtlib`,
/// so tests assert over the *multiset* of integer bindings the model carries.
fn sat_int_values(src: &str) -> Vec<i128> {
    let CheckResult::Sat(model) = solve_smtlib(src, &SolverConfig::default())
        .expect("solve")
        .result
    else {
        panic!("expected sat");
    };
    let mut vals: Vec<i128> = model
        .iter()
        .filter_map(|(_, v)| match v {
            Value::Int(n) => Some(n),
            _ => None,
        })
        .collect();
    vals.sort_unstable();
    vals
}

/// A word-first-fallback decline surfaces as `Err(SolverError::Parse(..))` (the
/// original bounded error reproduced), which for this slice is a sound `unknown`.
fn is_sat(src: &str) -> bool {
    matches!(
        solve_smtlib(src, &SolverConfig::default()).map(|o| o.result),
        Ok(CheckResult::Sat(_))
    )
}

fn is_unknown(src: &str) -> bool {
    match solve_smtlib(src, &SolverConfig::default()) {
        Ok(o) => matches!(o.result, CheckResult::Unknown(_)),
        Err(_) => true,
    }
}

/// cvc5 `issue6834`: `str.substr` of a constant subject with a **symbolic** length,
/// forced to the empty string by the word equation (`t·"B"·t = "B"` ⇒ `t = ""`,
/// invertible to `a ≤ 0`).
#[test]
fn substr_symbolic_length_word_eq_is_sat() {
    let src = r#"(set-logic QF_SLIA)
(declare-fun a () Int)
(assert (= (str.++ (str.substr "AAAAAAAAAAAAAAAAAA" 0 a) "B" (str.substr "AAAAAAAAAAAAAAAAAA" 0 a)) "B"))
(check-sat)"#;
    assert!(
        is_sat(src),
        "issue6834-shaped substr word equation must decide sat"
    );
}

/// cvc5 `issue4379`: a `distinct` mixing a ground `str.from_int` (folded) and a
/// symbolic `str.from_int` (fresh variable, inverted back to its integer).
#[test]
fn from_int_in_distinct_is_sat() {
    let src = r#"(set-logic QF_SLIA)
(declare-const i7 Int)
(declare-const Str8 String)
(declare-const Str17 String)
(assert (distinct (str.++ "" "rvhhcnrvhhcnrvhhcn" "" Str8 (str.from_int 56)) (str.++ "" (str.from_int i7) "" Str17) Str17))
(check-sat)"#;
    assert!(
        is_sat(src),
        "issue4379-shaped from_int distinct must decide sat"
    );
}

/// cvc5 `type002` (task #78): `str.from_int(i)` under an arithmetic bound `(>= i 420)`,
/// coupled to a word equation forcing an interior `"0"`. The LIA-coupled route
/// enumerates candidate integers in `[420, ∞)`, pinning each to its decimal and
/// re-solving — `i = 500` (`x = "500" = "5"·"0"·"0"`, `y = "5"`, `z = "0"`) is a
/// replay-checked witness that satisfies the bound.
#[test]
fn from_int_type002_arith_bound_is_sat() {
    let src = r#"(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun y () String)
(declare-fun z () String)
(declare-fun i () Int)
(assert (>= i 420))
(assert (= x (str.from_int i)))
(assert (= x (str.++ y "0" z)))
(assert (not (= y "")))
(assert (not (= z "")))
(check-sat)"#;
    assert!(
        is_sat(src),
        "type002 (from_int under an arithmetic bound) must decide sat via LIA coupling"
    );
}

/// Soundness trap (task #78): a `str.from_int(i)` under a bound `(>= i 420)` forced by
/// the word equation to end in **non-digit** characters (`"aaaa…"`). cvc5 reports
/// `unsat` (no integer's decimal ends in `"a"`); every enumerated candidate's pin
/// conflicts with the word equation, so the coupled route must stay `unknown` — never a
/// wrong `sat` and never `unsat`.
#[test]
fn from_int_arith_bound_non_digit_suffix_is_unknown() {
    let src = r#"(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun y () String)
(declare-fun z () String)
(declare-fun i () Int)
(assert (>= i 420))
(assert (= x (str.from_int i)))
(assert (= x (str.++ y "0" z "aaaaaaaaaaaaaaaaaaaa")))
(assert (not (= y "")))
(assert (not (= z "")))
(check-sat)"#;
    assert!(
        !is_sat(src),
        "a from_int whose word equation forces non-digit content must never be a wrong sat"
    );
    assert!(
        is_unknown(src),
        "the non-digit-suffix from_int trap must stay unknown"
    );
}

/// Soundness trap (task #78): the arithmetic bounds on the `str.from_int` argument are
/// **jointly unsatisfiable** (`i >= 420 ∧ i <= 5`). The intersected integer range is
/// empty, so no candidate exists and no witness can be built — the route must stay
/// `unknown` (never a wrong `sat` from ignoring one of the bounds, and never `unsat`).
#[test]
fn from_int_unsat_arith_range_is_unknown_not_sat() {
    let src = r#"(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun y () String)
(declare-fun z () String)
(declare-fun i () Int)
(assert (>= i 420))
(assert (<= i 5))
(assert (= x (str.from_int i)))
(assert (= x (str.++ y "0" z)))
(assert (not (= y "")))
(assert (not (= z "")))
(check-sat)"#;
    assert!(
        !is_sat(src),
        "an empty from_int bound range must never yield a wrong sat"
    );
    assert!(
        is_unknown(src),
        "the empty-range from_int trap must stay unknown"
    );
}

/// A `str.from_int(i)` under an **equality** bound `(= i 700)` coupled to a word
/// equation the value satisfies (`"700" = "7"·"0"·"0"`) is `sat`; the single candidate
/// `700` is pinned and inverts back to `i = 700` (task #78, `IntBoundKind::Eq`).
#[test]
fn from_int_eq_bound_is_sat() {
    let src = r#"(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun y () String)
(declare-fun z () String)
(declare-fun i () Int)
(assert (= i 700))
(assert (= x (str.from_int i)))
(assert (= x (str.++ y "0" z)))
(assert (not (= y "")))
(assert (not (= z "")))
(check-sat)"#;
    assert!(
        is_sat(src),
        "an equality-bounded from_int coupled to a satisfiable word equation must be sat"
    );
}

/// Soundness trap: `str.from_int(i)` forced to a **non-decimal** string. cvc5 reports
/// `unsat` (no integer maps to `"BBB"`); the word route must report `unknown` — the
/// solved fresh-variable string does not invert, so no `sat` is emitted, and the flat
/// route never emits `unsat`.
#[test]
fn from_int_forced_non_decimal_is_unknown_not_sat() {
    let src = r#"(set-logic QF_SLIA)
(declare-fun i () Int)
(assert (= (str.++ "AAAAAAAAAAAAAAAAAAAA" (str.from_int i)) "AAAAAAAAAAAAAAAAAAAABBB"))
(check-sat)"#;
    assert!(
        !is_sat(src),
        "a non-invertible from_int obligation must never yield a wrong sat"
    );
    assert!(
        is_unknown(src),
        "the non-decimal from_int trap must stay unknown"
    );
}

/// Soundness trap: `str.from_int(i)` forced to a **leading-zero** string `"00"`, which
/// is not a canonical `str.from_int` output. cvc5 reports `unsat`; the word route must
/// stay `unknown` (the leading-zero value fails inversion).
#[test]
fn from_int_forced_leading_zero_is_unknown_not_sat() {
    let src = r#"(set-logic QF_SLIA)
(declare-fun i () Int)
(assert (= (str.++ "AAAAAAAAAAAAAAAAAAAA" (str.from_int i)) "AAAAAAAAAAAAAAAAAAAA00"))
(check-sat)"#;
    assert!(
        !is_sat(src),
        "a leading-zero from_int value must never yield a wrong sat"
    );
    assert!(
        is_unknown(src),
        "the leading-zero from_int trap must stay unknown"
    );
}

// ---------------------------------------------------------------------------
// Task #79 — constant `str.to_int` pins folded onto declared `Int` variables.
// ---------------------------------------------------------------------------

/// cvc5 `type001`: big-constant `str.from_int` (folded to its decimal string, a word
/// equality replayed by the arrangement search) alongside constant `str.to_int` pins on
/// declared `Int` variables. `i = str.to_int("783914785582390527685649") = 783…649`
/// (24-digit all-digit value) and `j = str.to_int("-783…") = -1` (a `'-'` is not a
/// digit). The word route decides `sat` and the model binds the exact pinned values.
#[test]
fn to_int_const_pins_type001_is_sat_with_exact_values() {
    let src = r#"(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun y () String)
(declare-fun i () Int)
(declare-fun j () Int)
(declare-fun z () String)
(assert (= x (str.from_int 4785582390527685649)))
(assert (= y (str.from_int (- 9))))
(assert (= i (str.to_int "783914785582390527685649")))
(assert (= j (str.to_int "-783914785582390527685649")))
(check-sat)"#;
    assert!(
        is_sat(src),
        "type001 must decide sat via constant to_int pins"
    );
    let vals = sat_int_values(src);
    assert!(
        vals.contains(&783_914_785_582_390_527_685_649_i128),
        "i must be pinned to the exact 24-digit str.to_int value, got {vals:?}"
    );
    assert!(
        vals.contains(&-1),
        "j = str.to_int of a signed literal must be pinned to -1, got {vals:?}"
    );
}

/// A leading-zero literal `str.to_int("007")` folds to `7` (leading zeros are valid for
/// `str.to_int`, unlike `str.from_int`). The pin binds the exact value.
#[test]
fn to_int_leading_zero_pins_exact_value() {
    let src = r#"(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun i () Int)
(assert (= x (str.++ "AAAAAAAAAAAAAAAAAAAA" "B")))
(assert (= i (str.to_int "007")))
(check-sat)"#;
    assert!(is_sat(src), "to_int leading-zero pin must decide sat");
    assert!(
        sat_int_values(src).contains(&7),
        "str.to_int(\"007\") must pin to 7"
    );
}

/// An empty / non-digit `str.to_int` literal folds to `-1` (SMT-LIB totality).
#[test]
fn to_int_non_digit_and_empty_pin_minus_one() {
    for lit in ["\"\"", "\"abc\"", "\"12x\"", "\" 5\""] {
        let src = format!(
            r#"(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun i () Int)
(assert (= x (str.++ "AAAAAAAAAAAAAAAAAAAA" "B")))
(assert (= i (str.to_int {lit})))
(check-sat)"#
        );
        assert!(is_sat(&src), "non-digit to_int pin ({lit}) must decide sat");
        assert!(
            sat_int_values(&src).contains(&-1),
            "str.to_int({lit}) must pin to -1"
        );
    }
}

/// Soundness trap: two constant `str.to_int` pins forcing **conflicting** values on one
/// variable (`i = 12` and `i = 13`) make the script unsat. The route never claims
/// `unsat`, so it must stay `unknown` — and must NOT emit a wrong `sat`.
#[test]
fn to_int_conflicting_pins_is_unknown_not_sat() {
    let src = r#"(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun i () Int)
(assert (= x (str.++ "AAAAAAAAAAAAAAAAAAAA" "B")))
(assert (= i (str.to_int "12")))
(assert (= i (str.to_int "13")))
(check-sat)"#;
    assert!(
        !is_sat(src),
        "conflicting to_int pins must never yield a wrong sat"
    );
    assert!(is_unknown(src), "conflicting to_int pins must stay unknown");
}

/// Soundness trap: a non-digit `str.to_int` pin folds to `-1`, so pinning it against a
/// digit value (`i = str.to_int("abc") = -1` **and** `i = str.to_int("5") = 5`) is a
/// conflict — the route must not paper over the exact `-1` fold and call it sat.
#[test]
fn to_int_non_digit_vs_digit_conflict_is_unknown_not_sat() {
    let src = r#"(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun i () Int)
(assert (= x (str.++ "AAAAAAAAAAAAAAAAAAAA" "B")))
(assert (= i (str.to_int "abc")))
(assert (= i (str.to_int "5")))
(check-sat)"#;
    assert!(
        !is_sat(src),
        "a non-digit (-1) vs digit (5) to_int conflict must never be a wrong sat"
    );
    assert!(
        is_unknown(src),
        "the -1-vs-5 to_int conflict must stay unknown"
    );
}

/// A `str.to_int` literal whose all-digit value overflows `i128` cannot be represented
/// exactly, so the pin is **declined** (→ `unknown`) rather than truncated to a wrong
/// integer. 40 digits exceeds `i128::MAX` (≈ 1.7·10^38, 39 digits).
#[test]
fn to_int_i128_overflow_is_declined_unknown() {
    let src = r#"(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun i () Int)
(assert (= x (str.++ "AAAAAAAAAAAAAAAAAAAA" "B")))
(assert (= i (str.to_int "9999999999999999999999999999999999999999")))
(check-sat)"#;
    assert!(
        !is_sat(src),
        "an i128-overflowing to_int literal must not be truncated to a wrong sat"
    );
    assert!(
        is_unknown(src),
        "an i128-overflowing to_int literal must stay unknown"
    );
}
