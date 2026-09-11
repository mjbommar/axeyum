//! `(distinct x 3)` with `x : Real` must parse, exactly as `(= x 3)` does.
//!
//! SMT-LIB's `Reals_Ints` rule embeds an `Int` subterm appearing in a `Real`
//! context via `to_real`. `=` and `ite` both applied it; `distinct` type-checked
//! its operands for identical sorts FIRST and coerced never, so it rejected a
//! term `=` accepts and both cvc5 and z3 decide.
//!
//! MEASURED 2026-09-11 on the `QF_UFLRA` parity list: the `RandomDecoupled`
//! family spells random real constraints with bare integer numerals under
//! `distinct`, and 68 of its 69 files died at `fd:parse` in ~35 ms with
//! `attempts=1` -- no solver route was ever entered -- while cvc5 decided
//! 198/200 of the division.
//!
//! These are ASSERTED verdicts, not `unknown`-tolerant corpus entries: a
//! regression here re-breaks parsing, and a suite that skips `unknown` would
//! stay green through it.

use axeyum_smtlib::parse_script;

fn decides(src: &str) -> bool {
    parse_script(src).is_ok()
}

#[test]
fn distinct_accepts_an_integer_numeral_against_a_real() {
    assert!(
        decides(
            "(set-logic QF_UFLRA)\n(declare-fun x () Real)\n(assert (distinct x 3))\n(check-sat)\n"
        ),
        "`(distinct x 3)` with x : Real must parse -- `=` accepts it and so must `distinct`"
    );
}

#[test]
fn equality_and_distinct_agree_on_the_same_mixed_term() {
    let eq = "(set-logic QF_UFLRA)\n(declare-fun x () Real)\n(assert (= x 3))\n(check-sat)\n";
    let ne =
        "(set-logic QF_UFLRA)\n(declare-fun x () Real)\n(assert (distinct x 3))\n(check-sat)\n";
    assert_eq!(
        decides(eq),
        decides(ne),
        "`=` and `distinct` must accept the same mixed Real/Int operands"
    );
}

#[test]
fn distinct_still_rejects_genuinely_ill_sorted_operands() {
    assert!(
        !decides(
            "(set-logic QF_UFLIA)\n(declare-fun b () Bool)\n(declare-fun i () Int)\n(assert (distinct b i))\n(check-sat)\n"
        ),
        "coercion must not make `(distinct Bool Int)` parse"
    );
}

#[test]
fn pure_integer_distinct_is_untouched() {
    assert!(
        decides(
            "(set-logic QF_LIA)\n(declare-fun i () Int)\n(assert (distinct i 3))\n(check-sat)\n"
        ),
        "a pure-Int `distinct` must keep integer semantics"
    );
}

#[test]
fn nested_real_arithmetic_under_distinct_parses() {
    // The shape the RandomDecoupled family actually uses.
    assert!(
        decides(
            "(set-logic QF_UFLRA)\n(declare-fun x () Real)\n(declare-fun y () Real)\n\
             (assert (distinct (+ (- (* 17 x) (* 2 y)) 4) 0))\n(check-sat)\n"
        ),
        "real arithmetic against a bare integer numeral under `distinct` must parse"
    );
}
