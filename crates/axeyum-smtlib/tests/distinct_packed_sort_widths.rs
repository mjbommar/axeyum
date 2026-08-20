//! `distinct` must accept packed operands whose bit-widths differ, and must
//! still reject genuinely ill-sorted ones.
//!
//! A packed string or sequence encodes its SMT-LIB sort as a bit-vector whose
//! WIDTH carries the length bound, so two operands of the same SMT-LIB sort
//! routinely differ: `(seq.unit 0)` is `BitVec(17)`, a declared `(Seq Int)` is
//! `BitVec(115)`. `distinct` type-checked those for `Sort` equality before the
//! seq/string-aware pairwise expansion could align them, so it rejected queries
//! that `=` accepts.
//!
//! Found 2026-08-20 by refreshing a stale dominance audit:
//! `sat__regress0__strings__issue5542-strings-seq-mix.smt2` no longer PARSED,
//! while the committed audit still recorded it as decided `sat` with a replayed
//! model.
use axeyum_smtlib::parse_script;

fn parses(text: &str) -> Result<usize, String> {
    parse_script(text)
        .map(|s| s.assertions.len())
        .map_err(|e| format!("{e:?}"))
}

const SEQ: &str = "(set-logic ALL)\n(declare-fun c () (Seq Int))\n";
const STR: &str = "(set-logic ALL)\n(declare-fun s () String)\n";

#[test]
fn distinct_accepts_packed_sequences_of_different_widths() {
    assert!(
        parses(&format!(
            "{SEQ}(assert (distinct (seq.unit 0) c))\n(check-sat)"
        ))
        .is_ok()
    );
    // ...and the n-ary form, which expands pairwise.
    assert!(
        parses(&format!(
            "{SEQ}(declare-fun d () (Seq Int))\n(assert (distinct (seq.unit 0) c d))\n(check-sat)"
        ))
        .is_ok()
    );
}

#[test]
fn distinct_accepts_packed_strings_of_different_widths() {
    assert!(
        parses(&format!(
            "{STR}(assert (distinct (str.++ s s) s))\n(check-sat)"
        ))
        .is_ok()
    );
}

#[test]
fn distinct_still_agrees_with_equality() {
    // The defect was `distinct` rejecting what `=` accepts. Pin both.
    let eq = parses(&format!("{SEQ}(assert (= (seq.unit 0) c))\n(check-sat)"));
    let ne = parses(&format!(
        "{SEQ}(assert (distinct (seq.unit 0) c))\n(check-sat)"
    ));
    assert!(eq.is_ok() && ne.is_ok(), "eq={eq:?} distinct={ne:?}");
}

#[test]
fn distinct_still_rejects_genuinely_ill_sorted_arguments() {
    // The exemption must not become "any two bit-vectors". A sequence against
    // an integer is a real sort error and stays one.
    let mixed = parses(&format!("{SEQ}(assert (distinct c 1))\n(check-sat)"));
    assert!(mixed.is_err(), "Seq vs Int must not parse: {mixed:?}");

    // Two honest bit-vectors of different widths are still ill-sorted. Widths
    // chosen to be outside every packed-string and packed-sequence length grid.
    let bv = parses(
        "(set-logic ALL)\n(declare-fun x () (_ BitVec 3))\n(declare-fun y () (_ BitVec 5))\n\
         (assert (distinct x y))\n(check-sat)",
    );
    assert!(bv.is_err(), "BitVec(3) vs BitVec(5) must not parse: {bv:?}");
}

#[test]
fn the_corpus_file_that_regressed_parses_again() {
    let text = "(set-logic ALL)\n\
        (declare-fun a () String)\n(declare-fun b () String)\n(declare-fun c () (Seq Int))\n\
        (assert (distinct b (str.++ a a)))\n\
        (assert (distinct (seq.unit 0) (seq.extract c 1 1)))\n\
        (assert (= (seq.len c) 1))\n(check-sat)";
    assert!(parses(text).is_ok(), "{:?}", parses(text));
}
