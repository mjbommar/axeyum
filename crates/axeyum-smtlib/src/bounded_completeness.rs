//! Conservative syntactic detector for **bounded-complete** string queries
//! (task #75).
//!
//! The bounded packed-BV string model (ADR-0029) answers a genuinely-unsat
//! string query with `Unknown("no model within the bounded integer width N;
//! widen the bound")` rather than `Unsat`, because the bounded encoding is
//! incomplete on two axes (int width ≤ 32, string length ≤ `STRING_MAX_LEN`).
//! When a query is **bounded-complete** — every satisfying assignment, if any,
//! provably fits both bounds — a bounded-no-model result IS a real `unsat`, and
//! the front door may upgrade it.
//!
//! [`is_bounded_complete`] decides a **conservative subset** of bounded-complete
//! queries by a purely *syntactic* pass over the raw SMT-LIB text (decoupled
//! from lowering). It returns `true` only when the sound condition C1∧C2∧C3 of
//! `docs/research/01-foundations/bounded-string-completeness-unsat.md` is
//! *witnessed by the text*, and **declines (returns `false`) on anything it does
//! not explicitly recognise as safe** — the sound default, since a wrong `true`
//! upgrades an inconclusive result to a wrong `unsat` (the worst bug class).
//!
//! - **C1** — no free unbounded Int: no `declare-fun`/`declare-const` returns
//!   `Int` (or `Real`).
//! - **C2** — every declared `String` var carries a top-level asserted upper
//!   length bound `(str.len s) ≤ k` (or `<`, `=`, flipped) with `k ≤
//!   STRING_MAX_LEN`, so it fits the packed representation. (A ground query — no
//!   free String var — satisfies C2 vacuously.)
//! - **C3** — every Int quantity provably `< 2^31`: no `str.to_int`/`str.from_int`
//!   (can reach `10^len`), no nonlinear `*`/`div`/`mod`/`rem`, no integer literal
//!   `≥ 2^20` (a large literal can wrap the width-32 int-blast and *fabricate* a
//!   bounded-unsat), and no binder/definition (`let`/`define-fun`/quantifier/
//!   `match`) that could hide unbounded structure.
//! - **C4** — the query is alphabet-complete for the byte encoding: it uses no
//!   code-point-, order-, or regex-sensitive string operator, every literal is
//!   byte-representable, and the maximum number of code points across all free
//!   strings plus the literal alphabet fits the 256-byte alphabet. Under those
//!   conditions any real model can be injectively renamed into the byte alphabet
//!   while preserving the supported structural string operations.

use std::collections::BTreeSet;

use crate::parse::decode_string_code_points;
use crate::sexpr::{SExpr, read_all};

/// Packed per-symbol string length cap (mirrors `parse.rs::STRING_MAX_LEN`). A
/// declared string is representable iff its length is `≤` this, so a C2 length
/// bound must pin the var at or below it.
const STRING_MAX_LEN: i128 = 12;

const BYTE_ALPHABET_CARDINALITY: usize = 256;
const BYTE_MAX_CODE_POINT: u32 = 255;

/// Any integer literal of at least this magnitude is rejected (C3). The int-blast
/// is exact only below `2^31`; a larger literal (or one that, added to a bounded
/// quantity, crosses `2^31`) wraps modulo `2^32`, which can FLIP a comparison and
/// fabricate a spurious bounded-unsat. `2^20` dwarfs every real position/length
/// constant, so declining above it costs nothing and leaves ample headroom for
/// sums of `≤ cap` quantities.
const MAX_SAFE_INT_LITERAL: i128 = 1 << 20;

/// Returns `true` iff the raw SMT-LIB `input` is provably bounded-complete under
/// the conservative C1∧C2∧C3∧C4 test — i.e. a bounded-encoding `unsat` of it is a
/// real `unsat`. Declines (`false`) on parse failure or any unrecognised
/// construct (the sound default).
#[must_use]
pub fn is_bounded_complete(input: &str) -> bool {
    let Ok(exprs) = read_all(input) else {
        return false;
    };
    analyze(&exprs)
}

fn analyze(exprs: &[SExpr]) -> bool {
    // C3 (structural): a single forbidden construct anywhere disqualifies the
    // whole script — scan first so an early reject short-circuits.
    for e in exprs {
        if has_unsafe_construct(e) {
            return false;
        }
    }

    // C1 + collect declared String vars for C2.
    let mut string_vars: Vec<&str> = Vec::new();
    for e in exprs {
        match classify_decl(e) {
            DeclKind::FreeNumericOrUnknown => return false, // C1 (Int/Real) or an
            // unrecognised sort / n-ary function — decline conservatively.
            DeclKind::StringVar(name) => string_vars.push(name),
            DeclKind::Bool | DeclKind::NotADecl => {}
        }
    }

    // C4: structural string operations are invariant under an injective
    // code-point renaming. Reserve every literal byte, then conservatively
    // reserve one distinct byte for every possible position of every free
    // string. If that total fits, any real structural model has a byte-model
    // image. Alphabet-observing operators were rejected by the first scan.
    let Some(literal_alphabet) = literal_byte_alphabet(exprs) else {
        return false;
    };
    let Ok(max_len) = usize::try_from(STRING_MAX_LEN) else {
        return false;
    };
    let Some(required_alphabet) = string_vars
        .len()
        .checked_mul(max_len)
        .and_then(|slots| slots.checked_add(literal_alphabet.len()))
    else {
        return false;
    };
    if required_alphabet > BYTE_ALPHABET_CARDINALITY {
        return false;
    }

    // C2: every declared String var needs a top-level asserted upper length bound
    // ≤ STRING_MAX_LEN. Gather the set of bounded var names from the guaranteed
    // (top-level / conjoined) conjuncts of every `assert`.
    let mut bounded: Vec<&str> = Vec::new();
    for e in exprs {
        if let Some(body) = assert_body(e) {
            for conj in guaranteed_conjuncts(body) {
                if let Some(var) = length_upper_bounded_var(conj) {
                    bounded.push(var);
                }
            }
        }
    }
    string_vars.iter().all(|v| bounded.contains(v))
}

// --- C1 / declarations -------------------------------------------------------

enum DeclKind<'a> {
    /// `(declare-fun/const … String)` 0-ary — a free string var (name).
    StringVar(&'a str),
    /// `(declare-fun/const … Bool)` 0-ary — harmless (no completeness axis).
    Bool,
    /// A free `Int`/`Real`, or an n-ary function, or an unrecognised sort →
    /// decline (C1, plus conservative catch-all).
    FreeNumericOrUnknown,
    /// Not a declaration command.
    NotADecl,
}

/// Classify a top-level command as a declaration of interest.
fn classify_decl(e: &SExpr) -> DeclKind<'_> {
    let SExpr::List(items) = e else {
        return DeclKind::NotADecl;
    };
    let head = items.first().and_then(SExpr::atom);
    let (name, sort) = match head {
        // (declare-const NAME SORT)
        Some("declare-const") if items.len() == 3 => (&items[1], &items[2]),
        // (declare-fun NAME (ARGS...) SORT)  — 0-ary iff ARGS is the empty list.
        Some("declare-fun") if items.len() == 4 => {
            let is_zero_ary = matches!(&items[2], SExpr::List(a) if a.is_empty());
            if !is_zero_ary {
                // An n-ary function (incl. any Int-returning UF) — decline.
                return DeclKind::FreeNumericOrUnknown;
            }
            (&items[1], &items[3])
        }
        _ => return DeclKind::NotADecl,
    };
    let Some(name) = name.atom() else {
        return DeclKind::FreeNumericOrUnknown; // odd NAME shape → decline
    };
    match sort.atom() {
        Some("String") => DeclKind::StringVar(name),
        Some("Bool") => DeclKind::Bool,
        // Int/Real (C1) and every other/compound sort (BitVec, Seq, Array, an
        // uninterpreted sort) → decline conservatively.
        _ => DeclKind::FreeNumericOrUnknown,
    }
}

// --- C2 / length bounds ------------------------------------------------------

/// The body of an `(assert BODY)` command, if this expr is one.
fn assert_body(e: &SExpr) -> Option<&SExpr> {
    match e {
        SExpr::List(items)
            if items.len() == 2 && items.first().and_then(SExpr::atom) == Some("assert") =>
        {
            Some(&items[1])
        }
        _ => None,
    }
}

/// The conjuncts of `phi` that are GUARANTEED true when the assertion holds:
/// `phi` itself, and — recursively — the conjuncts of a top-level `(and …)`.
/// `(! X …)` annotations are unwrapped. Disjunctions / `ite` / `not` are opaque
/// (their inner facts are NOT guaranteed), so we do not descend into them.
fn guaranteed_conjuncts(phi: &SExpr) -> Vec<&SExpr> {
    // Explicit worklist rather than recursion: the `and` spine's depth is the
    // source's, so a left-associated `(and (and (and …)))` aborted the process.
    // `work` is a stack, so conjuncts come out in source order.
    let mut out = Vec::new();
    let mut work = vec![phi];
    while let Some(node) = work.pop() {
        let node = unwrap_annot(node);
        if let SExpr::List(items) = node
            && items.first().and_then(SExpr::atom) == Some("and")
        {
            work.extend(items[1..].iter().rev());
        } else {
            out.push(node);
        }
    }
    out
}

/// Unwrap a `(! X :key val …)` annotation to `X` (e.g. `:named`).
fn unwrap_annot(e: &SExpr) -> &SExpr {
    if let SExpr::List(items) = e
        && items.len() >= 2
        && items.first().and_then(SExpr::atom) == Some("!")
    {
        return unwrap_annot(&items[1]);
    }
    e
}

/// If `conj` is an upper length bound `(str.len s) OP k` (or the flipped form)
/// that pins `len(s) ≤ STRING_MAX_LEN`, return the bounded var name `s`.
///
/// Recognised (k a non-negative literal):
/// - `(<= (str.len s) k)`  with `k ≤ MAX`      → len ≤ k ≤ MAX
/// - `(< (str.len s) k)`   with `k ≤ MAX+1`    → len ≤ k−1 ≤ MAX
/// - `(= (str.len s) k)` / `(= k (str.len s))` with `k ≤ MAX`
/// - `(>= k (str.len s))`  with `k ≤ MAX`      → len ≤ k
/// - `(> k (str.len s))`   with `k ≤ MAX+1`
fn length_upper_bounded_var(conj: &SExpr) -> Option<&str> {
    // PyEx materializes a Boolean branch as `(= (ite C 1 0) 0)` and then wraps
    // that equality in path-polarity `not`s. An odd number of `not`s asserts
    // `C` itself. Recover only that exact truth-preserving shape; the even
    // polarity asserts `not C` and is deliberately not treated as an upper
    // bound.
    if let Some(condition) = pyex_asserted_true_condition(conj) {
        return length_upper_bounded_var(condition);
    }

    let SExpr::List(items) = conj else {
        return None;
    };
    if items.len() != 3 {
        return None;
    }
    let op = items[0].atom()?;
    let lhs = &items[1];
    let rhs = &items[2];

    // Generated path guards commonly spell `len(s) <= k` as
    // `(<= (- (str.len s) k) 0)`. This is exact over mathematical integers.
    if op == "<="
        && nonneg_int_literal(rhs) == Some(0)
        && let Some((var, k)) = str_len_minus_nonneg(lhs)
        && k <= STRING_MAX_LEN
    {
        return Some(var);
    }

    // Try to read (str.len s) on one side and a literal on the other; `flipped`
    // tracks whether str.len is on the RIGHT (so the operator direction flips).
    let (var, k, str_len_on_left) =
        if let (Some(v), Some(k)) = (str_len_arg(lhs), nonneg_int_literal(rhs)) {
            (v, k, true)
        } else if let (Some(k), Some(v)) = (nonneg_int_literal(lhs), str_len_arg(rhs)) {
            (v, k, false)
        } else {
            return None;
        };

    // Reduce every shape to "len(var) ≤ bound" and require bound ≤ MAX.
    // `<=`/`>=` are non-strict (bound = k); `<`/`>` are strict (bound = k−1);
    // `=` pins len = k. Direction depends on which side str.len sits.
    let ok = match (op, str_len_on_left) {
        // `<=`/`>=` non-strict (len ≤ k) and `=` (len = k) all need k ≤ MAX.
        ("<=", true) | (">=", false) | ("=", _) => k <= STRING_MAX_LEN,
        // `<`/`>` strict (len ≤ k−1) needs k ≤ MAX+1.
        ("<", true) | (">", false) => k <= STRING_MAX_LEN + 1,
        // (>=, true): len ≥ k — a LOWER bound, useless for C2.
        // (>, true), (<, false), (<=, false): also lower bounds. Reject.
        _ => false,
    };
    ok.then_some(var)
}

/// The condition `C` from an exact asserted `PyEx` wrapper
/// `(not ... (= (ite C 1 0) 0) ...)` when the number of `not`s is odd.
fn pyex_asserted_true_condition(mut e: &SExpr) -> Option<&SExpr> {
    let mut negated = false;
    while let SExpr::List(items) = e
        && items.len() == 2
        && items[0].atom() == Some("not")
    {
        negated = !negated;
        e = &items[1];
    }
    if !negated {
        return None;
    }

    let equality = e.list()?;
    if equality.len() != 3 || equality[0].atom() != Some("=") {
        return None;
    }
    let (ite, zero) = if equality[1].list().is_some() {
        (&equality[1], &equality[2])
    } else {
        (&equality[2], &equality[1])
    };
    if nonneg_int_literal(zero) != Some(0) {
        return None;
    }
    let ite = ite.list()?;
    (ite.len() == 4
        && ite[0].atom() == Some("ite")
        && nonneg_int_literal(&ite[2]) == Some(1)
        && nonneg_int_literal(&ite[3]) == Some(0))
    .then_some(&ite[1])
}

/// `(str.len s) - k` with a bare string variable and non-negative literal `k`.
fn str_len_minus_nonneg(e: &SExpr) -> Option<(&str, i128)> {
    let items = e.list()?;
    if items.len() != 3 || items[0].atom() != Some("-") {
        return None;
    }
    Some((str_len_arg(&items[1])?, nonneg_int_literal(&items[2])?))
}

/// If `e` is `(str.len s)` with `s` a bare symbol atom, return `s`.
fn str_len_arg(e: &SExpr) -> Option<&str> {
    let SExpr::List(items) = e else {
        return None;
    };
    if items.len() == 2 && items[0].atom() == Some("str.len") {
        items[1].atom()
    } else {
        None
    }
}

/// Parse a bare non-negative decimal integer literal atom (SMT-LIB numerals are
/// unsigned; a negation is the list `(- n)`, not a bound RHS we accept here).
fn nonneg_int_literal(e: &SExpr) -> Option<i128> {
    let a = e.atom()?;
    if a.is_empty() || !a.bytes().all(|b| b.is_ascii_digit()) {
        return None;
    }
    a.parse::<i128>().ok()
}

// --- C3 / unsafe constructs --------------------------------------------------

/// `true` if `e` (recursively) contains any construct that breaks the C3
/// "every Int quantity < 2^31" guarantee or hides unbounded structure.
fn has_unsafe_construct(e: &SExpr) -> bool {
    // Iterative scan: see [`SExpr::descendants`]. A recursive one aborts the
    // process on a deeply nested source instead of returning an answer.
    e.descendants().any(|n| match n {
        SExpr::Atom(a) => integer_literal_too_large(a),
        SExpr::List(items) => items
            .first()
            .and_then(SExpr::atom)
            .is_some_and(|head| FORBIDDEN_HEADS.contains(&head)),
    })
}

/// The distinct byte values fixed by string literals, or `None` when a literal
/// contains a real SMT-LIB code point outside the packed byte alphabet.
fn literal_byte_alphabet(exprs: &[SExpr]) -> Option<BTreeSet<u32>> {
    fn collect(e: &SExpr, alphabet: &mut BTreeSet<u32>) -> Option<()> {
        match e {
            SExpr::Atom(atom) => {
                if let Some(inner) = atom.strip_prefix('"').and_then(|s| s.strip_suffix('"')) {
                    for code_point in decode_string_code_points(inner)? {
                        if code_point > BYTE_MAX_CODE_POINT {
                            return None;
                        }
                        alphabet.insert(code_point);
                    }
                }
                Some(())
            }
            SExpr::List(items) => items.iter().try_for_each(|item| collect(item, alphabet)),
        }
    }

    let mut alphabet = BTreeSet::new();
    exprs
        .iter()
        .try_for_each(|expr| collect(expr, &mut alphabet))?;
    Some(alphabet)
}

/// Heads that disqualify the query (C3/C4). `str.to_int`/`str.from_int` can reach
/// `10^len ≥ 2^31`; `*`/`div`/`mod`/`rem` are nonlinear (a product of bounded
/// quantities can exceed `2^31`); the binders/definitions can hide an unbounded
/// Int or String behind a name or quantifier. Code conversion, lexicographic
/// order, and regex operations observe the Unicode alphabet rather than only
/// structural word identities, so the byte model is not complete for them.
const FORBIDDEN_HEADS: &[&str] = &[
    "str.to_code",
    "str.to_int",
    "str.from_code",
    "str.from_int",
    "str.<",
    "str.<=",
    "str.in_re",
    "str.indexof_re",
    "str.replace_re",
    "str.replace_re_all",
    "*",
    "div",
    "mod",
    "rem",
    "let",
    "define-fun",
    "define-fun-rec",
    "define-funs-rec",
    "forall",
    "exists",
    "match",
];

/// `true` if `a` is a decimal integer literal (possibly the numeral inside a
/// larger token is not our concern — atoms are already tokenised) whose value is
/// `≥ MAX_SAFE_INT_LITERAL`. Non-numeric atoms are safe.
fn integer_literal_too_large(a: &str) -> bool {
    if a.is_empty() || !a.bytes().all(|b| b.is_ascii_digit()) {
        return false;
    }
    // Long digit strings certainly exceed the threshold (avoid i128 overflow on
    // absurd literals like the 29-digit `str-code-unsat` constant).
    if a.len() > 12 {
        return true;
    }
    a.parse::<i128>()
        .map_or(true, |v| v >= MAX_SAFE_INT_LITERAL)
}

#[cfg(test)]
mod tests {
    use std::fmt::Write as _;

    use super::is_bounded_complete;

    // --- POSITIVE: provably bounded-complete → true --------------------------

    #[test]
    fn ground_string_unsat_is_bounded_complete() {
        // No free vars at all → C2 vacuous, C1/C3 trivially hold.
        assert!(is_bounded_complete(
            "(set-logic QF_S)\n(assert (not (= (str.update \"AAAAAA\" 1 \"B\") \"ABAAAA\")))\n(check-sat)\n"
        ));
    }

    #[test]
    fn length_capped_string_var_is_bounded_complete() {
        // s explicitly capped < 3 ≤ MAX_LEN; only str.substr/str.len/str.update.
        assert!(is_bounded_complete(
            "(set-logic QF_SLIA)\n(declare-fun s () String)\n\
             (assert (not (= (str.substr (str.update \"AAAAAA\" 1 s) 5 1) \"A\")))\n\
             (assert (< (str.len s) 3))\n(check-sat)\n"
        ));
    }

    #[test]
    fn le_bound_at_max_len_is_bounded_complete() {
        assert!(is_bounded_complete(
            "(set-logic QF_S)\n(declare-fun s () String)\n\
             (assert (<= (str.len s) 12))\n(assert (str.contains s \"z\"))\n(check-sat)\n"
        ));
    }

    #[test]
    fn flipped_and_eq_length_bounds_count() {
        assert!(is_bounded_complete(
            "(set-logic QF_S)\n(declare-fun s () String)\n(assert (>= 12 (str.len s)))\n(check-sat)\n"
        ));
        assert!(is_bounded_complete(
            "(set-logic QF_S)\n(declare-fun s () String)\n(assert (= (str.len s) 4))\n(check-sat)\n"
        ));
    }

    #[test]
    fn bound_inside_top_level_and_counts() {
        assert!(is_bounded_complete(
            "(set-logic QF_S)\n(declare-fun s () String)\n\
             (assert (and (str.contains s \"a\") (<= (str.len s) 5)))\n(check-sat)\n"
        ));
    }

    #[test]
    fn odd_pyex_indicator_polarity_exposes_true_length_upper_bound() {
        assert!(is_bounded_complete(
            "(set-logic QF_SLIA)\n(declare-fun s () String)\n\
             (assert (not (not (not (= (ite (<= (- (str.len s) 1) 0) 1 0) 0)))))\n\
             (check-sat)\n"
        ));
    }

    // --- NEGATIVE (soundness): must return false -----------------------------

    #[test]
    fn free_int_var_declines() {
        // C1: a free Int → no-model-at-width-32 is genuinely inconclusive.
        assert!(!is_bounded_complete(
            "(set-logic QF_SLIA)\n(declare-fun x () Int)\n(declare-fun s () String)\n\
             (assert (< (str.len s) 3))\n(assert (> x 5))\n(check-sat)\n"
        ));
    }

    #[test]
    fn unbounded_string_var_declines() {
        // C2: s has no upper length bound → a real model may need s > cap
        // (the `(str.at s 100) = "x"` / `str.len s > 100` wrong-unsat traps).
        assert!(!is_bounded_complete(
            "(set-logic QF_S)\n(declare-fun s () String)\n(assert (= (str.at s 100) \"x\"))\n(check-sat)\n"
        ));
        assert!(!is_bounded_complete(
            "(set-logic QF_S)\n(declare-fun s () String)\n(assert (> (str.len s) 100))\n(check-sat)\n"
        ));
    }

    #[test]
    fn lower_bound_only_declines() {
        // `(>= (str.len s) 2)` bounds s from BELOW — does not cap it → decline.
        assert!(!is_bounded_complete(
            "(set-logic QF_S)\n(declare-fun s () String)\n(assert (>= (str.len s) 2))\n(check-sat)\n"
        ));
    }

    #[test]
    fn bound_above_max_len_declines() {
        // `<= 13` allows len 13 which the packed sort cannot represent.
        assert!(!is_bounded_complete(
            "(set-logic QF_S)\n(declare-fun s () String)\n(assert (<= (str.len s) 13))\n(check-sat)\n"
        ));
    }

    #[test]
    fn bound_hidden_in_disjunction_declines() {
        // The bound is not GUARANTEED (an `or` branch) → decline.
        assert!(!is_bounded_complete(
            "(set-logic QF_S)\n(declare-fun s () String)\n\
             (assert (or (str.contains s \"a\") (<= (str.len s) 3)))\n(check-sat)\n"
        ));
    }

    #[test]
    fn false_or_malformed_pyex_indicator_does_not_fake_an_upper_bound() {
        assert!(!is_bounded_complete(
            "(set-logic QF_SLIA)\n(declare-fun s () String)\n\
             (assert (not (not (= (ite (<= (- (str.len s) 1) 0) 1 0) 0))))\n\
             (check-sat)\n"
        ));
        assert!(!is_bounded_complete(
            "(set-logic QF_SLIA)\n(declare-fun s () String)\n\
             (assert (not (= (ite (<= (- (str.len s) 1) 0) 2 0) 0)))\n\
             (check-sat)\n"
        ));
    }

    #[test]
    fn str_to_int_declines() {
        // C3: str.to_int can reach 10^len ≥ 2^31.
        assert!(!is_bounded_complete(
            "(set-logic QF_SLIA)\n(declare-fun s () String)\n\
             (assert (<= (str.len s) 8))\n(assert (> (str.to_int s) 5))\n(check-sat)\n"
        ));
    }

    #[test]
    fn unicode_alphabet_observers_decline() {
        for assertion in [
            "(= (str.to_code s) 300)",
            r#"(str.< "\u{ff}" s)"#,
            r#"(str.in_re s (re.comp (str.to_re "A")))"#,
            r#"(str.contains s "\u{100}")"#,
        ] {
            let input = format!(
                "(set-logic QF_SLIA)\n(declare-fun s () String)\n\
                 (assert (= (str.len s) 1))\n(assert {assertion})\n(check-sat)\n"
            );
            assert!(!is_bounded_complete(&input), "must decline {assertion}");
        }
    }

    #[test]
    fn excessive_free_string_alphabet_capacity_declines() {
        let mut input = "(set-logic QF_S)\n".to_owned();
        for index in 0..22 {
            write!(
                &mut input,
                "(declare-fun s{index} () String)\n(assert (<= (str.len s{index}) 12))\n"
            )
            .expect("write bounded-completeness capacity case");
        }
        input.push_str("(check-sat)\n");
        assert!(!is_bounded_complete(&input));
    }

    #[test]
    fn nonlinear_mul_declines() {
        assert!(!is_bounded_complete(
            "(set-logic QF_SLIA)\n(declare-fun s () String)\n\
             (assert (<= (str.len s) 8))\n(assert (> (* (str.len s) (str.len s)) 3))\n(check-sat)\n"
        ));
    }

    #[test]
    fn large_int_literal_declines() {
        // A literal ≥ 2^20 can wrap the width-32 int-blast.
        assert!(!is_bounded_complete(
            "(set-logic QF_SLIA)\n(declare-fun s () String)\n\
             (assert (<= (str.len s) 8))\n(assert (< (str.len s) 9999999999))\n(check-sat)\n"
        ));
    }

    #[test]
    fn let_binder_declines() {
        assert!(!is_bounded_complete(
            "(set-logic QF_S)\n(declare-fun s () String)\n\
             (assert (let ((b (str.contains s \"a\"))) b))\n(assert (<= (str.len s) 5))\n(check-sat)\n"
        ));
    }

    #[test]
    fn n_ary_function_declines() {
        // A UF (even Bool-returning) → conservative decline in slice 1.
        assert!(!is_bounded_complete(
            "(set-logic QF_S)\n(declare-fun f (String) Bool)\n(declare-fun s () String)\n\
             (assert (<= (str.len s) 5))\n(assert (f s))\n(check-sat)\n"
        ));
    }
}
