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

use crate::sexpr::{SExpr, read_all};

/// Packed per-symbol string length cap (mirrors `parse.rs::STRING_MAX_LEN`). A
/// declared string is representable iff its length is `≤` this, so a C2 length
/// bound must pin the var at or below it.
const STRING_MAX_LEN: i128 = 8;

/// Any integer literal of at least this magnitude is rejected (C3). The int-blast
/// is exact only below `2^31`; a larger literal (or one that, added to a bounded
/// quantity, crosses `2^31`) wraps modulo `2^32`, which can FLIP a comparison and
/// fabricate a spurious bounded-unsat. `2^20` dwarfs every real position/length
/// constant, so declining above it costs nothing and leaves ample headroom for
/// sums of `≤ cap` quantities.
const MAX_SAFE_INT_LITERAL: i128 = 1 << 20;

/// Returns `true` iff the raw SMT-LIB `input` is provably bounded-complete under
/// the conservative C1∧C2∧C3 test — i.e. a bounded-encoding `unsat` of it is a
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
    let phi = unwrap_annot(phi);
    if let SExpr::List(items) = phi
        && items.first().and_then(SExpr::atom) == Some("and")
    {
        return items[1..].iter().flat_map(guaranteed_conjuncts).collect();
    }
    vec![phi]
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
    let SExpr::List(items) = conj else {
        return None;
    };
    if items.len() != 3 {
        return None;
    }
    let op = items[0].atom()?;
    let lhs = &items[1];
    let rhs = &items[2];

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
    match e {
        SExpr::Atom(a) => integer_literal_too_large(a),
        SExpr::List(items) => {
            if let Some(head) = items.first().and_then(SExpr::atom)
                && FORBIDDEN_HEADS.contains(&head)
            {
                return true;
            }
            items.iter().any(has_unsafe_construct)
        }
    }
}

/// Heads that disqualify the query (C3). `str.to_int`/`str.from_int` can reach
/// `10^len ≥ 2^31`; `*`/`div`/`mod`/`rem` are nonlinear (a product of bounded
/// quantities can exceed `2^31`); the binders/definitions can hide an unbounded
/// Int or String behind a name or quantifier.
const FORBIDDEN_HEADS: &[&str] = &[
    "str.to_int",
    "str.from_int",
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
             (assert (<= (str.len s) 8))\n(assert (str.contains s \"z\"))\n(check-sat)\n"
        ));
    }

    #[test]
    fn flipped_and_eq_length_bounds_count() {
        assert!(is_bounded_complete(
            "(set-logic QF_S)\n(declare-fun s () String)\n(assert (>= 8 (str.len s)))\n(check-sat)\n"
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
        // `<= 12` allows len 9..12 which the packed sort cannot represent.
        assert!(!is_bounded_complete(
            "(set-logic QF_S)\n(declare-fun s () String)\n(assert (<= (str.len s) 12))\n(check-sat)\n"
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
    fn str_to_int_declines() {
        // C3: str.to_int can reach 10^len ≥ 2^31.
        assert!(!is_bounded_complete(
            "(set-logic QF_SLIA)\n(declare-fun s () String)\n\
             (assert (<= (str.len s) 8))\n(assert (> (str.to_int s) 5))\n(check-sat)\n"
        ));
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
