//! ADR-2000: WHERE the linear `distinct` encoding is allowed to fire, and where
//! it must not.
//!
//! The encoding replaces `(distinct t1 … tN)` with `⋀ᵢ f(tᵢ) = i` for a fresh
//! uninterpreted `f : S → Int`. That is exact, but only in POSITIVE polarity:
//! `f` is existentially quantified in effect, so under a negation the encoding
//! is satisfiable by any disagreeing `f` and a wrong `sat` follows.
//!
//! Every test here observes the rewrite DIRECTLY — by asking the arena whether
//! the internal injection was declared — rather than inferring it from a
//! verdict. A test that only asserted "the script parsed" could not fail on the
//! polarity bug it exists to catch, because the buggy parse succeeds.
//!
//! The verdict half of the obligation is
//! `axeyum-solver/tests/distinct_linear_soundness.rs`.

use axeyum_smtlib::parse_script_with_distinct_lever;

/// The name the encoding probes for first. Present in the arena's INTERNAL
/// function namespace exactly when the rewrite fired at least once.
const FIRST_INJECTION: &str = "!distinct.inj.0";

fn fired(src: &str, lever: Option<&str>) -> bool {
    let script = parse_script_with_distinct_lever(src, lever)
        .unwrap_or_else(|e| panic!("parse failed for lever {lever:?}: {e:?}"));
    script
        .arena
        .find_internal_function(FIRST_INJECTION)
        .is_some()
}

fn preamble(sort: &str, names: &[&str]) -> String {
    let mut s = String::from("(set-logic UFNIA)\n(declare-sort U 0)\n");
    for n in names {
        s.push_str(&format!("(declare-fun {n} () {sort})\n"));
    }
    s
}

fn distinct_of(names: &[&str]) -> String {
    format!("(distinct {})", names.join(" "))
}

// ---------------------------------------------------------------------------
// The lever itself
// ---------------------------------------------------------------------------

#[test]
fn the_shipped_default_never_rewrites() {
    let names = ["a", "b", "c"];
    let src = format!(
        "{}(assert {})\n(check-sat)\n",
        preamble("U", &names),
        distinct_of(&names)
    );
    assert!(
        !fired(&src, None),
        "with the lever unset the parser must be byte-identical to the pairwise path"
    );
}

#[test]
fn an_unrecognised_lever_value_is_off_not_on() {
    let names = ["a", "b", "c"];
    let src = format!(
        "{}(assert {})\n(check-sat)\n",
        preamble("U", &names),
        distinct_of(&names)
    );
    for bad in [
        "",
        "yes",
        "1",
        "on:",
        "on:notanumber",
        "on:1",
        "mutant",
        "mutant:oops",
    ] {
        assert!(
            !fired(&src, Some(bad)),
            "lever value {bad:?} must be OFF -- a typo must not silently enable a rewrite"
        );
    }
}

#[test]
fn the_lever_fires_at_its_stated_arity_and_not_below() {
    let names = ["a", "b", "c", "d"];
    let base = preamble("U", &names);
    let three = format!("{base}(assert {})\n(check-sat)\n", distinct_of(&names[..3]));
    let four = format!("{base}(assert {})\n(check-sat)\n", distinct_of(&names));
    assert!(
        fired(&four, Some("on:4")),
        "arity 4 must fire at min-arity 4"
    );
    assert!(
        !fired(&three, Some("on:4")),
        "arity 3 must NOT fire at min-arity 4 -- the threshold is a real threshold"
    );
}

#[test]
fn the_default_threshold_is_the_pairwise_cap_not_a_small_number() {
    // `MAX_DISTINCT_EXPANSION_PAIRS` is 65_536, so the smallest arity whose
    // pairwise expansion exceeds it is 363. A bare `on` must not fire below it,
    // or enabling the lever would change the encoding of ordinary benchmarks
    // rather than only the ones the front door refuses today.
    let names: Vec<String> = (0..362).map(|i| format!("a{i}")).collect();
    let refs: Vec<&str> = names.iter().map(String::as_str).collect();
    let src = format!(
        "{}(assert {})\n(check-sat)\n",
        preamble("U", &refs),
        distinct_of(&refs)
    );
    assert!(
        !fired(&src, Some("on")),
        "arity 362 is INSIDE the pairwise cap and a bare `on` must leave it alone"
    );

    let names: Vec<String> = (0..363).map(|i| format!("a{i}")).collect();
    let refs: Vec<&str> = names.iter().map(String::as_str).collect();
    let src = format!(
        "{}(assert {})\n(check-sat)\n",
        preamble("U", &refs),
        distinct_of(&refs)
    );
    assert!(
        fired(&src, Some("on")),
        "arity 363 is the first arity OVER the pairwise cap and a bare `on` must take it"
    );
}

// ---------------------------------------------------------------------------
// Polarity — the soundness scope
// ---------------------------------------------------------------------------

#[test]
fn a_negated_distinct_is_never_rewritten() {
    let names = ["a", "b", "c"];
    let src = format!(
        "{}(assert (not {}))\n(check-sat)\n",
        preamble("U", &names),
        distinct_of(&names)
    );
    assert!(
        !fired(&src, Some("on:3")),
        "`(not (distinct …))` is NEGATIVE polarity; rewriting it is a wrong `sat`"
    );
}

#[test]
fn a_distinct_under_any_connective_is_never_rewritten() {
    let names = ["a", "b", "c"];
    let base = preamble("U", &names);
    let d = distinct_of(&names);
    for body in [
        format!("(or {d} false)"),
        format!("(and {d} true)"),
        format!("(=> true {d})"),
        format!("(ite true {d} false)"),
        format!("(= {d} true)"),
        format!("(not (not {d}))"),
    ] {
        let src = format!("{base}(assert {body})\n(check-sat)\n");
        assert!(
            !fired(&src, Some("on:3")),
            "only the WHOLE body of an `assert` is positive by construction; {body} is not"
        );
    }
}

#[test]
fn the_positive_site_still_fires_under_push_and_pop() {
    // `push`/`pop` scope assertions; they never negate one, so the body of an
    // `assert` inside a scope is still positive.
    let names = ["a", "b", "c"];
    let src = format!(
        "{}(push 1)\n(assert {})\n(check-sat)\n(pop 1)\n(check-sat)\n",
        preamble("U", &names),
        distinct_of(&names)
    );
    assert!(
        fired(&src, Some("on:3")),
        "a scoped assertion body is positive and must still be rewritten"
    );
}

// ---------------------------------------------------------------------------
// Sort scope
// ---------------------------------------------------------------------------

#[test]
fn only_uninterpreted_sorts_are_rewritten() {
    // Each of these is a 3-way `distinct` whose arguments do NOT have an
    // uninterpreted sort. All must decline to the pairwise path.
    let cases = [
        (
            "(declare-fun a () Int)(declare-fun b () Int)(declare-fun c () Int)",
            "QF_LIA",
        ),
        (
            "(declare-fun a () (_ BitVec 8))(declare-fun b () (_ BitVec 8))(declare-fun c () (_ BitVec 8))",
            "QF_BV",
        ),
        (
            "(declare-fun a () Bool)(declare-fun b () Bool)(declare-fun c () Bool)",
            "QF_UF",
        ),
        (
            "(declare-fun a () Real)(declare-fun b () Real)(declare-fun c () Real)",
            "QF_LRA",
        ),
        (
            "(declare-fun a () (Array Int Int))(declare-fun b () (Array Int Int))(declare-fun c () (Array Int Int))",
            "QF_ALIA",
        ),
    ];
    for (decls, logic) in cases {
        let src = format!("(set-logic {logic})\n{decls}\n(assert (distinct a b c))\n(check-sat)\n");
        assert!(
            !fired(&src, Some("on:3")),
            "{logic}: a non-uninterpreted sort must take the unchanged pairwise path"
        );
    }
}

#[test]
fn a_mixed_sort_application_is_not_rewritten() {
    // `(distinct x 3)` with `x : Real` coerces the numeral; the coercion lives
    // in the pairwise path, so a mixed application must decline.
    let src = "(set-logic QF_UFLRA)\n(declare-fun x () Real)\n(declare-fun y () Real)\n\
               (declare-fun z () Real)\n(assert (distinct x y z 3))\n(check-sat)\n";
    assert!(!fired(src, Some("on:3")));
}

// ---------------------------------------------------------------------------
// Freshness
// ---------------------------------------------------------------------------

#[test]
fn two_applications_get_two_injections() {
    // Sharing one injection across two applications forces one indexing to
    // satisfy both, which is a SPURIOUS UNSAT. Observe both names directly.
    let names = ["a", "b", "c", "d", "e", "f"];
    let src = format!(
        "{}(assert {})\n(assert {})\n(check-sat)\n",
        preamble("U", &names),
        distinct_of(&names[..3]),
        distinct_of(&names[3..])
    );
    let script = parse_script_with_distinct_lever(&src, Some("on:3")).expect("parse");
    assert!(
        script
            .arena
            .find_internal_function("!distinct.inj.0")
            .is_some()
    );
    assert!(
        script
            .arena
            .find_internal_function("!distinct.inj.1")
            .is_some(),
        "a second `distinct` must get a SECOND injection, never the first one again"
    );
}

#[test]
fn the_shared_mutant_really_does_share_one_injection() {
    // The negative control for the test above: if `!distinct.inj.1` could not be
    // absent, the assertion above would be measuring nothing.
    let names = ["a", "b", "c", "d", "e", "f"];
    let src = format!(
        "{}(assert {})\n(assert {})\n(check-sat)\n",
        preamble("U", &names),
        distinct_of(&names[..3]),
        distinct_of(&names[3..])
    );
    let script = parse_script_with_distinct_lever(&src, Some("mutant:shared:3")).expect("parse");
    assert!(
        script
            .arena
            .find_internal_function("!distinct.inj.shared")
            .is_some()
    );
    assert!(
        script
            .arena
            .find_internal_function("!distinct.inj.1")
            .is_none(),
        "the shared mutant must declare ONE injection -- otherwise it is not a mutant"
    );
}

#[test]
fn a_user_symbol_spelled_like_the_injection_does_not_collide() {
    // A benchmark is free to declare `|!distinct.inj.0|`. The internal namespace
    // is disjoint, so the rewrite must still declare its own.
    let names = ["a", "b", "c"];
    let src = format!(
        "{}(declare-fun |!distinct.inj.0| (U) Int)\n(assert (= (|!distinct.inj.0| a) 7))\n\
         (assert {})\n(check-sat)\n",
        preamble("U", &names),
        distinct_of(&names)
    );
    let script = parse_script_with_distinct_lever(&src, Some("on:3")).expect("parse");
    let user = script
        .arena
        .find_function("!distinct.inj.0")
        .expect("user declaration");
    let internal = script
        .arena
        .find_internal_function("!distinct.inj.0")
        .expect("internal injection");
    assert_ne!(
        user, internal,
        "the user's symbol and the injection must be DIFFERENT functions -- \
         conflating them would let `(= (f a) 7)` contradict `(= (f a) 0)` and \
         produce a spurious `unsat`"
    );
}

// ---------------------------------------------------------------------------
// Degenerate input
// ---------------------------------------------------------------------------

#[test]
fn a_repeated_argument_is_false_in_both_encodings() {
    let src = "(set-logic UFNIA)\n(declare-sort U 0)\n(declare-fun a () U)\n\
               (declare-fun b () U)\n(assert (distinct a b a))\n(check-sat)\n";
    let pairwise = parse_script_with_distinct_lever(src, None).expect("parse");
    let linear = parse_script_with_distinct_lever(src, Some("on:3")).expect("parse");
    assert_eq!(
        pairwise.assertions.len(),
        linear.assertions.len(),
        "both paths must record one assertion"
    );
    // Both must fold to the same interned `false`; the arenas are separate, so
    // compare the rendered node instead of the id.
    assert_eq!(
        format!("{:?}", pairwise.arena.node(pairwise.assertions[0])),
        format!("{:?}", linear.arena.node(linear.assertions[0])),
        "a repeated argument is `false` in both encodings, not merely equisatisfiable"
    );
}
