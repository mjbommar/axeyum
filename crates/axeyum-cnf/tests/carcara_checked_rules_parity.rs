//! Derives Carcara's checkable-rule vocabulary from the vendored clone's
//! `get_rule` match arms and compares it against our pinned
//! [`axeyum_cnf::CARCARA_CHECKED_RULES`] list.
//!
//! This exists because a hand-maintained list is checkable only against a
//! maintainer's memory of Carcara's source — see
//! `docs/contributor-guide/evidence-and-checker-discipline.md`: "a test named
//! 'every X' must derive its X from the authority, not a literal." The
//! authority here is `references/carcara/carcara/src/checker/shared.rs`'s
//! `pub fn get_rule`, not the pinned constant's own doc comment.
//!
//! `references/` is gitignored and commonly absent (CI, a fresh clone,
//! most hosts). This test SKIPS cleanly in that case — and prints which
//! case it took, so a skip is never silently mistaken for a pass:
//!
//! ```text
//! [skip] references/carcara not present at ...; ...
//! [run] parsing Carcara's get_rule arms from ...
//! ```
//!
//! Build/clone the reference with `scripts/fetch-references.sh` (or
//! `git clone https://github.com/ufmg-smite/carcara references/carcara`) to
//! exercise the real comparison locally.

use std::collections::BTreeSet;
use std::path::PathBuf;

use axeyum_cnf::CARCARA_CHECKED_RULES;

/// Rule names Carcara's `get_rule` matches but does not actually check: it
/// sets the `is_holey` flag instead of running a checker (`hole`,
/// `lia_generic`), or defers to cvc5's external RARE rewrite database, which
/// we do not vendor (`rare_rewrite`). This mirrors the exclusion documented
/// on `CARCARA_CHECKED_RULES` in `crates/axeyum-cnf/src/alethe.rs`, and is
/// covered independently there by a test asserting all three are rejected by
/// `is_carcara_checked_rule`. If Carcara's `get_rule` ever drops one of these
/// three arms entirely, subtracting an absent name is a no-op and this test
/// still holds.
const DELIBERATELY_EXCLUDED: &[&str] = &["hole", "lia_generic", "rare_rewrite"];

/// Path to the vendored Carcara clone's `checker/shared.rs`, relative to this
/// crate's manifest directory (`crates/axeyum-cnf` -> workspace root ->
/// `references/carcara/...`). Returns `None` when the (gitignored) clone is
/// absent.
fn carcara_shared_rs_path() -> Option<PathBuf> {
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../references/carcara/carcara/src/checker/shared.rs");
    path.is_file().then_some(path)
}

/// Parses the body of `pub fn get_rule` in Carcara's `shared.rs`, returning
/// the set of distinct string-literal rule-name patterns matched by its arms
/// (the union over every `"a" | "b" [if cond] => ...` arm; the `_ => None`
/// catch-all contributes no string literal and is naturally excluded).
///
/// This is a line-oriented parse, not a full Rust parser — it is sufficient
/// because every arm in `get_rule` is single-line as of clone `6624ea80c`.
/// Method: for each non-comment line inside the function's brace-delimited
/// body that contains both `"` and `=>`, take the text before the first
/// `=>` and collect every double-quoted substring in it. Multiple arms
/// naming the same rule under different guards (e.g. `"resolution" |
/// "th_resolution" if elaborated => ...` and the unguarded arm further
/// down) collapse to one set member, which is correct: the rule name is
/// checkable if *any* arm reaches a real checker.
fn parse_get_rule_arms(source: &str) -> BTreeSet<String> {
    let fn_start = source
        .find("pub fn get_rule")
        .expect("get_rule function not found in shared.rs — Carcara's source layout changed");
    let after = &source[fn_start..];
    let open = after
        .find('{')
        .expect("get_rule has no body (no opening brace found)");

    // Walk brace depth from the opening '{' to find the matching '}', so
    // reformatting/reindentation of the file doesn't break the parse.
    let bytes = after.as_bytes();
    let mut depth = 0i32;
    let mut close = None;
    for (i, &b) in bytes.iter().enumerate().skip(open) {
        match b {
            b'{' => depth += 1,
            b'}' => {
                depth -= 1;
                if depth == 0 {
                    close = Some(i);
                    break;
                }
            }
            _ => {}
        }
    }
    let close = close.expect("get_rule's opening brace has no matching close");
    let body = &after[open..=close];

    let mut names = BTreeSet::new();
    for line in body.lines() {
        let stripped = line.trim();
        if stripped.starts_with("//") || !stripped.contains('"') || !stripped.contains("=>") {
            continue;
        }
        let lhs = stripped.split("=>").next().unwrap();
        let mut in_string = false;
        let mut current = String::new();
        for c in lhs.chars() {
            if c == '"' {
                if in_string {
                    names.insert(std::mem::take(&mut current));
                }
                in_string = !in_string;
            } else if in_string {
                current.push(c);
            }
        }
    }
    names
}

#[test]
fn carcara_checked_rules_matches_get_rule_arms() {
    let expected_path = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../references/carcara");
    let Some(path) = carcara_shared_rs_path() else {
        eprintln!(
            "[skip] references/carcara not present at {}; this parity check did not run. \
             Build it with scripts/fetch-references.sh (or clone \
             https://github.com/ufmg-smite/carcara into references/carcara) to exercise it.",
            expected_path.display()
        );
        return;
    };
    eprintln!(
        "[run] parsing Carcara's get_rule arms from {}",
        path.display()
    );

    let source =
        std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("read {}: {e}", path.display()));
    let parsed = parse_get_rule_arms(&source);

    // Sanity floor: if the parser regresses to matching almost nothing (a
    // source-layout change it can't handle), fail loudly instead of quietly
    // reporting a huge spurious diff.
    assert!(
        parsed.len() > 100,
        "parsed only {} rule names from {} — the line-oriented parser likely broke on a \
         Carcara source-layout change; investigate get_rule's current shape before trusting \
         this test",
        parsed.len(),
        path.display()
    );

    let expected: BTreeSet<&str> = parsed
        .iter()
        .map(String::as_str)
        .filter(|n| !DELIBERATELY_EXCLUDED.contains(n))
        .collect();
    let ours: BTreeSet<&str> = CARCARA_CHECKED_RULES.iter().copied().collect();

    eprintln!(
        "[info] get_rule: {} distinct match-arm strings; deliberately excluded: {:?}; \
         expected checked set: {}; CARCARA_CHECKED_RULES: {}",
        parsed.len(),
        DELIBERATELY_EXCLUDED,
        expected.len(),
        ours.len(),
    );

    let missing: Vec<&str> = expected.difference(&ours).copied().collect();
    let extra: Vec<&str> = ours.difference(&expected).copied().collect();

    assert!(
        missing.is_empty() && extra.is_empty(),
        "CARCARA_CHECKED_RULES (crates/axeyum-cnf/src/alethe.rs) has drifted from Carcara's \
         get_rule vocabulary at {} (minus the documented {:?} exclusion).\n\
         missing from our pinned list (Carcara checks these; we do not claim them): {:?}\n\
         extra in our pinned list (we claim these; Carcara's get_rule does not match them): {:?}",
        path.display(),
        DELIBERATELY_EXCLUDED,
        missing,
        extra,
    );
}

#[test]
fn deliberately_excluded_rules_are_actually_present_in_get_rule() {
    // Guards the exclusion list itself: if one of these three strings stops
    // appearing in get_rule at all, subtracting it from `parsed` in the main
    // test silently becomes a no-op and the exclusion stops doing anything.
    // This does not need the clone to make a true-or-false claim about our
    // own pinned list, but it DOES need the clone to check itself against
    // Carcara, so it skips the same way.
    let Some(path) = carcara_shared_rs_path() else {
        eprintln!(
            "[skip] references/carcara not present; did not verify the DELIBERATELY_EXCLUDED \
             names are still present in get_rule."
        );
        return;
    };
    eprintln!(
        "[run] checking DELIBERATELY_EXCLUDED against {}",
        path.display()
    );
    let source =
        std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("read {}: {e}", path.display()));
    let parsed = parse_get_rule_arms(&source);
    for name in DELIBERATELY_EXCLUDED {
        assert!(
            parsed.contains(*name),
            "{name:?} is in DELIBERATELY_EXCLUDED but no longer appears as a get_rule match \
             arm at {} — the exclusion is now a no-op and CARCARA_CHECKED_RULES's doc comment \
             is stale; re-check whether it should be added to the pinned list instead",
            path.display()
        );
    }
}
