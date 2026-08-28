//! ADR-0605 §3 guard: **no shipped (non-test) call site constructs the
//! `AxReal` ring signature.**
//!
//! `LraReconstructCtx::new_over_axreal`/`::try_new_over_axreal` build the
//! legacy axiomatized `Real` package — this repository's entire remaining
//! trusted surface, 30 axioms. The rename in [`super`] makes the choice
//! explicit at every call site; this module is the complementary guard the
//! ADR asks for, because a rename alone does not stop a *future* call site
//! from picking the axiom-bearing constructor again, deliberately or not.
//!
//! The check reads this crate's own `src/reconstruct/` tree from disk (the
//! same `CARGO_MANIFEST_DIR`-relative pattern used by
//! [`crate::reconstruct::tests`]) rather than trusting a hand-maintained list
//! of "known-good" files — the [`CLAUDE.md`] gotcha about inventories that
//! iterate their own list applies here just as much as to a theorem count.
//!
//! # Why this is a *discriminating* check, not a checker that cannot fail
//!
//! [`scan_for_axreal_constructor_calls`] is exercised by three tests, not one:
//!
//! - [`the_guard_flags_a_planted_call_outside_any_test_module`] plants a call
//!   in a synthetic, non-test-shaped fixture and asserts it IS reported — the
//!   positive control proving the scanner can fire at all;
//! - [`the_guard_ignores_a_call_inside_a_cfg_test_module`] plants the same
//!   call inside a `#[cfg(test)] mod { ... }` body and asserts it is NOT
//!   reported — proving the scanner does not simply flag every occurrence of
//!   the name, which would make every one of this crate's own tests a false
//!   positive;
//! - [`no_shipped_reconstruct_source_constructs_the_axreal_signature`] is the
//!   real gate: it walks the actual `src/reconstruct/` tree and asserts empty.
//!
//! A guard with only the third test would be indistinguishable from one that
//! never scans anything (an empty result and a broken scanner both print
//! nothing); the first two are what prove a nonempty result is reachable and
//! that legitimate test usage does not trip it.

use std::path::{Path, PathBuf};

/// One reported call: the file (relative to `src/reconstruct/`) and the
/// 1-based line number.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct FlaggedCall {
    pub(crate) file: PathBuf,
    pub(crate) line: usize,
    pub(crate) text: String,
}

/// The two identifiers this guard exists to keep out of shipped code.
///
/// A plain substring search is enough here — these are not Rust keywords, an
/// identifier that merely CONTAINS one of these as a strict substring with
/// adjacent word characters (e.g. a hypothetical
/// `new_over_axreal_and_something_else`) does not exist in this crate today,
/// and the real gate test below re-derives its truth from the actual source
/// tree rather than from this list being exhaustive in the abstract.
const FLAGGED_CALLS: [&str; 2] = [
    "LraReconstructCtx::new_over_axreal",
    "LraReconstructCtx::try_new_over_axreal",
];

/// Scan `source` for occurrences of [`FLAGGED_CALLS`] that lie OUTSIDE any
/// top-level `#[cfg(test)]` item (a `mod { ... }` block, or a single
/// `#[cfg(test)]`-attributed item on the following brace-delimited item).
///
/// This is a brace-counting scanner, not a full Rust parser: it tracks `{`/`}`
/// depth and a pending "we are inside a `#[cfg(test)]` span" flag armed by
/// seeing the attribute on its own logical line. That is sufficient for this
/// codebase's actual shape — every AxReal-constructing call site in
/// `src/reconstruct/` today is either inside `#[cfg(test)] mod tests { ... }`
/// or in a file gated by `#[cfg(test)] mod <name>;` from its parent (which
/// never reaches this scanner at all, since the scanner only reads files
/// reachable from `src/reconstruct/`'s own module tree — see
/// [`is_excluded_from_this_scan`]) — and the two control tests above pin the
/// scanner's behaviour on exactly the shapes that matter, so a change to this
/// heuristic that broke coverage would show up as one of them failing.
pub(crate) fn scan_for_axreal_constructor_calls(source: &str, file: &Path) -> Vec<FlaggedCall> {
    let mut flagged = Vec::new();
    let mut depth: i64 = 0;
    // Depth at which the current `#[cfg(test)]` span started, if any. `None`
    // means we are not inside one.
    let mut test_span_from: Option<i64> = None;
    let mut pending_cfg_test = false;

    for (idx, raw_line) in source.lines().enumerate() {
        let line = raw_line;
        let trimmed = line.trim();

        // Strip a `//` line comment for the purposes of brace counting and
        // the flagged-identifier search, so a call mentioned only in prose
        // (as this very file's doc comments do) is never mistaken for code.
        let code_part = strip_line_comment(line);

        if trimmed.starts_with("#[cfg(test)]") || trimmed == "#[cfg(test)]" {
            pending_cfg_test = true;
        }

        // `try_from` rather than `as`: a source line cannot hold `i64::MAX`
        // braces, but a silent wrap would make the depth counter run backwards
        // and mis-attribute a whole span, so saturate visibly instead.
        let opens = i64::try_from(code_part.matches('{').count()).unwrap_or(i64::MAX);
        let closes = i64::try_from(code_part.matches('}').count()).unwrap_or(i64::MAX);

        if pending_cfg_test && opens > 0 {
            // The `{` that opens the cfg(test)-attributed item. Record the
            // depth BEFORE this line's opens as the span's floor: once depth
            // returns to that floor, the span is over.
            test_span_from = Some(depth);
            pending_cfg_test = false;
        }

        if test_span_from.is_none() {
            for flag in FLAGGED_CALLS {
                if let Some(col) = code_part.find(flag) {
                    // Reject a match that is itself part of a longer
                    // identifier (defence in depth; see FLAGGED_CALLS' doc).
                    let before_ok = col == 0
                        || !code_part.as_bytes()[col - 1].is_ascii_alphanumeric()
                            && code_part.as_bytes()[col - 1] != b'_';
                    let after = col + flag.len();
                    let after_ok = after >= code_part.len()
                        || !(code_part.as_bytes()[after].is_ascii_alphanumeric()
                            || code_part.as_bytes()[after] == b'_');
                    if before_ok && after_ok {
                        flagged.push(FlaggedCall {
                            file: file.to_path_buf(),
                            line: idx + 1,
                            text: trimmed.to_owned(),
                        });
                    }
                }
            }
        }

        depth += opens - closes;

        if let Some(from) = test_span_from
            && depth <= from
        {
            test_span_from = None;
        }
    }

    flagged
}

/// Strip a `//` line comment, respecting `"..."` and `'.'` literals well
/// enough for this crate's own source (no raw strings or byte-string
/// escaping tricks appear on any line this scanner needs to classify
/// correctly, and the doc-comment lines this file itself contains are
/// exactly the case this exists to handle).
fn strip_line_comment(line: &str) -> &str {
    let bytes = line.as_bytes();
    let mut in_str = false;
    let mut i = 0;
    while i < bytes.len() {
        match bytes[i] {
            b'"' => in_str = !in_str,
            b'/' if !in_str && i + 1 < bytes.len() && bytes[i + 1] == b'/' => {
                return &line[..i];
            }
            b'\\' if in_str => i += 1,
            _ => {}
        }
        i += 1;
    }
    line
}

/// Whether `path` is out of scope for this scan.
///
/// Two disjoint reasons a file is excluded, and both are load-bearing:
///
/// - it is a file this crate declares ONLY under `#[cfg(test)]` (e.g.
///   `mod signature_tests;` guarded by `#[cfg(test)]` in `signature.rs`) —
///   never compiled into a shipped binary, so out of scope by construction,
///   the same way `#[cfg(feature = "full")]`-gated suites are out of scope
///   for a default-feature build; or
/// - it is THIS module. [`FLAGGED_CALLS`] holds the two identifiers as
///   string literals in ordinary (non-test) code, which is real code that
///   legitimately contains the flagged text as DATA rather than as a call —
///   scanning this file for its own needle would be a permanent false
///   positive, not a finding. Excluding it by name rather than by, say,
///   special-casing string-literal contents keeps the scanner itself simple;
///   the alternative (a scanner that understands Rust string literals) is
///   more code to keep discriminating for no gain, since this is the only
///   file in the tree that has a legitimate reason to hold the identifiers as
///   data.
fn is_excluded_from_this_scan(path: &Path) -> bool {
    let name = path.file_stem().and_then(|s| s.to_str()).unwrap_or("");
    name == "tests" || name.ends_with("_tests") || name == "axreal_call_site_guard"
}

/// Recursively collect every `.rs` file under `dir`.
fn collect_rs_files(dir: &Path, out: &mut Vec<PathBuf>) {
    let Ok(entries) = std::fs::read_dir(dir) else {
        return;
    };
    let mut entries: Vec<_> = entries.filter_map(Result::ok).collect();
    // Deterministic order (CLAUDE.md: no hash-map/dir-iteration order in
    // anything this test's failure message reports).
    entries.sort_by_key(std::fs::DirEntry::path);
    for entry in entries {
        let path = entry.path();
        if path.is_dir() {
            collect_rs_files(&path, out);
        } else if path.extension().and_then(|e| e.to_str()) == Some("rs") {
            out.push(path);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// **Positive control**: a call outside any test module IS flagged.
    ///
    /// This is the proof the checker can fail. Without it, the real gate test
    /// below passing would be indistinguishable from a scanner that never
    /// matches anything.
    #[test]
    fn the_guard_flags_a_planted_call_outside_any_test_module() {
        let fixture = "\
pub fn shipped_helper() {
    let mut ctx = LraReconstructCtx::new_over_axreal();
    let _ = ctx;
}
";
        let flagged = scan_for_axreal_constructor_calls(fixture, Path::new("fixture.rs"));
        assert_eq!(
            flagged.len(),
            1,
            "a shipped call to the AxReal constructor must be flagged, got {flagged:?}"
        );
        assert_eq!(flagged[0].line, 2);
    }

    /// **Negative control**: the SAME call, moved inside a `#[cfg(test)] mod`,
    /// is NOT flagged — proving the scanner distinguishes shipped code from
    /// test code rather than just matching the identifier everywhere, which
    /// would make every real test in this crate a false positive.
    #[test]
    fn the_guard_ignores_a_call_inside_a_cfg_test_module() {
        let fixture = "\
pub fn shipped_helper() {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn some_test() {
        let mut ctx = LraReconstructCtx::new_over_axreal();
        let _ = ctx;
    }
}
";
        let flagged = scan_for_axreal_constructor_calls(fixture, Path::new("fixture.rs"));
        assert!(
            flagged.is_empty(),
            "a call inside #[cfg(test)] must not be flagged, got {flagged:?}"
        );
    }

    /// A call that is merely MENTIONED in a doc comment or line comment (as
    /// this very source file does, repeatedly) must not be flagged either —
    /// otherwise this guard's own module would fail its own check.
    #[test]
    fn the_guard_ignores_a_mention_in_a_comment() {
        let fixture = "\
/// See `LraReconstructCtx::new_over_axreal` for the AxReal route.
pub fn shipped_helper() {
    // LraReconstructCtx::new_over_axreal() is what we must NOT call here.
}
";
        let flagged = scan_for_axreal_constructor_calls(fixture, Path::new("fixture.rs"));
        assert!(
            flagged.is_empty(),
            "a comment-only mention must not be flagged, got {flagged:?}"
        );
    }

    /// **The real gate.** No shipped file under `src/reconstruct/` — this
    /// crate's actual, on-disk source tree, not a hand-maintained list of
    /// files believed to be clean — constructs the `AxReal` signature outside a
    /// `#[cfg(test)]` span.
    ///
    /// This is a *discriminating* assertion: reintroducing
    /// `let ctx = LraReconstructCtx::new_over_axreal();` at top level in, say,
    /// `arithmetic.rs`'s non-test code turns this test red (verified by hand
    /// while landing this guard: planting such a line and re-running failed
    /// exactly this test and no other, then the line was reverted).
    #[test]
    fn no_shipped_reconstruct_source_constructs_the_axreal_signature() {
        let root = Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("src")
            .join("reconstruct");
        let mut files = Vec::new();
        collect_rs_files(&root, &mut files);
        assert!(
            files.len() > 10,
            "expected to find this crate's reconstruct/ source tree under {}, found {} files \
             -- the scan is pointed at the wrong place",
            root.display(),
            files.len()
        );

        let mut all_flagged = Vec::new();
        for file in &files {
            if is_excluded_from_this_scan(file) {
                continue;
            }
            let Ok(source) = std::fs::read_to_string(file) else {
                continue;
            };
            let rel = file.strip_prefix(&root).unwrap_or(file);
            all_flagged.extend(scan_for_axreal_constructor_calls(&source, rel));
        }

        assert!(
            all_flagged.is_empty(),
            "shipped (non-test) reconstruct/ source constructs the AxReal ring signature -- \
             ADR-0605 says the obvious constructor must not be reachable by accident:\n{}",
            all_flagged
                .iter()
                .map(|f| format!("  {}:{}: {}", f.file.display(), f.line, f.text))
                .collect::<Vec<_>>()
                .join("\n")
        );
    }
}
