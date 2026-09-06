//! The retrieval index must see the whole kernel.
//!
//! `examples/shape_search.rs` is the tool a lane runs to answer *"does a
//! declaration of this shape already exist?"*, and an ABSENT verdict from it is
//! what a lane acts on. A prelude group the example never builds therefore
//! produces a confident, wrong "no such declaration" — the measured root cause
//! of repeated lane-hours spent re-deriving lemmas that were already in the
//! tree.
//!
//! Measured 2026-09-06, before this test existed: the crate defined **31**
//! `pub fn build_*_prelude` functions and `shape_search` reached **17** of them
//! (15 called directly, 2 more transitively). It was blind to 14: every `fo_*`
//! module (11 builders, `--ns FO` returned nothing against a 4,839-row dump),
//! `metric_prod` (`Metric.prod*`), the list prelude (`List.Perm` and kin) and
//! `ipc_eval`.
//!
//! The example carries its own internal cross-check (declared `coverage:`
//! groups vs. indexed groups) and it passed throughout, because BOTH halves
//! omitted the same builders. A check whose two sides are written by the same
//! hand at the same moment cannot fail. This test is the outside check: its
//! subject is derived from the crate's own source, so it cannot be kept green
//! by editing the example alone.
//!
//! # What is derived, and from where
//!
//! * **The authority** — every `pub fn build_*_prelude` defined under `src/`,
//!   read from the source text. Never a literal list.
//! * **The call graph** — for each builder, the other builders named inside
//!   that builder's own function body. Body only, so a builder a *test* module
//!   happens to call never counts as coverage.
//! * **The example's reach** — every `build_*_prelude(` call site in
//!   `examples/shape_search.rs`, with `//` comment lines stripped so that a
//!   builder merely *discussed* in prose is not mistaken for one that is built.
//!
//! A builder is covered when it is reachable from a direct call site through
//! that call graph. Anything else must appear in `DELIBERATELY_UNINDEXED` with
//! a measured reason, or this test fails and prints both sides.

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};

/// Builders the index deliberately does not reach.
///
/// Each entry is `(builder, measured reason)`. A reason must be a
/// **measurement**, not an intention: what it costs, or what makes it
/// unreachable. A short reason is not accepted (see `reasons_are_measured`).
const DELIBERATELY_UNINDEXED: &[(&str, &str)] = &[];

fn manifest_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
}

/// Every `.rs` file under `src/`, excluding the out-of-line test modules
/// (`*_tests.rs`, declared `#[cfg(test)] mod …_tests;`).
fn source_files(dir: &Path, out: &mut Vec<PathBuf>) {
    let entries = std::fs::read_dir(dir).unwrap_or_else(|e| panic!("read_dir {dir:?}: {e}"));
    for entry in entries {
        let path = entry.expect("dir entry").path();
        if path.is_dir() {
            source_files(&path, out);
        } else if path.extension().is_some_and(|ext| ext == "rs") {
            let name = path
                .file_name()
                .and_then(|n| n.to_str())
                .unwrap_or_default()
                .to_owned();
            if !name.ends_with("_tests.rs") {
                out.push(path);
            }
        }
    }
}

/// Strip whole-line `//`, `///` and `//!` comments.
///
/// Prose in this crate quotes builder names constantly (`build_ipc_eval_prelude`
/// appears in three doc comments), and counting a name that is only *discussed*
/// as a name that is *built* is precisely the false all-clear this test exists
/// to prevent.
fn strip_line_comments(text: &str) -> String {
    text.lines()
        .filter(|line| !line.trim_start().starts_with("//"))
        .collect::<Vec<_>>()
        .join("\n")
}

/// The builder names appearing as CALL SITES (`name(`) in `text`.
fn builders_called(text: &str, authority: &BTreeSet<String>) -> BTreeSet<String> {
    let stripped = strip_line_comments(text);
    authority
        .iter()
        .filter(|name| stripped.contains(&format!("{name}(")))
        .cloned()
        .collect()
}

/// `pub fn build_<x>_prelude` definitions, mapped to the file that owns them.
///
/// This is the authority. It is read from the source text on every run, so a
/// builder added tomorrow is in the denominator tomorrow.
fn builder_definitions() -> BTreeMap<String, PathBuf> {
    let mut files = Vec::new();
    source_files(&manifest_dir().join("src"), &mut files);
    files.sort();
    let mut defs = BTreeMap::new();
    for file in files {
        let text = std::fs::read_to_string(&file).expect("source file is readable");
        for line in text.lines() {
            let Some(rest) = line.strip_prefix("pub fn build_") else {
                continue;
            };
            let Some(name) = rest.split(['(', '<']).next() else {
                continue;
            };
            if name.ends_with("_prelude") {
                defs.insert(format!("build_{name}"), file.clone());
            }
        }
    }
    defs
}

/// The text of one builder's own function body.
///
/// Top-level items in this crate are rustfmt-formatted, so an item that starts
/// at column 0 ends at the next line that is exactly `}`. Restricting the scan
/// to the body is the conservative direction: a builder call that lives in a
/// helper would be MISSED, making this test complain about a builder that is in
/// fact reached — a false alarm, never a false all-clear.
fn builder_body(file: &Path, builder: &str) -> String {
    let text = std::fs::read_to_string(file).expect("source file is readable");
    let head = format!("pub fn {builder}");
    let mut body = String::new();
    let mut inside = false;
    for line in text.lines() {
        if !inside {
            if line.starts_with(&head) {
                inside = true;
            }
            continue;
        }
        if line == "}" {
            break;
        }
        body.push_str(line);
        body.push('\n');
    }
    assert!(
        inside,
        "builder {builder} was found by the definition scan but its body could \
         not be located in {file:?}; the definition scan and the body scan \
         disagree, which makes every coverage verdict below meaningless"
    );
    body
}

/// `builder -> the builders its own body calls`.
fn call_graph(defs: &BTreeMap<String, PathBuf>) -> BTreeMap<String, BTreeSet<String>> {
    let authority: BTreeSet<String> = defs.keys().cloned().collect();
    defs.iter()
        .map(|(builder, file)| {
            let mut called = builders_called(&builder_body(file, builder), &authority);
            called.remove(builder);
            (builder.clone(), called)
        })
        .collect()
}

/// The builders `examples/shape_search.rs` calls directly.
fn shape_search_direct(authority: &BTreeSet<String>) -> BTreeSet<String> {
    let path = manifest_dir().join("examples/shape_search.rs");
    let text = std::fs::read_to_string(&path).expect("shape_search.rs is readable");
    builders_called(&text, authority)
}

/// Everything reachable from `direct` through the call graph.
fn reachable(
    direct: &BTreeSet<String>,
    graph: &BTreeMap<String, BTreeSet<String>>,
) -> BTreeSet<String> {
    let mut seen: BTreeSet<String> = BTreeSet::new();
    let mut stack: Vec<String> = direct.iter().cloned().collect();
    while let Some(builder) = stack.pop() {
        if !seen.insert(builder.clone()) {
            continue;
        }
        if let Some(next) = graph.get(&builder) {
            stack.extend(next.iter().cloned());
        }
    }
    seen
}

fn join(names: impl IntoIterator<Item = impl AsRef<str>>) -> String {
    names
        .into_iter()
        .map(|name| name.as_ref().to_owned())
        .collect::<Vec<_>>()
        .join(" ")
}

/// The gate: every `build_*_prelude` in the crate is reachable from
/// `shape_search`, or is listed with a measured reason.
#[test]
fn shape_search_indexes_every_prelude_builder() {
    let defs = builder_definitions();
    let authority: BTreeSet<String> = defs.keys().cloned().collect();
    assert!(
        authority.len() >= 25,
        "the builder scan found only {} definitions; the authority scan is \
         broken and a green verdict from it would be meaningless (positive \
         control: 31 builders existed on 2026-09-06)",
        authority.len()
    );

    let graph = call_graph(&defs);
    let direct = shape_search_direct(&authority);
    assert!(
        !direct.is_empty(),
        "the call-site scan of examples/shape_search.rs found no builder at \
         all, so this test could not fail no matter what the example built"
    );
    let covered = reachable(&direct, &graph);

    let allowed: BTreeSet<String> = DELIBERATELY_UNINDEXED
        .iter()
        .map(|(name, _)| (*name).to_owned())
        .collect();
    let missing: Vec<&String> = authority
        .iter()
        .filter(|name| !covered.contains(*name) && !allowed.contains(*name))
        .collect();
    let transitive: Vec<&String> = covered.difference(&direct).collect();

    println!("authority ({}): {}", authority.len(), join(&authority));
    println!("built directly ({}): {}", direct.len(), join(&direct));
    println!(
        "reached transitively ({}): {}",
        transitive.len(),
        join(&transitive)
    );
    println!("allowlisted ({}): {}", allowed.len(), join(&allowed));
    println!("BLIND ({}): {}", missing.len(), join(&missing));

    assert!(
        missing.is_empty(),
        "shape_search is blind to {} of the crate's {} prelude builders:\n  {}\n\
         An ABSENT verdict for anything those builders declare is a confident \
         wrong answer. Either index them in examples/shape_search.rs (adding a \
         row to the GROUPS table, which is the single source of both the \
         `coverage:` line and the kernels actually built), or list them in \
         DELIBERATELY_UNINDEXED with a MEASURED reason.\n\
         built directly ({}): {}\n  reached transitively ({}): {}",
        missing.len(),
        authority.len(),
        missing
            .iter()
            .map(|name| name.as_str())
            .collect::<Vec<_>>()
            .join("\n  "),
        direct.len(),
        join(&direct),
        transitive.len(),
        join(&transitive),
    );
}

/// An allowlist entry with no measured reason is an omission wearing a badge.
#[test]
fn reasons_are_measured() {
    let defs = builder_definitions();
    for (name, reason) in DELIBERATELY_UNINDEXED {
        assert!(
            defs.contains_key(*name),
            "DELIBERATELY_UNINDEXED names {name}, which is not a \
             `pub fn build_*_prelude` in this crate — a stale entry silently \
             excuses nothing and hides a real gap"
        );
        assert!(
            reason.len() >= 30,
            "DELIBERATELY_UNINDEXED entry {name} carries no measured reason \
             ({reason:?}); an entry must say what it COSTS or what makes it \
             unreachable, not that somebody chose to skip it"
        );
    }
}

/// The example's `coverage:` line names one group per indexed kernel, and the
/// group table is the single source of both. This test checks that the table
/// exists in the shape the runtime cross-check depends on — if somebody
/// re-splits it into two hand-written halves, the in-example assert goes back
/// to comparing a list against itself.
#[test]
fn shape_search_derives_its_groups_from_one_table() {
    let path = manifest_dir().join("examples/shape_search.rs");
    let text = std::fs::read_to_string(&path).expect("shape_search.rs is readable");
    assert!(
        text.contains("const GROUPS: &[Group]"),
        "examples/shape_search.rs no longer declares a single `GROUPS` table. \
         The `coverage:` line and the set of kernels actually indexed must come \
         from ONE list; when they were two hand-written lists the internal \
         cross-check passed for months while both halves omitted the same \
         fourteen builders."
    );
}
