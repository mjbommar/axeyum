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
//! * **The example's reach** — a walk that STARTS at the `build:` fields of
//!   the example's `GROUPS` table and follows local functions, with `//`
//!   comment lines stripped. Not "every call site in the file": a helper the
//!   table no longer names is dead code that still contains the call, and
//!   scanning the whole file let two deleted `Group` rows pass green (measured
//!   as surviving mutants M1/M2 on 2026-09-06).
//!
//! A builder is covered when it is reachable from a direct call site through
//! that call graph. Anything else must appear in one of the two allowlists with
//! a measured reason, or the gate fails and prints both sides.
//!
//! There are two gates, over DISJOINT denominators: `*_prelude` builders, and
//! exported builders that are not `*_prelude`. Disjoint because two gates
//! sharing a denominator both die to one deletion, and a guard set whose
//! members all fail through the same finding cannot tell you which guard is
//! load-bearing.

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
    let entries =
        std::fs::read_dir(dir).unwrap_or_else(|e| panic!("read_dir {}: {e}", dir.display()));
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
         not be located in {}; the definition scan and the body scan disagree, \
         which makes every coverage verdict below meaningless",
        file.display()
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

/// The body of a top-level `fn <name>` in `text`.
///
/// Same column-0 convention as [`builder_body`].
fn local_fn_body(text: &str, name: &str) -> Option<String> {
    let head = format!("fn {name}(");
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
    inside.then_some(body)
}

/// Every top-level `fn` name in `text`.
fn local_fn_names(text: &str) -> BTreeSet<String> {
    text.lines()
        .filter_map(|line| line.strip_prefix("fn "))
        .filter_map(|rest| rest.split(['(', '<']).next())
        .map(str::to_owned)
        .collect()
}

/// The builders `examples/shape_search.rs` calls FROM ITS GROUPS TABLE.
///
/// Not "calls anywhere in the file". A `Group` row is what makes a builder
/// run; a helper the table no longer names is dead code that still contains
/// the call. Scanning the whole file therefore made this census satisfiable by
/// a leftover function — verified as a surviving mutant on 2026-09-06: deleting
/// the `metric_prod` and `fo_substitution` rows left every test GREEN, because
/// `fn build_metric_prod` was still in the file. The walk starts at the
/// `build:` fields and follows local functions, so only builders the table can
/// actually reach are counted.
fn shape_search_direct(authority: &BTreeSet<String>) -> BTreeSet<String> {
    let path = manifest_dir().join("examples/shape_search.rs");
    let text = std::fs::read_to_string(&path).expect("shape_search.rs is readable");
    let stripped = strip_line_comments(&text);

    let entries: Vec<String> = stripped
        .lines()
        .filter_map(|line| line.trim().strip_prefix("build: "))
        .map(|rest| rest.trim_end_matches(',').trim().to_owned())
        .collect();
    assert!(
        !entries.is_empty(),
        "no `build:` field was found in examples/shape_search.rs, so the walk \
         below starts nowhere and every gate in this file would pass \
         vacuously"
    );

    let locals = local_fn_names(&stripped);
    let mut seen: BTreeSet<String> = BTreeSet::new();
    let mut called: BTreeSet<String> = BTreeSet::new();
    let mut stack = entries;
    while let Some(name) = stack.pop() {
        if !seen.insert(name.clone()) {
            continue;
        }
        let Some(body) = local_fn_body(&stripped, &name) else {
            continue;
        };
        called.extend(builders_called(&body, authority));
        for local in &locals {
            if body.contains(&format!("{local}(")) {
                stack.push(local.clone());
            }
        }
    }
    called
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

/// What `shape_search` reaches, computed ONCE over the widest call graph.
///
/// Both gates below ask the same question of different denominators, and the
/// path to a prelude can leave the prelude family: `build_list_prelude` is
/// reached only through `build_list_nat_bridge`, which is not a `*_prelude`.
/// Computing reachability over the narrow graph alone therefore reports a
/// prelude as blind while the example does build it. One graph, two
/// denominators.
fn shape_search_reach() -> (BTreeSet<String>, BTreeSet<String>) {
    let defs = exported_builder_definitions();
    let authority: BTreeSet<String> = defs.keys().cloned().collect();
    let graph = call_graph(&defs);
    let direct = shape_search_direct(&authority);
    assert!(
        !direct.is_empty(),
        "the GROUPS-table walk over examples/shape_search.rs found no builder \
         at all, so neither gate below could fail no matter what the example \
         built"
    );
    let covered = reachable(&direct, &graph);
    (direct, covered)
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

    let (all_direct, covered) = shape_search_reach();
    let direct: BTreeSet<String> = all_direct.intersection(&authority).cloned().collect();

    let allowed: BTreeSet<String> = DELIBERATELY_UNINDEXED
        .iter()
        .map(|(name, _)| (*name).to_owned())
        .collect();
    let missing: Vec<&String> = authority
        .iter()
        .filter(|name| !covered.contains(*name) && !allowed.contains(*name))
        .collect();
    let reached: BTreeSet<String> = covered.intersection(&authority).cloned().collect();
    let transitive: Vec<&String> = reached.difference(&direct).collect();

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

/// Builders that are not `*_prelude` and that the index deliberately skips.
///
/// Same contract as `DELIBERATELY_UNINDEXED`: `(builder, measured reason)`.
const DELIBERATELY_UNINDEXED_NON_PRELUDE: &[(&str, &str)] = &[];

/// Every `pub fn build_*` under `src/` that `src/lib.rs` also names, mapped to
/// the file that owns it.
///
/// `*_prelude` is not the whole builder surface, and the difference is not
/// cosmetic. Measured 2026-09-06: `build_list_prelude` alone gives 15 rows
/// under `List` and `--name-contains List.Perm` returns NOTHING, because
/// `List.Perm` is declared by `build_list_perm` over `build_list_nat_bridge`.
/// A census restricted to `*_prelude` would have called that covered. So the
/// authority for this second gate is every builder an example could actually
/// call: defined `pub` under `src/`, and named in `src/lib.rs`.
fn exported_builder_definitions() -> BTreeMap<String, PathBuf> {
    let lib =
        std::fs::read_to_string(manifest_dir().join("src/lib.rs")).expect("src/lib.rs is readable");
    let exported = strip_line_comments(&lib);
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
            let Some(suffix) = rest.split(['(', '<']).next() else {
                continue;
            };
            let name = format!("build_{suffix}");
            if exported.contains(&name) {
                defs.insert(name, file.clone());
            }
        }
    }
    defs
}

/// The second gate: the same reachability question over every exported builder
/// that is NOT a `*_prelude`.
///
/// Disjoint from the gate above on purpose. Two gates sharing a denominator
/// both die to one deletion, and a guard set where every member fails through
/// the same finding tells you nothing about which guard is load-bearing —
/// measured here as M1/M2 killing two tests apiece before this split. With
/// disjoint denominators, removing a prelude row kills exactly the prelude
/// gate and removing `build_list_perm` kills exactly this one.
#[test]
fn shape_search_indexes_every_exported_non_prelude_builder() {
    let preludes = builder_definitions();
    let mut defs = exported_builder_definitions();
    let exported_total = defs.len();
    defs.retain(|name, _| !preludes.contains_key(name));
    let authority: BTreeSet<String> = defs.keys().cloned().collect();
    assert!(
        exported_total > preludes.len() && !authority.is_empty(),
        "the exported-builder scan found {exported_total} builders and the \
         prelude scan found {}, leaving {} for this gate; if that remainder is \
         empty the gate is measuring nothing and cannot catch what the prelude \
         gate misses (positive control: 40 exported, 31 prelude, 9 non-prelude \
         on 2026-09-06)",
        preludes.len(),
        authority.len()
    );

    let (all_direct, covered) = shape_search_reach();
    let direct: BTreeSet<String> = all_direct.intersection(&authority).cloned().collect();

    let allowed: BTreeSet<String> = DELIBERATELY_UNINDEXED_NON_PRELUDE
        .iter()
        .map(|(name, _)| (*name).to_owned())
        .collect();
    let missing: Vec<&String> = authority
        .iter()
        .filter(|name| !covered.contains(*name) && !allowed.contains(*name))
        .collect();
    let reached: BTreeSet<String> = covered.intersection(&authority).cloned().collect();
    let transitive: Vec<&String> = reached.difference(&direct).collect();

    println!(
        "non-prelude authority ({}): {}",
        authority.len(),
        join(&authority)
    );
    println!("built directly ({}): {}", direct.len(), join(&direct));
    println!(
        "reached transitively ({}): {}",
        transitive.len(),
        join(&transitive)
    );
    println!("BLIND ({}): {}", missing.len(), join(&missing));

    assert!(
        missing.is_empty(),
        "shape_search is blind to {} of the crate's {} exported NON-PRELUDE \
         builders:\n  {}\n\
         These declare into the kernel like any prelude does, so an ABSENT \
         verdict for what they declare is a confident wrong answer. Index them \
         in examples/shape_search.rs or list them in \
         DELIBERATELY_UNINDEXED_NON_PRELUDE with a MEASURED reason.",
        missing.len(),
        authority.len(),
        missing
            .iter()
            .map(|name| name.as_str())
            .collect::<Vec<_>>()
            .join("\n  "),
    );
}

/// An allowlist entry with no measured reason is an omission wearing a badge.
#[test]
fn reasons_are_measured() {
    let defs = exported_builder_definitions();
    for (name, reason) in DELIBERATELY_UNINDEXED
        .iter()
        .chain(DELIBERATELY_UNINDEXED_NON_PRELUDE)
    {
        assert!(
            defs.contains_key(*name),
            "DELIBERATELY_UNINDEXED names {name}, which is not a \
             exported `pub fn build_*` in this crate — a stale entry silently \
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
