//! The trust ledger's status column, checked against the code that produces the
//! trust steps (roadmap P0.5).
//!
//! `tests/trust_ledger.rs` is a golden test over the *rendered* markdown, and its
//! `trust_ids_are_well_formed` iterates `ALL_TRUST_IDS` — its own list. That is
//! the "every X" shape `docs/contributor-guide/evidence-and-checker-discipline.md`
//! warns about: it measures the maintainer's memory, not the code. A reduction
//! added to `TrustId` and forgotten everywhere else passes it, and a route that
//! stopped certifying passes it too.
//!
//! This suite derives instead. Its authority is
//! `crates/axeyum-solver/src/**.rs`: the `(TrustId::…, <certified>)` pairs the
//! producing code actually writes when it builds an `EvidenceReport`. From those
//! it recomputes, per reduction, the same fold `TrustId::coverage` performs over
//! `trust::EVIDENCE_ROUTES`, and fails on any disagreement — in either direction.
//!
//! What each test can catch, stated as the mutation that kills it:
//!
//! | Test | Dies when |
//! |---|---|
//! | `every_trust_id_variant_is_in_all_trust_ids` | a `TrustId` variant is added and not listed |
//! | `every_trust_id_declares_an_evidence_route` | a `TrustId` is added with no `EVIDENCE_ROUTES` row |
//! | `declared_coverage_matches_the_flags_the_code_records` | a route's `certifies` disagrees with the `certified:` flag the producer writes |
//! | `every_route_names_a_symbol_that_exists` | a producer or checker is renamed or deleted |
//! | `a_route_with_no_checker_cannot_certify` | a row claims `certifies: true` with `NO_CHECKER` |
//! | `the_rendered_ledger_is_the_derived_set` | the markdown stops reflecting `coverage()` |
//!
//! Every scan carries a non-vacuity floor, because a scanner that silently
//! matched nothing would make all six pass over an empty set.
#![cfg(feature = "full")]

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};

use axeyum_solver::trust::{
    ALL_TRUST_IDS, CertifiedCoverage, EVIDENCE_ROUTES, NO_CHECKER, TrustId, trust_ledger_markdown,
};

/// Floors below which a scan is reporting on nothing and its verdict is
/// meaningless. Measured at the commit that introduced this suite: 43 recorded
/// flag sites over 15 reductions.
const MIN_RECORDED_FLAG_SITES: usize = 30;
const MIN_REDUCTIONS_WITH_A_RECORDED_FLAG: usize = 12;

fn crate_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
}

fn workspace_crates() -> Vec<PathBuf> {
    let crates = crate_root().join("..");
    [
        "axeyum-solver",
        "axeyum-cnf",
        "axeyum-smtlib",
        "axeyum-rewrite",
    ]
    .iter()
    .map(|name| crates.join(name).join("src"))
    .collect()
}

/// Every `.rs` file under `dir`, recursively, in sorted order (determinism is a
/// public promise; a hash-ordered walk would make failures irreproducible).
fn rust_sources(dir: &Path) -> Vec<PathBuf> {
    let mut out = Vec::new();
    let mut stack = vec![dir.to_path_buf()];
    while let Some(next) = stack.pop() {
        let Ok(entries) = std::fs::read_dir(&next) else {
            continue;
        };
        let mut paths: Vec<PathBuf> = entries.flatten().map(|e| e.path()).collect();
        paths.sort();
        for path in paths {
            if path.is_dir() {
                stack.push(path);
            } else if path.extension().is_some_and(|e| e == "rs") {
                out.push(path);
            }
        }
    }
    out.sort();
    out
}

/// Drops `//`-comments (so doc comments and explanatory prose naming a `TrustId`
/// are never mistaken for a production site) and everything from the first
/// top-level `#[cfg(test)]` onward (so a test fixture is never mistaken for one
/// either). Conservative in the direction that loses observations, which the
/// non-vacuity floors then catch.
fn production_text(source: &str) -> String {
    let mut out = String::with_capacity(source.len());
    for line in source.lines() {
        if line.trim() == "#[cfg(test)]" {
            break;
        }
        let code = match line.find("//") {
            Some(at) => &line[..at],
            None => line,
        };
        out.push_str(code);
        out.push('\n');
    }
    out
}

/// Removes the `EVIDENCE_ROUTES` declaration from `trust.rs`'s text. The table is
/// the thing under test; letting it be its own evidence is exactly the circular
/// "checker that cannot fail" this suite exists to avoid.
fn without_the_route_table(text: &str) -> String {
    let Some(start) = text.find("pub const EVIDENCE_ROUTES") else {
        return text.to_owned();
    };
    let tail = &text[start..];
    let end = tail.find("\n];").map_or(text.len(), |at| start + at + 3);
    let mut out = String::from(&text[..start]);
    out.push_str(&text[end..]);
    out
}

/// What a producing site wrote for a step's `certified` flag.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum RecordedFlag {
    /// A literal `true`.
    AlwaysCertified,
    /// A literal `false`.
    NeverCertified,
    /// A runtime expression: the route can produce either, so the reduction is
    /// partially covered by construction.
    Computed,
}

/// Scans production source for `(TrustId::X, <flag>)` and
/// `TrustStep { id: TrustId::X, certified: <flag> }` sites.
fn recorded_flags() -> BTreeMap<String, BTreeSet<RecordedFlag>> {
    let mut found: BTreeMap<String, BTreeSet<RecordedFlag>> = BTreeMap::new();
    let mut sites = 0usize;
    for path in rust_sources(&crate_root().join("src")) {
        if path.file_name().is_some_and(|n| n == "tests.rs") {
            continue;
        }
        let Ok(raw) = std::fs::read_to_string(&path) else {
            continue;
        };
        let text = without_the_route_table(&production_text(&raw));
        for (variant, flag) in scan_sites(&text) {
            sites += 1;
            found.entry(variant).or_default().insert(flag);
        }
    }
    assert!(
        sites >= MIN_RECORDED_FLAG_SITES,
        "the scanner found only {sites} recorded trust-step flags in \
         crates/axeyum-solver/src — below the {MIN_RECORDED_FLAG_SITES} floor. \
         Either the producing code moved or the scanner stopped matching; either \
         way this suite is reporting on an empty set and must not pass.",
    );
    assert!(
        found.len() >= MIN_REDUCTIONS_WITH_A_RECORDED_FLAG,
        "only {} reduction(s) had a recorded flag (floor {MIN_REDUCTIONS_WITH_A_RECORDED_FLAG}): {:?}",
        found.len(),
        found.keys().collect::<Vec<_>>(),
    );
    found
}

fn scan_sites(text: &str) -> Vec<(String, RecordedFlag)> {
    const MARKER: &str = "TrustId::";
    let bytes = text.as_bytes();
    let mut out = Vec::new();
    let mut cursor = 0usize;
    while let Some(at) = text[cursor..].find(MARKER) {
        let start = cursor + at + MARKER.len();
        cursor = start;
        let mut end = start;
        while end < bytes.len() && (bytes[end].is_ascii_alphanumeric() || bytes[end] == b'_') {
            end += 1;
        }
        if end == start {
            continue;
        }
        let variant = text[start..end].to_owned();
        // A recorded step is `TrustId::X` followed immediately by a comma.
        let mut rest = text[end..].trim_start();
        if !rest.starts_with(',') {
            continue;
        }
        rest = rest[1..].trim_start();
        if let Some(after) = rest.strip_prefix("certified:") {
            rest = after.trim_start();
        }
        let value: String = rest
            .chars()
            .take_while(|c| !matches!(c, ',' | ')' | '}' | ';' | '\n'))
            .collect();
        let value = value.trim();
        // A struct-field spelling (`producer: "…"`) is a declaration, not a
        // recorded step; and a token that cannot begin a Rust expression is the
        // punctuation after a bare list entry (`TrustId::Diophantine,\n];`), not
        // a flag at all.
        if value.is_empty()
            || value.contains(':')
            || !value.starts_with(|c: char| c.is_ascii_alphanumeric() || c == '_')
        {
            continue;
        }
        out.push((
            variant,
            match value {
                "true" => RecordedFlag::AlwaysCertified,
                "false" => RecordedFlag::NeverCertified,
                _ => RecordedFlag::Computed,
            },
        ));
    }
    out
}

/// The same fold `TrustId::coverage` performs, recomputed from the flags the
/// producing code writes rather than from the declared table.
fn coverage_from_recorded(flags: &BTreeSet<RecordedFlag>) -> CertifiedCoverage {
    if flags.is_empty() {
        return CertifiedCoverage::Unrouted;
    }
    if flags.contains(&RecordedFlag::Computed) {
        return CertifiedCoverage::Partial;
    }
    let certifies = flags.contains(&RecordedFlag::AlwaysCertified);
    let trusts = flags.contains(&RecordedFlag::NeverCertified);
    match (certifies, trusts) {
        (true, false) => CertifiedCoverage::Full,
        (true, true) => CertifiedCoverage::Partial,
        (false, true) => CertifiedCoverage::Uncertified,
        (false, false) => CertifiedCoverage::Unrouted,
    }
}

/// The `TrustId` enum's variant names, read out of `trust.rs` itself. Deriving
/// them from the source rather than from `ALL_TRUST_IDS` is the whole point: a
/// list cannot testify that it is complete.
fn declared_variants() -> Vec<String> {
    let source = std::fs::read_to_string(crate_root().join("src/trust.rs")).expect("read trust.rs");
    let body = source
        .split_once("pub enum TrustId {")
        .expect("TrustId enum")
        .1;
    let body = body.split_once("\n}").expect("TrustId enum end").0;
    let mut out = Vec::new();
    for line in body.lines() {
        let line = line.trim();
        if line.is_empty() || line.starts_with("//") || line.starts_with('#') {
            continue;
        }
        let Some(name) = line.strip_suffix(',') else {
            continue;
        };
        if name.chars().all(|c| c.is_ascii_alphanumeric() || c == '_')
            && name.starts_with(|c: char| c.is_ascii_uppercase())
        {
            out.push(name.to_owned());
        }
    }
    assert!(
        out.len() >= 10,
        "parsed only {} TrustId variants from trust.rs — the parser broke",
        out.len(),
    );
    out
}

fn debug_name(id: TrustId) -> String {
    format!("{id:?}")
}

#[test]
fn every_trust_id_variant_is_in_all_trust_ids() {
    let listed: BTreeSet<String> = ALL_TRUST_IDS.iter().copied().map(debug_name).collect();
    let declared = declared_variants();
    let missing: Vec<&String> = declared.iter().filter(|v| !listed.contains(*v)).collect();
    assert!(
        missing.is_empty(),
        "TrustId variant(s) {missing:?} are declared in the enum but absent from \
         ALL_TRUST_IDS, so the ledger cannot render them",
    );
    assert_eq!(
        declared.len(),
        ALL_TRUST_IDS.len(),
        "ALL_TRUST_IDS has {} entries for {} enum variants (a duplicate, or an id \
         listed twice)",
        ALL_TRUST_IDS.len(),
        declared.len(),
    );
}

#[test]
fn every_trust_id_declares_an_evidence_route() {
    let unrouted: Vec<String> = ALL_TRUST_IDS
        .iter()
        .filter(|id| id.coverage() == CertifiedCoverage::Unrouted)
        .map(|id| debug_name(*id))
        .collect();
    assert!(
        unrouted.is_empty(),
        "TrustId(s) {unrouted:?} have no row in trust::EVIDENCE_ROUTES. A reduction \
         with no declared producer, artifact and checker cannot be graded, and the \
         ledger must not guess a status for it.",
    );
}

#[test]
fn a_route_with_no_checker_cannot_certify() {
    for route in EVIDENCE_ROUTES {
        assert!(
            !(route.checker == NO_CHECKER && route.certifies),
            "{:?} route via {} claims to certify with no checker at all",
            route.id,
            route.producer,
        );
    }
    // Non-vacuity: the invariant is only meaningful if such routes exist.
    let uncheckable = EVIDENCE_ROUTES
        .iter()
        .filter(|r| r.checker == NO_CHECKER)
        .count();
    assert!(
        uncheckable >= 3,
        "expected several checker-free routes (bare unsat, search-only XOR, \
         undischarged theory lemma); found {uncheckable}",
    );
}

#[test]
fn declared_coverage_matches_the_flags_the_code_records() {
    let recorded = recorded_flags();
    let mut disagreements = Vec::new();
    for &id in ALL_TRUST_IDS {
        let name = debug_name(id);
        let flags = recorded.get(&name).cloned().unwrap_or_default();
        let derived = coverage_from_recorded(&flags);
        if derived == CertifiedCoverage::Unrouted {
            // The producer computes this id's flag through a helper the textual
            // scan cannot classify. The route table must still name that helper,
            // and `every_route_names_a_symbol_that_exists` proves it is real.
            assert!(
                EVIDENCE_ROUTES.iter().any(|r| r.id == id),
                "{name} has no recorded flag and no declared route",
            );
            continue;
        }
        if derived != id.coverage() {
            disagreements.push(format!(
                "{name}: code records {flags:?} => {derived:?}, but \
                 EVIDENCE_ROUTES folds to {:?}",
                id.coverage()
            ));
        }
    }
    assert!(
        disagreements.is_empty(),
        "trust::EVIDENCE_ROUTES disagrees with the trust steps the producing code \
         writes:\n  {}",
        disagreements.join("\n  "),
    );
}

#[test]
fn every_route_names_a_symbol_that_exists() {
    let sources: Vec<String> = workspace_crates()
        .iter()
        .flat_map(|dir| rust_sources(dir))
        .filter_map(|path| std::fs::read_to_string(path).ok())
        .collect();
    assert!(
        sources.len() >= 100,
        "loaded only {} source files — the search corpus is wrong",
        sources.len(),
    );
    let defines = |name: &str| {
        ["fn ", "struct ", "enum ", "type ", "trait "]
            .iter()
            .any(|kw| {
                let needle = format!("{kw}{name}");
                sources.iter().any(|src| {
                    src.match_indices(&needle).any(|(at, _)| {
                        let after = at + needle.len();
                        src.as_bytes()
                            .get(after)
                            .is_none_or(|c| !(c.is_ascii_alphanumeric() || *c == b'_'))
                    })
                })
            })
    };
    let mut missing = Vec::new();
    for route in EVIDENCE_ROUTES {
        if !defines(route.producer) {
            missing.push(format!("{:?} producer `{}`", route.id, route.producer));
        }
        if route.checker != NO_CHECKER && !defines(route.checker) {
            missing.push(format!("{:?} checker `{}`", route.id, route.checker));
        }
    }
    assert!(
        missing.is_empty(),
        "trust::EVIDENCE_ROUTES names symbol(s) that are not defined anywhere in \
         the solver/cnf/smtlib/rewrite sources: {missing:?}. A route whose \
         producer or checker is gone is not an evidence route.",
    );
    // Non-vacuity: a `defines` that always returned true would pass the above.
    assert!(
        !defines("a_symbol_that_is_not_in_this_tree_at_all"),
        "the symbol search matches anything — it proves nothing",
    );
}

#[test]
fn the_rendered_ledger_is_the_derived_set() {
    let markdown = trust_ledger_markdown();

    // The Status column is `is_certified()`, which is the fold, not a literal.
    for &id in ALL_TRUST_IDS {
        let status = if id.is_certified() {
            "certified"
        } else {
            "trust hole"
        };
        let row = format!(
            "| {} | {} | {} | {} | {} |",
            id.label(),
            id.meaning(),
            id.pedantic_level(),
            status,
            id.reference()
        );
        assert!(
            markdown.contains(&row),
            "{} has no Status row matching its derived coverage {:?}",
            id.label(),
            id.coverage(),
        );
    }

    // Every declared route renders, with the coverage word the fold produced.
    for route in EVIDENCE_ROUTES {
        let row = format!(
            "| {} | {} | `{}` |",
            route.id.label(),
            route.id.coverage().label(),
            route.producer,
        );
        assert!(
            markdown.contains(&row),
            "the coverage table is missing {row:?}",
        );
    }

    let holes = ALL_TRUST_IDS.iter().filter(|id| !id.is_certified()).count();
    let partial = ALL_TRUST_IDS
        .iter()
        .filter(|id| id.coverage() == CertifiedCoverage::Partial)
        .count();
    let uncertified = ALL_TRUST_IDS
        .iter()
        .filter(|id| id.coverage() == CertifiedCoverage::Uncertified)
        .count();
    assert_eq!(
        holes,
        partial + uncertified,
        "a trust hole is exactly a reduction that is not fully covered",
    );
    assert!(
        markdown.contains(&format!(
            "Trusted base: **{holes}** reduction(s) remain trust holes."
        )),
        "the headline count is not the derived one ({holes})",
    );
    assert!(
        markdown.contains(&format!("**{partial}** are *partially certified*")),
        "the coverage split's partial count is not the derived one ({partial})",
    );
    assert!(
        markdown.contains(&format!("**{uncertified}** have no certified route")),
        "the coverage split's uncertified count is not the derived one ({uncertified})",
    );
}
