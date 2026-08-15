//! Census one or more format-3.1 `lean4export` streams: report every kernel
//! decline, not just the first.
//!
//! `lean4export_import` is fail-closed, so on a stream our kernel cannot fully
//! check it names one blocker and stops. This walks the same records through the
//! same trusted gate, skipping each refused declaration and recording why, so a
//! whole stream (or a whole batch of them) yields a distribution instead of a
//! single sample.
//!
//! Nothing here admits anything the gate refused: a skipped declaration is
//! absent from the staging kernel, which is exactly why dependents of a skipped
//! declaration show up as `UnknownConst`. Those are marked `cascade` below and
//! must not be counted as independent blockers.
//!
//! ```sh
//! cargo run -p axeyum-lean-import --example lean4export_census -- export.ndjson ...
//! ```

use std::collections::{BTreeMap, BTreeSet};
use std::fs::File;
use std::io::BufReader;
use std::path::PathBuf;

use axeyum_lean_import::{CensusDecline, ImportLimits, census_ndjson};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let paths: Vec<PathBuf> = std::env::args_os().skip(1).map(PathBuf::from).collect();
    if paths.is_empty() {
        return Err("usage: lean4export_census <export.ndjson> [more.ndjson ...]".into());
    }

    let mut streams_total = 0usize;
    let mut streams_clean = 0usize;
    let mut records_total = 0usize;
    let mut declines_total = 0usize;
    let mut by_code: BTreeMap<String, usize> = BTreeMap::new();
    let mut by_cluster: BTreeMap<&'static str, usize> = BTreeMap::new();
    // A declaration can be refused once per stream that mentions it; count the
    // distinct names so a widely re-exported blocker is not inflated.
    let mut distinct_root: BTreeSet<String> = BTreeSet::new();
    let mut distinct_cascade: BTreeSet<String> = BTreeSet::new();

    for path in &paths {
        streams_total += 1;
        let reader = BufReader::new(File::open(path)?);
        let census = match census_ndjson(reader, ImportLimits::default()) {
            Ok(census) => census,
            Err(error) => {
                println!("STREAM|{}|reader-error|{error}", path.display());
                continue;
            }
        };
        records_total += census.declaration_records;
        declines_total += census.declines.len();
        if census.declines.is_empty() {
            streams_clean += 1;
        }
        println!(
            "STREAM|{}|records={}|admitted_records={}|admitted_decls={}|declines={}",
            path.display(),
            census.declaration_records,
            census.admitted_records,
            census.admitted_declarations,
            census.declines.len(),
        );
        for decline in &census.declines {
            let cascade = is_cascade(decline);
            let cluster = cluster_of(&decline.declaration, cascade);
            *by_code.entry(decline.code.clone()).or_default() += 1;
            *by_cluster.entry(cluster).or_default() += 1;
            if cascade {
                distinct_cascade.insert(decline.declaration.clone());
            } else {
                distinct_root.insert(decline.declaration.clone());
            }
            println!(
                "  DECLINE|line={}|{}|{}|{}|{}",
                decline.line,
                decline.declaration,
                decline.code,
                cluster,
                if cascade { "cascade" } else { "root" },
            );
        }
    }

    println!(
        "CENSUS|streams={streams_total}|clean_streams={streams_clean}|decl_records={records_total}|declines={declines_total}|distinct_root={}|distinct_cascade={}",
        distinct_root.len(),
        distinct_cascade.len(),
    );
    for (code, count) in &by_code {
        println!("CODE|{code}|{count}");
    }
    for (cluster, count) in &by_cluster {
        println!("CLUSTER|{cluster}|{count}");
    }
    println!("--- distinct root blockers ---");
    for name in &distinct_root {
        println!("ROOT|{name}|{}", cluster_of(name, false));
    }
    Ok(())
}

/// A decline caused only by an earlier skip. `UnknownConst` cannot arise from a
/// well-formed export otherwise: `lean4export` emits dependencies first, so the
/// only way a constant is missing is that we refused it upstream.
fn is_cascade(decline: &CensusDecline) -> bool {
    decline.code == "UnknownConst"
}

/// Group a refused declaration by the kernel capability it is waiting on. Names
/// are Lean's compiler-generated conventions, so this is a read of *what the
/// elaborator emitted*, not a guess about our kernel.
fn cluster_of(name: &str, cascade: bool) -> &'static str {
    if cascade {
        return "cascade";
    }
    if name.contains("noConfusion") {
        return "noConfusion";
    }
    if name.contains("brecOn") || name.contains("below") || name.contains("ibelow") {
        return "brecOn/below";
    }
    if name.contains(".match_") || name.contains("_matcher") {
        return "match-auxiliary";
    }
    if name.ends_with("._f") || name.contains("._f.") || name.contains(".go") {
        return "structural-recursion-body";
    }
    if name.contains("heq") || name.contains("HEq") {
        return "HEq";
    }
    "other"
}
