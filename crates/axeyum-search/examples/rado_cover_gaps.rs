//! What a partial tree cover has NOT covered, as a resumable pending file.
//!
//! `run_adaptive_cover` writes its pending set when it exits. A run that is
//! killed — an operator, an OOM, a host going away — never gets to, and then
//! the only durable record is the ledger, which is flushed row by row. This
//! driver reconstructs the resume point from that ledger alone, so **no run is
//! ever unresumable**, however it died.
//!
//! It is also the tool for splitting one tree across hosts. The gaps of a
//! partial cover, filtered by prefix, are a disjoint work partition: give one
//! host the gaps under `c(p1)=1,2` and another the cubes `[3]` and `[4]`, and
//! the union of the two ledgers is a cover of the whole tree with no overlap
//! anywhere.
//!
//! # What a gap is
//!
//! Walking the branch trie from the root: a node with a refuted row is covered;
//! a node with at least one refuted descendant is partially covered and is
//! recursed into; a node with no refuted descendant at all is a **maximal
//! uncovered cube** and is emitted. Emitting the maximal cube rather than its
//! leaves is what keeps a resume file small and lets the resumed run choose its
//! own splitting.
//!
//! This cannot cover for a mistake: if the gaps are wrong, the union of the
//! ledgers fails `verify_cube_cover` with `MissingCell` and nothing certifies.
//! The pending file also re-derives every cube code from its own path when it
//! is read back, so a corrupted or hand-edited file fails closed.
//!
//! An **overlap** — a refuted cube that also has refuted descendants — is
//! reported as an error rather than silently pruned: it means two runs covered
//! the same region, and which of them to keep is not this tool's decision.
//!
//! usage: `rado_cover_gaps a=5 b=4 k=4 n=741 points=5,10,… out=<pending.tsv> \
//!         ledger=<tsv> [ledger2=<tsv> …] [under=2] [depth_cap=16]`
//!
//! `under=` keeps only gaps whose first choice is in the given comma-separated
//! list; that is the host-partition filter.
//!
//! exit: 0 gaps written (0 gaps means the cover is complete), 3 an overlap or a
//! bad ledger, 2 usage.

// `main` is one long linear script by design: read the ledgers, walk the trie,
// write the resume file. The `as f64` casts are a percentage for a human in a
// log line; the exact covered measure is printed next to it as a ratio of
// integers, and that is the figure anything downstream should read.
#![allow(clippy::too_many_lines, clippy::cast_precision_loss)]

use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::process::ExitCode;

use axeyum_search::cover::colour_branch_plan;
use axeyum_search::harness::{PendingCube, PendingReason, render_pending};
use axeyum_search::ledger::parse_ledger;
use axeyum_search::{ColouringFamily, Rado};

fn main() -> ExitCode {
    let args: BTreeMap<String, String> = std::env::args()
        .skip(1)
        .filter_map(|arg| {
            arg.split_once('=')
                .map(|(key, value)| (key.to_string(), value.to_string()))
        })
        .collect();
    let number = |key: &str, fallback: usize| -> usize {
        args.get(key)
            .map_or(fallback, |value| value.parse().expect("number"))
    };
    let Some(out) = args.get("out") else {
        eprintln!(
            "usage: rado_cover_gaps a=5 b=4 k=4 n=741 points=5,10,… out=<pending.tsv> \
             ledger=<tsv> [ledger2=<tsv> …] [under=1,2]"
        );
        return ExitCode::from(2);
    };
    let (a, b, k, n) = (
        number("a", 5),
        number("b", 4),
        number("k", 4),
        number("n", 741),
    );
    let family = Rado::new(a, b, k).expect("family");
    let problem = family.problem(n).expect("problem");
    let points: Vec<usize> = match args.get("points") {
        Some(list) => list
            .split(',')
            .map(|token| token.parse().expect("branch point"))
            .collect(),
        None => family.branch_points(number("depth", 16)),
    };
    let plan = colour_branch_plan(&problem, &points).expect("plan");

    let mut refuted: BTreeSet<Vec<usize>> = BTreeSet::new();
    let mut ledgers: Vec<&String> = args
        .iter()
        .filter(|(key, _)| key.starts_with("ledger"))
        .map(|(_, value)| value)
        .collect();
    ledgers.sort();
    for path in &ledgers {
        let text = fs::read_to_string(path).unwrap_or_else(|error| {
            eprintln!("{path}: {error}");
            String::new()
        });
        match parse_ledger(&text) {
            Ok(rows) => {
                println!("ledger {path}: {} rows", rows.len());
                for row in rows {
                    // A row whose code contradicts its own path is a corrupted
                    // ledger; refuse rather than resume on a cube nobody meant.
                    let code = plan.prefix_code(&row.choices).expect("cube code");
                    if code != row.index {
                        println!(
                            "{{\"status\":\"bad-row\",\"index\":{},\"choices\":{:?}}}",
                            row.index, row.choices
                        );
                        return ExitCode::from(3);
                    }
                    refuted.insert(row.choices);
                }
            }
            Err(error) => {
                println!("{{\"status\":\"bad-ledger\",\"path\":{path:?},\"error\":\"{error}\"}}");
                return ExitCode::from(3);
            }
        }
    }

    // Every proper prefix of a refuted cube: the partially covered interior.
    let mut interior: BTreeSet<Vec<usize>> = BTreeSet::new();
    for path in &refuted {
        for level in 0..path.len() {
            interior.insert(path[..level].to_vec());
        }
    }
    let under: Option<Vec<usize>> = args.get("under").map(|list| {
        list.split(',')
            .map(|token| token.parse().expect("choice"))
            .collect()
    });

    let mut gaps: Vec<PendingCube> = Vec::new();
    let mut covered = 0usize;
    let mut stack: Vec<Vec<usize>> = vec![Vec::new()];
    while let Some(path) = stack.pop() {
        let inside = refuted.contains(&path);
        let partial = interior.contains(&path);
        if inside && partial {
            println!(
                "{{\"status\":\"overlap\",\"cube\":{path:?},\
                 \"note\":\"this cube is refuted AND has refuted descendants\"}}"
            );
            return ExitCode::from(3);
        }
        if inside {
            covered += 1;
            continue;
        }
        if !partial {
            if under
                .as_ref()
                .is_none_or(|keep| path.first().is_none_or(|first| keep.contains(first)))
            {
                gaps.push(PendingCube {
                    code: plan.prefix_code(&path).expect("cube code"),
                    path,
                    reason: PendingReason::Unstarted,
                });
            }
            continue;
        }
        let Some(group) = plan.groups().get(path.len()) else {
            println!("{{\"status\":\"impossible\",\"cube\":{path:?}}}");
            return ExitCode::from(3);
        };
        for choice in (1..=group.arity()).rev() {
            let mut child = path.clone();
            child.push(choice);
            stack.push(child);
        }
    }
    gaps.sort_by_key(|cube| cube.code);

    fs::write(out, render_pending(&gaps)).expect("write pending");
    // The covered measure: a cube at depth d holds 4^-d of the space when every
    // group has arity k. Reported as a ratio of exact integers so it is a
    // measurement rather than a floating-point impression.
    let deepest = refuted.iter().map(Vec::len).max().unwrap_or(0);
    let scale = u128::try_from(k)
        .expect("k")
        .pow(u32::try_from(deepest).expect("depth"));
    let mass: u128 = refuted
        .iter()
        .map(|path| {
            scale
                / u128::try_from(k)
                    .expect("k")
                    .pow(u32::try_from(path.len()).expect("depth"))
        })
        .sum();
    println!(
        "{{\"status\":\"gaps\",\"refuted\":{covered},\"gaps\":{},\"covered\":\"{mass}/{scale}\",\
         \"covered_pct\":{:.6},\"deepest_refuted\":{deepest},\"under\":{:?},\"out\":{out:?}}}",
        gaps.len(),
        100.0 * (mass as f64) / (scale as f64),
        under,
    );
    ExitCode::SUCCESS
}
