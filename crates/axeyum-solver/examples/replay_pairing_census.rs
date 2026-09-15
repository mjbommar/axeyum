//! Does the front door's `sat` evidence actually pair? A census, with the exit
//! status depending on the finding.
//!
//! # What this measures
//!
//! `solve_smtlib_with_model` hands back three things out of ONE run: the parsed
//! `script` (an arena), the `assertions` the flat encoding decided, and the
//! front door's own `model`. The standing rule is that a `sat` is checkable by
//! evaluating the original term against the lifted model, and the canonical
//! form of that check is
//!
//! ```text
//! check_model(&solved.script.arena, &solved.assertions, model)
//! ```
//!
//! ADR-2010 handed off a measurement: on the string divisions some `sat`
//! results come back with `assertions` = the **packed flat vector** and `model`
//! = a **source-level `Seq` model**, so the two bind different symbol sets and
//! the replay cannot run at all. This example re-derives that number on the
//! current tree and attributes each row to the front-door stage that decided
//! it, so the finding is per-route rather than per-division.
//!
//! # Why the exit status is not decorative
//!
//! A census that always exits 0 is a report, not a checker. `--require-paired`
//! makes the process fail when any `sat` carries a model that cannot be
//! replayed against the assertions shipped beside it, which is exactly the
//! defect. `--expect-mismatch N` is the inverse control: it fails unless the
//! count is `N`, so a run that silently stopped finding anything (a corpus path
//! typo, a budget too small to reach the routes) is distinguishable from a run
//! that found the defect repaired.
//!
//! # Usage
//!
//! ```text
//! cargo run --release -p axeyum-solver --features full --example replay_pairing_census -- \
//!     --budget-ms 3000 corpus/public-curated/non-incremental/QF_S
//! ```

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};
use std::time::Duration;

use axeyum_ir::{SymbolId, TermArena, TermId, TermNode};
use axeyum_solver::{
    CheckResult, RouteAttributionGuard, RouteOutcome, SolverConfig, Verdict, check_model,
    last_route_attribution,
    smtlib::{SmtLibSolved, solve_smtlib_with_model},
};

/// What the replay did for one `sat` row.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Replay {
    /// `assertions` empty and `model` `None` — the route withheld replay state
    /// on purpose. Honest, and NOT the defect.
    Withheld,
    /// `check_model` returned `Ok(true)`.
    Holds,
    /// `check_model` returned `Ok(false)` — the model does not satisfy the
    /// assertions shipped with it. On a correct `sat` this is a false alarm.
    Refuted,
    /// `check_model` returned `Err(..)` — it could not evaluate at all. The
    /// symbol-set mismatch this census exists to count.
    Errored,
}

struct Counts {
    holds: usize,
    refuted: usize,
    errored: usize,
    withheld: usize,
}

impl Counts {
    /// Records one `sat` row into both the total and its route's slot, so the
    /// two can never drift apart by a missed arm.
    fn add(&mut self, verdict: Replay, slot: &mut [usize; 4]) {
        let (total, index) = match verdict {
            Replay::Holds => (&mut self.holds, 0),
            Replay::Refuted => (&mut self.refuted, 1),
            Replay::Errored => (&mut self.errored, 2),
            Replay::Withheld => (&mut self.withheld, 3),
        };
        *total += 1;
        slot[index] += 1;
    }
}

/// The parsed command line.
struct Args {
    budget_ms: u64,
    require_paired: bool,
    explain: bool,
    expect_mismatch: Option<usize>,
    roots: Vec<PathBuf>,
}

fn parse_args() -> Args {
    let argv: Vec<String> = std::env::args().skip(1).collect();
    let mut parsed = Args {
        budget_ms: 3_000,
        require_paired: false,
        explain: false,
        expect_mismatch: None,
        roots: Vec::new(),
    };
    let mut i = 0;
    while i < argv.len() {
        match argv[i].as_str() {
            "--budget-ms" => {
                i += 1;
                parsed.budget_ms = argv[i].parse().expect("--budget-ms takes a number");
            }
            "--require-paired" => parsed.require_paired = true,
            "--explain" => parsed.explain = true,
            "--expect-mismatch" => {
                i += 1;
                parsed.expect_mismatch =
                    Some(argv[i].parse().expect("--expect-mismatch takes a number"));
            }
            other => parsed.roots.push(PathBuf::from(other)),
        }
        i += 1;
    }
    assert!(!parsed.roots.is_empty(), "no corpus roots given");
    parsed
}

/// The `.smt2` files under `roots`, in a deterministic order.
fn corpus(roots: &[PathBuf]) -> Vec<PathBuf> {
    let mut files: Vec<PathBuf> = Vec::new();
    for root in roots {
        collect(root, &mut files);
    }
    files.sort();
    assert!(!files.is_empty(), "corpus roots matched no .smt2 files");
    files
}

fn main() {
    let Args {
        budget_ms,
        require_paired,
        explain,
        expect_mismatch,
        roots,
    } = parse_args();
    let files = corpus(&roots);
    let config = SolverConfig::default().with_timeout(Duration::from_millis(budget_ms));

    let mut examined = 0usize;
    let mut undecided = 0usize;
    let mut unsat = 0usize;
    let mut sat = 0usize;
    let mut total = Counts {
        holds: 0,
        refuted: 0,
        errored: 0,
        withheld: 0,
    };
    let mut errored_out = 0usize;
    let mut error_detail: BTreeMap<String, usize> = BTreeMap::new();
    let mut per_route: BTreeMap<String, [usize; 4]> = BTreeMap::new();
    let mut mismatches: Vec<(String, String, String)> = Vec::new();

    for file in &files {
        let Ok(input) = std::fs::read_to_string(file) else {
            continue;
        };
        examined += 1;
        let solved = {
            let _guard = RouteAttributionGuard::enable();
            solve_smtlib_with_model(&input, &config)
        };
        // ADR-2045's arm reported `losses=0` by verdict while creating five new
        // aborts, because the harness folded errors into "undecided". They are
        // counted apart here: an arm that trades a wrong pairing for a crash has
        // not improved anything, and a single denominator cannot show that.
        let solved = match solved {
            Ok(solved) => solved,
            Err(error) => {
                errored_out += 1;
                *error_detail
                    .entry(error.to_string().chars().take(80).collect::<String>())
                    .or_insert(0) += 1;
                continue;
            }
        };
        let route = deciding_stage();
        match &solved.outcome.result {
            CheckResult::Unsat => {
                unsat += 1;
                continue;
            }
            CheckResult::Unknown(_) => {
                undecided += 1;
                continue;
            }
            CheckResult::Sat(_) => {}
        }
        sat += 1;
        let (verdict, detail) = classify(&solved);
        total.add(verdict, per_route.entry(route.clone()).or_insert([0; 4]));
        if matches!(verdict, Replay::Refuted | Replay::Errored) {
            if explain {
                explain_mismatch(file, &solved);
            }
            mismatches.push((file.display().to_string(), route, detail));
        }
    }

    report(
        budget_ms,
        examined,
        undecided,
        errored_out,
        &error_detail,
        unsat,
        sat,
        &total,
        &per_route,
        &mismatches,
    );
    gate(require_paired, expect_mismatch, sat, &total);
}

/// What the canonical replay says about one `sat` row's shipped pair.
fn classify(solved: &SmtLibSolved) -> (Replay, String) {
    let Some(model) = &solved.model else {
        return (Replay::Withheld, String::new());
    };
    match check_model(&solved.script.arena, &solved.assertions, model) {
        Ok(true) => (Replay::Holds, String::new()),
        Ok(false) => (Replay::Refuted, "check_model returned false".to_owned()),
        Err(error) => (
            Replay::Errored,
            error.to_string().chars().take(200).collect(),
        ),
    }
}

/// Prints the census. Every count carries its denominator: a bare zero here
/// would be indistinguishable from a census that examined nothing.
#[allow(clippy::too_many_arguments)]
fn report(
    budget_ms: u64,
    examined: usize,
    undecided: usize,
    errored_out: usize,
    error_detail: &BTreeMap<String, usize>,
    unsat: usize,
    sat: usize,
    total: &Counts,
    per_route: &BTreeMap<String, [usize; 4]>,
    mismatches: &[(String, String, String)],
) {
    let carrying = sat - total.withheld;
    println!("budget                                {budget_ms:>6} ms");
    println!("files examined (denominator)          {examined:>6}");
    println!("  undecided                           {undecided:>6}");
    println!("  front door returned Err             {errored_out:>6}");
    for (detail, count) in error_detail {
        println!("      {count:>4}  {detail}");
    }
    println!("  unsat                               {unsat:>6}");
    println!("  sat                                 {sat:>6}");
    println!(
        "    withholding replay state          {:>6}   of {sat}",
        total.withheld
    );
    println!("    carrying a model                  {carrying:>6}   of {sat}");
    println!("      replay Ok(true)                 {:>6}", total.holds);
    println!("      replay Ok(false)                {:>6}", total.refuted);
    println!("      replay Err(..)                  {:>6}", total.errored);
    println!();
    println!("per deciding front-door stage (Ok(true) / Ok(false) / Err / withheld):");
    for (route, counts) in per_route {
        println!(
            "  {route:<40} {:>4} {:>4} {:>4} {:>4}",
            counts[0], counts[1], counts[2], counts[3]
        );
    }
    if !mismatches.is_empty() {
        println!();
        println!("mispaired rows ({}):", mismatches.len());
        for (file, route, detail) in mismatches {
            println!("  {file}");
            println!("      route={route}  {detail}");
        }
    }
}

/// Makes the exit status depend on the finding. A census that always exits 0 is
/// a report, not a checker.
fn gate(require_paired: bool, expect_mismatch: Option<usize>, sat: usize, total: &Counts) {
    let mismatch_total = total.refuted + total.errored;
    let mut failed = false;
    if require_paired && mismatch_total > 0 {
        eprintln!(
            "FAIL: {mismatch_total} of {sat} `sat` results ship a model that cannot be replayed \
             against the assertions beside it"
        );
        failed = true;
    }
    if let Some(expected) = expect_mismatch
        && mismatch_total != expected
    {
        eprintln!("FAIL: expected {expected} mispaired rows, measured {mismatch_total}");
        failed = true;
    }
    if failed {
        std::process::exit(1);
    }
}

/// Names the symbol-identity mismatch for one mispaired row.
///
/// `symbol #0 unbound` is a symptom, not a diagnosis. What matters is WHICH
/// symbols the assertions reference and which ones the model binds, and at what
/// sort — a `Seq`-sorted binding beside a `BitVec`-sorted free symbol is a
/// different defect from a missing binding on the same symbol.
fn explain_mismatch(file: &Path, solved: &SmtLibSolved) {
    let Some(model) = &solved.model else {
        return;
    };
    let arena = &solved.script.arena;
    let mut free = BTreeSet::new();
    for &assertion in &solved.assertions {
        free_symbols(arena, assertion, &mut free);
    }
    println!("--- {} ---", file.display());
    println!("  assertions: {}", solved.assertions.len());
    println!("  free symbols of the PACKED assertion vector:");
    for &symbol in &free {
        let (name, sort) = arena.symbol(symbol);
        let bound = if model.get(symbol).is_some() {
            "bound"
        } else {
            "UNBOUND"
        };
        println!("    #{:<4} {name:<28} {sort:?}   {bound}", symbol.index());
    }
    println!("  what the model actually binds:");
    for (symbol, value) in model.iter() {
        let (name, sort) = arena.symbol(symbol);
        let used = if free.contains(&symbol) {
            "used by the assertions"
        } else {
            "NOT REFERENCED by the assertions"
        };
        let rendered = format!("{value:?}");
        println!(
            "    #{:<4} {name:<28} {sort:?}   {used}   = {}",
            symbol.index(),
            rendered.chars().take(60).collect::<String>()
        );
    }
    println!();
}

/// Collects the free symbols of `term`'s DAG.
fn free_symbols(arena: &TermArena, term: TermId, out: &mut BTreeSet<SymbolId>) {
    match arena.node(term) {
        TermNode::Symbol(symbol) => {
            out.insert(*symbol);
        }
        TermNode::App { args, .. } => {
            for &arg in args {
                free_symbols(arena, arg, out);
            }
        }
        _ => {}
    }
}

/// The front-door stage whose recorded attempt last decided `sat`.
///
/// Read from the route attribution rather than guessed from the script's shape:
/// the dispatch ladder and the string second chances both record here, so a row
/// the flat path decided and a row a source route decided are distinguishable
/// by what actually ran, not by what the file looks like.
fn deciding_stage() -> String {
    let trace = last_route_attribution();
    for attempt in trace.attempts().iter().rev() {
        if matches!(attempt.outcome, RouteOutcome::Decided(Verdict::Sat)) {
            return attempt.route.to_owned();
        }
    }
    "UNATTRIBUTED".to_owned()
}

fn collect(root: &Path, out: &mut Vec<PathBuf>) {
    if root.is_file() {
        if root.extension().is_some_and(|e| e == "smt2") {
            out.push(root.to_path_buf());
        }
        return;
    }
    let Ok(entries) = std::fs::read_dir(root) else {
        return;
    };
    let mut paths: Vec<PathBuf> = entries.flatten().map(|e| e.path()).collect();
    paths.sort();
    for path in paths {
        collect(&path, out);
    }
}
