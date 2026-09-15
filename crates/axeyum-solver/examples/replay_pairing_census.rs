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

use axeyum_ir::{Sort, SymbolId, TermArena, TermId, TermNode, Value};
use axeyum_smtlib::{decode_packed_string, packed_string_max_len};
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

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let mut budget_ms = 3_000u64;
    let mut require_paired = false;
    let mut explain = false;
    let mut try_lift = false;
    let mut expect_mismatch: Option<usize> = None;
    let mut roots: Vec<PathBuf> = Vec::new();
    let mut i = 0;
    while i < args.len() {
        match args[i].as_str() {
            "--budget-ms" => {
                i += 1;
                budget_ms = args[i].parse().expect("--budget-ms takes a number");
            }
            "--require-paired" => require_paired = true,
            "--explain" => explain = true,
            "--try-lift" => try_lift = true,
            "--expect-mismatch" => {
                i += 1;
                expect_mismatch = Some(args[i].parse().expect("--expect-mismatch takes a number"));
            }
            other => roots.push(PathBuf::from(other)),
        }
        i += 1;
    }
    assert!(!roots.is_empty(), "no corpus roots given");

    let mut files: Vec<PathBuf> = Vec::new();
    for root in &roots {
        collect(root, &mut files);
    }
    files.sort();
    assert!(!files.is_empty(), "corpus roots matched no .smt2 files");

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
                error_detail
                    .entry(error.to_string().chars().take(80).collect::<String>())
                    .and_modify(|n| *n += 1)
                    .or_insert(1usize);
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
        let (verdict, detail) = match &solved.model {
            None => (Replay::Withheld, String::new()),
            Some(model) => match check_model(&solved.script.arena, &solved.assertions, model) {
                Ok(true) => (Replay::Holds, String::new()),
                Ok(false) => (Replay::Refuted, "check_model returned false".to_owned()),
                Err(error) => (Replay::Errored, error.to_string()),
            },
        };
        let slot = per_route.entry(route.clone()).or_insert([0; 4]);
        match verdict {
            Replay::Holds => {
                total.holds += 1;
                slot[0] += 1;
            }
            Replay::Refuted => {
                total.refuted += 1;
                slot[1] += 1;
            }
            Replay::Errored => {
                total.errored += 1;
                slot[2] += 1;
            }
            Replay::Withheld => {
                total.withheld += 1;
                slot[3] += 1;
            }
        }
        if matches!(verdict, Replay::Refuted | Replay::Errored) {
            if explain {
                explain_mismatch(file, &solved);
            }
            if try_lift {
                probe_lift(file, &solved);
            }
            mismatches.push((
                file.display().to_string(),
                route,
                detail.chars().take(200).collect(),
            ));
        }
    }

    // The denominator is printed beside every count, always: a bare zero here
    // would be indistinguishable from a census that examined nothing.
    let carrying = sat - total.withheld;
    println!("budget                                {budget_ms:>6} ms");
    println!("files examined (denominator)          {examined:>6}");
    println!("  undecided                           {undecided:>6}");
    println!("  front door returned Err             {errored_out:>6}");
    for (detail, count) in &error_detail {
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
    for (route, counts) in &per_route {
        println!(
            "  {route:<40} {:>4} {:>4} {:>4} {:>4}",
            counts[0], counts[1], counts[2], counts[3]
        );
    }
    if !mismatches.is_empty() {
        println!();
        println!("mispaired rows ({}):", mismatches.len());
        for (file, route, detail) in &mismatches {
            println!("  {file}");
            println!("      route={route}  {detail}");
        }
    }

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

/// Dry-runs repair (b) — lift the source-level `Seq` witness into the packed
/// bit-vector space — and reports what `check_model` says AFTERWARDS.
///
/// This is the measurement the repair choice turns on, and it has three
/// possible answers, only one of which is the repair working:
///
/// * `Ok(true)` — the lift is real evidence: the packed vector is satisfied by
///   the packed witness, so the replay checks the run that happened.
/// * `Ok(false)` — the lift ran and the packed vector REJECTS the source
///   witness. That is not a repair; it converts an honest `Err` into a false
///   soundness signal, which is strictly worse.
/// * unliftable — the witness cannot be represented in the packed encoding at
///   all (a code point above a byte, or a length past the packed cap). Then
///   repair (b) is impossible for that row, not merely large.
fn probe_lift(file: &Path, solved: &SmtLibSolved) {
    let Some(model) = &solved.model else {
        return;
    };
    let script = &solved.script;
    let arena = &script.arena;
    let mut lifted = model.clone();
    let mut unliftable: Vec<String> = Vec::new();
    let mut packed = 0usize;
    for &(symbol, _) in &script.declared_strings {
        if lifted.get(symbol).is_some() {
            continue;
        }
        let (name, sort) = arena.symbol(symbol);
        let Sort::BitVec(width) = sort else {
            continue;
        };
        let Some(word) = arena.find_internal_symbol(&format!("!weq!{name}")) else {
            unliftable.push(format!("{name}: no `!weq!` witness symbol"));
            continue;
        };
        let Some(Value::Seq(elements)) = lifted.get(word) else {
            unliftable.push(format!("{name}: `!weq!{name}` carries no `Seq` value"));
            continue;
        };
        let mut bytes = Vec::with_capacity(elements.len());
        let mut wide = None;
        for element in &elements {
            match element {
                Value::Bv { value, .. } if *value <= 0xff => {
                    bytes.push(u8::try_from(*value).expect("masked to a byte"));
                }
                Value::Bv { value, .. } => wide = Some(*value),
                _ => wide = Some(u128::MAX),
            }
        }
        if let Some(code) = wide {
            unliftable.push(format!(
                "{name}: witness carries code point {code}, outside the packed BYTE encoding"
            ));
            continue;
        }
        let Some(max_len) = packed_string_max_len(width) else {
            unliftable.push(format!(
                "{name}: width {width} is not a packed string layout"
            ));
            continue;
        };
        if bytes.len() > max_len as usize {
            unliftable.push(format!(
                "{name}: witness is {} bytes, past the packed cap {max_len} for width {width}",
                bytes.len()
            ));
            continue;
        }
        let lw = 32 - max_len.leading_zeros();
        let mut content: u128 = 0;
        for (i, &b) in bytes.iter().enumerate() {
            content |= u128::from(b) << (8 * i);
        }
        let bits = (content << lw) | u128::from(bytes.len() as u32);
        if decode_packed_string(width, bits).as_deref() != Some(bytes.as_slice()) {
            unliftable.push(format!(
                "{name}: packing did not round-trip through the decoder"
            ));
            continue;
        }
        lifted.set(symbol, Value::Bv { width, value: bits });
        packed += 1;
    }
    let after = match check_model(arena, &solved.assertions, &lifted) {
        Ok(true) => "Ok(true)  -- the lift IS real evidence".to_owned(),
        Ok(false) => "Ok(false) -- the packed vector REJECTS the source witness".to_owned(),
        Err(error) => format!("Err({error})"),
    };
    // Is the packed vector satisfiable AT ALL? For a row whose source witness
    // is longer than the packed cap this is the decisive question: if the packed
    // assertions have no model, then no lift can exist, and pairing ANY model
    // with them would replay `false` on a correct `sat`.
    let mut probe_arena = arena.clone();
    let packed_satisfiable = match axeyum_solver::check_auto(
        &mut probe_arena,
        &solved.assertions,
        &SolverConfig::default().with_timeout(Duration::from_millis(5_000)),
    ) {
        Ok(CheckResult::Sat(_)) => "sat",
        Ok(CheckResult::Unsat) => "UNSAT -- no lift can exist",
        Ok(CheckResult::Unknown(_)) => "unknown",
        Err(_) => "error",
    };
    println!("  LIFT PROBE {}", file.display());
    println!("    packed assertion vector alone: {packed_satisfiable}");
    println!(
        "    symbols packed: {packed}   unliftable: {}",
        unliftable.len()
    );
    for reason in &unliftable {
        println!("      {reason}");
    }
    println!("    check_model after lift: {after}");
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
    let mut paths: Vec<PathBuf> = entries.filter_map(|e| e.ok()).map(|e| e.path()).collect();
    paths.sort();
    for path in paths {
        collect(&path, out);
    }
}
