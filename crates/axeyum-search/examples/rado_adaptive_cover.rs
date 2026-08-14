//! Adaptive cube-cover driver for the Rado family, built for `F_741`.
//!
//! The 2026-08-12 probe of `R_4(5(x-y)=4z)` at `n = 741` measured where a flat
//! cover fails: of 1946 finished depth-6 cells, 746 fell to unit propagation
//! instantly and 1132 exhausted a 200k-conflict budget. Uniform deepening
//! multiplies the easy cells for nothing; a uniform budget raise pays the
//! hard cells' worst case everywhere. So this driver runs
//! [`run_adaptive_cover`]: a cube that exhausts its budget is split on the next
//! branch point and its children queued.
//!
//! What comes out, all under `out=`:
//!
//! | file | what it is |
//! |---|---|
//! | `cover.run-<run>.tsv` | ledger: one row per **refuted** cube |
//! | `pending.run-<run>.tsv` | every cube not refuted, with why — the resume point |
//! | `proofs/` | per-cube DRAT, for the offline certification pass |
//! | `model.run-<run>.txt` | written first and `fsync`ed if a cube is satisfiable |
//!
//! A stopped run is not a failed run: `pending.run-<run>.tsv` fed back as
//! `resume=` continues exactly where this one stopped, and the two runs'
//! ledgers concatenate into one cover because cube codes do not depend on the
//! tree's shape.
//!
//! Nothing here trusts this run: the ledger's `check` column is `deferred`
//! whenever a proof is over `check_cap`, and `rado_certify_tree_cover` is what
//! turns a pile of dumped proofs into a certificate.
//!
//! usage: `rado_adaptive_cover a=5 b=4 k=4 n=741 out=/path run=b1 [key=value ...]`
//!
//! | key | default | meaning |
//! |---|---|---|
//! | `depth` | 12 | branch groups, i.e. the maximum split depth |
//! | `initial` | 6 | depth of the starting frontier |
//! | `points` | `2,4,6,…` | explicit branch points, overriding `depth` |
//! | `workers` | 8 | worker threads |
//! | `conflicts` | 200000 | per-cube conflict budget above full depth |
//! | `final_conflicts` | 20000000 | per-cube budget at full depth (cannot split) |
//! | `check` | `deferred` | `deferred`, `backward`, or `forward` |
//! | `check_cap` | 0 | check inline only proofs at most this many steps |
//! | `hours` | 6 | whole-run wall-clock budget |
//! | `cube_seconds` | 0 | per-cube wall-clock budget, 0 for none |
//! | `resume` | — | a `pending.tsv` to continue from |
//! | `progress` | 200 | print a census line every this many finished cubes |
//! | `proofs` | `<out>/proofs` | proof dump directory, or `none` to keep none |
//!
//! exit: 0 refuted (see the JSON for whether it also certified), 6 incomplete,
//! 10 SATISFIABLE (which would retire the paper's tightness claim at k = 4),
//! 3 error, 2 usage.

// `main` is one long linear script by design: parse the arguments, run, and
// report. Splitting it would scatter a driver that is meant to be read top to
// bottom next to the log it produces.
#![allow(clippy::too_many_lines)]

use std::collections::BTreeMap;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::ExitCode;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Mutex, PoisonError};
use std::time::{Duration, Instant};

use axeyum_search::cover::colour_branch_plan;
use axeyum_search::harness::{
    AdaptiveOptions, AdaptiveOutcome, CoverObserver, PendingReason, parse_pending, render_pending,
    run_adaptive_cover,
};
use axeyum_search::ledger::render_ledger;
use axeyum_search::{CellRecord, CheckMode, ColouringFamily, CoverOptions, Rado, RunId};

/// `key=value` arguments, so a long command line stays readable in a log.
struct Args(BTreeMap<String, String>);

impl Args {
    fn parse() -> Self {
        Self(
            std::env::args()
                .skip(1)
                .filter_map(|arg| {
                    arg.split_once('=')
                        .map(|(key, value)| (key.to_string(), value.to_string()))
                })
                .collect(),
        )
    }

    fn get(&self, key: &str) -> Option<&str> {
        self.0.get(key).map(String::as_str)
    }

    fn number(&self, key: &str, fallback: usize) -> usize {
        self.get(key)
            .map_or(fallback, |value| value.parse().expect("number"))
    }

    fn float(&self, key: &str, fallback: f64) -> f64 {
        self.get(key)
            .map_or(fallback, |value| value.parse().expect("float"))
    }
}

/// Prints a census line periodically instead of one line per cube: an adaptive
/// run over `F_741` finishes hundreds of thousands of them.
struct Progress {
    started: Instant,
    every: usize,
    finished: AtomicUsize,
    splits: AtomicUsize,
    steps: AtomicUsize,
    deepest: AtomicUsize,
    slowest: Mutex<(f64, usize)>,
}

impl Progress {
    fn new(every: usize) -> Self {
        Self {
            started: Instant::now(),
            every: every.max(1),
            finished: AtomicUsize::new(0),
            splits: AtomicUsize::new(0),
            steps: AtomicUsize::new(0),
            deepest: AtomicUsize::new(0),
            slowest: Mutex::new((0.0, 0)),
        }
    }

    fn census(&self) -> String {
        let slowest = *self.slowest.lock().unwrap_or_else(PoisonError::into_inner);
        format!(
            "[{elapsed:8.1}s] refuted={refuted} splits={splits} steps={steps} \
             deepest={deepest} slowest={slow:.1}s(cube {cube})",
            elapsed = self.started.elapsed().as_secs_f64(),
            refuted = self.finished.load(Ordering::Relaxed),
            splits = self.splits.load(Ordering::Relaxed),
            steps = self.steps.load(Ordering::Relaxed),
            deepest = self.deepest.load(Ordering::Relaxed),
            slow = slowest.0,
            cube = slowest.1,
        )
    }
}

impl CoverObserver for Progress {
    fn on_cell_finished(&self, record: &CellRecord) {
        let count = self.finished.fetch_add(1, Ordering::Relaxed) + 1;
        self.steps.fetch_add(record.steps, Ordering::Relaxed);
        self.deepest
            .fetch_max(record.choices.len(), Ordering::Relaxed);
        let solve = record.solve.as_secs_f64();
        {
            let mut slowest = self.slowest.lock().unwrap_or_else(PoisonError::into_inner);
            if solve > slowest.0 {
                *slowest = (solve, record.index);
            }
        }
        if count.is_multiple_of(self.every) {
            println!("{}", self.census());
        }
    }

    fn on_note(&self, message: &str) {
        if message.starts_with("split cube") {
            let splits = self.splits.fetch_add(1, Ordering::Relaxed) + 1;
            if splits.is_multiple_of(self.every) {
                println!("{message}");
                println!("{}", self.census());
            }
            return;
        }
        println!("{message}");
    }

    fn on_model_persisted(&self, cell: usize, path: &Path, model: &[bool]) {
        println!(
            "SATISFIABLE: cube {cell}, {} model values persisted to {}",
            model.len(),
            path.display()
        );
    }
}

fn check_mode(token: &str) -> CheckMode {
    match token {
        "deferred" => CheckMode::Deferred,
        "backward" => CheckMode::Backward,
        "forward" => CheckMode::Forward,
        other => panic!("unknown check mode {other:?}"),
    }
}

fn main() -> ExitCode {
    let args = Args::parse();
    let (Some(out), Some(run)) = (args.get("out"), args.get("run")) else {
        eprintln!(
            "usage: rado_adaptive_cover a=5 b=4 k=4 n=741 out=<dir> run=<id> [key=value ...]"
        );
        return ExitCode::from(2);
    };
    let out = PathBuf::from(out);
    let run = RunId::new(run).expect("run id");
    let (a, b, k, n) = (
        args.number("a", 5),
        args.number("b", 4),
        args.number("k", 4),
        args.number("n", 741),
    );

    let family = Rado::new(a, b, k).expect("family");
    let problem = family.problem(n).expect("problem");
    let formula = problem.encode().expect("encode");
    let points: Vec<usize> = match args.get("points") {
        Some(list) => list
            .split(',')
            .map(|token| token.parse().expect("branch point"))
            .collect(),
        None => family.branch_points(args.number("depth", 12)),
    };
    let plan = colour_branch_plan(&problem, &points).expect("plan");

    fs::create_dir_all(&out).expect("create out dir");
    let ledger_path = out.join(format!("cover.run-{run}.tsv"));
    let pending_path = out.join(format!("pending.run-{run}.tsv"));
    // `proofs=none` runs the checker inline and keeps nothing on disk. At
    // `F_741` scale that is not a convenience: a hard cube's proof is tens of
    // megabytes of text DRAT, and a tree cover can have tens of thousands of
    // them, so dumping unconditionally is how a run dies of disk rather than of
    // difficulty. The cube list in the ledger is the artifact that matters —
    // every proof is regenerable from it, deterministically.
    let proof_dir = match args.get("proofs") {
        Some("none") => None,
        Some(dir) => Some(PathBuf::from(dir)),
        None => Some(out.join("proofs")),
    };
    let options = CoverOptions {
        workers: args.number("workers", 8),
        cell_conflicts: args.number("conflicts", 200_000),
        cell_time: match args.number("cube_seconds", 0) {
            0 => None,
            seconds => Some(Duration::from_secs(
                u64::try_from(seconds).expect("seconds"),
            )),
        },
        total_time: Some(Duration::from_secs_f64(args.float("hours", 6.0) * 3600.0)),
        check: check_mode(args.get("check").unwrap_or("deferred")),
        check_step_cap: args.number("check_cap", 0),
        retain_proofs: false,
        proof_dir: proof_dir.clone(),
        proof_prefix: format!("f{n}"),
        model_path: Some(out.join(format!("model.run-{run}.txt"))),
        ledger_path: Some(ledger_path.clone()),
        run: run.clone(),
        ..CoverOptions::default()
    };
    let seed_cubes = args.get("resume").map(|path| {
        let text = fs::read_to_string(path).expect("read resume file");
        parse_pending(&plan, &text)
            .expect("parse resume file")
            .into_iter()
            .map(|cube| cube.path)
            .collect::<Vec<_>>()
    });
    let adaptive = AdaptiveOptions {
        initial_depth: args.number("initial", 6),
        final_conflicts: args.number("final_conflicts", 20_000_000),
        seed_cubes,
        pending_path: Some(pending_path.clone()),
    };

    println!(
        "instance R_{k}({a}(x-y)={b}z) n={n}: {} vars, {} clauses; branch points {points:?}",
        formula.variable_count(),
        formula.clauses().len()
    );
    println!(
        "workers={} conflicts={} final_conflicts={} check={:?} check_cap={} hours={} initial_depth={} resume={:?}",
        options.workers,
        options.cell_conflicts,
        adaptive.final_conflicts,
        options.check,
        options.check_step_cap,
        args.float("hours", 6.0),
        adaptive.initial_depth,
        args.get("resume"),
    );

    let progress = Progress::new(args.number("progress", 200));
    let started = Instant::now();
    let outcome = match run_adaptive_cover(&formula, &plan, &options, &adaptive, &progress) {
        Ok(outcome) => outcome,
        Err(error) => {
            println!("{{\"status\":\"error\",\"error\":\"{error}\"}}");
            return ExitCode::from(3);
        }
    };
    let wall = started.elapsed().as_secs_f64();
    println!("{}", progress.census());

    // A byte-stable ledger next to the live one: the live file's row order is
    // completion order, which no two runs agree on.
    let stable = out.join(format!("cover.run-{run}.sorted.tsv"));
    fs::write(&stable, render_ledger(outcome.records())).expect("write sorted ledger");

    match &outcome {
        AdaptiveOutcome::Satisfiable { path, model, .. } => {
            println!(
                "{{\"status\":\"sat\",\"n\":{n},\"cube\":{path:?},\"model_values\":{},\"wall_s\":{wall:.1}}}",
                model.len()
            );
            ExitCode::from(10)
        }
        AdaptiveOutcome::Refuted {
            certificate,
            certificate_gap,
            records,
            splits,
            ..
        } => {
            let steps: usize = records.iter().map(|record| record.steps).sum();
            println!(
                "{{\"status\":\"refuted\",\"n\":{n},\"cubes\":{},\"splits\":{splits},\
                 \"steps\":{steps},\"certified\":{},\"gap\":{:?},\"wall_s\":{wall:.1},\
                 \"ledger\":{:?},\"proofs\":{:?}}}",
                records.len(),
                certificate.is_some(),
                certificate_gap.as_deref().unwrap_or(""),
                stable.display().to_string(),
                proof_dir
                    .as_ref()
                    .map_or_else(|| "none".to_string(), |dir| dir.display().to_string()),
            );
            ExitCode::SUCCESS
        }
        AdaptiveOutcome::Incomplete {
            pending,
            records,
            splits,
            ..
        } => {
            let mut census: BTreeMap<&str, usize> = BTreeMap::new();
            for cube in pending {
                *census.entry(cube.reason.as_str()).or_default() += 1;
            }
            let deepest = pending
                .iter()
                .map(|cube| cube.path.len())
                .max()
                .unwrap_or(0);
            let stuck: Vec<_> = pending
                .iter()
                .filter(|cube| cube.reason != PendingReason::Unstarted)
                .collect();
            println!(
                "{{\"status\":\"incomplete\",\"n\":{n},\"refuted\":{},\"splits\":{splits},\
                 \"pending\":{},\"pending_census\":{:?},\"deepest_pending\":{deepest},\
                 \"stuck\":{},\"wall_s\":{wall:.1},\"resume\":{:?}}}",
                records.len(),
                pending.len(),
                census,
                stuck.len(),
                pending_path.display().to_string(),
            );
            // Belt and braces: the harness already wrote the pending file, but
            // a run that stops without one is a run that has to start over.
            if !pending_path.exists() {
                fs::write(&pending_path, render_pending(pending)).expect("write pending");
            }
            ExitCode::from(6)
        }
    }
}
